use std::fmt::Error;
use std::ops::{Add, Neg, Sub};
use bls12_381::{G1Affine, G1Projective, G2Affine, G2Projective, Gt, pairing, Scalar};
use rand::prelude::*;
use sha3::{Digest, Sha3_256};
use sha3::digest::Output;
use crate::accumulator::ZkpProof;
use crate::commitment::Commiter;
use crate::{AccNa, random_scalar};

#[derive(Debug, Clone)]
pub struct BBS {
    g1: G1Affine,
    g2: G2Affine,
    sk: Scalar,
    w: G2Affine,
    pk: Vec<G1Affine>,
}

pub struct SPK {
    A_prime: G1Projective,
    Abar: G1Projective,
    D: G1Projective,
    e_caret: Scalar,
    r2_caret: Scalar,
    r3_caret: Scalar,
    s_caret: Scalar,
    m_caret: Vec<Scalar>,
    C1: G1Projective,
    C2: G1Projective,
}

impl SPK {
    pub(crate) fn detach(self) -> (G1Projective, G1Projective, G1Projective, Scalar, Scalar, Scalar, Scalar, Vec<Scalar>, G1Projective, G1Projective) {
        (self.A_prime, self.Abar, self.D, self.e_caret,
         self.r2_caret, self.r3_caret, self.s_caret, self.m_caret, self.C1, self.C2)
    }
}


impl BBS {
    pub(crate) fn keygen(attr_nums: i32) -> BBS {
        let mut rng = thread_rng();
        let sk = random_scalar(&mut rng);

        let g1 = G1Affine::generator();
        let g2 = G2Affine::generator();
        let w = G2Affine::from(g2 * sk);
        let mut pk = Vec::new();

        for i in 0..attr_nums + 1 {
            let temp = G1Affine::from(g1 * random_scalar(&mut rng));
            pk.push(temp);
        }

        BBS {
            g1,
            g2,
            w,
            sk,
            pk,
        }
    }

    pub(crate) fn sign(self, msgs: &Vec<Scalar>) -> (G1Affine, Scalar, Scalar) {
        let mut rng = thread_rng();
        let e = random_scalar(&mut rng);
        let s = random_scalar(&mut rng);

        assert_eq!(msgs.contains(&e), false);
        assert_eq!(msgs.contains(&s), false);

        let mut A = self.g1 + self.pk[0] * s;
        for i in 0..msgs.len() {
            A = A + self.pk[i + 1] * msgs[i];
        }
        (G1Affine::from(A * (self.sk + e).invert().unwrap()), e, s)
    }

    pub(crate) fn verify(msgs: &Vec<Scalar>, A: &G1Affine, e: &Scalar, s: &Scalar, pk: &Vec<G1Affine>, g1: &G1Affine, g2: &G2Affine, w: &G2Affine) {
        let mut B = g1 + pk[0] * s;
        for i in 0..msgs.len() {
            B = B + pk[i + 1] * msgs[i];
        }

        assert_eq!(pairing(A, &G2Affine::from(w + g2 * e)),
                   pairing(&G1Affine::from(B), g2)
        )
    }

    pub(crate) fn gen_spk(msgs: &Vec<Scalar>, A: &G1Affine, e: &Scalar, s: &Scalar, reveal_index: &Vec<i32>, pk: &Vec<G1Affine>, g1: &G1Affine) -> SPK {
        let mut rng = thread_rng();

        //---------------------------accumulator zkp values---------------------------------------//
        // let r1 = random_scalar(&mut rng);
        // let r2 = random_scalar(&mut rng);
        // let w1 = (commiter.g * r1).add(&(&commiter.h * r2));
        // let w1_r = w1 * x;
        //
        //
        // let delta1 = x * r1;
        // let delta2 = x * r2;
        //
        //
        // let o_com = random_scalar(&mut rng);
        // let cr = (commiter.g * x).add(&(&commiter.h * o_com));
        // let w2 = wx.add(&(commiter.g * r1));

        //------------------------accumulator zkp values------------------------------------------//
        let mut unreveal_index = Vec::new();
        for i in 0..msgs.len() as i32 {
            if reveal_index.contains(&i) == false {
                unreveal_index.push(i);
            }
        }


        let (A_prime, Abar, D,
            c,
            e_tilde, r2_tilde, r3_tilde, m_tildes, r2, r3
            , s_prime, s_tilde, C1, C2)
            = loop {
            //-----------------------bbs zkp blindings--------------------------------------------//
            let r1 = random_scalar(&mut rng);
            let r2 = random_scalar(&mut rng);
            let e_tilde = random_scalar(&mut rng);
            let r2_tilde = random_scalar(&mut rng);
            let r3_tilde = random_scalar(&mut rng);
            let s_tilde = random_scalar(&mut rng);

            let mut m_tildes = Vec::new();
            for i in 0..unreveal_index.len() {
                m_tildes.push(random_scalar(&mut rng));
            }

            let mut b = g1 + pk[0] * s;
            for i in 0..msgs.len() {
                b = b + pk[i + 1] * msgs[i];
            }

            let r3 = r1.invert().unwrap();
            let A_prime = A * r1;
            let Abar = A_prime * (-e) + b * r1;
            let D = b * r1 + pk[0] * r2;
            let s_prime = s + r2 * r3;
            let C1 = A_prime * e_tilde + pk[0] * r2_tilde;
            let mut C2 = D * (-r3_tilde) + pk[0] * s_tilde;

            for i in 0..m_tildes.len() {
                C2 = C2 + pk[unreveal_index[i] as usize + 1] * m_tildes[i];
            }

            let mut hasher = Sha3_256::new();
            let mut pk_string = String::new();
            for public_key in pk {
                pk_string = pk_string + &*public_key.to_string();
            }

            let mut msg_string = String::new();
            for msg in msgs {
                msg_string = msg_string + &*msg.to_string();
            }

            //Fiat-Shamir Heuristic
            let hash_data = pk_string + &*A_prime.to_string() + &*Abar.to_string() + &*D.to_string()
                + &*C1.to_string() + &*C2.to_string() + &*msg_string;
            hasher.update(hash_data);

            let result = hasher.finalize();
            // println!("{:?}", result);
            let flag = Scalar::from_bytes(result.as_ref()).is_none().unwrap_u8();

            if flag == 0 {
                break (A_prime, Abar, D,
                       Scalar::from_bytes(result.as_ref()).unwrap(),
                       e_tilde, r2_tilde, r3_tilde, m_tildes, r2, r3, s_prime, s_tilde, C1, C2
                );
            }
        };

        let e_caret = e_tilde + c * e;
        let r2_caret = r2_tilde + c * r2;
        let r3_caret = r3_tilde + c * r3;

        let s_caret = s_tilde + c * s_prime;
        let mut m_caret = Vec::new();
        for idx in 0..m_tildes.len() {
            m_caret.push(m_tildes[idx] + c * msgs[unreveal_index[idx] as usize]);
        }


        let spk = SPK {
            A_prime,
            Abar,
            D,
            e_caret,
            r2_caret,
            r3_caret,
            s_caret,
            m_caret,
            C1,
            C2,
        }
            ;
        spk
    }

    pub(crate) fn verify_spk(msgs: &Vec<Scalar>, reveal_index: Vec<i32>, pk: &Vec<G1Affine>, g1: &G1Affine, spk: SPK, w: &G2Affine, g2: &G2Affine) -> bool {
        let mut unreveal_index = Vec::new();
        for i in 0..msgs.len() as i32 {
            if reveal_index.contains(&i) == false {
                unreveal_index.push(i);
            }
        }


        let (A_prime, Abar, D, e_caret,
            r2_caret, r3_caret, s_caret, m_caret, C1, C2) = spk.detach();

            let mut hasher = Sha3_256::new();
            let mut pk_string = String::new();
            for public_key in pk {
                pk_string = pk_string + &*public_key.to_string();
            }

            let mut msg_string = String::new();
            for msg in msgs {
                msg_string = msg_string + &*msg.to_string();
            }
            //compute c
            let hash_data = pk_string + &*A_prime.to_string() + &*Abar.to_string() + &*D.to_string()
                + &*C1.to_string() + &*C2.to_string() + &*msg_string;
            hasher.update(hash_data);

            let result = hasher.finalize();
            let c = Scalar::from_bytes(result.as_ref()).unwrap();


        let C1_prime = (Abar - D) * c + A_prime * e_caret + pk[0] * r2_caret;
        assert_eq!(C1, C1_prime);

        let mut T = G1Projective::from(g1);
        for idx in reveal_index {
            T += pk[idx as usize + 1] * msgs[idx as usize];
        }

        let mut C2_prime = T * c + D * (-r3_caret) + pk[0] * s_caret;
        for idx in 0..m_caret.len() {
            C2_prime += pk[unreveal_index[idx] as usize + 1] * m_caret[idx];
        }
        assert_eq!(C2, C2_prime);

        assert_ne!(A_prime, G1Projective::identity());
        let pairing_1 = pairing(&G1Affine::from(A_prime), w);
        let pairing_2 = pairing(&G1Affine::from(Abar), &-g2);
        assert_eq!(pairing_1 + pairing_2, Gt::identity());

        true
    }

    pub(crate) fn gen_spk_with_acc(msgs: &Vec<Scalar>, A: &G1Affine, e: &Scalar, s: &Scalar,
                                   reveal_index: &Vec<i32>, pk: &Vec<G1Affine>, g1: &G1Affine,
                                   commiter: &Commiter, wx:&G1Affine, acc:&AccNa) -> (SPK, ZkpProof) {
        let mut rng = thread_rng();

        //---------------------------accumulator zkp values---------------------------------------//
        let r1_acc = random_scalar(&mut rng);
        let r2_acc = random_scalar(&mut rng);
        let w1 = (commiter.g * r1_acc).add(&(&commiter.h * r2_acc));
        let x = msgs[0];
        let w1_r = w1 * x;


        let delta1 = x * r1_acc;
        let delta2 = x * r2_acc;


        let o_com = random_scalar(&mut rng);
        let cr = (commiter.g * x).add(&(&commiter.h * o_com));
        let w2 = wx.add(&(commiter.g * r1_acc));

        //------------------------accumulator zkp values------------------------------------------//

        let mut unreveal_index = Vec::new();
        for i in 0..msgs.len() as i32 {
            if reveal_index.contains(&i) == false {
                unreveal_index.push(i);
            }
        }


        let (blind_r1, blind_r2, R1, blind_delta1, blind_delta2, R2, R3
            , blind_x, blind_o_com, R4,
            A_prime, Abar, D,
            c,
            e_tilde, r2_tilde, r3_tilde, m_tildes, r2, r3
            , s_prime, s_tilde, C1, C2)
            = loop {
                //-----------------------bbs zkp blindings--------------------------------------------//
                let r1 = random_scalar(&mut rng);
                let r2 = random_scalar(&mut rng);
                let e_tilde = random_scalar(&mut rng);
                let r2_tilde = random_scalar(&mut rng);
                let r3_tilde = random_scalar(&mut rng);
                let s_tilde = random_scalar(&mut rng);

                let mut m_tildes = Vec::new();
                for i in 0..unreveal_index.len() {
                    m_tildes.push(random_scalar(&mut rng));
                }

                let mut b = g1 + pk[0] * s;
                for i in 0..msgs.len() {
                    b = b + pk[i + 1] * msgs[i];
                }

                let r3 = r1.invert().unwrap();
                let A_prime = A * r1;
                let Abar = A_prime * (-e) + b * r1;
                let D = b * r1 + pk[0] * r2;
                let s_prime = s + r2 * r3;
                let C1 = A_prime * e_tilde + pk[0] * r2_tilde;
                let mut C2 = D * (-r3_tilde) + pk[0] * s_tilde;

                for i in 0..m_tildes.len() {
                    C2 = C2 + pk[unreveal_index[i] as usize + 1] * m_tildes[i];
                }

                let mut hasher = Sha3_256::new();
                let mut pk_string = String::new();
                for public_key in pk {
                    pk_string = pk_string + &*public_key.to_string();
                }

                let mut msg_string = String::new();
                for msg in msgs {
                    msg_string = msg_string + &*msg.to_string();
                }


                //----------------------------accumulator zkp blindings------------------------------//
                let blind_r1 = random_scalar(&mut rng);
                let blind_r2 = random_scalar(&mut rng);
                let R1 = (commiter.g * blind_r1).add(&(&commiter.h * blind_r2));


                let blind_delta1 = random_scalar(&mut rng);
                let blind_delta2 = random_scalar(&mut rng);
                let R2 = (commiter.g * blind_delta1).add(&(&commiter.h * blind_delta2));

                let blind_x = m_tildes[0];
                let R3 = (pairing(&G1Affine::from(w2), &acc.g2) * blind_x.neg())
                    .add(pairing(&commiter.g, &acc.g2) * blind_delta1)
                    .add(pairing(&commiter.g, &acc.ga) * blind_r1);


                let blind_o_com = random_scalar(&mut rng);
                let R4 = (commiter.g * blind_x).add(&(&commiter.h * blind_o_com));

                //Fiat-Shamir Heuristic
                let hash_data_acc = R1.to_string() + &*R2.to_string() +
                    &*R3.to_string() + &*R4.to_string() +
                    &*commiter.g.to_string() + &*commiter.h.to_string() +
                    &*w1.to_string() + &*w1_r.to_string() + &*w2.to_string() + &*cr.to_string()
                    ;

                //Fiat-Shamir Heuristic
                hasher.update(hash_data_acc);
                let hash_data = pk_string + &*A_prime.to_string() + &*Abar.to_string() + &*D.to_string()
                    + &*C1.to_string() + &*C2.to_string() + &*msg_string;
                hasher.update(hash_data.clone());

                let result = hasher.finalize();
                // println!("{:?}", result);
                let flag = Scalar::from_bytes(result.as_ref()).is_none().unwrap_u8();

                if flag == 0 {
                    break (blind_r1, blind_r2, R1, blind_delta1, blind_delta2, R2, R3
                           , blind_x, blind_o_com, R4,
                           A_prime, Abar, D,
                           Scalar::from_bytes(result.as_ref()).unwrap(),
                           e_tilde, r2_tilde, r3_tilde, m_tildes, r2, r3, s_prime, s_tilde, C1, C2,
                    );
                }
        };

        let e_caret = e_tilde + c * e;
        let r2_caret = r2_tilde + c * r2;
        let r3_caret = r3_tilde + c * r3;

        let s_caret = s_tilde + c * s_prime;
        let mut m_caret = Vec::new();
        for idx in 0..m_tildes.len() {
            m_caret.push(m_tildes[idx] + c * msgs[unreveal_index[idx] as usize]);
        }


        let spk = SPK {
            A_prime,
            Abar,
            D,
            e_caret,
            r2_caret,
            r3_caret,
            s_caret,
            m_caret,
            C1,
            C2,
        };

        //generate values for proof
        let s_r1 = blind_r1 + c * r1_acc;
        let s_r2 = blind_r2 + c * r2_acc;
        let s_delta1 = blind_delta1 + c * delta1;
        let s_delta2 = blind_delta2 + c * delta2;
        let s_x = blind_x + c * x;
        let s_o_com = blind_o_com + c * o_com;

        let zkp_proof = ZkpProof::init(cr,
                                       w1,
                                       w1_r,
                                       w2,
                                       R1,
                                       R2,
                                       R3,
                                       R4,
                                       s_r1,
                                       s_r2,
                                       s_delta1,
                                       s_delta2,
                                       s_x,
                                       s_o_com);

        (spk, zkp_proof)
    }

    pub(crate) fn verify_spk_with_acc(msgs: &Vec<Scalar>, reveal_index: Vec<i32>, pk: &Vec<G1Affine>,
                                      g1: &G1Affine, spk: SPK, w: &G2Affine, g2: &G2Affine,
                                      zkp_proof:&ZkpProof, acc:&AccNa, commiter:&Commiter) -> bool {
        //------------------------------------------------compute c--------------------------------//
        let (cr, w1, w1_r, w2, R1, R2, R3, R4,
            s_r1, s_r2, s_delta1, s_delta2, s_x, s_o_com) = zkp_proof.unpack();

        let (A_prime, Abar, D, e_caret,
            r2_caret, r3_caret, s_caret, m_caret, C1, C2) = spk.detach();
        //compute c
        let mut hasher = Sha3_256::new();
        let mut pk_string = String::new();
        for public_key in pk {
            pk_string = pk_string + &*public_key.to_string();
        }

        let mut msg_string = String::new();
        for msg in msgs {
            msg_string = msg_string + &*msg.to_string();
        }
        //compute c
        //Fiat-Shamir Heuristic
        let hash_data_acc = R1.to_string() + &*R2.to_string() +
            &*R3.to_string() + &*R4.to_string() +
            &*commiter.g.to_string() + &*commiter.h.to_string() +
            &*w1.to_string() + &*w1_r.to_string() + &*w2.to_string() + &*cr.to_string()
            ;

        //Fiat-Shamir Heuristic
        hasher.update(hash_data_acc);
        let hash_data = pk_string + &*A_prime.to_string() + &*Abar.to_string() + &*D.to_string()
            + &*C1.to_string() + &*C2.to_string() + &*msg_string;
        hasher.update(hash_data);

        let result = hasher.finalize();
        let c = Scalar::from_bytes(result.as_ref()).unwrap();
        //------------------------------------------------compute c-------------------------------//


        let mut unreveal_index = Vec::new();
        for i in 0..msgs.len() as i32 {
            if reveal_index.contains(&i) == false {
                unreveal_index.push(i);
            }
        }




        let C1_prime = (Abar - D) * c + A_prime * e_caret + pk[0] * r2_caret;
        assert_eq!(C1, C1_prime);

        let mut T = G1Projective::from(g1);
        for idx in reveal_index {
            T += pk[idx as usize + 1] * msgs[idx as usize];
        }

        let mut C2_prime = T * c + D * (-r3_caret) + pk[0] * s_caret;
        for idx in 0..m_caret.len() {
            C2_prime += pk[unreveal_index[idx] as usize + 1] * m_caret[idx];
        }
        assert_eq!(C2, C2_prime);

        let mut pk_string = String::new();
        for public_key in pk {
            pk_string = pk_string + &*public_key.to_string();
        }

        let mut msg_string = String::new();
        for msg in msgs {
            msg_string = msg_string + &*msg.to_string();
        }

        assert_ne!(A_prime, G1Projective::identity());
        let pairing_1 = pairing(&G1Affine::from(A_prime), w);
        let pairing_2 = pairing(&G1Affine::from(Abar), &-g2);
        assert_eq!(pairing_1 + pairing_2, Gt::identity());

        //--------------------------ACC ZKP--------------------------------------------------------//

        let R1_prime = (commiter.g * s_r1).add(&(&commiter.h * s_r2));
        assert_eq!(R1.add_mixed(&G1Affine::from(w1 * c)), R1_prime);

        let R2_prime = (commiter.g * s_delta1).add(&(&commiter.h * s_delta2));
        assert_eq!(R2.add_mixed(&G1Affine::from(w1_r * c)), R2_prime);

        let inverse = pairing(&acc.v0, &acc.g2) * Scalar::one().neg();

        //e(w2,ga)/e(v0,g2)
        let R3_prime = (pairing(&G1Affine::from(w2), &acc.ga).add(inverse) * c).add(R3);

        let R3_p = (pairing(&G1Affine::from(w2), &acc.g2) * s_x.neg())
            .add(pairing(&commiter.g, &acc.g2) * s_delta1).add(pairing(&commiter.g, &acc.ga) * s_r1);
        assert_eq!(R3_prime, R3_p);

        let R4_prime = (commiter.g * s_x).add(&(&commiter.h * s_o_com));
        assert_eq!(R4.add_mixed(&G1Affine::from(cr * c)), R4_prime);

        assert_eq!(s_x, m_caret[0]);
        true
    }

}


#[cfg(test)]
mod test {
    use std::time::{Duration, Instant};
    use bls12_381::G1Affine;
    use rand::thread_rng;
    use crate::bbs::BBS;
    use crate::{AccNa, random_scalar};
    use crate::commitment::Commiter;

    #[test]
    fn test_key_gen() {
        let attr_nums = 5;
        BBS::keygen(attr_nums);
    }

    #[test]
    fn test_sign() {
        let attr_nums = 5;
        let bbs = BBS::keygen(attr_nums);
        let mut msgs = Vec::new();
        let mut rng = thread_rng();

        for i in 0..attr_nums {
            msgs.push(random_scalar(&mut rng));
        }
        let (A, e, s) = bbs.sign(&msgs);
    }

    #[test]
    fn test_verify() {
        let attr_nums = 5;
        let bbs = BBS::keygen(attr_nums);
        let mut msgs = Vec::new();
        let mut rng = thread_rng();

        for i in 0..attr_nums {
            msgs.push(random_scalar(&mut rng));
        }
        let (A, e, s) = bbs.clone().sign(&msgs);
        BBS::verify(&msgs, &A, &e, &s, &bbs.pk, &bbs.g1, &bbs.g2, &bbs.w);
    }

    #[test]
    fn test_spk_gen() {
        let attr_nums = 5;
        let bbs = BBS::keygen(attr_nums);
        let mut msgs = Vec::new();
        let mut rng = thread_rng();

        for i in 0..attr_nums {
            msgs.push(random_scalar(&mut rng));
        }
        let (A, e, s) = bbs.clone().sign(&msgs);
        let reveal_index = vec![2, 3, 4];

        BBS::gen_spk(&msgs, &A, &e, &s, &reveal_index, &bbs.pk, &bbs.g1);
    }

    #[test]
    fn test_spk_verify() {
        let attr_nums = 5;
        let bbs = BBS::keygen(attr_nums);
        let mut msgs = Vec::new();
        let mut rng = thread_rng();

        for i in 0..attr_nums {
            msgs.push(random_scalar(&mut rng));
        }
        let (A, e, s) = bbs.clone().sign(&msgs);
        let reveal_index = vec![2, 3, 4];

        let spk = BBS::gen_spk(&msgs, &A, &e, &s, &reveal_index, &bbs.pk, &bbs.g1);
        BBS::verify_spk(&msgs, reveal_index.clone(), &bbs.pk, &bbs.g1, spk, &bbs.w, &bbs.g2);
    }

    #[test]
    fn test_spk_gen_with_acc() {
        let attr_nums = 5;
        let bbs = BBS::keygen(attr_nums);
        let mut msgs = Vec::new();
        let mut rng = thread_rng();

        for i in 0..attr_nums {
            msgs.push(random_scalar(&mut rng));
        }
        let (A, e, s) = bbs.clone().sign(&msgs);
        let reveal_index = vec![2, 3, 4];

        let mut rng = thread_rng();
        let x = msgs[0];

        let acc = AccNa::setup().unwrap();
        let wx = acc.add(&x);
        let commiter = Commiter::default();

        BBS::gen_spk_with_acc(&msgs, &A, &e, &s, &reveal_index, &bbs.pk, &bbs.g1,&commiter, &wx,&acc);
    }

    #[test]
    fn test_spk_verify_with_acc() {
        let attr_nums = 5;
        let bbs = BBS::keygen(attr_nums);
        let mut msgs = Vec::new();
        let mut rng = thread_rng();

        for i in 0..attr_nums {
            msgs.push(random_scalar(&mut rng));
        }
        let (A, e, s) = bbs.clone().sign(&msgs);
        let reveal_index = vec![2, 3, 4];

        let mut rng = thread_rng();
        let x = msgs[0];

        let acc = AccNa::setup().unwrap();
        let wx = acc.add(&x);
        let commiter = Commiter::default();
        let (spk, zkp) = BBS::gen_spk_with_acc(&msgs, &A, &e, &s, &reveal_index, &bbs.pk, &bbs.g1,&commiter, &wx,&acc);
        BBS::verify_spk_with_acc(&msgs, reveal_index.clone(), &bbs.pk, &bbs.g1, spk, &bbs.w, &bbs.g2,&zkp,&acc,&commiter);
    }

    #[test]
    fn test_time_metrics() {
        let mut time_key_gen_sum = Duration::ZERO;
        let mut time_sign_sum = Duration::ZERO;
        let mut time_spk_gen_sum = Duration::ZERO;
        let mut time_spk_verify_sum = Duration::ZERO;
        let mut time_gen_spk_with_acc_sum = Duration::ZERO;
        let mut time_verify_spk_with_acc_sum = Duration::ZERO;

        for i in 0..100 {
            let attr_nums = 20;

            let start_key_gen = Instant::now();
            let bbs = BBS::keygen(attr_nums);
            let time_key_gen = start_key_gen.elapsed();
            time_key_gen_sum += time_key_gen;

            let mut msgs = Vec::new();
            let mut rng = thread_rng();

            for i in 0..attr_nums {
                msgs.push(random_scalar(&mut rng));
            }

            let start_sign = Instant::now();
            let (A, e, s) = bbs.clone().sign(&msgs);
            let reveal_index = vec![2, 3, 4];
            let time_sign = start_sign.elapsed();
            time_sign_sum += time_sign;

            let start_spk_gen = Instant::now();
            let spk_0 = BBS::gen_spk(&msgs, &A, &e, &s, &reveal_index, &bbs.pk, &bbs.g1);
            let time_spk_gen = start_spk_gen.elapsed();
            time_spk_gen_sum += time_spk_gen;

            let start_spk_verify = Instant::now();
            BBS::verify_spk(&msgs, reveal_index.clone(), &bbs.pk, &bbs.g1, spk_0, &bbs.w, &bbs.g2);
            let time_spk_verify = start_spk_verify.elapsed();
            time_spk_verify_sum += time_spk_verify;

            let x = msgs[0];

            let acc = AccNa::setup().unwrap();
            let wx = acc.add(&x);
            let commiter = Commiter::default();

            let start_gen_spk_with_acc = Instant::now();
            let (spk, zkp) = BBS::gen_spk_with_acc(&msgs, &A, &e, &s, &reveal_index, &bbs.pk, &bbs.g1,&commiter, &wx,&acc);
            let time_gen_spk_with_acc = start_gen_spk_with_acc.elapsed();
            time_gen_spk_with_acc_sum += time_gen_spk_with_acc;

            let start_verify_spk_with_acc = Instant::now();
            BBS::verify_spk_with_acc(&msgs, reveal_index.clone(), &bbs.pk, &bbs.g1, spk, &bbs.w, &bbs.g2,&zkp,&acc,&commiter);
            let time_verify_spk_with_acc = start_verify_spk_with_acc.elapsed();
            time_verify_spk_with_acc_sum += time_verify_spk_with_acc;
        }

        println!("The average time of key_gen() is {:#?}", time_key_gen_sum/100);
        println!("The average time of sign() is {:#?}", time_sign_sum/100);
        println!("The average time of spk_gen() is {:#?}", time_spk_gen_sum/100);
        println!("The average time of spk_verify() is {:#?}", time_spk_verify_sum/100);
        println!("The average time of spk_gen_with_acc() is {:#?}", time_gen_spk_with_acc_sum/100);
        println!("The average time of spk_verify_with_acc() is {:#?}", time_verify_spk_with_acc_sum/100);

    }

}