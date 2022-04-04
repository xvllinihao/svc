use std::fmt::Error;
use std::ops::{Add, Sub};
use bls12_381::{G1Affine, G1Projective, G2Affine, G2Projective, Gt, pairing, Scalar};
use rand::prelude::*;
use sha3::{Digest, Sha3_256};
use crate::commitment::Commitment;


pub fn random_scalar(mut rng: &mut ThreadRng) -> Scalar {
    let mut buf = [0; 64];
    rng.fill_bytes(&mut buf);

    Scalar::from_bytes_wide(&buf)
}

pub(crate) struct ZkpProof {
    c:G1Projective,
    w1: G1Projective,
    w2: G1Projective,
    w1_r: G1Projective,
    R1:G1Projective,
    R2:G1Projective,
    R3:Gt,
    R4:G1Projective,
    s_r1:Scalar,
    s_r2:Scalar,
    s_delta1:Scalar,
    s_delta2:Scalar,
    s_x:Scalar,
    s_o_com:Scalar
}

pub(crate) struct AccNa {
    g1: G1Affine,
    g2: G2Affine,
    sk: Scalar,
    v0: G1Affine,
    ga: G2Affine,
}

// pub(crate) struct AccA {
//     pk:
//     sk:
// }


impl AccNa {
    /// wx = g1^(1/(x+a))
    /// v0 = g1^u0
    /// ga = g2^a
    fn setup() -> Result<AccNa, Error> {
        let mut rng = thread_rng();
        let g1 = G1Affine::generator();
        let g2 = G2Affine::generator();


        let sk = random_scalar(&mut rng);
        let u0 = random_scalar(&mut rng);

        let v0 = G1Affine::from(g1 * u0);
        let ga = G2Affine::from(g2 * sk);

        Ok(AccNa {
            g1,
            g2,
            sk,
            v0,
            ga,
        })
    }

    /// e(v0, g2) = e(wx, ga + gx)
    fn verify(x: &Scalar, wx: &G1Affine, v0: &G1Affine, ga: &G2Affine, g2: &G2Affine) -> bool {
        pairing(v0, g2) == pairing(wx, &G2Affine::from(&ga.add(g2 * x)))
    }

    fn add(&self, x: &Scalar) -> G1Affine {
        let inverse_xa = x.clone().add(&self.sk).invert().unwrap();

        let wx = G1Affine::from(self.v0 * inverse_xa);
        assert_eq!(AccNa::verify(x, &wx, &self.v0, &self.ga, &self.g2), true);
        wx
    }

    fn delete(&self, y: &Scalar) -> Result<AccNa, Error> {
        let gy = self.g1 * y;

        let inverse_ya = y.clone().add(&self.sk).invert().unwrap();

        let new_v0 = G1Affine::from(self.v0 * inverse_ya);

        Ok(AccNa {
            g1: self.g1,
            g2: self.g2,
            sk: self.sk,
            v0: new_v0,
            ga: self.ga,
        })
    }

    fn update_witness(wx: &G1Affine, x: &Scalar, y: &Scalar, new_v0: &G1Affine, ga: &G2Affine, g2: &G2Affine) -> G1Affine {
        let inverse_xy = x.sub(y).invert().unwrap();
        let inverse_yx = y.sub(x).invert().unwrap();


        let new_wx = (wx * inverse_yx).add(&(new_v0 * inverse_xy));
        assert_eq!(AccNa::verify(&x, &
            G1Affine::from(new_wx), new_v0, ga, g2), true);
        G1Affine::from(new_wx)
    }

    /// generate zkp of the membership
    fn gen_zkp(wx: &G1Affine, x: &Scalar, v0: &G1Affine, g2: &G2Affine, ga: &G2Affine, commiter: &Commitment)
               -> ZkpProof {
        //generate random values
        let mut rng = thread_rng();
        let r1 = random_scalar(&mut rng);
        let r2 = random_scalar(&mut rng);
        let w1 = (commiter.g * r1).add(&(&commiter.h * r2));
        let w1_r = w1 * x;


        let delta1 = x * r1;
        let delta2 = x * r2;


        let o_com = random_scalar(&mut rng);
        let c = (commiter.g * r1).add(&(&commiter.h * r2));
        let w2 = wx.add(&(commiter.g * r1));

        //generate blinding values
        let (blind_r1, blind_r2, R1, blind_delta1, blind_delat2, R2, R3
            , blind_x, blind_o_com, R4, c) = loop
        {
            let blind_r1 = random_scalar(&mut rng);
            let blind_r2 = random_scalar(&mut rng);
            let R1 = (commiter.g * blind_r1).add(&(&commiter.h * blind_r2));


            let blind_delta1 = random_scalar(&mut rng);
            let blind_delta2 = random_scalar(&mut rng);
            let R2 = (commiter.g * blind_delta1).add(&(&commiter.h * blind_delta2));

            let blind_x = random_scalar(&mut rng);
            let R3 = (pairing(&G1Affine::from(w2), g2) * blind_x)
                .add(pairing(&commiter.g, g2) * blind_delta1)
                .add(pairing(&commiter.g, ga) * blind_r1);


            let blind_o_com = random_scalar(&mut rng);
            let R4 = (commiter.g * blind_x).add(&(&commiter.h * blind_o_com));


            let mut hasher = Sha3_256::new();

            ///Fiat-Shamir Heuristic
            let hash_data = R1.to_string() + &*R2.to_string() +
                &*R3.to_string() + &*R4.to_string() +
                &*commiter.g.to_string() + &*commiter.h.to_string() +
                &*w1.to_string() + &*w1_r.to_string() + &*w2.to_string() + &*c.to_string();
            hasher.update(hash_data);

            let result = hasher.finalize();
            // println!("{:?}", result);
            let flag = Scalar::from_bytes(result.as_ref()).is_none().unwrap_u8();

            if flag == 0 {
                break (blind_r1, blind_r2, R1, blind_delta1, blind_delta2, R2, R3
                       , blind_x, blind_o_com, R4,
                       Scalar::from_bytes(result.as_ref()).unwrap());
            }
        };

        //generate values for proof
        let s_r1 = blind_r1.add(&(c * r1));
        let s_r2 = blind_r1.add(&(c * r2));
        let s_delta1 = blind_r1.add(&(c * delta1));
        let s_delta2 = blind_r1.add(&(c * delta2));
        let s_x = blind_r1.add(&(c * x));
        let s_o_com = blind_r1.add(&(c * o_com));

        let zkp_proof = ZkpProof{
            c,
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
            s_o_com
        };
        zkp_proof
    }

    pub fn verify_zkp(zkp_proof:&ZkpProof, g2: &G2Affine,
                      ga: &G2Affine, v0: &G1Affine, commiter:&Commitment
    ) -> bool {
        let mut hasher = Sha3_256::new();

        let (w, w1, w1_r, w2, R1, R2, R3, R4,
            s_r1, s_r2, s_delta1, s_delta2, s_x, s_o_com) = zkp_proof.unpack();
        //compute c
        let hash_data = R1.to_string() + &*R2.to_string() +
            &*R3.to_string() + &*R4.to_string() +
            &*commiter.g.to_string() + &*commiter.h.to_string();
        hasher.update(hash_data);

        let result = hasher.finalize();
        let c = Scalar::from_bytes(result.as_ref()).unwrap();

        let R1_prime = (commiter.g * s_r1).add(&(&commiter.h * s_r2));
        assert_eq!(R1.add_mixed(&G1Affine::from(w1 * c)), R1_prime);

        let R2_prime = (commiter.g * s_delta1).add(&(&commiter.h * s_delta2));
        assert_eq!(R2.add_mixed(&G1Affine::from(w1_r * c)), R2_prime);

        let inverse = Gt::identity().sub(pairing(v0, g2));
        let R3_prime = (pairing(&G1Affine::from(w2), ga).sub(inverse) * c).add(R3);
        let R3_p = (pairing(&G1Affine::from(w2), g2) * s_x)
            .add(pairing(&commiter.g, g2) * s_delta1)
            .add(pairing(&commiter.g, ga) * s_r1);
        assert_eq!(R3_prime, R3_p);

        let R4_prime = (commiter.g * s_x).add(&(&commiter.h * s_o_com));
        assert_eq!(R4.add_mixed(&G1Affine::from(w * c)), R4_prime);

        true
    }
}

impl ZkpProof {
    fn unpack(&self) -> (G1Projective, G1Projective, G1Projective, G1Projective,
                         G1Projective, G1Projective, Gt, G1Projective, Scalar,
                         Scalar, Scalar, Scalar, Scalar, Scalar) {
        (self.w, self.w1, self.w1_r, self.w2, self.R1,
         self.R2, self.R3, self.R4,
         self.s_r1, self.s_r2, self.s_delta1, self.s_delta2,
         self.s_x, self.s_o_com)
    }
}

#[cfg(test)]
mod tests {
    use rand::thread_rng;
    use crate::accumulator::{AccNa, random_scalar};
    use crate::commitment::Commitment;

    #[test]
    fn test_set_up() {
        AccNa::setup().unwrap();
    }

    #[test]
    fn test_add() {
        let mut rng = thread_rng();
        let x = random_scalar(&mut rng);

        let acc = AccNa::setup().unwrap();
        let wx = acc.add(&x);
    }

    #[test]
    fn test_delete() {
        let mut rng = thread_rng();
        let x = random_scalar(&mut rng);
        let y = random_scalar(&mut rng);

        let acc = AccNa::setup().unwrap();
        let wx = acc.add(&x);
        let wy = acc.add(&y);

        let new_acc = acc.delete(&y).unwrap();
    }

    #[test]
    fn test_update() {
        let mut rng = thread_rng();
        let x = random_scalar(&mut rng);
        let y = random_scalar(&mut rng);

        let acc = AccNa::setup().unwrap();
        let wx = acc.add(&x);
        let wy = acc.add(&y);

        let new_acc = acc.delete(&y).unwrap();
        let new_wx = AccNa::update_witness(&wx, &x, &y, &new_acc.v0, &acc.ga, &acc.g2);
    }

    #[test]
    fn test_zkp_gen() {
        let mut rng = thread_rng();
        let x = random_scalar(&mut rng);

        let acc = AccNa::setup().unwrap();
        let wx = acc.add(&x);
        let commiter = Commitment::default();
        let zkp = AccNa::gen_zkp(&wx, &x, &acc.v0, &acc.g2, &acc.ga, &commiter);
        assert_eq!(true, AccNa::verify_zkp(&zkp,&acc.g2,&acc.ga,&acc.v0,&commiter))
    }
}
