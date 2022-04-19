use std::fmt::Error;
use std::ops::{Add, Sub};
use bls12_381::{G1Affine, G1Projective, G2Affine, G2Projective, Scalar};
use rand::prelude::*;
use crate::accumulator::random_scalar;
use sha3::{Digest, Sha3_256};

/// this is a implementation for Pedersen Commitment
pub struct Commiter {
    pub(crate) g: G1Affine,
    pub(crate) h: G1Affine,
}


impl Default for Commiter {
    fn default() -> Self {
        let mut rng = thread_rng();
        let g_exponent = random_scalar(&mut rng);
        let h_exponent = random_scalar(&mut rng);

        let g = G1Affine::from(G1Affine::generator() * g_exponent);
        let h = G1Affine::from(G1Affine::generator() * h_exponent);

        Commiter {
            g,
            h,
        }
    }
}

impl Commiter {
    pub(crate) fn commit(&self, x: &Scalar, o_com: &Scalar) -> G1Affine {
        let C = (self.g * x).add(&(&self.h * o_com));

        G1Affine::from(C)
    }

    fn open(&self, x: &Scalar, o_com: &Scalar, C: &G1Affine) {
        assert_eq!(&G1Affine::from((self.g * x).add(&(&self.h * o_com))), C);
    }

    ///generate zero-knowledge proof of commitment
    ///  C = xG + o_comH
    ///  C_prime = aG + bH
    ///  t = hash (G,H,C_prime)
    ///  a_prime = a + tx
    ///  b_prime = b + tx
    pub(crate) fn zkp_gen(&self, x: &Scalar, o_com: &Scalar) -> (G1Affine, Scalar, Scalar) {
        let mut rng = thread_rng();

        let (a, b, C_prime, t) = loop
        {
            let a = random_scalar(&mut rng);
            let b = random_scalar(&mut rng);

            let C_prime = self.commit(&a, &b);
            let mut hasher = Sha3_256::new();

            ///Fiat-Shamir Heuristic
            let hash_data = C_prime.to_string() + &*self.g.to_string() + &*self.h.to_string();
            hasher.update(hash_data);

            let result = hasher.finalize();
            println!("{:?}", result);
            let flag = Scalar::from_bytes(result.as_ref()).is_none().unwrap_u8();

            if flag == 0 {
                break (a, b, C_prime, Scalar::from_bytes(result.as_ref()).unwrap());
            }
        };

        let a_prime = a.add(&(&t * x));
        let b_prime = b.add(&(&t * o_com));

        (C_prime, a_prime, b_prime)
    }

    ///verify the Pok of commitment
    /// a_prime * G + b_prime * H = C_prime + C * t
    fn zkp_verify(&self, c_prime: &G1Affine, a_prime: &Scalar, b_prime: &Scalar, c: &G1Affine) {
        let mut hasher = Sha3_256::new();

        ///Fiat-Shamir Heuristic
        let hash_data = c_prime.to_string() + &*self.g.to_string() + &*self.h.to_string();
        // hasher.update(C_prime.to_compressed());
        // hasher.update(self.g.to_compressed());
        // hasher.update(self.h.to_compressed());
        hasher.update(hash_data);

        let result = hasher.finalize();
        let t = Scalar::from_bytes(result.as_ref()).unwrap();
        println!("{:#?}", t);
        let res = G1Affine::from((c * t).add_mixed(c_prime));
        assert_eq!(self.commit(a_prime, b_prime), res);
    }
}

#[cfg(test)]
mod tests {
    use std::collections::BTreeMap;
    use rand::thread_rng;
    use crate::accumulator::random_scalar;
    use crate::commitment::{Commiter};



    #[test]
    fn test_commit() {
        let mut rng = thread_rng();
        let commitment = Commiter::default();

        let x = random_scalar(&mut rng);
        let o_com = random_scalar(&mut rng);
        let c = commitment.commit(&x, &o_com);

        commitment.open(&x, &o_com, &c);
    }

    #[test]
    fn test_zkp_gen() {
        let mut rng = thread_rng();
        let commitment = Commiter::default();

        let x = random_scalar(&mut rng);
        let o_com = random_scalar(&mut rng);
        let c = commitment.commit(&x, &o_com);
        let (C, a, b) = commitment.zkp_gen(&x, &o_com);
    }

    #[test]
    fn test_zkp_verify() {
        let mut rng = thread_rng();
        let commitment = Commiter::default();

        let x = random_scalar(&mut rng);
        let o_com = random_scalar(&mut rng);
        let c = commitment.commit(&x, &o_com);
        let (C, a, b) = commitment.zkp_gen(&x, &o_com);

        commitment.zkp_verify(&C, &a, &b, &c);
    }
}