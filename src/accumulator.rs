use std::fmt::Error;
use std::ops::{Add, Sub};
use bls12_381::{G1Affine, G2Affine, G2Projective, pairing, Scalar};
use rand::prelude::*;
use crate::commitment::Commitment;


pub fn random_scalar(mut rng: &mut ThreadRng) -> Scalar {
    let mut buf = [0; 64];
    rng.fill_bytes(&mut buf);

    Scalar::from_bytes_wide(&buf)
}

pub(crate) struct AccNa {
    g1:G1Affine,
    g2:G2Affine,
    sk:Scalar,
    v0:G1Affine,
    ga:G2Affine,
}

// pub(crate) struct AccA {
//     pk:
//     sk:
// }


impl AccNa {
    fn setup() -> Result<AccNa, Error> {
        let mut rng = thread_rng();
        let g1 = G1Affine::generator();
        let g2 = G2Affine::generator();


        let sk = random_scalar(&mut rng);
        let u0 =  random_scalar(&mut rng);

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

    fn verify(x: &Scalar, wx: &G1Affine, v0:&G1Affine, ga:&G2Affine,g2:&G2Affine) -> bool {
        pairing(v0,g2) == pairing(wx, &G2Affine::from(&ga.add(g2 * x)))
    }

    fn add(&self, x: &Scalar) -> G1Affine{
        let inverse_xa = x.clone().add(&self.sk).invert().unwrap();

        let wx = G1Affine::from(self.v0 * inverse_xa);
        assert_eq!(AccNa::verify(x, &wx, &self.v0,&self.ga,&self.g2),true);
        wx
    }

    fn delete(&self, y:&Scalar) -> Result<AccNa, Error> {
        let gy = self.g1 * y;

        let inverse_ya = y.clone().add(&self.sk).invert().unwrap();

        let new_v0 = G1Affine::from(self.v0 * inverse_ya);

        Ok(AccNa{
            g1: self.g1,
            g2: self.g2,
            sk: self.sk,
            v0: new_v0,
            ga: self.ga,
        })
    }

    fn update_witness(wx:&G1Affine, x:&Scalar, y:&Scalar, new_v0:&G1Affine, ga:&G2Affine, g2:&G2Affine) -> G1Affine {
        let inverse_xy = x.sub(y).invert().unwrap();
        let inverse_yx = y.sub(x).invert().unwrap();


        let new_wx = (wx * inverse_yx).add(&(new_v0 * inverse_xy));
        assert_eq!(AccNa::verify(&x, &
            G1Affine::from(new_wx), new_v0,ga,g2),true);
        G1Affine::from(new_wx)
    }

    /// generate zkp of the membership
    fn gen_zkp(wx:&G1Affine, x:&Scalar, v0:&G1Affine) {
        //generate params
        let mut rng = thread_rng();
        let r1 = random_scalar(&mut rng);
        let r2 = random_scalar(&mut rng);
        let o_com = random_scalar(&mut rng);

        let commiter = Commitment::default();
        let w1 = commiter.commit(&r1,&r2);
        let delta1 = o_com * r1;
        let delta2 = o_com * r2;


        //generate zkp for w1
        let pok_w1 = commiter.zkp_gen(&r1, &r2);
        //generate zkp for w1ˆr
        let pok_w2 = commiter.zkp_gen(&delta1,&delta2);

        //generate zkp for pairings


        //generate zkp for commitment
        let pok_c = commiter.zkp_gen(x,&o_com);
    }


}


//
// pub fn zkp_membership(wx:&G2Affine, x:&Scalar,v0:&G2Affine) {
//     let mut rng = thread_rng();
//     let r1 = random_scalar(&mut rng);
//     let r2 = random_scalar(&mut rng);
//
//     let o_com = random_scalar(&mut rng);
//     let C =
// }

#[cfg(test)]
mod  tests {
    use rand::thread_rng;
    use crate::accumulator::{AccNa, random_scalar};

    #[test]
    fn test_set_up(){
        AccNa::setup().unwrap();
    }

    #[test]
    fn test_add(){
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
        let new_wx = AccNa::update_witness(&wx,&x,&y,&new_acc.v0,&acc.ga,&acc.g2);
    }
}
