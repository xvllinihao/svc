extern crate core;

mod accumulator;
mod Issuer;
mod Verifier;
mod Prover;
mod commitment;

use std::ops::{Add, Sub};
use bls12_381::*;
use rand::prelude::*;

fn main() {
    let g1 = G1Affine::generator();
    let g2 = G2Affine::generator();
    let mut rng = thread_rng();
    let a = Scalar::from(rng.gen_range(0..1000));
    let u = Scalar::from(rng.gen_range(0..1000));


    let v0 = g2 * u;

    let ga = g1 * a;

    let x = Scalar::from(rng.gen_range(0..1000));
    let gx = g1 * x;

    let wx = v0.clone();
    let inverse_xa = x.clone().add(&a).invert().unwrap();
    let xa = x.clone().add(&a);

    let wx = v0 * inverse_xa;

    let v0_prime = wx * xa;
    assert_eq!(v0_prime,v0);
    //

    let v0_affine=G2Affine::from(v0);
    let gx_affine = G1Affine::from(gx);
    let wx_affine = G2Affine::from(wx);
    let ga_gx = G1Affine::from(gx_affine.add(&ga));
    //
    assert_eq!(pairing(&g1,&v0_affine),pairing(&ga_gx,&wx_affine));



    println!("Hello, world!");
}
