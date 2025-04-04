use digest::{consts::U32, generic_array::GenericArray};
use num_bigint::BigUint;
use substrate_bn::{AffineG1, Fq, GroupError};
use subtle::{Choice, ConditionallySelectable};
use sha2::{Sha256, digest::Digest};
use anyhow::Result;
use crate::HashToG1;

// https://www.ietf.org/archive/id/draft-irtf-cfrg-hash-to-curve-13.html#hashtofield
fn expand_message_xmd(msg: &[u8], dst: &[u8], LEN_IN_BYTES: usize) -> Vec<u8> {
    const B_IN_BYTES: usize = 32;
    const S_IN_BYTES: usize = 64;

    let ell = (LEN_IN_BYTES + B_IN_BYTES - 1) / B_IN_BYTES;

    assert!(ell <= 255, "len_in_bytes is too large");
    assert!(dst.len() <= 255, "dst is too large");
        
    let b_0 = Sha256::new()
        .chain_update([0u8; 64])    // s_in_bytes for sha256 = 64
        .chain_update(msg)
        .chain_update([(LEN_IN_BYTES >> 8) as u8, LEN_IN_BYTES as u8, 0u8])
        .chain_update(dst)
        .chain_update([dst.len() as u8])
        .finalize();

    let mut b_vals = Sha256::new()
        .chain_update(&b_0[..])
        .chain_update([1u8])
        .chain_update(dst)
        .chain_update([dst.len() as u8])
        .finalize();

    let mut buf = vec![0u8; LEN_IN_BYTES];
    let mut offset = 0;

    for i in 1..ell {
        // b_0 XOR b_(idx - 1)
        let mut tmp = GenericArray::<u8, U32>::default();
        b_0.iter()
            .zip(&b_vals[..])
            .enumerate()
            .for_each(|(j, (b0val, bi1val))| tmp[j] = b0val ^ bi1val);
        for b in b_vals {
            buf[offset % LEN_IN_BYTES].conditional_assign(
                &b,
                Choice::from(if offset < LEN_IN_BYTES { 1 } else { 0 }),
            );
            offset += 1;
        }
        b_vals = Sha256::new()
            .chain_update(tmp)
            .chain_update([(i + 1) as u8])
            .chain_update(dst)
            .chain_update([dst.len() as u8])
            .finalize();
    }
    for b in b_vals {
        buf[offset % LEN_IN_BYTES]
        .conditional_assign(&b, Choice::from(if offset < LEN_IN_BYTES { 1 } else { 0 }));
        offset += 1;
    }
    buf.into()
}

// https://www.ietf.org/archive/id/draft-irtf-cfrg-hash-to-curve-10.html#section-5.3
fn hash_to_field(msg: &[u8], dst: &[u8], count: usize) -> Vec<Fq> {
    const LEN_PER_ELM: usize = 48;
    let len_in_bytes = count * LEN_PER_ELM;

    let uniform_bytes = expand_message_xmd(msg, dst, len_in_bytes);

    (0..count)
        .map(|i| {
            let start = i * LEN_PER_ELM;
            let end = start + LEN_PER_ELM;
            Fq::from_slice(&uniform_bytes[start..end])
                .expect("Invalid field element encoding")
        })
        .collect()
}

trait Hash2Field {
    fn hash_to_field(msg: &[u8], dst: &[u8], count: usize) -> Vec<Fq>;
}

impl Hash2Field for Fq {
    fn hash_to_field(msg: &[u8], dst: &[u8], count: usize) -> Vec<Fq> {
        hash_to_field(msg, dst, count)
    }
}

impl HashToG1 for AffineG1 {
    type FieldElement = Fq;

    fn sgn0(x: Fq) -> u64 {
        let mut slice: [u8; 32] = [0; 32];
        x.to_big_endian(&mut slice).expect("Failed to convert Fq to big endian");
        slice[31] as u64 & 1
    }

    fn map_to_curve(u: Fq) -> Result<Self, GroupError> {
        let z: Fq = Fq::from_str("6350874878119819312338956282401532409788428879151445726012394534686998597021").unwrap();
        let c1: Fq = Fq::from_str("3515256640640002027109419384348854550457404359307959241360540244102768179501").unwrap();
        let c2: Fq = Fq::from_str("7768683996859727954953724731427871339453941139073188968338321679979113805781").unwrap();
        let c3: Fq = Fq::from_str("5174556184976127869173189452163337195348491024958816448391141365979064675186").unwrap();
        let c4: Fq = Fq::from_str("2609072103093089037936242735953952295622231240021995565748958972744717830193").unwrap();

        let mut tv1: Fq = u * u;       //    1.  tv1 = u²
        tv1 = tv1 * c1;                     //    2.  tv1 = tv1 * c1
        let tv2: Fq = Fq::one() + tv1;        //    3.  tv2 = 1 + tv1
        tv1 = Fq::one() - tv1;                //    4.  tv1 = 1 - tv1
        let mut tv3: Fq = tv1 * tv2;        //    5.  tv3 = tv1 * tv2 
        
        tv3 = tv3.inverse().unwrap();       //    6.  tv3 = inv0(tv3)
        let mut tv4: Fq = u * tv1;          //    7.  tv4 = u * tv1  
        tv4 = tv4 * tv3;                    //    8.  tv4 = tv4 * tv3
        tv4 = tv4 * c3;                     //    9.  tv4 = tv4 * c3
        let x1: Fq = c2 - tv4;              //    10.  x1 = c2 - tv4
        
        let mut gx1: Fq = x1 * x1;      //    11. gx1 = x1²
        //12. gx1 = gx1 + A  It is crucial to include this step if the curve has nonzero A coefficient.
        gx1 = gx1 * x1;                     //    13. gx1 = gx1 * x1    
        gx1 = gx1 + Fq::from_str("3").unwrap();            //    14. gx1 = gx1 + B
    
        let x2: Fq = c2 + tv4;              //    16.  x2 = c2 + tv4
        let mut gx2: Fq = x2 * x2;      //    17. gx2 = x2²
        //    18. gx2 = gx2 + A     See line 12
        gx2 = gx2 * x2;                     //    19. gx2 = gx2 * x2
        gx2 = gx2 + Fq::from_str("3").unwrap();            //    20. gx2 = gx2 + B
    
        let mut x3: Fq = tv2 * tv2;      //    22.  x3 = tv2²
        x3 = x3 * tv3;                      //    23.  x3 = x3 * tv3
        x3 = x3 * x3;                   //    24.  x3 = x3²
        x3 = x3 * c4;                       //    25.  x3 = x3 * c4
    
        x3 = x3 + z;                        //    26.  x3 = x3 + Z
    
        let mut x = if gx1.sqrt().is_some() { x1 } else { x3};

        if gx2.sqrt().is_some() && !gx1.sqrt().is_some() { x = x2 } //    28.   x = CMOV(x, x2, e2)    # x = x2 if gx2 is square and gx1 is not
        
        let mut gx = x * x;    //    29.  gx = x²
        //    30.  gx = gx + A
        gx = gx * x;                //    31.  gx = gx * x
        gx = gx + Fq::from_str("3").unwrap();      //    32.  gx = gx + B
    
        let mut y: Fq = gx.sqrt().unwrap();     //    33.   y = sqrt(gx)
    
    
        let signs_not_equal = Self::sgn0(u) ^ Self::sgn0(y);
    
        let tv1: Fq = Fq::zero() - y;
        if signs_not_equal == 0 {y = y} else {y = tv1}

        AffineG1::new(x, y)
    }

    fn hash(msg: &[u8], dst: &[u8]) -> Self {
        let u = Fq::hash_to_field(msg, dst, 2);
        let q_0 = Self::map_to_curve(u[0]).unwrap();
        let q_1 = Self::map_to_curve(u[1]).unwrap();
        let q = q_0 + q_1;
        q
    }
}