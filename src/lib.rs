use substrate_bn::{AffineG1, Fr, GroupError};
use rand::{thread_rng, Rng};

pub mod g1;
pub mod g2;

pub trait HashToCurve: Sized {
    type FieldElement;
    fn sgn0(x: Self::FieldElement) -> u64;
    fn map_to_curve(u: Self::FieldElement) -> Result<Self, GroupError>;
    fn hash(msg: &[u8], dst: &[u8]) -> Self;
}

// Pedersen-style vector commitment
pub fn commit(vs: &[Fr], G: AffineG1, r: Fr) -> AffineG1 {
    let dst = b"QUUX-V01-CS02-with-BN254G1_XMD:SHA-256_SVDW_RO_";
    vs.iter().enumerate().fold(G * r, |acc, (i, &v)| {
        acc + AffineG1::hash(&i.to_le_bytes(), dst) * v
    })
}


#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_commit_additive_homomorphic() {
        let mut rng = thread_rng();

        let v1 = (0..10).map(|_| Fr::random(&mut rng)).collect::<Vec<_>>();
        let v2 = (0..10).map(|_| Fr::random(&mut rng)).collect::<Vec<_>>();
        let v_sum: Vec<Fr> = v1.iter().zip(&v2).map(|(&a, &b)| a + b).collect();

        let r1 = Fr::random(&mut rng);
        let r2 = Fr::random(&mut rng);
        let r_sum = r1 + r2;

        let G = AffineG1::default();

        let c1 = commit(&v1, G, r1);
        let c2 = commit(&v2, G, r2);
        let c_sum = commit(&v_sum, G, r_sum);

        assert_eq!(c_sum, c1 + c2);
    }

    #[test]
    fn test_commit_scalar_multiplication_homomorphic() {
        let mut rng = thread_rng();

        let v = (0..10).map(|_| Fr::random(&mut rng)).collect::<Vec<_>>();
        let scalar = Fr::random(&mut rng);
        let v_scaled: Vec<Fr> = v.iter().map(|&x| x * scalar).collect();

        let r = Fr::random(&mut rng);
        let G = AffineG1::default();

        let c = commit(&v, G, r);
        let c_scaled = commit(&v_scaled, G, r * scalar);

        assert_eq!(c_scaled, c * scalar);
    }
}