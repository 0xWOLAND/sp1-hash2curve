use substrate_bn::GroupError;

pub mod g1;
pub mod g2;

pub trait HashToCurve: Sized {
    type FieldElement;
    fn sgn0(x: Self::FieldElement) -> u64;
    fn map_to_curve(u: Self::FieldElement) -> Result<Self, GroupError>;
    fn hash(msg: &[u8], dst: &[u8]) -> Self;
}
