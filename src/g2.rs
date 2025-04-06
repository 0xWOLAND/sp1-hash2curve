use substrate_bn::{arith::U256, AffineG2, Fq, Fq2, Fr, Group, G2};

use crate::{g1::HashToField, HashToCurve};

trait Conjugate {
    fn conjugate(self) -> Self;
}

impl Conjugate for Fq2 {
    fn conjugate(self) -> Self {
        Fq2::new(self.real(), -self.imaginary())
    }
}

impl Conjugate for G2 {
    fn conjugate(self) -> Self {
        G2::new(self.x().conjugate(), self.y().conjugate(), self.z().conjugate())
    }
}

fn psi(a: &AffineG2) -> AffineG2 {
    let a: G2 = (*a).into();
    let mut p = G2::one();

    let c0 = Fq::from_str("21575463638280843010398324269430826099269044274347216827212613867836435027261").unwrap();
    let c1 = Fq::from_str("10307601595873709700152284273816112264069230130616436755625194854815875713954").unwrap();     
    let endo_u = Fq2::new(c0, c1);

    let c0 = Fq::from_str("2821565182194536844548159561693502659359617185244120367078079554186484126554").unwrap();
    let c1 = Fq::from_str("3505843767911556378687030309984248845540243509899259641013678093033130930403").unwrap();
    let endo_v = Fq2::new(c0, c1);


    p = p.conjugate();

    p.set_x(p.x() * endo_u);
    p.set_y(p.y() * endo_v);

    p.into()
}

// https://github.com/Consensys/gnark-crypto/blob/master/ecc/bn254/g2.go#L635
fn clear_cofactor(q: AffineG2) -> AffineG2 {
    const X_GEN: u64 = 4965661367192848881;

    let mut points = [AffineG2::one();4];

    let x_gen_scalar = Fr::new(U256::from(X_GEN)).unwrap();

    points[0] = (G2::from(q) * x_gen_scalar).into();

    points[1] = (0..3).fold(G2::zero(), |acc, _| acc + points[0].into()).into();
    points[1] = psi(&points[1]);

    points[2] = psi(&points[0]);
    points[2] = psi(&points[2]);

    points[3] = psi(&q);
    points[3] = psi(&points[3]);
    points[3] = psi(&points[3]);

    points.iter().fold(G2::zero(), |acc, point| acc + (*point).into()).into()
}

impl HashToCurve for AffineG2 {
    type FieldElement = Fq2;

    fn sgn0(u: Fq2) -> u64 {
        let mut sign = 0u64;
        let mut zero = 1u64;


        let t: U256 = u.real().into_u256();
        let t0 = t.get_bit(0).unwrap();

        let mut sign_i = t0 as u64 & 1;
        let zero_i = ((t.0[0] as u64) == 0) as u64;

        sign = sign | (zero & sign_i);
        zero = zero & zero_i;

        let t: U256 = u.imaginary().into_u256();
        sign_i = t.0[0] as u64 & 1;
        sign = sign | (zero & sign_i);

        sign
    }
    
    fn map_to_curve(u: Fq2) -> Result<Self, substrate_bn::GroupError> {
        let z = Fq2::new(
            Fq::from_str("6350874878119819312338956282401532409788428879151445726012394534686998597021").unwrap(),
            Fq::from_str("0").unwrap()
        );

        let c1 = Fq2::new(
            Fq::from_str("1234912246041461878588942434875861039904126177810565185887158306408069993214").unwrap(), 
            Fq::from_str("568440292453150825972223760836185707764922522371208948902804025364325400423").unwrap()
        );

        let c2 = Fq2::new(
            Fq::from_str("7768683996859727954953724731427871339453941139073188968338321679979113805781").unwrap(), 
            Fq::from_str("0").unwrap()
        );

        let c3 = Fq2::new(
            Fq::from_str("14301738157933195389348253840724448307870907218086206201704502222609770096511").unwrap(), 
            Fq::from_str("18766576807588938823931941816656094168356257905513364070341807858523241306211").unwrap()
        );

        let c4 = Fq2::new(
            Fq::from_str("12945612253170900976712347250337035339258705867784462193943147521219390814770").unwrap(), 
            Fq::from_str("21130322481901740787616774064142360811676414460802878397485299194159459008019").unwrap()
        );
        
        let B = Fq2::new(
            Fq::from_str("19485874751759354771024239261021720505790618469301721065564631296452457478373").unwrap(), 
            Fq::from_str("266929791119991161246907387137283842545076965332900288569378510910307636690").unwrap()
        );


        let mut tv1 = u * u;       //    1.  tv1 = u²

        tv1 = tv1 * c1;                 //    2.  tv1 = tv1 * c1

        let tv2 = Fq2::one() + tv1;       //    3.  tv2 = 1 + tv1

        tv1 = Fq2::one() - tv1;           //    4.  tv1 = 1 - tv1
        let mut tv3 = tv1 * tv2;        //    5.  tv3 = tv1 * tv2

        tv3 = Fq2::one() / tv3;               //    6.  tv3 = inv0(tv3)
        let mut tv4 = u * tv1;          //    7.  tv4 = u * tv1
        tv4 = tv4 * tv3;                //    8.  tv4 = tv4 * tv3
        tv4 = tv4 * c3;                 //    9.  tv4 = tv4 * c3
        let x1 = c2 - tv4;              //    10.  x1 = c2 - tv4

        let mut gx1 = x1 * x1;      //    11. gx1 = x1²
        //12. gx1 = gx1 + A     All curves in gnark-crypto have A=0 (j-invariant=0). It is crucial to include this step if the curve has nonzero A coefficient.
        gx1 = gx1 * x1;                 //    13. gx1 = gx1 * x1
        gx1 = gx1 + B;              //    14. gx1 = gx1 + B

        let x2 = c2 + tv4;              //    15.  x2 = c2 + tv4
        let mut gx2 = x2 * x2;      //    16. gx2 = x2²
        //    17. gx2 = gx2 + A (see 12.)
        gx2 = gx2 * x2;                 //    18. gx2 = gx2 * x2
        gx2 = gx2 + B;              //    19. gx2 = gx2 + B

        let mut x3 = tv2 * tv2;      //    20.  x3 = tv2²
        x3 = x3 * tv3;                  //    21.  x3 = x3 * tv3
        x3 = x3 * x3;               //    22.  x3 = x3²
        x3 = x3 * c4;                   //    23.  x3 = x3 * c4

        x3 = x3 + z;                    //    24.  x3 = x3 + Z

        let mut x = if gx1.sqrt().is_some() {x1} else {x3};   //    25.   x = CMOV(x3, x1, e1)   # x = x1 if gx1 is square, else x = x3
        x = if gx2.sqrt().is_some() && !gx1.sqrt().is_some(){x2} else {x};      //    26.   x = CMOV(x, x2, e2)    # x = x2 if gx2 is square and gx1 is not

        let mut gx = x * x;        //    27.  gx = x²
        //    28.  gx = gx + A
        gx = gx * x;                    //    29.  gx = gx * x
        gx = gx + B;    //    30.  gx = gx + B

        let mut y = gx.sqrt().unwrap(); //    31.   y = sqrt(gx)

        let signs_not_equal = Self::sgn0(u) ^ Self::sgn0(y);  //    32.  e3 = sgn0(u) == sgn0(y)
        tv1 = Fq2::zero() - y;

        if signs_not_equal == 0 {y = y} else {y = tv1};   //    33.   y = CMOV(-y, y, e3)       # Select correct sign of y

        let res = AffineG2::new(x, y);

        res
    }
    
    fn hash(msg: &[u8], dst: &[u8]) -> Self {
        let u = Fq::hash_to_field(msg, dst, 4);

        let q0 = Self::map_to_curve(Fq2::new(u[0], u[1])).unwrap();
        let q1 = Self::map_to_curve(Fq2::new(u[2], u[3])).unwrap();

        let q = [q0, q1].iter().fold(G2::zero(), |acc, &q| acc + q.into()).into();
        
        clear_cofactor(q)
    }
}

trait Print {
    fn print(&self);
}

impl Print for Fq {
    fn print(&self) {
        let mut bytes = [0u8; 32];
        self.to_big_endian(&mut bytes).expect("Failed to convert Fq to big endian");
        bytes.reverse();
        println!("Fq bytes: {:?}", bytes);
    }
}

impl Print for Fq2 {
    fn print(&self) {
        let mut real_bytes = [0u8; 32];
        let mut imaginary_bytes = [0u8; 32];

        self.real().to_big_endian(&mut real_bytes).expect("Failed to convert real part to big endian");
        self.imaginary().to_big_endian(&mut imaginary_bytes).expect("Failed to convert imaginary part to big endian");

        real_bytes.reverse();
        imaginary_bytes.reverse();

        println!("Fq2 real part bytes: {:?}", real_bytes);
        println!("Fq2 imaginary part bytes: {:?}", imaginary_bytes);
    }
}
impl Print for AffineG2 {
    fn print(&self) {
        self.x().print();
        self.y().print();
    }
}


// #[cfg(test)]
// mod tests {
//     use super::*;

//     #[test]
//     fn test_map_to_curve() {
//         let R_inv: Fq = Fq::from_slice(&[14, 10, 119, 193, 154, 7, 223, 47, 102, 110, 163, 111, 120, 121, 70, 44, 10, 120, 235, 40, 245, 199, 11, 61, 211, 93, 67, 141, 197, 143, 13, 157]).unwrap();

//         let u = Fq2::new(
//             Fq::from_str("15963713818282906360305918686195491545577210390832157279818305179904408824931").unwrap() * R_inv,
//             Fq::from_str("2166278439352519416731010325104738631510195416620895094682522641528929475020").unwrap() * R_inv,
//         );

//         // let q = AffineG2::map_to_curve(u).unwrap();
//         // let expected = AffineG2::new(Fq2::new(
//         //     Fq::from_str("16872093352184426853297847012752141646605261411290781565485515569233955899058").unwrap(),
//         //     Fq::from_str("20482288690411193526247554560661659739533735966007371008469181348051437821826").unwrap()
//         // ), Fq2::new(
//         //     Fq::from_str("427035866446275812154335387235552457760650543923113579505536211797911740485").unwrap(),
//         //     Fq::from_str("14849552243024588631071292176876897701191437999604860450422231174965236442203").unwrap()
//         // )).unwrap();
//         // assert!(q == expected);

//         // let u = Fq2::new(
//         //     Fq::from_str("12752967732566665017975022503761080419696068755373050496264700974774108086129").unwrap(),
//         //     Fq::from_str("20655422394809824901799481664662586419100706577355794400212187554951433717414").unwrap()
//         // );

//         // let q = AffineG2::map_to_curve(u).unwrap();
//         // let expected = AffineG2::new(Fq2::new(
//         //     Fq::from_str("12193882055337081757241417044229479753659926309860257758224177044622322698984").unwrap(),
//         //     Fq::from_str("10092155993942609715417531227866448864240630219985669320168414926220064901453").unwrap()
//         // ), Fq2::new(
//         //     Fq::from_str("21850450548984866542151665069165216760882062028063278212318726360439829725223").unwrap(),
//         //     Fq::from_str("10197523149668572844555341938160230574503097016636734560718180396672437043430").unwrap()
//         // )).unwrap();
//         // assert!(q == expected);

//         // let u = Fq2::new(
//         //     Fq::from_str("18898141882839095816276844526801422247849121311000147859768000750276893266433").unwrap(),
//         //     Fq::from_str("3788127287937052767604234353437582991385298973804519256517508390161626404924").unwrap()
//         // );

//         // let q = AffineG2::map_to_curve(u).unwrap();
//         // let expected = AffineG2::new(Fq2::new(
//         //     Fq::from_str("452805888478466390914725495219599183584561454657558688011312346353060651482").unwrap(),
//         //     Fq::from_str("7959928416860499659800248632934402218020177178560427800377197797165640390130").unwrap()
//         // ), Fq2::new(
//         //     Fq::from_str("14268098188884406522254505541441598455366967966015814006726862271011081843493").unwrap(),
//         //     Fq::from_str("15148517265986515293057552799755027217326970615601185424102524485888012383276").unwrap()
//         // )).unwrap();
//         // assert!(q == expected);
//     }    

//     #[test]
//     fn test_hash_to_curve() {
//         let q = AffineG2::hash(b"abc", b"QUUX-V01-CS02-with-BN254G2_XMD:SHA-256_SVDW_RO_");
//         let expected = AffineG2::new(Fq2::new(
//             Fq::from_str("10305213714312555419584685236164610766057227018997600762219755820581571775698").unwrap(),
//             Fq::from_str("5140998983273781645596043003996621170933075714207210952317183701750931672829").unwrap()
//         ), Fq2::new(
//             Fq::from_str("12782657610222102886506935265351398708799194735435757564502179253917869011884").unwrap(),
//             Fq::from_str("15746452850775091549966312821847336261590899319279618339578671846526379873840").unwrap()
//         )).unwrap();
//         assert!(q == expected);
//     }
// }