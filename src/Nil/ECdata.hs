{-# LANGUAGE BinaryLiterals #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# OPTIONS_GHC -Wno-orphans #-}

module Nil.Ecdata where

import Data.Store (Store)
import Nil.Curve
  ( Curve (..)
  , Point (..)
  , c'g
  )
import Nil.Data (NIL)
import Nil.Field
  ( Extensionfield (..)
  , Irreduciblepoly (..)
  , Primefield (..)
  , ef
  )

{- | BN254: old SNARKs Pairing Curve (*new SNARKs curve: BLS-12-381)
   Barreto-Naehrig (BN) curve, G1=E(Fq): y^2 = x^3 + b
   Twisted BN, G2=E'(Fq^2): y^2 = x^3 + b/xi  where xi = u + 9
   xi must be in Fq^2 and neither a square nor a cube.
-}
data BN254

{- | G1, G2 and GT are both curve types and field types.

   G1 = E(Fq)    <--  [twist]  -->   G2 = E'(Fq^2)
   y^2 = x^3 + (b=3)                 y^2 = x^3 + (b/xi = 3/u+9)

   G1, G2 and GT are basically indicating curves like G1=E(Fq) and G1=E(Fq^2)
   Hereafter, however, it was used as a field type throughout the program
   since it is an important characteristic of curve.
-}
type G1 =
  Primefield
    21888242871839275222246405745257275088696311157297823662689037894645226208583

{- | Fr is the prime field governing the zk-SNARKs circuit,
   Characteristic of Fr is exactly the same as the order of G1
-}
type Fr =
  Primefield
    21888242871839275222246405745257275088548364400416034343698204186575808495617

-- | G2 := Extensionfield G1[x] / <p(x)>  where p(x) = x^2 + 1
type G2 = Extensionfield G1 X

data X

-- GT := Extensionfield G1[u] / <p(u)>  where p(u) = x^12 -18 * x^6 + 82
type GT = Extensionfield G1 U

data U

deriving instance Store (Irreduciblepoly G1 X)

deriving instance Store G2

deriving instance Store (Irreduciblepoly G1 U)

deriving instance Store GT

deriving instance Store (Point BN254 G1)

deriving instance Store (Point BN254 G2)

deriving instance Store (Point BN254 GT)

deriving instance Store (Curve BN254 G1)

deriving instance Store (Curve BN254 G2)

deriving instance Store (Curve BN254 GT)

-- | Generator or base point on G1
g1 :: Point BN254 G1
g1 = c'g bn254'g1

-- | G2 field constructor
field'g2 :: [G1] -> G2
field'g2 = ef (I pX) where pX = [1 :: G1, 0, 1]

-- | Generator or base point on G2
g2 :: Point BN254 G2
g2 = c'g bn254'g2

-- | GT field constructor
field'gt :: [G1] -> GT
field'gt = ef (I pU) where pU = [82 :: G1, 0, 0, 0, 0, 0, -18, 0, 0, 0, 0, 0, 1]

-- | Generator or base point on GT
gt :: Point BN254 GT
gt = c'g bn254'gt

-- G1 = E(Fq): BN254 over base field Fq
bn254'g1 :: Curve BN254 G1
bn254'g1 =
  Curve
    { c'name = "BN254"
    , c'p =
        21888242871839275222246405745257275088696311157297823662689037894645226208583
    , c'a = 0
    , c'b = 3
    , c'gx = 1
    , c'gy = 2
    , c'n =
        21888242871839275222246405745257275088548364400416034343698204186575808495617
    , c'h = 1
    }

-- | G2 = E(Fq^2): BN254 twisted over Fq^2
bn254'g2 :: Curve BN254 G2
bn254'g2 =
  Curve
    { c'name = "BN254-Q2"
    , c'p =
        21888242871839275222246405745257275088696311157297823662689037894645226208583
    , c'a = field'g2 [0]
    , c'b = field'g2 [3] / field'g2 [9, 1]
    , c'gx =
        field'g2
          [ 10857046999023057135944570762232829481370756359578518086990519993285655852781
          , 11559732032986387107991004021392285783925812861821192530917403151452391805634
          ]
    , c'gy =
        field'g2
          [ 8495653923123431417604973247489272438418190587263600148770280649306958101930
          , 4082367875863433681332203403145435568316851327593401208105741076214120093531
          ]
    , c'n = c'n bn254'g1
    , c'h = 1
    }

{- | GT = E(Fq^12): BN254 over Fq12
 the r-th root of unity subgroup of the multiplicative Fq12 group
-}
bn254'gt :: Curve BN254 GT
bn254'gt =
  Curve
    { c'name = "BN254-Q12"
    , c'p =
        21888242871839275222246405745257275088696311157297823662689037894645226208583
    , c'a = field'gt [0]
    , c'b = field'gt [3]
    , c'gx =
        field'gt
          [ 0
          , 0
          , 16260673061341949275257563295988632869519996389676903622179081103440260644990
          , 0
          , 0
          , 0
          , 0
          , 0
          , 11559732032986387107991004021392285783925812861821192530917403151452391805634
          ]
    , c'gy =
        field'gt
          [ 0
          , 0
          , 0
          , 15530828784031078730107954109694902500959150953518636601196686752670329677317
          , 0
          , 0
          , 0
          , 0
          , 0
          , 4082367875863433681332203403145435568316851327593401208105741076214120093531
          ]
    , c'n = c'n bn254'g1
    , c'h = 1
    }

{- | e: G1 x G2 -> GT
 precomputation of pairing value: e(g1, g2)
-}
e'g1'g2 :: GT
e'g1'g2 =
  field'gt
    [ 18443897754565973717256850119554731228214108935025491924036055734000366132575
    , 10734401203193558706037776473742910696504851986739882094082017010340198538454
    , 5985796159921227033560968606339653189163760772067273492369082490994528765680
    , 4093294155816392700623820137842432921872230622290337094591654151434545306688
    , 642121370160833232766181493494955044074321385528883791668868426879070103434
    , 4527449849947601357037044178952942489926487071653896435602814872334098625391
    , 3758435817766288188804561253838670030762970764366672594784247447067868088068
    , 18059168546148152671857026372711724379319778306792011146784665080987064164612
    , 14656606573936501743457633041048024656612227301473084805627390748872617280984
    , 17918828665069491344039743589118342552553375221610735811112289083834142789347
    , 19455424343576886430889849773367397946457449073528455097210946839000147698372
    , 7484542354754424633621663080190936924481536615300815203692506276894207018007
    ]

{- | Baby jubjub
 A twisted Edwards elliptic curve E(Fr) where the char of Fr is the order of BN254
-}
data BabyJubjub

{- | Montgomery form of Baby Jubjub
 By^2 = x^3 + Ax^2 + x
 where A = 168698 and B = 1
 Generator point, (Gx, Gy) =
 (7, 4258727773875940690362607550498304598101071202821725296872974770776423442226)
 Base point, (Bx, By) =
 (7117928050407583618111176421555214756675765419608405867398403713213306743542,
  14577268218881899420966779687690205425227431577728659819975198491127179315626)
-}

{- | Coversion Montgomery form into Weierstrass form
 Weierstrass form: v^2 = t^3 + at + b
 point map: (x, y) -> (t, v) = (x/B - A/3B, y/B)
 a = (3 - A^2) / 3B^2
 b = (2A^3 - 9A) / 27B^3
-}
babyJub :: Curve BabyJubjub Fr
babyJub =
  Curve
    { c'name = "Baby Jubjub"
    , c'p =
        21888242871839275222246405745257275088548364400416034343698204186575808495617
    , c'a =
        7296080957279758407415468581752425029516121466805344781232734728849116493472
    , c'b =
        16213513238399463127589930181672055621146936592900766180517188641980520820846
    , c'gx =
        14414009007687342025526645003307639786191886886413750648631138442071909631647
    , c'gy =
        14577268218881899420966779687690205425227431577728659819975198491127179315626
    , c'n =
        2736030358979909402780800718157159386076813972158567259200215660948447373041
    , c'h = 8
    }

{- | secp256k1: Bitcoin Curve
 k = 19298681539552699237261830834781317975472927379845817397100860523586360249056
 r | q^k - 1, the embedding degree is very huge, not pairing-friendly curve.
-}
data Secp256k1

type Fp =
  Primefield
    115792089237316195423570985008687907853269984665640564039457584007908834671663

secp256k1 :: Curve Secp256k1 Fp
secp256k1 =
  Curve
    { c'name = "secp256k1"
    , c'p =
        115792089237316195423570985008687907853269984665640564039457584007908834671663
    , c'a = 0
    , c'b = 7
    , c'gx =
        55066263022277343669578718895168534326250603453777594175500187360389116729240
    , c'gy =
        32670510020758816978083085130507043184471273380659243275938904335757337482424
    , c'n =
        115792089237316195423570985008687907852837564279074904382605163141518161494337
    , c'h = 1
    }
