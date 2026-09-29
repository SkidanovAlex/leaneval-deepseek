import Mathlib
import Submission.Work.C17.seventeen_defs

set_option maxHeartbeats 4000000

/-! Definitions for the adjoint certificate (Work.C17.adjoint_no_solution). -/

namespace Work.C17

open Polynomial

noncomputable section

/-- `D = X^6(X-1)^2(X+1)^2 = X^10 - 2X^8 + X^6`. -/
def Dadj : Polynomial ℚ := C 1 * X^10 + C (-2) * X^8 + C 1 * X^6

def Dadj1 : Polynomial ℚ := C 10 * X^9 + C (-16) * X^7 + C 6 * X^5

def Dadj2 : Polynomial ℚ := C 90 * X^8 + C (-112) * X^6 + C 30 * X^4

/-- `B = 2 P2' - P1`. -/
def Badj (a b : ℚ) : Polynomial ℚ := C ((-1)) + C ((8)*a*b) * X^1 + C ((13) + (-12)*b^2 + (-12)*a^2) * X^2 + C ((-16)*a*b) * X^3 + C ((-23) + (36)*b^2 + (36)*a^2) * X^4 + C ((-40)*a*b) * X^5 + C ((11)) * X^6

/-- `C = P2'' - P1' + P0`. -/
def Cadj (a b : ℚ) : Polynomial ℚ := C (a*b) + C ((9) + (-3)*b^2 + (-3)*a^2) * X^1 + C ((-40)*a*b) * X^2 + C ((-34) + (63)*b^2 + (63)*a^2) * X^3 + C ((-81)*a*b) * X^4 + C ((25)) * X^5

def Npoly (n : Fin 7 → ℚ) : Polynomial ℚ := ∑ k : Fin 7, C (n k) * X ^ (k : ℕ)

def NpolyD (n : Fin 7 → ℚ) : Polynomial ℚ := ∑ k : Fin 7, C ((k : ℕ) * n k) * X ^ ((k : ℕ) - 1)

def NpolyDD (n : Fin 7 → ℚ) : Polynomial ℚ := ∑ k : Fin 7, C (((k:ℕ) * ((k:ℕ) - 1)) * n k) * X ^ ((k : ℕ) - 2)

/-- `g_i · D^3 = x^{2i+11}(x-2)(x-1)^{8-i}(x+1)^6`. -/
def gD3_0 : Polynomial ℚ := C ((-2)) * X^11 + C ((5)) * X^12 + C ((8)) * X^13 + C ((-29)) * X^14 + C ((-6)) * X^15 + C ((69)) * X^16 + C ((-20)) * X^17 + C ((-85)) * X^18 + C ((50)) * X^19 + C ((55)) * X^20 + C ((-48)) * X^21 + C ((-15)) * X^22 + C ((22)) * X^23 + C ((-1)) * X^24 + C ((-4)) * X^25 + C ((1)) * X^26

def gD3_1 : Polynomial ℚ := C ((2)) * X^13 + C ((-3)) * X^14 + C ((-11)) * X^15 + C ((18)) * X^16 + C ((24)) * X^17 + C ((-45)) * X^18 + C ((-25)) * X^19 + C ((60)) * X^20 + C ((10)) * X^21 + C ((-45)) * X^22 + C ((3)) * X^23 + C ((18)) * X^24 + C ((-4)) * X^25 + C ((-3)) * X^26 + C ((1)) * X^27

def gD3_2 : Polynomial ℚ := C ((-2)) * X^15 + C ((1)) * X^16 + C ((12)) * X^17 + C ((-6)) * X^18 + C ((-30)) * X^19 + C ((15)) * X^20 + C ((40)) * X^21 + C ((-20)) * X^22 + C ((-30)) * X^23 + C ((15)) * X^24 + C ((12)) * X^25 + C ((-6)) * X^26 + C ((-2)) * X^27 + C ((1)) * X^28

def gD3_3 : Polynomial ℚ := C ((2)) * X^17 + C ((1)) * X^18 + C ((-11)) * X^19 + C ((-5)) * X^20 + C ((25)) * X^21 + C ((10)) * X^22 + C ((-30)) * X^23 + C ((-10)) * X^24 + C ((20)) * X^25 + C ((5)) * X^26 + C ((-7)) * X^27 + C ((-1)) * X^28 + C ((1)) * X^29

def gD3_4 : Polynomial ℚ := C ((-2)) * X^19 + C ((-3)) * X^20 + C ((8)) * X^21 + C ((13)) * X^22 + C ((-12)) * X^23 + C ((-22)) * X^24 + C ((8)) * X^25 + C ((18)) * X^26 + C ((-2)) * X^27 + C ((-7)) * X^28 + C ((1)) * X^30

def gD3_5 : Polynomial ℚ := C ((2)) * X^21 + C ((5)) * X^22 + C ((-3)) * X^23 + C ((-16)) * X^24 + C ((-4)) * X^25 + C ((18)) * X^26 + C ((10)) * X^27 + C ((-8)) * X^28 + C ((-6)) * X^29 + C ((1)) * X^30 + C ((1)) * X^31

def gD3 : Fin 6 → Polynomial ℚ := ![gD3_0, gD3_1, gD3_2, gD3_3, gD3_4, gD3_5]

/-- The cleared numerator of `M*β - Σ c_i g_i` for `β = N/D`. -/
def Epoly (a b : ℚ) (n : Fin 7 → ℚ) (c : Fin 6 → ℚ) : Polynomial ℚ :=
  P2x a b * (NpolyDD n * Dadj^2 - Npoly n * Dadj * Dadj2 - 2 * NpolyD n * Dadj * Dadj1
      + 2 * Npoly n * Dadj1^2)
    + Badj a b * (Dadj * (NpolyD n * Dadj - Npoly n * Dadj1))
    + Cadj a b * (Dadj^2 * Npoly n)
    - ∑ i : Fin 6, C (c i) * gD3 i

/-- The linear forms `L_d` (coefficient of `X^d` in the cleared identity). -/
def Lform (a b : ℚ) (n : Fin 7 → ℚ) (c : Fin 6 → ℚ) : ℕ → ℚ
  | 11 => ((-36)) * (n 0) + ((2)) * (c 0)
  | 12 => ((121)*a*b) * (n 0) + ((-25)) * (n 1) + ((-5)) * (c 0)
  | 13 => ((241)+(-99)*b^2+(-99)*a^2) * (n 0) + ((81)*a*b) * (n 1) + ((-16)) * (n 2) + ((-8)) * (c 0) + ((-2)) * (c 1)
  | 14 => ((-572)*a*b) * (n 0) + ((166)+(-63)*b^2+(-63)*a^2) * (n 1) + ((49)*a*b) * (n 2) + ((-9)) * (n 3) + ((29)) * (c 0) + ((3)) * (c 1)
  | 15 => ((-690)+(539)*b^2+(539)*a^2) * (n 0) + ((-396)*a*b) * (n 1) + ((105)+(-35)*b^2+(-35)*a^2) * (n 2) + ((25)*a*b) * (n 3) + ((-4)) * (n 4) + ((6)) * (c 0) + ((11)) * (c 1) + ((2)) * (c 2)
  | 16 => ((957)*a*b) * (n 0) + ((-471)+(351)*b^2+(351)*a^2) * (n 1) + ((-252)*a*b) * (n 2) + ((58)+(-15)*b^2+(-15)*a^2) * (n 3) + ((9)*a*b) * (n 4) + ((-1)) * (n 5) + ((-69)) * (c 0) + ((-18)) * (c 1) + ((-1)) * (c 2)
  | 17 => ((1095)+(-1166)*b^2+(-1166)*a^2) * (n 0) + ((693)*a*b) * (n 1) + ((-294)+(203)*b^2+(203)*a^2) * (n 2) + ((-140)*a*b) * (n 3) + ((25)+(-3)*b^2+(-3)*a^2) * (n 4) + (a*b) * (n 5) + ((20)) * (c 0) + ((-24)) * (c 1) + ((-12)) * (c 2) + ((-2)) * (c 3)
  | 18 => ((-528)*a*b) * (n 0) + ((740)+(-774)*b^2+(-774)*a^2) * (n 1) + ((469)*a*b) * (n 2) + ((-159)+(95)*b^2+(95)*a^2) * (n 3) + ((-60)*a*b) * (n 4) + ((6)+b^2+a^2) * (n 5) + (a*b) * (n 6) + ((85)) * (c 0) + ((45)) * (c 1) + ((6)) * (c 2) + ((-1)) * (c 3)
  | 19 => ((-1040)+(1254)*b^2+(1254)*a^2) * (n 0) + ((-432)*a*b) * (n 1) + ((455)+(-462)*b^2+(-462)*a^2) * (n 2) + ((285)*a*b) * (n 3) + ((-66)+(27)*b^2+(27)*a^2) * (n 4) + ((-12)*a*b) * (n 5) + (1+(-3)*b^2+(-3)*a^2) * (n 6) + ((-50)) * (c 0) + ((25)) * (c 1) + ((30)) * (c 2) + ((11)) * (c 3) + ((2)) * (c 4)
  | 20 => ((-253)*a*b) * (n 0) + ((-695)+(846)*b^2+(846)*a^2) * (n 1) + ((-336)*a*b) * (n 2) + ((240)+(-230)*b^2+(-230)*a^2) * (n 3) + ((141)*a*b) * (n 4) + ((-15)+(-1)*b^2+(-1)*a^2) * (n 5) + ((4)*a*b) * (n 6) + ((-55)) * (c 0) + ((-60)) * (c 1) + ((-15)) * (c 2) + ((5)) * (c 3) + ((3)) * (c 4)
  | 21 => ((591)+(-671)*b^2+(-671)*a^2) * (n 0) + ((-117)*a*b) * (n 1) + ((-420)+(518)*b^2+(518)*a^2) * (n 2) + ((-240)*a*b) * (n 3) + ((95)+(-78)*b^2+(-78)*a^2) * (n 4) + ((37)*a*b) * (n 5) + ((-6)+(11)*b^2+(11)*a^2) * (n 6) + ((48)) * (c 0) + ((-10)) * (c 1) + ((-40)) * (c 2) + ((-25)) * (c 3) + ((-8)) * (c 4) + ((-2)) * (c 5)
  | 22 => ((396)*a*b) * (n 0) + ((390)+(-459)*b^2+(-459)*a^2) * (n 1) + ((-21)*a*b) * (n 2) + ((-215)+(270)*b^2+(270)*a^2) * (n 3) + ((-144)*a*b) * (n 4) + ((20)+(-6)*b^2+(-6)*a^2) * (n 5) + ((-27)*a*b) * (n 6) + ((15)) * (c 0) + ((45)) * (c 1) + ((20)) * (c 2) + ((-10)) * (c 3) + ((-13)) * (c 4) + ((-5)) * (c 5)
  | 23 => ((-186)+(143)*b^2+(143)*a^2) * (n 0) + ((252)*a*b) * (n 1) + ((231)+(-287)*b^2+(-287)*a^2) * (n 2) + ((35)*a*b) * (n 3) + ((-80)+(102)*b^2+(102)*a^2) * (n 4) + ((-48)*a*b) * (n 5) + ((15)+(-14)*b^2+(-14)*a^2) * (n 6) + ((-22)) * (c 0) + ((-3)) * (c 1) + ((30)) * (c 2) + ((30)) * (c 3) + ((12)) * (c 4) + ((3)) * (c 5)
  | 24 => ((-121)*a*b) * (n 0) + ((-121)+(99)*b^2+(99)*a^2) * (n 1) + ((140)*a*b) * (n 2) + ((114)+(-155)*b^2+(-155)*a^2) * (n 3) + ((51)*a*b) * (n 4) + ((-15)+(14)*b^2+(14)*a^2) * (n 5) + ((48)*a*b) * (n 6) + (1) * (c 0) + ((-18)) * (c 1) + ((-15)) * (c 2) + ((10)) * (c 3) + ((22)) * (c 4) + ((16)) * (c 5)
  | 25 => ((25)) * (n 0) + ((-81)*a*b) * (n 1) + ((-70)+(63)*b^2+(63)*a^2) * (n 2) + ((60)*a*b) * (n 3) + ((39)+(-63)*b^2+(-63)*a^2) * (n 4) + ((27)*a*b) * (n 5) + ((-20)+(6)*b^2+(6)*a^2) * (n 6) + ((4)) * (c 0) + ((4)) * (c 1) + ((-12)) * (c 2) + ((-20)) * (c 3) + ((-8)) * (c 4) + ((4)) * (c 5)
  | 26 => ((16)) * (n 1) + ((-49)*a*b) * (n 2) + ((-33)+(35)*b^2+(35)*a^2) * (n 3) + ((12)*a*b) * (n 4) + ((6)+(-11)*b^2+(-11)*a^2) * (n 5) + ((-37)*a*b) * (n 6) + ((-1)) * (c 0) + ((3)) * (c 1) + ((6)) * (c 2) + ((-5)) * (c 3) + ((-18)) * (c 4) + ((-18)) * (c 5)
  | 27 => ((9)) * (n 2) + ((-25)*a*b) * (n 3) + ((-10)+(15)*b^2+(15)*a^2) * (n 4) + ((-4)*a*b) * (n 5) + ((15)+b^2+a^2) * (n 6) + ((-1)) * (c 1) + ((2)) * (c 2) + ((7)) * (c 3) + ((2)) * (c 4) + ((-10)) * (c 5)
  | 28 => ((4)) * (n 3) + ((-9)*a*b) * (n 4) + ((-1)+(3)*b^2+(3)*a^2) * (n 5) + ((12)*a*b) * (n 6) + ((-1)) * (c 2) + (1) * (c 3) + ((7)) * (c 4) + ((8)) * (c 5)
  | 29 => (1) * (n 4) + ((-1)*a*b) * (n 5) + ((-6)+(-1)*b^2+(-1)*a^2) * (n 6) + ((-1)) * (c 3) + ((6)) * (c 5)
  | 30 => ((-1)*a*b) * (n 6) + ((-1)) * (c 4) + ((-1)) * (c 5)
  | 31 => (1) * (n 6) + ((-1)) * (c 5)
  | _ => 0

/-- `G = Σ_d L_d X^d`, the explicit form of `Epoly`. -/
def Gpoly (a b : ℚ) (n : Fin 7 → ℚ) (c : Fin 6 → ℚ) : Polynomial ℚ :=
  ∑ d ∈ Finset.Icc 11 31, C (Lform a b n c d) * X ^ d

/-- `Ψ_8(a,b)`: the obstruction (sign chosen so that `Ψ_8(a,b) ≠ 0` at admissible pairs). -/
def Psib (a b : ℚ) : ℚ := - 59290*a^6*b^2 + 185493*a^5*b^3 - 8491*a^5*b - 249865*a^4*b^4 + 65541*a^4*b^2 + 6090*a^4 + 185493*a^3*b^5 - 119686*a^3*b^3 - 15225*a^3*b - 59290*a^2*b^6 + 65541*a^2*b^4 + 21000*a^2*b^2 - 975*a^2 - 8491*a*b^5 - 15225*a*b^3 + 4260*a*b + 6090*b^4 - 975*b^2 - 1755

/-- The 4x4 determinant of the reduced system (explicit). -/
def Pdet4 (a b : ℚ) : ℚ := ((-117/16)*b^4+(117/8)*a^2*b^2+(-117/16)*a^4+(-65/16)*b^6+(71/4)*a*b^5+(65/16)*a^2*b^4+(-71/2)*a^3*b^3+(65/16)*a^4*b^2+(71/4)*a^5*b+(-65/16)*a^6+(203/8)*b^8+(-1015/16)*a*b^7+(147/4)*a^2*b^6+(1015/16)*a^3*b^5+(-497/4)*a^4*b^4+(1015/16)*a^5*b^3+(147/4)*a^6*b^2+(-1015/16)*a^7*b+(203/8)*a^8+(-8491/240)*a*b^9+(21847/80)*a^2*b^8+(-6419/15)*a^3*b^7+(-21847/80)*a^4*b^6+(7413/8)*a^5*b^5+(-21847/80)*a^6*b^4+(-6419/15)*a^7*b^3+(21847/80)*a^8*b^2+(-8491/240)*a^9*b+(-5929/24)*a^2*b^10+(61831/80)*a^3*b^9+(-26257/48)*a^4*b^8+(-61831/80)*a^5*b^7+(12705/8)*a^6*b^6+(-61831/80)*a^7*b^5+(-26257/48)*a^8*b^4+(61831/80)*a^9*b^3+(-5929/24)*a^10*b^2)

/-- `Pdet = det` of the 4x4 reduced system `= -(a^2-b^2)^2 Ψ_8`. -/
def Pdet (a b : ℚ) : ℚ := -((a^2 - b^2)^2 * Psib a b) / 240

/-- The base change `ℚ(x) → ℂ(x)`. -/
def toC (β : RatFunc ℚ) : RatFunc ℂ :=
  algebraMap (Polynomial ℂ) (RatFunc ℂ) (β.num.map (algebraMap ℚ ℂ))
    / algebraMap (Polynomial ℂ) (RatFunc ℂ) (β.denom.map (algebraMap ℚ ℂ))

/-- The `ℂ`-images of the coefficient polynomials of `M*`. -/
def P2Cc (a b : ℚ) : Polynomial ℂ := (P2x a b).map (algebraMap ℚ ℂ)
def P1Cc (a b : ℚ) : Polynomial ℂ := (P1x a b).map (algebraMap ℚ ℂ)
def P0Cc (a b : ℚ) : Polynomial ℂ := (P0x a b).map (algebraMap ℚ ℂ)
def Pac (a b : ℚ) : RatFunc ℂ := algebraMap (Polynomial ℂ) (RatFunc ℂ) (P2Cc a b)
def Pbc (a b : ℚ) : RatFunc ℂ := algebraMap (Polynomial ℂ) (RatFunc ℂ) (P1Cc a b)
def Pcc (a b : ℚ) : RatFunc ℂ := algebraMap (Polynomial ℂ) (RatFunc ℂ) (P0Cc a b)
def yQc : RatFunc ℂ := (algebraMap (Polynomial ℂ) (RatFunc ℂ) X)^2 / (algebraMap (Polynomial ℂ) (RatFunc ℂ) (X - 1))
def dyQc : RatFunc ℂ := ((algebraMap (Polynomial ℂ) (RatFunc ℂ) X)^2 - 2*(algebraMap (Polynomial ℂ) (RatFunc ℂ) X)) / (algebraMap (Polynomial ℂ) (RatFunc ℂ) (X - 1))^2
def DadjC : RatFunc ℂ := algebraMap (Polynomial ℂ) (RatFunc ℂ) (Dadj.map (algebraMap ℚ ℂ))

/-- The `ℚ`-version of the RHS of the equation. -/
def yQ1 : RatFunc ℚ := (algebraMap (Polynomial ℚ) (RatFunc ℚ) X)^2 / (algebraMap (Polynomial ℚ) (RatFunc ℚ) (X - 1))
def dyQ1 : RatFunc ℚ := ((algebraMap (Polynomial ℚ) (RatFunc ℚ) X)^2 - 2*(algebraMap (Polynomial ℚ) (RatFunc ℚ) X)) / (algebraMap (Polynomial ℚ) (RatFunc ℚ) (X - 1))^2

end

end Work.C17