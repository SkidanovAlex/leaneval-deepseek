
import Mathlib
import Submission.Work.C17.adjoint_defs

/-!
# The adjoint certificate over `ℂ` (literal `ℂ`-copies of the `ℚ`-data)

`Work.C17C` holds literal `ℂ`-copies (`Q4xL, P2xL, P1xL, P0xL, BadjL, CadjL, DadjL, Dadj1L, Dadj2L,
gD3L, NpolyL, NpolyDL, NpolyDDL, LformL, PsibL, Pdet4L`) of the `ℚ`-data of
`Submission.Work.C17.adjoint_defs` / `seventeen_defs`, together with the certificate polynomials
`LeftPolyL, RightPolyL, EpolyL` and `GpolyL`, and the bridges identifying them with the base changes
of their `ℚ`-counterparts.

The point of the literal copies is that the (machine generated, 128-step) certificate
`Work.C17.linear_core` of `Submission/Work/C17/adjoint_core.lean` can be replayed verbatim over `ℂ`:
every `linear_combination` step is a *ring* identity with rational coefficients in the parameters
`a, b`, hence field independent.
-/

namespace Work.C17C

open Polynomial

noncomputable section

set_option maxHeartbeats 1000000
def Q4xL (a b : ℂ) : Polynomial ℂ :=
  1 - C (4 * a * b) * X + C (4 * a ^ 2 + 4 * b ^ 2 - 2) * X ^ 2
    - C (4 * a * b) * X ^ 3 + X ^ 4

def P2xL (a b : ℂ) : Polynomial ℂ := (X - 1) * X * (X + 1) * Q4xL a b

def P1xL (a b : ℂ) : Polynomial ℂ :=
  - (1 : Polynomial ℂ) + C (8 * a * b) * X + C (5 - 12 * a ^ 2 - 12 * b ^ 2) * X ^ 2
    + C (16 * a * b) * X ^ 3 + C (4 * a ^ 2 + 4 * b ^ 2 - 7) * X ^ 4
    - C (8 * a * b) * X ^ 5 + C 3 * X ^ 6

def P0xL (a b : ℂ) : Polynomial ℂ :=
  C (a * b) + C (1 - 3 * a ^ 2 - 3 * b ^ 2) * X + C (8 * a * b) * X ^ 2
    - C (a ^ 2 + b ^ 2 + 2) * X ^ 3 - C (a * b) * X ^ 4 + X ^ 5

def BadjL (a b : ℂ) : Polynomial ℂ := C ((-1)) + C ((8)*a*b) * X^1 + C ((13) + (-12)*b^2 + (-12)*a^2) * X^2 + C ((-16)*a*b) * X^3 + C ((-23) + (36)*b^2 + (36)*a^2) * X^4 + C ((-40)*a*b) * X^5 + C ((11)) * X^6

def CadjL (a b : ℂ) : Polynomial ℂ := C (a*b) + C ((9) + (-3)*b^2 + (-3)*a^2) * X^1 + C ((-40)*a*b) * X^2 + C ((-34) + (63)*b^2 + (63)*a^2) * X^3 + C ((-81)*a*b) * X^4 + C ((25)) * X^5

def DadjL : Polynomial ℂ := C 1 * X^10 + C (-2) * X^8 + C 1 * X^6

def Dadj1L : Polynomial ℂ := C 10 * X^9 + C (-16) * X^7 + C 6 * X^5

def Dadj2L : Polynomial ℂ := C 90 * X^8 + C (-112) * X^6 + C 30 * X^4

def NpolyL (n : Fin 7 → ℂ) : Polynomial ℂ := ∑ k : Fin 7, C (n k) * X ^ (k : ℕ)

def NpolyDL (n : Fin 7 → ℂ) : Polynomial ℂ := ∑ k : Fin 7, C ((k : ℕ) * n k) * X ^ ((k : ℕ) - 1)

def NpolyDDL (n : Fin 7 → ℂ) : Polynomial ℂ := ∑ k : Fin 7, C (((k:ℕ) * ((k:ℕ) - 1)) * n k) * X ^ ((k : ℕ) - 2)

def gD3L_0 : Polynomial ℂ := C ((-2)) * X^11 + C ((5)) * X^12 + C ((8)) * X^13 + C ((-29)) * X^14 + C ((-6)) * X^15 + C ((69)) * X^16 + C ((-20)) * X^17 + C ((-85)) * X^18 + C ((50)) * X^19 + C ((55)) * X^20 + C ((-48)) * X^21 + C ((-15)) * X^22 + C ((22)) * X^23 + C ((-1)) * X^24 + C ((-4)) * X^25 + C ((1)) * X^26

def gD3L_1 : Polynomial ℂ := C ((2)) * X^13 + C ((-3)) * X^14 + C ((-11)) * X^15 + C ((18)) * X^16 + C ((24)) * X^17 + C ((-45)) * X^18 + C ((-25)) * X^19 + C ((60)) * X^20 + C ((10)) * X^21 + C ((-45)) * X^22 + C ((3)) * X^23 + C ((18)) * X^24 + C ((-4)) * X^25 + C ((-3)) * X^26 + C ((1)) * X^27

def gD3L_2 : Polynomial ℂ := C ((-2)) * X^15 + C ((1)) * X^16 + C ((12)) * X^17 + C ((-6)) * X^18 + C ((-30)) * X^19 + C ((15)) * X^20 + C ((40)) * X^21 + C ((-20)) * X^22 + C ((-30)) * X^23 + C ((15)) * X^24 + C ((12)) * X^25 + C ((-6)) * X^26 + C ((-2)) * X^27 + C ((1)) * X^28

def gD3L_3 : Polynomial ℂ := C ((2)) * X^17 + C ((1)) * X^18 + C ((-11)) * X^19 + C ((-5)) * X^20 + C ((25)) * X^21 + C ((10)) * X^22 + C ((-30)) * X^23 + C ((-10)) * X^24 + C ((20)) * X^25 + C ((5)) * X^26 + C ((-7)) * X^27 + C ((-1)) * X^28 + C ((1)) * X^29

def gD3L_4 : Polynomial ℂ := C ((-2)) * X^19 + C ((-3)) * X^20 + C ((8)) * X^21 + C ((13)) * X^22 + C ((-12)) * X^23 + C ((-22)) * X^24 + C ((8)) * X^25 + C ((18)) * X^26 + C ((-2)) * X^27 + C ((-7)) * X^28 + C ((1)) * X^30

def gD3L_5 : Polynomial ℂ := C ((2)) * X^21 + C ((5)) * X^22 + C ((-3)) * X^23 + C ((-16)) * X^24 + C ((-4)) * X^25 + C ((18)) * X^26 + C ((10)) * X^27 + C ((-8)) * X^28 + C ((-6)) * X^29 + C ((1)) * X^30 + C ((1)) * X^31

def gD3L : Fin 6 → Polynomial ℂ := ![gD3L_0, gD3L_1, gD3L_2, gD3L_3, gD3L_4, gD3L_5]

def LformL (a b : ℂ) (n : Fin 7 → ℂ) (c : Fin 6 → ℂ) : ℕ → ℂ
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

def PsibL (a b : ℂ) : ℂ := - 59290*a^6*b^2 + 185493*a^5*b^3 - 8491*a^5*b - 249865*a^4*b^4 + 65541*a^4*b^2 + 6090*a^4 + 185493*a^3*b^5 - 119686*a^3*b^3 - 15225*a^3*b - 59290*a^2*b^6 + 65541*a^2*b^4 + 21000*a^2*b^2 - 975*a^2 - 8491*a*b^5 - 15225*a*b^3 + 4260*a*b + 6090*b^4 - 975*b^2 - 1755

def Pdet4L (a b : ℂ) : ℂ := ((-117/16)*b^4+(117/8)*a^2*b^2+(-117/16)*a^4+(-65/16)*b^6+(71/4)*a*b^5+(65/16)*a^2*b^4+(-71/2)*a^3*b^3+(65/16)*a^4*b^2+(71/4)*a^5*b+(-65/16)*a^6+(203/8)*b^8+(-1015/16)*a*b^7+(147/4)*a^2*b^6+(1015/16)*a^3*b^5+(-497/4)*a^4*b^4+(1015/16)*a^5*b^3+(147/4)*a^6*b^2+(-1015/16)*a^7*b+(203/8)*a^8+(-8491/240)*a*b^9+(21847/80)*a^2*b^8+(-6419/15)*a^3*b^7+(-21847/80)*a^4*b^6+(7413/8)*a^5*b^5+(-21847/80)*a^6*b^4+(-6419/15)*a^7*b^3+(21847/80)*a^8*b^2+(-8491/240)*a^9*b+(-5929/24)*a^2*b^10+(61831/80)*a^3*b^9+(-26257/48)*a^4*b^8+(-61831/80)*a^5*b^7+(12705/8)*a^6*b^6+(-61831/80)*a^7*b^5+(-26257/48)*a^8*b^4+(61831/80)*a^9*b^3+(-5929/24)*a^10*b^2)

/-! ## The certificate polynomials -/

/-- `NpolyL` is the numerator `Σ_k n_k x^k` (degree `≤ 6`). -/
theorem NpolyL_derivative (n : Fin 7 → ℂ) :
    (NpolyL n).derivative = NpolyDL n := by
  rw [NpolyL, NpolyDL]
  simp only [Polynomial.derivative_sum, Polynomial.derivative_C_mul_X_pow]
  apply Finset.sum_congr rfl
  intro k _
  rw [mul_comm (n k) ((k : ℕ) : ℂ)]

theorem NpolyDL_derivative (n : Fin 7 → ℂ) :
    (NpolyDL n).derivative = NpolyDDL n := by
  rw [NpolyDL, NpolyDDL]
  simp only [Polynomial.derivative_sum, Polynomial.derivative_C_mul_X_pow]
  apply Finset.sum_congr rfl
  intro k _
  fin_cases k <;> norm_num <;> (simp only [← C_mul]; congr 1; ring)

theorem DadjL_derivative : (DadjL).derivative = Dadj1L := by
  simp only [DadjL, Dadj1L, derivative_add, derivative_C_mul_X_pow]
  norm_num

theorem Dadj1L_derivative : (Dadj1L).derivative = Dadj2L := by
  simp only [Dadj1L, Dadj2L, derivative_add, derivative_C_mul_X_pow]
  norm_num

theorem DadjL_ne_zero : (DadjL : Polynomial ℂ) ≠ 0 := by
  intro h
  have hc := congrArg (fun p : Polynomial ℂ => p.coeff 10) h
  simp only [DadjL, coeff_add, coeff_C_mul_X_pow, coeff_zero] at hc
  norm_num at hc

theorem BadjL_eq_deriv (a b : ℂ) :
    BadjL a b = 2 * (P2xL a b).derivative - P1xL a b := by
  simp only [BadjL, P1xL, P2xL, Q4xL, derivative_add, derivative_mul,
    derivative_sub, derivative_X, derivative_C, derivative_one, derivative_X_pow]
  ring_nf
  simp only [map_mul, map_add, map_sub, map_pow, map_neg, map_natCast, map_ofNat, map_one,
    map_zero, Nat.cast_ofNat, pow_zero, mul_one, one_mul, zero_mul, mul_zero, neg_zero, zero_add,
    add_zero, pow_one]
  ring

theorem CadjL_eq_deriv (a b : ℂ) :
    CadjL a b
      = (P2xL a b).derivative.derivative - (P1xL a b).derivative + P0xL a b := by
  simp only [CadjL, P1xL, P2xL, P0xL, Q4xL, derivative_add,
    derivative_mul, derivative_sub, derivative_neg, derivative_X, derivative_C, derivative_one,
    derivative_X_pow]
  ring_nf
  simp only [map_mul, map_add, map_sub, map_pow, map_neg, map_natCast, map_ofNat, map_one,
    map_zero, Nat.cast_ofNat, pow_zero, mul_one, one_mul, zero_mul, mul_zero, neg_zero, zero_add,
    add_zero, pow_one]
  ring

/-- The `D³`-multiple of `(P₂β)'' - (P₁β)' + P₀β` for `β = N/D`. -/
def LeftPolyL (a b : ℂ) (n : Fin 7 → ℂ) : Polynomial ℂ :=
  P2xL a b * (NpolyDDL n * DadjL ^ 2
        - NpolyL n * DadjL * Dadj2L
        - 2 * NpolyDL n * DadjL * Dadj1L
        + 2 * NpolyL n * Dadj1L ^ 2)
    + BadjL a b * (DadjL * (NpolyDL n * DadjL - NpolyL n * Dadj1L))
    + CadjL a b * (DadjL ^ 2 * NpolyL n)

/-- The `D³`-multiple of `Σᵢ cᵢ y^{i-4} dy`. -/
def RightPolyL (c : Fin 6 → ℂ) : Polynomial ℂ :=
  ∑ i : Fin 6, C (c i) * gD3L i

/-- The cleared adjoint expression: `EpolyL a b n c = LeftPolyL a b n - RightPolyL c`. -/
def EpolyL (a b : ℂ) (n : Fin 7 → ℂ) (c : Fin 6 → ℂ) : Polynomial ℂ :=
  LeftPolyL a b n - RightPolyL c

/-- `GpolyL` is the explicit polynomial `Σ_d L_d X^d`. -/
def GpolyL (a b : ℂ) (n : Fin 7 → ℂ) (c : Fin 6 → ℂ) : Polynomial ℂ :=
  ∑ d ∈ Finset.Icc 11 31, C (LformL a b n c d) * X ^ d

/-- The adjoint of the operator `M = P₂∂² + P₁∂ + P₀` applied to `β` (`ℂ`-literal data). -/
def AdjOpL (a b : ℂ) (β : RatFunc ℂ) : RatFunc ℂ :=
  Submission.CDT.dRat (Submission.CDT.dRat (algebraMap (Polynomial ℂ) (RatFunc ℂ) (P2xL a b) * β))
    - Submission.CDT.dRat (algebraMap (Polynomial ℂ) (RatFunc ℂ) (P1xL a b) * β)
    + algebraMap (Polynomial ℂ) (RatFunc ℂ) (P0xL a b) * β

/-- The right hand side `Σᵢ cᵢ y^{i-4} y'` in the variable `y = x²/(x−1)`. -/
def RhsYc (c : Fin 6 → ℂ) : RatFunc ℂ :=
  ∑ i : Fin 6, algebraMap ℂ (RatFunc ℂ) (c i) * Work.C17.yQc ^ ((i : ℤ) - 4) * Work.C17.dyQc

/-! ## Bridges to the base changed `ℚ`-data (`Work.C17.P2C` etc.) -/

theorem Q4xL_eq_map (a b : ℚ) :
    Q4xL (a : ℂ) (b : ℂ) = (Work.C17.Q4x a b).map (algebraMap ℚ ℂ) := by
  rw [Q4xL, Work.C17.Q4x]
  simp only [Polynomial.map_add, Polynomial.map_sub, Polynomial.map_one, Polynomial.map_mul,
    Polynomial.map_C, Polynomial.map_X, Polynomial.map_pow, Polynomial.map_ofNat,
    Polynomial.map_neg, Polynomial.map_natCast, Polynomial.map_intCast]
  push_cast <;> norm_num

theorem P2xL_eq_map (a b : ℚ) :
    P2xL (a : ℂ) (b : ℂ) = (Work.C17.P2x a b).map (algebraMap ℚ ℂ) := by
  rw [P2xL, Work.C17.P2x, Q4xL_eq_map]
  simp only [Polynomial.map_add, Polynomial.map_sub, Polynomial.map_one, Polynomial.map_mul,
    Polynomial.map_C, Polynomial.map_X, Polynomial.map_pow, Polynomial.map_ofNat,
    Polynomial.map_neg, Polynomial.map_natCast, Polynomial.map_intCast]
  try ring

theorem P1xL_eq_map (a b : ℚ) :
    P1xL (a : ℂ) (b : ℂ) = (Work.C17.P1x a b).map (algebraMap ℚ ℂ) := by
  rw [P1xL, Work.C17.P1x]
  simp only [Polynomial.map_add, Polynomial.map_sub, Polynomial.map_one, Polynomial.map_mul,
    Polynomial.map_C, Polynomial.map_X, Polynomial.map_pow, Polynomial.map_ofNat,
    Polynomial.map_neg, Polynomial.map_natCast, Polynomial.map_intCast]
  push_cast <;> norm_num

theorem P0xL_eq_map (a b : ℚ) :
    P0xL (a : ℂ) (b : ℂ) = (Work.C17.P0x a b).map (algebraMap ℚ ℂ) := by
  rw [P0xL, Work.C17.P0x]
  simp only [Polynomial.map_add, Polynomial.map_sub, Polynomial.map_one, Polynomial.map_mul,
    Polynomial.map_C, Polynomial.map_X, Polynomial.map_pow, Polynomial.map_ofNat,
    Polynomial.map_neg, Polynomial.map_natCast, Polynomial.map_intCast]
  push_cast <;> norm_num

theorem BadjL_eq_map (a b : ℚ) :
    BadjL (a : ℂ) (b : ℂ) = (Work.C17.Badj a b).map (algebraMap ℚ ℂ) := by
  rw [BadjL, Work.C17.Badj]
  simp only [Polynomial.map_add, Polynomial.map_sub, Polynomial.map_one, Polynomial.map_mul,
    Polynomial.map_C, Polynomial.map_X, Polynomial.map_pow, Polynomial.map_ofNat,
    Polynomial.map_neg, Polynomial.map_natCast, Polynomial.map_intCast]
  push_cast <;> norm_num

theorem CadjL_eq_map (a b : ℚ) :
    CadjL (a : ℂ) (b : ℂ) = (Work.C17.Cadj a b).map (algebraMap ℚ ℂ) := by
  rw [CadjL, Work.C17.Cadj]
  simp only [Polynomial.map_add, Polynomial.map_sub, Polynomial.map_one, Polynomial.map_mul,
    Polynomial.map_C, Polynomial.map_X, Polynomial.map_pow, Polynomial.map_ofNat,
    Polynomial.map_neg, Polynomial.map_natCast, Polynomial.map_intCast]
  push_cast <;> norm_num

theorem DadjL_eq_map : DadjL = (Work.C17.Dadj).map (algebraMap ℚ ℂ) := by
  rw [DadjL, Work.C17.Dadj]
  simp only [Polynomial.map_add, Polynomial.map_sub, Polynomial.map_one, Polynomial.map_mul,
    Polynomial.map_C, Polynomial.map_X, Polynomial.map_pow, Polynomial.map_ofNat,
    Polynomial.map_neg, Polynomial.map_natCast, Polynomial.map_intCast]
  norm_num

theorem Dadj1L_eq_map : Dadj1L = (Work.C17.Dadj1).map (algebraMap ℚ ℂ) := by
  rw [Dadj1L, Work.C17.Dadj1]
  simp only [Polynomial.map_add, Polynomial.map_sub, Polynomial.map_one, Polynomial.map_mul,
    Polynomial.map_C, Polynomial.map_X, Polynomial.map_pow, Polynomial.map_ofNat,
    Polynomial.map_neg, Polynomial.map_natCast, Polynomial.map_intCast]
  norm_num

theorem Dadj2L_eq_map : Dadj2L = (Work.C17.Dadj2).map (algebraMap ℚ ℂ) := by
  rw [Dadj2L, Work.C17.Dadj2]
  simp only [Polynomial.map_add, Polynomial.map_sub, Polynomial.map_one, Polynomial.map_mul,
    Polynomial.map_C, Polynomial.map_X, Polynomial.map_pow, Polynomial.map_ofNat,
    Polynomial.map_neg, Polynomial.map_natCast, Polynomial.map_intCast]
  norm_num

theorem PsibL_eq_map (a b : ℚ) :
    PsibL (a : ℂ) (b : ℂ) = ((Work.C17.Psib a b : ℚ) : ℂ) := by
  rw [PsibL, Work.C17.Psib]
  push_cast
  ring

theorem Pdet4L_eq_map (a b : ℚ) :
    Pdet4L (a : ℂ) (b : ℂ) = ((Work.C17.Pdet4 a b : ℚ) : ℂ) := by
  rw [Pdet4L, Work.C17.Pdet4]
  push_cast
  ring

theorem PdetL_eq (a b : ℂ) :
    Pdet4L a b = (1/240) * ((a ^ 2 - b ^ 2) ^ 2 * PsibL a b) := by
  rw [Pdet4L, PsibL]
  ring

theorem WorkC_P2C_eq (a b : ℚ) :
    Work.C17.P2C a b = P2xL (a : ℂ) (b : ℂ) := (P2xL_eq_map a b).symm

theorem WorkC_P1C_eq (a b : ℚ) :
    Work.C17.P1C a b = P1xL (a : ℂ) (b : ℂ) := (P1xL_eq_map a b).symm

theorem WorkC_P0C_eq (a b : ℚ) :
    Work.C17.P0C a b = P0xL (a : ℂ) (b : ℂ) := (P0xL_eq_map a b).symm

theorem DadjC_eq :
    Work.C17.DadjC = algebraMap (Polynomial ℂ) (RatFunc ℂ) DadjL := by
  rw [Work.C17.DadjC, DadjL_eq_map]

end

end Work.C17C
