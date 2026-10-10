import Mathlib
import Submission.Work.MotAS.ASZElimData
import Submission.Work.Reflect.PolyId

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Work.MotAS

open MvPolynomial
open scoped BigOperators

/-! ## Numerals in `C` and under `map` (characteristic-free bookkeeping) -/

private lemma C_two' {R : Type*} [CommSemiring R] :
    (MvPolynomial.C (2 : R) : MvPolynomial (Fin 2) R) = (2 : MvPolynomial (Fin 2) R) :=
  MvPolynomial.C_eq_coe_nat 2

private lemma C_three' {R : Type*} [CommSemiring R] :
    (MvPolynomial.C (3 : R) : MvPolynomial (Fin 2) R) = (3 : MvPolynomial (Fin 2) R) :=
  MvPolynomial.C_eq_coe_nat 3

private lemma C_four' {R : Type*} [CommSemiring R] :
    (MvPolynomial.C (4 : R) : MvPolynomial (Fin 2) R) = (4 : MvPolynomial (Fin 2) R) :=
  MvPolynomial.C_eq_coe_nat 4

private lemma map_two' (K L : Type*) [CommSemiring K] [CommSemiring L] [Algebra K L] :
    MvPolynomial.map (algebraMap K L) (2 : MvPolynomial (Fin 2) K) =
      (2 : MvPolynomial (Fin 2) L) := by
  rw [show (2 : MvPolynomial (Fin 2) K) = ((2 : ℕ) : MvPolynomial (Fin 2) K) from rfl,
      show (2 : MvPolynomial (Fin 2) L) = ((2 : ℕ) : MvPolynomial (Fin 2) L) from rfl,
      map_natCast]

private lemma alg_two' (K L : Type*) [CommSemiring K] [CommSemiring L] [Algebra K L] :
    algebraMap K L (2 : K) = (2 : L) := by
  rw [show (2 : K) = ((2 : ℕ) : K) from rfl, show (2 : L) = ((2 : ℕ) : L) from rfl,
      map_natCast]

/-! ## The polynomial data of the factorisation identity -/

/-- One factor of the product: the value at `C θ + k` of `C a * X 0 + 2 * C a * T * X 1 + 4 * (T ^ 3 - T)`. -/
private noncomputable def fac {R : Type*} [CommRing R] (a θ : R) (k : ℕ) : MvPolynomial (Fin 2) R :=
  MvPolynomial.C a * MvPolynomial.X 0
    + (2 * MvPolynomial.C a) * (MvPolynomial.C θ + (k : MvPolynomial (Fin 2) R)) * MvPolynomial.X 1
    + 4 * ((MvPolynomial.C θ + (k : MvPolynomial (Fin 2) R)) ^(3:ℕ)
        - (MvPolynomial.C θ + (k : MvPolynomial (Fin 2) R)))

/-- The explicitation of `ASZElim.P 1 0 g` in the atom basis `C a`, `C θ`, `X 0`, `X 1` and numerals. -/
private noncomputable def Q2 {R : Type*} [CommRing R] (a : R) : MvPolynomial (Fin 2) R :=
  (MvPolynomial.C a)^(2:ℕ) * MvPolynomial.X 0^(5:ℕ) - MvPolynomial.C a * MvPolynomial.X 0^(3:ℕ) * MvPolynomial.X 1 * 2 - MvPolynomial.X 0^(3:ℕ) + MvPolynomial.X 0^(2:ℕ) * 2 - (MvPolynomial.C a)^(2:ℕ) * MvPolynomial.X 0 * MvPolynomial.X 1^(4:ℕ) - MvPolynomial.C a * MvPolynomial.X 0 * MvPolynomial.X 1^(3:ℕ) * 2 - MvPolynomial.X 0 * MvPolynomial.X 1^(2:ℕ) + (MvPolynomial.C a)^(3:ℕ) * MvPolynomial.X 1^(5:ℕ) * 2 - MvPolynomial.C a * MvPolynomial.X 1^(3:ℕ) + MvPolynomial.X 1^(2:ℕ) - 1

/-- The cofactor of the Artin–Schreier relation `(C θ)^5 - C θ - C a` in the exact division of the
difference of the two sides of the factorisation identity. -/
private noncomputable def Rq2 {R : Type*} [CommRing R] (a θ : R) : MvPolynomial (Fin 2) R :=
  (MvPolynomial.C θ)^(10:ℕ) * 1024 + (MvPolynomial.C θ)^(9:ℕ) * 30720 + MvPolynomial.C a * (MvPolynomial.C θ)^(8:ℕ) * MvPolynomial.X 1 * 2560 + (MvPolynomial.C θ)^(8:ℕ) * 409600 + MvPolynomial.C a * (MvPolynomial.C θ)^(7:ℕ) * MvPolynomial.X 0 * 1280 + MvPolynomial.C a * (MvPolynomial.C θ)^(7:ℕ) * MvPolynomial.X 1 * 66560 + (MvPolynomial.C θ)^(7:ℕ) * 3194880 + MvPolynomial.C a * (MvPolynomial.C θ)^(6:ℕ) * MvPolynomial.X 0 * 30720 + (MvPolynomial.C a)^(2:ℕ) * (MvPolynomial.C θ)^(6:ℕ) * MvPolynomial.X 1^(2:ℕ) * 2560 + MvPolynomial.C a * (MvPolynomial.C θ)^(6:ℕ) * MvPolynomial.X 1 * 765440 + (MvPolynomial.C θ)^(6:ℕ) * 16120832 + (MvPolynomial.C a)^(2:ℕ) * (MvPolynomial.C θ)^(5:ℕ) * MvPolynomial.X 0 * MvPolynomial.X 1 * 2560 + MvPolynomial.C a * (MvPolynomial.C θ)^(5:ℕ) * MvPolynomial.X 0 * 328960 + (MvPolynomial.C a)^(2:ℕ) * (MvPolynomial.C θ)^(5:ℕ) * MvPolynomial.X 1^(2:ℕ) * 56320 + MvPolynomial.C a * (MvPolynomial.C θ)^(5:ℕ) * MvPolynomial.X 1 * 5125120 + MvPolynomial.C a * (MvPolynomial.C θ)^(5:ℕ) * 1024 + (MvPolynomial.C θ)^(5:ℕ) * 54773760 + (MvPolynomial.C a)^(2:ℕ) * (MvPolynomial.C θ)^(4:ℕ) * MvPolynomial.X 0^(2:ℕ) * 640 + (MvPolynomial.C a)^(2:ℕ) * (MvPolynomial.C θ)^(4:ℕ) * MvPolynomial.X 0 * MvPolynomial.X 1 * 51200 + MvPolynomial.C a * (MvPolynomial.C θ)^(4:ℕ) * MvPolynomial.X 0 * 2073600 + (MvPolynomial.C a)^(3:ℕ) * (MvPolynomial.C θ)^(4:ℕ) * MvPolynomial.X 1^(3:ℕ) * 1280 + (MvPolynomial.C a)^(2:ℕ) * (MvPolynomial.C θ)^(4:ℕ) * MvPolynomial.X 1^(2:ℕ) * 542720 + MvPolynomial.C a * (MvPolynomial.C θ)^(4:ℕ) * MvPolynomial.X 1 * 22113280 + MvPolynomial.C a * (MvPolynomial.C θ)^(4:ℕ) * 30720 + (MvPolynomial.C θ)^(4:ℕ) * 125644800 + (MvPolynomial.C a)^(2:ℕ) * (MvPolynomial.C θ)^(3:ℕ) * MvPolynomial.X 0^(2:ℕ) * 11520 + (MvPolynomial.C a)^(3:ℕ) * (MvPolynomial.C θ)^(3:ℕ) * MvPolynomial.X 0 * MvPolynomial.X 1^(2:ℕ) * 1920 + (MvPolynomial.C a)^(2:ℕ) * (MvPolynomial.C θ)^(3:ℕ) * MvPolynomial.X 0 * MvPolynomial.X 1 * 453120 + MvPolynomial.C a * (MvPolynomial.C θ)^(3:ℕ) * MvPolynomial.X 0 * 8545280 + (MvPolynomial.C a)^(3:ℕ) * (MvPolynomial.C θ)^(3:ℕ) * MvPolynomial.X 1^(3:ℕ) * 23040 + (MvPolynomial.C a)^(2:ℕ) * (MvPolynomial.C θ)^(3:ℕ) * MvPolynomial.X 1^(2:ℕ) * 3010560 + (MvPolynomial.C a)^(2:ℕ) * (MvPolynomial.C θ)^(3:ℕ) * MvPolynomial.X 1 * 2560 + MvPolynomial.C a * (MvPolynomial.C θ)^(3:ℕ) * MvPolynomial.X 1 * 64194560 + MvPolynomial.C a * (MvPolynomial.C θ)^(3:ℕ) * 409600 + (MvPolynomial.C θ)^(3:ℕ) * 186654720 + (MvPolynomial.C a)^(3:ℕ) * (MvPolynomial.C θ)^(2:ℕ) * MvPolynomial.X 0^(2:ℕ) * MvPolynomial.X 1 * 960 + (MvPolynomial.C a)^(2:ℕ) * (MvPolynomial.C θ)^(2:ℕ) * MvPolynomial.X 0^(2:ℕ) * 93120 + (MvPolynomial.C a)^(3:ℕ) * (MvPolynomial.C θ)^(2:ℕ) * MvPolynomial.X 0 * MvPolynomial.X 1^(2:ℕ) * 30720 + (MvPolynomial.C a)^(2:ℕ) * (MvPolynomial.C θ)^(2:ℕ) * MvPolynomial.X 0 * MvPolynomial.X 1 * 2334720 + (MvPolynomial.C a)^(2:ℕ) * (MvPolynomial.C θ)^(2:ℕ) * MvPolynomial.X 0 * 1280 + MvPolynomial.C a * (MvPolynomial.C θ)^(2:ℕ) * MvPolynomial.X 0 * 24176640 + (MvPolynomial.C a)^(4:ℕ) * (MvPolynomial.C θ)^(2:ℕ) * MvPolynomial.X 1^(4:ℕ) * 320 + (MvPolynomial.C a)^(3:ℕ) * (MvPolynomial.C θ)^(2:ℕ) * MvPolynomial.X 1^(3:ℕ) * 177920 + (MvPolynomial.C a)^(2:ℕ) * (MvPolynomial.C θ)^(2:ℕ) * MvPolynomial.X 1^(2:ℕ) * 10620160 + (MvPolynomial.C a)^(2:ℕ) * (MvPolynomial.C θ)^(2:ℕ) * MvPolynomial.X 1 * 66560 + MvPolynomial.C a * (MvPolynomial.C θ)^(2:ℕ) * MvPolynomial.X 1 * 126945280 + MvPolynomial.C a * (MvPolynomial.C θ)^(2:ℕ) * 3194880 + (MvPolynomial.C θ)^(2:ℕ) * 154476544 + (MvPolynomial.C a)^(3:ℕ) * MvPolynomial.C θ * MvPolynomial.X 0^(3:ℕ) * 160 + (MvPolynomial.C a)^(3:ℕ) * MvPolynomial.C θ * MvPolynomial.X 0^(2:ℕ) * MvPolynomial.X 1 * 13440 + (MvPolynomial.C a)^(2:ℕ) * MvPolynomial.C θ * MvPolynomial.X 0^(2:ℕ) * 443520 + (MvPolynomial.C a)^(4:ℕ) * MvPolynomial.C θ * MvPolynomial.X 0 * MvPolynomial.X 1^(3:ℕ) * 640 + (MvPolynomial.C a)^(3:ℕ) * MvPolynomial.C θ * MvPolynomial.X 0 * MvPolynomial.X 1^(2:ℕ) * 213120 + (MvPolynomial.C a)^(2:ℕ) * MvPolynomial.C θ * MvPolynomial.X 0 * MvPolynomial.X 1 * 7751680 + (MvPolynomial.C a)^(2:ℕ) * MvPolynomial.C θ * MvPolynomial.X 0 * 30720 + MvPolynomial.C a * MvPolynomial.C θ * MvPolynomial.X 0 * 48051200 + (MvPolynomial.C a)^(4:ℕ) * MvPolynomial.C θ * MvPolynomial.X 1^(4:ℕ) * 4480 + (MvPolynomial.C a)^(3:ℕ) * MvPolynomial.C θ * MvPolynomial.X 1^(3:ℕ) * 770560 + (MvPolynomial.C a)^(3:ℕ) * MvPolynomial.C θ * MvPolynomial.X 1^(2:ℕ) * 2560 + (MvPolynomial.C a)^(2:ℕ) * MvPolynomial.C θ * MvPolynomial.X 1^(2:ℕ) * 24839680 + (MvPolynomial.C a)^(2:ℕ) * MvPolynomial.C θ * MvPolynomial.X 1 * 765440 + MvPolynomial.C a * MvPolynomial.C θ * MvPolynomial.X 1 * 169779200 + MvPolynomial.C a * MvPolynomial.C θ * 16121856 + MvPolynomial.C θ * 23838720 + (MvPolynomial.C a)^(3:ℕ) * MvPolynomial.X 0^(3:ℕ) * 1920 + (MvPolynomial.C a)^(4:ℕ) * MvPolynomial.X 0^(2:ℕ) * MvPolynomial.X 1^(2:ℕ) * 480 + (MvPolynomial.C a)^(3:ℕ) * MvPolynomial.X 0^(2:ℕ) * MvPolynomial.X 1 * 83040 + (MvPolynomial.C a)^(2:ℕ) * MvPolynomial.X 0^(2:ℕ) * 1374592 + (MvPolynomial.C a)^(4:ℕ) * MvPolynomial.X 0 * MvPolynomial.X 1^(3:ℕ) * 7680 + (MvPolynomial.C a)^(3:ℕ) * MvPolynomial.X 0 * MvPolynomial.X 1^(2:ℕ) * 837120 + (MvPolynomial.C a)^(3:ℕ) * MvPolynomial.X 0 * MvPolynomial.X 1 * 2560 + (MvPolynomial.C a)^(2:ℕ) * MvPolynomial.X 0 * MvPolynomial.X 1 * 17346560 + (MvPolynomial.C a)^(2:ℕ) * MvPolynomial.X 0 * 328960 + MvPolynomial.C a * MvPolynomial.X 0 * 67983360 + (MvPolynomial.C a)^(5:ℕ) * MvPolynomial.X 1^(5:ℕ) * 32 + (MvPolynomial.C a)^(4:ℕ) * MvPolynomial.X 1^(4:ℕ) * 25600 + (MvPolynomial.C a)^(3:ℕ) * MvPolynomial.X 1^(3:ℕ) * 2049664 + (MvPolynomial.C a)^(3:ℕ) * MvPolynomial.X 1^(2:ℕ) * 56320 + (MvPolynomial.C a)^(2:ℕ) * MvPolynomial.X 1^(2:ℕ) * 39102976 + (MvPolynomial.C a)^(2:ℕ) * MvPolynomial.X 1 * 5125120 + MvPolynomial.C a * MvPolynomial.X 1 * 153774080 + (MvPolynomial.C a)^(2:ℕ) * 1024 + MvPolynomial.C a * 54804480 - 62464000

private noncomputable def E2a {R : Type*} [CommRing R] (a θ : R) : MvPolynomial (Fin 2) R :=
  ((MvPolynomial.C a)^(4:ℕ) * (MvPolynomial.C θ)^(4:ℕ) * MvPolynomial.X 0^(3:ℕ) * MvPolynomial.X 1 * 32 + (MvPolynomial.C a)^(3:ℕ) * (MvPolynomial.C θ)^(4:ℕ) * MvPolynomial.X 0^(3:ℕ) * 2096 + (MvPolynomial.C a)^(4:ℕ) * (MvPolynomial.C θ)^(4:ℕ) * MvPolynomial.X 0^(2:ℕ) * MvPolynomial.X 1^(2:ℕ) * 960 + (MvPolynomial.C a)^(3:ℕ) * (MvPolynomial.C θ)^(4:ℕ) * MvPolynomial.X 0^(2:ℕ) * MvPolynomial.X 1 * 58560 + (MvPolynomial.C a)^(3:ℕ) * (MvPolynomial.C θ)^(4:ℕ) * MvPolynomial.X 0^(2:ℕ) * 128 + (MvPolynomial.C a)^(2:ℕ) * (MvPolynomial.C θ)^(4:ℕ) * MvPolynomial.X 0^(2:ℕ) * 578304 + (MvPolynomial.C a)^(5:ℕ) * (MvPolynomial.C θ)^(4:ℕ) * MvPolynomial.X 0 * MvPolynomial.X 1^(4:ℕ) * 16 + (MvPolynomial.C a)^(4:ℕ) * (MvPolynomial.C θ)^(4:ℕ) * MvPolynomial.X 0 * MvPolynomial.X 1^(3:ℕ) * 7552 + (MvPolynomial.C a)^(3:ℕ) * (MvPolynomial.C θ)^(4:ℕ) * MvPolynomial.X 0 * MvPolynomial.X 1^(2:ℕ) * 406848 + (MvPolynomial.C a)^(3:ℕ) * (MvPolynomial.C θ)^(4:ℕ) * MvPolynomial.X 0 * MvPolynomial.X 1 * 10240 + (MvPolynomial.C a)^(2:ℕ) * (MvPolynomial.C θ)^(4:ℕ) * MvPolynomial.X 0 * MvPolynomial.X 1 * 5343232 + (MvPolynomial.C a)^(2:ℕ) * (MvPolynomial.C θ)^(4:ℕ) * MvPolynomial.X 0 * 414720 + MvPolynomial.C a * (MvPolynomial.C θ)^(4:ℕ) * MvPolynomial.X 0 * 14167040 + (MvPolynomial.C a)^(5:ℕ) * (MvPolynomial.C θ)^(4:ℕ) * MvPolynomial.X 1^(5:ℕ) * 64 + (MvPolynomial.C a)^(4:ℕ) * (MvPolynomial.C θ)^(4:ℕ) * MvPolynomial.X 1^(4:ℕ) * 15360 + (MvPolynomial.C a)^(4:ℕ) * (MvPolynomial.C θ)^(4:ℕ) * MvPolynomial.X 1^(3:ℕ) * 256 + (MvPolynomial.C a)^(3:ℕ) * (MvPolynomial.C θ)^(4:ℕ) * MvPolynomial.X 1^(3:ℕ) * 689408 + (MvPolynomial.C a)^(3:ℕ) * (MvPolynomial.C θ)^(4:ℕ) * MvPolynomial.X 1^(2:ℕ) * 108544 + (MvPolynomial.C a)^(2:ℕ) * (MvPolynomial.C θ)^(4:ℕ) * MvPolynomial.X 1^(2:ℕ) * 8430592 + (MvPolynomial.C a)^(2:ℕ) * (MvPolynomial.C θ)^(4:ℕ) * MvPolynomial.X 1 * 4423168 + MvPolynomial.C a * (MvPolynomial.C θ)^(4:ℕ) * MvPolynomial.X 1 * 22446080 + (MvPolynomial.C a)^(2:ℕ) * (MvPolynomial.C θ)^(4:ℕ) * 6144 + MvPolynomial.C a * (MvPolynomial.C θ)^(4:ℕ) * 25210880 - (MvPolynomial.C θ)^(4:ℕ) * 1228800 + (MvPolynomial.C a)^(4:ℕ) * (MvPolynomial.C θ)^(3:ℕ) * MvPolynomial.X 0^(4:ℕ) * 4 + (MvPolynomial.C a)^(4:ℕ) * (MvPolynomial.C θ)^(3:ℕ) * MvPolynomial.X 0^(3:ℕ) * MvPolynomial.X 1 * 256 + (MvPolynomial.C a)^(3:ℕ) * (MvPolynomial.C θ)^(3:ℕ) * MvPolynomial.X 0^(3:ℕ) * 6528 + (MvPolynomial.C a)^(5:ℕ) * (MvPolynomial.C θ)^(3:ℕ) * MvPolynomial.X 0^(2:ℕ) * MvPolynomial.X 1^(3:ℕ) * 16 + (MvPolynomial.C a)^(4:ℕ) * (MvPolynomial.C θ)^(3:ℕ) * MvPolynomial.X 0^(2:ℕ) * MvPolynomial.X 1^(2:ℕ) * 3984 + (MvPolynomial.C a)^(3:ℕ) * (MvPolynomial.C θ)^(3:ℕ) * MvPolynomial.X 0^(2:ℕ) * MvPolynomial.X 1 * 127392 + (MvPolynomial.C a)^(3:ℕ) * (MvPolynomial.C θ)^(3:ℕ) * MvPolynomial.X 0^(2:ℕ) * 2304 + (MvPolynomial.C a)^(2:ℕ) * (MvPolynomial.C θ)^(3:ℕ) * MvPolynomial.X 0^(2:ℕ) * 839296 + (MvPolynomial.C a)^(5:ℕ) * (MvPolynomial.C θ)^(3:ℕ) * MvPolynomial.X 0 * MvPolynomial.X 1^(4:ℕ) * 128 + (MvPolynomial.C a)^(4:ℕ) * (MvPolynomial.C θ)^(3:ℕ) * MvPolynomial.X 0 * MvPolynomial.X 1^(3:ℕ) * 19456 + (MvPolynomial.C a)^(4:ℕ) * (MvPolynomial.C θ)^(3:ℕ) * MvPolynomial.X 0 * MvPolynomial.X 1^(2:ℕ) * 384 + (MvPolynomial.C a)^(3:ℕ) * (MvPolynomial.C θ)^(3:ℕ) * MvPolynomial.X 0 * MvPolynomial.X 1^(2:ℕ) * 628224 + (MvPolynomial.C a)^(3:ℕ) * (MvPolynomial.C θ)^(3:ℕ) * MvPolynomial.X 0 * MvPolynomial.X 1 * 90624 + (MvPolynomial.C a)^(2:ℕ) * (MvPolynomial.C θ)^(3:ℕ) * MvPolynomial.X 0 * MvPolynomial.X 1 * 5820416)

private noncomputable def E2b {R : Type*} [CommRing R] (a θ : R) : MvPolynomial (Fin 2) R :=
  ((MvPolynomial.C a)^(2:ℕ) * (MvPolynomial.C θ)^(3:ℕ) * MvPolynomial.X 0 * 1709312 + MvPolynomial.C a * (MvPolynomial.C θ)^(3:ℕ) * MvPolynomial.X 0 * 12503040 + (MvPolynomial.C a)^(5:ℕ) * (MvPolynomial.C θ)^(3:ℕ) * MvPolynomial.X 1^(5:ℕ) * 224 + (MvPolynomial.C a)^(4:ℕ) * (MvPolynomial.C θ)^(3:ℕ) * MvPolynomial.X 1^(4:ℕ) * 25600 + (MvPolynomial.C a)^(4:ℕ) * (MvPolynomial.C θ)^(3:ℕ) * MvPolynomial.X 1^(3:ℕ) * 4608 + (MvPolynomial.C a)^(3:ℕ) * (MvPolynomial.C θ)^(3:ℕ) * MvPolynomial.X 1^(3:ℕ) * 738688 + (MvPolynomial.C a)^(3:ℕ) * (MvPolynomial.C θ)^(3:ℕ) * MvPolynomial.X 1^(2:ℕ) * 602112 + (MvPolynomial.C a)^(2:ℕ) * (MvPolynomial.C θ)^(3:ℕ) * MvPolynomial.X 1^(2:ℕ) * 7009792 + (MvPolynomial.C a)^(3:ℕ) * (MvPolynomial.C θ)^(3:ℕ) * MvPolynomial.X 1 * 512 + (MvPolynomial.C a)^(2:ℕ) * (MvPolynomial.C θ)^(3:ℕ) * MvPolynomial.X 1 * 12852224 + MvPolynomial.C a * (MvPolynomial.C θ)^(3:ℕ) * MvPolynomial.X 1 * 23214080 + (MvPolynomial.C a)^(2:ℕ) * (MvPolynomial.C θ)^(3:ℕ) * 81920 + MvPolynomial.C a * (MvPolynomial.C θ)^(3:ℕ) * 37969920 + (MvPolynomial.C θ)^(3:ℕ) * 12492800 + (MvPolynomial.C a)^(4:ℕ) * (MvPolynomial.C θ)^(2:ℕ) * MvPolynomial.X 0^(4:ℕ) * 24 + (MvPolynomial.C a)^(5:ℕ) * (MvPolynomial.C θ)^(2:ℕ) * MvPolynomial.X 0^(3:ℕ) * MvPolynomial.X 1^(2:ℕ) * 8 + (MvPolynomial.C a)^(4:ℕ) * (MvPolynomial.C θ)^(2:ℕ) * MvPolynomial.X 0^(3:ℕ) * MvPolynomial.X 1 * 880 + (MvPolynomial.C a)^(3:ℕ) * (MvPolynomial.C θ)^(2:ℕ) * MvPolynomial.X 0^(3:ℕ) * 12304 + (MvPolynomial.C a)^(5:ℕ) * (MvPolynomial.C θ)^(2:ℕ) * MvPolynomial.X 0^(2:ℕ) * MvPolynomial.X 1^(3:ℕ) * 96 + (MvPolynomial.C a)^(4:ℕ) * (MvPolynomial.C θ)^(2:ℕ) * MvPolynomial.X 0^(2:ℕ) * MvPolynomial.X 1^(2:ℕ) * 8544 + (MvPolynomial.C a)^(4:ℕ) * (MvPolynomial.C θ)^(2:ℕ) * MvPolynomial.X 0^(2:ℕ) * MvPolynomial.X 1 * 192 + (MvPolynomial.C a)^(3:ℕ) * (MvPolynomial.C θ)^(2:ℕ) * MvPolynomial.X 0^(2:ℕ) * MvPolynomial.X 1 * 172992 + (MvPolynomial.C a)^(3:ℕ) * (MvPolynomial.C θ)^(2:ℕ) * MvPolynomial.X 0^(2:ℕ) * 18624 + (MvPolynomial.C a)^(2:ℕ) * (MvPolynomial.C θ)^(2:ℕ) * MvPolynomial.X 0^(2:ℕ) * 859392 + (MvPolynomial.C a)^(5:ℕ) * (MvPolynomial.C θ)^(2:ℕ) * MvPolynomial.X 0 * MvPolynomial.X 1^(4:ℕ) * 336 + (MvPolynomial.C a)^(4:ℕ) * (MvPolynomial.C θ)^(2:ℕ) * MvPolynomial.X 0 * MvPolynomial.X 1^(3:ℕ) * 27200 + (MvPolynomial.C a)^(4:ℕ) * (MvPolynomial.C θ)^(2:ℕ) * MvPolynomial.X 0 * MvPolynomial.X 1^(2:ℕ) * 6144 + (MvPolynomial.C a)^(3:ℕ) * (MvPolynomial.C θ)^(2:ℕ) * MvPolynomial.X 0 * MvPolynomial.X 1^(2:ℕ) * 623040 + (MvPolynomial.C a)^(3:ℕ) * (MvPolynomial.C θ)^(2:ℕ) * MvPolynomial.X 0 * MvPolynomial.X 1 * 466944 + (MvPolynomial.C a)^(2:ℕ) * (MvPolynomial.C θ)^(2:ℕ) * MvPolynomial.X 0 * MvPolynomial.X 1 * 5052416 + (MvPolynomial.C a)^(3:ℕ) * (MvPolynomial.C θ)^(2:ℕ) * MvPolynomial.X 0 * 256 + (MvPolynomial.C a)^(2:ℕ) * (MvPolynomial.C θ)^(2:ℕ) * MvPolynomial.X 0 * 4841472 + MvPolynomial.C a * (MvPolynomial.C θ)^(2:ℕ) * MvPolynomial.X 0 * 12375040 + (MvPolynomial.C a)^(5:ℕ) * (MvPolynomial.C θ)^(2:ℕ) * MvPolynomial.X 1^(5:ℕ) * 320 + (MvPolynomial.C a)^(5:ℕ) * (MvPolynomial.C θ)^(2:ℕ) * MvPolynomial.X 1^(4:ℕ) * 64 + (MvPolynomial.C a)^(4:ℕ) * (MvPolynomial.C θ)^(2:ℕ) * MvPolynomial.X 1^(4:ℕ) * 23040 + (MvPolynomial.C a)^(4:ℕ) * (MvPolynomial.C θ)^(2:ℕ) * MvPolynomial.X 1^(3:ℕ) * 35584 + (MvPolynomial.C a)^(3:ℕ) * (MvPolynomial.C θ)^(2:ℕ) * MvPolynomial.X 1^(3:ℕ) * 559360)

private noncomputable def E2c {R : Type*} [CommRing R] (a θ : R) : MvPolynomial (Fin 2) R :=
  ((MvPolynomial.C a)^(3:ℕ) * (MvPolynomial.C θ)^(2:ℕ) * MvPolynomial.X 1^(2:ℕ) * 2124544 + (MvPolynomial.C a)^(2:ℕ) * (MvPolynomial.C θ)^(2:ℕ) * MvPolynomial.X 1^(2:ℕ) * 6609920 + (MvPolynomial.C a)^(3:ℕ) * (MvPolynomial.C θ)^(2:ℕ) * MvPolynomial.X 1 * 13312 + (MvPolynomial.C a)^(2:ℕ) * (MvPolynomial.C θ)^(2:ℕ) * MvPolynomial.X 1 * 25542144 + MvPolynomial.C a * (MvPolynomial.C θ)^(2:ℕ) * MvPolynomial.X 1 * 30638080 + (MvPolynomial.C a)^(2:ℕ) * (MvPolynomial.C θ)^(2:ℕ) * 638976 + MvPolynomial.C a * (MvPolynomial.C θ)^(2:ℕ) * 34119680 + (MvPolynomial.C θ)^(2:ℕ) * 1228800 + (MvPolynomial.C a)^(5:ℕ) * MvPolynomial.C θ * MvPolynomial.X 0^(4:ℕ) * MvPolynomial.X 1 * 2 + (MvPolynomial.C a)^(4:ℕ) * MvPolynomial.C θ * MvPolynomial.X 0^(4:ℕ) * 68 + (MvPolynomial.C a)^(5:ℕ) * MvPolynomial.C θ * MvPolynomial.X 0^(3:ℕ) * MvPolynomial.X 1^(2:ℕ) * 32 + (MvPolynomial.C a)^(4:ℕ) * MvPolynomial.C θ * MvPolynomial.X 0^(3:ℕ) * MvPolynomial.X 1 * 1472 + (MvPolynomial.C a)^(4:ℕ) * MvPolynomial.C θ * MvPolynomial.X 0^(3:ℕ) * 32 + (MvPolynomial.C a)^(3:ℕ) * MvPolynomial.C θ * MvPolynomial.X 0^(3:ℕ) * 13632 + (MvPolynomial.C a)^(5:ℕ) * MvPolynomial.C θ * MvPolynomial.X 0^(2:ℕ) * MvPolynomial.X 1^(3:ℕ) * 168 + (MvPolynomial.C a)^(4:ℕ) * MvPolynomial.C θ * MvPolynomial.X 0^(2:ℕ) * MvPolynomial.X 1^(2:ℕ) * 9168 + (MvPolynomial.C a)^(4:ℕ) * MvPolynomial.C θ * MvPolynomial.X 0^(2:ℕ) * MvPolynomial.X 1 * 2688 + (MvPolynomial.C a)^(3:ℕ) * MvPolynomial.C θ * MvPolynomial.X 0^(2:ℕ) * MvPolynomial.X 1 * 145632 + (MvPolynomial.C a)^(3:ℕ) * MvPolynomial.C θ * MvPolynomial.X 0^(2:ℕ) * 88704 + (MvPolynomial.C a)^(2:ℕ) * MvPolynomial.C θ * MvPolynomial.X 0^(2:ℕ) * 708992 + (MvPolynomial.C a)^(5:ℕ) * MvPolynomial.C θ * MvPolynomial.X 0 * MvPolynomial.X 1^(4:ℕ) * 320 + (MvPolynomial.C a)^(5:ℕ) * MvPolynomial.C θ * MvPolynomial.X 0 * MvPolynomial.X 1^(3:ℕ) * 128 + (MvPolynomial.C a)^(4:ℕ) * MvPolynomial.C θ * MvPolynomial.X 0 * MvPolynomial.X 1^(3:ℕ) * 19712 + (MvPolynomial.C a)^(4:ℕ) * MvPolynomial.C θ * MvPolynomial.X 0 * MvPolynomial.X 1^(2:ℕ) * 42624 + (MvPolynomial.C a)^(3:ℕ) * MvPolynomial.C θ * MvPolynomial.X 0 * MvPolynomial.X 1^(2:ℕ) * 461568 + (MvPolynomial.C a)^(3:ℕ) * MvPolynomial.C θ * MvPolynomial.X 0 * MvPolynomial.X 1 * 1550848 + (MvPolynomial.C a)^(2:ℕ) * MvPolynomial.C θ * MvPolynomial.X 0 * MvPolynomial.X 1 * 4796416 + (MvPolynomial.C a)^(3:ℕ) * MvPolynomial.C θ * MvPolynomial.X 0 * 6144 + (MvPolynomial.C a)^(2:ℕ) * MvPolynomial.C θ * MvPolynomial.X 0 * 9676032 + MvPolynomial.C a * MvPolynomial.C θ * MvPolynomial.X 0 * 14039040 + (MvPolynomial.C a)^(5:ℕ) * MvPolynomial.C θ * MvPolynomial.X 1^(5:ℕ) * 160 + (MvPolynomial.C a)^(5:ℕ) * MvPolynomial.C θ * MvPolynomial.X 1^(4:ℕ) * 896 + (MvPolynomial.C a)^(4:ℕ) * MvPolynomial.C θ * MvPolynomial.X 1^(4:ℕ) * 12800 + (MvPolynomial.C a)^(4:ℕ) * MvPolynomial.C θ * MvPolynomial.X 1^(3:ℕ) * 154112 + (MvPolynomial.C a)^(3:ℕ) * MvPolynomial.C θ * MvPolynomial.X 1^(3:ℕ) * 510080 + (MvPolynomial.C a)^(4:ℕ) * MvPolynomial.C θ * MvPolynomial.X 1^(2:ℕ) * 512 + (MvPolynomial.C a)^(3:ℕ) * MvPolynomial.C θ * MvPolynomial.X 1^(2:ℕ) * 4979200 + (MvPolynomial.C a)^(2:ℕ) * MvPolynomial.C θ * MvPolynomial.X 1^(2:ℕ) * 8030720)

private noncomputable def E2d {R : Type*} [CommRing R] (a θ : R) : MvPolynomial (Fin 2) R :=
  ((MvPolynomial.C a)^(3:ℕ) * MvPolynomial.C θ * MvPolynomial.X 1 * 153088 + (MvPolynomial.C a)^(2:ℕ) * MvPolynomial.C θ * MvPolynomial.X 1 * 34980864 + MvPolynomial.C a * MvPolynomial.C θ * MvPolynomial.X 1 * 29870080 + (MvPolynomial.C a)^(2:ℕ) * MvPolynomial.C θ * 3224576 + MvPolynomial.C a * MvPolynomial.C θ * 15728640 - MvPolynomial.C θ * 12492800 + (MvPolynomial.C a)^(5:ℕ) * MvPolynomial.X 0^(4:ℕ) * MvPolynomial.X 1 * 4 + (MvPolynomial.C a)^(4:ℕ) * MvPolynomial.X 0^(4:ℕ) * 72 + (MvPolynomial.C a)^(5:ℕ) * MvPolynomial.X 0^(3:ℕ) * MvPolynomial.X 1^(2:ℕ) * 28 + (MvPolynomial.C a)^(4:ℕ) * MvPolynomial.X 0^(3:ℕ) * MvPolynomial.X 1 * 922 + (MvPolynomial.C a)^(4:ℕ) * MvPolynomial.X 0^(3:ℕ) * 384 + (MvPolynomial.C a)^(3:ℕ) * MvPolynomial.X 0^(3:ℕ) * 6221 + (MvPolynomial.C a)^(5:ℕ) * MvPolynomial.X 0^(2:ℕ) * MvPolynomial.X 1^(3:ℕ) * 80 + (MvPolynomial.C a)^(5:ℕ) * MvPolynomial.X 0^(2:ℕ) * MvPolynomial.X 1^(2:ℕ) * 96 + (MvPolynomial.C a)^(4:ℕ) * MvPolynomial.X 0^(2:ℕ) * MvPolynomial.X 1^(2:ℕ) * 3552 + (MvPolynomial.C a)^(4:ℕ) * MvPolynomial.X 0^(2:ℕ) * MvPolynomial.X 1 * 16608 + (MvPolynomial.C a)^(3:ℕ) * MvPolynomial.X 0^(2:ℕ) * MvPolynomial.X 1 * 41472 + (MvPolynomial.C a)^(3:ℕ) * MvPolynomial.X 0^(2:ℕ) * 274918 + (MvPolynomial.C a)^(2:ℕ) * MvPolynomial.X 0^(2:ℕ) * 110592 + (MvPolynomial.C a)^(5:ℕ) * MvPolynomial.X 0 * MvPolynomial.X 1^(4:ℕ) * 77 + (MvPolynomial.C a)^(5:ℕ) * MvPolynomial.X 0 * MvPolynomial.X 1^(3:ℕ) * 1536 + (MvPolynomial.C a)^(4:ℕ) * MvPolynomial.X 0 * MvPolynomial.X 1^(3:ℕ) * 3994 + (MvPolynomial.C a)^(4:ℕ) * MvPolynomial.X 0 * MvPolynomial.X 1^(2:ℕ) * 167424 + (MvPolynomial.C a)^(3:ℕ) * MvPolynomial.X 0 * MvPolynomial.X 1^(2:ℕ) * 58061 + (MvPolynomial.C a)^(4:ℕ) * MvPolynomial.X 0 * MvPolynomial.X 1 * 512 + (MvPolynomial.C a)^(3:ℕ) * MvPolynomial.X 0 * MvPolynomial.X 1 * 3469312 + (MvPolynomial.C a)^(2:ℕ) * MvPolynomial.X 0 * MvPolynomial.X 1 * 221184 + (MvPolynomial.C a)^(3:ℕ) * MvPolynomial.X 0 * 65792 + (MvPolynomial.C a)^(2:ℕ) * MvPolynomial.X 0 * 13596672 + (MvPolynomial.C a)^(6:ℕ) * MvPolynomial.X 1^(5:ℕ) * 6 + (MvPolynomial.C a)^(5:ℕ) * MvPolynomial.X 1^(4:ℕ) * 5120 + (MvPolynomial.C a)^(4:ℕ) * MvPolynomial.X 1^(3:ℕ) * 409933 + (MvPolynomial.C a)^(4:ℕ) * MvPolynomial.X 1^(2:ℕ) * 11264 + (MvPolynomial.C a)^(3:ℕ) * MvPolynomial.X 1^(2:ℕ) * 7820595 + (MvPolynomial.C a)^(3:ℕ) * MvPolynomial.X 1 * 1025024 + (MvPolynomial.C a)^(2:ℕ) * MvPolynomial.X 1 * 30754816 + (MvPolynomial.C a)^(3:ℕ) * 205 + (MvPolynomial.C a)^(2:ℕ) * 10960896 - MvPolynomial.C a * 12492800)

/-- The integral (characteristic-free) form of the factorisation identity: the difference of the two
sides is divisible by `5`. -/
private lemma master2 {R : Type*} [CommRing R] (a θ : R) :
    fac a θ 0 * fac a θ 1 * fac a θ 2 * fac a θ 3 * fac a θ 4
      - (MvPolynomial.C a) ^(3:ℕ) * Q2 a
      - ((MvPolynomial.C θ) ^(5:ℕ) - MvPolynomial.C θ - MvPolynomial.C a) * Rq2 a θ
      = 5 * (E2a a θ + E2b a θ + E2c a θ + E2d a θ) := by
  unfold fac Q2 Rq2 E2a E2b E2c E2d
  first | refl_ring1 | ring

/-! ## Rewriting lemmas -/

private lemma Pex (K : Type) [Field K] (g : K) :
    Work.MotAS.ASZElim.P 1 0 g
      = (MvPolynomial.C g) ^(2:ℕ) * MvPolynomial.X 0 ^(5:ℕ)
        - (2 * MvPolynomial.C g) * MvPolynomial.X 0 ^(3:ℕ) * MvPolynomial.X 1
        - (MvPolynomial.X 0 ^(3:ℕ)) + 2 * MvPolynomial.X 0 ^(2:ℕ)
        - (MvPolynomial.C g) ^(2:ℕ) * MvPolynomial.X 0 * MvPolynomial.X 1 ^(4:ℕ)
        - (2 * MvPolynomial.C g) * MvPolynomial.X 0 * MvPolynomial.X 1 ^(3:ℕ)
        - (MvPolynomial.X 0 * MvPolynomial.X 1 ^(2:ℕ))
        + (2 * (MvPolynomial.C g) ^(3:ℕ)) * MvPolynomial.X 1 ^(5:ℕ)
        - MvPolynomial.C g * MvPolynomial.X 1 ^(3:ℕ)
        + MvPolynomial.X 1 ^(2:ℕ) - 1 := by
  simp only [Work.MotAS.ASZElim.P, MvPolynomial.C_add, MvPolynomial.C_sub, MvPolynomial.C_mul,
    MvPolynomial.C_pow, MvPolynomial.C_neg, MvPolynomial.C_1, MvPolynomial.C_0,
    MvPolynomial.C_eq_coe_nat, C_two', C_three', C_four']
  refl_ring1

private lemma map_P_eq (K : Type) [Field K] (L : Type) [Field L] [Algebra K L] (g : K) :
    MvPolynomial.map (algebraMap K L) (Work.MotAS.ASZElim.P 1 0 g) = Q2 (algebraMap K L g) := by
  rw [Pex K g]
  simp only [Q2, map_add, map_sub, map_mul, map_pow, map_neg, map_one, map_zero, map_natCast,
    MvPolynomial.map_C, MvPolynomial.map_X, MvPolynomial.C_1, MvPolynomial.C_0,
    MvPolynomial.C_mul, MvPolynomial.C_pow, MvPolynomial.C_add, MvPolynomial.C_sub,
    MvPolynomial.C_neg, MvPolynomial.C_eq_coe_nat, C_two', C_three', C_four', map_two', alg_two']
  refl_ring1

private lemma fac_target {R : Type*} [CommRing R] (a θ : R) (k : ℕ) :
    fac a θ k = MvPolynomial.C a * MvPolynomial.X 0
      + MvPolynomial.C (2 * a * (θ + (k : R))) * MvPolynomial.X 1
      + MvPolynomial.C (4 * ((θ + (k : R)) ^(3:ℕ) - (θ + (k : R)))) := by
  simp only [fac, MvPolynomial.C_add, MvPolynomial.C_sub, MvPolynomial.C_mul, MvPolynomial.C_pow,
    MvPolynomial.C_neg, MvPolynomial.C_1, MvPolynomial.C_0, MvPolynomial.C_eq_coe_nat,
    C_two', C_three', C_four']

private lemma castHom_val (K : Type) [Field K] [CharP K 5] (L : Type) [Field L] [Algebra K L]
    (k : ℕ) :
    algebraMap K L (ZMod.castHom (dvd_refl 5) K (k : ZMod 5)) = (k : L) := by
  rw [map_natCast (ZMod.castHom (dvd_refl 5) K) k, map_natCast (algebraMap K L) k]

private lemma zmod5_prod {M : Type*} [CommMonoid M] (G : ZMod 5 → M) :
    (∏ i : ZMod 5, G i) = G 0 * G 1 * G 2 * G 3 * G 4 := by
  have h0 : (0 : ZMod 5) ∉ (insert 1 (insert 2 (insert 3 (insert 4 (∅ : Finset (ZMod 5)))))) := by
    decide
  have h1 : (1 : ZMod 5) ∉ (insert 2 (insert 3 (insert 4 (∅ : Finset (ZMod 5))))) := by decide
  have h2 : (2 : ZMod 5) ∉ (insert 3 (insert 4 (∅ : Finset (ZMod 5)))) := by decide
  have h3 : (3 : ZMod 5) ∉ (insert 4 (∅ : Finset (ZMod 5))) := by decide
  have h4 : (4 : ZMod 5) ∉ (∅ : Finset (ZMod 5)) := by decide
  rw [show (Finset.univ : Finset (ZMod 5))
      = insert 0 (insert 1 (insert 2 (insert 3 (insert 4 (∅ : Finset (ZMod 5)))))) from by decide]
  rw [Finset.prod_insert h0, Finset.prod_insert h1, Finset.prod_insert h2, Finset.prod_insert h3,
    Finset.prod_insert h4, Finset.prod_empty]
  simp only [mul_assoc, mul_one]

private lemma fac_eq_zmodk (K : Type) [Field K] [CharP K 5] (L : Type) [Field L] [Algebra K L]
    (g : K) (θ : L) (k : ℕ) :
    (MvPolynomial.C (algebraMap K L g) * MvPolynomial.X (0 : Fin 2)
      + MvPolynomial.C (2 * algebraMap K L g
          * (θ + algebraMap K L (ZMod.castHom (dvd_refl 5) K (k : ZMod 5)))) * MvPolynomial.X (1 : Fin 2)
      + MvPolynomial.C (4 * ((θ + algebraMap K L (ZMod.castHom (dvd_refl 5) K (k : ZMod 5))) ^(3:ℕ)
          - (θ + algebraMap K L (ZMod.castHom (dvd_refl 5) K (k : ZMod 5))))))
    = fac (algebraMap K L g) θ k := by
  rw [castHom_val K L k]
  exact (fac_target (algebraMap K L g) θ k).symm

/-! ## The factorisation identity -/

private lemma ASZB0FacL_aux (K : Type) [Field K] [CharP K 5] (L : Type) [Field L] [Algebra K L]
    (g : K) (θ : L) (hθ : θ ^(5:ℕ) - θ = algebraMap K L g) :
    (∏ i : ZMod 5,
        (MvPolynomial.C (algebraMap K L g) * MvPolynomial.X (0 : Fin 2)
          + MvPolynomial.C (2 * algebraMap K L g
              * (θ + algebraMap K L (ZMod.castHom (dvd_refl 5) K i))) * MvPolynomial.X (1 : Fin 2)
          + MvPolynomial.C (4 * ((θ + algebraMap K L (ZMod.castHom (dvd_refl 5) K i)) ^(3:ℕ)
              - (θ + algebraMap K L (ZMod.castHom (dvd_refl 5) K i))))))
      = MvPolynomial.C ((algebraMap K L g) ^(3:ℕ))
          * MvPolynomial.map (algebraMap K L) (Work.MotAS.ASZElim.P 1 0 g) := by
  have h5L : ((5 : ℕ) : L) = 0 := by
    rw [← map_natCast (algebraMap K L) 5, CharP.cast_eq_zero K 5, map_zero]
  have h5 : (5 : MvPolynomial (Fin 2) L) = 0 := by
    rw [← Nat.cast_ofNat (n := 5), ← MvPolynomial.C_eq_coe_nat, h5L, MvPolynomial.C_0]
  have hθ0 : θ ^(5:ℕ) - θ - algebraMap K L g = 0 := sub_eq_zero.mpr hθ
  have hfac0 : ((MvPolynomial.C θ) ^(5:ℕ) - MvPolynomial.C θ - MvPolynomial.C (algebraMap K L g)
      : MvPolynomial (Fin 2) L) = 0 := by
    rw [← MvPolynomial.C_pow, ← MvPolynomial.C_sub, ← MvPolynomial.C_sub, hθ0, MvPolynomial.C_0]
  have hkey := master2 (algebraMap K L g) θ
  rw [h5, zero_mul, hfac0, zero_mul, sub_zero] at hkey
  rw [map_P_eq K L g]
  rw [MvPolynomial.C_pow]
  rw [zmod5_prod]
  try dsimp only
  rw [show (0 : ZMod 5) = ((0 : ℕ) : ZMod 5) from by decide,
      show (1 : ZMod 5) = ((1 : ℕ) : ZMod 5) from by decide,
      show (2 : ZMod 5) = ((2 : ℕ) : ZMod 5) from by decide,
      show (3 : ZMod 5) = ((3 : ℕ) : ZMod 5) from by decide,
      show (4 : ZMod 5) = ((4 : ℕ) : ZMod 5) from by decide]
  rw [fac_eq_zmodk K L g θ 0, fac_eq_zmodk K L g θ 1, fac_eq_zmodk K L g θ 2,
    fac_eq_zmodk K L g θ 3, fac_eq_zmodk K L g θ 4]
  linear_combination (norm := refl_ring1) hkey

theorem ASZB0FacL (K : Type) [Field K] [CharP K 5] (L : Type) [Field L] [Algebra K L]
    (g : K) (θ : L) (hθ : θ ^(5:ℕ) - θ = algebraMap K L g) :
    (∏ i : ZMod 5,
        (MvPolynomial.C (algebraMap K L g) * MvPolynomial.X (0 : Fin 2)
          + MvPolynomial.C (2 * algebraMap K L g * (θ + algebraMap K L (ZMod.castHom (dvd_refl 5) K i))) * MvPolynomial.X (1 : Fin 2)
          + MvPolynomial.C (4 * ((θ + algebraMap K L (ZMod.castHom (dvd_refl 5) K i)) ^(3:ℕ) - (θ + algebraMap K L (ZMod.castHom (dvd_refl 5) K i))))))
      = MvPolynomial.C ((algebraMap K L g) ^(3:ℕ))
          * MvPolynomial.map (algebraMap K L) (Work.MotAS.ASZElim.P 1 0 g) :=
  ASZB0FacL_aux K L g θ hθ

end Work.MotAS
