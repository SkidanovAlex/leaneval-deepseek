import Mathlib
import Submission.Work.ALift.bridge

/-!
# Area ALift — the Zagier operator for `H`, and the evaluation bridges

`Submission.CDT.HA_odeLHS` is the order-2 operator `P·y'' + Q·y' + R·y` with `P = x(1-x)(1-9x)`,
`Q = 1-20x+27x²`, `R = -3+9x`, written out with PowerSeries.  Here we

* split it into its three factors `HA_PA, HA_QA, HA_RA`;
* record the formal identity `HA_odeLHS (HZ a b c) = C b + C c·(1-X)⁻¹` (from
  `ZagierH_odeLHS_coeff`);
* provide the evaluation bridges `evA Pdpoly q = Pd q` (and `Qd`, `Rd`, and
  `evA ((1-X)⁻¹) q = (1-q)⁻¹`, `evA (C b + C c·(1-X)⁻¹) q = b + c/(1-q)`), so that the analytic
  reading `Pd q * HU2 + Qd q * HU1 + Rd q * HU0` of the operator can be compared with the
  inhomogeneity (see `HU_ode`).
-/

open PowerSeries
open scoped BigOperators

namespace Work.ALift

open Submission.CDTPlan

noncomputable section

/-! ## Factorisation of the operator -/

/-- `P(x) = x - 10x² + 9x³ = x(1-x)(1-9x)`, as a power series. -/
def HA_PA : PowerSeries ℚ :=
  PowerSeries.X - PowerSeries.C 10 * PowerSeries.X ^ 2 + PowerSeries.C 9 * PowerSeries.X ^ 3

/-- `Q(x) = 1 - 20x + 27x²`, as a power series. -/
def HA_QA : PowerSeries ℚ :=
  1 - PowerSeries.C 20 * PowerSeries.X + PowerSeries.C 27 * PowerSeries.X ^ 2

/-- `R(x) = -3 + 9x`, as a power series. -/
def HA_RA : PowerSeries ℚ := -PowerSeries.C 3 + PowerSeries.C 9 * PowerSeries.X

/-- The operator `HA_odeLHS` is `P·y'' + Q·y' + R·y`. -/
lemma HA_odeLHS_eq (y : PowerSeries ℚ) :
    Submission.CDT.HA_odeLHS y
      = HA_PA * PowerSeries.derivative (R := ℚ) (PowerSeries.derivative (R := ℚ) y)
        + HA_QA * PowerSeries.derivative (R := ℚ) y + HA_RA * y := rfl

/-- **The formal ODE for `H = aH_A + bH_B + cH_C`**: the operator applied to `H` is the
inhomogeneity `b + c/(1-x)`. -/
theorem HZ_odeLHS (a b c : ℤ) :
    Submission.CDT.HA_odeLHS (HZ a b c)
      = PowerSeries.C (b : ℚ) + PowerSeries.C (c : ℚ) * ((1 : PowerSeries ℚ) - PowerSeries.X)⁻¹ := by
  apply PowerSeries.ext
  intro n
  unfold Submission.CDTPlan.HZ
  rw [Submission.CDT.ZagierH_odeLHS_coeff]
  rw [map_add, PowerSeries.coeff_C, PowerSeries.coeff_C_mul,
    Submission.CDT.coeff_inv_one_sub_eq_one]
  by_cases h : n = 0 <;> simp [h]

/-! ## Polynomial versions and the evaluation bridges -/

/-- `P` as a polynomial. -/
def Pdpoly : Polynomial ℚ :=
  Polynomial.X - Polynomial.C 10 * Polynomial.X ^ 2 + Polynomial.C 9 * Polynomial.X ^ 3

/-- `Q` as a polynomial. -/
def Qdpoly : Polynomial ℚ :=
  1 - Polynomial.C 20 * Polynomial.X + Polynomial.C 27 * Polynomial.X ^ 2

/-- `R` as a polynomial. -/
def Rdpoly : Polynomial ℚ := -Polynomial.C 3 + Polynomial.C 9 * Polynomial.X

lemma Pdpoly_coe : ((Pdpoly : Polynomial ℚ) : PowerSeries ℚ) = HA_PA := by
  simp only [Pdpoly, HA_PA]; push_cast; ring

lemma Qdpoly_coe : ((Qdpoly : Polynomial ℚ) : PowerSeries ℚ) = HA_QA := by
  simp only [Qdpoly, HA_QA]; push_cast; ring

lemma Rdpoly_coe : ((Rdpoly : Polynomial ℚ) : PowerSeries ℚ) = HA_RA := by
  simp only [Rdpoly, HA_RA]; push_cast; ring

lemma evA_Pd (q : ℂ) : Work.CLift.evA (Pdpoly : PowerSeries ℚ) q = Pd q := by
  rw [Work.CLift.evA_coe_poly]
  simp only [Pdpoly, Pd, Polynomial.eval₂_add, Polynomial.eval₂_sub, Polynomial.eval₂_mul,
    Polynomial.eval₂_pow, Polynomial.eval₂_C, Polynomial.eval₂_X, Polynomial.eval₂_one,
    Polynomial.eval₂_neg]
  norm_num
  try ring

lemma evA_Qd (q : ℂ) : Work.CLift.evA (Qdpoly : PowerSeries ℚ) q = Qd q := by
  rw [Work.CLift.evA_coe_poly]
  simp only [Qdpoly, Qd, Polynomial.eval₂_add, Polynomial.eval₂_sub, Polynomial.eval₂_mul,
    Polynomial.eval₂_pow, Polynomial.eval₂_C, Polynomial.eval₂_X, Polynomial.eval₂_one,
    Polynomial.eval₂_neg]
  norm_num
  try ring

lemma evA_Rd (q : ℂ) : Work.CLift.evA (Rdpoly : PowerSeries ℚ) q = Rd q := by
  rw [Work.CLift.evA_coe_poly]
  simp only [Rdpoly, Rd, Polynomial.eval₂_add, Polynomial.eval₂_mul,
    Polynomial.eval₂_C, Polynomial.eval₂_X, Polynomial.eval₂_neg]
  norm_num
  try ring

/-- `evA ((1-X)⁻¹) q = 1/(1-q)`: every coefficient of `(1-X)⁻¹` is `1`. -/
lemma evA_inv_one_sub (q : ℂ) (hq : ‖q‖ < 1) :
    Work.CLift.evA ((1 : PowerSeries ℚ) - PowerSeries.X)⁻¹ q = (1 - q)⁻¹ := by
  rw [Work.CLift.evA]
  have h : (fun k : ℕ =>
      ((PowerSeries.coeff k ((1 : PowerSeries ℚ) - PowerSeries.X)⁻¹ : ℚ) : ℂ) * q ^ k)
      = fun k : ℕ => q ^ k := by
    funext k
    rw [Submission.CDT.coeff_inv_one_sub_eq_one]; simp
  rw [h, tsum_geometric_of_norm_lt_one hq]

/-- The inhomogeneity is the evaluation of the formal right-hand side:
`evA (C b + C c·(1-X)⁻¹) q = b + c/(1-q)`. -/
lemma evA_rhs (b c : ℤ) (q : ℂ) (hq : ‖q‖ < 1) :
    Work.CLift.evA (PowerSeries.C (b : ℚ) + PowerSeries.C (c : ℚ)
      * ((1 : PowerSeries ℚ) - PowerSeries.X)⁻¹) q = rhsA b c q := by
  have hcoeff : ∀ n : ℕ, PowerSeries.coeff n (PowerSeries.C (b : ℚ) + PowerSeries.C (c : ℚ)
      * ((1 : PowerSeries ℚ) - PowerSeries.X)⁻¹)
      = (if n = 0 then (b : ℚ) else 0) + (c : ℚ) := by
    intro n
    rw [map_add, PowerSeries.coeff_C, PowerSeries.coeff_C_mul,
      Submission.CDT.coeff_inv_one_sub_eq_one]
    ring
  rw [Work.CLift.evA]
  have hpt : ∀ n : ℕ, ((PowerSeries.coeff n (PowerSeries.C (b : ℚ) + PowerSeries.C (c : ℚ)
        * ((1 : PowerSeries ℚ) - PowerSeries.X)⁻¹) : ℚ) : ℂ) * q ^ n
      = (((if n = 0 then (b : ℚ) else 0) : ℚ) : ℂ) * q ^ n + ((c : ℚ) : ℂ) * q ^ n := by
    intro n
    rw [hcoeff n]
    push_cast
    ring
  have hsum1 : Summable (fun n : ℕ => (((if n = 0 then (b : ℚ) else 0) : ℚ) : ℂ) * q ^ n) := by
    refine summable_of_ne_finset_zero (s := {0}) ?_
    intro n hn
    rw [Finset.mem_singleton] at hn
    simp [hn]
  have ht1 : (∑' n : ℕ, (((if n = 0 then (b : ℚ) else 0) : ℚ) : ℂ) * q ^ n) = (b : ℂ) := by
    rw [tsum_eq_single 0]
    · simp
    · intro n hn
      simp [hn]
  have h1 : HasSum (fun n : ℕ => (((if n = 0 then (b : ℚ) else 0) : ℚ) : ℂ) * q ^ n) (b : ℂ) := by
    have := hsum1.hasSum
    rwa [ht1] at this
  have h2 : HasSum (fun n : ℕ => ((c : ℚ) : ℂ) * q ^ n) ((c : ℂ) * (1 - q)⁻¹) :=
    (hasSum_geometric_of_norm_lt_one hq).mul_left _
  refine (tsum_congr hpt).trans ?_
  have key := (h1.add h2).tsum_eq
  rw [key, rhsA, div_eq_mul_inv]
  try ring

end

end Work.ALift
