import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Submission.Work.FTS.PhiStar.RadGreenSupport.ibp_upper
import Submission.Work.FTS.PhiStar.Series.Weil.integrableOn_prod_mul
import Submission.Work.FTS_RegExport.RXT.contDiffOn_two_integral_Itheta
import Submission.Work.FTS_RegExport.RXT.radial_noDecay_le
import Submission.Work.H2.T1Q.IbpCutoff
import Submission.Work.LWP.BiotSavart.nearField_bound
import Submission.Work.Spaces.sq_mul_div_rpow

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real
open MeasureTheory

namespace Work.FTS.PhiStar.Gegenbauer

/-- `gC k` is continuous. -/
lemma continuous_gC (k : ℕ) : Continuous (gC k) := (contDiff_gC k).continuous

attribute [local fun_prop] continuous_gC

/-- Pointwise form of the three-term recurrence specialised to `x · gC (k+1)`:
`x gC (k+1) x = ((k+2) gC (k+2) x + (k+3) gC k x) / (2k+5)`. -/
lemma gC_mul_x_succ (k : ℕ) (x : ℝ) :
    x * gC (k + 1) x
      = (((k : ℝ) + 2) * gC (k + 2) x + ((k : ℝ) + 3) * gC k x) / (2 * (k : ℝ) + 5) := by
  rw [eq_div_iff (by positivity : (2 * (k : ℝ) + 5) ≠ 0)]
  linarith [gC_rec k x]

/-- The half-interval Gegenbauer norm `∫_0^1 (1 - x²) gC k x ² dx`. -/
def Mhalf (k : ℕ) : ℝ := ∫ x in (0 : ℝ)..1, (1 - x ^ 2) * gC k x ^ 2

lemma Mhalf_zero : Mhalf 0 = 2 / 3 := by
  unfold Mhalf
  have h : (∫ x in (0 : ℝ)..1, (1 - x ^ 2) * gC 0 x ^ 2)
      = ∫ x in (0 : ℝ)..1, (1 - x ^ 2) := by
    refine intervalIntegral.integral_congr (fun x _ => ?_)
    rw [show gC 0 x = 1 from rfl]
    ring
  rw [h, intervalIntegral.integral_sub
      (Continuous.intervalIntegrable (by fun_prop) 0 1)
      (Continuous.intervalIntegrable (by fun_prop) 0 1)]
  rw [integral_one, integral_pow]
  norm_num

lemma Mhalf_one : Mhalf 1 = 6 / 5 := by
  unfold Mhalf
  have h : (∫ x in (0 : ℝ)..1, (1 - x ^ 2) * gC 1 x ^ 2)
      = ∫ x in (0 : ℝ)..1, (9 * x ^ 2 - 9 * x ^ 4) := by
    refine intervalIntegral.integral_congr (fun x _ => ?_)
    rw [show gC 1 x = 3 * x from rfl]
    ring
  rw [h, intervalIntegral.integral_sub
      (Continuous.intervalIntegrable (by fun_prop) 0 1)
      (Continuous.intervalIntegrable (by fun_prop) 0 1)]
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    integral_pow, integral_pow]
  norm_num

/-- The norm recursion: `Mhalf (j+2)` in terms of `Mhalf (j+1)`, using the recurrence twice
together with the equal-parity orthogonality (supplied as `hAB`, `hCD`). -/
lemma Mhalf_rec_of (j : ℕ)
    (hAB : (∫ x in (0 : ℝ)..1, (1 - x ^ 2) * gC j x * gC (j + 2) x) = 0)
    (hCD : (∫ x in (0 : ℝ)..1, (1 - x ^ 2) * gC (j + 1) x * gC (j + 3) x) = 0) :
    ((j : ℝ) + 2) * Mhalf (j + 2)
      = ((2 * (j : ℝ) + 5) * ((j : ℝ) + 4) / (2 * (j : ℝ) + 7)) * Mhalf (j + 1) := by
  have hA : (∫ x in (0 : ℝ)..1, (1 - x ^ 2) * x * gC (j + 1) x * gC (j + 2) x)
      = (((j : ℝ) + 4) / (2 * (j : ℝ) + 7)) * Mhalf (j + 1) := by
    have hpt : ∀ x : ℝ,
        (1 - x ^ 2) * x * gC (j + 1) x * gC (j + 2) x
          = (1 / (2 * (j : ℝ) + 7)) * (((j : ℝ) + 3) * ((1 - x ^ 2) * gC (j + 1) x * gC (j + 3) x)
              + ((j : ℝ) + 4) * ((1 - x ^ 2) * gC (j + 1) x ^ 2)) := by
      intro x
      have h := gC_mul_x_succ (j + 1) x
      simp only [show (j + 1) + 1 = j + 2 from rfl, show (j + 1) + 2 = j + 3 from rfl] at h
      push_cast at h
      rw [show ((j : ℝ) + 1) + 2 = (j : ℝ) + 3 from by ring,
          show ((j : ℝ) + 1) + 3 = (j : ℝ) + 4 from by ring,
          show 2 * ((j : ℝ) + 1) + 5 = 2 * (j : ℝ) + 7 from by ring] at h
      calc (1 - x ^ 2) * x * gC (j + 1) x * gC (j + 2) x
          = ((1 - x ^ 2) * gC (j + 1) x) * (x * gC (j + 2) x) := by ring
        _ = ((1 - x ^ 2) * gC (j + 1) x)
              * ((((j : ℝ) + 3) * gC (j + 3) x + ((j : ℝ) + 4) * gC (j + 1) x)
                  / (2 * (j : ℝ) + 7)) := by rw [h]
        _ = (1 / (2 * (j : ℝ) + 7)) * (((j : ℝ) + 3) * ((1 - x ^ 2) * gC (j + 1) x * gC (j + 3) x)
              + ((j : ℝ) + 4) * ((1 - x ^ 2) * gC (j + 1) x ^ 2)) := by ring
    rw [show (∫ x in (0 : ℝ)..1, (1 - x ^ 2) * x * gC (j + 1) x * gC (j + 2) x)
        = ∫ x in (0 : ℝ)..1, (1 / (2 * (j : ℝ) + 7))
            * (((j : ℝ) + 3) * ((1 - x ^ 2) * gC (j + 1) x * gC (j + 3) x)
              + ((j : ℝ) + 4) * ((1 - x ^ 2) * gC (j + 1) x ^ 2)) from
      intervalIntegral.integral_congr (fun x _ => hpt x)]
    rw [intervalIntegral.integral_const_mul,
      intervalIntegral.integral_add
        (Continuous.intervalIntegrable (by fun_prop) 0 1)
        (Continuous.intervalIntegrable (by fun_prop) 0 1),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul, hCD]
    rw [mul_zero, zero_add, show (∫ x in (0 : ℝ)..1, (1 - x ^ 2) * gC (j + 1) x ^ 2)
      = Mhalf (j + 1) from rfl]
    ring
  have hB : ((j : ℝ) + 2) * Mhalf (j + 2)
      = (2 * (j : ℝ) + 5) * (∫ x in (0 : ℝ)..1, (1 - x ^ 2) * x * gC (j + 1) x * gC (j + 2) x) := by
    have hpt : ∀ x : ℝ,
        ((j : ℝ) + 2) * ((1 - x ^ 2) * gC (j + 2) x ^ 2)
          = (2 * (j : ℝ) + 5) * ((1 - x ^ 2) * x * gC (j + 1) x * gC (j + 2) x)
            - ((j : ℝ) + 3) * ((1 - x ^ 2) * gC j x * gC (j + 2) x) := by
      intro x
      have h := gC_rec j x
      calc ((j : ℝ) + 2) * ((1 - x ^ 2) * gC (j + 2) x ^ 2)
          = ((1 - x ^ 2) * gC (j + 2) x) * (((j : ℝ) + 2) * gC (j + 2) x) := by ring
        _ = ((1 - x ^ 2) * gC (j + 2) x)
              * ((2 * (j : ℝ) + 5) * x * gC (j + 1) x - ((j : ℝ) + 3) * gC j x) := by rw [h]
        _ = (2 * (j : ℝ) + 5) * ((1 - x ^ 2) * x * gC (j + 1) x * gC (j + 2) x)
            - ((j : ℝ) + 3) * ((1 - x ^ 2) * gC j x * gC (j + 2) x) := by ring
    unfold Mhalf
    rw [← intervalIntegral.integral_const_mul]
    rw [show (∫ x in (0 : ℝ)..1, ((j : ℝ) + 2) * ((1 - x ^ 2) * gC (j + 2) x ^ 2))
        = ∫ x in (0 : ℝ)..1, ((2 * (j : ℝ) + 5)
            * ((1 - x ^ 2) * x * gC (j + 1) x * gC (j + 2) x)
            - ((j : ℝ) + 3) * ((1 - x ^ 2) * gC j x * gC (j + 2) x)) from
      intervalIntegral.integral_congr (fun x _ => hpt x)]
    rw [intervalIntegral.integral_sub
        (Continuous.intervalIntegrable (by fun_prop) 0 1)
        (Continuous.intervalIntegrable (by fun_prop) 0 1),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul, hAB]
    ring
  rw [hB, hA]
  ring

/-- The closed form of the half-interval Gegenbauer norm, from the equal-parity
orthogonality hypothesis. -/
lemma Mhalf_closed_of
    (horth : ∀ p q : ℕ, p ≠ q → Even (p + q) →
      (∫ x in (0 : ℝ)..1, (1 - x ^ 2) * gC p x * gC q x) = 0)
    (k : ℕ) : Mhalf k = ((k : ℝ) + 1) * ((k : ℝ) + 2) / (2 * (k : ℝ) + 3) := by
  induction k using Nat.twoStepInduction with
  | zero => rw [Mhalf_zero]; norm_num
  | one => rw [Mhalf_one]; norm_num
  | more j ih1 ih2 =>
    have hrec := Mhalf_rec_of j (horth j (j + 2) (by omega) ⟨j + 1, by ring⟩)
      (horth (j + 1) (j + 3) (by omega) ⟨j + 2, by ring⟩)
    have ih2' : Mhalf (j + 1) = ((j : ℝ) + 2) * ((j : ℝ) + 3) / (2 * (j : ℝ) + 5) := by
      rw [ih2]; push_cast; ring
    rw [ih2'] at hrec
    push_cast
    rw [show ((j : ℝ) + 2 + 1) = (j : ℝ) + 3 from by ring,
        show ((j : ℝ) + 2 + 2) = (j : ℝ) + 4 from by ring,
        show 2 * ((j : ℝ) + 2) + 3 = 2 * (j : ℝ) + 7 from by ring]
    have hgoal : ((j : ℝ) + 3) * ((j : ℝ) + 4) / (2 * (j : ℝ) + 7)
        = ((2 * (j : ℝ) + 5) * ((j : ℝ) + 4) / (2 * (j : ℝ) + 7))
            * (((j : ℝ) + 2) * ((j : ℝ) + 3) / (2 * (j : ℝ) + 5)) / ((j : ℝ) + 2) := by
      field_simp
    rw [hgoal, ← hrec]
    rw [eq_div_iff (by positivity : ((j : ℝ) + 2) ≠ 0)]
    ring

/-- The closed form `∫_0^1 (1 - x²) gC k x ² dx = (k+1)(k+2)/(2k+3)`. -/
lemma Mhalf_closed (k : ℕ) :
    Mhalf k = ((k : ℝ) + 1) * ((k : ℝ) + 2) / (2 * (k : ℝ) + 3) :=
  Mhalf_closed_of (fun p q hpq hpar => gC_orthogonal_half p q hpq hpar) k

theorem eFam_norm_fts (m : ℕ) :
    ∫ θ in Work.Spaces.Iθ, Work.FTS.PhiStar.Gegenbauer.eFam m θ ^ 2 * Real.cos θ
      = ((2 * (m : ℝ) + 2) * (2 * (m : ℝ) + 3)) / (4 * (m : ℝ) + 5) := by
  rw [eFam_norm_subst m]
  change Mhalf (2 * m + 1) = _
  rw [Mhalf_closed]
  push_cast
  ring

end Work.FTS.PhiStar.Gegenbauer
