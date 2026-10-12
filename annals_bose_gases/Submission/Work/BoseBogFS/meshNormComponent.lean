import Mathlib.Algebra.BigOperators.Field
import Mathlib.Tactic.NormNum.BigOperators
import Mathlib.Algebra.Order.Star.Real
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseBogFS

/-- Pure arithmetic core: for nonnegative `u`, the Euclidean norm of `u + 1/2`
dominates the Euclidean norm of `u` plus `1/2`.  This is the reason the "mesh
separation" `|p i| ≥ c (|M i|/σ + 1/2)` can be passed through the Euclidean norm
without losing the additive `c/2`. -/
theorem sqrt_norm_add_half {u : Fin 3 → ℝ} (hu : ∀ i, 0 ≤ u i) :
    Real.sqrt (∑ i, u i ^ 2) + 1 / 2 ≤ Real.sqrt (∑ i, (u i + 1 / 2) ^ 2) := by
  have hA : 0 ≤ ∑ i, u i ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
  have hV : 0 ≤ ∑ i, u i := Finset.sum_nonneg fun i _ => hu i
  have hsq : ∑ i, u i ^ 2 ≤ (∑ i, u i) ^ 2 :=
    Finset.sum_sq_le_sq_sum_of_nonneg fun i _ => hu i
  have hAle : Real.sqrt (∑ i, u i ^ 2) ≤ ∑ i, u i := by
    have := Real.sqrt_le_sqrt hsq
    rwa [Real.sqrt_sq hV] at this
  refine Real.le_sqrt_of_sq_le ?_
  have h1 : ∑ i, (u i + 1 / 2) ^ 2 = (∑ i, u i ^ 2) + (∑ i, u i) + 3 / 4 := by
    have hc' : ∀ i, (u i + 1 / 2) ^ 2 = u i ^ 2 + u i + 1 / 4 := fun i => by ring
    rw [Finset.sum_congr rfl fun i _ => hc' i]
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
    norm_num [Finset.sum_const, Finset.card_univ]
  have h2 : (Real.sqrt (∑ i, u i ^ 2) + 1 / 2) ^ 2
      = (∑ i, u i ^ 2) + Real.sqrt (∑ i, u i ^ 2) + 1 / 4 := by
    rw [add_sq, Real.sq_sqrt hA]
    ring
  rw [h1, h2]
  linarith

theorem meshNormComponent {σ c : ℝ} (hσ : 0 < σ) (hc : 0 < c) {M p : Fin 3 → ℝ}
    (h : ∀ i, c * (|M i| / σ + 1 / 2) ≤ |p i|) :
    c * (Real.sqrt (∑ i, M i ^ 2) / σ + 1 / 2) ≤ Real.sqrt (∑ i, p i ^ 2) := by
  have hsc : 0 ≤ c := hc.le
  have hstep : Real.sqrt (∑ i, M i ^ 2) / σ + 1 / 2 ≤
      Real.sqrt (∑ i, (|M i| / σ + 1 / 2) ^ 2) := by
    have hu : ∀ i, 0 ≤ |M i| / σ := fun i => div_nonneg (abs_nonneg _) hσ.le
    have hmain := sqrt_norm_add_half (u := fun i => |M i| / σ) hu
    have heq : Real.sqrt (∑ i, (|M i| / σ) ^ 2) = Real.sqrt (∑ i, M i ^ 2) / σ := by
      have hsum : ∑ i, (|M i| / σ) ^ 2 = (∑ i, M i ^ 2) / σ ^ 2 := by
        rw [Finset.sum_div]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [div_pow, sq_abs]
      rw [hsum]
      rw [show (∑ i, M i ^ 2) / σ ^ 2 = (Real.sqrt (∑ i, M i ^ 2) / σ) ^ 2 by
            rw [div_pow, Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg _)]]
      rw [Real.sqrt_sq (by positivity)]
    linarith [hmain, heq]
  have hsq : ∀ i, (c * (|M i| / σ + 1 / 2)) ^ 2 ≤ p i ^ 2 := by
    intro i
    have h2 : 0 ≤ c * (|M i| / σ + 1 / 2) := by positivity
    have h1 : c * (|M i| / σ + 1 / 2) ≤ |p i| := h i
    rw [show p i ^ 2 = |p i| ^ 2 from (sq_abs (p i)).symm]
    exact sq_le_sq.mpr (by rwa [abs_of_nonneg h2, abs_of_nonneg (abs_nonneg (p i))])
  have hsum_le : ∑ i, (c * (|M i| / σ + 1 / 2)) ^ 2 ≤ ∑ i, p i ^ 2 :=
    Finset.sum_le_sum fun i _ => hsq i
  have hfac : ∑ i, (c * (|M i| / σ + 1 / 2)) ^ 2 =
      c ^ 2 * ∑ i, (|M i| / σ + 1 / 2) ^ 2 := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  have hsqrtfac : Real.sqrt (∑ i, (c * (|M i| / σ + 1 / 2)) ^ 2)
      = c * Real.sqrt (∑ i, (|M i| / σ + 1 / 2) ^ 2) := by
    rw [hfac, Real.sqrt_mul (sq_nonneg c), Real.sqrt_sq hsc]
  calc c * (Real.sqrt (∑ i, M i ^ 2) / σ + 1 / 2)
      ≤ c * Real.sqrt (∑ i, (|M i| / σ + 1 / 2) ^ 2) := mul_le_mul_of_nonneg_left hstep hsc
    _ = Real.sqrt (∑ i, (c * (|M i| / σ + 1 / 2)) ^ 2) := hsqrtfac.symm
    _ ≤ Real.sqrt (∑ i, p i ^ 2) := Real.sqrt_le_sqrt hsum_le

end Work.BoseBogFS
