import Mathlib.Analysis.Calculus.TaylorIntegral
import Submission.Work.Conv3SmallC2
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# A4 — the second-order Taylor remainder bound for a `C²` function on `ℝ³`

First piece of the Taylor-remainder stage of `conv3Small_quadratic_dev`:
the abstract second-order Taylor bound, from Mathlib's Taylor formula with
integral remainder (`map_add_eq_sum_add_integral_iteratedFDeriv`, `n = 1`) —
for `f : ℝ³ → ℝ` of class `C²` with the second iterated derivative bounded
by `B` on the unit ball,

    ‖f t − f 0 − (fderiv f 0) t‖ ≤ B·‖t‖²    (‖t‖ ≤ 1).

The integral remainder is bounded pointwise
(`intervalIntegral.norm_integral_le_of_norm_le_const`) using the multilinear
operator bound `ContinuousMultilinearMap.le_opNorm`.
-/

noncomputable section
open MeasureTheory Metric Filter
open scoped Real Topology ContDiff
namespace Submission
set_option autoImplicit false
set_option linter.unusedVariables false
namespace BoseGases

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-- **second-order Taylor remainder bound on `ℝ³`**: for `f : ℝ³ → ℝ` of
class `C²` whose second iterated derivative is bounded by `B` on the unit
ball, `‖f t − f 0 − (fderiv f 0) t‖ ≤ B·‖t‖²` for `‖t‖ ≤ 1`. -/
lemma taylor_second_order_remainder_le {f : ℝ³ → ℝ} {B : ℝ} (hB : 0 ≤ B)
    (hf : ContDiff ℝ 2 f) (hbd : ∀ z : ℝ³, ‖z‖ ≤ 1 → ‖iteratedFDeriv ℝ 2 f z‖ ≤ B)
    {t : ℝ³} (ht : ‖t‖ ≤ 1) :
    ‖f t - f 0 - fderiv ℝ f 0 t‖ ≤ B * ‖t‖ ^ 2 := by
  have hseg : ∀ s ∈ Set.Icc (0 : ℝ) 1, ContDiffAt ℝ ((1 : ℕ) + 1 : ℕ∞ω) f ((0 : ℝ³) + s • t) := by
    intro s hs
    have h : ((1 : ℕ) + 1 : ℕ∞ω) = 2 := by norm_num
    rw [h]
    exact hf.contDiffAt
  have hida := map_add_eq_sum_add_integral_iteratedFDeriv (f := f) (x := (0 : ℝ³)) (y := t) hseg
  have hsum : (∑ k ∈ Finset.range (1 + 1),
        (((Nat.factorial k : ℕ) : ℝ))⁻¹ • (iteratedFDeriv ℝ k f (0 : ℝ³)) (fun _ => t))
      = f 0 + fderiv ℝ f 0 t := by
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial_zero, Nat.factorial_one,
      Nat.cast_one, inv_one, one_smul, zero_add]
    rw [iteratedFDeriv_zero_apply, iteratedFDeriv_one_apply]
  have hrem : f t - f 0 - fderiv ℝ f 0 t
      = ∫ s in (0 : ℝ)..1, (1 - s) • (iteratedFDeriv ℝ 2 f (s • t)) (fun _ => t) := by
    have h := hida
    rw [hsum] at h
    simp only [Nat.factorial_one, Nat.cast_one, inv_one, one_smul, pow_one, zero_add,
      Nat.reduceAdd] at h
    linarith [h]
  rw [hrem]
  refine (intervalIntegral.norm_integral_le_of_norm_le_const (C := B * ‖t‖ ^ 2) ?_).trans ?_
  · intro s hs
    have hs' : (0 : ℝ) < s ∧ s ≤ 1 := by
      simpa [Set.uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using hs
    obtain ⟨hs0, hs1⟩ := hs'
    have hst : ‖s • t‖ ≤ 1 := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos hs0]
      calc s * ‖t‖ ≤ 1 * 1 := mul_le_mul hs1 ht (norm_nonneg _) (by norm_num)
        _ = 1 := by norm_num
    have hD : ‖iteratedFDeriv ℝ 2 f (s • t)‖ ≤ B := hbd (s • t) hst
    have happ : ‖(iteratedFDeriv ℝ 2 f (s • t)) (fun _ => t)‖ ≤ B * ‖t‖ ^ 2 := by
      have h1 := ContinuousMultilinearMap.le_opNorm (iteratedFDeriv ℝ 2 f (s • t))
        (fun _ : Fin 2 => t)
      have hprod : (∏ _i : Fin 2, ‖t‖) = ‖t‖ ^ 2 := by simp [Finset.prod_const]
      rw [hprod] at h1
      exact le_trans h1 (mul_le_mul_of_nonneg_right hD (by positivity))
    calc ‖(1 - s) • (iteratedFDeriv ℝ 2 f (s • t)) (fun _ => t)‖
        = ‖1 - s‖ * ‖(iteratedFDeriv ℝ 2 f (s • t)) (fun _ => t)‖ := norm_smul _ _
      _ = (1 - s) * ‖(iteratedFDeriv ℝ 2 f (s • t)) (fun _ => t)‖ := by
            rw [Real.norm_eq_abs, abs_of_nonneg (by linarith)]
      _ ≤ 1 * (B * ‖t‖ ^ 2) :=
            mul_le_mul (by linarith) happ (norm_nonneg _) (by norm_num)
      _ = B * ‖t‖ ^ 2 := by ring
  · simp

/-- **the local quadratic deviation of `conv3Small M` at `0`** (`3 ≤ M`):
there is `C ≥ 0` with `|conv3Small M t − 1| ≤ C·‖t‖²` for `‖t‖ ≤ 1`.
`C` is taken from the second iterated derivative bounded on the unit ball
(`IsCompact.exists_bound_of_continuousOn` + `ContDiff.continuous_iteratedFDeriv'`);
the second-order Taylor bound is applied at `±t` and averaged, killing the
linear term by evenness (`conv3Small_symm`) — `conv3Small M 0 = 1`
(`conv3Small_zero`). -/
lemma conv3Small_quadratic_dev_local {M : ℕ} (hM : 3 ≤ M) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ³, ‖t‖ ≤ 1 → |conv3Small M t - 1| ≤ C * ‖t‖ ^ 2 := by
  have hC : ContDiff ℝ 2 (fun x : ℝ³ => conv3Small M x) := conv3Small_contDiff_two hM
  obtain ⟨B, hB⟩ := (isCompact_closedBall (0 : ℝ³) (1 : ℝ)).exists_bound_of_continuousOn
    (ContDiff.continuous_iteratedFDeriv' (m := 2) hC).continuousOn
  have hB0 : 0 ≤ B := le_trans (norm_nonneg _)
    (hB 0 (by simp [Metric.mem_closedBall]))
  refine ⟨B, hB0, ?_⟩
  intro t ht
  have hbd : ∀ z : ℝ³, ‖z‖ ≤ 1 → ‖iteratedFDeriv ℝ 2 (fun x : ℝ³ => conv3Small M x) z‖ ≤ B :=
    fun z hz => hB z (by simpa [Metric.mem_closedBall, dist_eq_norm] using hz)
  have hrt := taylor_second_order_remainder_le hB0 hC hbd ht
  have hrn := taylor_second_order_remainder_le (t := -t) hB0 hC hbd (by simpa using ht)
  have hF0 : conv3Small M 0 = 1 := conv3Small_zero (by omega : 1 ≤ M)
  have heven : conv3Small M (-t) = conv3Small M t := conv3Small_symm (by omega : 1 ≤ M) t
  have hlin : fderiv ℝ (fun x : ℝ³ => conv3Small M x) 0 (-t)
      = -fderiv ℝ (fun x : ℝ³ => conv3Small M x) 0 t := by
    exact map_neg (fderiv ℝ (fun x : ℝ³ => conv3Small M x) 0) t
  have hkey : conv3Small M t - conv3Small M 0
      = (1 / 2 : ℝ) * ((conv3Small M t - conv3Small M 0 - fderiv ℝ (fun x : ℝ³ => conv3Small M x) 0 t)
          + (conv3Small M (-t) - conv3Small M 0
              - fderiv ℝ (fun x : ℝ³ => conv3Small M x) 0 (-t))) := by
    rw [heven, hlin]
    ring
  rw [show |conv3Small M t - 1| = ‖conv3Small M t - conv3Small M 0‖ by
    rw [hF0, Real.norm_eq_abs]]
  calc ‖conv3Small M t - conv3Small M 0‖
      = ‖(1 / 2 : ℝ) * ((conv3Small M t - conv3Small M 0
            - fderiv ℝ (fun x : ℝ³ => conv3Small M x) 0 t)
          + (conv3Small M (-t) - conv3Small M 0
              - fderiv ℝ (fun x : ℝ³ => conv3Small M x) 0 (-t)))‖ := by
          conv_lhs => rw [hkey]
    _ = (1 / 2 : ℝ) * ‖(conv3Small M t - conv3Small M 0
            - fderiv ℝ (fun x : ℝ³ => conv3Small M x) 0 t)
          + (conv3Small M (-t) - conv3Small M 0
              - fderiv ℝ (fun x : ℝ³ => conv3Small M x) 0 (-t))‖ := by
          rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2),
            Real.norm_eq_abs]
    _ ≤ (1 / 2 : ℝ) * (‖conv3Small M t - conv3Small M 0
            - fderiv ℝ (fun x : ℝ³ => conv3Small M x) 0 t‖
          + ‖conv3Small M (-t) - conv3Small M 0
              - fderiv ℝ (fun x : ℝ³ => conv3Small M x) 0 (-t)‖) := by
          refine mul_le_mul_of_nonneg_left (norm_add_le _ _) (by norm_num)
    _ ≤ (1 / 2 : ℝ) * (B * ‖t‖ ^ 2 + B * ‖(-t)‖ ^ 2) := by
          refine mul_le_mul_of_nonneg_left (add_le_add hrt hrn) (by norm_num)
    _ = B * ‖t‖ ^ 2 := by
          rw [norm_neg]
          ring



end BoseGases
end Submission
