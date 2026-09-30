import Mathlib
import Submission.Work.BMF.parseval.Defs
import Submission.Work.BMF.dirichlet_parseval_shortint
import Submission.Work.BMF.aemeasurable_window_avg
import Submission.Work.BMF.norm_window_avg_le

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Elementary auxiliary estimates for the single-window Parseval bound

Sizes of `dirP` and the basic integral bounds used in the final assembly.
-/

namespace Work.BMF

open scoped BigOperators
open MeasureTheory intervalIntegral

noncomputable section

/-- Continuity of `t ↦ dirP a X t`. -/
theorem continuous_dirP (a : ℕ → ℂ) (X : ℝ) : Continuous (fun t : ℝ => dirP a X t) := by
  unfold dirP
  refine continuous_finsetSum _ (fun n _ => ?_)
  have h1 : Continuous (fun t : ℝ => -(1 + Complex.I*(t:ℂ))) := by continuity
  refine Continuous.mul continuous_const (Continuous.const_cpow h1 ?_)
  right
  intro t ht
  have := congrArg Complex.re ht
  simp at this

/-- Pointwise size of the Dirichlet polynomial. -/
theorem dirP_norm_le_sum (a : ℕ → ℂ) (ha : ∀ n, ‖a n‖ ≤ 1) (X t : ℝ) :
    ‖dirP a X t‖ ≤ ∑ n ∈ natIcc X (3*X), (1:ℝ)/(n:ℝ) := by
  unfold dirP
  refine (norm_sum_le _ _).trans ?_
  refine Finset.sum_le_sum (fun n _ => ?_)
  rcases eq_or_ne n 0 with h | h
  · subst h
    have hz : ((0:ℕ):ℂ) = (0:ℂ) := by norm_num
    rw [hz, norm_mul, Complex.zero_cpow (by
      intro hc
      have := congrArg Complex.re hc
      simp at this), norm_zero, mul_zero]
    simp
  · have hnpos : 0 < n := Nat.pos_of_ne_zero h
    rw [norm_mul, Complex.norm_natCast_cpow_of_pos hnpos]
    have hre : (-(1 + Complex.I*(t:ℂ))).re = -1 := by simp
    rw [hre, Real.rpow_neg_one]
    calc ‖a n‖ * (n:ℝ)⁻¹ ≤ 1 * (n:ℝ)⁻¹ :=
          mul_le_mul_of_nonneg_right (ha n) (by positivity)
      _ = (1:ℝ)/(n:ℝ) := by rw [one_mul, one_div]

/-- Uniform bound `‖dirP a X t‖ ≤ 4` for `X ≥ 1` and `‖a‖ ≤ 1`. -/
theorem dirP_norm_le (a : ℕ → ℂ) (ha : ∀ n, ‖a n‖ ≤ 1) (X t : ℝ) (hX : 1 ≤ X) :
    ‖dirP a X t‖ ≤ 4 :=
  le_trans (dirP_norm_le_sum a ha X t) (shortintDirPoly_inv_sum_le X hX)

/-- Mean-square bound over `[-2T,2T]` for `dirP`. -/
theorem dirP_integral_bound (a : ℕ → ℂ) (ha : ∀ n, ‖a n‖ ≤ 1) (X T : ℝ) (hX : 1 ≤ X)
    (hT : 0 ≤ T) :
    (∫ t in (-(2*T))..(2*T), ‖dirP a X t‖^2) ≤ 64*T := by
  have hab : -(2*T) ≤ 2*T := by linarith
  have hcont : Continuous (fun t : ℝ => ‖dirP a X t‖^2) := (continuous_dirP a X).norm.pow 2
  have hfi : IntervalIntegrable (fun t : ℝ => ‖dirP a X t‖^2) volume (-(2*T)) (2*T) :=
    hcont.intervalIntegrable _ _
  have hgi : IntervalIntegrable (fun _ : ℝ => (16:ℝ)) volume (-(2*T)) (2*T) :=
    intervalIntegrable_const
  have hpt : ∀ x ∈ Set.Icc (-(2*T)) (2*T), ‖dirP a X x‖^2 ≤ (16:ℝ) := by
    intro x _
    have h1 := dirP_norm_le a ha X x hX
    nlinarith [norm_nonneg (dirP a X x), h1]
  have hint := intervalIntegral.integral_mono_on hab hfi hgi hpt
  have hconst : (∫ _ in (-(2*T))..(2*T), (16:ℝ)) = 16*|2*T - (-(2*T))| := by
    rw [intervalIntegral.integral_const]
    simp only [smul_eq_mul]
    rw [abs_of_nonneg (by linarith : (0:ℝ) ≤ 2*T - (-(2*T)))]
    ring
  rw [hconst] at hint
  have h4 : 2*T - (-(2*T)) = 4*T := by ring
  rw [h4, abs_of_nonneg (by linarith : (0:ℝ) ≤ 4*T)] at hint
  linarith

/-- The `⨆`-term is bounded above whenever `T ↦ (R/T)∫_{-2T}^{2T}` is considered over `T ≥ R`. -/
theorem bddAbove_dirP_sup (a : ℕ → ℂ) (ha : ∀ n, ‖a n‖ ≤ 1) (X R : ℝ) (hX : 1 ≤ X) (hR : 0 < R) :
    BddAbove (Set.range (fun T : {T : ℝ // R ≤ T} =>
      R/T * (∫ t in (-(2*T.1))..(2*T.1), ‖dirP a X t‖^2))) := by
  refine ⟨64*R, ?_⟩
  rintro y ⟨T, rfl⟩
  have hT0 : 0 < T.1 := lt_of_lt_of_le hR T.2
  have hb := dirP_integral_bound a ha X T.1 hX hT0.le
  have hpos : 0 ≤ R/T.1 := by positivity
  have h2 : R/T.1 * (64*T.1) = 64*R := by field_simp
  calc R/T.1 * (∫ t in (-(2*T.1))..(2*T.1), ‖dirP a X t‖^2)
      ≤ R/T.1 * (64*T.1) := mul_le_mul_of_nonneg_left hb hpos
    _ = 64*R := h2

/-- The `⨆`-term is nonnegative. -/
theorem dirP_sup_nonneg (a : ℕ → ℂ) (ha : ∀ n, ‖a n‖ ≤ 1) (X R : ℝ) (hX : 1 ≤ X) (hR : 0 < R) :
    0 ≤ ⨆ (T : {T : ℝ // R ≤ T}), R/T * (∫ t in (-(2*T.1))..(2*T.1), ‖dirP a X t‖^2) := by
  have h0 : 0 ≤ R/R * (∫ t in (-(2*R))..(2*R), ‖dirP a X t‖^2) := by
    have h1 : 0 ≤ ∫ t in (-(2*R))..(2*R), ‖dirP a X t‖^2 :=
      intervalIntegral.integral_nonneg_of_forall (by linarith) (fun t => by positivity)
    positivity
  exact le_trans h0 (le_ciSup (bddAbove_dirP_sup a ha X R hX hR) ⟨R, le_refl R⟩)

end

end Work.BMF
