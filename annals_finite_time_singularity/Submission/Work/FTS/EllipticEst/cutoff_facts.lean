import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Tactic.Have
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.Stability.Cutoff

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst

open scoped ContDiff Topology
open Set Filter

/-! ## Elementary facts about the delivered cut-off `Work.Stability.chi = smoothTransition (2 - ‖·‖)`

The three helpers below are the local ingredients of `cutoff_facts`:

* `deriv_chi_eq_zero_of_abs_le_one` / `deriv_chi_eq_zero_of_two_le_abs` — the derivative of the
  cut-off vanishes on `[-1,1]` (where the bump is locally constant `≡ 1`, Fermat at `±1`) and off
  `(-2,2)` (where the bump is locally constant `≡ 0`, Fermat at `±2`);
* `chi_deriv_bounds` — a universal constant bounding `|χ'|` and `|χ''|` on all of `ℝ`.  Since `χ` is
  `C^∞` and supported in the *compact* set `[-2,2]`, both `χ'` and `χ''` are continuous and vanish
  outside `[-2,2]`, so both are bounded there by compactness;
* `deriv_comp_div` — the chain rule for the rescaling `z ↦ f (z/R)` (no hypothesis on `R`, which is
  irrelevant thanks to the totalised convention `x/0 = 0`).
-/

/-- **`χ' = 0` on `[-1,1]`.**  For `|t| < 1` the cut-off equals `1` on a whole neighbourhood of `t`;
at `t = ±1` it is a global maximum (`χ ≤ 1 = χ t`), so Fermat's rule applies. -/
private theorem deriv_chi_eq_zero_of_abs_le_one {t : ℝ} (ht : |t| ≤ 1) :
    deriv Work.Stability.chi t = 0 := by
  rcases lt_or_eq_of_le ht with h | h
  · have h1 : Work.Stability.chi =ᶠ[𝓝 t] (fun _ : ℝ => (1 : ℝ)) := by
      rw [abs_lt] at h
      filter_upwards [Ioo_mem_nhds h.1 h.2] with y hy
      exact Work.Stability.chi_eq_one (abs_le.mpr ⟨le_of_lt hy.1, le_of_lt hy.2⟩)
    rw [h1.deriv_eq, deriv_const]
  · have hct : Work.Stability.chi t = 1 := Work.Stability.chi_eq_one (le_of_eq h)
    exact IsLocalMax.deriv_eq_zero (Filter.Eventually.of_forall (fun y => by
      rw [hct]; exact Work.Stability.chi_le_one y))

/-- **`χ' = 0` off `(-2,2)`.**  For `|t| > 2` the cut-off vanishes on a whole neighbourhood of `t`;
at `t = ±2` it is a global minimum (`χ ≥ 0 = χ t`), so Fermat's rule applies. -/
private theorem deriv_chi_eq_zero_of_two_le_abs {t : ℝ} (ht : 2 ≤ |t|) :
    deriv Work.Stability.chi t = 0 := by
  rcases lt_or_eq_of_le ht with h | h
  · have h1 : Work.Stability.chi =ᶠ[𝓝 t] (fun _ : ℝ => (0 : ℝ)) := by
      rw [lt_abs] at h
      rcases h with h | h
      · filter_upwards [Ioi_mem_nhds h] with y hy
        have hy' : 2 < y := hy
        exact Work.Stability.chi_eq_zero (by rw [abs_of_pos (by linarith : 0 < y)]; linarith)
      · have ht2 : t < -2 := by linarith
        filter_upwards [Iio_mem_nhds ht2] with y hy
        have hy' : y < -2 := hy
        exact Work.Stability.chi_eq_zero (by rw [abs_of_neg (by linarith : y < 0)]; linarith)
    rw [h1.deriv_eq, deriv_const]
  · have hct : Work.Stability.chi t = 0 := Work.Stability.chi_eq_zero (le_of_eq h)
    exact IsLocalMin.deriv_eq_zero (Filter.Eventually.of_forall (fun y => by
      rw [hct]; exact Work.Stability.chi_nonneg y))

/-- **The cut-off has bounded first and second derivatives.**  `χ` is `C^∞` and supported in the
compact interval `[-2,2]`, so `χ'` and `χ''` are continuous (as derivatives of `C^∞` functions) and
supported in `[-2,2]` (by the two vanishing lemmas above); a continuous function on a compact set is
bounded. -/
private theorem chi_deriv_bounds :
    ∃ C : ℝ, 0 < C ∧
      (∀ t : ℝ, |deriv Work.Stability.chi t| ≤ C) ∧
      (∀ t : ℝ, |deriv (deriv Work.Stability.chi) t| ≤ C) := by
  have hcd : ContDiff ℝ ∞ Work.Stability.chi := Work.Stability.chi_contDiff
  have hd1 : ContDiff ℝ ∞ (deriv Work.Stability.chi) := contDiff_infty_iff_deriv.mp hcd |>.2
  have hd2 : ContDiff ℝ ∞ (deriv (deriv Work.Stability.chi)) :=
    contDiff_infty_iff_deriv.mp hd1 |>.2
  have hc1 : Continuous (deriv Work.Stability.chi) := hd1.continuous
  have hc2 : Continuous (deriv (deriv Work.Stability.chi)) := hd2.continuous
  -- points outside `[-2,2]` have `|t| > 2`
  have hout : ∀ t : ℝ, t ∉ Set.Icc (-2) 2 → 2 < |t| := by
    intro t ht
    rw [Set.mem_Icc, not_and_or, not_le, not_le] at ht
    rcases ht with h | h
    · rw [abs_of_neg (by linarith)]; linarith
    · rw [abs_of_pos (by linarith)]; linarith
  have hz1 : ∀ t : ℝ, t ∉ Set.Icc (-2) 2 → deriv Work.Stability.chi t = 0 :=
    fun t ht => deriv_chi_eq_zero_of_two_le_abs (hout t ht).le
  have hz2 : ∀ t : ℝ, t ∉ Set.Icc (-2) 2 → deriv (deriv Work.Stability.chi) t = 0 := by
    intro t ht
    have h2 : 2 < |t| := hout t ht
    have hev : deriv Work.Stability.chi =ᶠ[𝓝 t] (fun _ : ℝ => (0 : ℝ)) := by
      rw [lt_abs] at h2
      rcases h2 with h | h
      · filter_upwards [Ioi_mem_nhds h] with y hy
        have hy' : 2 < y := hy
        exact deriv_chi_eq_zero_of_two_le_abs
          (by rw [abs_of_pos (by linarith : 0 < y)]; linarith)
      · have ht2 : t < -2 := by linarith
        filter_upwards [Iio_mem_nhds ht2] with y hy
        have hy' : y < -2 := hy
        exact deriv_chi_eq_zero_of_two_le_abs
          (by rw [abs_of_neg (by linarith : y < 0)]; linarith)
    rw [hev.deriv_eq, deriv_const]
  obtain ⟨M1, hM1⟩ := isCompact_Icc.exists_bound_of_continuousOn hc1.continuousOn
  obtain ⟨M2, hM2⟩ := isCompact_Icc.exists_bound_of_continuousOn hc2.continuousOn
  refine ⟨max M1 (max M2 1), ?_, ?_, ?_⟩
  · exact lt_of_lt_of_le zero_lt_one (le_trans (le_max_right M2 1) (le_max_right M1 _))
  · intro t
    by_cases ht : t ∈ Set.Icc (-2:ℝ) 2
    · have h := hM1 t ht
      rw [Real.norm_eq_abs] at h
      exact le_trans h (le_max_left _ _)
    · rw [hz1 t ht, abs_zero]
      exact le_trans zero_le_one (le_trans (le_max_right M2 1) (le_max_right M1 _))
  · intro t
    by_cases ht : t ∈ Set.Icc (-2:ℝ) 2
    · have h := hM2 t ht
      rw [Real.norm_eq_abs] at h
      exact le_trans h (le_trans (le_max_left M2 1) (le_max_right M1 _))
    · rw [hz2 t ht, abs_zero]
      exact le_trans zero_le_one (le_trans (le_max_right M2 1) (le_max_right M1 _))

/-- **The chain rule for the rescaling `z ↦ z/R`**: `(f (·/R))' z = f'(z/R)/R`.  No hypothesis on
`R` (for `R = 0` both sides vanish by the totalised convention). -/
private theorem deriv_comp_div (f : ℝ → ℝ) (R z : ℝ)
    (hf : DifferentiableAt ℝ f (z / R)) :
    deriv (fun w : ℝ => f (w / R)) z = deriv f (z / R) / R := by
  have hg : HasDerivAt (fun w : ℝ => w / R) (1 / R) z := (hasDerivAt_id z).div_const R
  have h := hf.hasDerivAt.comp z hg
  have h' : deriv (fun w : ℝ => f (w / R)) z = deriv f (z / R) * (1 / R) := h.deriv
  rw [h', div_eq_mul_inv]
  ring

/-- **The rescaled cut-off `z ↦ chi (z/R)` of `Submission.Work.Stability`.**  With `chi = Work.Stability.chi` (smooth, `0 ≤ chi ≤ 1`, `chi = 1` on `[-1,1]`, `chi = 0` off `(-2,2)`), for every `R ≥ 1` the rescaled function `chi (·/R)` equals `1` on `[0,R]`, vanishes on `[2R,∞)`, takes values in `[0,1]`, and its first two derivatives are the rescaled derivatives of `chi` and are bounded by `C/R` and `C/R²` with a universal constant `C` (which also bounds `|chi'|` and `|chi''|` on `ℝ`).  Also `chi' = 0` on `[-1,1]` and off `(-2,2)`, so the truncated terms below are supported in `[R,2R]`. -/
theorem cutoff_facts :
    ∃ C : ℝ, 0 < C ∧
      (∀ t : ℝ, |deriv Work.Stability.chi t| ≤ C) ∧
      (∀ t : ℝ, |deriv (deriv Work.Stability.chi) t| ≤ C) ∧
      (∀ t : ℝ, |t| ≤ 1 → deriv Work.Stability.chi t = 0) ∧
      (∀ t : ℝ, 2 ≤ |t| → deriv Work.Stability.chi t = 0) ∧
      (∀ R : ℝ, 1 ≤ R → ∀ z : ℝ, 0 ≤ z → z ≤ R → Work.Stability.chi (z / R) = 1) ∧
      (∀ R : ℝ, 1 ≤ R → ∀ z : ℝ, 2 * R ≤ z → Work.Stability.chi (z / R) = 0) ∧
      (∀ R : ℝ, 1 ≤ R → ∀ z : ℝ, Work.Stability.chi (z / R) ∈ Set.Icc (0 : ℝ) 1) ∧
      (∀ R : ℝ, 1 ≤ R → ∀ z : ℝ,
        deriv (fun z : ℝ => Work.Stability.chi (z / R)) z
          = deriv Work.Stability.chi (z / R) / R) ∧
      (∀ R : ℝ, 1 ≤ R → ∀ z : ℝ,
        deriv (deriv (fun z : ℝ => Work.Stability.chi (z / R))) z
          = deriv (deriv Work.Stability.chi) (z / R) / R ^ 2) ∧
      (∀ R : ℝ, 1 ≤ R → ∀ z : ℝ,
        |deriv (fun z : ℝ => Work.Stability.chi (z / R)) z| ≤ C / R) ∧
      (∀ R : ℝ, 1 ≤ R → ∀ z : ℝ,
        |deriv (deriv (fun z : ℝ => Work.Stability.chi (z / R))) z| ≤ C / R ^ 2) := by
  obtain ⟨C, hCpos, hC1, hC2⟩ := chi_deriv_bounds
  have hdiff : Differentiable ℝ Work.Stability.chi :=
    contDiff_infty_iff_deriv.mp (Work.Stability.chi_contDiff : ContDiff ℝ ∞ Work.Stability.chi) |>.1
  have hdiff1 : Differentiable ℝ (deriv Work.Stability.chi) :=
    contDiff_infty_iff_deriv.mp
      ((contDiff_infty_iff_deriv.mp
        (Work.Stability.chi_contDiff : ContDiff ℝ ∞ Work.Stability.chi)).2) |>.1
  -- the two rescaling identities, kept as hypotheses for the two bound clauses
  have hderiv : ∀ R : ℝ, 1 ≤ R → ∀ z : ℝ,
      deriv (fun z : ℝ => Work.Stability.chi (z / R)) z
        = deriv Work.Stability.chi (z / R) / R :=
    fun R _ z => deriv_comp_div _ R z hdiff.differentiableAt
  have hderiv2 : ∀ R : ℝ, 1 ≤ R → ∀ z : ℝ,
      deriv (deriv (fun z : ℝ => Work.Stability.chi (z / R))) z
        = deriv (deriv Work.Stability.chi) (z / R) / R ^ 2 := by
    intro R hR z
    have hfun : deriv (fun w : ℝ => Work.Stability.chi (w / R))
        = fun w => deriv Work.Stability.chi (w / R) / R :=
      funext (fun w => deriv_comp_div _ R w hdiff.differentiableAt)
    rw [hfun, deriv_div_const R, deriv_comp_div _ R z hdiff1.differentiableAt]
    ring
  refine ⟨C, hCpos, hC1, hC2, ?_, ?_, ?_, ?_, ?_, hderiv, hderiv2, ?_, ?_⟩
  · intro t ht
    exact deriv_chi_eq_zero_of_abs_le_one ht
  · intro t ht
    exact deriv_chi_eq_zero_of_two_le_abs ht
  · -- `chi (z/R) = 1` for `0 ≤ z ≤ R`
    intro R hR z hz0 hz
    have hR0 : 0 < R := by linarith
    refine Work.Stability.chi_eq_one ?_
    rw [abs_of_nonneg (div_nonneg hz0 hR0.le), div_le_one hR0]
    exact hz
  · -- `chi (z/R) = 0` for `z ≥ 2R`
    intro R hR z hz
    have hR0 : 0 < R := by linarith
    have hz0 : 0 ≤ z := by linarith
    refine Work.Stability.chi_eq_zero ?_
    rw [abs_of_nonneg (div_nonneg hz0 hR0.le), le_div_iff₀ hR0]
    linarith
  · -- `0 ≤ chi (z/R) ≤ 1`
    intro R hR z
    exact ⟨Work.Stability.chi_nonneg _, Work.Stability.chi_le_one _⟩
  · -- `|(chi (·/R))'| ≤ C/R`
    intro R hR z
    have hR0 : 0 < R := by linarith
    rw [hderiv R hR z, abs_div, abs_of_pos hR0]
    exact div_le_div_of_nonneg_right (hC1 (z / R)) hR0.le
  · -- `|(chi (·/R))''| ≤ C/R²`
    intro R hR z
    have hR0 : 0 < R := by linarith
    rw [hderiv2 R hR z, abs_div, abs_of_pos (by positivity : (0:ℝ) < R ^ 2)]
    exact div_le_div_of_nonneg_right (hC2 (z / R)) (by positivity)

end Work.FTS.EllipticEst
