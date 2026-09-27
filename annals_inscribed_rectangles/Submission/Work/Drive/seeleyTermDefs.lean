import Mathlib
import Submission.Work.Drive.seeleyDefs

/-!
# Summands of the Seeley series

The Seeley series `seeleySum a b R` is the pointwise sum `∑' j, seeleyTerm a b R j`, where
`seeleyTerm a b R j p = a j • (ρ (b j * p.2) • R (p.1, -(b j * p.2)))`.  This file isolates
that summand, the weight used to dominate it, and the linear map `(x, s) ↦ (x, -b s)`.
-/

set_option linter.unusedSectionVars false

namespace Work.Drive

open scoped ContDiff Topology
open Filter

variable {X E : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The `j`-th summand of the Seeley series: `p ↦ a j • (ρ (b j p.2) • R (p.1, -(b j p.2)))`. -/
noncomputable def seeleyTerm (a b : ℕ → ℝ) (R : X × ℝ → E) (j : ℕ) : X × ℝ → E :=
  fun p => a j • (seeleyRho (b j * p.2) • R (p.1, -(b j * p.2)))

/-- The weight `|a j| * (1 + b j) ^ (2N+1)` dominating the `j`-th Seeley summand; it is summable
against the moment hypothesis. -/
noncomputable def seeleyWeight (a b : ℕ → ℝ) (N : ℕ) (j : ℕ) : ℝ :=
  |a j| * (1 + b j) ^ (2 * N + 1)

lemma seeleySum_eq_tsum (a b : ℕ → ℝ) (R : X × ℝ → E) :
    seeleySum a b R = fun p => ∑' j, seeleyTerm a b R j p := rfl

lemma seeleyTerm_apply (a b : ℕ → ℝ) (R : X × ℝ → E) (j : ℕ) (p : X × ℝ) :
    seeleyTerm a b R j p = a j • (seeleyRho (b j * p.2) • R (p.1, -(b j * p.2))) := rfl

/-- The linear map `(x, s) ↦ (x, -b * s)` used to write `seeleyTerm` as a composition. -/
noncomputable def seeleyL (b : ℝ) : (X × ℝ) →L[ℝ] (X × ℝ) :=
  (ContinuousLinearMap.fst ℝ X ℝ).prod ((-b) • ContinuousLinearMap.snd ℝ X ℝ)

lemma seeleyL_apply (b : ℝ) (p : X × ℝ) : seeleyL (X := X) b p = (p.1, -b * p.2) := by
  simp [seeleyL]

lemma seeleyL_snd (b : ℝ) (p : X × ℝ) : (seeleyL (X := X) b p).2 = -b * p.2 := by
  simp [seeleyL]

lemma norm_seeleyL_le (b : ℝ) (hb : 0 < b) : ‖seeleyL (X := X) b‖ ≤ 1 + b := by
  refine ContinuousLinearMap.opNorm_le_bound _ (by linarith) (fun x => ?_)
  have h1 : ‖x.1‖ ≤ (1 + b) * ‖x‖ := by
    have h := norm_fst_le x; have hx := norm_nonneg x; nlinarith
  have h2 : ‖(-b * x.2 : ℝ)‖ ≤ (1 + b) * ‖x‖ := by
    rw [Real.norm_eq_abs, abs_mul, abs_neg, abs_of_pos hb]
    have h := norm_snd_le x
    rw [Real.norm_eq_abs] at h
    have hx := norm_nonneg x
    nlinarith
  have hkey : ‖seeleyL (X := X) b x‖ = max ‖x.1‖ ‖(-b * x.2 : ℝ)‖ := by
    rw [seeleyL_apply, Prod.norm_def]
  rw [hkey]
  exact max_le h1 h2

end Work.Drive
