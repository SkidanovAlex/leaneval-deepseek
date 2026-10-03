import Mathlib
import Submission.Work.FIArea4.logSine_defs

namespace Work.FIArea4

set_option linter.unusedVariables false

open scoped ContDiff
open MeasureTheory intervalIntegral

noncomputable section

/-! ### The first two derivatives of `ufun` -/

lemma Psi_diff (N : ℕ) (hN : 1 ≤ N) (y : ℝ) : HasDerivAt (Psi N) (deriv (Psi N) y) y :=
  ((contDiff_Psi N hN).differentiable (by simp)).differentiableAt.hasDerivAt

lemma dPsi_diff (N : ℕ) (hN : 1 ≤ N) (y : ℝ) :
    HasDerivAt (deriv (Psi N)) (deriv (deriv (Psi N)) y) y := by
  have h : ContDiff ℝ ∞ (deriv (Psi N)) := by
    have h := (contDiff_Psi N hN).iterate_deriv 1
    simpa using h
  exact ((h.differentiable (by simp)).differentiableAt).hasDerivAt

lemma hasDerivAt_ufun (N : ℕ) (hN : 1 ≤ N) (α : ℝ) :
    HasDerivAt (ufun N) (Real.sin α * (deriv (Psi N) (1 + Real.cos α)
      - deriv (Psi N) (1 - Real.cos α))) α := by
  have hg : HasDerivAt (fun x : ℝ => 1 - Real.cos x) (Real.sin α) α := by
    simpa only [neg_neg] using (Real.hasDerivAt_cos α).const_sub (1:ℝ)
  have hh : HasDerivAt (fun x : ℝ => 1 + Real.cos x) (-Real.sin α) α :=
    (Real.hasDerivAt_cos α).const_add 1
  have hA : HasDerivAt (fun x : ℝ => Psi N (1 - Real.cos x))
      (deriv (Psi N) (1 - Real.cos α) * Real.sin α) α := by
    have h := (Psi_diff N hN (1 - Real.cos α)).comp α hg
    simpa [Function.comp_def] using h
  have hB : HasDerivAt (fun x : ℝ => Psi N (1 + Real.cos x))
      (deriv (Psi N) (1 + Real.cos α) * (-Real.sin α)) α := by
    have h := (Psi_diff N hN (1 + Real.cos α)).comp α hh
    simpa [Function.comp_def] using h
  have hsum := (hA.neg.sub hB).add_const (2 * Real.log 2)
  have hv : -(deriv (Psi N) (1 - Real.cos α) * Real.sin α)
      - deriv (Psi N) (1 + Real.cos α) * (-Real.sin α)
      = Real.sin α * (deriv (Psi N) (1 + Real.cos α) - deriv (Psi N) (1 - Real.cos α)) := by ring
  rw [hv] at hsum
  change HasDerivAt (ufun N) _ α
  exact hsum

lemma deriv_ufun_eq (N : ℕ) (hN : 1 ≤ N) :
    deriv (ufun N) = fun α => Real.sin α * (deriv (Psi N) (1 + Real.cos α)
      - deriv (Psi N) (1 - Real.cos α)) :=
  funext fun α => (hasDerivAt_ufun N hN α).deriv

lemma hasDerivAt_deriv_ufun (N : ℕ) (hN : 1 ≤ N) (α : ℝ) :
    HasDerivAt (deriv (ufun N))
      (Real.cos α * (deriv (Psi N) (1 + Real.cos α) - deriv (Psi N) (1 - Real.cos α))
        - Real.sin α ^ 2 * (deriv (deriv (Psi N)) (1 - Real.cos α)
            + deriv (deriv (Psi N)) (1 + Real.cos α))) α := by
  rw [deriv_ufun_eq N hN]
  have hg : HasDerivAt (fun x : ℝ => 1 - Real.cos x) (Real.sin α) α := by
    simpa only [neg_neg] using (Real.hasDerivAt_cos α).const_sub (1:ℝ)
  have hh : HasDerivAt (fun x : ℝ => 1 + Real.cos x) (-Real.sin α) α :=
    (Real.hasDerivAt_cos α).const_add 1
  have hG1 : HasDerivAt (fun x : ℝ => deriv (Psi N) (1 + Real.cos x))
      (deriv (deriv (Psi N)) (1 + Real.cos α) * (-Real.sin α)) α := by
    have h := (dPsi_diff N hN (1 + Real.cos α)).comp α hh
    simpa [Function.comp_def] using h
  have hG2 : HasDerivAt (fun x : ℝ => deriv (Psi N) (1 - Real.cos x))
      (deriv (deriv (Psi N)) (1 - Real.cos α) * Real.sin α) α := by
    have h := (dPsi_diff N hN (1 - Real.cos α)).comp α hg
    simpa [Function.comp_def] using h
  have hG : HasDerivAt (fun x : ℝ => deriv (Psi N) (1 + Real.cos x) - deriv (Psi N) (1 - Real.cos x))
      (deriv (deriv (Psi N)) (1 + Real.cos α) * (-Real.sin α)
        - deriv (deriv (Psi N)) (1 - Real.cos α) * Real.sin α) α := hG1.sub hG2
  have hmain := (Real.hasDerivAt_sin α).mul hG
  have hv : Real.cos α * (deriv (Psi N) (1 + Real.cos α) - deriv (Psi N) (1 - Real.cos α))
      + Real.sin α * (deriv (deriv (Psi N)) (1 + Real.cos α) * (-Real.sin α)
        - deriv (deriv (Psi N)) (1 - Real.cos α) * Real.sin α)
      = Real.cos α * (deriv (Psi N) (1 + Real.cos α) - deriv (Psi N) (1 - Real.cos α))
        - Real.sin α ^ 2 * (deriv (deriv (Psi N)) (1 - Real.cos α)
            + deriv (deriv (Psi N)) (1 + Real.cos α)) := by ring
  rw [hv] at hmain
  exact hmain

lemma deriv_deriv_ufun_eq (N : ℕ) (hN : 1 ≤ N) :
    deriv (deriv (ufun N)) = fun α =>
      Real.cos α * (deriv (Psi N) (1 + Real.cos α) - deriv (Psi N) (1 - Real.cos α))
        - Real.sin α ^ 2 * (deriv (deriv (Psi N)) (1 - Real.cos α)
            + deriv (deriv (Psi N)) (1 + Real.cos α)) :=
  funext fun α => (hasDerivAt_deriv_ufun N hN α).deriv

/-! ### Symmetries of `u_N''` -/

/-- `u_N''` is even. -/
lemma deriv_deriv_ufun_neg (N : ℕ) (hN : 1 ≤ N) (α : ℝ) :
    deriv (deriv (ufun N)) (-α) = deriv (deriv (ufun N)) α := by
  rw [deriv_deriv_ufun_eq N hN]
  simp only [Real.cos_neg, Real.sin_neg, neg_sq]

/-- `u_N''(π - α) = u_N''(α)`. -/
lemma deriv_deriv_ufun_pi_sub (N : ℕ) (hN : 1 ≤ N) (α : ℝ) :
    deriv (deriv (ufun N)) (Real.pi - α) = deriv (deriv (ufun N)) α := by
  rw [deriv_deriv_ufun_eq N hN]
  simp only [Real.cos_pi_sub, Real.sin_pi_sub]
  ring_nf

/-- `deriv (deriv (ufun N))` is smooth (hence continuous). -/
lemma contDiff_deriv2_ufun (N : ℕ) (hN : 1 ≤ N) :
    ContDiff ℝ ∞ (deriv (deriv (ufun N))) := by
  have h : ContDiff ℝ ∞ (deriv^[2] (ufun N)) := (contDiff_ufun N hN).iterate_deriv 2
  have h2 : deriv^[2] (ufun N) = deriv (deriv (ufun N)) := by
    simp [Function.iterate_succ]
  rwa [h2] at h

end
