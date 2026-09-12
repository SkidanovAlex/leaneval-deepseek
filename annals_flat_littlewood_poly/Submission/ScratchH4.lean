import Mathlib
import Submission.RS
import Submission.Sec3Defs
import Submission.Sec3H_defs
import Submission.Sec3H_deriv

noncomputable section
open scoped Polynomial BigOperators
open Polynomial Complex

namespace Submission.Sec3H

/-- product eθ·α (first H term) -/
def FA (t : ℕ) : ℝ → ℂ := fun y => Sec3.eθ y * alpha t y
/-- product eθ(2·)·β (second H term) -/
def FB (t : ℕ) : ℝ → ℂ := fun y => Sec3.eθ (2 * y) * beta t y

lemma H_eq_FA_add_FB (t : ℕ) : H t = FA t + FB t := by
  funext x
  rfl

lemma iteratedDeriv_FA_sum (t : ℕ) (k : ℕ) (x : ℝ) :
    iteratedDeriv k (FA t) x =
      ∑ i ∈ Finset.range (k + 1),
        (((k.choose i : ℂ) * (Complex.I ^ i * Sec3.eθ x)) * iteratedDeriv (k - i) (alpha t) x) := by
  have hf : ContDiffAt ℝ k (fun y : ℝ => Sec3.eθ y) x := (contDiff_eθ (n := k)).contDiffAt
  have hg : ContDiffAt ℝ k (alpha t) x := (contDiff_alpha (n := k) t).contDiffAt
  unfold FA
  rw [iteratedDeriv_mul (f := fun y : ℝ => Sec3.eθ y) (g := alpha t) hf hg]
  apply Finset.sum_congr rfl
  intro i hi
  rw [iteratedDeriv_eθ i x]
  ring

lemma iteratedDeriv_FB_sum (t : ℕ) (k : ℕ) (x : ℝ) :
    iteratedDeriv k (FB t) x =
      ∑ i ∈ Finset.range (k + 1),
        (((k.choose i : ℂ) * (((2 : ℂ) * Complex.I) ^ i * Sec3.eθ (2 * x))) * iteratedDeriv (k - i) (beta t) x) := by
  have hf : ContDiffAt ℝ k (fun y : ℝ => Sec3.eθ (2 * y)) x := (contDiff_eθ_mul (n := k) 2).contDiffAt
  have hg : ContDiffAt ℝ k (beta t) x := (contDiff_beta (n := k) t).contDiffAt
  unfold FB
  rw [iteratedDeriv_mul (f := fun y : ℝ => Sec3.eθ (2 * y)) (g := beta t) hf hg]
  apply Finset.sum_congr rfl
  intro i hi
  rw [iteratedDeriv_eθ2 i x]
  ring

end Submission.Sec3H
