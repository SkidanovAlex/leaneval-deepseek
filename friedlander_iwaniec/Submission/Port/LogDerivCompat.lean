import Mathlib.Analysis.Calculus.LogDeriv
import Mathlib.Algebra.BigOperators.Pi

/-!
# Port compatibility: the pre-v4.35 forms of `logDeriv_mul` / `logDeriv_prod`

Mathlib (v4.35 pin) states `logDeriv_mul` for `f * g` and `logDeriv_prod` for `∏ i ∈ s, f i`;
the proofs in this closure were written against the pointwise forms
`fun z => f z * g z` and `fun x => ∏ i ∈ s, f i x`.  These wrappers restate the old forms.
-/

namespace Submission.Port

variable {𝕜 𝕜' : Type*} [NontriviallyNormedField 𝕜] [NontriviallyNormedField 𝕜']
  [NormedAlgebra 𝕜 𝕜']

theorem logDeriv_mul_fun {f g : 𝕜 → 𝕜'} (x : 𝕜) (hf : f x ≠ 0) (hg : g x ≠ 0)
    (hdf : DifferentiableAt 𝕜 f x) (hdg : DifferentiableAt 𝕜 g x) :
    logDeriv (fun z => f z * g z) x = logDeriv f x + logDeriv g x :=
  logDeriv_mul x hf hg hdf hdg

theorem logDeriv_prod_fun {ι : Type*} {s : Finset ι} {f : ι → 𝕜 → 𝕜'} {x : 𝕜}
    (hf : ∀ i ∈ s, f i x ≠ 0) (hd : ∀ i ∈ s, DifferentiableAt 𝕜 (f i) x) :
    logDeriv (∏ i ∈ s, f i ·) x = ∑ i ∈ s, logDeriv (f i) x := by
  have h : (fun y => ∏ i ∈ s, f i y) = ∏ i ∈ s, f i := by
    ext y; simp [Finset.prod_apply]
  rw [h]
  exact logDeriv_prod hf hd

end Submission.Port
