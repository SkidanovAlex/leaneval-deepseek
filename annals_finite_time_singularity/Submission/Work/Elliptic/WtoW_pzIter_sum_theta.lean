/-
Copyright: work module for the Elgindi finite-time singularity project.

# `pzIter` commutes with a `θ`-dependent finite linear combination

`pzIter c` is `c`-fold `∂_z`.  Since the coefficient `φ i θ` does not depend on
`z`, a finite sum `∑ i ∈ s, φ i θ * X i z θ` may be differentiated term by term
inside `pzIter c`.  This is the `z`-directional counterpart of
`Work.Spaces.iteratedDeriv_sum_const_mul`, obtained by rewriting `pzIter` as an
iterated derivative (`Work.Spaces.pzIter_eq_iteratedDeriv`).
-/
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Submission.Work.Spaces.pz_aux

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.Elliptic

theorem WtoW_pzIter_sum_theta {ι : Type*} (s : Finset ι) (φ : ι → ℝ → ℝ)
    (X : ι → ℝ → ℝ → ℝ) (c : ℕ) {z θ : ℝ}
    (h : ∀ i ∈ s, ContDiffAt ℝ (c : ℕ∞) (fun z' => X i z' θ) z) :
    Work.Spaces.pzIter c (fun z θ => ∑ i ∈ s, φ i θ * X i z θ) z θ
      = ∑ i ∈ s, φ i θ * Work.Spaces.pzIter c (X i) z θ := by
  simp only [Work.Spaces.pzIter_eq_iteratedDeriv]
  exact Work.Spaces.iteratedDeriv_sum_const_mul s (fun i => φ i θ)
    (fun i z' => X i z' θ) c z h

end Work.Elliptic
