import Mathlib
import Submission.Work.Cohomology.AlexanderWhitney
import Submission.Work.Cohomology.linSimplex_boundary
import Submission.Work.Cohomology.CupRing
import Submission.Work.Cohomology.Kronecker

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# A cocycle of odd degree vanishes on constant simplices

This is the ingredient which kills the "junk" faces in the prism (Eilenberg–Zilber shuffle)
computation of the chain-level cup product witness
`Work.Cohomology.Crux33.prodSph33_cup_witness` for `A = S³ × S³ ⊆ S³ × D⁴`: for a singular
`3`-simplex of `S³` which is constant on `∂Δ³` (a collapse of the simplex onto the sphere), every
proper face is a *constant* simplex, and the junk terms of the shuffle sum are constant, hence are
killed by any `3`-cocycle.

## Main results

* `Work.Cohomology.Crux33.genEval_eq_zero_of_faces` — if a `3`-simplex `x` is the common value of
  all five faces of a `4`-simplex `y`, then `ψ x = 0` for every `3`-cocycle `ψ`;
* `Work.Cohomology.Crux33.genEval_const` — the special case of a constant `3`-simplex.

Why the cancellation is not immediate: the constant `4`-simplex has five faces, of which the first
two are both the constant `3`-simplex and cancel (`d₀ s₀ = d₁ s₀ = id`); the alternating sum
`Σ_{j=0}^{4}(-1)^j` is `1`, so `∂y = x` and the cocycle condition `δψ(y) = ψ(∂y) = 0` gives
`ψ x = 0`.  (For a `3`-simplex which is merely degenerate this is false, which is exactly the
"normalization" phenomenon: a cocycle vanishing on *all* degenerate `3`-simplices is the same as a
cocycle of the normalized complex, and is not forced to vanish.)
-/

open CategoryTheory AlgebraicTopology Simplicial Limits
open scoped Simplicial

namespace Work.Cohomology.Crux33

noncomputable section

/-- **A `3`-cocycle vanishes on a `3`-simplex which is the common value of the five faces of a
`4`-simplex.** -/
theorem genEval_eq_zero_of_faces (X : SSet) (α : Cochain ℤ X 3)
    (hα : cochainDiff ℤ X α = 0) (x : X _⦋3⦌) (y : X _⦋4⦌)
    (h : ∀ j : Fin 5, X.δ j y = x) : genEval ℤ X α x = 0 := by
  have hd : ((X.chainComplex (ModuleCat.of ℤ ℤ)).d 4 3)
      ((X.ιChainComplex (R := ModuleCat.of ℤ ℤ) y).hom 1)
      = (X.ιChainComplex (R := ModuleCat.of ℤ ℤ) x).hom 1 := by
    rw [chainComplex_d_ι_apply ℤ (X := X) (n := 3) y, Fin.sum_univ_five]
    rw [h 0, h 1, h 2, h 3, h 4]
    norm_num [zsmul_eq_mul]
  have h2 := cochainDiff_apply ℤ X α y
  rw [hα] at h2
  simp only [LinearMap.zero_apply, genEval, hd] at h2
  exact h2.symm

/-- **A `3`-cocycle vanishes on constant `3`-simplices.**  Here `x` is the constant `3`-simplex
with vertex `v`, obtained by applying a map `⦋3⦌ ⟶ ⦋0⦌` to `v`; the `4`-simplex obtained from `v`
by `⦋4⦌ ⟶ ⦋0⦌` has all five faces equal to `x`. -/
theorem genEval_const (X : SSet) (α : Cochain ℤ X 3) (hα : cochainDiff ℤ X α = 0)
    (v : X _⦋0⦌) (f3 : ⦋3⦌ ⟶ ⦋0⦌) (f4 : ⦋4⦌ ⟶ ⦋0⦌)
    (hface : ∀ j : Fin 5, X.δ j (X.map f4.op v) = X.map f3.op v) :
    genEval ℤ X α (X.map f3.op v) = 0 :=
  genEval_eq_zero_of_faces X α hα _ _ hface

end

end Work.Cohomology.Crux33
