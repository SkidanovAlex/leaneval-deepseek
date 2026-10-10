import Submission.Work.K3.BaseChangeBirational

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.K3.pointBaseChange` — the points of a base change along a field extension

The descent step of `thm:K3` (`NOTES.md` §6(c), step 1) needs, for every point `x` of the `ℚ`-model
of the link, the corresponding point of its base change to `𝕜`: the exceptional divisors
`x_𝕜`, `y_𝕜` and the base point `z₀,𝕜`.

For `f : T ⟶ S` and `X` an `S`-scheme, Mathlib (`AlgebraicGeometry.Scheme.Pullback.carrierEquiv`)
identifies the points of `X ×_S T` with pairs `(x, ℘)` where `x : X` and `℘` is a prime of the
residue-field tensor product `κ(x) ⊗_{κ(s)} κ(y)`; in our situation (`T = Spec 𝕜`, `S = Spec ℚ`)
this is a prime of `κ(x) ⊗_ℚ 𝕜`.  This file produces the point over a given `x : X` (using
`Triplet.exists_preimage`, which needs only that the tensor product is nontrivial), and identifies
its projection.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

namespace Work.K3

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme Order

section Points

variable {K L : Type} [Field K] [Field L] [Algebra K L]

/-- The unique point of `Spec K` for a field `K`. -/
noncomputable def specPoint (K : Type) [Field K] : Spec (.of K) := default

/-- **Every point of an `S`-scheme has a point of its base change above it**: for `f = specMap K L`
(a field extension) and `x : X` (with `X` over `Spec K`) there is `p : X ×_{Spec K} Spec L` whose
projection to `X` is `x`.  This is step 1 of the descent (`NOTES.md` §6(c)): the point exists
because the residue-field tensor product `κ(x) ⊗_K L` is nontrivial. -/
theorem exists_point_baseChangeAlong (X : Scheme.{0}) [X.Over (Spec (.of K))] (x : X) :
    ∃ p : Work.K3.baseChangeAlong (Work.K3.specMap K L) X,
      Work.K3.baseChangeAlongProj (Work.K3.specMap K L) X p = x := by
  have h : Work.K3.specMap K L (specPoint L) = (X ↘ Spec (.of K)) x :=
    Subsingleton.elim _ _
  obtain ⟨p, -, hp⟩ :=
    Scheme.Pullback.Triplet.exists_preimage
      (Scheme.Pullback.Triplet.mk' (f := Work.K3.specMap K L) (g := X ↘ Spec (.of K))
        (specPoint L) x h)
  exact ⟨p, hp⟩

end Points

end Work.K3
