/-
Area AV (abelian-variety toolkit) for the Jacobian challenge: descent of morphisms.
-/
import Submission.Work.AbVar.Basic
import Submission.Work.AbVar.Gen
import Submission.Work.AbVar.Extend.desc_of_flat_surjective_quasiCompact

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# Descent of morphisms along fpqc covers

`Work.AbVar.Extend.desc_of_flat_surjective_quasiCompact` descends a morphism `Φ : W ⟶ A` along
a flat, surjective, quasi-compact `π : W ⟶ J` provided the two composites
`W ×_J W ⇉ W ⟶ A` agree. Here we record the form actually used in practice (the "translation
trick"): it suffices that they agree on a *dense* open of `W ×_J W`, because the locus where two
morphisms into a separated scheme agree is closed (see `Work.AbVar.eq_of_isDominant`).
-/

set_option autoImplicit false

universe u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open scoped MonObj
open AlgebraicGeometry

namespace Work.AbVar

variable {k : Type u} [Field k]
variable {W J A : Sch k}

/-- If `Φ : W ⟶ A` is constant along the fibres of a flat, surjective, quasi-compact
`π : W ⟶ J` *on a dense subobject of the kernel pair of `π`*, then `Φ` descends to `J`.

The intended instantiation is the "translation trick": `V` is an open subscheme of
`W ×_J W` whose image is dense, and `Φ` is shown to be constant along the fibres of `π`
there — the locus where the two composites agree is closed because `A` is separated. -/
theorem desc_of_flat_surjective_quasiCompact_of_dense (π : W ⟶ J) [Flat π.left]
    [Surjective π.left] [QuasiCompact π.left] (Φ : W ⟶ A) [IsSeparated A.hom]
    [IsReduced (pullback π π).left]
    {V : Sch k} (j : V ⟶ pullback π π) [IsDominant j.left]
    (h : j ≫ pullback.fst π π ≫ Φ = j ≫ pullback.snd π π ≫ Φ) :
    ∃! (g : J ⟶ A), π ≫ g = Φ :=
  Work.AbVar.Extend.desc_of_flat_surjective_quasiCompact π Φ (eq_of_isDominant (A := A) j h)

end Work.AbVar
