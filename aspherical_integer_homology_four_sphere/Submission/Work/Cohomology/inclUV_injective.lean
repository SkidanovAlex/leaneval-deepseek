import Mathlib
import Submission.Work.Cohomology.SmallSES
import Submission.Work.Homology.SimplexShim

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# Injectivity of the inclusions `U ∩ V ↪ U`, `U ∩ V ↪ V` on singular simplices

The Mayer–Vietoris short exact sequence (`Submission/Work/Cohomology/SmallSES.lean`) is exact in
the middle because a chain of `X` supported in both `U` and `V` is a chain of `U ∩ V`.  At the
level of singular simplices this rests on the elementary fact proved here: the inclusion
`U ∩ V ↪ U` (resp. `U ∩ V ↪ V`) is injective, and pushing forward a singular simplex along an
injective continuous map is again injective.

## Main results

* `toSSet_map_app_injective` — pushing singular `n`-simplices forward along an injective
  continuous map `f : X ⟶ Y` is injective;
* `inclUV_injective` — the application to the two inclusions `U ∩ V ↪ U` and `U ∩ V ↪ V`.
-/

set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicTopology Simplicial Limits
open scoped Simplicial
open Work.Cohomology

namespace Work.Cohomology

noncomputable section

/-- **Pushing singular simplices forward along an injective map is injective.**  A singular
`n`-simplex of `X` is a continuous map `Δⁿ ⟶ X` (`Work.Homology.toSSetObjEquiv'`); pushing it forward
along `f : X ⟶ Y` is postcomposition with `f`, so injectivity of `f` gives injectivity of the
induced map on `n`-simplices. -/
theorem toSSet_map_app_injective {X Y : TopCat} (f : X ⟶ Y) (hf : Function.Injective f)
    (n : SimplexCategoryᵒᵖ) : Function.Injective ((TopCat.toSSet.map f).app n) := by
  intro x y hxy
  have h : Work.Homology.toSSetObjEquiv' X n x = Work.Homology.toSSetObjEquiv' X n y := by
    ext z
    have h1 := congrArg (fun t => Work.Homology.toSSetObjEquiv' Y n t z) hxy
    rw [toSSetObjEquiv_map_apply, toSSetObjEquiv_map_apply] at h1
    exact hf h1
  exact (Work.Homology.toSSetObjEquiv' X n).injective h

/-- **The inclusions `U ∩ V ↪ U` and `U ∩ V ↪ V` are injective on singular `n`-simplices.** -/
theorem inclUV_injective {X : TopCat} (U V : Set X) (n : SimplexCategoryᵒᵖ) :
    Function.Injective ((TopCat.toSSet.map (inclUVU U V)).app n) ∧
    Function.Injective ((TopCat.toSSet.map (inclUVV U V)).app n) := by
  constructor
  · exact toSSet_map_app_injective (inclUVU U V)
      (fun a b h => Subtype.ext (congrArg (fun x : U => (x : X)) h)) n
  · exact toSSet_map_app_injective (inclUVV U V)
      (fun a b h => Subtype.ext (congrArg (fun x : V => (x : X)) h)) n

end

end Work.Cohomology
