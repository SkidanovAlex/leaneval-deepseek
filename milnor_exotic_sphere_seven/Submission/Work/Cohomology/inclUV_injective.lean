import Mathlib
import Submission.Work.Cohomology.SmallSES

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

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
`n`-simplex of `X` is a continuous map `Δⁿ ⟶ X` (`TopCat.toSSetObjEquiv`); pushing it forward
along `f : X ⟶ Y` is postcomposition with `f`, so injectivity of `f` gives injectivity of the
induced map on `n`-simplices. -/
theorem toSSet_map_app_injective {X Y : TopCat} (f : X ⟶ Y) (hf : Function.Injective f)
    (n : SimplexCategoryᵒᵖ) : Function.Injective ((TopCat.toSSet.map f).app n) := by
  intro x y hxy
  have h : TopCat.toSSetObjEquiv X n x = TopCat.toSSetObjEquiv X n y := by
    ext z
    have h1 := congrArg (fun t => TopCat.toSSetObjEquiv Y n t z) hxy
    rw [toSSetObjEquiv_map_apply, toSSetObjEquiv_map_apply] at h1
    exact hf h1
  exact (TopCat.toSSetObjEquiv X n).injective h

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
