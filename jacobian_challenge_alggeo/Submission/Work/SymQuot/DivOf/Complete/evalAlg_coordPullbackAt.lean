import Mathlib
import Submission.Work.SymQuot.DivOf.Complete.Setup

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


set_option autoImplicit false
set_option maxHeartbeats 2000000

universe u

namespace Work.SymQuot.DivOf.Complete

open CategoryTheory Limits AlgebraicGeometry in
theorem evalAlg_coordPullbackAt {K : Type u} [Field K] {C : Work.CurveBasics.Curve K} {n : ℕ}
    {V : C.left.Opens} {S : Type u} [CommRing S] [Algebra K S]
    (x : Fin n → Work.SpecLin.RPt C.toOver S)
    (h : ⊤ ≤ (Limits.Pi.lift x : Work.SpecLin.specOf (K := K) S ⟶
      Work.SymQuot.prod C.toOver n).left ⁻¹ᵁ Work.SymQuot.piOpen C.toOver V n)
    (m : Fin n) (hm : ⊤ ≤ (x m).left ⁻¹ᵁ V) (b : Γ(C.left, V)) :
    evalAlg C V n x h (coordPullbackAt C n V m b) = ptVal C V (x m) hm b := by
  -- The `m`-th projection of `Pi.lift x` is `x m`, on the underlying schemes.
  have hcomp : (Limits.Pi.lift x).left ≫ (Work.SymQuot.proj C.toOver n m).left =
      (x m).left :=
    congrArg (fun t : Work.SpecLin.specOf (K := K) S ⟶ C.toOver => t.left)
      (Limits.Pi.lift_comp_π x m)
  -- Hence the two ways of pulling back a section of `V` to `Spec S` agree.
  have key : Scheme.Hom.appLE (Work.SymQuot.proj C.toOver n m).left V
        (Work.SymQuot.piOpen C.toOver V n)
        (Work.SymQuot.DivOf.piOpen_le_preimage_proj C n V m) ≫
      Scheme.Hom.appLE (Limits.Pi.lift x).left (Work.SymQuot.piOpen C.toOver V n) ⊤ h =
      Scheme.Hom.appLE (x m).left V ⊤ hm := by
    rw [Scheme.Hom.appLE_comp_appLE]
    exact Work.SymQuot.appLE_congr_hom hcomp _ _
  have key2 : (Scheme.Hom.appLE (Limits.Pi.lift x).left (Work.SymQuot.piOpen C.toOver V n)
        ⊤ h).hom.comp
      (Scheme.Hom.appLE (Work.SymQuot.proj C.toOver n m).left V
        (Work.SymQuot.piOpen C.toOver V n)
        (Work.SymQuot.DivOf.piOpen_le_preimage_proj C n V m)).hom =
      (Scheme.Hom.appLE (x m).left V ⊤ hm).hom := by
    simpa only [CommRingCat.hom_comp] using congrArg CommRingCat.Hom.hom key
  simp only [evalAlg, ptVal, Work.SymQuot.DivOf.coordPullbackAt_apply, RingHom.comp_apply]
  exact congrArg (fun f => (Scheme.ΓSpecIso (CommRingCat.of S)).hom.hom (f b)) key2

end Work.SymQuot.DivOf.Complete
