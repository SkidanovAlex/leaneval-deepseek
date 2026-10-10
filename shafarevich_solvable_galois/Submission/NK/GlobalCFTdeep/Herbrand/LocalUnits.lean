import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RepresentationTheory.Rep.Basic
import Mathlib.Topology.Metrizable.Uniformity
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Topology.Algebra.RestrictedProduct.Basic
import Submission.NK.GlobalCFT.Inclusion.globalCFT_localAction
import Submission.NK.GlobalCFTdeep.Herbrand.Fiber
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The decomposition group acting on the local units

For a place `w` of `L` over a place `v` of `K`, the decomposition group
`D_w = {σ : Gal(L/K) | σ • w = w}` (`NK.GlobalCFTdeep.decompositionSubgroup`) acts on the local
field `L_w` through the transported local isomorphism
`NK.GlobalCFT.Inclusion.Place.localAction σ w h : L_w ≃+* L_w` (`h : σ • w = w`), hence on the
local units `L_wˣ`.

This file packages that action as a `MulDistribMulAction` and as a `Rep ℤ D_w`
(`NK.GlobalCFTdeep.localUnitsRep`), the module that Milne's Proposition 2.7 coinduces from: the
fibre `∏_{w' | v} L_{w'}ˣ` (`NK.GlobalCFTdeep.fiberIdelesRep`) is `Coind_{D_w}^{G} L_wˣ`.

The group-action axioms are checked by a density argument inside the completion `L_w`: the
functions involved are continuous and agree on the image of the dense embedding `L → L_w`
(`NK.GlobalCFT.Inclusion.Place.localAction_algebraMap`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1600000

open scoped NumberField RestrictedProduct
open NumberField IsDedekindDomain

noncomputable section

namespace NK.GlobalCFTdeep

open NK.GlobalCFT

variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

/-- The local action of `σ ∈ Gal(L/K)` fixing `w` on `L_w`, unfolded. -/
theorem localAction_apply_eq (σ : L ≃ₐ[K] L) (w : Place L) (h : σ • w = w)
    (y : Place.localField L w) :
    NK.GlobalCFT.Inclusion.Place.localAction σ w h y =
      h ▸ (Place.localRingEquiv σ w y) := rfl

/-- The local action of `σ` on the image of `L` in `L_w`. -/
theorem localAction_algebraMap_eq (σ : L ≃ₐ[K] L) (w : Place L) (h : σ • w = w) (x : L) :
    NK.GlobalCFT.Inclusion.Place.localAction σ w h
        (algebraMap L (Place.localField L w) x) =
      algebraMap L (Place.localField L w) (σ x) := by
  rw [localAction_apply_eq, Place.localRingEquiv_algebraMap,
    Galois.localField_cast_algebraMap h (σ x)]

/-- The local action of the identity is the identity: both sides are continuous and agree on the
dense image of `L` in `L_w`. -/
theorem localAction_one_eq_refl (w : Place L) (h : (1 : L ≃ₐ[K] L) • w = w) :
    NK.GlobalCFT.Inclusion.Place.localAction (1 : L ≃ₐ[K] L) w h = 1 := by
  have hfun : (fun y : Place.localField L w =>
        NK.GlobalCFT.Inclusion.Place.localAction (1 : L ≃ₐ[K] L) w h y) = id := by
    refine DenseRange.equalizer (Galois.denseRange_algebraMap_localField w)
      (NK.GlobalCFT.Inclusion.Place.continuous_localAction _ _ _) continuous_id ?_
    funext x
    simp only [Function.comp_apply, id_eq]
    rw [localAction_algebraMap_eq, AlgEquiv.one_apply]
  exact RingEquiv.ext fun y => congrFun hfun y

/-- **The local action is multiplicative**: for `σ, τ` stabilising `w`, the local automorphism of
`L_w` attached to `σ * τ` is the composite of those attached to `σ` and `τ`.  Proved by density,
like `localAction_one_eq_refl`. -/
theorem localAction_mul_eq_trans (σ τ : L ≃ₐ[K] L) (w : Place L)
    (hσ : σ • w = w) (hτ : τ • w = w) (h : (σ * τ) • w = w) :
    NK.GlobalCFT.Inclusion.Place.localAction (σ * τ) w h =
      (NK.GlobalCFT.Inclusion.Place.localAction τ w hτ).trans
        (NK.GlobalCFT.Inclusion.Place.localAction σ w hσ) := by
  have hfun : (fun y : Place.localField L w =>
        NK.GlobalCFT.Inclusion.Place.localAction (σ * τ) w h y) =
      fun y : Place.localField L w =>
        NK.GlobalCFT.Inclusion.Place.localAction σ w hσ
          (NK.GlobalCFT.Inclusion.Place.localAction τ w hτ y) := by
    refine DenseRange.equalizer (Galois.denseRange_algebraMap_localField w)
      (NK.GlobalCFT.Inclusion.Place.continuous_localAction _ _ _)
      (Continuous.comp (NK.GlobalCFT.Inclusion.Place.continuous_localAction _ _ _)
        (NK.GlobalCFT.Inclusion.Place.continuous_localAction _ _ _)) ?_
    funext x
    simp only [Function.comp_apply]
    rw [localAction_algebraMap_eq τ w hτ x, localAction_algebraMap_eq σ w hσ (τ x),
      localAction_algebraMap_eq (σ * τ) w h x, AlgEquiv.mul_apply]
  exact RingEquiv.ext fun y => congrFun hfun y

/-- The action of the decomposition group on the local units `L_wˣ`, through the transported local
isomorphism `Place.localAction`. -/
noncomputable def decompositionUnitsAction (w : Place L) :
    MulDistribMulAction (decompositionSubgroup (K := K) (L := L) w)
      ((Place.localField L w)ˣ) where
  smul σ u := Units.map
    (NK.GlobalCFT.Inclusion.Place.localAction (σ : L ≃ₐ[K] L) w
      ((mem_decompositionSubgroup (K := K) (w := w)).mp σ.2)).toMonoidHom u
  one_smul u := by
    apply Units.ext
    exact congrArg (fun f : (Place.localField L w) ≃+* (Place.localField L w) => f ↑u)
      (localAction_one_eq_refl w
        ((mem_decompositionSubgroup (K := K) (w := w)).mp
          (1 : decompositionSubgroup (K := K) (L := L) w).2))
  mul_smul σ τ u := by
    apply Units.ext
    exact congrArg (fun f : (Place.localField L w) ≃+* (Place.localField L w) => f ↑u)
      (localAction_mul_eq_trans (σ : L ≃ₐ[K] L) (τ : L ≃ₐ[K] L) w
        ((mem_decompositionSubgroup (K := K) (w := w)).mp σ.2)
        ((mem_decompositionSubgroup (K := K) (w := w)).mp τ.2)
        ((mem_decompositionSubgroup (K := K) (w := w)).mp (σ * τ).2))
  smul_mul σ u v := by
    apply Units.ext
    exact map_mul _ _ _
  smul_one σ := by
    apply Units.ext
    exact map_one _

/-- **Milne's local units of the decomposition group, as a `ℤ[D_w]`-module**: the local units
`L_wˣ` with the action of `D_w = {σ | σ • w = w}` through the transported local isomorphism.
This is the module whose coinduction is the fibre `∏_{w' | v} L_{w'}ˣ`. -/
noncomputable def localUnitsRep (w : Place L) :
    Rep ℤ (decompositionSubgroup (K := K) (L := L) w) :=
  letI := decompositionUnitsAction (K := K) (L := L) w
  Rep.ofMulDistribMulAction (decompositionSubgroup (K := K) (L := L) w)
    ((Place.localField L w)ˣ)

end NK.GlobalCFTdeep
