import Mathlib.Combinatorics.Quiver.ReflQuiver
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Algebra.Module.StablyFree.Basic
import Mathlib.RepresentationTheory.Homological.GroupCohomology.LongExactSequence
import Mathlib.RepresentationTheory.Homological.GroupHomology.LongExactSequence
import Submission.Work.SSGRoute.H1Dual.Vanish
import Submission.Work.SSGRoute.H1Dual.degreeZeroBijective
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

noncomputable section

open CategoryTheory
open CategoryTheory.Limits

namespace Work.SSGRoute.H1Dual

universe u

variable {k : Type} [Field k] {G : Type} [Group G] [Fintype G]

/-- `H₀(G, augKer M)` is finite-dimensional, `M` being finite and `G` finite. -/
theorem moduleFinite_H0_augKer (M : Rep k G) [Finite M.V] :
    Module.Finite k (groupHomology.H0 (augKer M)) := by
  haveI h : Module.Finite k (coindRep k G M.V).V := by
    haveI : Module.Finite k (G → M.V) := Module.Finite.of_finite
    exact inferInstanceAs (Module.Finite k (G → M.V))
  haveI : Module.Finite k (augKer M).V :=
    inferInstanceAs (Module.Finite k
      ↥(LinearMap.ker (Rep.Hom.hom (coindAugHom M)).toLinearMap))
  haveI hc : Module.Finite k ((Rep.coinvariantsFunctor k G).obj (augKer M)) :=
    inferInstanceAs (Module.Finite k ((augKer M).ρ.Coinvariants))
  exact Module.Finite.of_surjective
    (Iso.toLinearEquiv (groupHomology.H0Iso (augKer M))).symm.toLinearMap
    (Iso.toLinearEquiv (groupHomology.H0Iso (augKer M))).symm.surjective

/-- **Tate duality in degrees `-2` and `1`**, assembly form: using the two dimension shifts and
the degree-`0` pairing, `H₁(G,M) ≅ H¹(G,M^∨)^∨`. -/
theorem tateDual_main (M : Rep k G) [Finite M.V]
    (hS₂ : (dualSES M).ShortExact)
    (hnat : ∀ {X Y : Rep k G} (f : X ⟶ Y) (l : Module.Dual k (groupHomology.H0 Y)),
      H0DualMap X
          ((ModuleCat.Hom.hom ((groupHomology.functor k G 0).map f)).dualMap l) =
        (ModuleCat.Hom.hom ((groupCohomology.functor k G 0).map (dualHom f)))
          (H0DualMap Y l)) :
    Nonempty (groupHomology.H1 M ≃ₗ[k]
      Module.Dual k (groupCohomology.H1 (dualRep M))) := by
  classical
  haveI : Module.Finite k (groupHomology.H0 (augKer M)) := moduleFinite_H0_augKer M
  -- the two dimension shifts
  obtain ⟨eA⟩ := H1_ker_H0 M (isZero_groupHomology_coindRep (k := k) (G := G) M.V)
  obtain ⟨eB⟩ := H1_dual_coker M hS₂
    (isZero_groupCohomology_dualRep_coindRep (k := k) (G := G) M.V)
  -- the maps `H₀(M') → H₀(F)` and its transpose `H⁰(F^∨) → H⁰((M')^∨)`
  set homR : groupHomology.H0 (augKer M) →ₗ[k] groupHomology.H0 (coindRep k G M.V) :=
    ModuleCat.Hom.hom ((groupHomology.functor k G 0).map (augKerSubtype M)) with hhomR
  set cohR : groupCohomology.H0 (dualRep (coindRep k G M.V)) →ₗ[k]
      groupCohomology.H0 (dualRep (augKer M)) :=
    ModuleCat.Hom.hom ((groupCohomology.functor k G 0).map (dualHom (augKerSubtype M)))
    with hcohR
  -- the degree-`0` pairings
  set ΦX : Module.Dual k (groupHomology.H0 (augKer M)) ≃ₗ[k]
      groupCohomology.H0 (dualRep (augKer M)) :=
    LinearEquiv.ofBijective (H0DualMap (augKer M)) (degreeZeroBijective (augKer M)) with hΦX
  set ΦY : Module.Dual k (groupHomology.H0 (coindRep k G M.V)) ≃ₗ[k]
      groupCohomology.H0 (dualRep (coindRep k G M.V)) :=
    LinearEquiv.ofBijective (H0DualMap (coindRep k G M.V))
      (degreeZeroBijective (coindRep k G M.V)) with hΦY
  have hnat' : ∀ l : Module.Dual k (groupHomology.H0 (coindRep k G M.V)),
      ΦX (homR.dualMap l) = cohR (ΦY l) := by
    intro l
    show H0DualMap (augKer M)
      ((ModuleCat.Hom.hom ((groupHomology.functor k G 0).map (augKerSubtype M))).dualMap l) =
      (ModuleCat.Hom.hom ((groupCohomology.functor k G 0).map (dualHom (augKerSubtype M))))
        (H0DualMap (coindRep k G M.V) l)
    exact hnat (augKerSubtype M) l
  -- `ΦX` carries `range (homR^∨)` onto `range cohR`
  have hrange : Submodule.map (ΦX : Module.Dual k (groupHomology.H0 (augKer M)) →ₗ[k]
      groupCohomology.H0 (dualRep (augKer M))) homR.dualMap.range = cohR.range := by
    apply le_antisymm
    · rintro _ ⟨l, hl, rfl⟩
      obtain ⟨l', rfl⟩ := hl
      refine ⟨ΦY l', ?_⟩
      rw [← hnat' l']
      rfl
    · rintro _ ⟨χ, rfl⟩
      refine ⟨homR.dualMap (ΦY.symm χ), ⟨_, rfl⟩, ?_⟩
      have h := hnat' (ΦY.symm χ)
      rw [LinearEquiv.apply_symm_apply] at h
      exact h
  -- quotient comparison and `coker(g^∨) ≅ (ker g)^∨`
  have hq : (Module.Dual k (groupHomology.H0 (augKer M)) ⧸ homR.dualMap.range) ≃ₗ[k]
      (groupCohomology.H0 (dualRep (augKer M)) ⧸ cohR.range) :=
    Submodule.Quotient.equiv homR.dualMap.range cohR.range ΦX hrange
  obtain ⟨eC⟩ := dualCoker homR
  have eD : groupCohomology.H1 (dualRep M) ≃ₗ[k] Module.Dual k ↥homR.ker :=
    eB.trans (hq.symm.trans eC)
  -- double dual of the (finite-dimensional) kernel
  haveI : Module.Finite k ↥homR.ker := inferInstance
  refine ⟨eA.trans ((Module.evalEquiv k ↥homR.ker).trans (LinearEquiv.dualMap eD))⟩

end Work.SSGRoute.H1Dual
