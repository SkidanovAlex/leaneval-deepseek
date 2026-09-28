import Mathlib
import Submission.Work.Cohomology.Crux.vkOvl_model_pair_map
import Submission.Work.Cohomology.Crux.vkOvlDefs
import Submission.Work.Cohomology.Crux.relComplexMapHomologyIsoCompat
import Submission.Work.Cohomology.CompatTrans.sph3DiscRelHomology
import Submission.Work.Cohomology.uctDual_evaluation
import Submission.Work.Cohomology.Crux.ovlPairModelDefs

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
set_option linter.style.haveILetI false

namespace Work.Cohomology.Endgame

open CategoryTheory AlgebraicTopology CategoryTheory.Limits
open scoped Topology

noncomputable section

/-- The evaluation duality `((Fin r → ℤ) →ₗ[ℤ] ℤ) ≃ₗ[ℤ] (Fin r → ℤ)` given by the dual basis of the
standard basis of `Fin r → ℤ`. -/
def dualSelfFin (r : ℕ) : ((Fin r → ℤ) →ₗ[ℤ] ℤ) ≃ₗ[ℤ] (Fin r → ℤ) :=
  ((Pi.basisFun ℤ (Fin r)).dualBasis).equivFun

/-- **The relative cohomology of the model pair `(S³ × D⁴, S³ × S³)`.**

It is `ℤ` in degrees `4` and `7` and zero otherwise: the universal coefficient theorem identifies
the relative cohomology with the `ℤ`-dual of the relative homology computed in
`Work.Cohomology.sph3DiscRelHomology`, and the dual of `ℤ^r` (with `r ∈ {0,1}`) is `ℤ^r`. -/
theorem pairRelCohom_iso (n : ℕ) :
    Nonempty (Work.Cohomology.relCohomology ℤ Work.Cohomology.PairXT Work.Cohomology.PairAT n ≅
      ModuleCat.of ℤ (Fin ((if n = 4 then 1 else 0) + (if n = 7 then 1 else 0)) → ℤ)) := by
  have hfree : ∀ k, Module.Free ℤ
      ↥((Work.Cohomology.relChains Work.Cohomology.PairXT Work.Cohomology.PairAT).homology k) := by
    intro k
    obtain ⟨ek⟩ := Work.Cohomology.sph3DiscRelHomology k
    haveI : Module.Free ℤ ↥(ModuleCat.of ℤ
        (Fin ((if k = 4 then 1 else 0) + (if k = 7 then 1 else 0)) → ℤ)) := inferInstance
    exact Module.Free.of_equiv (σ := RingHom.id ℤ) (σ' := RingHom.id ℤ)
      (Work.Cohomology.uctIsoToLinearEquiv ek).symm
  obtain ⟨eDual⟩ :=
    Work.Cohomology.relCochainDual (Work.Cohomology.PairXT) (Work.Cohomology.PairAT)
  obtain ⟨eUct⟩ := Work.Cohomology.uctDual
    (Work.Cohomology.relChains Work.Cohomology.PairXT Work.Cohomology.PairAT)
    (Work.Cohomology.relChainsProjective _ _) hfree n
  obtain ⟨eHom⟩ := Work.Cohomology.sph3DiscRelHomology n
  -- the identification of the dual with `ℤ` in the two degrees where the homology is nonzero
  let L : ↥((Work.Cohomology.relChains Work.Cohomology.PairXT
      Work.Cohomology.PairAT).homology n) ≃ₗ[ℤ]
      (Fin ((if n = 4 then 1 else 0) + (if n = 7 then 1 else 0)) → ℤ) :=
    Work.Cohomology.uctIsoToLinearEquiv eHom
  let dIso : ModuleCat.of ℤ
      (Module.Dual ℤ ↥((Work.Cohomology.relChains Work.Cohomology.PairXT
        Work.Cohomology.PairAT).homology n)) ≅
      ModuleCat.of ℤ (Fin ((if n = 4 then 1 else 0) + (if n = 7 then 1 else 0)) → ℤ) :=
    LinearEquiv.toModuleIso
      ((LinearEquiv.dualMap L.symm).trans (dualSelfFin _))
  exact ⟨(HomologicalComplex.homologyMapIso eDual n).trans (eUct.trans dIso)⟩

/-- The comparison map of pairs `(U ∩ V, (U ∩ V) ∩ Mk) ⟶ (S³ × D⁴, S³ × S³)` induces an
isomorphism on relative cohomology in every degree: it is a homotopy equivalence of pairs. -/
theorem ovlRelComplexMap_isIso (n : ℕ) : CategoryTheory.IsIso (HomologicalComplex.homologyMap
    (Work.Cohomology.relComplexMap (X₁ := Work.Cohomology.Crux.vkOvl)
      (X₂ := Work.Cohomology.PairXT) ℤ Work.Cohomology.Crux.vkOvlA Work.Cohomology.PairAT
      Work.Cohomology.Crux.ovlPairMap Work.Cohomology.Crux.ovlPairMap_mem) n) :=
  Work.Cohomology.Crux.relComplexMapHomologyIsoCompat (X₁ := Work.Cohomology.Crux.vkOvl)
    (X₂ := Work.Cohomology.PairXT) (A₁ := Work.Cohomology.Crux.vkOvlA) (A₂ := Work.Cohomology.PairAT)
    (f := Work.Cohomology.Crux.ovlPairMap) (h := Work.Cohomology.Crux.ovlPairMap_mem) n
    Work.Cohomology.Crux.ovlPairMap_chainMap_isIso
    Work.Cohomology.Crux.ovlPairMapA_chainMap_isIso

theorem ovlCohomologyGroups (n : ℕ) :
    Nonempty (Work.Cohomology.relCohomology ℤ Work.Cohomology.Crux.vkOvl Work.Cohomology.Crux.vkOvlA n ≅
      ModuleCat.of ℤ (Fin ((if n = 4 then 1 else 0) + (if n = 7 then 1 else 0)) → ℤ)) := by
  obtain ⟨eModel⟩ := pairRelCohom_iso n
  let f := HomologicalComplex.homologyMap
      (Work.Cohomology.relComplexMap (X₁ := Work.Cohomology.Crux.vkOvl)
        (X₂ := Work.Cohomology.PairXT) ℤ Work.Cohomology.Crux.vkOvlA Work.Cohomology.PairAT
        Work.Cohomology.Crux.ovlPairMap Work.Cohomology.Crux.ovlPairMap_mem) n
  haveI : CategoryTheory.IsIso f := ovlRelComplexMap_isIso n
  exact ⟨(CategoryTheory.asIso f).symm ≪≫ eModel⟩

end

end Work.Cohomology.Endgame
