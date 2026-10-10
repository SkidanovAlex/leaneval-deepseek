import Mathlib.Algebra.CharZero.Infinite
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.RingTheory.Ideal.Norm.AbsNorm
import Mathlib.Topology.Algebra.Category.ProfiniteGrp.Completion
import Submission.Work.SSGRoute.inertia_of_isInertia
import Submission.Work.SSGRoute.isInertia_of_mem_inertia
import Submission.Work.SSGRoute.local_tame_defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute

/-- The residue-cardinality normalisation at the local-structure `q`. -/
theorem residueCardMatches_localStructure (A' : NK.FrobeniusBridge.FinitePlaceOf ℚ SSGRoute.QBar) :
    NK.ResidueFrob.ResidueCardMatches A'
      (NK.LocalStructure.residueCard ℚ (Submission.NeukirchUchida.primeOf A'.1 A'.2)) := by
  rw [NK.ResidueFrob.ResidueCardMatches]
  unfold NK.LocalStructure.residueCard
  rw [Commons.NumberTheory.NumberField.residueCard_adicCompletion_eq_absNorm,
    Ideal.absNorm_apply, Submodule.cardQuot_apply]

theorem localZhatHom_ker (A' : NK.FrobeniusBridge.FinitePlaceOf ℚ SSGRoute.QBar) :
    (Work.SSGRoute.localZhatHom A').ker = Work.SSGRoute.globalInertiaSub A' := by
  classical
  -- identify the decomposition group of the place with its `NeukirchUchida` incarnation
  let e : ↥(SSGRoute.decomp ℚ A'.1) →*
      Gal(NK.FrobeniusBridge.localClosure A' / NK.FrobeniusBridge.localField A') :=
    (NK.FrobeniusBridge.localGaloisEquiv A').toMonoidHom
  -- the two directions of the inertia identification (the imported halves)
  have hS : ∀ σ : ↥(SSGRoute.decomp ℚ A'.1),
      SSGRoute.IsInertia ℚ A'.1 (σ : SSGRoute.QBar ≃ₐ[ℚ] SSGRoute.QBar) ↔
        e σ ∈ localInertia A' := by
    intro σ
    constructor
    · intro h
      exact inertia_of_isInertia A' (residueChar A')
        (NK.LocalStructure.residueCard ℚ (Submission.NeukirchUchida.primeOf A'.1 A'.2))
        (tameData_rat A') (residueCardMatches_localStructure A') rfl σ h
    · intro h
      exact isInertia_of_mem_inertia A' (residueChar A')
        (NK.LocalStructure.residueCard ℚ (Submission.NeukirchUchida.primeOf A'.1 A'.2))
        (tameData_rat A') (residueCardMatches_localStructure A') rfl σ h
  -- the global inertia subgroup is the preimage of the local inertia subgroup
  have hK : Subgroup.comap e (localInertia A') = globalInertiaSub A' := by
    rw [globalInertiaSub]
    apply le_antisymm
    · intro g hg
      exact Subgroup.subset_closure
        ((hS g).mpr ((Subgroup.mem_comap (K := localInertia A') (f := e)).mp hg))
    · rw [Subgroup.closure_le]
      intro g hg
      exact (Subgroup.mem_comap (K := localInertia A') (f := e)).mpr ((hS g).mp hg)
  -- the kernel of the quotient map is exactly that preimage
  have hker : (localZhatHom A').ker = Subgroup.comap e (localInertia A') := by
    have hdef : localZhatHom A' =
        (Classical.choice ((localTameData A').structure_input.unramifiedQuotient)).toMonoidHom.comp
          ((QuotientGroup.mk' (localInertia A')).comp e) := rfl
    calc (localZhatHom A').ker
        = ((Classical.choice
              ((localTameData A').structure_input.unramifiedQuotient)).toMonoidHom.comp
            ((QuotientGroup.mk' (localInertia A')).comp e)).ker := by rw [hdef]
      _ = ((QuotientGroup.mk' (localInertia A')).comp e).ker :=
            MonoidHom.ker_mulEquiv_comp _
              (Classical.choice ((localTameData A').structure_input.unramifiedQuotient))
      _ = Subgroup.comap e (QuotientGroup.mk' (localInertia A')).ker :=
            (MonoidHom.comap_ker (QuotientGroup.mk' (localInertia A')) e).symm
      _ = Subgroup.comap e (localInertia A') := by rw [QuotientGroup.ker_mk']
  rw [hker, hK]

end Work.SSGRoute
