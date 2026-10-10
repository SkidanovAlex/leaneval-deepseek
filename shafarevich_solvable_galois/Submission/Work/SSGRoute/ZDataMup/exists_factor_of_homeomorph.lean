import Mathlib.FieldTheory.KrullTopology
import Mathlib.Algebra.Field.ZMod
import Mathlib.Topology.LocallyConstant.Basic
import Submission.Work.SSGRoute.ZDataMup.exists_factor_restrictNormalHom
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute.ZDataMup

theorem exists_factor_of_homeomorph {p : ℕ} [Fact p.Prime] {F F' G : Type*} [Field F]
    [Field F'] [Algebra F F'] [IsGalois F F'] [Group G] [TopologicalSpace G]
    (e : G ≃* (F' ≃ₐ[F] F')) (he : IsHomeomorph (⇑e))
    (y : G →* Multiplicative (ZMod p)) (hy : IsLocallyConstant y) :
    ∃ y' : NK.LocalCFT.AbGal F F' →* Multiplicative (ZMod p),
      y'.comp ((AlgEquiv.restrictNormalHom (NK.LocalReciprocity.maxAbelianSubext F F')).comp
        e.toMonoidHom) = y := by
  classical
  -- `Gal(F^{ab}/F)` is Galois over `F`: it is the fixed field of the commutator subgroup.
  haveI : IsGalois F (NK.LocalReciprocity.maxAbelianSubext F F') := inferInstance
  -- Transport `y` across the homeomorphism `e` to a locally constant character of `Gal(F'/F)`.
  have hz : IsLocallyConstant (⇑(y.comp e.symm.toMonoidHom)) := by
    show IsLocallyConstant (⇑y ∘ ⇑e.symm)
    refine hy.comp_continuous ?_
    rw [show (⇑e.symm : (F' ≃ₐ[F] F') → G) = ⇑((e : G ≃ (F' ≃ₐ[F] F')).symm) from rfl]
    exact (Equiv.continuous_symm_iff _).mpr he.isOpenMap
  -- Factor the transported character through the restriction to `F^{ab}`.
  obtain ⟨y', hy'⟩ := Work.SSGRoute.ZDataMup.exists_factor_restrictNormalHom (p := p)
    (y.comp e.symm.toMonoidHom) hz
  refine ⟨y', ?_⟩
  rw [← MonoidHom.comp_assoc]
  rw [hy']
  ext g
  simp [MulEquiv.symm_apply_apply]

end Work.SSGRoute.ZDataMup
