import Mathlib.GroupTheory.SemidirectProduct
import Mathlib.Tactic.Have
import Mathlib.Algebra.Field.ZMod
import Mathlib.RepresentationTheory.Homological.GroupHomology.Functoriality
import Submission.Work.CohomologicalShrinking.hochschildSerre.flowQuotH1Equiv
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

open scoped TensorProduct
open CategoryTheory

namespace Work.CohomologicalShrinking.hochschildSerre

theorem flowHSExact (p : ℕ) [Fact p.Prime] (G : Type) [Group G] [Fintype G] (m i j : ℕ)
    (T : Type) [AddCommGroup T] [Module (ZMod p) T] [DistribMulAction G T]
    [SMulCommClass G (ZMod p) T] :
    ∃ α : groupHomology.H1 (Rep.res (flowNormal p G m i j).subtype (flowRep p G m i j T)) →+
            groupHomology.H1 (flowRep p G m i j T),
      ∃ β : groupHomology.H1 (flowRep p G m i j T) →+
            groupHomology.H1 (flowRepG p G m i j T),
        (∀ x, α x = (groupHomology.H1CoresCoinfOfTrivial (flowRep p G m i j T)
              (flowNormal p G m i j)).f.hom x) ∧
        Function.Surjective β ∧ α.range = β.ker := by
  classical
  -- The identification `Γ ⧸ S ≃* G` carries the representation `(flowRep p G m i j T).ofQuotient S`
  -- to `flowRepG p G m i j T`.
  have he : ∀ q : flowGroup p G m i j ⧸ flowNormal p G m i j,
      (LinearEquiv.refl (ZMod p) (E p G m i j ⊗[ZMod p] T)) ∘ₗ
        ((Rep.ofQuotient (flowRep p G m i j T) (flowNormal p G m i j)).ρ q) =
      (flowRepG p G m i j T).ρ (flowQuotEquiv p G m i j q) ∘ₗ
        (LinearEquiv.refl (ZMod p) (E p G m i j ⊗[ZMod p] T)) := by
    intro q
    rw [LinearEquiv.refl_toLinearMap, LinearMap.id_comp, LinearMap.comp_id]
    induction q using QuotientGroup.induction_on with
    | H γ =>
      apply LinearMap.ext
      intro x
      rw [show flowQuotEquiv p G m i j (QuotientGroup.mk γ) = flowQuot p G m i j γ from by
        have h1 : (QuotientGroup.quotientMulEquivOfEq (flowQuot_ker p G m i j).symm)
            (QuotientGroup.mk γ) = QuotientGroup.mk γ :=
          QuotientGroup.quotientMulEquivOfEq_mk _ _
        rw [flowQuotEquiv, MulEquiv.trans_apply, h1]
        simp only [QuotientGroup.quotientKerEquivOfSurjective,
          QuotientGroup.quotientKerEquivOfRightInverse_apply]
        exact QuotientGroup.kerLift_mk _ _]
      rw [Representation.ofQuotient_coe_apply]
      rfl
  -- The composite `H₁(Γ, A) ⟶ H₁(Γ⧸S, A_S) ≅ H₁(G, B)`.
  let eL : (groupHomology.H1 (Rep.ofQuotient (flowRep p G m i j T)
        (flowNormal p G m i j)) : Type) ≃ₗ[ZMod p]
      (groupHomology.H1 (flowRepG p G m i j T) : Type) :=
    (groupHomology.mapIso (flowQuotEquiv p G m i j)
      (LinearEquiv.refl (ZMod p) (E p G m i j ⊗[ZMod p] T)) he 1).toLinearEquiv
  let fL : (groupHomology.H1 (Rep.res (flowNormal p G m i j).subtype
        (flowRep p G m i j T)) : Type) →ₗ[ZMod p]
      (groupHomology.H1 (flowRep p G m i j T) : Type) :=
    (groupHomology.H1CoresCoinfOfTrivial (flowRep p G m i j T) (flowNormal p G m i j)).f.hom
  let gL : (groupHomology.H1 (flowRep p G m i j T) : Type) →ₗ[ZMod p]
      (groupHomology.H1 (Rep.ofQuotient (flowRep p G m i j T)
        (flowNormal p G m i j)) : Type) :=
    (groupHomology.H1CoresCoinfOfTrivial (flowRep p G m i j T) (flowNormal p G m i j)).g.hom
  let βL : (groupHomology.H1 (flowRep p G m i j T) : Type) →ₗ[ZMod p]
      (groupHomology.H1 (flowRepG p G m i j T) : Type) := eL.toLinearMap.comp gL
  refine ⟨fL.toAddMonoidHom, βL.toAddMonoidHom, ?_, ?_, ?_⟩
  · intro x; rfl
  · -- `g` is surjective (it is an epimorphism) and `eL` is an isomorphism.
    intro y
    have hgsurj : Function.Surjective gL :=
      (ModuleCat.epi_iff_surjective _).mp inferInstance
    obtain ⟨z, hz⟩ := hgsurj (eL.symm y)
    exact ⟨z, by change eL (gL z) = y; rw [hz, LinearEquiv.apply_symm_apply]⟩
  · -- Exactness of `H₁(S, A) → H₁(Γ, A) → H₁(Γ⧸S, A_S)`, transported along `eL`.
    have hrange : fL.range = gL.ker :=
      CategoryTheory.ShortComplex.Exact.moduleCat_range_eq_ker
        (groupHomology.H1CoresCoinfOfTrivial_exact (flowRep p G m i j T) (flowNormal p G m i j))
    have hker : βL.ker = gL.ker := by
      ext x
      rw [LinearMap.mem_ker, LinearMap.mem_ker]
      change eL (gL x) = 0 ↔ gL x = 0
      rw [eL.map_eq_zero_iff]
    have hα : (fL.toAddMonoidHom).range = fL.range.toAddSubgroup :=
      (LinearMap.range_toAddSubgroup fL).symm
    have hβ : (βL.toAddMonoidHom).ker = βL.ker.toAddSubgroup :=
      (LinearMap.ker_toAddSubgroup βL).symm
    rw [hα, hβ, hker, ← hrange]

end Work.CohomologicalShrinking.hochschildSerre
