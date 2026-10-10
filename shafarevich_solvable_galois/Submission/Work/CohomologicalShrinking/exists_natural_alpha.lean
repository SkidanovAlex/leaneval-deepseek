import Mathlib.GroupTheory.SemidirectProduct
import Mathlib.Algebra.Field.ZMod
import Mathlib.RepresentationTheory.Homological.GroupHomology.LowDegree
import Submission.Work.CohomologicalShrinking.naturalAlpha.cores_natural
import Submission.Work.CohomologicalShrinking.naturalAlpha.exists_psiLin
import Submission.Work.CohomologicalShrinking.naturalAlpha.psiLin_natural
import Submission.Work.CohomologicalShrinking.naturalAlpha.sqLin_natural
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

set_option maxHeartbeats 1600000

namespace Work.CohomologicalShrinking

open scoped TensorProduct

theorem exists_natural_alpha (p : ℕ) [Fact p.Prime] (G : Type) [Group G] [Fintype G] {i j : ℕ}
    (hi : 2 ≤ i) (T : Type) [AddCommGroup T] [Module (ZMod p) T] [DistribMulAction G T]
    [SMulCommClass G (ZMod p) T] :
    ∃ α : ∀ m : ℕ, TensorProduct (ZMod p) (squareQuotient p G m)
        (TensorProduct (ZMod p) (E p G m i j) T) →+
        (↑(groupHomology.H1 (flowRep p G m i j T)) : Type),
      (∀ m : ℕ, (α m).range = (flowHSα p G i j T m).range) ∧
      (∀ ⦃m n : ℕ⦄ (Φ : OperatorMap G m n)
        (x : TensorProduct (ZMod p) (squareQuotient p G m)
          (TensorProduct (ZMod p) (E p G m i j) T)),
        α n (Φ.h1Map p G T x) = flowZMap (p := p) G i j Φ T (α m x)) := by
  classical
  -- the universal-coefficient surjection `pQN ⊗ E ⊗ T ↠ H₁(N, E ⊗ T)`
  let psi := fun m : ℕ => Classical.choose (naturalAlpha.exists_psiLin p ↥(flowNormal p G m i j)
      (Rep.res (flowNormal p G m i j).subtype (flowRep p G m i j T)))
  have psi_spec := fun m : ℕ => Classical.choose_spec
    (naturalAlpha.exists_psiLin p ↥(flowNormal p G m i j)
      (Rep.res (flowNormal p G m i j).subtype (flowRep p G m i j T)))
  have psi_surj : ∀ m : ℕ, Function.Surjective (psi m) := fun m => (psi_spec m).1
  -- the canonical identification `F(m)/F(m)^2 → (F(m)/ν)/(F(m)/ν)^2`
  let sq : ∀ m : ℕ, squareQuotient p G m →ₗ[ZMod p]
      Additive (Work.Shrinking.pCentralQuotient p ↥(flowNormal p G m i j) 0) :=
    fun m => naturalAlpha.pQMapLin p (flow.flowNormalSurj p G m i j)
  -- the composite `F(m)/F(m)^2 ⊗ E ⊗ T → H₁(N_m, E ⊗ T)`
  let beta : ∀ m : ℕ, TensorProduct (ZMod p) (squareQuotient p G m)
      (TensorProduct (ZMod p) (E p G m i j) T) →+
      (↑(groupHomology.H1 (Rep.res (flowNormal p G m i j).subtype (flowRep p G m i j T))) : Type) :=
    fun m => (psi m).comp (TensorProduct.map (sq m) (LinearMap.id)).toAddMonoidHom
  -- the paper's `α`
  let alpha : ∀ m : ℕ, TensorProduct (ZMod p) (squareQuotient p G m)
      (TensorProduct (ZMod p) (E p G m i j) T) →+
      (↑(groupHomology.H1 (flowRep p G m i j T)) : Type) :=
    fun m => (naturalAlpha.coresH p G i j T m).comp (beta m)
  have beta_surjective : ∀ m, Function.Surjective (beta m) := by
    intro m
    have hsq : Function.Surjective (TensorProduct.map (sq m) (LinearMap.id :
        TensorProduct (ZMod p) (E p G m i j) T →ₗ[ZMod p]
          TensorProduct (ZMod p) (E p G m i j) T)) :=
      TensorProduct.map_surjective
        (naturalAlpha.pQMapLin_surjective p (flow.flowNormalSurj p G m i j)
          (flow.flowNormalSurj_surjective p G m i j)) (fun y => ⟨y, rfl⟩)
    exact (psi_surj m).comp hsq
  refine ⟨alpha, ?_, ?_⟩
  · intro m
    have hβ : (alpha m).range = (naturalAlpha.coresH p G i j T m).range := by
      show ((naturalAlpha.coresH p G i j T m).comp (beta m)).range
        = (naturalAlpha.coresH p G i j T m).range
      rw [AddMonoidHom.range_comp, AddMonoidHom.range_eq_top.mpr (beta_surjective m),
        ← AddMonoidHom.range_eq_map]
    rw [hβ, ← naturalAlpha.flowHSα_eq_coresH p G i j T m]
  · intro m n Φ x
    -- the tensor-level naturality square
    have hsquare : (TensorProduct.map (sq n) (LinearMap.id)) ∘ₗ
        (TensorProduct.map (quotMapLin p G Φ.toHom Φ.surjective)
          ((gradedMapLin p Φ.toHom Φ.surjective i j).rTensor T))
        = (TensorProduct.map (naturalAlpha.pQMapLin p (flowNormalSubMap p G i j Φ))
            ((Rep.Hom.hom (naturalAlpha.flowRepMapN p G i j Φ T)).toLinearMap)) ∘ₗ
          (TensorProduct.map (sq m) (LinearMap.id)) := by
      rw [naturalAlpha.flowRepMapN_hom]
      rw [← TensorProduct.map_comp, ← TensorProduct.map_comp]
      congr 1
      · refine LinearMap.ext fun q => ?_
        rw [LinearMap.comp_apply, LinearMap.comp_apply]
        change naturalAlpha.pQMapLin p (flow.flowNormalSurj p G n i j)
            (quotMapLin p G Φ.toHom Φ.surjective q)
          = naturalAlpha.pQMapLin p (flowNormalSubMap p G i j Φ)
            (naturalAlpha.pQMapLin p (flow.flowNormalSurj p G m i j) q)
        exact (naturalAlpha.sqLin_natural p G i j Φ q).symm
    have hbeta_nat : beta n (Φ.h1Map p G T x) = naturalAlpha.mapNormal p G i j Φ T (beta m x) := by
      have h := LinearMap.congr_fun hsquare x
      rw [LinearMap.comp_apply, LinearMap.comp_apply] at h
      show psi n ((TensorProduct.map (sq n) (LinearMap.id))
            ((TensorProduct.map (quotMapLin p G Φ.toHom Φ.surjective)
              ((gradedMapLin p Φ.toHom Φ.surjective i j).rTensor T)) x))
          = naturalAlpha.mapNormal p G i j Φ T (psi m ((TensorProduct.map (sq m) (LinearMap.id)) x))
      rw [h]
      exact naturalAlpha.psiLin_natural p
        (A := Rep.res (flowNormal p G m i j).subtype (flowRep p G m i j T))
        (A' := Rep.res (flowNormal p G n i j).subtype (flowRep p G n i j T))
        (f := flowNormalSubMap p G i j Φ) (c := naturalAlpha.flowRepMapN p G i j Φ T)
        (ψ := psi m) (ψ' := psi n) (psi_spec m).2 (psi_spec n).2 _
    calc alpha n (Φ.h1Map p G T x)
        = naturalAlpha.coresH p G i j T n (beta n (Φ.h1Map p G T x)) := rfl
      _ = naturalAlpha.coresH p G i j T n (naturalAlpha.mapNormal p G i j Φ T (beta m x)) := by
            rw [hbeta_nat]
      _ = flowZMap (p := p) G i j Φ T (naturalAlpha.coresH p G i j T m (beta m x)) := by
            change ((naturalAlpha.coresH p G i j T n).comp (naturalAlpha.mapNormal p G i j Φ T)) (beta m x)
              = ((flowZMap (p := p) G i j Φ T).comp (naturalAlpha.coresH p G i j T m)) (beta m x)
            rw [← naturalAlpha.cores_natural p G i j Φ T]
      _ = flowZMap (p := p) G i j Φ T (alpha m x) := rfl

end Work.CohomologicalShrinking
