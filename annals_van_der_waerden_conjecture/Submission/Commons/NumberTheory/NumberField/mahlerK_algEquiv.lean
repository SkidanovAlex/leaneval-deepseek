import Mathlib
import Submission.Commons.NumberTheory.NumberField.ncard_mahler_one_le

set_option maxHeartbeats 1000000

open NumberField
open scoped Classical

namespace Commons.NumberTheory.NumberField

noncomputable section

/-- The Mahler measure of an element is the product of `max 1 ‖σ x‖` over all ring embeddings
`σ : K →+* ℂ`.  This holds for every element (no integrality hypothesis is needed). -/
lemma mahlerK_eq_prod_ringHom {K : Type*} [Field K] [NumberField K] (x : K) :
    mahlerK K x = ∏ σ : K →+* ℂ, max 1 ‖σ x‖ := by
  classical
  rw [mahlerK]
  simp only [NumberField.mixedEmbedding.normAtPlace_apply]
  rw [← Finset.prod_fiberwise Finset.univ (fun σ : K →+* ℂ => NumberField.InfinitePlace.mk σ)
        (fun σ => max 1 ‖σ x‖)]
  refine Finset.prod_congr rfl (fun w _ => ?_)
  rw [Finset.prod_congr rfl (fun σ (hσ : σ ∈ Finset.univ.filter
        (fun σ : K →+* ℂ => NumberField.InfinitePlace.mk σ = w)) => ?_),
      Finset.prod_const]
  · rw [NumberField.InfinitePlace.card_filter_mk_eq]
  · have h : NumberField.InfinitePlace.mk σ = w := (Finset.mem_filter.mp hσ).2
    rw [← h, NumberField.InfinitePlace.apply]

theorem mahlerK_algEquiv {L K : Type*} [Field L] [Field K] [Algebra ℚ L] [Algebra ℚ K]
    [NumberField L] [NumberField K] (e : L ≃ₐ[ℚ] K) (x : L) :
    Commons.NumberTheory.NumberField.mahlerK K (e x)
      = Commons.NumberTheory.NumberField.mahlerK L x := by
  rw [mahlerK_eq_prod_ringHom (K := K) (e x), mahlerK_eq_prod_ringHom (K := L) x]
  let ψ : (K →+* ℂ) ≃ (L →+* ℂ) :=
    { toFun := fun σ => σ.comp (e.toAlgHom : L →+* K)
      invFun := fun τ => τ.comp (e.symm.toAlgHom : K →+* L)
      left_inv := by
        intro σ
        ext y
        exact congrArg σ (AlgEquiv.apply_symm_apply e y)
      right_inv := by
        intro τ
        ext y
        exact congrArg τ (AlgEquiv.symm_apply_apply e y) }
  refine Fintype.prod_equiv ψ (fun σ : K →+* ℂ => max 1 ‖σ (e x)‖)
    (fun τ : L →+* ℂ => max 1 ‖τ x‖) ?_
  intro σ
  show max 1 ‖σ (e x)‖ = max 1 ‖(σ.comp (e.toAlgHom : L →+* K)) x‖
  rw [RingHom.comp_apply]
  rfl

end

end Commons.NumberTheory.NumberField
