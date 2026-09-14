import Mathlib
import Submission.Commons.NumberTheory.NumberField.ncard_mahler_one_le
import Submission.Commons.NumberTheory.Height.NumberField.logHeight1_eq_sum_embeddings_log_max_of_isIntegral

namespace Commons.NumberTheory.NumberField

open scoped Classical

theorem mahlerK_eq_prod_embeddings {K : Type*} [Field K] [NumberField K] {x : K} (hx : IsIntegral ℤ x) :
    Commons.NumberTheory.NumberField.mahlerK K x = ∏ σ : K →+* ℂ, max 1 ‖σ x‖ := by
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

end Commons.NumberTheory.NumberField
