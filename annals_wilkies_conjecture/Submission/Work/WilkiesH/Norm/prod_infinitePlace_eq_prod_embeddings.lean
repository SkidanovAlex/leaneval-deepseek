import Mathlib

namespace Work.WilkiesH.Norm

/-- The archimedean part of the (multiplicative) height of a tuple over a number field, expressed
as a product over the infinite places weighted by their multiplicity, equals the product over all
complex embeddings of the largest modulus attained by the tuple.

This is the "group by infinite place" identity: the complex embeddings of `K` partition into the
fibres of `InfinitePlace.mk`, each fibre over a place `v` having cardinality `v.mult`, and on each
fibre the quantity `⨆ i, ‖φ (x i)‖` equals `⨆ i, v (x i)`. -/
theorem prod_infinitePlace_eq_prod_embeddings {K : Type*} [Field K] [NumberField K]
    {ι : Type*} [Fintype ι] (x : ι → K) :
    (∏ v : NumberField.InfinitePlace K, (⨆ i, v (x i)) ^ v.mult)
      = ∏ φ : K →+* ℂ, ⨆ i, ‖φ (x i)‖ := by
  classical
  -- Rewrite the product over all complex embeddings as a product over the fibres of
  -- `NumberField.InfinitePlace.mk`.
  rw [← Finset.prod_fiberwise (s := Finset.univ)
        (g := fun φ : K →+* ℂ => NumberField.InfinitePlace.mk φ)
        (f := fun φ : K →+* ℂ => ⨆ i, ‖φ (x i)‖)]
  apply Finset.prod_congr rfl
  intro w _
  -- On the fibre of a place `w`, all embeddings give the same value `⨆ i, w (x i)`.
  have hfiber : ∀ φ ∈ Finset.univ.filter
        (fun φ : K →+* ℂ => NumberField.InfinitePlace.mk φ = w),
      (⨆ i, ‖φ (x i)‖) = (⨆ i, w (x i)) := by
    intro φ hφ
    rw [Finset.mem_filter] at hφ
    apply iSup_congr
    intro i
    rw [← NumberField.InfinitePlace.apply φ (x i), hφ.2]
  -- The fibre is constant, and its cardinality is the multiplicity `w.mult`.
  rw [Finset.prod_congr rfl hfiber, Finset.prod_const,
    NumberField.InfinitePlace.card_filter_mk_eq]

end Work.WilkiesH.Norm
