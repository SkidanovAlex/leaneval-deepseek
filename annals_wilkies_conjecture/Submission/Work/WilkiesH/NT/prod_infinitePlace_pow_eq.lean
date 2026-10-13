import Mathlib
import Submission.Work.WilkiesH.Norm.prod_infinitePlace_eq_prod_embeddings

namespace Work.WilkiesH.NT

open scoped Classical

/-- The archimedean part of the height, written with `max _ 1`, computed as a product over
the infinite places weighted by their multiplicity, equals the same quantity computed as a
product over all complex embeddings.

This is the `max _ 1` variant of `Work.WilkiesH.Norm.prod_infinitePlace_eq_prod_embeddings`; it
follows from it by grouping the complex embeddings into the fibres of `InfinitePlace.mk` and
using that each fibre has cardinality `w.mult`. -/
theorem prod_max_eq_prod_embeddings {K : Type*} [Field K] [NumberField K] (x : K) :
    (∏ w : NumberField.InfinitePlace K, max (w x) 1 ^ w.mult)
      = ∏ φ : K →+* ℂ, max ‖φ x‖ 1 := by
  classical
  rw [← Finset.prod_fiberwise (s := Finset.univ)
        (g := fun φ : K →+* ℂ => NumberField.InfinitePlace.mk φ)
        (f := fun φ : K →+* ℂ => max ‖φ x‖ 1)]
  apply Finset.prod_congr rfl
  intro w _
  -- on the fibre of `w` all embeddings take the same value `w x`
  have hfiber : ∀ φ ∈ Finset.univ.filter
        (fun φ : K →+* ℂ => NumberField.InfinitePlace.mk φ = w),
      max ‖φ x‖ 1 = max (w x) 1 := by
    intro φ hφ
    rw [Finset.mem_filter] at hφ
    rw [← hφ.2]
    simp
  rw [Finset.prod_congr rfl hfiber, Finset.prod_const,
    NumberField.InfinitePlace.card_filter_mk_eq]

/-- The fibre of the restriction map `φ ↦ φ ∘ (F ↪ K)` on complex embeddings of `K`, above a
fixed complex embedding `ψ` of `F`, has cardinality `[K : F]`.

The fibre is exactly the set of `F`-algebra homomorphisms `K → ℂ` for the `F`-algebra structure
on `ℂ` induced by `ψ`, and the cardinality of that set is `finrank ↥F K` by `AlgHom.card`. -/
theorem card_fiber_comp {K : Type*} [Field K] [NumberField K] (F : IntermediateField ℚ K)
    (ψ : ↥F →+* ℂ) :
    (Finset.univ.filter (fun φ : K →+* ℂ => φ.comp (algebraMap ↥F K) = ψ)).card
      = Module.finrank ↥F K := by
  classical
  rw [← Fintype.card_subtype]
  letI : Algebra ↥F ℂ := ψ.toAlgebra
  let toF : {φ : K →+* ℂ // φ.comp (algebraMap ↥F K) = ψ} → (K →ₐ[↥F] ℂ) :=
    fun φ => AlgHom.mk φ.1 (fun a => by
      rw [RingHom.algebraMap_toAlgebra]
      exact RingHom.congr_fun φ.2 a)
  let invF : (K →ₐ[↥F] ℂ) → {φ : K →+* ℂ // φ.comp (algebraMap ↥F K) = ψ} :=
    fun f => ⟨f.toRingHom, by ext a; exact f.commutes a⟩
  have hl : Function.LeftInverse invF toF := fun φ => by ext a; rfl
  have hr : Function.RightInverse invF toF := fun f => by ext a; rfl
  let e : {φ : K →+* ℂ // φ.comp (algebraMap ↥F K) = ψ} ≃ (K →ₐ[↥F] ℂ) := ⟨toF, invF, hl, hr⟩
  rw [Fintype.card_congr e, AlgHom.card ↥F K ℂ]

/-- Grouping the complex embeddings of `K` by their restriction to `F`, each fibre having
cardinality `[K : F]`, the product over the embeddings of `K` of `max ‖φ z‖ 1` (for `z ∈ F`)
is the `[K : F]`-th power of the corresponding product over the embeddings of `F`. -/
theorem prod_comp_eq_pow {K : Type*} [Field K] [NumberField K] (F : IntermediateField ℚ K)
    (z : ↥F) :
    (∏ φ : K →+* ℂ, max ‖φ (z : K)‖ 1)
      = (∏ ψ : ↥F →+* ℂ, max ‖ψ z‖ 1) ^ Module.finrank ↥F K := by
  classical
  have hcard : ∀ ψ : ↥F →+* ℂ,
      (Finset.univ.filter (fun φ : K →+* ℂ => φ.comp (algebraMap ↥F K) = ψ)).card
        = Module.finrank ↥F K := fun ψ => card_fiber_comp F ψ
  rw [← Finset.prod_fiberwise (s := Finset.univ)
        (g := fun φ : K →+* ℂ => φ.comp (algebraMap ↥F K))
        (f := fun φ : K →+* ℂ => max ‖φ (z : K)‖ 1)]
  rw [← Finset.prod_pow]
  apply Finset.prod_congr rfl
  intro ψ _
  have hfib : ∀ φ ∈ Finset.univ.filter
      (fun φ : K →+* ℂ => φ.comp (algebraMap ↥F K) = ψ), max ‖φ (z : K)‖ 1 = max ‖ψ z‖ 1 := by
    intro φ hφ
    rw [Finset.mem_filter] at hφ
    have h2 : φ (z : K) = ψ z := RingHom.congr_fun hφ.2 z
    rw [h2]
  rw [Finset.prod_congr rfl hfib, Finset.prod_const, hcard ψ]

theorem prod_infinitePlace_pow_eq {K : Type*} [Field K] [NumberField K]
    (F : IntermediateField ℚ K) (z : ↥F) :
    (∏ w : NumberField.InfinitePlace K, max (w (z : K)) 1 ^ w.mult)
      = (∏ v : NumberField.InfinitePlace ↥F, max (v z) 1 ^ v.mult) ^ Module.finrank ↥F K := by
  rw [prod_max_eq_prod_embeddings (K := K) (z : K),
      prod_max_eq_prod_embeddings (K := ↥F) z, prod_comp_eq_pow F z]

end Work.WilkiesH.NT
