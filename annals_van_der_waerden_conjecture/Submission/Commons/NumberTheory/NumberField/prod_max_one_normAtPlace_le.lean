import Mathlib.Analysis.Polynomial.MahlerMeasure
import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.Basic
import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.SimpleRing.Principal
import Submission.Commons.NumberTheory.NumberField.abs_norm_eq_abs_coeff_zero_minpoly

namespace Commons.NumberTheory.NumberField

open Polynomial
open scoped Classical IntermediateField

/-- The product over the infinite places `w` of `K` of `(max 1 (w x)) ^ w.mult` equals the
product over all complex embeddings `σ` of `K` of `max 1 ‖σ x‖`.

This is because the complex embeddings are partitioned into the fibers of `σ ↦ InfinitePlace.mk σ`,
each fiber has cardinality `w.mult` and on each fiber `‖σ x‖ = w x`. -/
private theorem prod_max_one_place_eq_prod_embeddings {K : Type*} [Field K] [NumberField K]
    (x : K) :
    (∏ w : NumberField.InfinitePlace K, (max 1 (w x)) ^ w.mult)
      = ∏ σ : K →+* ℂ, max 1 ‖σ x‖ := by
  classical
  rw [← Finset.prod_fiberwise Finset.univ (fun σ : K →+* ℂ => NumberField.InfinitePlace.mk σ)
        (fun σ => max 1 ‖σ x‖)]
  refine Finset.prod_congr rfl (fun w _ => ?_)
  rw [Finset.prod_congr rfl (fun σ (hσ : σ ∈ Finset.univ.filter
        (fun σ : K →+* ℂ => NumberField.InfinitePlace.mk σ = w)) => ?_),
      Finset.prod_const]
  · rw [NumberField.InfinitePlace.card_filter_mk_eq]
  · have h : NumberField.InfinitePlace.mk σ = w := (Finset.mem_filter.mp hσ).2
    rw [← h, NumberField.InfinitePlace.apply]

/-- The Mahler measure of the minimal polynomial of `α` (viewed over `ℂ`) equals the product over
all complex embeddings `σ` of `max 1 ‖σ α‖`. -/
private theorem mahlerMeasure_map_minpoly_eq_prod_embeddings {K : Type*} [Field K] [NumberField K]
    {α : K} (hgen : Algebra.adjoin ℚ ({α} : Set K) = ⊤) (hint : IsIntegral ℤ α) :
    ((minpoly ℤ α).map (Int.castRingHom ℂ)).mahlerMeasure
      = ∏ σ : K →+* ℂ, max 1 ‖σ α‖ := by
  classical
  have hinj : Function.Injective (fun σ : K →+* ℂ => σ α) := by
    have hgenIF : ℚ⟮α⟯ = ⊤ := by
      have h : (IntermediateField.adjoin ℚ ({α} : Set K)).toSubalgebra =
          (⊤ : IntermediateField ℚ K).toSubalgebra := by
        rw [IntermediateField.adjoin_toSubalgebra, hgen]
        rfl
      exact IntermediateField.toSubalgebra_inj.mp h
    have hIFinj : Function.Injective (fun φ : K →ₐ[ℚ] ℂ => φ α) :=
      (Field.primitive_element_iff_algHom_eq_of_eval' ℚ ℂ
        (fun x => IsAlgClosed.splits _) α).mp hgenIF
    intro σ ψ h
    apply (RingHom.equivRatAlgHom K ℂ).injective
    apply hIFinj
    simpa using h
  set f : ℂ[X] := (minpoly ℤ α).map (Int.castRingHom ℂ) with hf
  set Q : ℂ[X] := (minpoly ℚ α).map (algebraMap ℚ ℂ) with hQ
  have hfQ : f = Q := by
    have hcomp : (algebraMap ℚ ℂ).comp (algebraMap ℤ ℚ) = Int.castRingHom ℂ :=
      RingHom.ext_int _ _
    rw [hf, hQ, minpoly.isIntegrallyClosed_eq_field_fractions' (R:=ℤ) (K:=ℚ) (S:=K) hint,
        Polynomial.map_map, hcomp]
  have hfmonic : f.Monic := (minpoly.monic hint).map _
  have hfne : f ≠ 0 := hfmonic.ne_zero
  have hQne : Q ≠ 0 := hfQ ▸ hfne
  have hQsep : Q.Separable := by
    rw [hQ]
    exact Polynomial.Separable.map (Algebra.IsSeparable.isSeparable ℚ α)
  have hnodup : f.roots.Nodup := by
    rw [hfQ]
    exact Polynomial.nodup_roots hQsep
  set S : Finset ℂ := Finset.univ.image (fun σ : K →+* ℂ => σ α) with hS
  have hSval : f.roots = S.val := by
    refine (Multiset.Nodup.ext hnodup S.nodup).mpr (fun a => ?_)
    rw [hfQ]
    show a ∈ Q.roots ↔ a ∈ S
    rw [Polynomial.mem_roots hQne, Polynomial.IsRoot.def, hQ]
    rw [Polynomial.eval_map, ← Polynomial.aeval_def]
    rw [← Polynomial.mem_rootSet_of_ne (show minpoly ℚ α ≠ 0 from minpoly.ne_zero_of_finite ℚ α)]
    rw [← NumberField.Embeddings.range_eval_eq_rootSet_minpoly K ℂ α]
    rw [hS, Finset.mem_image]
    simp only [Set.mem_range, Finset.mem_univ, true_and]
  rw [Polynomial.mahlerMeasure_eq_leadingCoeff_mul_prod_roots, hfmonic.leadingCoeff, norm_one,
      one_mul, hSval]
  have hinjOn : Set.InjOn (fun σ : K →+* ℂ => σ α) (↑(Finset.univ : Finset (K →+* ℂ))) := by
    intro a _ b _ h
    exact hinj h
  rw [show (Multiset.map (fun a => max 1 ‖a‖) S.val).prod = ∏ a ∈ S, max 1 ‖a‖ from rfl,
      hS, Finset.prod_image hinjOn]

/-- The product over the infinite places of `K` of `max 1 (w α) ^ w.mult` is bounded by
`sqrt ([K : ℚ] + 1) * B` whenever `B` bounds the absolute values of the coefficients of the
minimal polynomial of `α` over `ℤ`.

This is Landau's inequality applied to the minimal polynomial of `α`, together with the
identification of the product over the infinite places with the Mahler measure of that
polynomial. -/
theorem prod_max_one_normAtPlace_le {K : Type*} [Field K] [NumberField K] {α : K}
    (hgen : Algebra.adjoin ℚ ({α} : Set K) = ⊤) (hint : IsIntegral ℤ α) {B : ℝ}
    (hcoeff : ∀ i, |((((minpoly ℤ α).coeff i : ℤ)) : ℝ)| ≤ B) :
    (∏ w : NumberField.InfinitePlace K,
        (max 1 (NumberField.mixedEmbedding.normAtPlace w
          (NumberField.mixedEmbedding K α))) ^ w.mult)
      ≤ Real.sqrt (Module.finrank ℚ K + 1) * B := by
  classical
  set f : ℂ[X] := (minpoly ℤ α).map (Int.castRingHom ℂ) with hf
  have hfsup : f.supNorm ≤ B := by
    rw [Polynomial.supNorm_eq_iSup]
    refine ciSup_le (fun i => ?_)
    have h1 : f.coeff i = (((minpoly ℤ α).coeff i : ℤ) : ℂ) := by
      rw [hf, Polynomial.coeff_map]
      rfl
    rw [h1, Complex.norm_intCast]
    exact hcoeff i
  have hnat : f.natDegree = Module.finrank ℚ K := by
    have h1 : f.natDegree = (minpoly ℤ α).natDegree := by
      rw [hf]
      exact Polynomial.natDegree_map_eq_of_injective Int.cast_injective _
    have h2 : (minpoly ℤ α).natDegree = (minpoly ℚ α).natDegree := by
      rw [minpoly.isIntegrallyClosed_eq_field_fractions' (R:=ℤ) (K:=ℚ) (S:=K) hint]
      exact (Polynomial.natDegree_map_eq_of_injective
        (f := algebraMap ℤ ℚ) (Int.cast_injective) (minpoly ℤ α)).symm
    have h3 : (minpoly ℚ α).natDegree = Module.finrank ℚ K := by
      have hgenIF : ℚ⟮α⟯ = ⊤ := by
        have h : (IntermediateField.adjoin ℚ ({α} : Set K)).toSubalgebra =
            (⊤ : IntermediateField ℚ K).toSubalgebra := by
          rw [IntermediateField.adjoin_toSubalgebra, hgen]
          rfl
        exact IntermediateField.toSubalgebra_inj.mp h
      exact (Field.primitive_element_iff_minpoly_natDegree_eq ℚ α).mp hgenIF
    rw [h1, h2, h3]
  have hmm : f.mahlerMeasure = ∏ σ : K →+* ℂ, max 1 ‖σ α‖ := by
    rw [hf]
    exact mahlerMeasure_map_minpoly_eq_prod_embeddings hgen hint
  have hprod := prod_max_one_place_eq_prod_embeddings (K := K) α
  have hL := Polynomial.mahlerMeasure_le_sqrt_natDegree_add_one_mul_supNorm f
  calc
    (∏ w : NumberField.InfinitePlace K,
        (max 1 (NumberField.mixedEmbedding.normAtPlace w
          (NumberField.mixedEmbedding K α))) ^ w.mult)
        = ∏ σ : K →+* ℂ, max 1 ‖σ α‖ := by
          simp only [NumberField.mixedEmbedding.normAtPlace_apply]
          exact hprod
    _ = f.mahlerMeasure := hmm.symm
    _ ≤ Real.sqrt (Module.finrank ℚ K + 1) * B := by
          refine hL.trans ?_
          rw [hnat]
          exact mul_le_mul_of_nonneg_left hfsup (Real.sqrt_nonneg _)

end Commons.NumberTheory.NumberField