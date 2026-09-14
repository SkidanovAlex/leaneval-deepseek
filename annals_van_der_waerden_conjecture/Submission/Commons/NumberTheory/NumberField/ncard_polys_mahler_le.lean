import Mathlib
import Submission.Commons.NumberTheory.Height.NumberField.logHeight1_eq_sum_embeddings_log_max_of_isIntegral
import Submission.Commons.NumberTheory.Height.NumberField.mahlerMeasure_minpoly_int_eq_mulHeight1
import Submission.Commons.NumberTheory.NumberField.ncard_max_normAtPlace_le

open Polynomial
open scoped NumberField BigOperators

set_option linter.style.haveILetI false

namespace Commons.NumberTheory.NumberField

/-- For an algebraic integer `x`, the multiplicative height of `x` equals the product over the
infinite places of `max 1 (normAtPlace)` to the multiplicity. -/
lemma mulHeight₁_eq_prod_normAtPlace {K : Type*} [Field K] [NumberField K] {x : K}
    (hx : IsIntegral ℤ x) :
    Height.mulHeight₁ x =
      ∏ w : _root_.NumberField.InfinitePlace K,
        max 1 (_root_.NumberField.mixedEmbedding.normAtPlace w
          (_root_.NumberField.mixedEmbedding K x)) ^ w.mult := by
  have hpos : ∀ w : _root_.NumberField.InfinitePlace K,
      0 < max 1 (_root_.NumberField.mixedEmbedding.normAtPlace w
        (_root_.NumberField.mixedEmbedding K x)) ^ w.mult := by
    intro w
    have h1 : (0:ℝ) < max 1 (_root_.NumberField.mixedEmbedding.normAtPlace w
        (_root_.NumberField.mixedEmbedding K x)) := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
    positivity
  have key := Commons.NumberTheory.Height.NumberField.sum_embeddings_eq_sum_infinitePlace_mult
    (K := K) x (fun y : ℝ => Real.log (max 1 y))
  have hlog : Real.log (Height.mulHeight₁ x) = Real.log
      (∏ w : _root_.NumberField.InfinitePlace K,
        max 1 (_root_.NumberField.mixedEmbedding.normAtPlace w
          (_root_.NumberField.mixedEmbedding K x)) ^ w.mult) := by
    rw [← Height.logHeight₁_eq_log_mulHeight₁,
      Commons.NumberTheory.Height.NumberField.logHeight1_eq_sum_embeddings_log_max_of_isIntegral hx,
      key]
    rw [Real.log_prod]
    · refine Finset.sum_congr rfl (fun w _ => ?_)
      rw [Real.log_pow, _root_.NumberField.mixedEmbedding.normAtPlace_apply]
    · intro w _
      exact (hpos w).ne'
  exact Real.log_injOn_pos (Height.mulHeight₁_pos x)
    (Finset.prod_pos (fun w _ => hpos w)) hlog

/-- The image of the root of an `AdjoinRoot` under a `ℚ`-algebra equivalence generates the
target field. -/
lemma adjoin_root_algEquiv_eq_top {K : Type*} [Field K] [NumberField K] {g : ℚ[X]}
    (e : AdjoinRoot g ≃ₐ[ℚ] K) :
    Algebra.adjoin ℚ ({(e : AdjoinRoot g →ₐ[ℚ] K) (AdjoinRoot.root g)} : Set K) = ⊤ := by
  rw [← AlgHom.map_adjoin_singleton (e : AdjoinRoot g →ₐ[ℚ] K) (AdjoinRoot.root g),
    AdjoinRoot.adjoinRoot_eq_top, Algebra.map_top]
  refine eq_top_iff.mpr ?_
  intro x _
  obtain ⟨y, hy⟩ := e.surjective x
  exact ⟨y, hy⟩

/-- For `f ∈ S` there is an algebraic integer `α` with `minpoly ℚ α = f.map ℚ` and with
`mapMahlerMeasure f = mulHeight₁ α`. -/
lemma exists_ringOfIntegers_root_mahler {K : Type*} [Field K] [NumberField K]
    {Y : ℝ} {S : Set (Polynomial ℤ)}
    (hS : ∀ f ∈ S, Polynomial.Monic f ∧ Polynomial.natDegree f = Module.finrank ℚ K ∧
        Irreducible (Polynomial.map (algebraMap ℤ ℚ) f) ∧
        Nonempty (AdjoinRoot (Polynomial.map (algebraMap ℤ ℚ) f) ≃ₐ[ℚ] K) ∧
        Polynomial.mapMahlerMeasure f (Int.castRingHom ℂ) ≤ Y) :
    ∀ f : ↥S, ∃ α : NumberField.RingOfIntegers K,
      f.1.map (algebraMap ℤ ℚ) = minpoly ℚ (((α : NumberField.RingOfIntegers K) : K)) ∧
      Polynomial.mapMahlerMeasure f.1 (Int.castRingHom ℂ) =
        Height.mulHeight₁ (((α : NumberField.RingOfIntegers K) : K)) := by
  intro f
  obtain ⟨hmon, hdeg, hIrr, hne, hM⟩ := hS f.1 f.2
  obtain ⟨e⟩ := hne
  set r := AdjoinRoot.root (f.1.map (algebraMap ℤ ℚ)) with hr
  set αK : K := (e : AdjoinRoot (f.1.map (algebraMap ℤ ℚ)) →ₐ[ℚ] K) r with hαK
  have hrootg : (Polynomial.aeval r) (f.1.map (algebraMap ℤ ℚ)) = 0 := by
    rw [AdjoinRoot.aeval_eq]; exact AdjoinRoot.mk_self
  have hint_root : IsIntegral ℤ r := by
    refine IsIntegral.of_aeval_monic (p := f.1) hmon ?_ ?_
    · rw [hdeg]; exact (Module.finrank_pos (R := ℚ) (M := K)).ne'
    · rw [show (Polynomial.aeval r) f.1 = 0 from ?_]
      exact isIntegral_zero
      rw [← Polynomial.aeval_map_algebraMap (A := ℚ) r f.1]
      exact hrootg
  have hint : IsIntegral ℤ αK := by
    rw [hαK]
    exact IsIntegral.map (e : AdjoinRoot (f.1.map (algebraMap ℤ ℚ)) →ₐ[ℚ] K) hint_root
  have hroot' : (Polynomial.aeval αK) (f.1.map (algebraMap ℤ ℚ)) = 0 := by
    rw [hαK, Polynomial.aeval_algHom_apply, hrootg, map_zero]
  have hmin : f.1.map (algebraMap ℤ ℚ) = minpoly ℚ αK := by
    have h2 := minpoly.eq_of_irreducible hIrr hroot'
    have hgm : (f.1.map (algebraMap ℤ ℚ)).Monic := hmon.map _
    rw [← h2, hgm.leadingCoeff, inv_one, map_one, mul_one]
  have hgen : Algebra.adjoin ℚ ({αK} : Set K) = ⊤ := by
    rw [hαK]
    exact adjoin_root_algEquiv_eq_top e
  have hminZ : minpoly ℤ αK = f.1 := by
    have hmapZ : (minpoly ℤ αK).map (algebraMap ℤ ℚ) = minpoly ℚ αK :=
      (minpoly.isIntegrallyClosed_eq_field_fractions' (R := ℤ) (K := ℚ) (S := K) hint).symm
    refine Polynomial.map_injective (algebraMap ℤ ℚ) Int.cast_injective ?_
    rw [hmapZ, hmin]
  have hbridge : Polynomial.mapMahlerMeasure f.1 (Int.castRingHom ℂ) = Height.mulHeight₁ αK := by
    rw [← hminZ]
    exact Commons.NumberTheory.Height.NumberField.mahlerMeasure_minpoly_int_eq_mulHeight1 hint hgen
  exact ⟨⟨αK, hint⟩, hmin, hbridge⟩


theorem ncard_polys_mahler_le {K : Type*} [Field K] [NumberField K]
    (hn : 2 ≤ Module.finrank ℚ K) (Y lam : ℝ) (hY : 1 ≤ Y) (hlam : 1 ≤ lam)
    (hsep : ∀ α : NumberField.RingOfIntegers K, ((α : K)) ∉ Set.range (algebraMap ℤ K) →
      lam ≤ NumberField.house ((α : K)))
    (S : Set (Polynomial ℤ))
    (hS : ∀ f ∈ S, Polynomial.Monic f ∧ Polynomial.natDegree f = Module.finrank ℚ K ∧
        Irreducible (Polynomial.map (algebraMap ℤ ℚ) f) ∧
        Nonempty (AdjoinRoot (Polynomial.map (algebraMap ℤ ℚ) f) ≃ₐ[ℚ] K) ∧
        Polynomial.mapMahlerMeasure f (Int.castRingHom ℂ) ≤ Y) :
    (S.ncard : ℝ) ≤ (100000 : ℝ) ^ Module.finrank ℚ K * Y *
        (1 + Real.log Y) ^ (Module.finrank ℚ K - 1) / lam := by
  classical
  set A : Set (NumberField.RingOfIntegers K) := {α | ((α : K)) ∉ Set.range (algebraMap ℤ K) ∧
      (∏ w : _root_.NumberField.InfinitePlace K, max 1 (_root_.NumberField.mixedEmbedding.normAtPlace w
        (_root_.NumberField.mixedEmbedding K ((α : K)))) ^ w.mult) ≤ Y} with hAdef
  have hex := exists_ringOfIntegers_root_mahler (K := K) (Y := Y) hS
  have hex2 : ∀ f : ↥S, ∃ α : ↥A,
      f.1.map (algebraMap ℤ ℚ) = minpoly ℚ (((α : 𝓞 K) : K)) := by
    intro f
    obtain ⟨α, hmin, hbridge⟩ := hex f
    refine ⟨⟨α, ?_, ?_⟩, hmin⟩
    · intro hmem
      obtain ⟨m, hm⟩ := Set.mem_range.mp hmem
      have h1 : (minpoly ℚ (((α : 𝓞 K) : K))).natDegree = 1 := by
        have hthis : minpoly ℚ (((α : 𝓞 K) : K)) = Polynomial.X - Polynomial.C ((m : ℚ)) := by
          rw [← hm]
          rw [show (algebraMap ℤ K) m = algebraMap ℚ K (m : ℚ) from by
            rw [IsScalarTower.algebraMap_apply ℤ ℚ K m]; simp]
          exact minpoly.eq_X_sub_C_of_algebraMap_inj (m : ℚ) (algebraMap ℚ K).injective
        rw [hthis, natDegree_X_sub_C]
      have h2 : (minpoly ℚ (((α : 𝓞 K) : K))).natDegree = Module.finrank ℚ K := by
        rw [← hmin, (hS f.1 f.2).1.natDegree_map (algebraMap ℤ ℚ)]
        exact (hS f.1 f.2).2.1
      omega
    · rw [← mulHeight₁_eq_prod_normAtPlace (NumberField.RingOfIntegers.isIntegral_coe α), ← hbridge]
      exact (hS f.1 f.2).2.2.2.2
  let φ : ↥S → ↥A := fun f => (hex2 f).choose
  have hφ : ∀ f : ↥S, f.1.map (algebraMap ℤ ℚ) = minpoly ℚ ((((φ f : ↥A) : 𝓞 K) : K)) :=
    fun f => (hex2 f).choose_spec
  have hinj : Function.Injective φ := by
    intro f g hfg
    apply Subtype.ext
    have h1 := hφ f
    have h2 := hφ g
    rw [hfg] at h1
    exact Polynomial.map_injective (algebraMap ℤ ℚ) Int.cast_injective (h1.trans h2.symm)
  have hAfin : A.Finite := by
    rw [hAdef]
    refine Set.Finite.subset (Set.Finite.preimage (f := fun α : 𝓞 K => ((α : K)))
      ?_ (NumberField.finite_setOfPred_mulHeight₁_le K Y)) ?_
    · intro a _ b _ hab
      exact Subtype.coe_injective hab
    · intro α hα
      rw [Set.mem_preimage, Set.mem_ofPred_eq]
      rw [mulHeight₁_eq_prod_normAtPlace (NumberField.RingOfIntegers.isIntegral_coe α)]
      exact hα.2
  haveI : Finite ↥A := hAfin.to_subtype
  have hcore : (Nat.card ↥A : ℝ) ≤ (100000 : ℝ) ^ Module.finrank ℚ K * Y *
      (1 + Real.log Y) ^ (Module.finrank ℚ K - 1) / lam :=
    ncard_max_normAtPlace_le (K := K) hn Y lam hY hlam hsep
  rw [← Nat.card_coe_set_eq S]
  calc (Nat.card ↥S : ℝ) ≤ (Nat.card ↥A : ℝ) := by
        exact_mod_cast Nat.card_le_card_of_injective φ hinj
      _ ≤ _ := hcore

end Commons.NumberTheory.NumberField
