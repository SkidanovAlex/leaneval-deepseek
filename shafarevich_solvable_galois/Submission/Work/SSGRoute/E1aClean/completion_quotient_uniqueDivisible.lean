import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Submission.Work.SSGRoute.E1aClean.adicCompletion_units_eq_baseUnits_mul_pow
import Submission.Work.SSGRoute.ExtChain.decompField_aux
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute.E1aClean

open scoped NumberField
open NumberField

/-- If `φ : E →+* L` has relatively algebraically closed image in `L` and `K` is a finite
extension of `ℚ` mapping into `L`, then the image of `K` lies in the range of `φ`.  Indeed the
elements of `K` are algebraic over `ℚ ⊆ range φ`. -/
lemma algebraMap_mem_range_of_relAlgClosed {E K L : Type} [Field E] [Field K] [Field L]
    [Algebra ℚ K] [Algebra ℚ L] [Algebra ℚ E] [Module.Finite ℚ K] [Algebra K L]
    (φ : E →+* L)
    (halg : ∀ z : L, (∃ r : Polynomial E, r ≠ 0 ∧ Polynomial.eval₂ φ z r = 0) →
      ∃ x : E, φ x = z)
    (x : K) : ∃ y : E, φ y = algebraMap K L x := by
  have hxint : IsIntegral ℚ x := Algebra.IsIntegral.isIntegral x
  -- both `φ ∘ algebraMap ℚ E` and `algebraMap ℚ L` are ring homs `ℚ →+* L`
  have hcompφ : φ.comp (algebraMap ℚ E) = algebraMap ℚ L := Subsingleton.elim _ _
  have hcompKL : (algebraMap K L).comp (algebraMap ℚ K) = algebraMap ℚ L := Subsingleton.elim _ _
  -- the structure map of `K` commutes with evaluation of rational polynomials
  have key : ∀ p : Polynomial ℚ,
      Polynomial.eval₂ (algebraMap ℚ L) (algebraMap K L x) p
        = algebraMap K L (Polynomial.eval₂ (algebraMap ℚ K) x p) := by
    intro p
    rw [← hcompKL, ← Polynomial.eval₂_map, Polynomial.eval₂_hom, Polynomial.eval_map]
  refine halg (algebraMap K L x) ⟨(minpoly ℚ x).map (algebraMap ℚ E), ?_, ?_⟩
  · rw [Polynomial.map_ne_zero_iff (algebraMap ℚ E).injective]
    exact minpoly.ne_zero hxint
  · rw [Polynomial.eval₂_map, hcompφ]
    rw [key, ← Polynomial.aeval_def, minpoly.aeval, map_zero]

/-- Units version of `algebraMap_mem_range_of_relAlgClosed`. -/
lemma exists_unit_preimage_algebraMap {E K L : Type} [Field E] [Field K] [Field L]
    [Algebra ℚ K] [Algebra ℚ L] [Algebra ℚ E] [Module.Finite ℚ K] [Algebra K L]
    (φ : E →+* L)
    (halg : ∀ z : L, (∃ r : Polynomial E, r ≠ 0 ∧ Polynomial.eval₂ φ z r = 0) →
      ∃ x : E, φ x = z)
    (k : Kˣ) : ∃ u : Eˣ, Units.map φ.toMonoidHom u = Units.map (algebraMap K L).toMonoidHom k := by
  obtain ⟨y, hy⟩ := algebraMap_mem_range_of_relAlgClosed (L := L) φ halg (k : K)
  have hy0 : y ≠ 0 := by
    intro h0
    rw [h0, map_zero] at hy
    exact (Units.ne_zero (Units.map (algebraMap K L).toMonoidHom k)) (by simpa using hy.symm)
  refine ⟨Units.mk0 y hy0, ?_⟩
  ext
  simpa using hy

theorem completion_quotient_uniqueDivisible (k Ω : Type) [Field k] [NumberField k] [Field Ω]
    [Algebra k Ω] [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K]
    [IsGalois k K] [NumberField K] (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A)
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (φ : ↥(IntermediateField.fixedField (SSGRoute.decomp k A ⊓ (SSGRoute.res k K).ker)) →+*
        (NK.GlobalCFT.Place.localField K (NK.GlobalCFT.Place.ofFinite q)))
    (hφ : Function.Injective φ)
    (halg : ∀ z : NK.GlobalCFT.Place.localField K (NK.GlobalCFT.Place.ofFinite q),
      (∃ r : Polynomial ↥(IntermediateField.fixedField
            (SSGRoute.decomp k A ⊓ (SSGRoute.res k K).ker)),
          r ≠ 0 ∧ Polynomial.eval₂ φ z r = 0) →
        ∃ x : ↥(IntermediateField.fixedField (SSGRoute.decomp k A ⊓ (SSGRoute.res k K).ker)),
          φ x = z) :
    (∀ n : ℕ, 0 < n → ∀ z : (NK.GlobalCFT.Place.localField K
          (NK.GlobalCFT.Place.ofFinite q))ˣ,
      ∃ (w : (NK.GlobalCFT.Place.localField K (NK.GlobalCFT.Place.ofFinite q))ˣ)
        (u : (↥(IntermediateField.fixedField (SSGRoute.decomp k A ⊓ (SSGRoute.res k K).ker)))ˣ),
        z = Units.map φ.toMonoidHom u * w ^ n) ∧
    (∀ n : ℕ, 0 < n → ∀ (z : (NK.GlobalCFT.Place.localField K
          (NK.GlobalCFT.Place.ofFinite q))ˣ)
        (u : (↥(IntermediateField.fixedField (SSGRoute.decomp k A ⊓ (SSGRoute.res k K).ker)))ˣ),
      z ^ n = Units.map φ.toMonoidHom u →
        ∃ u' : (↥(IntermediateField.fixedField (SSGRoute.decomp k A ⊓ (SSGRoute.res k K).ker)))ˣ,
          z = Units.map φ.toMonoidHom u') := by
  classical
  refine ⟨?_, ?_⟩
  · -- Divisibility: `Kˣ · (K_qˣ)ⁿ = K_qˣ`, and `Kˣ ⊆ range φ`.
    intro n hn z
    obtain ⟨k, w, hw⟩ := adicCompletion_units_eq_baseUnits_mul_pow (K := ↥K) q n hn z
    obtain ⟨u, hu⟩ := exists_unit_preimage_algebraMap (K := ↥K)
      (L := NK.GlobalCFT.Place.localField K (NK.GlobalCFT.Place.ofFinite q)) φ halg k
    refine ⟨w, u, ?_⟩
    rw [hu]
    exact hw.symm
  · -- Purity: if `z ^ n` lies in the range of `φ`, then `z` does, by relative algebraic closedness.
    intro n hn z u hzu
    have hval : (z : NK.GlobalCFT.Place.localField K (NK.GlobalCFT.Place.ofFinite q)) ^ n
        = φ (u : ↥(IntermediateField.fixedField
            (SSGRoute.decomp k A ⊓ (SSGRoute.res k K).ker))) := by
      have h := congrArg Units.val hzu
      simpa using h
    have hpoly : Polynomial.eval₂ φ
        (z : NK.GlobalCFT.Place.localField K (NK.GlobalCFT.Place.ofFinite q))
        (Polynomial.X ^ n - Polynomial.C (u : ↥(IntermediateField.fixedField
            (SSGRoute.decomp k A ⊓ (SSGRoute.res k K).ker)))) = 0 := by
      rw [Polynomial.eval₂_sub, Polynomial.eval₂_pow, Polynomial.eval₂_X, Polynomial.eval₂_C, hval,
        sub_self]
    have hP0 : Polynomial.X ^ n - Polynomial.C (u : ↥(IntermediateField.fixedField
          (SSGRoute.decomp k A ⊓ (SSGRoute.res k K).ker))) ≠ 0 := by
      have hc : (Polynomial.X ^ n - Polynomial.C (u : ↥(IntermediateField.fixedField
            (SSGRoute.decomp k A ⊓ (SSGRoute.res k K).ker)))).coeff n = 1 := by
        rw [Polynomial.coeff_sub, Polynomial.coeff_X_pow_self, Polynomial.coeff_C, if_neg hn.ne',
          sub_zero]
      intro h
      rw [h, Polynomial.coeff_zero] at hc
      exact one_ne_zero hc.symm
    obtain ⟨y, hy⟩ := halg (z : NK.GlobalCFT.Place.localField K (NK.GlobalCFT.Place.ofFinite q))
      ⟨_, hP0, hpoly⟩
    have hy0 : y ≠ 0 := by
      intro h0
      rw [h0, map_zero] at hy
      exact Units.ne_zero z hy.symm
    exact ⟨Units.mk0 y hy0, by
      refine Units.ext ?_
      simpa using hy.symm⟩

end Work.SSGRoute.E1aClean
