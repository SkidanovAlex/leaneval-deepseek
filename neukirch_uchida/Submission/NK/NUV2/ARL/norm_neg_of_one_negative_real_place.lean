import Mathlib

/-!
# The sign of the norm of an element of a number field with a prescribed sign pattern

If `a ≠ 0` in a number field `K` is negative at exactly one real place `w₀` and positive at every
other real place, then `Algebra.norm ℚ a < 0`.

The norm is the product of the images of `a` under all complex embeddings: the non-real embeddings
come in conjugate pairs and contribute the positive factors `‖φ a‖²`, while the real embeddings
contribute their (real) values, exactly one of which is negative.

This is the companion of `NK.CFTLib.ARL.norm_pos_of_totallyPositive` (the totally positive case)
and is the arithmetic input isolated in
`Submission/Work/NUV2/ARL/NOTES_unifUnit_pow_mem_localNormSubgroup.md` for step L3 (real place) of
the Hilbert-reciprocity design.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open scoped NumberField
open NumberField

noncomputable section

namespace NK.NUV2.ARL

private lemma list_prod_map_eq_finset_prod {α β : Type*} [CommMonoid β] (s : Finset α)
    (f : α → β) : (s.toList.map f).prod = ∏ x ∈ s, f x := by
  rw [← Multiset.prod_coe, ← Multiset.map_coe, Finset.coe_toList, Finset.prod_eq_multiset_prod]

/-- **The sign of the norm.**  An element of a number field which is negative at exactly one real
place `w₀` and positive at all the other real places has negative norm. -/
theorem norm_lt_zero_of_neg_at_one_real_place {K : Type*} [Field K] [NumberField K] (a : K)
    (ha : a ≠ 0) (w₀ : InfinitePlace K) (hw₀ : w₀.IsReal)
    (hneg : (InfinitePlace.embedding_of_isReal hw₀) a < 0)
    (hpos : ∀ (w : InfinitePlace K) (hw : w.IsReal), w ≠ w₀ →
      0 < (InfinitePlace.embedding_of_isReal hw) a) :
    Algebra.norm ℚ a < 0 := by
  classical
  have hne : ∀ φ : K →+* ℂ, φ a ≠ 0 := fun φ => by
    simpa using (RingHom.injective φ).ne ha
  have hnorm : algebraMap ℚ ℂ (Algebra.norm ℚ a) = ∏ φ : K →+* ℂ, φ a := by
    rw [Algebra.norm_eq_prod_embeddings ℚ ℂ a]
    refine Fintype.prod_equiv ((RingHom.equivRatAlgHom K ℂ).symm) (fun σ : K →ₐ[ℚ] ℂ => σ a)
      (fun φ : K →+* ℂ => φ a) (fun σ => ?_)
    simp
  -- the "unit part" of each factor
  let u : (K →+* ℂ) → ℂ := fun φ => φ a / ((‖φ a‖ : ℝ) : ℂ)
  -- the non-real embeddings pair up under complex conjugation and contribute `1`
  have hT : (∏ φ ∈ Finset.univ.filter (fun φ : K →+* ℂ => ¬ ComplexEmbedding.IsReal φ),
      u φ) = 1 := by
    refine Finset.prod_involution
      (fun φ _ => NumberField.ComplexEmbedding.conjugate φ) ?_ ?_ ?_ ?_
    · intro φ hφ
      show φ a / ↑‖φ a‖ * ((NumberField.ComplexEmbedding.conjugate φ) a /
        ↑‖(NumberField.ComplexEmbedding.conjugate φ) a‖) = 1
      have hz : ((‖φ a‖ : ℝ) : ℂ) ≠ 0 :=
        Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr (hne φ))
      have hn : ‖(starRingEnd ℂ) (φ a)‖ = ‖φ a‖ := Complex.norm_conj _
      rw [NumberField.ComplexEmbedding.conjugate_coe_eq, hn]
      field_simp
      rw [starRingEnd_apply, Complex.star_def, Complex.mul_conj']
    · intro φ hφ h
      rw [Finset.mem_filter] at hφ
      intro hc
      exact hφ.2 (NumberField.ComplexEmbedding.isReal_iff.mpr hc)
    · intro φ hφ
      rw [Finset.mem_filter] at hφ
      rw [Finset.mem_filter]
      exact ⟨Finset.mem_univ _,
        fun h => hφ.2 (NumberField.ComplexEmbedding.isReal_conjugate_iff.mp h)⟩
    · intro φ hφ
      exact NumberField.ComplexEmbedding.involutive_conjugate K φ
  -- the real embeddings contribute `±1` according to the sign of their value at `a`
  have hR : (∏ φ ∈ Finset.univ.filter (fun φ : K →+* ℂ => ComplexEmbedding.IsReal φ), u φ) =
      (∏ φ ∈ Finset.univ.filter (fun φ : K →+* ℂ => ComplexEmbedding.IsReal φ),
        (if 0 < (φ a).re then (1 : ℂ) else -1)) := by
    refine Finset.prod_congr rfl (fun φ hφ => ?_)
    rw [Finset.mem_filter] at hφ
    obtain ⟨-, hφr⟩ := hφ
    have him : (φ a).im = 0 := by
      refine Complex.conj_eq_iff_im.mp ?_
      rw [← NumberField.ComplexEmbedding.conjugate_coe_eq,
        NumberField.ComplexEmbedding.isReal_iff.mp hφr]
    have hre : (((φ a).re : ℝ) : ℂ) = φ a := by
      rw [← Complex.re_add_im (φ a), him]
      simp
    set t : ℝ := (φ a).re with ht
    have ht0 : t ≠ 0 := by
      intro h0
      exact hne φ (by rw [← hre, h0]; simp)
    have hnormt : ‖(((t : ℝ) : ℂ))‖ = |t| := by
      simpa using RCLike.norm_ofReal (K := ℂ) t
    have hval : t / |t| = if 0 < t then (1 : ℝ) else -1 := by
      rcases lt_or_gt_of_ne ht0 with hlt | hgt
      · rw [if_neg (not_lt.mpr (le_of_lt hlt)), abs_of_neg hlt, div_neg,
          div_self (ne_of_lt hlt)]
      · rw [if_pos hgt, abs_of_pos hgt, div_self (ne_of_gt hgt)]
    have h1 : u φ = ((t : ℝ) : ℂ) / ((|t| : ℝ) : ℂ) := by
      show φ a / ((‖φ a‖ : ℝ) : ℂ) = ((t : ℝ) : ℂ) / ((|t| : ℝ) : ℂ)
      rw [hre.symm, hnormt]
    have h2 : ((t / |t| : ℝ) : ℂ) = (if 0 < t then (1 : ℂ) else -1) := by
      rw [hval]
      by_cases h : 0 < t <;> simp [h]
    rw [h1, ← Complex.ofReal_div]
    exact h2
  -- exactly one real embedding is negative: `w₀.embedding`
  have hsign : (∏ φ ∈ Finset.univ.filter (fun φ : K →+* ℂ => ComplexEmbedding.IsReal φ),
        (if 0 < (φ a).re then (1 : ℂ) else -1)) = -1 := by
    have hw₀real : ComplexEmbedding.IsReal w₀.embedding := (InfinitePlace.isReal_iff).mp hw₀
    have hw₀mem : w₀.embedding ∈ Finset.univ.filter
        (fun φ : K →+* ℂ => ComplexEmbedding.IsReal φ) := by
      rw [Finset.mem_filter]; exact ⟨Finset.mem_univ _, hw₀real⟩
    have hw₀neg : ¬ (0 < (w₀.embedding a).re) := by
      have h1 : ((w₀.embedding) a).re = (InfinitePlace.embedding_of_isReal hw₀) a := by
        have h2 := InfinitePlace.embedding_of_isReal_apply hw₀ a
        exact (congrArg Complex.re h2).symm.trans
          (Complex.ofReal_re ((InfinitePlace.embedding_of_isReal hw₀) a))
      rw [h1]
      exact not_lt.mpr (le_of_lt hneg)
    have hsingle : (∏ φ ∈ Finset.univ.filter (fun φ : K →+* ℂ => ComplexEmbedding.IsReal φ),
        (if 0 < (φ a).re then (1 : ℂ) else -1)) =
        (if 0 < (w₀.embedding a).re then (1 : ℂ) else -1) := by
      refine Finset.prod_eq_single (w₀.embedding) ?_ (fun hnot => absurd hw₀mem hnot)
      intro φ hφ hne'
      rw [Finset.mem_filter] at hφ
      obtain ⟨-, hφr⟩ := hφ
      have him : (φ a).im = 0 := by
        refine Complex.conj_eq_iff_im.mp ?_
        rw [← NumberField.ComplexEmbedding.conjugate_coe_eq,
          NumberField.ComplexEmbedding.isReal_iff.mp hφr]
      have hre : (((φ a).re : ℝ) : ℂ) = φ a := by
        rw [← Complex.re_add_im (φ a), him]
        simp
      rw [if_pos]
      by_contra hle
      push_neg at hle
      have hne0 : (φ a).re ≠ 0 := by
        intro h0
        exact hne φ (by rw [← hre, h0]; simp)
      have hlt : (φ a).re < 0 := lt_of_le_of_ne hle hne0
      have hreal : (InfinitePlace.mk φ).IsReal := (InfinitePlace.isReal_mk_iff).mpr hφr
      have hval : (InfinitePlace.embedding_of_isReal hreal) a = (φ a).re := by
        have h1 : ((InfinitePlace.embedding_of_isReal hreal) a : ℂ) = φ a := by
          have h2 := InfinitePlace.embedding_of_isReal_apply hreal a
          rw [InfinitePlace.embedding_mk_eq_of_isReal hφr] at h2
          exact h2
        exact Complex.ofReal_injective (by rw [h1]; exact hre.symm)
      have hplace : InfinitePlace.mk φ = w₀ := by
        by_contra hne''
        have h2 := hpos (InfinitePlace.mk φ) hreal hne''
        rw [hval] at h2
        exact absurd h2 (not_lt.mpr (le_of_lt hlt))
      refine hne' ?_
      have h2 := InfinitePlace.embedding_mk_eq_of_isReal hφr
      rw [hplace] at h2
      exact h2.symm
    rw [hsingle, if_neg hw₀neg]
  -- the "unit part" over all embeddings is `-1`
  have hu : (∏ φ : K →+* ℂ, u φ) = -1 := by
    rw [← Finset.prod_filter_mul_prod_filter_not Finset.univ
      (fun φ : K →+* ℂ => ComplexEmbedding.IsReal φ) u, hR, hsign, hT, mul_one]
  -- the product of the embeddings is `-(∏ ‖φ a‖)`
  have hP : (∏ φ : K →+* ℂ, φ a) = -(((∏ φ : K →+* ℂ, ‖φ a‖ : ℝ) : ℂ)) := by
    have h1 : ∀ φ : K →+* ℂ, φ a = u φ * ((‖φ a‖ : ℝ) : ℂ) := by
      intro φ
      have hz : ((‖φ a‖ : ℝ) : ℂ) ≠ 0 :=
        Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr (hne φ))
      show φ a = φ a / ((‖φ a‖ : ℝ) : ℂ) * ((‖φ a‖ : ℝ) : ℂ)
      field_simp
    calc (∏ φ : K →+* ℂ, φ a)
        = ∏ φ : K →+* ℂ, u φ * ((‖φ a‖ : ℝ) : ℂ) :=
          Finset.prod_congr rfl (fun φ _ => h1 φ)
      _ = (∏ φ : K →+* ℂ, u φ) * ∏ φ : K →+* ℂ, ((‖φ a‖ : ℝ) : ℂ) :=
          Finset.prod_mul_distrib
      _ = -(((∏ φ : K →+* ℂ, ‖φ a‖ : ℝ) : ℂ)) := by
          rw [hu, neg_mul, one_mul]
          congr 1
          exact (map_prod Complex.ofRealHom (fun φ : K →+* ℂ => ‖φ a‖) Finset.univ).symm
  have hprod : 0 < (∏ φ : K →+* ℂ, ‖φ a‖ : ℝ) :=
    Finset.prod_pos (fun φ _ => norm_pos_iff.mpr (hne φ))
  -- conclude
  have h3 : ((Algebra.norm ℚ a : ℚ) : ℝ) = -(∏ φ : K →+* ℂ, ‖φ a‖ : ℝ) := by
    have h4 : algebraMap ℚ ℂ (Algebra.norm ℚ a) = -(((∏ φ : K →+* ℂ, ‖φ a‖ : ℝ) : ℂ)) :=
      hnorm.trans hP
    have h5 : (((Algebra.norm ℚ a : ℚ) : ℝ) : ℂ) =
        (((-(∏ φ : K →+* ℂ, ‖φ a‖ : ℝ) : ℝ)) : ℂ) := by
      rw [Complex.ofReal_neg, Complex.ofReal_ratCast]
      exact h4
    exact Complex.ofReal_injective h5
  have hlt : ((Algebra.norm ℚ a : ℚ) : ℝ) < 0 := by
    rw [h3]
    linarith
  exact_mod_cast hlt

end NK.NUV2.ARL
