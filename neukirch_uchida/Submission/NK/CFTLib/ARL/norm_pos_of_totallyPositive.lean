import Mathlib

namespace NK.CFTLib.ARL

/-- The norm of a totally positive element of a number field is positive.

If every real embedding of `a` is positive, then so is its norm: the norm is the product of the
images of `a` under all complex embeddings, the non-real embeddings come in conjugate pairs and
contribute the positive factors `‖φ a‖²`, while the real embeddings contribute the (positive)
values of the real embeddings of `a`. -/
theorem norm_pos_of_totallyPositive {K : Type*} [Field K] [NumberField K] (a : K) (ha : a ≠ 0)
    (hpos : ∀ φ : K →+* ℝ, 0 < φ a) : 0 < Algebra.norm ℚ a := by
  classical
  -- `φ a ≠ 0` for every embedding `φ` of `K` into `ℂ`
  have hne : ∀ φ : K →+* ℂ, φ a ≠ 0 := fun φ => by
    simpa using (RingHom.injective φ).ne ha
  -- the norm is the product of the images of `a` under the embeddings into `ℂ`
  have hnorm : algebraMap ℚ ℂ (Algebra.norm ℚ a) = ∏ φ : K →+* ℂ, φ a := by
    rw [Algebra.norm_eq_prod_embeddings ℚ ℂ a]
    refine Fintype.prod_equiv ((RingHom.equivRatAlgHom K ℂ).symm) (fun σ : K →ₐ[ℚ] ℂ => σ a)
      (fun φ : K →+* ℂ => φ a) (fun σ => ?_)
    simp
  -- the "unit part" of each factor
  let u : (K →+* ℂ) → ℂ := fun φ => φ a / ((‖φ a‖ : ℝ) : ℂ)
  -- the non-real embeddings pair up under complex conjugation and the product of `u` over them
  -- is `1`
  have hT : (∏ φ ∈ Finset.univ.filter (fun φ : K →+* ℂ => ¬ NumberField.ComplexEmbedding.IsReal φ),
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
  -- the real embeddings contribute `1` to the unit part, by total positivity
  have hR : (∏ φ ∈ Finset.univ.filter (fun φ : K →+* ℂ => NumberField.ComplexEmbedding.IsReal φ),
      u φ) = 1 := by
    refine Finset.prod_eq_one (fun φ hφ => ?_)
    rw [Finset.mem_filter] at hφ
    obtain ⟨-, hφr⟩ := hφ
    show φ a / ((‖φ a‖ : ℝ) : ℂ) = 1
    have hcoe : ((hφr.embedding a : ℝ) : ℂ) = φ a := hφr.coe_embedding_apply a
    have hpos' : 0 < hφr.embedding a := hpos (hφr.embedding)
    have hnormeq : ‖φ a‖ = hφr.embedding a := by
      rw [← hcoe]
      simpa [abs_of_pos hpos'] using RCLike.norm_ofReal (K := ℂ) (hφr.embedding a)
    rw [hnormeq, ← hcoe]
    exact div_self (Complex.ofReal_ne_zero.mpr (ne_of_gt hpos'))
  have hu : (∏ φ : K →+* ℂ, u φ) = 1 := by
    have h := Finset.prod_filter_mul_prod_filter_not Finset.univ
      (fun φ : K →+* ℂ => NumberField.ComplexEmbedding.IsReal φ) u
    rw [hR, hT, one_mul] at h
    simpa using h.symm
  -- hence the product over all embeddings is the (positive) product of the norms `‖φ a‖`
  have hP : (∏ φ : K →+* ℂ, φ a) = ((∏ φ : K →+* ℂ, ‖φ a‖ : ℝ) : ℂ) := by
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
      _ = ∏ φ : K →+* ℂ, ((‖φ a‖ : ℝ) : ℂ) := by rw [hu, one_mul]
      _ = ((∏ φ : K →+* ℂ, ‖φ a‖ : ℝ) : ℂ) :=
          (map_prod Complex.ofRealHom (fun φ : K →+* ℂ => ‖φ a‖) Finset.univ).symm
  have hprod : 0 < (∏ φ : K →+* ℂ, ‖φ a‖ : ℝ) :=
    Finset.prod_pos (fun φ _ => norm_pos_iff.mpr (hne φ))
  have h3 : algebraMap ℚ ℂ (Algebra.norm ℚ a) = ((∏ φ : K →+* ℂ, ‖φ a‖ : ℝ) : ℂ) :=
    hnorm.trans hP
  have h4 : (((Algebra.norm ℚ a : ℚ) : ℝ) : ℂ) = ((∏ φ : K →+* ℂ, ‖φ a‖ : ℝ) : ℂ) := by
    rw [Complex.ofReal_ratCast]
    simpa using h3
  have h5 : ((Algebra.norm ℚ a : ℚ) : ℝ) = (∏ φ : K →+* ℂ, ‖φ a‖ : ℝ) :=
    Complex.ofReal_injective h4
  exact Rat.cast_pos.mp (h5.symm ▸ hprod)

end NK.CFTLib.ARL
