import Mathlib
import Submission.Work.BW.siegel_heights

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW

/-- **Height bound from a bound on the mixed-embedding coordinates.**

If every `mixedEmbedding.stdBasis` coordinate of `mixedEmbedding F (x j : F)` (`j : κ`) is at
most `r ≥ 1` in absolute value, then
`logHeight x ≤ [F:ℚ] · log r + r₂ · log 2`, where `r₂` is the number of complex places of `F`.

Indeed, at a real place `w` the single coordinate `re` is the real embedding of `x j`, so
`w (x j) = |σ x j| ≤ r`, while at a complex place `w` the two coordinates `re, im` are the real and
imaginary parts of a complex embedding `σ x j`, so `w (x j) = |σ x j| ≤ √2 · r`.  Summing the
place-wise bounds with weights `mult w` gives
`r₁ log r + 2 r₂ log(√2 r) = (r₁ + 2 r₂) log r + r₂ log 2`. -/
theorem logHeight_le_of_mixed_coord_le {F : Type*} [Field F] [NumberField F] {κ : Type*} [Fintype κ]
    (x : κ → NumberField.RingOfIntegers F) {r : ℝ} (hr : 1 ≤ r)
    (h : ∀ j (k : NumberField.mixedEmbedding.index F),
      |(NumberField.mixedEmbedding.stdBasis F).repr
        (NumberField.mixedEmbedding F (x j : F)) k| ≤ r) :
    Height.logHeight (fun j => (x j : F)) ≤
      (Module.finrank ℚ F : ℝ) * Real.log r +
        (NumberField.InfinitePlace.nrComplexPlaces F : ℝ) * Real.log 2 := by
  classical
  -- At a real place the mixed-embedding coordinate is the real embedding itself.
  have hreal : ∀ j (w : {w : NumberField.InfinitePlace F // w.IsReal}), w.1 (x j : F) ≤ r := by
    intro j w
    have hk := h j (Sum.inl w)
    rw [NumberField.mixedEmbedding.stdBasis_apply_isReal] at hk
    rw [NumberField.mixedEmbedding.mixedEmbedding_apply_isReal] at hk
    rw [← Real.norm_eq_abs, NumberField.InfinitePlace.norm_embedding_of_isReal] at hk
    exact hk
  -- At a complex place the two coordinates are the real and imaginary parts of a complex
  -- embedding, whence the bound `√2 · r`.
  have hcomp : ∀ j (w : {w : NumberField.InfinitePlace F // w.IsComplex}),
      w.1 (x j : F) ≤ Real.sqrt 2 * r := by
    intro j w
    have hk0 := h j (Sum.inr (w, 0))
    have hk1 := h j (Sum.inr (w, 1))
    rw [NumberField.mixedEmbedding.stdBasis_apply_isComplex_fst] at hk0
    rw [NumberField.mixedEmbedding.stdBasis_apply_isComplex_snd] at hk1
    rw [NumberField.mixedEmbedding.mixedEmbedding_apply_isComplex] at hk0 hk1
    have hsq : ‖w.1.embedding (x j : F)‖ ^ 2 ≤ (Real.sqrt 2 * r) ^ 2 := by
      rw [Complex.sq_norm, Complex.normSq_apply]
      have h1 : (w.1.embedding (x j : F)).re ^ 2 ≤ r ^ 2 := by
        have := pow_le_pow_left₀ (abs_nonneg _) hk0 2
        rwa [sq_abs] at this
      have h2 : (w.1.embedding (x j : F)).im ^ 2 ≤ r ^ 2 := by
        have := pow_le_pow_left₀ (abs_nonneg _) hk1 2
        rwa [sq_abs] at this
      have h3 : Real.sqrt 2 ^ 2 = (2 : ℝ) := Real.sq_sqrt (by norm_num)
      nlinarith [h1, h2, h3, hr]
    have h4 := sq_le_sq.mp hsq
    rw [abs_of_nonneg (norm_nonneg _),
      abs_of_nonneg (mul_nonneg (Real.sqrt_nonneg 2) (by linarith))] at h4
    rw [← NumberField.InfinitePlace.norm_embedding_eq w.1 (x j : F)]
    exact h4
  -- The place-wise bound to feed into `logHeight_le_of_place_bound`.
  set f : NumberField.InfinitePlace F → ℝ :=
    fun w => if w.IsReal then r else Real.sqrt 2 * r with hf_def
  have hf : ∀ w, 1 ≤ f w := by
    intro w
    rw [hf_def]
    by_cases hw : w.IsReal
    · simp only [hw, ite_true]; exact hr
    · simp only [hw, ite_false]
      have h1 : (1 : ℝ) ≤ Real.sqrt 2 := by
        rw [← Real.sqrt_one]; exact Real.sqrt_le_sqrt (by norm_num)
      nlinarith [hr]
  have hbound : ∀ j w, w (x j : F) ≤ f w := by
    intro j w
    rw [hf_def]
    by_cases hw : w.IsReal
    · simp only [hw, ite_true]; exact hreal j ⟨w, hw⟩
    · simp only [hw, ite_false]
      exact hcomp j ⟨w, NumberField.InfinitePlace.not_isReal_iff_isComplex.mp hw⟩
  have hstep := Work.BW.logHeight_le_of_place_bound x f hf hbound
  refine hstep.trans ?_
  -- Evaluate the weighted sum of the place bounds.
  have hsum : ∑ w : NumberField.InfinitePlace F, (w.mult : ℝ) * Real.log (f w)
      = (NumberField.InfinitePlace.nrRealPlaces F : ℝ) * Real.log r
        + (NumberField.InfinitePlace.nrComplexPlaces F : ℝ) * (Real.log 2 + 2 * Real.log r) := by
    rw [NumberField.InfinitePlace.sum_eq_sum_add_sum]
    have hrterm : ∀ w : {w : NumberField.InfinitePlace F // w.IsReal},
        (w.1.mult : ℝ) * Real.log (f w.1) = Real.log r := by
      intro w
      have hfr : f w.1 = r := by rw [hf_def]; simp [w.2]
      rw [hfr, NumberField.InfinitePlace.mult_isReal w, Nat.cast_one, one_mul]
    have hcterm : ∀ w : {w : NumberField.InfinitePlace F // w.IsComplex},
        (w.1.mult : ℝ) * Real.log (f w.1) = Real.log 2 + 2 * Real.log r := by
      intro w
      have hfr : f w.1 = Real.sqrt 2 * r := by
        rw [hf_def]
        simp [NumberField.InfinitePlace.not_isReal_iff_isComplex.mpr w.2]
      rw [hfr, NumberField.InfinitePlace.mult_isComplex w, Nat.cast_ofNat]
      have hs2 : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
      rw [Real.log_mul (ne_of_gt hs2) (by linarith : r ≠ 0),
        Real.log_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
      ring
    rw [Finset.sum_congr rfl (fun w _ => hrterm w), Finset.sum_congr rfl (fun w _ => hcterm w),
      Finset.sum_const, Finset.sum_const, nsmul_eq_mul, nsmul_eq_mul, Finset.card_univ,
      Finset.card_univ]
  rw [hsum]
  -- `nrRealPlaces + 2 * nrComplexPlaces = [F : ℚ]`.
  have hrank : (NumberField.InfinitePlace.nrRealPlaces F : ℝ)
      + 2 * (NumberField.InfinitePlace.nrComplexPlaces F : ℝ) = (Module.finrank ℚ F : ℝ) := by
    rw [← Nat.cast_two, ← Nat.cast_mul, ← Nat.cast_add,
      NumberField.InfinitePlace.card_add_two_mul_card_eq_rank]
  have key : (NumberField.InfinitePlace.nrRealPlaces F : ℝ) * Real.log r
        + (NumberField.InfinitePlace.nrComplexPlaces F : ℝ) * (Real.log 2 + 2 * Real.log r)
      = (Module.finrank ℚ F : ℝ) * Real.log r
        + (NumberField.InfinitePlace.nrComplexPlaces F : ℝ) * Real.log 2 := by
    rw [← hrank]; ring
  rw [key]

end Work.BW
