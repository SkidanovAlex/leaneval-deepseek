import Mathlib
import Submission.Work.Drive.BoxParityDefs
import Submission.Work.Drive.interior_unitBox

/-!
# Crossing of the boundary of the unit box by a flow line of `flowField F`

A flow line `γ` of the tangential field `Work.Drive.flowField F` which at time `0` sits at a point
`b` of the boundary of the unit box lying on exactly one face `i` (coordinate `i` equal to `0` or
`1`, all other coordinates strictly between `0` and `1`) and for which the `i`-th component of the
field at `b` is nonzero, crosses the boundary of the box transversally at `t = 0`: on one of the
two sides of `0` it lies in the interior of the box, on the other side outside the box.

The whole content is the one-dimensional fact that a differentiable function with nonzero derivative
at `0` changes sign there, together with continuity of `γ` at `0` for the remaining coordinates:
`slope f 0 t = t⁻¹ (f t - f 0)` has the sign of the derivative near `0`, whence `f t - f 0` has the
sign of `t` times the sign of the derivative.  No smoothness or continuity of `F` is needed.
-/

namespace Work.Drive

open Set Filter
open scoped Topology

noncomputable section

/-- A statement which holds eventually in the punctured neighbourhood filter of `0` holds on a
punctured interval `(-δ, δ)`. -/
theorem eventually_nhdsNE_iff_exists_pos {P : ℝ → Prop}
    (h : ∀ᶠ t in 𝓝[≠] (0:ℝ), P t) : ∃ δ > 0, ∀ t, 0 < |t| → |t| < δ → P t := by
  rw [eventually_nhdsWithin_iff] at h
  rw [Metric.eventually_nhds_iff] at h
  obtain ⟨δ, hδ, hP⟩ := h
  refine ⟨δ, hδ, fun t ht hlt => hP ?_ ?_⟩
  · rwa [Real.dist_eq, sub_zero]
  · simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
    exact abs_pos.mp ht

/-- A differentiable function `f` with positive derivative `c` at `0` is increasing through `0`:
`f t > f 0` just to the right of `0` and `f t < f 0` just to the left, and `f` differs from `f 0`
by less than `1` near `0`. -/
theorem scalar_pos {f : ℝ → ℝ} {c : ℝ} (h : HasDerivAt f c 0) (hc : 0 < c) :
    ∃ δ > 0, (∀ t ∈ Ioo (0:ℝ) δ, f 0 < f t) ∧ (∀ t ∈ Ioo (-δ) 0, f t < f 0) ∧
      (∀ t ∈ Ioo (-δ) δ, |f t - f 0| < 1) := by
  have hslope : ∀ᶠ t in 𝓝[≠] (0:ℝ), 0 < slope f 0 t :=
    h.tendsto_slope.eventually (Ioi_mem_nhds hc)
  obtain ⟨δ₁, hδ₁, hS⟩ := eventually_nhdsNE_iff_exists_pos hslope
  have hcont : f ⁻¹' Ioo (f 0 - 1) (f 0 + 1) ∈ 𝓝 (0:ℝ) :=
    h.continuousAt.preimage_mem_nhds
      (isOpen_Ioo.mem_nhds ⟨by linarith, by linarith⟩)
  obtain ⟨δ₂, hδ₂, hC⟩ := Metric.eventually_nhds_iff.mp hcont
  refine ⟨min δ₁ δ₂, lt_min hδ₁ hδ₂, ?_, ?_, ?_⟩
  · intro t ht
    have ht1 : 0 < t := ht.1
    have hle : |t| < δ₁ := by
      rw [abs_of_pos ht1]; linarith [ht.2, min_le_left δ₁ δ₂]
    have hs : 0 < slope f 0 t := hS t (abs_pos.mpr (ne_of_gt ht1)) hle
    have hs' : 0 < t⁻¹ * (f t - f 0) := by
      simpa [slope, sub_zero] using hs
    have := mul_pos ht1 hs'
    rw [← mul_assoc, mul_inv_cancel₀ (ne_of_gt ht1), one_mul] at this
    linarith
  · intro t ht
    have ht1 : t < 0 := ht.2
    have hle : |t| < δ₁ := by
      rw [abs_of_neg ht1]; linarith [ht.1, min_le_left δ₁ δ₂]
    have hs : 0 < slope f 0 t := hS t (abs_pos.mpr (ne_of_lt ht1)) hle
    have hs' : 0 < t⁻¹ * (f t - f 0) := by
      simpa [slope, sub_zero] using hs
    have := mul_neg_of_neg_of_pos ht1 hs'
    rw [← mul_assoc, mul_inv_cancel₀ (ne_of_lt ht1), one_mul] at this
    linarith
  · intro t ht
    have hdist : dist t 0 < δ₂ := by
      rw [Real.dist_eq, sub_zero, abs_lt]
      exact ⟨by linarith [ht.1, min_le_right δ₁ δ₂],
             by linarith [ht.2, min_le_right δ₁ δ₂]⟩
    have hmem : f t ∈ Ioo (f 0 - 1) (f 0 + 1) := hC hdist
    simp only [Set.mem_Ioo] at hmem
    rw [abs_sub_lt_iff]
    exact ⟨by linarith, by linarith⟩

/-- A differentiable function `f` with negative derivative `c` at `0` is decreasing through `0`:
`f t < f 0` just to the right of `0` and `f t > f 0` just to the left, and `f` differs from `f 0`
by less than `1` near `0`. -/
theorem scalar_neg {f : ℝ → ℝ} {c : ℝ} (h : HasDerivAt f c 0) (hc : c < 0) :
    ∃ δ > 0, (∀ t ∈ Ioo (0:ℝ) δ, f t < f 0) ∧ (∀ t ∈ Ioo (-δ) 0, f 0 < f t) ∧
      (∀ t ∈ Ioo (-δ) δ, |f t - f 0| < 1) := by
  have hslope : ∀ᶠ t in 𝓝[≠] (0:ℝ), slope f 0 t < 0 :=
    h.tendsto_slope.eventually (Iio_mem_nhds hc)
  obtain ⟨δ₁, hδ₁, hS⟩ := eventually_nhdsNE_iff_exists_pos hslope
  have hcont : f ⁻¹' Ioo (f 0 - 1) (f 0 + 1) ∈ 𝓝 (0:ℝ) :=
    h.continuousAt.preimage_mem_nhds
      (isOpen_Ioo.mem_nhds ⟨by linarith, by linarith⟩)
  obtain ⟨δ₂, hδ₂, hC⟩ := Metric.eventually_nhds_iff.mp hcont
  refine ⟨min δ₁ δ₂, lt_min hδ₁ hδ₂, ?_, ?_, ?_⟩
  · intro t ht
    have ht1 : 0 < t := ht.1
    have hle : |t| < δ₁ := by
      rw [abs_of_pos ht1]; linarith [ht.2, min_le_left δ₁ δ₂]
    have hs : slope f 0 t < 0 := hS t (abs_pos.mpr (ne_of_gt ht1)) hle
    have hs' : t⁻¹ * (f t - f 0) < 0 := by
      simpa [slope, sub_zero] using hs
    have := mul_neg_of_pos_of_neg ht1 hs'
    rw [← mul_assoc, mul_inv_cancel₀ (ne_of_gt ht1), one_mul] at this
    linarith
  · intro t ht
    have ht1 : t < 0 := ht.2
    have hle : |t| < δ₁ := by
      rw [abs_of_neg ht1]; linarith [ht.1, min_le_left δ₁ δ₂]
    have hs : slope f 0 t < 0 := hS t (abs_pos.mpr (ne_of_lt ht1)) hle
    have hs' : t⁻¹ * (f t - f 0) < 0 := by
      simpa [slope, sub_zero] using hs
    have := mul_pos_of_neg_of_neg ht1 hs'
    rw [← mul_assoc, mul_inv_cancel₀ (ne_of_lt ht1), one_mul] at this
    linarith
  · intro t ht
    have hdist : dist t 0 < δ₂ := by
      rw [Real.dist_eq, sub_zero, abs_lt]
      exact ⟨by linarith [ht.1, min_le_right δ₁ δ₂],
             by linarith [ht.2, min_le_right δ₁ δ₂]⟩
    have hmem : f t ∈ Ioo (f 0 - 1) (f 0 + 1) := hC hdist
    simp only [Set.mem_Ioo] at hmem
    rw [abs_sub_lt_iff]
    exact ⟨by linarith, by linarith⟩

/-- For a differentiable curve `γ` in `Amb m`, the `i`-th coordinate is differentiable with
derivative the `i`-th coordinate of the derivative. -/
theorem hasDerivAt_apply {m : ℕ} {γ : ℝ → Amb m} {v : Amb m} {t : ℝ}
    (h : HasDerivAt γ v t) (i : Fin (m + 1)) : HasDerivAt (fun s => γ s i) (v i) t := by
  have hL : HasFDerivAt ((EuclideanSpace.proj i : Amb m →L[ℝ] ℝ))
      (EuclideanSpace.proj i : Amb m →L[ℝ] ℝ) (γ t) := ContinuousLinearMap.hasFDerivAt _
  exact hL.comp_hasDerivAt t h

/-- **A flow line of `flowField F` crosses the boundary of the unit box transversally.**  At a
boundary point `b` lying on exactly one face `i` of the box, with the `i`-th component of the field
nonzero there, the flow line enters the interior of the box on one side of `0` and lies outside the
box on the other side. -/
theorem crossing_of_deriv_ne_zero {m : ℕ} {F : Work.Drive.Amb m → Work.Drive.Tgt m}
    {γ : ℝ → Work.Drive.Amb m} (hγ : ∀ t, HasDerivAt γ (Work.Drive.flowField F (γ t)) t)
    {b : Work.Drive.Amb m} (hb0 : γ 0 = b) (i : Fin (m + 1))
    (hface : (b i = 0 ∨ b i = 1) ∧ (∀ j, j ≠ i → b j ∈ Set.Ioo (0 : ℝ) 1))
    (hne : Work.Drive.flowField F b i ≠ 0) :
    ∃ ε > 0, ((∀ t ∈ Set.Ioo (0 : ℝ) ε, γ t ∈ interior (Submission.Drive.unitBox m)) ∧
      (∀ t ∈ Set.Ioo (-ε) 0, γ t ∉ Submission.Drive.unitBox m)) ∨
      ((∀ t ∈ Set.Ioo (-ε) 0, γ t ∈ interior (Submission.Drive.unitBox m)) ∧
      (∀ t ∈ Set.Ioo (0 : ℝ) ε, γ t ∉ Submission.Drive.unitBox m)) := by
  have hγcont : Continuous γ := continuous_iff_continuousAt.mpr fun t => (hγ t).continuousAt
  have hγ0 : HasDerivAt γ (flowField F b) 0 := by
    have h := hγ 0
    rwa [hb0] at h
  have hderiv : HasDerivAt (fun s => γ s i) (flowField F b i) 0 := hasDerivAt_apply hγ0 i
  have hf0 : γ 0 i = b i := by simp [hb0]
  -- All coordinates other than the `i`-th are strictly inside `(0,1)` near `t = 0`.
  have hgood : ∀ᶠ t in 𝓝 (0:ℝ), ∀ j : Fin (m + 1), j ≠ i → γ t j ∈ Ioo (0:ℝ) 1 := by
    refine Filter.eventually_all.mpr (fun j => ?_)
    rcases eq_or_ne j i with rfl | hj
    · exact Filter.Eventually.of_forall (fun t h => absurd rfl h)
    · have hmem : {x : Amb m | x j ∈ Ioo (0:ℝ) 1} ∈ 𝓝 (γ 0) := by
        rw [hb0]
        exact (isOpen_Ioo.preimage (by fun_prop)).mem_nhds (hface.2 j hj)
      filter_upwards [hγcont.continuousAt.preimage_mem_nhds hmem] with t ht
      exact fun _ => ht
  obtain ⟨δ₂, hδ₂pos, hδ₂⟩ := Metric.eventually_nhds_iff.mp hgood
  rcases lt_or_gt_of_ne hne with hc | hc
  · -- the `i`-th component of the field at `b` is negative
    obtain ⟨δ₁, hδ₁, hP1, hP2, hP3⟩ := scalar_neg hderiv hc
    have hoth : ∀ t, t ∈ Ioo (-(min δ₁ δ₂)) (min δ₁ δ₂) → ∀ j, j ≠ i → γ t j ∈ Ioo (0:ℝ) 1 := by
      intro t ht j hj
      refine hδ₂ ?_ j hj
      rw [Real.dist_eq, sub_zero, abs_lt]
      exact ⟨by linarith [ht.1, min_le_right δ₁ δ₂], by linarith [ht.2, min_le_right δ₁ δ₂]⟩
    have inside_of : ∀ t, t ∈ Ioo (-(min δ₁ δ₂)) (min δ₁ δ₂) → γ t i ∈ Ioo (0:ℝ) 1 →
        γ t ∈ interior (Submission.Drive.unitBox m) := by
      intro t ht hti
      rw [interior_unitBox m]
      intro j
      rcases eq_or_ne j i with rfl | hj
      · exact hti
      · exact hoth t ht j hj
    have outside_of : ∀ t, (γ t i < 0 ∨ 1 < γ t i) → γ t ∉ Submission.Drive.unitBox m := by
      intro t h hmem
      have hmem' : γ t i ∈ Set.Icc (0:ℝ) 1 := hmem i
      rcases h with h | h
      · linarith [hmem'.1]
      · linarith [hmem'.2]
    rcases hface.1 with hbi0 | hbi1
    · -- `b i = 0`: the flow line enters on the negative side
      refine ⟨min δ₁ δ₂, lt_min hδ₁ hδ₂pos, Or.inr ⟨?_, ?_⟩⟩
      · intro t ht
        have ht' : t ∈ Ioo (-(min δ₁ δ₂)) (min δ₁ δ₂) :=
          ⟨ht.1, by linarith [ht.2, lt_min hδ₁ hδ₂pos]⟩
        refine inside_of t ht' ⟨?_, ?_⟩
        · have h' := hP2 t ⟨by linarith [ht.1, min_le_left δ₁ δ₂], ht.2⟩
          simp only [hf0, hbi0] at h'
          exact h'
        · have h' := hP3 t ⟨by linarith [ht.1, min_le_left δ₁ δ₂], by linarith [ht.2, hδ₁]⟩
          simp only [hf0, hbi0, sub_zero] at h'
          exact (abs_lt.mp h').2
      · intro t ht
        refine outside_of t (Or.inl ?_)
        have h' := hP1 t ⟨ht.1, lt_of_lt_of_le ht.2 (min_le_left δ₁ δ₂)⟩
        simp only [hf0, hbi0] at h'
        exact h'
    · -- `b i = 1`: the flow line enters on the positive side
      refine ⟨min δ₁ δ₂, lt_min hδ₁ hδ₂pos, Or.inl ⟨?_, ?_⟩⟩
      · intro t ht
        have ht' : t ∈ Ioo (-(min δ₁ δ₂)) (min δ₁ δ₂) :=
          ⟨by linarith [ht.1, lt_min hδ₁ hδ₂pos], ht.2⟩
        refine inside_of t ht' ⟨?_, ?_⟩
        · have h' := hP3 t ⟨by linarith [ht.1, hδ₁], by linarith [ht.2, min_le_left δ₁ δ₂]⟩
          simp only [hf0, hbi1] at h'
          have := (abs_lt.mp h').1
          linarith
        · have h' := hP1 t ⟨ht.1, lt_of_lt_of_le ht.2 (min_le_left δ₁ δ₂)⟩
          simp only [hf0, hbi1] at h'
          exact h'
      · intro t ht
        refine outside_of t (Or.inr ?_)
        have h' := hP2 t ⟨by linarith [ht.1, min_le_left δ₁ δ₂], ht.2⟩
        simp only [hf0, hbi1] at h'
        exact h'
  · -- the `i`-th component of the field at `b` is positive
    obtain ⟨δ₁, hδ₁, hP1, hP2, hP3⟩ := scalar_pos hderiv hc
    have hoth : ∀ t, t ∈ Ioo (-(min δ₁ δ₂)) (min δ₁ δ₂) → ∀ j, j ≠ i → γ t j ∈ Ioo (0:ℝ) 1 := by
      intro t ht j hj
      refine hδ₂ ?_ j hj
      rw [Real.dist_eq, sub_zero, abs_lt]
      exact ⟨by linarith [ht.1, min_le_right δ₁ δ₂], by linarith [ht.2, min_le_right δ₁ δ₂]⟩
    have inside_of : ∀ t, t ∈ Ioo (-(min δ₁ δ₂)) (min δ₁ δ₂) → γ t i ∈ Ioo (0:ℝ) 1 →
        γ t ∈ interior (Submission.Drive.unitBox m) := by
      intro t ht hti
      rw [interior_unitBox m]
      intro j
      rcases eq_or_ne j i with rfl | hj
      · exact hti
      · exact hoth t ht j hj
    have outside_of : ∀ t, (γ t i < 0 ∨ 1 < γ t i) → γ t ∉ Submission.Drive.unitBox m := by
      intro t h hmem
      have hmem' : γ t i ∈ Set.Icc (0:ℝ) 1 := hmem i
      rcases h with h | h
      · linarith [hmem'.1]
      · linarith [hmem'.2]
    rcases hface.1 with hbi0 | hbi1
    · -- `b i = 0`: the flow line enters on the positive side
      refine ⟨min δ₁ δ₂, lt_min hδ₁ hδ₂pos, Or.inl ⟨?_, ?_⟩⟩
      · intro t ht
        have ht' : t ∈ Ioo (-(min δ₁ δ₂)) (min δ₁ δ₂) :=
          ⟨by linarith [ht.1, lt_min hδ₁ hδ₂pos], ht.2⟩
        refine inside_of t ht' ⟨?_, ?_⟩
        · have h' := hP1 t ⟨ht.1, lt_of_lt_of_le ht.2 (min_le_left δ₁ δ₂)⟩
          simp only [hf0, hbi0] at h'
          exact h'
        · have h' := hP3 t ⟨by linarith [ht.1, hδ₁], by linarith [ht.2, min_le_left δ₁ δ₂]⟩
          simp only [hf0, hbi0, sub_zero] at h'
          exact (abs_lt.mp h').2
      · intro t ht
        refine outside_of t (Or.inl ?_)
        have h' := hP2 t ⟨by linarith [ht.1, min_le_left δ₁ δ₂], ht.2⟩
        simp only [hf0, hbi0] at h'
        exact h'
    · -- `b i = 1`: the flow line enters on the negative side
      refine ⟨min δ₁ δ₂, lt_min hδ₁ hδ₂pos, Or.inr ⟨?_, ?_⟩⟩
      · intro t ht
        have ht' : t ∈ Ioo (-(min δ₁ δ₂)) (min δ₁ δ₂) :=
          ⟨ht.1, by linarith [ht.2, lt_min hδ₁ hδ₂pos]⟩
        refine inside_of t ht' ⟨?_, ?_⟩
        · have h' := hP3 t ⟨by linarith [ht.1, min_le_left δ₁ δ₂], by linarith [ht.2, hδ₁]⟩
          simp only [hf0, hbi1] at h'
          have := (abs_lt.mp h').1
          linarith
        · have h' := hP2 t ⟨by linarith [ht.1, min_le_left δ₁ δ₂], ht.2⟩
          simp only [hf0, hbi1] at h'
          exact h'
      · intro t ht
        refine outside_of t (Or.inr ?_)
        have h' := hP1 t ⟨ht.1, lt_of_lt_of_le ht.2 (min_le_left δ₁ δ₂)⟩
        simp only [hf0, hbi1] at h'
        exact h'

end

end Work.Drive
