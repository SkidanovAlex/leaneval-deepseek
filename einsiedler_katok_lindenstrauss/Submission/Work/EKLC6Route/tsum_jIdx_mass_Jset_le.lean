import Mathlib
import Submission.Work.EKLC6Route.L7Aux

/-!
# `Work.EKLC6Route.tsum_jIdx_mass_Jset_le` — bounded depth mass

This module proves that the depth-index weighted masses of the window `w` are bounded by `4`:

`∑' J : Option ℕ, ENNReal.ofReal ((jIdx J : ℝ) * (μ (w.Jset J)).toReal) ≤ 4`.

The mathematical input is exactly the *tail decay* field `Window.hCtail` of the window
structure: writing `m_j := μ (W ∩ θ ⁻¹' C j)` and `m_∞ := μ (W ∩ θ ⁻¹' ⋂_i C i)`, the field says
`m_j - m_∞ ≤ 2^{-j}`.  Since

`Jset (some j) = W ∩ θ ⁻¹' (C j \ C (j+1)) ⊆ (W ∩ θ ⁻¹' C j) \ (W ∩ θ ⁻¹' ⋂_i C i)`

(because `⋂_i C i ⊆ C (j+1)`), we get `μ (Jset (some j)) ≤ 2^{-j}`.  The `J = none` term of the
sum vanishes (it carries the index `jIdx none = 0`), so the whole series is bounded by

`∑' j, (j+1) · 2^{-j} = 1/(1-1/2)^2 = 4`.

The two "pure" ingredients are proved first: the classical geometric series evaluation
(`hasSum_succ_mul_half_pow`, `tsum_ofReal_succ_mul_half_pow`) and the measure estimate
(`toReal_measure_Jset_some_le_aux`).
-/

namespace Work.EKLC6Route

open MeasureTheory
open scoped ENNReal

noncomputable section

/-! ## 1. The geometric series `∑ (j+1) 2^{-j} = 4` -/

/-- `∑_{j} (j+1) (1/2)^j = 4`, in the form of a `HasSum` statement (so that summability is also
available).  It is the sum of `∑ j (1/2)^j = (1/2)/(1-1/2)^2 = 2` and `∑ (1/2)^j = (1-1/2)^{-1} = 2`. -/
theorem hasSum_succ_mul_half_pow : HasSum (fun j : ℕ => ((j : ℝ) + 1) * ((1 / 2 : ℝ) ^ j)) 4 := by
  have h1 := hasSum_coe_mul_geometric_of_norm_lt_one (𝕜 := ℝ) (r := (1 / 2 : ℝ)) (by norm_num)
  have h2 := hasSum_geometric_of_norm_lt_one (ξ := (1 / 2 : ℝ)) (by norm_num)
  have h3 := h1.add h2
  have h4 : HasSum (fun j : ℕ => ((j : ℝ) + 1) * ((1 / 2 : ℝ) ^ j))
      ((1 / 2 : ℝ) / (1 - 1 / 2) ^ 2 + (1 - 1 / 2)⁻¹) := h3.congr_fun (fun j => by ring)
  have h5 : (1 / 2 : ℝ) / (1 - 1 / 2) ^ 2 + (1 - 1 / 2)⁻¹ = 4 := by norm_num
  rwa [h5] at h4

/-- The `ℝ≥0∞`-valued version of the previous identity. -/
theorem tsum_ofReal_succ_mul_half_pow :
    (∑' j : ℕ, ENNReal.ofReal (((j : ℝ) + 1) * ((1 / 2 : ℝ) ^ j))) = 4 := by
  rw [← ENNReal.ofReal_tsum_of_nonneg (f := fun j : ℕ => ((j : ℝ) + 1) * ((1 / 2 : ℝ) ^ j))
        (fun j => by positivity) hasSum_succ_mul_half_pow.summable,
      hasSum_succ_mul_half_pow.tsum_eq]
  norm_num

/-! ## 2. The measure bound on `Jset (some j)` -/

/-- The tail decay field of the window bounds the mass of the depth-`j` layer:
`μ (Jset (some j)) ≤ 2^{-j}`.  The point is the inclusion
`Jset (some j) ⊆ (W ∩ θ ⁻¹' C j) \ (W ∩ θ ⁻¹' ⋂_i C i)`, which holds because
`θ x ∈ C j \ C (j+1)` forces `θ x ∉ C (j+1) ⊇ ⋂_i C i`. -/
theorem toReal_measure_Jset_some_le_aux {μ : MeasureTheory.Measure Work.EKLContract.X3}
    {t : Fin 3 → ℝ} (w : Work.EKLC6Route.Window μ t) (j : ℕ) :
    (μ (w.Jset (some j))).toReal ≤ (1 / 2 : ℝ) ^ j := by
  have hsub : w.Jset (some j) ⊆
      (w.W ∩ w.θ ⁻¹' w.C j) \ ⋂ i, (w.W ∩ w.θ ⁻¹' w.C i) := by
    intro x hx
    have hx' : x ∈ w.W ∧ w.θ x ∈ w.C j \ w.C (j + 1) := hx
    refine ⟨⟨hx'.1, hx'.2.1⟩, ?_⟩
    intro hmem
    exact hx'.2.2 (Set.mem_iInter.mp hmem (j + 1)).2
  have h1 : μ (w.Jset (some j)) ≤
      μ ((w.W ∩ w.θ ⁻¹' w.C j) \ ⋂ i, (w.W ∩ w.θ ⁻¹' w.C i)) := measure_mono hsub
  have h2 := w.hCtail j
  have h3 : μ (w.Jset (some j)) ≤ ENNReal.ofReal ((1 / 2 : ℝ) ^ j) := le_trans h1 h2
  calc (μ (w.Jset (some j))).toReal ≤ (ENNReal.ofReal ((1 / 2 : ℝ) ^ j)).toReal :=
        ENNReal.toReal_mono ENNReal.ofReal_ne_top h3
    _ = (1 / 2 : ℝ) ^ j := ENNReal.toReal_ofReal (by positivity)

/-! ## 3. The main estimate -/

theorem tsum_jIdx_mass_Jset_le {μ : MeasureTheory.Measure Work.EKLContract.X3}
    [MeasureTheory.IsProbabilityMeasure μ] {t : Fin 3 → ℝ} (w : Work.EKLC6Route.Window μ t) :
    (∑' J : Option ℕ,
      ENNReal.ofReal ((Work.EKLC6Route.jIdx J : ℝ) * (μ (w.Jset J)).toReal)) ≤ 4 := by
  -- Split the label `Option ℕ` into the `none` term (which is `0`) and the depths `some j`.
  have hsplit : (∑' J : Option ℕ,
      ENNReal.ofReal ((Work.EKLC6Route.jIdx J : ℝ) * (μ (w.Jset J)).toReal))
      ≤ ∑' j : ℕ, ENNReal.ofReal
          ((Work.EKLC6Route.jIdx (some j) : ℝ) * (μ (w.Jset (some j))).toReal) := by
    have h := Work.EKLC6Route.tsum_option_le
      (fun J : Option ℕ => ENNReal.ofReal ((Work.EKLC6Route.jIdx J : ℝ) * (μ (w.Jset J)).toReal))
    have hn : ENNReal.ofReal ((Work.EKLC6Route.jIdx (none : Option ℕ) : ℝ)
        * (μ (w.Jset none)).toReal) = 0 := by
      simp [Work.EKLC6Route.jIdx_none]
    rwa [hn, zero_add] at h
  -- Each depth term is at most `(j+1) * 2^{-j}`.
  have hle : ∀ j : ℕ,
      ENNReal.ofReal ((Work.EKLC6Route.jIdx (some j) : ℝ) * (μ (w.Jset (some j))).toReal)
      ≤ ENNReal.ofReal (((j : ℝ) + 1) * ((1 / 2 : ℝ) ^ j)) := by
    intro j
    have h := toReal_measure_Jset_some_le_aux w j
    have hnn : (0 : ℝ) ≤ (j : ℝ) + 1 := by positivity
    simp only [Work.EKLC6Route.jIdx_some]
    have hcast : (((j + 1 : ℕ)) : ℝ) = (j : ℝ) + 1 := by push_cast; ring
    rw [hcast]
    exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left h hnn)
  have hsum : (∑' j : ℕ, ENNReal.ofReal
        ((Work.EKLC6Route.jIdx (some j) : ℝ) * (μ (w.Jset (some j))).toReal))
      ≤ ∑' j : ℕ, ENNReal.ofReal (((j : ℝ) + 1) * ((1 / 2 : ℝ) ^ j)) :=
    ENNReal.tsum_le_tsum hle
  calc (∑' J : Option ℕ,
        ENNReal.ofReal ((Work.EKLC6Route.jIdx J : ℝ) * (μ (w.Jset J)).toReal))
      ≤ ∑' j : ℕ, ENNReal.ofReal
          ((Work.EKLC6Route.jIdx (some j) : ℝ) * (μ (w.Jset (some j))).toReal) := hsplit
    _ ≤ ∑' j : ℕ, ENNReal.ofReal (((j : ℝ) + 1) * ((1 / 2 : ℝ) ^ j)) := hsum
    _ ≤ 4 := le_of_eq tsum_ofReal_succ_mul_half_pow

end

end Work.EKLC6Route
