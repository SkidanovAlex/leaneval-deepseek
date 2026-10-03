/-
# Positivity and non-vanishing of the arc periodization `arcTileH`

`arcTileH u = Σ_{m ∈ ℤ} arcBump0 (u - m)` is the periodization of the rescaled bump
`arcBump0 u = lipSchChi (4u/3)`, which equals `1` for `|u| ≤ 3/8` and `0` for `|u| ≥ 3/4`
(`Work.KMTAreas.A4.lip2ArcDefs`).  This file proves the "strictly positive" part of the
docstring of `lip2ArcDefs`, namely that

* `arcTileH_re_pos u : 0 < (arcTileH u).re`, the real part is the sum of the non-negative real
  numbers `arcBumpR (u - m)`, and at least one of them (the one with `|u - m| ≤ 1/2`) is strictly
  positive;
* `arcTileH_im_eq_zero u : (arcTileH u).im = 0`, so `arcTileH u` is a positive *real* number;
* `arcTileH_ne_zero u : arcTileH u ≠ 0`, the statement needed to form the tiling bump
  `arcChi u = arcBump0 u / arcTileH u`.

The proof is elementary: for an integer `m₀` with `|u - m₀| ≤ 1/2` (take `m₀ = ⌊u + 1/2⌋`) the
summand is strictly positive, and only the three indices `m₀ - 1, m₀, m₀ + 1` can contribute at
all, since `arcBump0` vanishes at distance `≥ 3/4` from the origin.  So the infinite sum is a
*finite* sum of non-negative real numbers, one of which is positive.
-/
import Mathlib
import Submission.Work.KMTAreas.A4.arcBumpBasic

set_option autoImplicit false

open scoped BigOperators

namespace Work.KMTAreas.A4

/-- An integer within distance `1/2` of `u`: `arcInt u = ⌊u + 1/2⌋`. -/
private noncomputable def arcInt (u : ℝ) : ℤ := ⌊u + 1 / 2⌋

/-- The defining property of `arcInt`: `u` lies in `[arcInt u - 1/2, arcInt u + 1/2)`. -/
private theorem arcInt_spec (u : ℝ) :
    ((arcInt u : ℤ) : ℝ) ≤ u + 1 / 2 ∧ u + 1 / 2 < ((arcInt u : ℤ) : ℝ) + 1 :=
  ⟨Int.floor_le _, Int.lt_floor_add_one _⟩

/-- `arcTileH u` is the *finite* sum of `arcBump0 (u - m)` over the three relevant indices
`m ∈ {arcInt u - 1, arcInt u, arcInt u + 1}`: every other index contributes `0`, because
`arcBump0` vanishes at distance `≥ 3/4` from the origin while `|u - arcInt u| ≤ 1/2`. -/
private theorem arcTileH_eq_sum_arcInt (u : ℝ) :
    arcTileH u =
      ∑ m ∈ Finset.Icc (arcInt u - 1) (arcInt u + 1), arcBump0 (u - (m : ℝ)) := by
  rw [arcTileH]
  refine tsum_eq_sum fun m hm => ?_
  rw [Finset.mem_Icc] at hm
  obtain ⟨hm₀_le, hm₀_lt⟩ := arcInt_spec u
  have hcases : m < arcInt u - 1 ∨ arcInt u + 1 < m := by omega
  have habs : 3 / 4 ≤ |u - (m : ℝ)| := by
    rcases hcases with hm' | hm'
    · -- `m ≤ arcInt u - 2`, so `u - m ≥ (u - arcInt u) + 2 ≥ 3/2`
      have hm2 : (m : ℝ) ≤ ((arcInt u : ℤ) : ℝ) - 2 := by
        have : m ≤ arcInt u - 2 := by omega
        exact_mod_cast this
      rw [abs_of_nonneg (by linarith)]
      linarith
    · -- `m ≥ arcInt u + 2`, so `u - m ≤ (u - arcInt u) - 2 ≤ -3/2`
      have hm2 : ((arcInt u : ℤ) : ℝ) + 2 ≤ (m : ℝ) := by
        have : arcInt u + 2 ≤ m := by omega
        exact_mod_cast this
      rw [abs_of_neg (by linarith)]
      linarith
  rw [arcBump0_eq_ofReal, arcBumpR_eq_zero (u - (m : ℝ)) habs, Complex.ofReal_zero]

/-- `arcTileH u` is a positive real number: its real part is the finite sum of the non-negative
terms `arcBumpR (u - m)`, and the term with `m = arcInt u` is strictly positive. -/
theorem arcTileH_re_pos (u : ℝ) : 0 < (Work.KMTAreas.A4.arcTileH u).re := by
  obtain ⟨hm₀_le, hm₀_lt⟩ := arcInt_spec u
  have hmem : arcInt u ∈ Finset.Icc (arcInt u - 1) (arcInt u + 1) := by simp
  have hRpos : 0 < arcBumpR (u - ((arcInt u : ℤ) : ℝ)) := by
    apply arcBumpR_pos
    rw [abs_lt]
    constructor <;> linarith
  have hpossum :
      0 < ∑ m ∈ Finset.Icc (arcInt u - 1) (arcInt u + 1), arcBumpR (u - (m : ℝ)) :=
    Finset.sum_pos' (fun m _ => arcBumpR_nonneg _) ⟨arcInt u, hmem, hRpos⟩
  have hre : (arcTileH u).re =
      ∑ m ∈ Finset.Icc (arcInt u - 1) (arcInt u + 1), arcBumpR (u - (m : ℝ)) := by
    rw [arcTileH_eq_sum_arcInt u, Complex.re_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [arcBump0_eq_ofReal, Complex.ofReal_re]
  rw [hre]
  exact hpossum

/-- `arcTileH u` is real: its imaginary part vanishes, since `arcBump0 = ofReal ∘ arcBumpR`. -/
theorem arcTileH_im_eq_zero (u : ℝ) : (Work.KMTAreas.A4.arcTileH u).im = 0 := by
  have him : (arcTileH u).im =
      ∑ m ∈ Finset.Icc (arcInt u - 1) (arcInt u + 1), (arcBump0 (u - (m : ℝ))).im := by
    rw [arcTileH_eq_sum_arcInt u, Complex.im_sum]
  rw [him]
  refine Finset.sum_eq_zero fun m _ => ?_
  rw [arcBump0_eq_ofReal, Complex.ofReal_im]

/-- The periodization `arcTileH u = Σ_m arcBump0 (u - m)` never vanishes. -/
theorem arcTileH_ne_zero (u : ℝ) : Work.KMTAreas.A4.arcTileH u ≠ 0 := by
  intro h
  have hz : (arcTileH u).re = 0 := by rw [h]; simp
  linarith [arcTileH_re_pos u]

end Work.KMTAreas.A4
