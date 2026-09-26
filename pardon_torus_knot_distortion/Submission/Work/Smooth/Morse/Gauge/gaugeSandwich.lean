import Mathlib
import Submission.Work.Smooth.Morse.Gauge
import Submission.Work.Smooth.Morse.Gauge.PBox_subset_boxGauge
import Submission.Work.Smooth.Morse.Gauge.boxGauge_subset_PBox
import Submission.Work.Smooth.Morse.Defs

namespace Work.Smooth.Morse.Gauge

open LeanEval.KnotTheory.PardonDistortion
open Set

/-- The `ℓ^{2k}`-gauge is non-negative: it is a non-negative real power of a sum of
non-negative terms. -/
theorem boxGauge_nonneg (c : R3) (σ : Equiv.Perm (Fin 3)) (k : ℕ) (y : R3) :
    0 ≤ Work.Smooth.Morse.boxGauge c σ k y := by
  unfold Work.Smooth.Morse.boxGauge
  exact Real.rpow_nonneg (Finset.sum_nonneg (fun i _ => pow_nonneg (abs_nonneg _) _)) _

/-- **The gauge sandwich.** The sublevel sets of the `ℓ^{2k}`-gauge `boxGauge` trap Pardon's box
`PBox t c σ` between two nearby levels: there is `δ > 0` (namely `δ = 3^{1/(2k)} - 1`) such that
on the surface `F = torus ψ`

`F ∩ PBox t c σ ⊆ F ∩ {boxGauge / (1+δ) < t}`  and  `F ∩ {boxGauge / (1+δ) < t} ⊆ PBox ((1+δ) t)`.

This is exactly the sandwich hypothesis of the box-sweep theorems, in the form produced by the
explicit gauge `boxGauge`.  The upper bound comes from
`PBox_subset_boxGauge` (`PBox t ⊆ {boxGauge < 3^{1/(2k)} t}`, and `1 + δ = 3^{1/(2k)}`), the lower
bound from `boxGauge_subset_PBox` (`{boxGauge < s} ⊆ PBox s`) applied at `s = (1+δ) t > 0`; for
`t < 0` (respectively `t ≤ 0`) the box (respectively the region) is empty. -/
theorem gaugeSandwich (ψ : Submission.Diffeo) (c : LeanEval.KnotTheory.PardonDistortion.R3) (σ : Equiv.Perm (Fin 3)) (k : ℕ) (hk : 1 ≤ k) :
    ∃ δ : ℝ, 0 < δ ∧
      (∀ t : ℝ, Submission.PBox t c σ ∩ (Work.Smooth.Morse.torus ψ).carrier ⊆
        Work.Smooth.Morse.region ψ (fun y => Work.Smooth.Morse.boxGauge c σ k y / (1 + δ)) t) ∧
      (∀ t : ℝ, Work.Smooth.Morse.region ψ (fun y => Work.Smooth.Morse.boxGauge c σ k y / (1 + δ)) t ⊆
        Submission.PBox ((1 + δ) * t) c σ) := by
  have hk2pos : (0 : ℝ) < 2 * (k : ℝ) := by
    have h1 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
    linarith
  have hexp_pos : 0 < 1 / (2 * (k : ℝ)) := by positivity
  have hroot : (1 : ℝ) < (3 : ℝ) ^ (1 / (2 * (k : ℝ))) :=
    Real.one_lt_rpow (by norm_num) hexp_pos
  have hδpos : (0 : ℝ) < (3 : ℝ) ^ (1 / (2 * (k : ℝ))) - 1 := by linarith
  have h1δpos : (0 : ℝ) < 1 + ((3 : ℝ) ^ (1 / (2 * (k : ℝ))) - 1) := by linarith
  have h1δeq : 1 + ((3 : ℝ) ^ (1 / (2 * (k : ℝ))) - 1) = (3 : ℝ) ^ (1 / (2 * (k : ℝ))) := by ring
  refine ⟨(3 : ℝ) ^ (1 / (2 * (k : ℝ))) - 1, hδpos, ?_, ?_⟩
  · intro t x hx
    rw [Set.mem_inter_iff] at hx
    obtain ⟨hxbox, hxcar⟩ := hx
    rw [Work.Smooth.Morse.mem_region]
    refine ⟨hxcar, ?_⟩
    rcases lt_or_ge t 0 with ht | ht
    · exfalso
      have h0 := hxbox 0
      rw [Submission.boxSide_zero, one_mul] at h0
      exact absurd h0 (not_lt.mpr (le_trans (le_of_lt ht) (abs_nonneg _)))
    · have hgauge := PBox_subset_boxGauge c σ k hk t ht hxbox
      simp only [Set.mem_ofPred_eq] at hgauge
      rw [div_lt_iff₀ h1δpos, h1δeq, mul_comm t]
      exact hgauge
  · intro t x hx
    rw [Work.Smooth.Morse.mem_region] at hx
    obtain ⟨hxcar, hxg⟩ := hx
    rcases le_or_gt t 0 with ht | ht
    · exfalso
      have hnn : 0 ≤ Work.Smooth.Morse.boxGauge c σ k x /
          (1 + ((3 : ℝ) ^ (1 / (2 * (k : ℝ))) - 1)) :=
        div_nonneg (boxGauge_nonneg c σ k x) (le_of_lt h1δpos)
      exact absurd hxg (not_lt.mpr (le_trans ht hnn))
    · have hspos : (0 : ℝ) < (1 + ((3 : ℝ) ^ (1 / (2 * (k : ℝ))) - 1)) * t :=
        mul_pos h1δpos ht
      have hsub := boxGauge_subset_PBox c σ k hk
        ((1 + ((3 : ℝ) ^ (1 / (2 * (k : ℝ))) - 1)) * t) hspos
      apply hsub
      simp only [Set.mem_ofPred_eq]
      rw [div_lt_iff₀ h1δpos] at hxg
      rw [mul_comm t] at hxg
      exact hxg

end Work.Smooth.Morse.Gauge
