import Mathlib
import Submission.Work.FatouCoord.Setup
import Submission.Work.FatouCoord.Estimate.wMap_sub_bound
import Submission.Work.FatouCoord.Petal.petal_mapsTo
import Submission.Work.FatouCoord.Petal.petal_orbit_tendsto_zero

namespace Work.FatouCoord.Petal

open Work.FatouCoord Metric Set Filter

variable {f h : ℂ → ℂ} {a : ℂ} {r A A' : ℝ}

/-- **The chart dynamics is a translation up to `1/2`, uniformly past some level.**
Using `Estimate.wMap_sub_bound` (`wMap f w = w + 1 + (1-a)/w + O(1/w^2)`) there is a level
`N` such that for `Re w > N` the chart dynamics stays within `1/2` of the translation
`w ↦ w + 1`.  This is the quantitative input that makes the *right sector* `PetalChart r M`
forward invariant for **every** level `M ≥ N` (not merely for the single level produced by
`petal_mapsTo`). -/
lemma exists_wMap_close_one (hb : ParabolicBounds f h a r A A') :
    ∃ N : ℝ, 0 < N ∧ 1 / r < N ∧ ∀ w : ℂ, N < w.re → ‖wMap f w - (w + 1)‖ ≤ 1 / 2 := by
  obtain ⟨Nb, Cb, hNbpos, hCbnn, hrNb, hsub⟩ := Estimate.wMap_sub_bound hb
  set N : ℝ := max (max Nb (1 / r)) (max (4 * Cb) (4 * ‖(1 : ℂ) - a‖)) + 2 with hNdef
  have hNbN : Nb < N := by
    rw [hNdef]
    have h1 : Nb ≤ max Nb (1 / r) := le_max_left _ _
    have h2 : max Nb (1 / r) ≤ max (max Nb (1 / r)) (max (4 * Cb) (4 * ‖(1 : ℂ) - a‖)) :=
      le_max_left _ _
    linarith
  have hrN : 1 / r < N := by
    rw [hNdef]
    have h1 : 1 / r ≤ max Nb (1 / r) := le_max_right _ _
    have h2 : max Nb (1 / r) ≤ max (max Nb (1 / r)) (max (4 * Cb) (4 * ‖(1 : ℂ) - a‖)) :=
      le_max_left _ _
    linarith
  have hN4Cb : 4 * Cb ≤ N := by
    rw [hNdef]
    have h1 : 4 * Cb ≤ max (4 * Cb) (4 * ‖(1 : ℂ) - a‖) := le_max_left _ _
    have h2 : max (4 * Cb) (4 * ‖(1 : ℂ) - a‖)
        ≤ max (max Nb (1 / r)) (max (4 * Cb) (4 * ‖(1 : ℂ) - a‖)) := le_max_right _ _
    linarith
  have hN41a : 4 * ‖(1 : ℂ) - a‖ ≤ N := by
    rw [hNdef]
    have h1 : 4 * ‖(1 : ℂ) - a‖ ≤ max (4 * Cb) (4 * ‖(1 : ℂ) - a‖) := le_max_right _ _
    have h2 : max (4 * Cb) (4 * ‖(1 : ℂ) - a‖)
        ≤ max (max Nb (1 / r)) (max (4 * Cb) (4 * ‖(1 : ℂ) - a‖)) := le_max_right _ _
    linarith
  have hN2 : (2 : ℝ) ≤ N := by
    rw [hNdef]
    have h0 : (0 : ℝ) ≤ max (max Nb (1 / r)) (max (4 * Cb) (4 * ‖(1 : ℂ) - a‖)) := by
      have h1 : Nb ≤ max Nb (1 / r) := le_max_left _ _
      have h2 : max Nb (1 / r) ≤ max (max Nb (1 / r)) (max (4 * Cb) (4 * ‖(1 : ℂ) - a‖)) :=
        le_max_left _ _
      linarith [hNbpos]
    linarith
  have hNpos : 0 < N := by linarith
  refine ⟨N, hNpos, hrN, ?_⟩
  intro w hw
  have hwnorm : N < ‖w‖ := lt_of_lt_of_le hw (Complex.re_le_norm w)
  have hwnormpos : 0 < ‖w‖ := lt_of_lt_of_le hNpos hwnorm.le
  have hb1 := hsub w (lt_trans hNbN hw)
  have hb2 : ‖(1 - a) / w‖ = ‖1 - a‖ / ‖w‖ := by rw [norm_div]
  have hden1 : Cb / ‖w‖ ^ 2 ≤ 1 / 4 := by
    rw [div_le_iff₀ (by positivity : (0 : ℝ) < ‖w‖ ^ 2)]
    have h1 : N ^ 2 ≤ ‖w‖ ^ 2 := by nlinarith [hwnorm, hNpos]
    have h2 : 4 * Cb ≤ N ^ 2 := by nlinarith [hN4Cb, hN2, hCbnn]
    linarith
  have hden2 : ‖1 - a‖ / ‖w‖ ≤ 1 / 4 := by
    rw [div_le_iff₀ hwnormpos]
    nlinarith [hN41a, hwnorm]
  have hsplit : wMap f w - w - 1 = (wMap f w - w - 1 - (1 - a) / w) + (1 - a) / w := by ring
  have hnorm : ‖wMap f w - w - 1‖ ≤ 1 / 2 := by
    rw [hsplit]
    calc ‖(wMap f w - w - 1 - (1 - a) / w) + (1 - a) / w‖
        ≤ ‖wMap f w - w - 1 - (1 - a) / w‖ + ‖(1 - a) / w‖ := norm_add_le _ _
      _ ≤ Cb / ‖w‖ ^ 2 + ‖1 - a‖ / ‖w‖ := by rw [hb2]; linarith
      _ ≤ 1 / 4 + 1 / 4 := add_le_add hden1 hden2
      _ = 1 / 2 := by norm_num
  have he : wMap f w - (w + 1) = wMap f w - w - 1 := by ring
  rw [he]
  exact hnorm

/-- **The petal `Petal r M` is forward invariant for every level `M` past a threshold.**

Working in the chart `w = -1/z`: if `Re w > M ≥ N` then `‖wMap f w - (w+1)‖ ≤ 1/2`
(`exists_wMap_close_one`), so `Re (wMap f w) ≥ Re w + 1/2 > M` and
`‖wMap f w‖ ≥ ‖w+1‖ - 1/2 ≥ ‖w‖ - 3/2 > 1/r`; hence `wMap f w ∈ PetalChart r M`, i.e.
`f z ∈ Petal r M`.  Unlike `petal_mapsTo` this holds for *all* sufficiently large levels. -/
lemma petal_mapsTo_of_le (hb : ParabolicBounds f h a r A A') :
    ∃ M₀ : ℝ, ∀ M : ℝ, M₀ ≤ M → MapsTo f (Petal r M) (Petal r M) := by
  obtain ⟨N, hNpos, hrN, hclose⟩ := exists_wMap_close_one hb
  refine ⟨max N (1 / r + 2), fun M hM z hz => ?_⟩
  have hM' : max N (1 / r + 2) ≤ M := hM
  have hNM : N ≤ M := le_trans (le_max_left _ _) hM'
  have hM2 : 1 / r + 2 ≤ M := le_trans (le_max_right _ _) hM'
  have hz0 : z ≠ 0 := ne_zero_of_mem_Petal hz
  have hchart : chart z ∈ PetalChart r M := (chart_mem_Petal_iff hb.hr hz0).mp hz
  obtain ⟨hwre, _⟩ := hchart
  have hww : wMap f (chart z) = chart (f z) := by rw [wMap, chart_chart hz0]
  have hclose' : ‖wMap f (chart z) - (chart z + 1)‖ ≤ 1 / 2 :=
    hclose (chart z) (lt_of_le_of_lt hNM hwre)
  have hre_goal : M < (wMap f (chart z)).re := by
    have h1 := Complex.abs_re_le_norm (wMap f (chart z) - (chart z + 1))
    rw [abs_le] at h1
    have h2 : (wMap f (chart z) - (chart z + 1)).re
        = (wMap f (chart z)).re - (chart z + 1).re := Complex.sub_re _ _
    have h3 : (chart z + 1).re = (chart z).re + 1 := by simp
    linarith [h1.1, hclose', hwre]
  have hnorm_goal : 1 / r < ‖wMap f (chart z)‖ := by
    have hb2 : ‖chart z‖ - 1 ≤ ‖chart z + 1‖ := by
      have h := norm_sub_le (chart z + 1) (1 : ℂ)
      rw [add_sub_cancel_right, norm_one] at h
      linarith
    have hb3 : ‖chart z + 1‖ - ‖wMap f (chart z) - (chart z + 1)‖ ≤ ‖wMap f (chart z)‖ := by
      have h := abs_norm_sub_norm_le (chart z + 1) ((chart z + 1) - wMap f (chart z))
      rw [sub_sub_cancel] at h
      have h2 := (abs_le.mp h).2
      have he : ‖(chart z + 1) - wMap f (chart z)‖
          = ‖wMap f (chart z) - (chart z + 1)‖ := by
        rw [← norm_neg]; congr 1; ring
      linarith
    have hwn : M < ‖chart z‖ := lt_of_lt_of_le hwre (Complex.re_le_norm _)
    linarith [hb2, hb3, hclose', hwn, hM2]
  have hmem : wMap f (chart z) ∈ PetalChart r M := ⟨hre_goal, hnorm_goal⟩
  rw [Petal_eq_preimage_chart hb.hr, mem_preimage, ← hww]
  exact hmem

/-- Once a petal of level `M` is forward invariant with orbits converging to `0`, the same holds
for every *larger* level `M' ≥ M`: petals are nested, `Petal r M' ⊆ Petal r M` when `M ≤ M'`
(`Petal_mono`).  Combining the invariance statement `petal_mapsTo_of_le` with the convergence
threshold of `petal_orbit_tendsto_zero` gives the requested single threshold. -/
theorem petal_mapsTo_tendsto_of_le {f h : ℂ → ℂ} {a : ℂ} {r A A' : ℝ} (hb : ParabolicBounds f h a r A A') : ∃ M₀ : ℝ, ∀ M : ℝ, M₀ ≤ M → MapsTo f (Petal r M) (Petal r M) ∧ ∀ z ∈ Petal r M, Tendsto (fun n : ℕ => f^[n] z) atTop (nhds 0) := by
  obtain ⟨M₁, hmap⟩ := petal_mapsTo_of_le hb
  obtain ⟨M₂, _, hconv⟩ := petal_orbit_tendsto_zero hb
  refine ⟨max M₁ M₂, fun M hM => ⟨hmap M (le_trans (le_max_left _ _) hM), ?_⟩⟩
  · intro z hz
    have hM₂ : M₂ ≤ M := le_trans (le_max_right _ _) hM
    exact hconv z (Petal_mono le_rfl hM₂ hz)

end Work.FatouCoord.Petal
