import Mathlib
import Submission.Work.FatouCoord.Setup
import Submission.Work.FatouCoord.Estimate.wMap_iterate_deriv_bound

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# The attracting petal is mapped into itself

For a parabolic germ `f z = z + z ^ 2 * h z` with `h 0 = 1` (collected in `ParabolicBounds`)
there is a level `M > 0` such that `f` maps the petal `Petal r M` into itself.

The proof works in the parabolic chart `w = -1/z`.  On the sector `PetalChart r M` (which is the
image of `Petal r M` under the chart, `Petal_eq_preimage_chart`) the chart dynamics
`wMap f w = -1 / f (-1/w)` is a translation by `1` up to an error of order `1/‖w‖`; this is
`Estimate.wMap_sub_bound_aux`:

`‖wMap f w - w - 1‖ ≤ Ksub A a / ‖w‖` for `Re w > 0`, `‖w‖ > 1/r`, `‖w‖ ≥ 4`.

Choosing `M` with `M > 1/r + 4`, `M > 4` and `2 * Ksub A a + 2 ≤ M` we get, for `w` with
`Re w > M`, that the error is at most `1/2`.  Hence

* `Re (wMap f w) ≥ Re w + 1 - 1/2 > M`, and
* `‖wMap f w‖ ≥ ‖w + 1‖ - 1/2 ≥ ‖w‖ - 1 - 1/2 > 1/r`,

i.e. `wMap f w ∈ PetalChart r M`; translating back with the chart gives `f z ∈ Petal r M`.
-/

namespace Work.FatouCoord.Petal

open Work.FatouCoord Metric Set

theorem petal_mapsTo {f h : ℂ → ℂ} {a : ℂ} {r A A' : ℝ} (hb : ParabolicBounds f h a r A A') :
    ∃ M : ℝ, 0 < M ∧ MapsTo f (Petal r M) (Petal r M) := by
  set K : ℝ := Estimate.Ksub A a with hKdef
  have hKnn : 0 ≤ K := by rw [hKdef]; exact Estimate.Ksub_nonneg hb.hA a
  set M : ℝ := max (1 / r + 4) (max (2 * K + 2) 4) with hMdef
  have hM1 : 1 / r + 4 ≤ M := by rw [hMdef]; exact le_max_left _ _
  have hM2 : max (2 * K + 2) 4 ≤ M := by rw [hMdef]; exact le_max_right _ _
  have hM3 : 2 * K + 2 ≤ M := le_trans (le_max_left _ _) hM2
  have hM4 : (4 : ℝ) ≤ M := le_trans (le_max_right _ _) hM2
  have hMpos : 0 < M := lt_of_lt_of_le (by norm_num) hM4
  have hMinvr : 1 / r < M := by linarith
  have hMgt4 : 4 < M := by
    have h1r : 0 < 1 / r := one_div_pos.mpr hb.hr
    linarith
  refine ⟨M, hMpos, ?_⟩
  intro z hz
  have hz0 : z ≠ 0 := ne_zero_of_mem_Petal hz
  have hns : 0 < Complex.normSq z := normSq_pos_of_mem_Petal hz
  obtain ⟨hzr, hzre⟩ := hz
  set w : ℂ := chart z with hwdef
  have hw_re : M < w.re := by
    rw [hwdef, re_chart hz0, lt_div_iff₀ hns]
    linarith [hzre]
  have hwpos : 0 < w.re := lt_trans hMpos hw_re
  have hwnorm : M < ‖w‖ := lt_of_lt_of_le hw_re (Complex.re_le_norm w)
  have hwnormpos : 0 < ‖w‖ := lt_trans hMpos hwnorm
  have hwnorm4 : (4 : ℝ) ≤ ‖w‖ := le_of_lt (lt_trans hMgt4 hwnorm)
  have hwnorminvr : 1 / r < ‖w‖ := lt_trans hMinvr hwnorm
  have hbound0 := Estimate.wMap_sub_bound_aux hb hwpos hwnorminvr hwnorm4
  have hbound : ‖wMap f w - (w + 1)‖ ≤ K / ‖w‖ := by
    have h' : ‖wMap f w - w - 1‖ ≤ K / ‖w‖ := hKdef.symm ▸ hbound0
    have he : wMap f w - (w + 1) = wMap f w - w - 1 := by ring
    rw [he]
    exact h'
  have hKM : K / ‖w‖ ≤ 1 / 2 := by
    rw [div_le_iff₀ hwnormpos]
    linarith
  have hdelta : ‖wMap f w - (w + 1)‖ ≤ 1 / 2 := le_trans hbound hKM
  have hrew : M < (wMap f w).re := by
    have h1 := Complex.abs_re_le_norm (wMap f w - (w + 1))
    rw [abs_le] at h1
    have h2 : (wMap f w - (w + 1)).re = (wMap f w).re - (w + 1).re := Complex.sub_re _ _
    have h3 : (w + 1).re = w.re + 1 := by simp
    linarith [h1.1, hdelta]
  have hnormw' : 1 / r < ‖wMap f w‖ := by
    have hb2 : ‖w‖ - 1 ≤ ‖w + 1‖ := by
      have h := norm_sub_le (w + 1) (1 : ℂ)
      rw [add_sub_cancel_right, norm_one] at h
      linarith
    have hb3 : ‖w + 1‖ - ‖wMap f w - (w + 1)‖ ≤ ‖wMap f w‖ := by
      have h := abs_norm_sub_norm_le (w + 1) ((w + 1) - wMap f w)
      rw [sub_sub_cancel] at h
      have h2 := (abs_le.mp h).2
      have he : ‖(w + 1) - wMap f w‖ = ‖wMap f w - (w + 1)‖ := by
        rw [← norm_neg]
        congr 1
        ring
      linarith
    linarith [hb2, hb3, hdelta, hwnorm, hMinvr]
  have hchart : wMap f w ∈ PetalChart r M := ⟨hrew, hnormw'⟩
  have hww : chart w = z := by rw [hwdef, chart_chart hz0]
  have hmaps : wMap f w = chart (f z) := by
    show chart (f (chart w)) = chart (f z)
    rw [hww]
  have hfz : f z ∈ Petal r M := by
    rw [Petal_eq_preimage_chart hb.hr, mem_preimage, ← hmaps]
    exact hchart
  exact hfz

end Work.FatouCoord.Petal
