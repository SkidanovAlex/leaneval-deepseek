import Mathlib
import Submission.Work.Pert.pert2v2.walk_to_window
import Submission.Work.Pert.pert2v2.steps
import Submission.Work.Pert.pert2v2.walk_left_drift
import Submission.Work.Pert.pert2v2.walk_right_drift
import Submission.Work.Pert.waist_low
import Submission.Work.Pert.liftF_lower_ends

/-!
# `Work.Pert.pert2v2.waist_return_bound_low`

**The return translate `Φm ∘ Tt α` is BOUNDED on the lower part of the waist.**  For a
near-translation `F` on the lower gate `Qm Ξ α = Qreg (Ξ - 1/α) (-Ξ)` with a Fatou coordinate
`Φm`, exponentially close to `z ↦ z + ρ` (`‖ρ - 1‖ ≤ 1/32`) at the *lower* end,
there are `K C` such that every point `ς` of the waist `{|Re z| + 2 < |Im z| - Ξ}` below height
`-K` satisfies `‖Φm (Tt α ς) - Φm ς‖ ≤ C`.

This is the lower-end analogue of `Work.Pert.pert2v2.waist_return_bound_up`, and it is the
boundedness (not the limit) of `R̃_f - id` that the periodicity/Phragmén–Lindelöf pieces of the
assembly consume.

**The route.**  Write `dev z = Φm z - z/ρ` for the drift of `Φm` against the *end slope* `ρ`.
The waist hypothesis is exactly `ς ∈ Qm Ξ α ∧ Tt α ς ∈ Qm Ξ α` (`Tt_mem_Qm_iff` and
`Qm_inter_Qp`), so both points are legal arguments of `Φm`.  Contract's `FatouEnds` gives a
constant `c` with `dev z ≈ c` at the lower end, but its threshold is attached to the *centre*
`x` of a window `|z.re - x| ≤ 2`, so it cannot be applied "at `Re ς`" uniformly over the
unbounded waist.  The fix is to *walk* each of the two points `ς`, `Tt α ς` into the fixed
window `|Re| ≤ 2` while preserving the drift `dev` up to `1`:

* `walk_left_drift` (forward walk) for a point with `Re ≤ -2`,
* `walk_right_drift` (backward walk) for a point with `2 ≤ Re`,
* the middle case `-2 < Re < 2` needs no walk at all.

Both walks preserve `dev` up to `1` (the step defect `F w - w - ρ` is `≲ M e^{κ w.im}`, and the
walk stays at depth `≳ |w.im|/2`, so the telescoping sum is `< 1` for deep points).  Applying
`FatouEnds` at the single centre `x = 0` then pins the drift of the two *images* to the same
constant `c` within `2`, and the assembly

`Φm (Tt α ς) - Φm ς = (dev (Tt α ς) - c) - (dev ς - c) - 1/(αρ)`

gives the bound `‖1/(αρ)‖ + 5`.

Only `hF`, `hΞ`, `hα`, `hQAdm`, `hNT`, `hΦm` and `hdecL` are used; `Φp`, `hrel` and the upper
gate play no role in this bound (they belong to the *limit* statement, not to boundedness).

NOTE for the reader of the contract: as originally dispatched, the two hypotheses `hΦm`, `hΦp`
read `IsFatouCoordOn F (Qm Ξ α)`, which does not elaborate (`IsFatouCoordOn` takes the coordinate
as its second argument); the missing coordinate argument has been restored here, matching
`waist_return_bound_up`.  Nothing else in the statement was touched.
-/

namespace Work.Pert.pert2v2

open Complex Set

noncomputable section

theorem waist_return_bound_low {u : ℂ → ℂ} {σ α d : ℂ} {Ξ : ℝ} {F Φm Φp : ℂ → ℂ}
    (hF : MandelDim.FatouStatement) (hΞ : 0 < Ξ) (hα : MandelDim.InF1 α)
    (hQAdm : MandelDim.QAdm (some ((Ξ : ℂ) - 1 / α)) (some (-(Ξ : ℂ))))
    (hQAdmp : MandelDim.QAdm (some ((Ξ : ℂ))) (some (-(Ξ : ℂ) + 1 / α)))
    (hNT : MandelDim.NearTranslationL1 F (Work.Pert.Qm Ξ α))
    (hNTp : MandelDim.NearTranslationL1 F (Work.Pert.Qp Ξ α))
    (hΦm : MandelDim.IsFatouCoordOn F Φm (Work.Pert.Qm Ξ α))
    (hΦp : MandelDim.IsFatouCoordOn F Φp (Work.Pert.Qp Ξ α))
    (hrel : ∀ z ∈ Work.Pert.Qp Ξ α, Φm (Work.Pert.Tt α z) = Φp z + d)
    (hdecL : ∃ ρ : ℂ, ∃ M κ Y : ℝ, ‖ρ - 1‖ ≤ 1 / 32 ∧ 0 < M ∧ 0 < κ ∧
      ∀ z ∈ Work.Pert.Qm Ξ α, z.im < -Y → ‖F z - (z + ρ)‖ ≤ M * Real.exp (κ * z.im)) :
    ∃ K C : ℝ, ∀ ς : ℂ, |ς.re| + 2 < |ς.im| - Ξ → ς.im ≤ -K →
      ‖Φm (Work.Pert.Tt α ς) - Φm ς‖ ≤ C := by
  obtain ⟨ρ, M, κ, Y, hρ, hM, hκ, hdec⟩ := hdecL
  -- `𝓕₁` is preserved by inversion (strictly), so the waist is the symmetric window
  have hF1 : |(1 / α).im| < (1 / α).re := Work.Pert.abs_im_one_div_lt_re_one_div hα
  have hntOn : MandelDim.NearTranslationOn F (Work.Pert.Qm Ξ α) := hNT.1
  have habel : ∀ w ∈ Work.Pert.Qm Ξ α, F w ∈ Work.Pert.Qm Ξ α → Φm (F w) = Φm w + 1 :=
    hΦm.2.2
  -- ## the one-step lemmas of the walk, in the shape the walk lemmas want
  have hfwd : ∀ z ∈ Work.Pert.Qm Ξ α, 1 + 1 / 8 ≤ Work.Pert.margB_g Ξ z →
      F z ∈ Work.Pert.Qm Ξ α ∧ Φm (F z) = Φm z + 1 := fun z hz hroom =>
    fwdStep (Ξ := Ξ) (α := α) (F := F) (Φ := Φm) (fun w hw => (hntOn.2 w hw).1) hz hroom habel
  have hbwd : ∀ z ∈ Work.Pert.Qm Ξ α, 1 + 1 / 4 ≤ Work.Pert.margA_g Ξ α z →
      ∃ w : ℂ, ‖w - (z - 1)‖ ≤ 1 / 32 ∧ F w = z ∧ w ∈ Work.Pert.Qm Ξ α ∧ Φm w = Φm z - 1 :=
    fun z hz hroom => backStep_exists (Ξ := Ξ) (α := α) (F := F) (Φ := Φm)
      hntOn.1 (fun w hw => hntOn.2 w hw) hz hroom habel
  -- ## the two deep walks (left and right), preserving the drift `Φm - ·/ρ`
  obtain ⟨Yl, hYl⟩ := walk_left_drift (Ξ := Ξ) (α := α) (ρ := ρ) (M := M) (κ := κ) (Y := Y)
    (F := F) (Φ := Φm) hM hκ hρ hfwd hdec
  obtain ⟨Yr, hYr⟩ := walk_right_drift (Ξ := Ξ) (α := α) (ρ := ρ) (M := M) (κ := κ) (Y := Y)
    (F := F) (Φ := Φm) hM hκ hρ hbwd hdec
  -- ## the lower-end asymptotics of `Φm`, at the fixed centre `0`
  obtain ⟨c, hc⟩ := (hF.2.2.2.2.2 (some ((Ξ : ℂ) - 1 / α)) (some (-(Ξ : ℂ))) F Φm ρ M κ Y
      hQAdm hntOn hΦm hκ hρ).2 hdec
  obtain ⟨Yend, hYend⟩ := hc 0 1 (by norm_num)
  -- ## the constants
  set aa : ℝ := |(1 / α).im| + ‖(1 : ℂ) / α‖ with haa
  have haa0 : 0 ≤ aa := by rw [haa]; positivity
  have hB_le : (1 / α).im ≤ aa := by
    rw [haa]
    have h1 := le_abs_self ((1 / α).im)
    have h2 := norm_nonneg ((1 : ℂ) / α)
    linarith
  have hnegB_le : -aa ≤ (1 / α).im := by
    rw [haa]
    have h1 := neg_abs_le ((1 / α).im)
    have h2 := norm_nonneg ((1 : ℂ) / α)
    linarith
  have hA_le : (1 / α).re ≤ aa := by
    rw [haa]
    have h1 := Complex.abs_re_le_norm ((1 : ℂ) / α)
    have h2 := abs_nonneg ((1 / α).im)
    have h3 := le_abs_self ((1 / α).re)
    linarith
  set Kw : ℝ := max (max Yl Yr) 0 + 1 with hKw
  set Ke : ℝ := max Yend 0 + 1 with hKe
  set S : ℝ := 2 * aa + Ξ + 4 with hS
  have hKwpos : 0 < Kw := by rw [hKw]; linarith [le_max_right (max Yl Yr) 0]
  have hKepos : 0 < Ke := by rw [hKe]; linarith [le_max_right Yend 0]
  have hSpos : 0 < S := by rw [hS]; linarith
  have hYl_kw : Yl ≤ Kw := by
    rw [hKw]; linarith [le_max_left Yl Yr, le_max_left (max Yl Yr) 0]
  have hYr_kw : Yr ≤ Kw := by
    rw [hKw]; linarith [le_max_right Yl Yr, le_max_left (max Yl Yr) 0]
  have hYend_ke : Yend < Ke := by
    rw [hKe]; linarith [le_max_left Yend 0, le_max_right Yend 0]
  set K : ℝ := Kw + Ke + (S + 4 + 2 * max Yend 0) + (2 * aa + 2) with hKdef
  have hX0 : 0 ≤ S + 4 + 2 * max Yend 0 := by linarith [hSpos]
  have hY0 : 0 ≤ 2 * aa + 2 := by linarith
  have hKpos : 0 < K := by rw [hKdef]; linarith [hKwpos, hKepos, hX0, hY0]
  have hK_gt_Kw : Kw < K := by rw [hKdef]; linarith [hKepos, hX0, hY0]
  have hK_gt_Yend : Yend < K := by rw [hKdef]; linarith [hKwpos, hKepos, hYend_ke, hX0, hY0]
  have hK_gt_Yend_aa : Yend + aa < K := by
    rw [hKdef]
    linarith [hKwpos, hKepos, hYend_ke, hX0, hY0, haa0]
  have hK_gt_Kw_aa : Kw + aa < K := by
    rw [hKdef]
    linarith [hKepos, hX0, hY0, haa0]
  have hK_big : 2 * Yend + 3 * aa + 2 < K := by
    rw [hKdef, hS]
    have h1 : Yend ≤ max Yend 0 := le_max_left Yend 0
    linarith [hKwpos, hKepos, haa0, hΞ, h1]
  have hK_two : 2 * Yend + 2 < K := by linarith [hK_big, haa0]
  -- ## the walk to the fixed window `|Re| ≤ 2`, preserving the drift
  have hwalk : ∀ z : ℂ, z ∈ Work.Pert.Qm Ξ α → z.im ≤ -Kw →
      z.im + |z.re| / 2 + 2 < -Yend → z.im < -Yend →
      ∃ w : ℂ, w ∈ Work.Pert.Qm Ξ α ∧ |w.re| ≤ 2 ∧ w.im < -Yend ∧
        ‖(Φm w - w / ρ) - (Φm z - z / ρ)‖ ≤ 1 := by
    intro z hz hzle hfit hzend
    by_cases hleft : z.re ≤ -2
    · obtain ⟨w, hwQ, hwre, hwdrift, hwim⟩ := hYl z hz (by linarith [hzle, hYl_kw]) hleft
      exact ⟨w, hwQ, by rw [abs_le]; exact ⟨hwre.1, by linarith [hwre.2]⟩,
        by linarith [hwim, hfit], hwdrift⟩
    · by_cases hright : 2 ≤ z.re
      · obtain ⟨w, hwQ, hwre, hwdrift, hwim⟩ := hYr z hz (by linarith [hzle, hYr_kw]) hright
        exact ⟨w, hwQ, by rw [abs_le]; exact ⟨by linarith [hwre.1], hwre.2⟩,
          by linarith [hwim, hfit], hwdrift⟩
      · push Not at hleft hright
        exact ⟨z, hz, by rw [abs_le]; exact ⟨by linarith, by linarith⟩, hzend,
          by simp⟩
  refine ⟨K, ‖1 / (α * ρ)‖ + 5, ?_⟩
  intro ς hwaist hdeep
  -- ## the geometry of `ς`
  have hneg : ς.im < 0 := by linarith [hKpos]
  have hwaist' : |ς.re| < |ς.im| - Ξ := by linarith
  obtain ⟨hmem1, hmem2⟩ := (Work.Pert.mem_waist_iff hF1).mpr hwaist'
  have hre_bound : |ς.re| < -ς.im - Ξ - 2 := by
    have h := hwaist
    have habs : |ς.im| = -ς.im := abs_of_neg hneg
    rw [habs] at h
    linarith
  -- ## the height bookkeeping for the first point `ς`
  have hle_w₁ : ς.im ≤ -Kw := by linarith [hdeep, hK_gt_Kw]
  have hend_w₁ : ς.im < -Yend := by linarith [hdeep, hK_gt_Yend]
  have hfit_w₁ : ς.im + |ς.re| / 2 + 2 < -Yend := by
    have h1 : ς.im + |ς.re| / 2 + 2 < ς.im + (-ς.im - Ξ - 2) / 2 + 2 := by linarith
    have h2 : ς.im + (-ς.im - Ξ - 2) / 2 + 2 = ς.im / 2 - Ξ / 2 + 1 := by ring
    have h3 : ς.im / 2 - Ξ / 2 + 1 ≤ -K / 2 - Ξ / 2 + 1 := by linarith
    have h4 : -K / 2 - Ξ / 2 + 1 < -Yend := by linarith [hK_two, hΞ]
    linarith
  obtain ⟨w₁, hw₁Q, hw₁re, hw₁im, hw₁drift⟩ := hwalk ς hmem1 hle_w₁ hfit_w₁ hend_w₁
  -- ## the height bookkeeping for the second point `Tt α ς`
  have hTt_im : (Work.Pert.Tt α ς).im = ς.im - (1 / α).im := by
    simp only [Work.Pert.Tt, Complex.sub_im]
  have hTt_re : (Work.Pert.Tt α ς).re = ς.re - (1 / α).re := by
    simp only [Work.Pert.Tt, Complex.sub_re]
  have hA0 : 0 ≤ (1 / α).re := le_of_lt (lt_of_le_of_lt (abs_nonneg _) hF1)
  have hTt_absre : |(Work.Pert.Tt α ς).re| ≤ |ς.re| + (1 / α).re := by
    rw [hTt_re]
    calc |ς.re - (1 / α).re| ≤ |ς.re| + |(1 / α).re| := abs_sub _ _
      _ = |ς.re| + (1 / α).re := by rw [abs_of_nonneg hA0]
  have hle_w₂ : (Work.Pert.Tt α ς).im ≤ -Kw := by
    rw [hTt_im]; linarith [hdeep, hK_gt_Kw_aa, hnegB_le]
  have hend_w₂ : (Work.Pert.Tt α ς).im < -Yend := by
    rw [hTt_im]; linarith [hdeep, hK_gt_Yend_aa, hnegB_le]
  have hfit_w₂ : (Work.Pert.Tt α ς).im + |(Work.Pert.Tt α ς).re| / 2 + 2 < -Yend := by
    rw [hTt_im]
    have h1 : ς.im - (1 / α).im + |(Work.Pert.Tt α ς).re| / 2 + 2
        ≤ ς.im - (1 / α).im + (|ς.re| + (1 / α).re) / 2 + 2 := by linarith
    have h2 : ς.im - (1 / α).im + (|ς.re| + (1 / α).re) / 2 + 2
        < ς.im / 2 - Ξ / 2 + ((1 / α).re / 2 - (1 / α).im) + 1 := by linarith
    have h3 : ((1 / α).re / 2 - (1 / α).im) ≤ 3 * aa / 2 := by linarith
    have h4 : ς.im / 2 - Ξ / 2 + ((1 / α).re / 2 - (1 / α).im) + 1
        ≤ -K / 2 - Ξ / 2 + 3 * aa / 2 + 1 := by linarith
    have h5 : -K / 2 - Ξ / 2 + 3 * aa / 2 + 1 < -Yend := by linarith [hK_big, hΞ]
    linarith
  obtain ⟨w₂, hw₂Q, hw₂re, hw₂im, hw₂drift⟩ :=
    hwalk (Work.Pert.Tt α ς) hmem2 hle_w₂ hfit_w₂ hend_w₂
  -- ## the two window values are within `1` of the same end constant
  have hc₁ : ‖(Φm w₁ - w₁ / ρ) - c‖ < 1 := by
    have hre : |w₁.re - 0| ≤ 2 := by rw [sub_zero]; exact hw₁re
    exact hYend w₁ hw₁Q hw₁im hre
  have hc₂ : ‖(Φm w₂ - w₂ / ρ) - c‖ < 1 := by
    have hre : |w₂.re - 0| ≤ 2 := by rw [sub_zero]; exact hw₂re
    exact hYend w₂ hw₂Q hw₂im hre
  -- ## hence the drift at the two original points is within `2` of `c`
  have hdrift₁ : ‖(Φm ς - ς / ρ) - c‖ ≤ 2 := by
    have hsplit : (Φm ς - ς / ρ) - c
        = ((Φm ς - ς / ρ) - (Φm w₁ - w₁ / ρ)) + ((Φm w₁ - w₁ / ρ) - c) := by ring
    rw [hsplit]
    have h1 : ‖(Φm ς - ς / ρ) - (Φm w₁ - w₁ / ρ)‖ ≤ 1 := by
      rw [norm_sub_rev]; exact hw₁drift
    have h2 := norm_add_le ((Φm ς - ς / ρ) - (Φm w₁ - w₁ / ρ)) ((Φm w₁ - w₁ / ρ) - c)
    linarith
  have hdrift₂ : ‖(Φm (Work.Pert.Tt α ς) - Work.Pert.Tt α ς / ρ) - c‖ ≤ 2 := by
    have hsplit : (Φm (Work.Pert.Tt α ς) - Work.Pert.Tt α ς / ρ) - c
        = ((Φm (Work.Pert.Tt α ς) - Work.Pert.Tt α ς / ρ) - (Φm w₂ - w₂ / ρ))
          + ((Φm w₂ - w₂ / ρ) - c) := by ring
    rw [hsplit]
    have h1 : ‖(Φm (Work.Pert.Tt α ς) - Work.Pert.Tt α ς / ρ) - (Φm w₂ - w₂ / ρ)‖ ≤ 1 := by
      rw [norm_sub_rev]; exact hw₂drift
    have h2 := norm_add_le ((Φm (Work.Pert.Tt α ς) - Work.Pert.Tt α ς / ρ) - (Φm w₂ - w₂ / ρ))
      ((Φm w₂ - w₂ / ρ) - c)
    linarith
  -- ## the value comparison: two drifts differ by the deck translation `-1/(αρ)`
  have hkey : Φm (Work.Pert.Tt α ς) - Φm ς
      = ((Φm (Work.Pert.Tt α ς) - Work.Pert.Tt α ς / ρ) - c)
        - ((Φm ς - ς / ρ) - c) - 1 / (α * ρ) := by
    have hTt : Work.Pert.Tt α ς = ς - 1 / α := rfl
    rw [hTt]
    ring
  rw [hkey]
  have hsub := norm_sub_le ((Φm (Work.Pert.Tt α ς) - Work.Pert.Tt α ς / ρ) - c)
    ((Φm ς - ς / ρ) - c)
  calc ‖((Φm (Work.Pert.Tt α ς) - Work.Pert.Tt α ς / ρ) - c)
        - ((Φm ς - ς / ρ) - c) - 1 / (α * ρ)‖
      ≤ ‖((Φm (Work.Pert.Tt α ς) - Work.Pert.Tt α ς / ρ) - c)
        - ((Φm ς - ς / ρ) - c)‖ + ‖1 / (α * ρ)‖ := norm_sub_le _ _
    _ ≤ (2 + 2) + ‖1 / (α * ρ)‖ := by linarith
    _ ≤ ‖1 / (α * ρ)‖ + 5 := by linarith [norm_nonneg (1 / (α * ρ))]

end

end Work.Pert.pert2v2
