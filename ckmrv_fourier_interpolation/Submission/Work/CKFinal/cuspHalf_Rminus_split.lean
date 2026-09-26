import Mathlib
import Submission.Work.Asymptotics.TSasm.layerSemi_Tregion
import Submission.Work.Asymptotics.TSasm.cuspOneLowHalfTile_TS
import Submission.Work.Asymptotics.BlLow.Defs
import Submission.Work.Asymptotics.im_le_two_of_Tregion_TS

namespace Work.CKFinal

open UpperHalfPlane ModularGroup

/-!
# Splitting the cusp-`±1` half tile: the `τ - 1 ∈ Tregion` case

For `τ ∈ 𝒟` with `u := τ - 1 ∈ Tregion` (i.e. `u ∈ 𝒟`, `1/2 ≤ Im (S • u) ≤ 2`), the point `τ`
lies in one of three regions on which the layer seminorm bound is separately available:

* `τ ∈ Tregion` itself (`layerSemi_Tregion`);
* `τ ∈ blLowSet`, the low bad-line region `2/5 ≤ Im τ ≤ 1/2`, `|Re τ| > 3/4`
  (`LayerSemiBlLowTS`);
* the low strip `1/2 ≤ Im τ ≤ 2` with `Im (S • τ) < 1/2` (`layer_cuspHalf_Rminus_lowstrip`).

The mathematics is elementary.  Since `u = τ - 1` has `Re u = Re τ - 1 < 0`, the two
`Re u < 0` facts of `kernelTransform_seminorm_cuspHalf_TS_prelude` apply:

* `ts_not_two_le_im_S_vadd_one`: `¬ 2 ≤ Im (S • (1 + u)) = Im (S • τ)`, so `Im (S • τ) < 2`
  always;
* `ts_lt_quarter_of_im_S_vadd_one`: if in addition `Im u = Im τ < 1/2` and
  `Im (S • (1 + u)) = Im (S • τ) < 1/2`, then `|Re u| < 1/4`, i.e. `Re τ > 3/4`.

Hence, if `Im τ ≥ 1/2` the third alternative holds unless `Im (S • τ) ≥ 1/2`, in which case
`τ ∈ Tregion`; and if `Im τ < 1/2`, then either `τ ∈ Tregion` (when `Im (S • τ) ≥ 1/2`), or
`Im τ ≥ 2/5` (by `im_two_fifths_of_mem_Tregion`, applied to `u ∈ Tregion` with the arc
inequality of `𝒟`) and `Re τ > 3/4`, so that `τ ∈ blLowSet`.
-/

theorem cuspHalf_Rminus_split {τ : UpperHalfPlane}
    (hτD : τ ∈ Work.Asymptotics.DomainD)
    (hwT : ((-1 : ℝ) +ᵥ τ) ∈ Work.Asymptotics.Tregion) :
    τ ∈ Work.Asymptotics.Tregion ∨ τ ∈ Work.Asymptotics.BlLow.blLowSet ∨
      ((1 : ℝ) / 2 ≤ τ.im ∧ τ.im ≤ 2 ∧
        ¬ ((1 : ℝ) / 2 ≤ (ModularGroup.S • τ).im)) := by
  have hτre : τ.re < 1 := (Work.Asymptotics.mem_DomainD.mp hτD).2.1
  -- `Re (τ - 1) < 0`, so the two `Re u < 0` inputs of the prelude apply to `u = τ - 1`.
  have hrew : (((-1 : ℝ) +ᵥ τ : UpperHalfPlane)).re < 0 := by
    rw [UpperHalfPlane.vadd_re]; linarith
  have hsu : (1 : ℝ) +ᵥ ((-1 : ℝ) +ᵥ τ) = τ := by rw [← add_vadd]; norm_num
  -- `Im (S • τ) < 2` (the `E`-case is empty for `Re u < 0`).
  have hnot2 : ¬ (2 ≤ (ModularGroup.S • τ).im) := by
    have h := Work.Asymptotics.ts_not_two_le_im_S_vadd_one ((-1 : ℝ) +ᵥ τ) hwT hrew
    rwa [hsu] at h
  have himu : (((-1 : ℝ) +ᵥ τ : UpperHalfPlane)).im = τ.im := UpperHalfPlane.vadd_im (-1) τ
  -- `Im τ ≤ 2`, because `τ - 1 ∈ Tregion`.
  have him2 : τ.im ≤ 2 := by
    rw [← himu]; exact Work.Asymptotics.im_le_two_of_Tregion_TS hwT
  have hlt2 : (ModularGroup.S • τ).im < 2 := not_le.mp hnot2
  rcases le_or_gt ((1 : ℝ) / 2) τ.im with hy | hy
  · rcases le_or_gt ((1 : ℝ) / 2) ((ModularGroup.S • τ).im) with hS | hS
    · exact Or.inl ⟨hτD, hS, le_of_lt hlt2⟩
    · exact Or.inr (Or.inr ⟨hy, him2, not_le.mpr hS⟩)
  · rcases le_or_gt ((1 : ℝ) / 2) ((ModularGroup.S • τ).im) with hS | hS
    · exact Or.inl ⟨hτD, hS, le_of_lt hlt2⟩
    · refine Or.inr (Or.inl ⟨hτD, ?_, le_of_lt hy, Or.inl ?_⟩)
      · rw [← himu]
        exact Work.Asymptotics.im_two_fifths_of_mem_Tregion hwT
          (Work.Asymptotics.ts_abs_re_lt_normSq_of_mem_DomainD hwT.1)
      · have hlt : |(((-1 : ℝ) +ᵥ τ : UpperHalfPlane)).re| < 1 / 4 :=
          Work.Asymptotics.ts_lt_quarter_of_im_S_vadd_one ((-1 : ℝ) +ᵥ τ) hwT hrew
            (by rw [himu]; exact hy)
            (by rw [hsu]; exact hS)
        have h2 := (abs_lt.mp hlt).1
        rw [UpperHalfPlane.vadd_re] at h2
        linarith

end Work.CKFinal
