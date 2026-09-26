import Mathlib
import Submission.Work.HFN.seminormK_cusp0_half
import Submission.Work.Asymptotics.KEpsilon
import Submission.Work.Asymptotics.kernelTransform_seminorm_cuspHalf_TS_prelude
import Submission.Work.Asymptotics.TSasm.layerSemi_Tregion

namespace Work.Asymptotics

open UpperHalfPlane ModularGroup
open scoped MatrixGroups UpperHalfPlane

/-!
# The `r`-seminorm bound for the CKMRV layer on the low half-funnel with negative real part

The target `Work.Asymptotics.layerSemi_lowHalfFunnelNegRe` bounds the `r`-seminorms of the CKMRV
layer `Work.Asymptotics.layer (Gcusp ℓ d) ℓ d w ·` uniformly on the region

  `R = {w ∈ 𝒟 : 1/2 ≤ Im w ≤ 2, Re w < 0}`.

Since `𝒟` sits in the strip `-1 < Re w < 1`, the region is the "low half" (`1/2 ≤ Im w ≤ 2`) of
the fundamental domain, cut down to the *left* half (`Re w < 0`); the closure meets `𝒟` only along
the bad line `Re w = -1` and at the tangency point `-1/2 + i/2`.

The region `R` is split into three parts, each handled by an already-established bound:

* `{Re w < -3/4}` — the bad-line neighbourhood `Work.Asymptotics.HalfFunnel.lowBadSet`; there the
  contour transform is controlled by the translate-pole decomposition of
  `Work.Asymptotics.HalfFunnel.lowRegion_badLine`, whose layer-side content is reproduced below.
* `{(S • w).im ≥ 1/2}` (automatically `≤ 2` because `Im w ≥ 1/2`) — the cusp-`0` half tile
  `Tregion = {w ∈ 𝒟 : 1/2 ≤ Im (S • w) ≤ 2}`, handled by `Work.Asymptotics.layerSemi_Tregion`.
* the remaining set — there `(S • w).im < 1/2` together with `-3/4 ≤ Re w` forces `Im w > 3/2`, so
  the region lies in the compact box `lowNegBox = {-3/4 ≤ Re w ≤ 1/2, 3/2 ≤ Im w ≤ 2} ⊆ 𝒟`, where
  the compact part of CKMRV Proposition 4.6 (`Work.Asymptotics.layer_seminorm_on_compact`) gives
  the bound.
-/

/-! ## Elementary geometry of `R` -/

/-- `Im (S • w) = Im w / ‖w‖²`. -/
lemma lowNeg_im_S_smul (w : ℍ) :
    (ModularGroup.S • w).im = w.im / ‖(w : ℂ)‖ ^ 2 :=
  ts_im_S_smulTS w

/-- On `{1/2 ≤ Im w}` the `S`-image stays below height `2`: `Im (S • w) ≤ 2`. -/
lemma im_S_smul_le_two_of_half_le_im {w : ℍ} (hy : (1 : ℝ) / 2 ≤ w.im) :
    (ModularGroup.S • w).im ≤ 2 := by
  rw [lowNeg_im_S_smul]
  have hpos : (0 : ℝ) < ‖(w : ℂ)‖ ^ 2 := by
    have hne : (w : ℂ) ≠ 0 := w.ne_zero
    positivity
  rw [div_le_iff₀ hpos]
  have hsq : ‖(w : ℂ)‖ ^ 2 = w.re ^ 2 + w.im ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    simp only [UpperHalfPlane.coe_re, UpperHalfPlane.coe_im]
    ring
  rw [hsq]
  nlinarith [hy, sq_nonneg w.re, sq_nonneg w.im, w.im_pos,
    mul_nonneg (by linarith : (0 : ℝ) ≤ 2 * w.im - 1) (le_of_lt w.im_pos)]

/-- The compact box containing the "far" part of `R`. -/
def lowNegBox : Set ℍ :=
  {w : ℍ | -(3 : ℝ) / 4 ≤ w.re ∧ w.re ≤ 1 / 2 ∧ (3 : ℝ) / 2 ≤ w.im ∧ w.im ≤ 2}

lemma isClosed_lowNegBox : IsClosed lowNegBox := by
  have h1 : IsClosed {w : ℍ | -(3 : ℝ) / 4 ≤ w.re} :=
    isClosed_le continuous_const UpperHalfPlane.continuous_re
  have h2 : IsClosed {w : ℍ | w.re ≤ 1 / 2} :=
    isClosed_le UpperHalfPlane.continuous_re continuous_const
  have h3 : IsClosed {w : ℍ | (3 : ℝ) / 2 ≤ w.im} :=
    isClosed_le continuous_const UpperHalfPlane.continuous_im
  have h4 : IsClosed {w : ℍ | w.im ≤ 2} :=
    isClosed_le UpperHalfPlane.continuous_im continuous_const
  have h : lowNegBox = {w : ℍ | -(3 : ℝ) / 4 ≤ w.re} ∩ {w : ℍ | w.re ≤ 1 / 2} ∩
      {w : ℍ | (3 : ℝ) / 2 ≤ w.im} ∩ {w : ℍ | w.im ≤ 2} := by
    ext w; simp [lowNegBox, and_assoc]
  rw [h]
  exact ((h1.inter h2).inter h3).inter h4

lemma isBounded_lowNegBox : Bornology.IsBounded lowNegBox := by
  rw [Metric.isBounded_iff_subset_closedBall (⟨Complex.I, by simp⟩ : ℍ)]
  refine ⟨3, fun w hw => ?_⟩
  obtain ⟨h1, h2, h3, h4⟩ := hw
  rw [Metric.mem_closedBall]
  have hstep : dist w (⟨Complex.I, by simp⟩ : ℍ)
      ≤ ‖(w : ℂ) - Complex.I‖ / Real.sqrt (w.im * 1) := by
    have hh := UpperHalfPlane.dist_le_dist_coe_div_sqrt w (⟨Complex.I, by simp⟩ : ℍ)
    rw [dist_eq_norm] at hh
    rw [show (↑(⟨Complex.I, by simp⟩ : ℍ) : ℂ) = Complex.I from rfl,
        show (⟨Complex.I, by simp⟩ : ℍ).im = 1 from rfl] at hh
    simpa using hh
  have hnum : ‖(w : ℂ) - Complex.I‖ ≤ 7 / 4 := by
    have h := Complex.norm_le_abs_re_add_abs_im ((w : ℂ) - Complex.I)
    rw [show ((w : ℂ) - Complex.I).re = w.re by simp,
        show ((w : ℂ) - Complex.I).im = w.im - 1 by simp] at h
    have hre' : |w.re| ≤ 3 / 4 := abs_le.mpr ⟨by linarith, by linarith⟩
    have him' : |w.im - 1| ≤ 1 := abs_le.mpr ⟨by linarith, by linarith⟩
    linarith
  have hden : (1 : ℝ) ≤ Real.sqrt (w.im * 1) := by
    rw [Real.one_le_sqrt]; linarith
  calc dist w (⟨Complex.I, by simp⟩ : ℍ) ≤ ‖(w : ℂ) - Complex.I‖ / Real.sqrt (w.im * 1) :=
        hstep
    _ ≤ (7 / 4) / 1 := div_le_div₀ (by norm_num) hnum (by norm_num) hden
    _ ≤ 3 := by norm_num

lemma isCompact_lowNegBox : IsCompact lowNegBox := by
  rw [Metric.isCompact_iff_isClosed_bounded]
  exact ⟨isClosed_lowNegBox, isBounded_lowNegBox⟩

lemma lowNegBox_subset_DomainD : lowNegBox ⊆ DomainD := by
  intro w hw
  obtain ⟨h1, h2, h3, h4⟩ := hw
  rw [mem_DomainD]
  refine ⟨by linarith, by linarith, ?_, ?_⟩
  · have h := Complex.abs_im_le_norm ((w : ℂ) - (1 / 2 : ℂ))
    have him : ((w : ℂ) - (1 / 2 : ℂ)).im = w.im := by simp
    rw [him, abs_of_pos (by linarith : (0 : ℝ) < w.im)] at h
    linarith
  · have h := Complex.abs_im_le_norm ((w : ℂ) + (1 / 2 : ℂ))
    have him : ((w : ℂ) + (1 / 2 : ℂ)).im = w.im := by simp
    rw [him, abs_of_pos (by linarith : (0 : ℝ) < w.im)] at h
    linarith

/-- **The "far" part of `R` lands in the compact box.**  If `-3/4 ≤ Re w`, `1/2 ≤ Im w ≤ 2` and
`Im (S • w) < 1/2`, then `Im w > 3/2`, so `w ∈ lowNegBox`. -/
lemma mem_lowNegBox_of {w : ℍ} (hre0 : w.re < 0) (hre_lo : -(3 : ℝ) / 4 ≤ w.re)
    (him1 : (1 : ℝ) / 2 ≤ w.im) (him2 : w.im ≤ 2)
    (himS : (ModularGroup.S • w).im < 1 / 2) : w ∈ lowNegBox := by
  refine ⟨hre_lo, by linarith, ?_, him2⟩
  rw [lowNeg_im_S_smul] at himS
  have hpos : (0 : ℝ) < ‖(w : ℂ)‖ ^ 2 := by
    have hne : (w : ℂ) ≠ 0 := w.ne_zero
    positivity
  rw [div_lt_iff₀ hpos] at himS
  have hsq : ‖(w : ℂ)‖ ^ 2 = w.re ^ 2 + w.im ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    simp only [UpperHalfPlane.coe_re, UpperHalfPlane.coe_im]
    ring
  rw [hsq] at himS
  have hkey : 1 < w.re ^ 2 + (w.im - 1) ^ 2 := by nlinarith [himS]
  have hre2 : w.re ^ 2 ≤ 9 / 16 := by nlinarith [hre_lo, hre0]
  have h1 : 7 / 16 < (w.im - 1) ^ 2 := by nlinarith [hkey, hre2]
  by_contra hcon
  push_neg at hcon
  have h2 : (w.im - 1) ^ 2 ≤ 1 / 4 := by nlinarith [hcon, him1]
  linarith

/-! ## The bad-line layer bound -/

/-- **The `r`-seminorm bound for the CKMRV layer on the bad-line region `lowBadSet`.**  This is
the layer-side content of `Work.Asymptotics.HalfFunnel.lowRegion_badLine`: the explicit
translate-pole layer `Work.Asymptotics.blLowF2` agrees with `paperLayer (Gcusp ℓ d)` on
`lowBadSet` (`Work.Asymptotics.HalfFunnel.lowF2_eq_paperLayer`) and its seminorms are bounded
(`Work.Asymptotics.blLowF2_seminorm`). -/
theorem layer_lowBadSet_seminorm (ℓ : Work.Kernels.LogLambdaData) (d : ℕ)
    (hd : d = 8 ∨ d = 24) :
    ∀ k l : ℕ, ∃ C : ℝ, 0 ≤ C ∧
      ∀ (τ : UpperHalfPlane) (r : ℝ), Work.Asymptotics.HalfFunnel.lowBadSet τ →
        (|r| ^ k) * ‖iteratedDeriv l (fun s : ℝ =>
          layer (Gcusp ℓ d) ℓ d τ s) r‖ ≤ C := by
  intro k l
  obtain ⟨Cks, hCks, hks⟩ := Work.HFN.HalfFunnel.lowBad_kernel_spike_b ℓ d hd
  obtain ⟨Cdec, hCdec, hdec1, hdec2⟩ :=
    Work.HFN.HalfFunnel.lowBad_spike_b_adapter ℓ d hCks hks
  obtain ⟨Ct, Mt, hCt, hMt, htail⟩ := Work.HFN.HalfFunnel.lowBad_Aexp_tail ℓ d hd
  obtain ⟨C, hC, hb⟩ := Work.HFN.blLowF2_seminorm ℓ d hd hCdec hdec1 hdec2
    ⟨Ct, Mt, hCt, hMt, htail⟩
    (fun m N => Work.Asymptotics.HalfFunnel.lowBad_PhiSpike_deriv ℓ d hd m N)
    (fun m N => Work.HFN.HalfFunnel.lowBad_Phi12_deriv ℓ d hd Cdec hCdec hdec1 m N)
    k l
  refine ⟨C, hC, fun τ r hτ => ?_⟩
  have hfun : (fun s : ℝ => layer (Gcusp ℓ d) ℓ d τ s) = fun s : ℝ => Work.HFN.blLowF2 ℓ d τ s := by
    funext s
    rw [layer, Work.HFN.blLowF2]
    by_cases hs : s = 0
    · rw [if_pos hs, if_pos hs]
    · rw [if_neg hs, if_neg hs]
      exact (Work.HFN.HalfFunnel.lowF2_eq_paperLayer ℓ d hd Cdec hCdec hdec1 hdec2
        τ s hτ).symm
  rw [hfun]
  exact hb τ r hτ

/-! ## The target -/

theorem layerSemi_lowHalfFunnelNegRe (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24) :
    ∀ k l : ℕ, ∃ C : ℝ, 0 ≤ C ∧
      ∀ (w : UpperHalfPlane) (r : ℝ), w ∈ Work.Asymptotics.DomainD → (1 : ℝ) / 2 ≤ w.im →
        w.im ≤ 2 → w.re < 0 →
        (|r| ^ k) * ‖iteratedDeriv l (fun s : ℝ =>
          Work.Asymptotics.layer (Work.Asymptotics.Gcusp ℓ d) ℓ d w s) r‖ ≤ C := by
  intro k l
  have hG : ∀ i j : Fin 2,
      Work.Kernels.ModerateGrowthOn Work.Asymptotics.DomainD (Work.Asymptotics.Gcusp ℓ d i j) :=
    fun i j => Work.HFN.Gcusp_moderate ℓ d i j
  have h8 : d = 8 → ∀ j : Fin 2, Work.Asymptotics.Gcusp ℓ d 1 j = 0 := by
    intro h8d j
    rw [Work.Asymptotics.Gcusp, if_pos h8d]
    funext τ
    fin_cases j <;> simp [Work.Asymptotics.Gcusp8]
  -- ### the bad-line part
  obtain ⟨CA, hCA, hbA⟩ := layer_lowBadSet_seminorm ℓ d hd k l
  -- ### the cusp-`0` half tile `Tregion`
  obtain ⟨CB, hCB, hbB⟩ := Work.Asymptotics.layerSemi_Tregion ℓ d hd k l
  -- ### the compact box
  obtain ⟨CC, hCC, hbC⟩ := Work.HFN.layer_seminorm_on_compact ℓ d hd
    (Work.Asymptotics.Gcusp ℓ d) hG h8 isCompact_lowNegBox lowNegBox_subset_DomainD
    (Work.Asymptotics.MFix.Kaxis_local_flat ℓ d hd isCompact_lowNegBox lowNegBox_subset_DomainD)
    (Work.HFN.cusp_expansion_of_kernel ℓ d hd isCompact_lowNegBox lowNegBox_subset_DomainD)
    k l
  refine ⟨CA + CB + CC, by linarith, ?_⟩
  intro w r hwD hlo hhi hre
  have hSle2 : (ModularGroup.S • w).im ≤ 2 := im_S_smul_le_two_of_half_le_im hlo
  by_cases hT : (1 : ℝ) / 2 ≤ (ModularGroup.S • w).im
  · exact le_trans (hbB w r ⟨hwD, hT, hSle2⟩) (by linarith)
  · push_neg at hT
    by_cases hbad : w.re < -(3 : ℝ) / 4
    · exact le_trans (hbA w r ⟨hwD, hlo, hhi, Or.inr (by linarith [hbad])⟩) (by linarith)
    · push_neg at hbad
      have hmem := mem_lowNegBox_of hre hbad hlo hhi hT
      exact le_trans (hbC w r hmem) (by linarith)

end Work.Asymptotics
