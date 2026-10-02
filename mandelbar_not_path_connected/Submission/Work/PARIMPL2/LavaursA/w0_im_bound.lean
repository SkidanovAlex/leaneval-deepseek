/-
Copyright: subproject `Submission/Work/PARIMPL2/` of `mandelbar_not_path_connected`.

# `Work.PARIMPL2.LavaursA.w0_im_bound` — the imaginary part of the chart coordinate is controlled

The attracting flower coordinate `φa` of `Work.FlowerGlue2.AttrCompare` satisfies, on its petal
and at depth `Re (w0 P z) > A.N`,

  `φa z = approxCoord (P.κ c₀) (w0 P z) + A.sa + O(1/Re (w0 P z))`,

where `approxCoord κ w = w − κ log w`.  Taking imaginary parts, this reads

  `Im (w0 P z) = Im (φa z) − Im (A.sa) + Im (κ log (w0 P z)) + O(1)`,

and since `‖log w‖ ≤ log‖w‖ + π` while `‖w‖ ≤ Re w + |Im w|`, the term `Im (κ log (w0 P z))`
is of size `O(log(1 + Re (w0 P z)))` with coefficient `‖P.κ c₀‖`.  Hence, whenever the imaginary
part of `φa z` is bounded by `H`, the imaginary part of the chart coordinate `w0 P z` obeys

  `|Im (w0 P z)| ≤ B + ‖P.κ c₀‖ log (1 + Re (w0 P z)) + H + |Im (A.sa)|`

for a constant `B` depending only on the data `P`, `A` and `H` (and not on `z`).

The proof splits on whether `|Im w|` is at most `1` (then it is bounded by the constant `B`) or
larger (then `‖w‖ ≥ 1`, the real part of the logarithm is nonnegative, and the self-referential
inequality `|Im w| ≤ D + ‖κ‖ log|Im w|` forces `|Im w|` to be bounded by a constant, unless
`|Im w| ≤ 1 + Re w` in which case the logarithm is already controlled by `log (1 + Re w)`).

## Contents

* `exists_bound_le_add_mul_log` — the real-analysis tool `t ≤ D + c log t ⟹ t ≤ M`;
* `w0_im_bound_aux` — the statement with the comparison datum abstracted away;
* `w0_im_bound` — the requested lemma.
-/
import Mathlib
import Submission.Work.PARIMPL2.Lavaurs.Defs
import Submission.Work.FlowerGlue2.Defs

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

open Classical Filter Set Metric
open scoped Topology

noncomputable section

namespace Work.PARIMPL2.LavaursA

/-! ## The real-analysis tool -/

/-- **A bound for `t > 0` with `t ≤ D + c log t`.**  For every `c ≥ 0` and every real `D` there is
a constant `M` with `t ≤ D + c · log t ⟹ t ≤ M` for all `t > 0` (`log` is dominated by the
identity, so `t − c log t → +∞` along `+∞`). -/
theorem exists_bound_le_add_mul_log {c D : ℝ} (hc : 0 ≤ c) :
    ∃ M : ℝ, ∀ t : ℝ, 0 < t → t ≤ D + c * Real.log t → t ≤ M := by
  have hg : Tendsto (fun t : ℝ => Real.log t / t) atTop (𝓝 0) :=
    Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero
  have hpos : 0 < 1 / (2 * (c + 1)) := by positivity
  have hev : ∀ᶠ t in atTop, Real.log t / t ≤ 1 / (2 * (c + 1)) :=
    hg.eventually (eventually_le_nhds hpos)
  obtain ⟨T₀, hT₀⟩ := eventually_atTop.mp hev
  refine ⟨max (max T₀ 1) (2 * D), ?_⟩
  intro t ht hle
  rcases le_or_gt t (max T₀ 1) with hT | hT
  · exact le_trans hT (le_max_left _ _)
  · have hlog := hT₀ t (le_trans (le_max_left T₀ 1) hT.le)
    rw [div_le_iff₀ ht] at hlog
    have hclog : c * Real.log t ≤ t / 2 := by
      have h1 : c * Real.log t ≤ c * ((1 / (2 * (c + 1))) * t) :=
        mul_le_mul_of_nonneg_left hlog hc
      have h2 : c * ((1 / (2 * (c + 1))) * t) ≤ t / 2 := by
        rw [show c * ((1 / (2 * (c + 1))) * t) = (c / (2 * (c + 1))) * t by ring]
        have hc1 : c / (2 * (c + 1)) ≤ 1 / 2 := by
          rw [div_le_iff₀ (by positivity : (0:ℝ) < 2 * (c + 1))]
          linarith
        calc (c / (2 * (c + 1))) * t ≤ (1 / 2) * t :=
              mul_le_mul_of_nonneg_right hc1 (le_of_lt ht)
          _ = t / 2 := by ring
      linarith
    have h2D : t ≤ 2 * D := by linarith
    exact le_trans h2D (le_max_right _ _)

/-! ## The statement with the comparison datum abstracted away -/

/-- **The imaginary-part bound, abstract form.**  Fix `κ sa : ℂ`, `K N H : ℝ` with `N > 0`,
`K ≥ 0`.  There is a constant `B > 0` such that every `w φ : ℂ` with `Re w > N`,
`|Im φ| ≤ H` and `‖φ − (approxCoord κ w + sa)‖ ≤ K / Re w` satisfies
`|Im w| ≤ B + ‖κ‖ log (1 + Re w) + H + |Im sa|`. -/
theorem w0_im_bound_aux (κ sa : ℂ) (K N H : ℝ) (hN : 0 < N) (hK : 0 ≤ K) :
    ∃ B : ℝ, 0 < B ∧ ∀ (w φ : ℂ), N < w.re → |φ.im| ≤ H →
      ‖φ - (Work.FatouCoord.approxCoord κ w + sa)‖ ≤ K / w.re →
      |w.im| ≤ B + ‖κ‖ * Real.log (1 + w.re) + H + |sa.im| := by
  set c : ℝ := ‖κ‖ with hcdef
  have hc : 0 ≤ c := by rw [hcdef]; exact norm_nonneg κ
  set C₁ : ℝ := H + |sa.im| + K / N + c * Real.pi with hC₁
  set D : ℝ := C₁ + c * Real.log 2 with hD
  obtain ⟨M, hM⟩ := exists_bound_le_add_mul_log (c := c) (D := D) hc
  refine ⟨max 1 (max D M), lt_of_lt_of_le one_pos (le_max_left _ _), ?_⟩
  intro w φ hNw hφ hnorm
  have hH0 : 0 ≤ H := le_trans (abs_nonneg φ.im) hφ
  have ha_pos : 0 < w.re := lt_trans hN hNw
  have herr : ‖φ - (w - κ * Complex.log w + sa)‖ ≤ K / w.re := by
    simpa only [Work.FatouCoord.approxCoord] using hnorm
  have hdecomp : w = φ - sa + κ * Complex.log w - (φ - (w - κ * Complex.log w + sa)) := by ring
  have him : w.im = φ.im - sa.im + (κ * Complex.log w).im
      - (φ - (w - κ * Complex.log w + sa)).im := by
    have h := congrArg Complex.im hdecomp
    simpa only [Complex.add_im, Complex.sub_im] using h
  have herr_im : |(φ - (w - κ * Complex.log w + sa)).im| ≤ K / N := by
    have h1 : |(φ - (w - κ * Complex.log w + sa)).im| ≤
        ‖φ - (w - κ * Complex.log w + sa)‖ := Complex.abs_im_le_norm _
    have h3 : K / w.re ≤ K / N := div_le_div_of_nonneg_left hK hN (le_of_lt hNw)
    linarith
  -- the key inequality, valid as soon as `|Im w| > 1`
  have key : 1 < |w.im| → |w.im| ≤ C₁ + c * Real.log (w.re + |w.im|) := by
    intro hb1
    have hwn : 1 < ‖w‖ := lt_of_lt_of_le hb1 (Complex.abs_im_le_norm w)
    have hlog_im : |(κ * Complex.log w).im| ≤ c * (Real.log ‖w‖ + Real.pi) := by
      have h1 : |(κ * Complex.log w).im| ≤ ‖κ * Complex.log w‖ := Complex.abs_im_le_norm _
      have h2 : ‖κ * Complex.log w‖ = c * ‖Complex.log w‖ := by rw [norm_mul, hcdef]
      have h3 : ‖Complex.log w‖ ≤ Real.log ‖w‖ + Real.pi := by
        have h4 : ‖Complex.log w‖ ≤ |(Complex.log w).re| + |(Complex.log w).im| :=
          Complex.norm_le_abs_re_add_abs_im _
        rw [Complex.log_re, Complex.log_im] at h4
        have h5 : |Real.log ‖w‖| = Real.log ‖w‖ :=
          abs_of_nonneg (Real.log_nonneg (le_of_lt hwn))
        have h6 : |w.arg| ≤ Real.pi := Complex.abs_arg_le_pi w
        rw [h5] at h4
        linarith
      calc |(κ * Complex.log w).im| ≤ ‖κ * Complex.log w‖ := h1
        _ = c * ‖Complex.log w‖ := h2
        _ ≤ c * (Real.log ‖w‖ + Real.pi) := mul_le_mul_of_nonneg_left h3 hc
    have hlog_norm : Real.log ‖w‖ ≤ Real.log (w.re + |w.im|) := by
      apply Real.log_le_log
      · exact lt_trans zero_lt_one hwn
      · have h := Complex.norm_le_abs_re_add_abs_im w
        rw [abs_of_pos ha_pos] at h
        exact h
    have him_bound : |w.im| ≤ H + |sa.im| + K / N + |(κ * Complex.log w).im| := by
      rw [him]
      have h1 : |φ.im - sa.im + (κ * Complex.log w).im - (φ - (w - κ * Complex.log w + sa)).im|
          ≤ |φ.im - sa.im + (κ * Complex.log w).im|
            + |(φ - (w - κ * Complex.log w + sa)).im| := abs_sub _ _
      have h2 : |φ.im - sa.im + (κ * Complex.log w).im|
          ≤ |φ.im| + |sa.im| + |(κ * Complex.log w).im| := by
        have hh := abs_add_le (φ.im - sa.im) ((κ * Complex.log w).im)
        have h3 : |φ.im - sa.im| ≤ |φ.im| + |sa.im| := abs_sub _ _
        linarith
      linarith [h1, h2, herr_im, hφ]
    have hfin : |w.im| ≤ H + |sa.im| + K / N + c * (Real.log ‖w‖ + Real.pi) := by linarith
    calc |w.im| ≤ H + |sa.im| + K / N + c * (Real.log ‖w‖ + Real.pi) := hfin
      _ ≤ H + |sa.im| + K / N + c * (Real.log (w.re + |w.im|) + Real.pi) := by
          have := mul_le_mul_of_nonneg_left hlog_norm hc; linarith
      _ = C₁ + c * Real.log (w.re + |w.im|) := by rw [hC₁]; ring
  -- the case split
  rcases le_or_gt |w.im| 1 with hb1 | hb1
  · -- `|Im w| ≤ 1 ≤ B`
    calc |w.im| ≤ 1 := hb1
      _ ≤ max 1 (max D M) := le_max_left _ _
      _ ≤ max 1 (max D M) + c * Real.log (1 + w.re) + H + |sa.im| := by
          have h1 : 0 ≤ c * Real.log (1 + w.re) :=
            mul_nonneg hc (Real.log_nonneg (by linarith))
          linarith [abs_nonneg sa.im]
  · have keyb := key hb1
    rcases le_or_gt |w.im| (1 + w.re) with hle | hgt
    · -- `|Im w| ≤ 1 + Re w`: `log‖w‖ ≤ log 2 + log (1 + Re w)`
      have hlog_le : Real.log (w.re + |w.im|) ≤ Real.log 2 + Real.log (1 + w.re) := by
        have h1 : w.re + |w.im| ≤ 2 * (1 + w.re) := by linarith
        have h2 : Real.log (w.re + |w.im|) ≤ Real.log (2 * (1 + w.re)) :=
          Real.log_le_log (by linarith [abs_nonneg w.im, ha_pos]) h1
        rw [Real.log_mul (by norm_num) (by linarith)] at h2
        exact h2
      have hfin : |w.im| ≤ D + c * Real.log (1 + w.re) := by
        have h3 : c * Real.log (w.re + |w.im|) ≤ c * (Real.log 2 + Real.log (1 + w.re)) :=
          mul_le_mul_of_nonneg_left hlog_le hc
        rw [hD]
        linarith
      calc |w.im| ≤ D + c * Real.log (1 + w.re) := hfin
        _ ≤ max 1 (max D M) + c * Real.log (1 + w.re) + H + |sa.im| := by
            have h1 : D ≤ max 1 (max D M) := le_trans (le_max_left D M) (le_max_right 1 (max D M))
            linarith [abs_nonneg sa.im]
    · -- `|Im w| > 1 + Re w`: `log‖w‖ ≤ log 2 + log |Im w|`, which bounds `|Im w|` by `M`
      have hlog_le : Real.log (w.re + |w.im|) ≤ Real.log 2 + Real.log |w.im| := by
        have h1 : w.re + |w.im| ≤ 2 * |w.im| := by linarith [abs_nonneg w.im]
        have h2 : Real.log (w.re + |w.im|) ≤ Real.log (2 * |w.im|) :=
          Real.log_le_log (by linarith [abs_nonneg w.im, ha_pos]) h1
        rw [Real.log_mul (by norm_num) (ne_of_gt (by linarith : 0 < |w.im|))] at h2
        exact h2
      have hfin : |w.im| ≤ M := by
        apply hM |w.im| (by linarith)
        have h3 : c * Real.log (w.re + |w.im|) ≤ c * (Real.log 2 + Real.log |w.im|) :=
          mul_le_mul_of_nonneg_left hlog_le hc
        rw [hD]
        linarith
      calc |w.im| ≤ M := hfin
        _ ≤ max 1 (max D M) := le_trans (le_max_right D M) (le_max_right 1 (max D M))
        _ ≤ max 1 (max D M) + c * Real.log (1 + w.re) + H + |sa.im| := by
            have h1 : 0 ≤ c * Real.log (1 + w.re) :=
              mul_nonneg hc (Real.log_nonneg (by linarith))
            linarith [abs_nonneg sa.im]

/-! ## The requested lemma -/

theorem w0_im_bound {c₀ : ℂ} {d : Work.EL.RootParabolic c₀} (P : Work.PARIMPL.ParNormal d)
    {Pa : Set ℂ} {φa : ℂ → ℂ} (A : Work.FlowerGlue2.AttrCompare P Pa φa) (H : ℝ) :
    ∃ B : ℝ, 0 < B ∧ ∀ z ∈ Pa, A.N < (Work.PARIMPL2.w0 P z).re → |(φa z).im| ≤ H →
      |(Work.PARIMPL2.w0 P z).im| ≤
        B + ‖P.κ c₀‖ * Real.log (1 + (Work.PARIMPL2.w0 P z).re) + H + |A.sa.im| := by
  obtain ⟨B, hBpos, hB⟩ := w0_im_bound_aux (P.κ c₀) A.sa A.K A.N H A.N_pos A.K_nonneg
  refine ⟨B, hBpos, fun z hz hN hH => ?_⟩
  have hz_ne : z ≠ d.z₁ := by
    intro h
    rw [h] at hN
    simp only [Work.PARIMPL2.w0, sub_self, div_zero, Complex.zero_re] at hN
    linarith [A.N_pos]
  have hasymp : ‖φa z - (Work.FatouCoord.approxCoord (P.κ c₀) (Work.PARIMPL2.w0 P z) + A.sa)‖
      ≤ A.K / (Work.PARIMPL2.w0 P z).re := by
    have h := A.asymp z hz hz_ne (by simpa only [Work.PARIMPL2.w0, Work.FlowerGlue2.w0] using hN)
    simpa only [Work.FlowerGlue2.w0, Work.PARIMPL2.w0] using h
  exact hB (Work.PARIMPL2.w0 P z) (φa z) hN hH hasymp

end Work.PARIMPL2.LavaursA

end
