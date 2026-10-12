import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Submission.Work.BoseBoxFock.PCFU.Dchan_dzero_word_split
import Submission.Work.BoseFixB3.CS.Pieces.convScale_ge_of_norm_le
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.PCFU.chiScale_W1fun_slice_integrable`

**Bochner-integrability of the windowed slice of the `χ`-renormalised one-body kernel**

    z ↦ χ_ℓ(z) · W₁(u − z),      W₁ = W1fun v h ℓ = wScaled ℓ (g₀ v h),

for `ℓ > 0` and for *every* `u` with `χ_ℓ(u) ≠ 0`.

## Why the hypothesis `χ_ℓ(u) ≠ 0` is exactly what is needed

The corpus's `g₀ = v(1−ω)` is only *locally* integrable under `ScatSol v`
(`IsScatteringSolution.rhs_integrable`) — the potential need not even have compact
support — and the renormalisation factor `(χ⋆χ)_ℓ = convScale ℓ` is **not** bounded
below on its whole support: `(χ⋆χ)(w) = 0` for `‖w‖ ≥ 1`, so the quotient
`g₀/(χ⋆χ)_ℓ` blows up near the sphere `‖·‖ = ℓ`.  The cutoff saves the day on the
slice: `χ_ℓ(u) ≠ 0` forces `‖u‖ < ℓ/2` (`chiScale_ne_zero_iff`), and `χ_ℓ(z) ≠ 0`
forces `‖z‖ < ℓ/2`, so the argument `u − z` of the kernel always lies in the
*closed* ball of radius `r := ‖u‖ + ℓ/2 < ℓ`, where the (continuous) factor
`(χ⋆χ)_ℓ` is bounded below by a positive constant `m`.

The slice is therefore dominated pointwise by `(A/m)·|g₀(u − ·)|`, and — after
replacing `g₀` by its truncation `1_{‖·‖ ≤ 2ℓ}·g₀` (which agrees with `g₀` on the
relevant ball and is *globally* integrable, `integrable_indicator_g0`) — that
dominating function is integrable by translation invariance
(`Integrable.comp_sub_left`).  The whole content is thus the lower bound
`convScale_lower_closedBall` on a closed ball of radius `< ℓ`, proved here from the
strict positivity of `χ⋆χ` on the open unit ball (`conv3_chi_pos_of_norm_lt_one`,
the point `w/2` lies in the support of both factors) and compactness.

The proof of the slice bound is the same argument as the (private) fibre bound
`Work.BoseFixB1B.integrable_fibre_g0`; the difference is that here the numerator is
only *locally* integrable, which is why the truncation step is needed.
-/

namespace Work.BoseBoxFock.PCFU

open MeasureTheory Metric Filter
open scoped Topology Real ENNReal

local notation "E3" => EuclideanSpace ℝ (Fin 3)

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## 1. The support of the cutoff -/

/-- The corpus bump `χ` vanishes outside the closed ball of radius `1/2`. -/
lemma sliceAux_chi_eq_zero_of_half_le_norm (y : E3) (hy : 1 / 2 ≤ ‖y‖) :
    Submission.BoseGases.chi y = 0 := by
  have h0 : Submission.BoseGases.chiBase y = 0 := by
    rw [Submission.BoseGases.chiBase]
    exact Submission.BoseGases.chiBump.zero_of_le_dist
      (by simpa [Submission.BoseGases.chiBump, dist_eq_norm] using hy)
  simp [Submission.BoseGases.chi, h0]

/-- If `χ_ℓ(x) ≠ 0` then `‖x‖ < ℓ/2` — the *strict* form of
`KernelIds.chiScale_support_le`. -/
lemma sliceAux_chiScale_ne_zero_imp_norm_lt {ℓ : ℝ} (hℓ : 0 < ℓ) {x : E3}
    (hx : Submission.BoseGases.chiScale ℓ x ≠ 0) : ‖x‖ < ℓ / 2 := by
  have h1 : ‖(ℓ⁻¹ : ℝ) • x‖ < 1 / 2 := by
    by_contra hcon
    exact hx (sliceAux_chi_eq_zero_of_half_le_norm _ (le_of_not_gt hcon))
  have h2 : ℓ * ‖(ℓ⁻¹ : ℝ) • x‖ = ‖x‖ := by
    calc ℓ * ‖(ℓ⁻¹ : ℝ) • x‖ = |ℓ| * ‖(ℓ⁻¹ : ℝ) • x‖ := by rw [abs_of_pos hℓ]
      _ = ‖ℓ • ((ℓ⁻¹ : ℝ) • x)‖ := (norm_smul ℓ ((ℓ⁻¹ : ℝ) • x)).symm
      _ = ‖x‖ := by rw [smul_smul, mul_inv_cancel₀ (ne_of_gt hℓ), one_smul]
  have h3 : ℓ * ‖(ℓ⁻¹ : ℝ) • x‖ < ℓ / 2 := by
    have := mul_lt_mul_of_pos_left h1 hℓ
    linarith
  rw [← h2]
  exact h3

/-! ## 2. Positivity of the renormalisation factor -/

/-- `χ ⋆ χ` is strictly positive on the open unit ball: at `y₀ := w/2` both arguments
`y₀` and `w − y₀` have norm `‖w‖/2 < 1/2`, hence both factors of the convolution
integrand are strictly positive there, and continuity of the (nonnegative, compactly
supported) integrand upgrades a single positive value to a positive integral. -/
lemma sliceAux_conv3_chi_pos_of_norm_lt_one {w : E3} (hw : ‖w‖ < 1) :
    0 < Submission.BoseGases.conv3 Submission.BoseGases.chi Submission.BoseGases.chi w := by
  have hZ : 0 < Real.sqrt Submission.BoseGases.chiNormSq :=
    Real.sqrt_pos.mpr Submission.BoseGases.chiNormSq_pos
  have hy0n : ‖(2 : ℝ)⁻¹ • w‖ < 1 / 2 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2⁻¹)]
    linarith
  have hwyn : ‖w - (2 : ℝ)⁻¹ • w‖ < 1 / 2 := by
    have heq : w - (2 : ℝ)⁻¹ • w = (1 - (2 : ℝ)⁻¹) • w := by rw [sub_smul, one_smul]
    rw [heq, show (1 : ℝ) - 2⁻¹ = 2⁻¹ by norm_num]
    exact hy0n
  have hpos1 : 0 < Submission.BoseGases.chi ((2 : ℝ)⁻¹ • w) := by
    rw [Submission.BoseGases.chi]
    refine div_pos ?_ hZ
    rw [Submission.BoseGases.chiBase]
    exact Submission.BoseGases.chiBump.pos_of_mem_ball (by
      rw [Metric.mem_ball, dist_eq_norm, sub_zero]
      simpa [Submission.BoseGases.chiBump] using hy0n)
  have hpos2 : 0 < Submission.BoseGases.chi (w - (2 : ℝ)⁻¹ • w) := by
    rw [Submission.BoseGases.chi]
    refine div_pos ?_ hZ
    rw [Submission.BoseGases.chiBase]
    exact Submission.BoseGases.chiBump.pos_of_mem_ball (by
      rw [Metric.mem_ball, dist_eq_norm, sub_zero]
      simpa [Submission.BoseGases.chiBump] using hwyn)
  have hcont : Continuous fun y : E3 =>
      Submission.BoseGases.chi y * Submission.BoseGases.chi (w - y) :=
    Submission.BoseGases.chi_continuous.mul
      (Submission.BoseGases.chi_continuous.comp (continuous_const.sub continuous_id))
  have hsupp : HasCompactSupport fun y : E3 =>
      Submission.BoseGases.chi y * Submission.BoseGases.chi (w - y) :=
    Submission.BoseGases.chi_hasCompactSupport.mul_right
  have hgoal := Continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero
    (μ := MeasureTheory.volume) hcont hsupp
    (fun y => mul_nonneg (Submission.BoseGases.chi_nonneg y)
      (Submission.BoseGases.chi_nonneg (w - y)))
    (mul_ne_zero (ne_of_gt hpos1) (ne_of_gt hpos2))
  simpa [Submission.BoseGases.conv3] using hgoal

/-- A uniform positive lower bound for `χ ⋆ χ` on any closed ball of radius `< 1`. -/
lemma sliceAux_exists_pos_le_conv3_chi_closedBall {d : ℝ} (hd : d < 1) :
    ∃ m : ℝ, 0 < m ∧ ∀ z : E3, ‖z‖ ≤ d →
      m ≤ Submission.BoseGases.conv3 Submission.BoseGases.chi Submission.BoseGases.chi z := by
  by_cases hd0 : d < 0
  · exact ⟨1, one_pos,
      fun z hz => absurd hz (not_le.mpr (lt_of_lt_of_le hd0 (norm_nonneg z)))⟩
  · have hd0' : 0 ≤ d := le_of_not_gt hd0
    have hne : (Metric.closedBall (0 : E3) d).Nonempty :=
      ⟨0, by simp [Metric.mem_closedBall, hd0']⟩
    obtain ⟨z0, hz0mem, hz0min⟩ := (isCompact_closedBall (0 : E3) d)
      |>.exists_isMinOn hne Submission.BoseGases.conv_contDiff.continuous.continuousOn
    refine ⟨Submission.BoseGases.conv3 Submission.BoseGases.chi Submission.BoseGases.chi z0,
      ?_, ?_⟩
    · have hz0 : ‖z0‖ ≤ d := by simpa [Metric.mem_closedBall] using hz0mem
      exact sliceAux_conv3_chi_pos_of_norm_lt_one (lt_of_le_of_lt hz0 hd)
    · intro z hz
      exact hz0min (by simpa [Metric.mem_closedBall] using hz)

/-- A uniform positive lower bound for `(χ⋆χ)_ℓ` on any closed ball of radius `< ℓ`. -/
lemma sliceAux_exists_pos_le_convScale_closedBall {ℓ r : ℝ} (hℓ : 0 < ℓ) (hr : r < ℓ) :
    ∃ m : ℝ, 0 < m ∧ ∀ z : E3, ‖z‖ ≤ r → m ≤ Submission.BoseGases.convScale ℓ z := by
  obtain ⟨m, hmpos, hm⟩ :=
    sliceAux_exists_pos_le_conv3_chi_closedBall (d := r / ℓ) (by rw [div_lt_one hℓ]; exact hr)
  refine ⟨m, hmpos, fun z hz => ?_⟩
  have hz' : ‖(ℓ⁻¹ : ℝ) • z‖ ≤ r / ℓ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hℓ), ← div_eq_inv_mul]
    exact div_le_div_of_nonneg_right hz (le_of_lt hℓ)
  exact hm _ hz'

/-! ## 3. The slice bound for a globally integrable numerator -/

/-- **The slice bound.**  For a *globally* integrable numerator `G`, `ℓ > 0` and
`χ_ℓ(u) ≠ 0`, the windowed slice `z ↦ χ_ℓ(z)·(G(u − z)/(χ⋆χ)_ℓ(u − z))` is Bochner
integrable.  The proof is the fibre argument of
`Work.BoseFixB1B.integrable_fibre_g0`: `χ_ℓ(u) ≠ 0` gives `‖u‖ < ℓ/2`, the support
of `χ_ℓ` gives `‖z‖ < ℓ/2`, so `u − z` stays in the closed ball of radius
`‖u‖ + ℓ/2 < ℓ` where `(χ⋆χ)_ℓ ≥ m > 0`; the dominating function
`(A/m)·|G(u − ·)|` is integrable by translation invariance. -/
lemma sliceAux_integrable_chiScale_div {G : E3 → ℝ} (hG : MeasureTheory.Integrable G)
    {ℓ : ℝ} (hℓ : 0 < ℓ) {u : E3} (hu : Submission.BoseGases.chiScale ℓ u ≠ 0) :
    MeasureTheory.Integrable (fun z : E3 =>
      Submission.BoseGases.chiScale ℓ z *
        (G (u - z) / Submission.BoseGases.convScale ℓ (u - z))) := by
  have hun : ‖u‖ < ℓ / 2 := sliceAux_chiScale_ne_zero_imp_norm_lt hℓ hu
  obtain ⟨m, hmpos, hmin⟩ :=
    sliceAux_exists_pos_le_convScale_closedBall (ℓ := ℓ) (r := ‖u‖ + ℓ / 2) hℓ (by linarith)
  set A : ℝ := (Real.sqrt Submission.BoseGases.chiNormSq)⁻¹ with hA
  have hApos : 0 < A := by
    rw [hA]; exact inv_pos.mpr (Real.sqrt_pos.mpr Submission.BoseGases.chiNormSq_pos)
  have hAmnn : 0 ≤ A / m := div_nonneg (le_of_lt hApos) (le_of_lt hmpos)
  -- the dominating function
  have hdom : MeasureTheory.Integrable
      (fun z : E3 => (A / m) * |G (u - z)|) :=
    (hG.abs.comp_sub_left u).const_mul (A / m)
  -- the pointwise bound
  have hpt : ∀ z : E3,
      ‖Submission.BoseGases.chiScale ℓ z *
        (G (u - z) / Submission.BoseGases.convScale ℓ (u - z))‖
      ≤ (A / m) * |G (u - z)| := by
    intro z
    rw [Real.norm_eq_abs]
    by_cases hz : Submission.BoseGases.chiScale ℓ z = 0
    · rw [hz, zero_mul, abs_zero]
      exact mul_nonneg hAmnn (abs_nonneg _)
    · have hznorm : ‖z‖ < ℓ / 2 := sliceAux_chiScale_ne_zero_imp_norm_lt hℓ hz
      have hznorm' : ‖u - z‖ ≤ ‖u‖ + ℓ / 2 := by
        calc ‖u - z‖ ≤ ‖u‖ + ‖z‖ := norm_sub_le u z
          _ ≤ ‖u‖ + ℓ / 2 := by linarith
      have hden : m ≤ Submission.BoseGases.convScale ℓ (u - z) := hmin _ hznorm'
      have hdenpos : 0 < Submission.BoseGases.convScale ℓ (u - z) := lt_of_lt_of_le hmpos hden
      have hAsup : |Submission.BoseGases.chiScale ℓ z| ≤ A := by
        rw [hA]; exact Submission.BoseGases.abs_chiScale_le ℓ z
      have hquot : |G (u - z)| / Submission.BoseGases.convScale ℓ (u - z)
          ≤ |G (u - z)| / m :=
        div_le_div_of_nonneg_left (abs_nonneg _) hmpos hden
      calc |Submission.BoseGases.chiScale ℓ z *
              (G (u - z) / Submission.BoseGases.convScale ℓ (u - z))|
          = |Submission.BoseGases.chiScale ℓ z|
            * (|G (u - z)| / Submission.BoseGases.convScale ℓ (u - z)) := by
            rw [abs_mul, abs_div, abs_of_pos hdenpos]
        _ ≤ A * (|G (u - z)| / m) :=
            mul_le_mul hAsup hquot (div_nonneg (abs_nonneg _) (le_of_lt hdenpos))
              (le_of_lt hApos)
        _ = (A / m) * |G (u - z)| := by ring
  -- a.e. strong measurability
  have hmeas : AEStronglyMeasurable
      (fun z : E3 => Submission.BoseGases.chiScale ℓ z *
        (G (u - z) / Submission.BoseGases.convScale ℓ (u - z)))
      (MeasureTheory.volume : MeasureTheory.Measure E3) := by
    have hqmp : Measure.QuasiMeasurePreserving (fun z : E3 => u - z)
        (MeasureTheory.volume : MeasureTheory.Measure E3)
        (MeasureTheory.volume : MeasureTheory.Measure E3) :=
      MeasureTheory.quasiMeasurePreserving_sub_left_of_right_invariant
        (MeasureTheory.volume : MeasureTheory.Measure E3) u
    have hshift : AEMeasurable (fun z : E3 => G (u - z))
        (MeasureTheory.volume : MeasureTheory.Measure E3) := by
      have := hG.aestronglyMeasurable.aemeasurable.comp_quasiMeasurePreserving hqmp
      simpa [Function.comp_def] using this
    have hquot : AEMeasurable
        (fun z : E3 => G (u - z) / Submission.BoseGases.convScale ℓ (u - z))
        (MeasureTheory.volume : MeasureTheory.Measure E3) :=
      hshift.div ((Submission.BoseGases.convScale_continuous ℓ).comp
        (by fun_prop : Continuous fun z : E3 => u - z)).measurable.aemeasurable
    have hchi : AEMeasurable (fun z : E3 => Submission.BoseGases.chiScale ℓ z)
        (MeasureTheory.volume : MeasureTheory.Measure E3) :=
      (Submission.BoseGases.chiScale_continuous ℓ).measurable.aemeasurable
    exact (hchi.mul hquot).aestronglyMeasurable
  exact MeasureTheory.Integrable.mono' hdom hmeas (Filter.Eventually.of_forall hpt)

/-! ## 4. The requested statement -/

theorem chiScale_W1fun_slice_integrable {v : EuclideanSpace ℝ (Fin 3) → ℝ}
    (h : Work.UBB.ScatSol v) {ℓ : ℝ} (hℓ : 0 < ℓ) {u : EuclideanSpace ℝ (Fin 3)}
    (hu : Submission.BoseGases.chiScale ℓ u ≠ 0) :
    MeasureTheory.Integrable (fun z : EuclideanSpace ℝ (Fin 3) =>
      Submission.BoseGases.chiScale ℓ z * Work.BoseFixR.W1fun v h ℓ (u - z)) := by
  -- replace the merely locally integrable numerator `g₀` by its truncation, which is
  -- *globally* integrable and agrees with `g₀` wherever `χ_ℓ(z) ≠ 0`
  set G : E3 → ℝ :=
    (Metric.closedBall (0 : E3) (2 * ℓ)).indicator (Submission.BoseGases.g0 v h) with hGdef
  have hGint : MeasureTheory.Integrable G := by
    rw [hGdef]
    exact integrable_indicator_g0 h
  refine (sliceAux_integrable_chiScale_div hGint hℓ hu).congr
    (Filter.Eventually.of_forall fun z => ?_)
  show Submission.BoseGases.chiScale ℓ z *
      (G (u - z) / Submission.BoseGases.convScale ℓ (u - z))
    = Submission.BoseGases.chiScale ℓ z * Work.BoseFixR.W1fun v h ℓ (u - z)
  by_cases hz : Submission.BoseGases.chiScale ℓ z = 0
  · rw [hz, zero_mul, zero_mul]
  · have hun : ‖u‖ < ℓ / 2 := sliceAux_chiScale_ne_zero_imp_norm_lt hℓ hu
    have hzn : ‖z‖ < ℓ / 2 := sliceAux_chiScale_ne_zero_imp_norm_lt hℓ hz
    have huz : ‖u - z‖ ≤ 2 * ℓ := by
      have h := norm_sub_le u z
      linarith
    have hGval : G (u - z) = Submission.BoseGases.g0 v h (u - z) := by
      rw [hGdef]
      exact Set.indicator_of_mem
        (by rw [Metric.mem_closedBall, dist_zero_right]; exact huz) _
    rw [hGval]
    simp only [Work.BoseFixR.W1fun, Submission.BoseGases.wScaled]

end Work.BoseBoxFock.PCFU
