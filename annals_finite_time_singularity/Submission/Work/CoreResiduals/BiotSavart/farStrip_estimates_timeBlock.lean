import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Topology.MetricSpace.Holder
import Submission.Work.CoreResiduals.Defs
import Submission.Work.CoreResiduals.BiotSavart.slicesSupportedStrip_timeDeriv
import Submission.Work.LWP.FarField
import Submission.Work.LWP.BiotSavart.farField_decay_fderiv
import Submission.Work.StabilityFar.Decay.timeDeriv_timeHolder
import Submission.Work.StabilityFar.Decay.biotSavart_sub
import Submission.Work.StabilityFar.Decay.slicesSupported_timeDeriv_window

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.CoreResiduals.BiotSavart

open FiniteTimeSingularity

/-- **The far-field estimates for the time block `E(x,t) = BS (∂ₜω(·,t)) x` on the strip**
`Icc 0 S`.

The strip analogue of the three inputs for the `∂ₜu` block that `St4` consumes
(`Work.StabilityFar.velocity_decay_timeDeriv`, `Work.StabilityFar.Decay.timeDeriv_timeHolder`,
`Work.StabilityFar.timeDeriv_lipschitz_x`), with the window-indexed hypotheses replaced by the
strip bundle on `Icc 0 S`.  All three need the *support of `∂ₜω` on the strip*, which for a strip
bundle with `0 < S` holds (the short argument: at an interior time by
`Work.StabilityFar.Decay.timeDeriv_eq_zero_of_notMem_closedBall`, at the endpoint `t = 0` by
restricting the bundle's two-sided `HasDerivAt` to `Ioi 0` and using that the slice vanishes there
— this is the statement `Work.CoreResiduals.BiotSavart.slicesSupportedStrip_timeDeriv`, available
as `import Submission.Work.CoreResiduals.BiotSavart.slicesSupportedStrip_timeDeriv`).

* *bound*: `‖E(x,t)‖ ≤ (4/3)·M₁·R³/‖x‖²` for `2R ≤ ‖x‖` (`farField_decay_const` applied to the
  slice `∂ₜω(·,t)`, bounded by the bundle's uniform bound `M₁` and supported in `B(0,R)`);
* *`t`-Hölder*: `‖E(x,t) - E(x,τ)‖ ≤ Atu·|t-τ|^α` for `2R < ‖x‖`, `t,τ ∈ Icc 0 S`
  (`Decay.biotSavart_timeDeriv_sub_le`: the difference `∂ₜω(·,t) - ∂ₜω(·,τ)` is supported in
  `B(0,R)` and bounded by `N₁|t-τ|^α` by the bundle's `TimeDerivStripHolder`; note that fact is
  stated in the two-sided window form, so redo its short proof on `Icc 0 S`);
* *`x`-Lipschitz*: `‖E(x,t) - E(y,t)‖ ≤ A₁‖x-y‖` for `2R+5 < ‖x‖` and `‖x-y‖ ≤ 1`
  (`Work.LWP.BiotSavart.biotSavart_lipschitzOn_far`, as in
  `Work.StabilityFar.timeDeriv_lipschitz_x`). -/
theorem farStrip_estimates_timeBlock {α : NNReal} (hα : 0 < (α : ℝ)) (hα1 : (α : ℝ) < 1)
    {ω : Work.LWP.R3 → ℝ → Work.LWP.R3} {R S : ℝ} (hS : 0 < S)
    (hbun : Work.CoreResiduals.BSAdmissibleStripFull α ω R S) :
    ∃ M₁ Atu A₁ : ℝ, 0 ≤ M₁ ∧ 0 ≤ Atu ∧ 0 ≤ A₁ ∧
      (∀ t ∈ Set.Icc (0:ℝ) S, ∀ x : Work.LWP.R3, 2 * R ≤ ‖x‖ →
        ‖Work.LWP.biotSavart (fun y => FiniteTimeSingularity.timeDeriv ω y t) x‖
          ≤ (4 / 3) * M₁ * R ^ 3 / ‖x‖ ^ 2) ∧
      (∀ x : Work.LWP.R3, 2 * R < ‖x‖ → ∀ t ∈ Set.Icc (0:ℝ) S, ∀ τ ∈ Set.Icc (0:ℝ) S,
        ‖Work.LWP.biotSavart (fun y => FiniteTimeSingularity.timeDeriv ω y t) x
          - Work.LWP.biotSavart (fun y => FiniteTimeSingularity.timeDeriv ω y τ) x‖
          ≤ Atu * |t - τ| ^ (α : ℝ)) ∧
      (∀ t ∈ Set.Icc (0:ℝ) S, ∀ x y : Work.LWP.R3, 2 * R + 5 < ‖x‖ → ‖x - y‖ ≤ 1 →
        ‖Work.LWP.biotSavart (fun z => FiniteTimeSingularity.timeDeriv ω z t) x
          - Work.LWP.biotSavart (fun z => FiniteTimeSingularity.timeDeriv ω z t) y‖
          ≤ A₁ * ‖x - y‖) := by
  -- ## Unpack the strip bundle (keeping a copy for the support lemma)
  have hbunKeep : Work.CoreResiduals.BSAdmissibleStripFull α ω R S := hbun
  unfold Work.CoreResiduals.BSAdmissibleStripFull at hbun
  obtain ⟨hstrip, htd, hholder⟩ := hbun
  unfold Work.CoreResiduals.BSAdmissibleStrip at hstrip
  obtain ⟨hRpos, _hsuppω, _hbddω, _hholderω, _htimeω, _hmeasω⟩ := hstrip
  unfold Work.CoreResiduals.TimeDerivStrip at htd
  obtain ⟨_hHasDeriv, hbddDt₀, hmeasDt⟩ := htd
  unfold Work.CoreResiduals.TimeDerivStripHolder at hholder
  obtain ⟨N₀, hN₀⟩ := hholder
  -- ## The support of `∂ₜω` on the strip
  have hsuppDt : ∀ t ∈ Set.Icc (0:ℝ) S, ∀ y : Work.LWP.R3,
      FiniteTimeSingularity.timeDeriv ω y t ≠ 0 → y ∈ Metric.closedBall 0 R :=
    slicesSupportedStrip_timeDeriv hS hbunKeep
  -- ## The constants
  obtain ⟨M₀, hM₀⟩ := hbddDt₀
  set M₁ : ℝ := max M₀ 0 with hM₁def
  have hM₁nonneg : 0 ≤ M₁ := by rw [hM₁def]; exact le_max_right _ _
  have hbddDt : ∀ t ∈ Set.Icc (0:ℝ) S, ∀ y : Work.LWP.R3,
      ‖FiniteTimeSingularity.timeDeriv ω y t‖ ≤ M₁ := by
    intro t ht y
    rw [hM₁def]
    exact le_trans (hM₀ t ht y) (le_max_left _ _)
  set N₁ : ℝ := max N₀ 0 with hN₁def
  have hN₁nonneg : 0 ≤ N₁ := by rw [hN₁def]; exact le_max_right _ _
  have hholderN : ∀ y : Work.LWP.R3, ∀ t ∈ Set.Icc (0:ℝ) S, ∀ t' ∈ Set.Icc (0:ℝ) S,
      ‖FiniteTimeSingularity.timeDeriv ω y t - FiniteTimeSingularity.timeDeriv ω y t'‖
        ≤ N₁ * |t - t'| ^ (α : ℝ) := by
    intro y t ht t' ht'
    rw [hN₁def]
    exact le_trans (hN₀ y t ht t' ht')
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg (abs_nonneg _) _))
  set Atu : ℝ := N₁ * R / 3 with hAtudef
  set A₁ : ℝ := 2 ^ 17 * M₁ with hA₁def
  have hAtunonneg : 0 ≤ Atu := by
    rw [hAtudef]; exact div_nonneg (mul_nonneg hN₁nonneg hRpos.le) (by norm_num)
  have hA₁nonneg : 0 ≤ A₁ := by rw [hA₁def]; positivity
  refine ⟨M₁, Atu, A₁, hM₁nonneg, hAtunonneg, hA₁nonneg, ?_, ?_, ?_⟩
  · -- ## Clause 1: the far-field bound
    intro t ht x hx
    exact Work.LWP.BiotSavart.farField_decay_const hRpos.le hM₁nonneg
      (fun y => hbddDt t ht y) (fun y => hsuppDt t ht y) x hx
  · -- ## Clause 2: the `t`-Hölder bound
    intro x hx t ht τ hτ
    have hs : 0 ≤ |t - τ| ^ (α : ℝ) := Real.rpow_nonneg (abs_nonneg _) _
    -- linearity of Biot–Savart
    have hsub : Work.LWP.biotSavart (fun y => FiniteTimeSingularity.timeDeriv ω y t) x
        - Work.LWP.biotSavart (fun y => FiniteTimeSingularity.timeDeriv ω y τ) x
        = Work.LWP.biotSavart
            ((fun y => FiniteTimeSingularity.timeDeriv ω y t)
              - (fun y => FiniteTimeSingularity.timeDeriv ω y τ)) x :=
      (Work.StabilityFar.Decay.biotSavart_sub hRpos.le hM₁nonneg
        (fun y => hbddDt t ht y) (fun y => hbddDt τ hτ y)
        (fun y => hsuppDt t ht y) (fun y => hsuppDt τ hτ y)
        (hmeasDt t ht) (hmeasDt τ hτ) x).symm
    rw [hsub]
    -- the difference field is supported in `B(0,R)` and bounded by `N₁|t-τ|^α`
    have hbddDiff : ∀ y : Work.LWP.R3,
        ‖((fun y => FiniteTimeSingularity.timeDeriv ω y t)
            - (fun y => FiniteTimeSingularity.timeDeriv ω y τ)) y‖
          ≤ N₁ * |t - τ| ^ (α : ℝ) := by
      intro y
      rw [Pi.sub_apply]
      by_cases hy : y ∈ Metric.closedBall 0 R
      · exact hholderN y t ht τ hτ
      · have ht0 : FiniteTimeSingularity.timeDeriv ω y t = 0 := by
          by_contra hne; exact hy (hsuppDt t ht y hne)
        have hτ0 : FiniteTimeSingularity.timeDeriv ω y τ = 0 := by
          by_contra hne; exact hy (hsuppDt τ hτ y hne)
        rw [ht0, hτ0, sub_zero, norm_zero]
        exact mul_nonneg hN₁nonneg hs
    have hsuppDiff : ∀ y : Work.LWP.R3,
        ((fun y => FiniteTimeSingularity.timeDeriv ω y t)
            - (fun y => FiniteTimeSingularity.timeDeriv ω y τ)) y ≠ 0 →
          y ∈ Metric.closedBall 0 R := by
      intro y hy
      by_contra hcon
      apply hy
      rw [Pi.sub_apply]
      have ht0 : FiniteTimeSingularity.timeDeriv ω y t = 0 := by
        by_contra hne; exact hcon (hsuppDt t ht y hne)
      have hτ0 : FiniteTimeSingularity.timeDeriv ω y τ = 0 := by
        by_contra hne; exact hcon (hsuppDt τ hτ y hne)
      rw [ht0, hτ0, sub_zero]
    have hfar := Work.LWP.BiotSavart.farField_decay_const hRpos.le
      (mul_nonneg hN₁nonneg hs) hbddDiff hsuppDiff x hx.le
    refine hfar.trans ?_
    -- `R³/‖x‖² ≤ R/4`
    have hkey : R ^ 3 / ‖x‖ ^ 2 ≤ R / 4 := by
      have hXpos : 0 < ‖x‖ ^ 2 := pow_pos (by linarith) 2
      rw [div_le_iff₀ hXpos, div_mul_eq_mul_div, le_div_iff₀ (by norm_num : (0 : ℝ) < 4)]
      have h2 : (2 * R) ^ 2 ≤ ‖x‖ ^ 2 := by
        have h1 : 0 ≤ 2 * R := by linarith
        simpa using pow_le_pow_left₀ h1 hx.le 2
      nlinarith [h2]
    have hstep : (4 / 3) * (N₁ * |t - τ| ^ (α : ℝ)) * R ^ 3 / ‖x‖ ^ 2
        = (4 / 3) * (N₁ * |t - τ| ^ (α : ℝ)) * (R ^ 3 / ‖x‖ ^ 2) := by ring
    rw [hstep]
    calc (4 / 3) * (N₁ * |t - τ| ^ (α : ℝ)) * (R ^ 3 / ‖x‖ ^ 2)
        ≤ (4 / 3) * (N₁ * |t - τ| ^ (α : ℝ)) * (R / 4) :=
          mul_le_mul_of_nonneg_left hkey (by nlinarith [hN₁nonneg, hs])
      _ = (N₁ * R / 3) * |t - τ| ^ (α : ℝ) := by ring
      _ = Atu * |t - τ| ^ (α : ℝ) := by rw [hAtudef]
  · -- ## Clause 3: the `x`-Lipschitz bound
    intro t ht x y hx hxy
    have hxR : 2 * R ≤ ‖x‖ := by linarith
    have hxpos : 0 < ‖x‖ := by linarith
    have hxmem : x ∈ Metric.ball x (‖x‖ / 4) := by
      rw [Metric.mem_ball, dist_self]; linarith
    have hymem : y ∈ Metric.ball x (‖x‖ / 4) := by
      rw [Metric.mem_ball, dist_eq_norm, norm_sub_rev]; linarith
    have hlipfar := Work.LWP.BiotSavart.biotSavart_lipschitzOn_far hRpos.le hM₁nonneg
      (fun z => hbddDt t ht z) (fun z => hsuppDt t ht z) (hmeasDt t ht) hxR
    rw [lipschitzOnWith_iff_norm_sub_le] at hlipfar
    have hb := hlipfar hxmem hymem
    have hK : (2 ^ 20 : ℝ) * M₁ * R ^ 3 / ‖x‖ ^ 3 ≤ A₁ := by
      rw [hA₁def]
      have hxx : (2 * R) ^ 3 ≤ ‖x‖ ^ 3 := pow_le_pow_left₀ (by linarith) hxR 3
      have h8 : (2 * R) ^ 3 = 8 * R ^ 3 := by ring
      rw [div_le_iff₀ (pow_pos hxpos 3)]
      have hstep : 2 ^ 17 * M₁ * (8 * R ^ 3) ≤ 2 ^ 17 * M₁ * ‖x‖ ^ 3 :=
        mul_le_mul_of_nonneg_left (by rw [← h8]; exact hxx) (by positivity)
      have hpow : (2 : ℝ) ^ 20 = 2 ^ 17 * 8 := by norm_num
      nlinarith [hstep, hpow]
    calc ‖Work.LWP.biotSavart (fun z => FiniteTimeSingularity.timeDeriv ω z t) x
          - Work.LWP.biotSavart (fun z => FiniteTimeSingularity.timeDeriv ω z t) y‖
        ≤ (((2 ^ 20 : ℝ) * M₁ * R ^ 3 / ‖x‖ ^ 3).toNNReal : ℝ) * ‖x - y‖ := hb
      _ = (2 ^ 20 * M₁ * R ^ 3 / ‖x‖ ^ 3) * ‖x - y‖ := by
          rw [Real.coe_toNNReal _ (by positivity)]
      _ ≤ A₁ * ‖x - y‖ := mul_le_mul_of_nonneg_right hK (norm_nonneg _)

end Work.CoreResiduals.BiotSavart
