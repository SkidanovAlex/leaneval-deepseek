/-
# The axis level of the meridian stream function is continuous (slim hypotheses)

Port of `Work.FTS.BSIdent.Weyl.Levels.continuous_axisLevel` to the *slim* hypotheses used by the
StreamBdry boundary layer: the interior `C²`-ness `hsm` of the profile is assumed only on
`w > 0`, and the rate hypothesis carries only the three first-order clauses.

The original proof calls the `θ`-derivative continuity lemma at the point `(w(z), π/2)` with
`w(z) = ρ(0,z)^{3α}/B(τ)`, deriving `-1 < w(z)` from `0 ≤ w(z)`.  At `z = 0` this gives
`w = 0`, which the slim hypothesis does not cover.  Here the `z = 0` case is treated separately:
the axis level is `z ↦ -z·A(τ)⁻¹·∂_θΦ(w(z),π/2)`, and the second factor is *bounded* near `0`
(each slice bound `|∂_θΦ(w,θ)| ≤ C₀(1+w)^{-λ} ≤ C₀` extends to `θ = π/2` by continuity, and
`1 + w ≥ 1`), so the product tends to `0 = axisLevel 0`.

At `z ≠ 0` the original argument applies verbatim: `w(z) > 0`, so `hsm` gives `C²`-ness at
`(w(z), π/2)`, hence continuity of `∂_θΦ` there, and `z ↦ (w(z), π/2)` is continuous.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Submission.Work.FTS.BSIdent.Defs
import Submission.Work.FTS_BSIdentP.Slim.Dev8
import Submission.Work.FTS_BSIdentP.Slim.Dev12
import Submission.Work.FTS_BSIdentP.Slim.Dev2

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.BSIdentP.Levels

open Filter Set
open scoped Topology

open Work.FTS.BSIdent

theorem continuous_axisLevel {α : ℝ} {A B : ℝ → ℝ} {Φ : Work.FTS.BSIdent.Fam}
    {C : Physical.PhysClock} {t : ℝ}
    (hα : 0 < α) (hA : A (Physical.clockInv C t) ≠ 0) (hB : 0 < B (Physical.clockInv C t))
    (hsm : ∀ w θ : ℝ, 0 < w → -Real.pi / 2 - 1 < θ → θ < Real.pi / 2 + 1 →
      ContDiffAt ℝ 2 (fun p : ℝ × ℝ => Φ p.1 p.2 (Physical.clockInv C t)) (w, θ))
    (hzeroPlane : ∀ w : ℝ, 0 < w → Φ w 0 (Physical.clockInv C t) = 0)
    (hzeroAxis : ∀ w : ℝ, 0 < w → Φ w (Real.pi / 2) (Physical.clockInv C t) = 0)
    {lam C₀ : ℝ} (hlam : 0 < lam) (hC₀ : 0 < C₀)
    (hexp : 2 ≤ Work.FTS.Regularity.pExp α * lam)
    (hrate : ∀ w θ : ℝ, 0 ≤ w → 0 ≤ θ → θ < Real.pi / 2 →
      |Φ w θ (Physical.clockInv C t)| ≤ C₀ * (Real.pi / 2 - θ) * (1 + w) ^ (-lam) ∧
      |deriv (fun w' : ℝ => Φ w' θ (Physical.clockInv C t)) w|
        ≤ C₀ * (Real.pi / 2 - θ) * (1 + w) ^ (-lam - 1) ∧
      |deriv (fun θ' : ℝ => Φ w θ' (Physical.clockInv C t)) θ| ≤ C₀ * (1 + w) ^ (-lam)) :
    Continuous (Work.FTS.BSIdentP.Dev12.axisLevel α A B Φ (Physical.clockInv C t)) := by
  set τ := Physical.clockInv C t with hτ
  have hp : 0 < Work.FTS.Regularity.pExp α := by
    rw [Work.FTS.Regularity.pExp]; linarith
  -- `z ↦ ρ(0,z) = √(z²)` is continuous
  have hρ : Continuous (fun z : ℝ => Work.Cyl.rhoP 0 z) := by
    have hfun : (fun z : ℝ => Work.Cyl.rhoP 0 z) = fun z : ℝ => Real.sqrt (z ^ 2) := by
      funext z; simp [Work.Cyl.rhoP]
    rw [hfun]
    exact Real.continuous_sqrt.comp (continuous_id.pow 2)
  -- hence so is the weight `z ↦ ρ(0,z)^{3α}/B(τ)`
  have hψ : Continuous (fun z : ℝ => Work.Cyl.rhoP 0 z ^ Work.FTS.Regularity.pExp α / B τ) := by
    have h1 : Continuous (fun z : ℝ => Work.Cyl.rhoP 0 z ^ Work.FTS.Regularity.pExp α) := by
      rw [continuous_iff_continuousAt]
      intro z
      exact (Real.continuousAt_rpow_const (Work.Cyl.rhoP 0 z) (Work.FTS.Regularity.pExp α)
        (Or.inr hp.le)).comp hρ.continuousAt
    exact h1.div_const (B τ)
  -- `∂_θΦ(·,π/2)` is continuous at `(w, π/2)` for every `w > 0`
  have hpdZ : ∀ w : ℝ, 0 < w → ContinuousAt (fun p : ℝ × ℝ =>
      deriv (fun θ' : ℝ => Φ p.1 θ' τ) p.2) (w, Real.pi / 2) := by
    intro w hw
    have hG := Work.FTS.BSIdentP.Dev2.continuousAt_pdZ_Phi (τ := τ) (Φ := Φ) hsm hw
      Work.FTS.BSIdentP.Dev2.abs_pi_div_two_lt
    simpa only [Work.Cyl.pdZ] using hG
  -- ## the slice derivative is continuous at every `z ≠ 0`
  have hg_ne : ∀ z : ℝ, z ≠ 0 → ContinuousAt (fun z : ℝ =>
      deriv (fun θ' : ℝ => Φ (Work.Cyl.rhoP 0 z ^ Work.FTS.Regularity.pExp α / B τ) θ' τ)
        (Real.pi / 2)) z := by
    intro z hz
    have hw : 0 < Work.Cyl.rhoP 0 z ^ Work.FTS.Regularity.pExp α / B τ :=
      div_pos (Real.rpow_pos_of_pos (Work.FTS.BSIdentP.Dev8.rhoP_zero_pos hz) _) hB
    have hinner : ContinuousAt (fun z : ℝ =>
        (Work.Cyl.rhoP 0 z ^ Work.FTS.Regularity.pExp α / B τ, Real.pi / 2)) z :=
      hψ.continuousAt.prodMk continuousAt_const
    exact (hpdZ _ hw).tendsto.comp hinner
  -- ## the slice derivative is bounded on the punctured line
  have hbd : ∀ z : ℝ, z ≠ 0 →
      |deriv (fun θ' : ℝ => Φ (Work.Cyl.rhoP 0 z ^ Work.FTS.Regularity.pExp α / B τ) θ' τ)
        (Real.pi / 2)| ≤ C₀ := by
    intro z hz
    set w : ℝ := Work.Cyl.rhoP 0 z ^ Work.FTS.Regularity.pExp α / B τ with hwdef
    have hw : 0 < w :=
      div_pos (Real.rpow_pos_of_pos (Work.FTS.BSIdentP.Dev8.rhoP_zero_pos hz) _) hB
    have hcont' : ContinuousAt (fun θ : ℝ => deriv (fun θ' : ℝ => Φ w θ' τ) θ)
        (Real.pi / 2) :=
      (hpdZ w hw).comp (continuousAt_const.prodMk continuousAt_id)
    have hlim : Tendsto (fun θ : ℝ => |deriv (fun θ' : ℝ => Φ w θ' τ) θ|)
        (𝓝[Set.Iio (Real.pi / 2)] (Real.pi / 2))
        (𝓝 |deriv (fun θ' : ℝ => Φ w θ' τ) (Real.pi / 2)|) :=
      (hcont'.tendsto.mono_left nhdsWithin_le_nhds).abs
    have hbound : |deriv (fun θ' : ℝ => Φ w θ' τ) (Real.pi / 2)| ≤ C₀ := by
      refine le_of_tendsto hlim ?_
      filter_upwards [self_mem_nhdsWithin (s := Set.Iio (Real.pi / 2)),
        nhdsWithin_le_nhds (isOpen_Ioi.mem_nhds (show (0 : ℝ) < Real.pi / 2 by positivity))]
        with θ hθ hθ0
      calc |deriv (fun θ' : ℝ => Φ w θ' τ) θ| ≤ C₀ * (1 + w) ^ (-lam) :=
            (hrate w θ hw.le hθ0.le hθ).2.2
        _ ≤ C₀ := by
            have h1 : (1 + w) ^ (-lam) ≤ 1 :=
              Real.rpow_le_one_of_one_le_of_nonpos (by linarith) (by linarith)
            nlinarith [hC₀.le]
    simpa [hwdef] using hbound
  -- ## continuity of the product
  have hprod : Continuous (fun z : ℝ => -z * (A τ)⁻¹ *
      deriv (fun θ' : ℝ => Φ (Work.Cyl.rhoP 0 z ^ Work.FTS.Regularity.pExp α / B τ) θ' τ)
        (Real.pi / 2)) := by
    rw [continuous_iff_continuousAt]
    intro z
    rcases eq_or_ne z 0 with hz | hz
    · -- at `z = 0` the bounded factor is killed by the factor `z`
      subst hz
      have hval : (-(0 : ℝ) * (A τ)⁻¹ * deriv (fun θ' : ℝ =>
          Φ (Work.Cyl.rhoP 0 0 ^ Work.FTS.Regularity.pExp α / B τ) θ' τ)
            (Real.pi / 2)) = 0 := by ring
      rw [ContinuousAt, hval]
      have hbdd : ∀ y : ℝ, ‖deriv (fun θ' : ℝ =>
          Φ (Work.Cyl.rhoP 0 y ^ Work.FTS.Regularity.pExp α / B τ) θ' τ)
            (Real.pi / 2)‖ ≤ max C₀ |deriv (fun θ' : ℝ =>
              Φ (Work.Cyl.rhoP 0 0 ^ Work.FTS.Regularity.pExp α / B τ) θ' τ)
                (Real.pi / 2)| := by
        intro y
        rcases eq_or_ne y 0 with hy | hy
        · subst hy; exact le_max_right _ _
        · rw [Real.norm_eq_abs]
          exact le_trans (hbd y hy) (le_max_left _ _)
      have h1 : Tendsto (fun y : ℝ => -y * (A τ)⁻¹) (𝓝 (0 : ℝ)) (𝓝 0) := by
        have h10 : Tendsto (fun y : ℝ => -y * (A τ)⁻¹) (𝓝 (0 : ℝ))
            (𝓝 (-(0 : ℝ) * (A τ)⁻¹)) :=
          (tendsto_id (α := ℝ)).neg.mul tendsto_const_nhds
        simpa using h10
      have h2 : Tendsto (fun y : ℝ => ‖-y * (A τ)⁻¹‖ *
          max C₀ |deriv (fun θ' : ℝ =>
            Φ (Work.Cyl.rhoP 0 0 ^ Work.FTS.Regularity.pExp α / B τ) θ' τ)
              (Real.pi / 2)|) (𝓝 (0 : ℝ)) (𝓝 0) := by
        simpa using h1.norm.mul tendsto_const_nhds
      have h4 : Tendsto (fun y : ℝ => ‖-y * (A τ)⁻¹ * deriv (fun θ' : ℝ =>
          Φ (Work.Cyl.rhoP 0 y ^ Work.FTS.Regularity.pExp α / B τ) θ' τ)
            (Real.pi / 2)‖) (𝓝 (0 : ℝ)) (𝓝 0) := by
        refine squeeze_zero
          (f := fun y : ℝ => ‖-y * (A τ)⁻¹ * deriv (fun θ' : ℝ =>
            Φ (Work.Cyl.rhoP 0 y ^ Work.FTS.Regularity.pExp α / B τ) θ' τ)
              (Real.pi / 2)‖)
          (g := fun y : ℝ => ‖-y * (A τ)⁻¹‖ * max C₀ |deriv (fun θ' : ℝ =>
            Φ (Work.Cyl.rhoP 0 0 ^ Work.FTS.Regularity.pExp α / B τ) θ' τ)
              (Real.pi / 2)|)
          (fun y => norm_nonneg _) (fun y => ?_) h2
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_left (hbdd y) (norm_nonneg _)
      exact tendsto_zero_iff_norm_tendsto_zero.mpr h4
    · exact (continuousAt_id.neg.mul continuousAt_const).mul (hg_ne z hz)
  exact hprod

end Work.FTS.BSIdentP.Levels
