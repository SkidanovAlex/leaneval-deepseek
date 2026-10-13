import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Submission.Work.FTS.BSIdent.Defs
import Submission.Work.FTS.BSIdent.Weyl.Levels._dev12
import Submission.Work.FTS.BSIdent.Weyl.Levels._dev2

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.BSIdent.Weyl.Levels

open Filter Set
open scoped Topology

theorem continuous_axisLevel {α : ℝ} {A B : ℝ → ℝ} {Φ : Work.FTS.BSIdent.Fam}
    {C : Physical.PhysClock} {t : ℝ}
    (hα : 0 < α) (hA : A (Physical.clockInv C t) ≠ 0) (hB : 0 < B (Physical.clockInv C t))
    (hsm : ∀ w θ : ℝ, -1 < w → -Real.pi / 2 - 1 < θ → θ < Real.pi / 2 + 1 →
      ContDiffAt ℝ 2 (fun p : ℝ × ℝ => Φ p.1 p.2 (Physical.clockInv C t)) (w, θ))
    (hzeroPlane : ∀ w : ℝ, 0 < w → Φ w 0 (Physical.clockInv C t) = 0)
    (hzeroAxis : ∀ w : ℝ, 0 < w → Φ w (Real.pi / 2) (Physical.clockInv C t) = 0)
    {lam C₀ : ℝ} (hlam : 0 < lam) (hC₀ : 0 < C₀)
    (hexp : 2 ≤ Work.FTS.Regularity.pExp α * lam)
    (hrate : ∀ w θ : ℝ, 0 ≤ w → 0 ≤ θ → θ < Real.pi / 2 →
      |Φ w θ (Physical.clockInv C t)| ≤ C₀ * (Real.pi / 2 - θ) * (1 + w) ^ (-lam) ∧
      |deriv (fun w' : ℝ => Φ w' θ (Physical.clockInv C t)) w|
        ≤ C₀ * (Real.pi / 2 - θ) * (1 + w) ^ (-lam - 1) ∧
      |deriv (fun θ' : ℝ => Φ w θ' (Physical.clockInv C t)) θ| ≤ C₀ * (1 + w) ^ (-lam) ∧
      |deriv (fun θ' : ℝ => deriv (fun θ'' : ℝ => Φ w θ'' (Physical.clockInv C t)) θ') θ|
        ≤ C₀ * (1 + w) ^ (-lam) ∧
      |deriv (fun θ' : ℝ => deriv (fun w' : ℝ => Φ w' θ' (Physical.clockInv C t)) w) θ|
        ≤ C₀ * (1 + w) ^ (-lam - 1) ∧
      |deriv (fun w' : ℝ => deriv (fun w'' : ℝ => Φ w'' θ (Physical.clockInv C t)) w') w|
        ≤ C₀ * (Real.pi / 2 - θ) * (1 + w) ^ (-lam - 2)) :
    Continuous (Work.FTS.BSIdent.Weyl.Dev12.axisLevel α A B Φ (Physical.clockInv C t)) := by
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
  -- the slice derivative `w ↦ ∂_θΦ(w,π/2)(τ)` is continuous where `Φ` is `C²`
  have hg : Continuous (fun z : ℝ =>
      deriv (fun θ' : ℝ => Φ (Work.Cyl.rhoP 0 z ^ Work.FTS.Regularity.pExp α / B τ) θ' τ)
        (Real.pi / 2)) := by
    rw [continuous_iff_continuousAt]
    intro z
    have hw : -1 < Work.Cyl.rhoP 0 z ^ Work.FTS.Regularity.pExp α / B τ := by
      have h1 : 0 ≤ Work.Cyl.rhoP 0 z ^ Work.FTS.Regularity.pExp α :=
        Real.rpow_nonneg (Real.sqrt_nonneg _) _
      have h2 : 0 ≤ Work.Cyl.rhoP 0 z ^ Work.FTS.Regularity.pExp α / B τ :=
        div_nonneg h1 (le_of_lt hB)
      linarith
    have hG := Work.FTS.BSIdent.Weyl.Dev2.continuousAt_pdZ_Phi (τ := τ) (Φ := Φ) hsm hw
      Work.FTS.BSIdent.Weyl.Dev2.abs_pi_div_two_lt
    have hinner : ContinuousAt (fun z : ℝ =>
        (Work.Cyl.rhoP 0 z ^ Work.FTS.Regularity.pExp α / B τ, Real.pi / 2)) z :=
      hψ.continuousAt.prodMk continuousAt_const
    exact hG.tendsto.comp hinner
  have hfin : Continuous (fun z : ℝ => -z * (A τ)⁻¹ *
      deriv (fun θ' : ℝ => Φ (Work.Cyl.rhoP 0 z ^ Work.FTS.Regularity.pExp α / B τ) θ' τ)
        (Real.pi / 2)) :=
    (continuous_neg.mul continuous_const).mul hg
  exact hfin

end Work.FTS.BSIdent.Weyl.Levels
