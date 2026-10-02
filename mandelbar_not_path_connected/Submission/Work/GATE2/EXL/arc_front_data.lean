import Mathlib
import Submission.Work.GATE2.CaseII
import Submission.Work.GATE2.EXL.deviation_rayPt
import Submission.Work.FSeed.API.mem_Mandelbar

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.GATE2.EXL

open LeanEval.ComplexAnalysis (Mandelbar Tantibar)

/-- **Front-leg data of the equipotential arc.**  If the `Ψ`-image of the arc `A` is the ray
point of angle `θ(r) = θ₀ + r (α₁ - θ₀)` and level `exp p > 1`, with `θ₀ < α₁` and
`α₁ - θ₀ < 1/524288`, then

* the front leg misses the filled Julia set `K c` (it is a dynamical ray point), and
* its `α₁`-deviation is the closed form `θ(r) - α₁`, hence of modulus `< 1/524288`.

This is the sharp numerical input of `Work.GATE2.caseIILeak_of_arcAngle`: the whole angular
window `[θ₀, α₁]` lies in `(α₁ - 1/2, α₁ + 1/2]`, so the lift of the Böttcher argument is the
angle itself (`Work.GATE.Gate.deviation_rayPt`), and the deviation is maximised at `r = 0`. -/
theorem arc_front_data {c : ℂ} {d : Work.EL.RootParabolic c}
    (fl : Work.EL.ParabolicFlower (Work.EL.F c) ((LeanEval.ComplexAnalysis.Tantibar c)^[5]) d.z₁)
    {θ₀ p : ℝ} (A : C(unitInterval, ℂ))
    (hangle : ∀ r : unitInterval,
      fl.Ψ (A r) = Work.EL.rayPt d.hN (θ₀ + (r : ℝ) * (Work.EL.alpha1 - θ₀)) (Real.exp p))
    (hp : 0 < p) (hθ₀ : θ₀ < Work.EL.alpha1) (hθ₀' : Work.EL.alpha1 - θ₀ < 1 / (32 * 16384)) :
    (∀ r : unitInterval, fl.Ψ (A r) ∉ Work.EL.K c) ∧
    (∀ r : unitInterval,
      |Work.GATE.deviation (Work.Bottcher.varphiCrit c) Work.EL.alpha1 (fl.Ψ (A r))| <
        1 / 524288) := by
  have hM : c ∈ Mandelbar := Work.FSeed.API.mem_Mandelbar d
  have hcritB : Work.ParamRays.IsCritBottcher c d.φ :=
    Work.ParamRays.IsDynBottcher.isCritBottcher d.bottcher
  have hp1 : (1 : ℝ) < Real.exp p := Real.one_lt_exp_iff.mpr hp
  have hθ₀le : θ₀ ≤ Work.EL.alpha1 := le_of_lt hθ₀
  have hδ : Work.EL.alpha1 - θ₀ < 1 / 524288 := by
    have h : (32 : ℝ) * 16384 = 524288 := by norm_num
    rw [h] at hθ₀'
    exact hθ₀'
  have hθ₀lo : Work.EL.alpha1 - 1 / 2 < θ₀ := by linarith
  constructor
  · intro r
    rw [hangle r]
    exact Work.EL.rayPt_notMem_K d.hN hp1
  · intro r
    have hr0 : (0 : ℝ) ≤ (r : ℝ) := r.2.1
    have hr1 : (r : ℝ) ≤ 1 := r.2.2
    rw [hangle r]
    set θ : ℝ := θ₀ + (r : ℝ) * (Work.EL.alpha1 - θ₀) with hθdef
    have hθle : θ ≤ Work.EL.alpha1 := by
      rw [hθdef]
      nlinarith [hθ₀le, hr1]
    have hθlo : Work.EL.alpha1 - 1 / 2 < θ := by
      rw [hθdef] at *
      nlinarith [hθ₀lo, hr0, hθ₀le]
    have hθhi : θ ≤ Work.EL.alpha1 + 1 / 2 := by linarith
    have hnotK : Work.EL.rayPt d.hN θ (Real.exp p) ∉ Work.EL.K c :=
      Work.EL.rayPt_notMem_K d.hN hp1
    have hcrit : Work.EL.rayPt d.hN θ (Real.exp p) ∈ Work.ParamRays.critDomain c := by
      rw [Work.ParamRays.mem_critDomain,
        (Work.ParamRays.paramPotential_eq_zero_iff c).mpr hM,
        ← Work.Bottcher.CritBasic.green_eq]
      exact Work.PARIMPL.green_pos_of_notMem_K hnotK
    have heq : Work.Bottcher.varphiCrit c (Work.EL.rayPt d.hN θ (Real.exp p)) =
        d.φ (Work.EL.rayPt d.hN θ (Real.exp p)) :=
      Work.Bottcher.varphiCrit_unique hcritB hcrit
    rw [show Work.GATE.deviation (Work.Bottcher.varphiCrit c) Work.EL.alpha1
          (Work.EL.rayPt d.hN θ (Real.exp p))
        = Work.GATE.deviation d.φ Work.EL.alpha1 (Work.EL.rayPt d.hN θ (Real.exp p)) by
      simp only [Work.GATE.deviation, Work.GATE.liftAngle, Work.GATE.bAngle, heq]]
    rw [Work.GATE.Gate.deviation_rayPt d.hN hp1 hθlo hθhi, abs_of_nonpos (by linarith), neg_sub]
    have hfac : Work.EL.alpha1 - θ = (1 - (r : ℝ)) * (Work.EL.alpha1 - θ₀) := by
      rw [hθdef]; ring
    rw [hfac]
    have hle : (1 - (r : ℝ)) * (Work.EL.alpha1 - θ₀) ≤ 1 * (Work.EL.alpha1 - θ₀) :=
      mul_le_mul_of_nonneg_right (by linarith) (by linarith)
    linarith

end Work.GATE2.EXL
