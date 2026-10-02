import Mathlib
import Submission.Work.GATE2.EXL.arc_mem_pairSideNear
import Submission.Work.GATE2.EXL.arcLift_exists
import Submission.Work.GATE2.EXL.ArcPreimage
import Submission.Work.GATE2.EXL.z1_mem_K

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open Classical Filter Set Metric
open scoped Topology

set_option autoImplicit false
set_option linter.unusedVariables false

noncomputable section

namespace Work.GATE2.EXL

open LeanEval.ComplexAnalysis (Mandelbar Tantibar)

theorem arc_exists {c : ℂ} (d : Work.EL.RootParabolic c)
    (fl : Work.EL.ParabolicFlower (Work.EL.F c) ((LeanEval.ComplexAnalysis.Tantibar c)^[5]) d.z₁)
    (nest : Work.EL.Z1Nest d.hN d.z₁ fl.Pa) (Lray : Work.ELRig.RayCylLift d fl)
    (hQa : ∀ n : ℕ, (nest.Q n).a = Work.ELNest.bAng' n)
    (hQb : ∀ n : ℕ, (nest.Q n).b = Work.ELNest.bAng n + 1)
    (n : ℕ) {θ₀ x₀ p : ℝ} (hθ₀ : θ₀ ∈ Set.Ioo (Work.ELNest.bAng n) Work.EL.alpha1)
    (hp : 0 < p) (hx₀R : x₀ < -Lray.R)
    (hx₀ : fl.Ψ ((x₀ : ℝ) : ℂ) = Work.EL.rayPt d.hN θ₀ (Real.exp p))
    {Rc : ℝ} (hcover : ∀ z : ℂ, z ≠ d.z₁ → ‖z - d.z₁‖ < Rc →
      z ∈ fl.Pa ∨ ∃ w : ℂ, w.re < -Lray.R ∧ fl.Ψ w = z)
    {g : ℝ} (hg : 0 < g) (hpg : p < g)
    (hsmall : ∀ z : ℂ, z ∈ Work.EL.pairSideNear nest.P0 → z ∈ Work.EL.pairSideNear (nest.Q n) →
      Work.EL.pot d.hN z < g → ‖z - d.z₁‖ < Rc)
    {s₁ : ℝ} (hτ : Lray.τ s₁ = Real.exp p) (hγ₁R : (Lray.γ₁ s₁).re < -Lray.R) :
    ∃ A : C(unitInterval, ℂ), A 0 = ((x₀ : ℝ) : ℂ) ∧ A 1 = Lray.γ₁ s₁ ∧
      (∀ r : unitInterval, (A r).re < -Lray.R) ∧
      (∀ r : unitInterval, fl.Ψ (A r) =
        Work.EL.rayPt d.hN (θ₀ + (r : ℝ) * (Work.EL.alpha1 - θ₀)) (Real.exp p)) := by
  classical
  have hpotz₁ : Work.EL.pot d.hN d.z₁ = 0 :=
    Work.EL.pot_of_mem d.hN (Work.GATE2.EXL.z1_mem_K d)
  have hexp1 : (1 : ℝ) < Real.exp p := by
    rw [Real.one_lt_exp_iff]; exact hp
  have hside : ∀ θ ∈ Set.Ico θ₀ Work.EL.alpha1,
      Work.EL.rayPt d.hN θ (Real.exp p) ∈ Work.EL.pairSideNear nest.P0 ∧
        Work.EL.rayPt d.hN θ (Real.exp p) ∈ Work.EL.pairSideNear (nest.Q n) :=
    fun θ hθ =>
      Work.GATE2.EXL.arc_mem_pairSideNear d.hN d.z₁ fl.Pa nest hQa hQb n hθ₀ hθ hexp1
  have hpre : ∀ θ ∈ Set.Ico θ₀ Work.EL.alpha1,
      Work.EL.rayPt d.hN θ (Real.exp p) ∈ fl.Ψ '' {w : ℂ | w.re < -Lray.R} :=
    Work.GATE2.EXL.arc_mem_preimage d fl nest (nest.Q n) hp hpg hsmall hcover hpotz₁
      (fun θ hθ => (hside θ hθ).1) (fun θ hθ => (hside θ hθ).2)
  have harc : ∀ θ ∈ Set.Icc θ₀ Work.EL.alpha1,
      Work.EL.rayPt d.hN θ (Real.exp p) ∈ fl.Ψ '' {w : ℂ | w.re < -Lray.R} := by
    intro θ hθ
    rcases lt_or_eq_of_le hθ.2 with hlt | heq
    · exact hpre θ ⟨hθ.1, hlt⟩
    · rw [heq]
      exact ⟨Lray.γ₁ s₁, hγ₁R, by rw [Lray.hΨ₁ s₁, hτ]⟩
  exact Work.GATE2.EXL.arcLift_exists d fl Lray hθ₀.2.le hx₀R hγ₁R hτ hx₀ harc

end Work.GATE2.EXL
