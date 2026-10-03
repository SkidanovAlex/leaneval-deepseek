import Mathlib
import Submission.Work.Motion.pertSetup
import Submission.Work.Motion.pertSupport
import Submission.Work.Motion.hasStrictFDerivAt_newtonMap
import Submission.Work.Motion.isInvertible_sndPartial_newtonMap
import Submission.Work.Motion.norm_newtonFixpoint_lt

/-!
# The moving Newton fixed point is holomorphic in the parameter

`Work.Motion.Pert.newtonFixpoint` produces, for every parameter `q` in the closed region
`closedBall γ ρ₁ ×ˢ closedBall p r₁`, a point `v q ∈ closedBall 0 ε` with
`Fmap τ m q (v q) = -Amap τ m q`, unique in that ball.  This file shows that the solution may be
chosen holomorphic in `q` on the open region `ball γ ρ₁ ×ˢ ball p r₁`.

The holomorphy is obtained from the implicit function theorem in the complex plane, in the form
`HasStrictFDerivAt.implicitFunctionOfProdDomain`: the residual
`Fp τ m p = (Tc p.1.1)^[m] (τ p.1.2 + p.2) - p.1.2` is strictly differentiable at `(q, v q)`
(`hasStrictFDerivAt_newtonMap`), its partial derivative in the second variable is multiplication
by `deriv (Fmap τ m q) (v q)`, which is within `b / 4` of `Bmap τ m q` of norm `≥ b > 0` and hence
invertible (`isInvertible_sndPartial_newtonMap`).  The implicit function `ψ` produced by the
theorem is holomorphic at `q`; near `q` it agrees with `v`, because its values are close to
`v q ∈ ball 0 ε` (`norm_newtonFixpoint_lt`) and the solution in `closedBall 0 ε` is unique.
-/

namespace Work.Motion

open LeanEval.Dynamics.MandelbrotBoundary
open Set Metric Filter Function
open scoped Topology

namespace Pert

/-- The Newton residual: for `p = (q, w)`,
`Fp τ m p = (Tc q.1)^[m] (τ q.2 + w) - q.2`; its zeroes are the moving fixed points. -/
def Fp (τ : ℂ → ℂ) (m : ℕ) : (ℂ × ℂ) × ℂ → ℂ :=
  fun p => TcIter m (p.1.1, τ p.1.2 + p.2) - p.1.2

@[simp] theorem Fp_apply (τ : ℂ → ℂ) (m : ℕ) (p : (ℂ × ℂ) × ℂ) :
    Fp τ m p = TcIter m (p.1.1, τ p.1.2 + p.2) - p.1.2 := rfl

/-- `Fp` is the sum of the defect `Amap` and the perturbed iterate `Fmap`. -/
theorem Fp_eq (τ : ℂ → ℂ) (m : ℕ) (q : ℂ × ℂ) (w : ℂ) :
    Fp τ m (q, w) = Fmap τ m q w + Amap τ m q := by
  simp only [Fp, Fmap_apply, Amap_apply]
  ring

/-- The zero set of `Fp` is the fixed point equation `Fmap q w = -Amap q`. -/
theorem Fp_eq_zero_iff (τ : ℂ → ℂ) (m : ℕ) (q : ℂ × ℂ) (w : ℂ) :
    Fp τ m (q, w) = 0 ↔ Fmap τ m q w = -Amap τ m q := by
  rw [Fp_eq]
  constructor <;> intro h <;> linear_combination h

end Pert

theorem newtonHolo {τ : ℂ → ℂ} {m : ℕ} {γ p : ℂ} {ρ₁ r₁ ε b : ℝ}
    (hε : 0 < ε) (hb : 0 < b) (hτ : DifferentiableOn ℂ τ (Metric.ball p r₁))
    (hB : ∀ q ∈ Metric.closedBall γ ρ₁ ×ˢ Metric.closedBall p r₁,
      b ≤ ‖Work.Motion.Pert.Bmap τ m q‖)
    (hA : ∀ q ∈ Metric.closedBall γ ρ₁ ×ˢ Metric.closedBall p r₁,
      ‖Work.Motion.Pert.Amap τ m q‖ ≤ b * ε / 4)
    (hd : ∀ q ∈ Metric.closedBall γ ρ₁ ×ˢ Metric.closedBall p r₁,
      ∀ w ∈ Metric.closedBall (0 : ℂ) ε, DifferentiableAt ℂ (Work.Motion.Pert.Fmap τ m q) w)
    (hbd : ∀ q ∈ Metric.closedBall γ ρ₁ ×ˢ Metric.closedBall p r₁,
      ∀ w ∈ Metric.closedBall (0 : ℂ) ε,
        ‖deriv (Work.Motion.Pert.Fmap τ m q) w - Work.Motion.Pert.Bmap τ m q‖ ≤ b / 4) :
    ∃ v : ℂ × ℂ → ℂ,
      (∀ q ∈ Metric.closedBall γ ρ₁ ×ˢ Metric.closedBall p r₁,
        v q ∈ Metric.closedBall (0 : ℂ) ε ∧
          Work.Motion.Pert.Fmap τ m q (v q) = -Work.Motion.Pert.Amap τ m q) ∧
      (∀ q ∈ Metric.closedBall γ ρ₁ ×ˢ Metric.closedBall p r₁, ∀ w ∈ Metric.closedBall (0 : ℂ) ε,
        Work.Motion.Pert.Fmap τ m q w = -Work.Motion.Pert.Amap τ m q → w = v q) ∧
      DifferentiableOn ℂ v (Metric.ball γ ρ₁ ×ˢ Metric.ball p r₁) := by
  classical
  set U : Set (ℂ × ℂ) := Metric.closedBall γ ρ₁ ×ˢ Metric.closedBall p r₁ with hU
  set S : Set (ℂ × ℂ) := Metric.ball γ ρ₁ ×ˢ Metric.ball p r₁ with hS
  -- the chosen solution of the moving fixed point equation
  let v : ℂ × ℂ → ℂ := fun q =>
    if hq : q ∈ U then
      (Pert.newtonFixpoint (F := Pert.Fmap τ m q) (A := Pert.Amap τ m q) (B := Pert.Bmap τ m q)
        (ε := ε) (b := b) hb hε (Pert.Fmap_zero τ m q) (hB q hq) (hA q hq) (hd q hq)
        (hbd q hq)).choose
    else 0
  have hv : ∀ q ∈ U, v q ∈ Metric.closedBall (0 : ℂ) ε ∧
      Pert.Fmap τ m q (v q) = -Pert.Amap τ m q ∧
      (∀ w ∈ Metric.closedBall (0 : ℂ) ε, Pert.Fmap τ m q w = -Pert.Amap τ m q → w = v q) := by
    intro q hq
    have h := (Pert.newtonFixpoint (F := Pert.Fmap τ m q) (A := Pert.Amap τ m q)
      (B := Pert.Bmap τ m q) (ε := ε) (b := b) hb hε (Pert.Fmap_zero τ m q) (hB q hq)
      (hA q hq) (hd q hq) (hbd q hq)).choose_spec
    dsimp only [v]
    rw [dite_eq_left hq]
    exact h
  refine ⟨v, ?_, ?_, ?_⟩
  · intro q hq
    exact ⟨(hv q hq).1, (hv q hq).2.1⟩
  · intro q hq w hw hwq
    exact (hv q hq).2.2 w hw hwq
  · -- holomorphy of the selected solution on the open region
    change DifferentiableOn ℂ v S
    have hSopen : IsOpen S := by
      rw [hS]
      exact Metric.isOpen_ball.prod Metric.isOpen_ball
    have hSU : S ⊆ U := by
      rw [hS, hU]
      intro q hq
      exact ⟨Metric.ball_subset_closedBall hq.1, Metric.ball_subset_closedBall hq.2⟩
    -- the solution lies in the *open* ball `ball 0 ε`
    have hmem : ∀ q ∈ S, ‖v q‖ < ε := by
      intro q hq
      have hqU : q ∈ U := hSU hq
      obtain ⟨hv1, hv2, -⟩ := hv q hqU
      exact norm_newtonFixpoint_lt (F := Pert.Fmap τ m q) (A := Pert.Amap τ m q)
        (B := Pert.Bmap τ m q) (ε := ε) (b := b) hb hε (Pert.Fmap_zero τ m q) (hB q hqU)
        (hA q hqU) (hd q hqU) (hbd q hqU) hv2 hv1
    intro q₀ hq₀
    have hqU : q₀ ∈ U := hSU hq₀
    have hq2 : q₀.2 ∈ Metric.ball p r₁ := hq₀.2
    -- `τ` is holomorphic in a neighbourhood of the relevant point
    have hτd : ∀ᶠ z in nhds q₀.2, DifferentiableAt ℂ τ z := by
      filter_upwards [Metric.isOpen_ball.mem_nhds hq2] with z hz
      exact hτ.differentiableAt (Metric.isOpen_ball.mem_nhds hz)
    set u : (ℂ × ℂ) × ℂ := (q₀, v q₀) with hu
    -- the implicit function theorem at `(q₀, v q₀)`
    have hstrict : HasStrictFDerivAt (Pert.Fp τ m) (fderiv ℂ (Pert.Fp τ m) u) u :=
      hasStrictFDerivAt_newtonMap (τ := τ) (m := m) (u := u) hτd
    have hInv : ((fderiv ℂ (Pert.Fp τ m) u) ∘L
        (ContinuousLinearMap.inr ℂ (ℂ × ℂ) ℂ)).IsInvertible :=
      isInvertible_sndPartial_newtonMap (τ := τ) (m := m) (u := u) (b := b) (ε := ε)
        hb hτd.self_of_nhds (hB q₀ hqU) (hbd q₀ hqU) (hv q₀ hqU).1
    set ψ : ℂ × ℂ → ℂ := hstrict.implicitFunctionOfProdDomain hInv with hψ
    have hψd : DifferentiableAt ℂ ψ q₀ :=
      (hstrict.hasStrictFDerivAt_implicitFunctionOfProdDomain hInv).differentiableAt
    have hten : Tendsto ψ (nhds q₀) (nhds (v q₀)) :=
      hstrict.tendsto_implicitFunctionOfProdDomain hInv
    -- near `q₀` the implicit solution stays in the closed ball
    have hcl : ∀ᶠ x in nhds q₀, ψ x ∈ Metric.closedBall (0 : ℂ) ε := by
      have hvε : ‖v q₀‖ < ε := hmem q₀ hq₀
      have hβ : 0 < ε - ‖v q₀‖ := sub_pos.mpr hvε
      have hb' := (Metric.tendsto_nhds.mp hten) (ε - ‖v q₀‖) hβ
      filter_upwards [hb'] with x hx
      rw [dist_eq_norm] at hx
      rw [Metric.mem_closedBall, dist_eq_norm, sub_zero]
      calc ‖ψ x‖ = ‖(ψ x - v q₀) + v q₀‖ := by congr 1; ring
        _ ≤ ‖ψ x - v q₀‖ + ‖v q₀‖ := norm_add_le _ _
        _ ≤ ε := by linarith
    -- the residual vanishes at `u`
    have hFu : Pert.Fp τ m u = 0 := by
      show Pert.Fp τ m (q₀, v q₀) = 0
      rw [Pert.Fp_eq_zero_iff]
      exact (hv q₀ hqU).2.1
    -- ... and at the implicit solution
    have hev : ∀ᶠ x in nhds q₀, Pert.Fp τ m (x, ψ x) = Pert.Fp τ m u :=
      hstrict.eventually_apply_implicitFunctionOfProdDomain hInv
    have hglue : ψ =ᶠ[nhds q₀] v := by
      filter_upwards [hcl, hev, hSopen.mem_nhds hq₀] with x hxcl hxev hxS
      have hxU : x ∈ U := hSU hxS
      have hx0 : Pert.Fp τ m (x, ψ x) = 0 := by rw [hxev, hFu]
      have heq : Pert.Fmap τ m x (ψ x) = -Pert.Amap τ m x :=
        (Pert.Fp_eq_zero_iff τ m x (ψ x)).mp hx0
      exact (hv x hxU).2.2 (ψ x) hxcl heq
    have hvd : DifferentiableAt ℂ v q₀ := hψd.congr_of_eventuallyEq hglue.symm
    exact hvd.differentiableWithinAt

end Work.Motion
