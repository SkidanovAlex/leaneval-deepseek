/-
Copyright: work module for the Elgindi finite-time singularity project.

# `Submission/Work/FTS/EpsEngine/UnifTraceDefs.lean` — the uniform (ε-δ) trace vocabulary

The class-`C` invariant of the local step's Picard iteration needs the boundary-trace data of the
raw slices in the **uniform** form that the mollifier consumes
(`StrongEps.BdryTraces_Jeps`'s hypotheses `hz0`/`hzin`/`ht0`/`ht1` and `axis_Jeps`'s `hax`).
`EpsEngine/ClassCFromHonesty.lean` also defines the *pointwise* halves `ZTraces`/`TauTraces` of
`BdryTraces`, and it was tempting to route the θ-half through them.  **That route is false**:
`TauTraces` is a statement at each fixed `z`, and `J_ε` averages over a fixed-length window in `z`
(the shift `z ↦ z e^{-p₁}`), so a *travelling spike*
`f(z',θ') = M · cos^β θ' · χ((z' - 1 - sin^{α/20}θ')/sin^{α/10}θ')` satisfies `TauTraces α k f`,
`SmoothOpen f` and the sup bounds, while `sin(2θ)^{-α/10}(J_ε f(1,θ))²` does not tend to `0`
(the spike is hit by a `p`-window whose measure is `~ sin^{α/20}θ`).  Hence the θ-half **must** be
routed through the uniform ε-δ conditions.

This module packages exactly those conditions (`UnifTrace`), proves the elementary consequences
(`TauTraces`, `BdryTraces` from `UnifTrace` plus the pointwise `z`-half), and is the vocabulary in
which the two analytic residuals of the class-`C` invariance are stated.

Everything here is `sorry`-free.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS.EpsEngine.ClassCFromHonesty

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter
open Work.FTS.Galerkin (Fn)

namespace Work.FTS.EpsEngine

set_option autoImplicit false
set_option linter.unusedVariables false

/-- **The uniform (ε-δ) boundary-trace data of a profile up to order `k`**: the four conditions
consumed by `StrongEps.BdryTraces_Jeps` (radial and angular, at both ends, uniform in the *other*
variable) together with the `ε`-`δ` axis condition of `StrongEps.axis_Jeps` and the sup bounds of
`SoftClass.hbdd`.  This is exactly `SoftClass`'s hypothesis list about the *source* profile. -/
structure UnifTrace (α : ℝ) (k : ℕ) (f : Fn) : Prop where
  /-- the slots are bounded on the whole open quadrant. -/
  bdd : ∀ a b : ℕ, a + b ≤ k → ∃ M : ℝ, ∀ z θ : ℝ, 0 < z →
    θ ∈ Set.Ioo 0 (Real.pi / 2) → |Work.Spaces.mixed b a f z θ| ≤ M
  /-- radial vanishing at `z → 0⁺`, uniformly in `θ`. -/
  z0 : ∀ a b : ℕ, a + b ≤ k → ∀ ε' > 0, ∃ δ > 0, ∀ z : ℝ, 0 < z → z < δ →
    ∀ θ : ℝ, θ ∈ Set.Ioo 0 (Real.pi / 2) →
      z * (Work.Spaces.mixed b a f z θ * Work.Spaces.w z) ^ 2 ≤ ε'
  /-- radial vanishing at `z → ∞`, uniformly in `θ`. -/
  zin : ∀ a b : ℕ, a + b ≤ k → ∀ ε' > 0, ∃ Z : ℝ, ∀ z : ℝ, Z < z →
    ∀ θ : ℝ, θ ∈ Set.Ioo 0 (Real.pi / 2) →
      z * (Work.Spaces.mixed b a f z θ * Work.Spaces.w z) ^ 2 ≤ ε'
  /-- angular vanishing at `θ → 0⁺`, uniformly in `z`. -/
  t0 : ∀ a b : ℕ, a + b ≤ k → ∀ ε' > 0, ∃ δ > 0, ∀ θ : ℝ, 0 < θ → θ < δ →
    ∀ z : ℝ, 0 < z →
      Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α) * (Work.Spaces.mixed b a f z θ) ^ 2 ≤ ε'
  /-- angular vanishing at `θ → (π/2)⁻`, uniformly in `z`. -/
  t1 : ∀ a b : ℕ, a + b ≤ k → ∀ ε' > 0, ∃ δ > 0, ∀ θ : ℝ, θ < Real.pi / 2 →
    Real.pi / 2 - δ < θ → ∀ z : ℝ, 0 < z →
      Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α) * (Work.Spaces.mixed b a f z θ) ^ 2 ≤ ε'
  /-- the axis condition `f = o(z)` at `z → 0⁺`, uniformly in `θ`. -/
  ax : ∀ ε' > 0, ∃ δ > 0, ∀ z : ℝ, 0 < z → z < δ →
    ∀ θ : ℝ, θ ∈ Set.Ioo 0 (Real.pi / 2) → |f z θ / z| ≤ ε'

/-- **The uniform ANGULAR flatness alone** (the two ε-δ conditions at the θ-ends, uniform in
`z`).  This is the input that the mollifier consumes for the angular half of the traces, and — by
contrast with `UnifTrace` — it carries *no* radial condition, which is what lets the class-`C`
invariance of the local step avoid the (*hard*) radial flatness `profRHS = O(z²)`: the radial half
of `BdryTraces` is obtained from honesty through the leaf (T1). -/
structure ThetaUnif (α : ℝ) (k : ℕ) (f : Fn) : Prop where
  /-- angular vanishing at `θ → 0⁺`, uniformly in `z`. -/
  t0 : ∀ a b : ℕ, a + b ≤ k → ∀ ε' > 0, ∃ δ > 0, ∀ θ : ℝ, 0 < θ → θ < δ →
    ∀ z : ℝ, 0 < z →
      Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α) * (Work.Spaces.mixed b a f z θ) ^ 2 ≤ ε'
  /-- angular vanishing at `θ → (π/2)⁻`, uniformly in `z`. -/
  t1 : ∀ a b : ℕ, a + b ≤ k → ∀ ε' > 0, ∃ δ > 0, ∀ θ : ℝ, θ < Real.pi / 2 →
    Real.pi / 2 - δ < θ → ∀ z : ℝ, 0 < z →
      Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α) * (Work.Spaces.mixed b a f z θ) ^ 2 ≤ ε'

/-- `UnifTrace` contains the angular conditions. -/
theorem UnifTrace.thetaUnif {α : ℝ} {k : ℕ} {f : Fn} (h : UnifTrace α k f) :
    ThetaUnif α k f := ⟨h.t0, h.t1⟩

/-- The two angular ε-δ conditions give the pointwise θ-half `TauTraces` (a shared helper). -/
theorem tauTraces_of_theta {α : ℝ} {k : ℕ} {f : Fn}
    (t0 : ∀ a b : ℕ, a + b ≤ k → ∀ ε' > 0, ∃ δ > 0, ∀ θ : ℝ, 0 < θ → θ < δ →
      ∀ z : ℝ, 0 < z →
        Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α) * (Work.Spaces.mixed b a f z θ) ^ 2 ≤ ε')
    (t1 : ∀ a b : ℕ, a + b ≤ k → ∀ ε' > 0, ∃ δ > 0, ∀ θ : ℝ, θ < Real.pi / 2 →
      Real.pi / 2 - δ < θ → ∀ z : ℝ, 0 < z →
        Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α) * (Work.Spaces.mixed b a f z θ) ^ 2 ≤ ε') :
    TauTraces α k f := by
  intro a b hab z hz
  have hzpos : 0 < z := hz
  refine ⟨?_, ?_⟩
  · rw [Metric.tendsto_nhds]
    intro η hη
    have htol : (0 : ℝ) < min 1 (η / 2) := lt_min one_pos (by linarith)
    obtain ⟨δ, hδpos, hδ⟩ := t0 a b hab (min 1 (η / 2)) htol
    have hlt : (0 : ℝ) < min δ 1 := lt_min hδpos one_pos
    filter_upwards [Ioo_mem_nhdsGT hlt] with θ hθ
    have hθδ : θ < δ := lt_of_lt_of_le hθ.2 (min_le_left _ _)
    have hθ1 : θ < 1 := lt_of_lt_of_le hθ.2 (min_le_right _ _)
    have h1 := hδ θ hθ.1 hθδ z hzpos
    have harg : 0 ≤ 2 * θ ∧ 2 * θ ≤ Real.pi :=
      ⟨by linarith [hθ.1], by linarith [hθ1, Real.pi_gt_three]⟩
    have hs : 0 ≤ Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α) :=
      Real.rpow_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi harg.1 harg.2) _
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (mul_nonneg hs (sq_nonneg _))]
    linarith [le_trans h1 (min_le_right _ _)]
  · rw [Metric.tendsto_nhds]
    intro η hη
    have htol : (0 : ℝ) < min 1 (η / 2) := lt_min one_pos (by linarith)
    obtain ⟨δ, hδpos, hδ⟩ := t1 a b hab (min 1 (η / 2)) htol
    have hlt : Real.pi / 2 - min δ 1 < Real.pi / 2 := by
      have hpos : 0 < min δ 1 := lt_min hδpos one_pos
      linarith
    filter_upwards [Ioo_mem_nhdsLT hlt] with θ hθ
    have hθδ : Real.pi / 2 - δ < θ := by
      have h1 : Real.pi / 2 - δ ≤ Real.pi / 2 - min δ 1 := by
        linarith [min_le_left δ (1 : ℝ)]
      linarith [hθ.1]
    have hθu : 1 < Real.pi / 2 := by linarith [Real.pi_gt_three]
    have hθ1 : Real.pi / 2 - 1 < θ := by
      have h1 : Real.pi / 2 - 1 ≤ Real.pi / 2 - min δ 1 := by
        linarith [min_le_right δ (1 : ℝ)]
      linarith [hθ.1]
    have h1 := hδ θ hθ.2 hθδ z hzpos
    have harg : 0 ≤ 2 * θ ∧ 2 * θ ≤ Real.pi :=
      ⟨by linarith [hθ1, hθu], by linarith [hθ.2]⟩
    have hs : 0 ≤ Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α) :=
      Real.rpow_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi harg.1 harg.2) _
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (mul_nonneg hs (sq_nonneg _))]
    linarith [le_trans h1 (min_le_right _ _)]

/-- `ThetaUnif` gives the pointwise θ-half `TauTraces`. -/
theorem ThetaUnif.tauTraces {α : ℝ} {k : ℕ} {f : Fn} (h : ThetaUnif α k f) :
    TauTraces α k f := tauTraces_of_theta h.t0 h.t1

/-- **The uniform data gives the pointwise θ-half `TauTraces`.** -/
theorem UnifTrace.tauTraces {α : ℝ} {k : ℕ} {f : Fn} (h : UnifTrace α k f) :
    TauTraces α k f := tauTraces_of_theta h.t0 h.t1

/-- **The uniform data plus the pointwise `z`-half gives `BdryTraces`.** -/
theorem UnifTrace.bdryTraces {α : ℝ} {k : ℕ} {f : Fn} (h : UnifTrace α k f)
    (hz : ZTraces α k f) : Work.FTS.Nonlin.BdryTraces α k f :=
  bdryTraces_of_z_tau hz h.tauTraces

end Work.FTS.EpsEngine
