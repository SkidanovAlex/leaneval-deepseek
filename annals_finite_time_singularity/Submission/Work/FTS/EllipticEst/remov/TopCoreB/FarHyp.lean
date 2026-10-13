import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.EllipticEst.StraightDefs
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.EllipticEst.remov.TopCoreB.FarDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The hypothesis bundle and the right-hand side of the far-region estimate

The far-region angular estimate `TopCoreB.slice_ang_far` of Elgindi's §"General ℋ^k case"
bounds the top angular derivative slot on `[3π/8, π/2]` by the *lower* slots, the source slot
and the three low-order quantities.  Everything the estimate needs is collected here, so that
the individual steps of the proof can be stated (and proved) independently of the target.

Vocabulary (all in `Work.FTS.EllipticEst.remov.TopCoreB`):

* `qW k γ θ = sin(2θ)^{2k-γ}` (the weight of the top slot; already in `FarDefs`),
* `vF u = u / cos θ` (already in `FarDefs`),
* `farSet = Icc (3π/8) (π/2)` (the far window),
* `FarR k γ u g` — the right-hand side of the target (without the constant),
* `FarHyp k γ u g` — the hypotheses of the target.
-/

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.remov.TopCoreB

set_option autoImplicit false

/-- The far window `[3π/8, π/2]` of the angular estimate. -/
def farSet : Set ℝ := Set.Icc (3 * Real.pi / 8) (Real.pi / 2)

/-- The right-hand side of the far-region estimate (the target's parenthesised factor). -/
def FarR (k : ℕ) (γ : ℝ) (u g : ℝ → ℝ) : ℝ :=
  (∫ θ in Work.Spaces.Iθ, (iteratedDeriv k g θ) ^ 2
      * Real.rpow (Real.sin (2 * θ)) (2 * (k : ℝ) - γ))
    + (∑ j ∈ Finset.Icc 3 (k + 1), ∫ θ in Work.Spaces.Iθ, (iteratedDeriv j u θ) ^ 2
        * Real.rpow (Real.sin (2 * θ)) (2 * (j : ℝ) - 4 - γ))
    + (∫ θ in Work.Spaces.Iθ, (deriv (deriv u) θ) ^ 2
        * Real.rpow (Real.sin (2 * θ)) (-(Work.Spaces.eta)))
    + (∫ θ in Work.Spaces.Iθ, (deriv u θ) ^ 2)
    + (∫ θ in Work.Spaces.Iθ, (u θ) ^ 2)

/-- The hypotheses of the far-region estimate, bundled. -/
def FarHyp (k : ℕ) (γ : ℝ) (u g : ℝ → ℝ) : Prop :=
  1 ≤ γ ∧ γ ≤ 5 / 4 ∧
  ContDiffOn ℝ (k + 2) u (Set.Ioo 0 (Real.pi / 2)) ∧
  ContinuousOn u (Set.Icc 0 (Real.pi / 2)) ∧
  u 0 = 0 ∧ u (Real.pi / 2) = 0 ∧
  (∀ θ ∈ Set.Ioo 0 (Real.pi / 2), g θ = Work.FTS.EllipticEst.Lzero1 u θ) ∧
  MeasureTheory.IntegrableOn (fun θ => (iteratedDeriv (k + 2) u θ) ^ 2
      * Real.rpow (Real.sin (2 * θ)) (2 * (k : ℝ) - γ)) Work.Spaces.Iθ ∧
  MeasureTheory.IntegrableOn (fun θ => (iteratedDeriv k g θ) ^ 2
      * Real.rpow (Real.sin (2 * θ)) (2 * (k : ℝ) - γ)) Work.Spaces.Iθ ∧
  (∀ j ∈ Finset.Icc 3 (k + 1), MeasureTheory.IntegrableOn
      (fun θ => (iteratedDeriv j u θ) ^ 2
        * Real.rpow (Real.sin (2 * θ)) (2 * (j : ℝ) - 4 - γ)) Work.Spaces.Iθ) ∧
  MeasureTheory.IntegrableOn (fun θ => (deriv (deriv u) θ) ^ 2
      * Real.rpow (Real.sin (2 * θ)) (-(Work.Spaces.eta))) Work.Spaces.Iθ ∧
  MeasureTheory.IntegrableOn (fun θ => (deriv u θ) ^ 2) Work.Spaces.Iθ ∧
  MeasureTheory.IntegrableOn (fun θ => (u θ) ^ 2) Work.Spaces.Iθ

/-- The far window sits inside `Iθ`. -/
theorem farSet_subset_Iθ : farSet ⊆ Work.Spaces.Iθ := by
  intro x hx
  exact ⟨by linarith [hx.1, Real.pi_pos], by linarith [hx.2, Real.pi_pos]⟩

section Projections

variable {k : ℕ} {γ : ℝ} {u g : ℝ → ℝ}

theorem FarHyp.hγ1 (h : FarHyp k γ u g) : 1 ≤ γ := h.1
theorem FarHyp.hγ2 (h : FarHyp k γ u g) : γ ≤ 5 / 4 := h.2.1
theorem FarHyp.huC (h : FarHyp k γ u g) :
    ContDiffOn ℝ (k + 2) u (Set.Ioo 0 (Real.pi / 2)) := h.2.2.1
theorem FarHyp.hucont (h : FarHyp k γ u g) :
    ContinuousOn u (Set.Icc 0 (Real.pi / 2)) := h.2.2.2.1
theorem FarHyp.hu0 (h : FarHyp k γ u g) : u 0 = 0 := h.2.2.2.2.1
theorem FarHyp.hupi (h : FarHyp k γ u g) : u (Real.pi / 2) = 0 := h.2.2.2.2.2.1
theorem FarHyp.hg (h : FarHyp k γ u g) :
    ∀ θ ∈ Set.Ioo 0 (Real.pi / 2), g θ = Work.FTS.EllipticEst.Lzero1 u θ :=
  h.2.2.2.2.2.2.1
theorem FarHyp.hH1 (h : FarHyp k γ u g) :
    MeasureTheory.IntegrableOn (fun θ => (iteratedDeriv (k + 2) u θ) ^ 2
      * Real.rpow (Real.sin (2 * θ)) (2 * (k : ℝ) - γ)) Work.Spaces.Iθ := h.2.2.2.2.2.2.2.1
theorem FarHyp.hH2 (h : FarHyp k γ u g) :
    MeasureTheory.IntegrableOn (fun θ => (iteratedDeriv k g θ) ^ 2
      * Real.rpow (Real.sin (2 * θ)) (2 * (k : ℝ) - γ)) Work.Spaces.Iθ :=
  h.2.2.2.2.2.2.2.2.1
theorem FarHyp.hH3 (h : FarHyp k γ u g) :
    ∀ j ∈ Finset.Icc 3 (k + 1), MeasureTheory.IntegrableOn
      (fun θ => (iteratedDeriv j u θ) ^ 2
        * Real.rpow (Real.sin (2 * θ)) (2 * (j : ℝ) - 4 - γ)) Work.Spaces.Iθ :=
  h.2.2.2.2.2.2.2.2.2.1
theorem FarHyp.hH4 (h : FarHyp k γ u g) :
    MeasureTheory.IntegrableOn (fun θ => (deriv (deriv u) θ) ^ 2
      * Real.rpow (Real.sin (2 * θ)) (-(Work.Spaces.eta))) Work.Spaces.Iθ :=
  h.2.2.2.2.2.2.2.2.2.2.1
theorem FarHyp.hH5 (h : FarHyp k γ u g) :
    MeasureTheory.IntegrableOn (fun θ => (deriv u θ) ^ 2) Work.Spaces.Iθ :=
  h.2.2.2.2.2.2.2.2.2.2.2.1
theorem FarHyp.hH6 (h : FarHyp k γ u g) :
    MeasureTheory.IntegrableOn (fun θ => (u θ) ^ 2) Work.Spaces.Iθ :=
  h.2.2.2.2.2.2.2.2.2.2.2.2

end Projections

/-- `3π/8 < π/2`. -/
theorem three_pi_eight_lt_pi_half : 3 * Real.pi / 8 < Real.pi / 2 := by
  linarith [Real.pi_pos]

/-- On the far window, `sin θ ≥ sin(3π/8) > 0`. -/
theorem sin_ge_sin_three_pi_eight_of_far {θ : ℝ} (hθ : θ ∈ farSet) :
    Real.sin (3 * Real.pi / 8) ≤ Real.sin θ := by
  have h1 : θ ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2) :=
    ⟨by linarith [hθ.1, Real.pi_pos], by linarith [hθ.2, Real.pi_pos]⟩
  have h2 : (3 * Real.pi / 8) ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2) :=
    ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
  exact Real.monotoneOn_sin h2 h1 hθ.1

/-- On the far window, `sin θ > 0`. -/
theorem sin_pos_of_far {θ : ℝ} (hθ : θ ∈ farSet) : 0 < Real.sin θ :=
  lt_of_lt_of_le (Real.sin_pos_of_pos_of_lt_pi (by linarith [Real.pi_pos])
    (by linarith [Real.pi_pos])) (sin_ge_sin_three_pi_eight_of_far hθ)

/-- On the far window, the double angle sine is nonnegative. -/
theorem sin_two_nonneg_of_far {θ : ℝ} (hθ : θ ∈ farSet) : 0 ≤ Real.sin (2 * θ) := by
  refine Real.sin_nonneg_of_mem_Icc ⟨by linarith [hθ.1, Real.pi_pos], ?_⟩
  linarith [hθ.2, Real.pi_pos]

/-- Monotonicity: a nonnegative density integrated over the far window is at most its integral
over `Iθ`. -/
theorem farIntegral_le_Iθ {f : ℝ → ℝ} (hf : MeasureTheory.IntegrableOn f Work.Spaces.Iθ)
    (hnn : ∀ θ ∈ Work.Spaces.Iθ, 0 ≤ f θ) :
    ∫ θ in farSet, f θ ≤ ∫ θ in Work.Spaces.Iθ, f θ := by
  refine MeasureTheory.setIntegral_mono_set hf ?_ ?_
  · filter_upwards [MeasureTheory.ae_restrict_mem (μ := MeasureTheory.volume)
      (show MeasurableSet Work.Spaces.Iθ from measurableSet_Icc)] with x hx
    exact hnn x hx
  · exact Filter.Eventually.of_forall (fun x hx => farSet_subset_Iθ hx)

end Work.FTS.EllipticEst.remov.TopCoreB
