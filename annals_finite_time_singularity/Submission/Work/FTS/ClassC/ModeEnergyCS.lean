/-
Copyright: work module for the Elgindi finite-time singularity project.

# `FTS/ClassC/ModeEnergyCS` — the weighted `L²` corollary of the per-mode energy identity

`modeWeightedEnergy` (`Submission/Work/FTS/ClassC/modeWeightedEnergy.lean`) gives, for a solution
`a` of the mode-`m` radial equation `α²z²a'' + α(5+α)z a' = λ a − c` whose flux vanishes at both
ends,

  `α²∫_0^∞ (z a')² w²  +  (λ − 3α² − 3α(5+α)/2) ∫_0^∞ a² w²  ≤  ∫_0^∞ c a w²`.

The elementary inequality `2 μ x y ≤ x² + μ² y²` (for `μ > 0`, the AM–GM inequality applied to
`x = c w`, `y = a w`) bounds the pairing by `(∫ c² w² + μ² ∫ a² w²)/(2μ)`; feeding that back
into the identity cancels the `a²`-term and leaves the **sharp per-mode bound**

  `μ² · ∫_0^∞ a² w²  ≤  ∫_0^∞ c² w²`,      `μ = λ − 3α² − 3α(5+α)/2`      (`modeWeightedEnergy_sq`),

equivalently `μ · ‖a w‖₂ ≤ ‖c w‖₂` (`modeWeightedEnergy_norm`).  For `m ≥ 1`,
`λ_m = 2m(2m+5) ≥ 14` and `0 < α ≤ 1/4` give `μ ≥ 11.8`, so this is the `λ_m^{-1}` gain that
makes the mode sums of the honest-modal route (`NOTES_mode_energy.md`) converge.

The two statements are the raw and the normalised form of the bound; the coefficient is kept as
the explicit expression `lam − 3α² − 3α(5+α)/2` rather than a named constant, so that consumers
can substitute `lam = lamR m = 2m(2m+5)` and use arithmetic.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.ClassC.modeWeightedEnergy

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.ClassC

set_option autoImplicit false

/-! ## Nonnegativity of the two weighted `L²` functionals -/

/-- Nonnegativity of the weighted `L²` functional `∫_0^∞ f² w²`. -/
theorem integral_sq_w_sq_nonneg (f : ℝ → ℝ) :
    0 ≤ ∫ z in Set.Ioi 0, (f z) ^ 2 * (Work.Spaces.w z) ^ 2 :=
  MeasureTheory.integral_nonneg_of_ae (μ := volume.restrict (Set.Ioi 0))
    (Filter.Eventually.of_forall fun z => by positivity)

/-- Nonnegativity of the weighted gradient functional `∫_0^∞ (z f')² w²`. -/
theorem integral_grad_w_sq_nonneg (f : ℝ → ℝ) :
    0 ≤ ∫ z in Set.Ioi 0, (z * deriv f z) ^ 2 * (Work.Spaces.w z) ^ 2 :=
  MeasureTheory.integral_nonneg_of_ae (μ := volume.restrict (Set.Ioi 0))
    (Filter.Eventually.of_forall fun z => by positivity)

/-! ## The AM–GM bound of the weighted pairing -/

/-- **The AM–GM bound.**  For `μ > 0`, the weighted pairing is dominated by
`(∫ c² w² + μ² ∫ a² w²)/(2μ)`.  Pointwise this is
`2μ·c a w² ≤ c² w² + μ² a² w²`, the elementary inequality `2 μ x y ≤ x² + μ² y²` with
`x = c w`, `y = a w`. -/
theorem integral_pairing_le {μ : ℝ} (hμ : 0 < μ) {a c : ℝ → ℝ}
    (hint3 : MeasureTheory.IntegrableOn
      (fun z => c z * a z * (Work.Spaces.w z) ^ 2) (Set.Ioi 0))
    (hint2 : MeasureTheory.IntegrableOn
      (fun z => (a z) ^ 2 * (Work.Spaces.w z) ^ 2) (Set.Ioi 0))
    (hint4 : MeasureTheory.IntegrableOn
      (fun z => (c z) ^ 2 * (Work.Spaces.w z) ^ 2) (Set.Ioi 0)) :
    (∫ z in Set.Ioi 0, c z * a z * (Work.Spaces.w z) ^ 2)
      ≤ ((∫ z in Set.Ioi 0, (c z) ^ 2 * (Work.Spaces.w z) ^ 2)
          + μ ^ 2 * (∫ z in Set.Ioi 0, (a z) ^ 2 * (Work.Spaces.w z) ^ 2)) / (2 * μ) := by
  have h2μ : 0 < 2 * μ := by linarith
  have hInt : MeasureTheory.IntegrableOn
      (fun z => (((c z) ^ 2 * (Work.Spaces.w z) ^ 2)
          + μ ^ 2 * ((a z) ^ 2 * (Work.Spaces.w z) ^ 2)) / (2 * μ)) (Set.Ioi 0) :=
    (hint4.add (hint2.const_mul _)).div_const _
  have hmono := MeasureTheory.setIntegral_mono hint3 hInt (fun z => by
    have h := sq_nonneg (c z * Work.Spaces.w z - μ * (a z * Work.Spaces.w z))
    have e : (c z * Work.Spaces.w z - μ * (a z * Work.Spaces.w z)) ^ 2
        = (c z) ^ 2 * (Work.Spaces.w z) ^ 2
          - 2 * μ * (c z * a z * (Work.Spaces.w z) ^ 2)
          + μ ^ 2 * ((a z) ^ 2 * (Work.Spaces.w z) ^ 2) := by ring
    rw [e] at h
    rw [le_div_iff₀ h2μ]
    nlinarith [h])
  calc (∫ z in Set.Ioi 0, c z * a z * (Work.Spaces.w z) ^ 2)
      ≤ ∫ z in Set.Ioi 0, (((c z) ^ 2 * (Work.Spaces.w z) ^ 2)
          + μ ^ 2 * ((a z) ^ 2 * (Work.Spaces.w z) ^ 2)) / (2 * μ) := hmono
    _ = ((∫ z in Set.Ioi 0, (c z) ^ 2 * (Work.Spaces.w z) ^ 2)
          + μ ^ 2 * (∫ z in Set.Ioi 0, (a z) ^ 2 * (Work.Spaces.w z) ^ 2)) / (2 * μ) := by
        rw [MeasureTheory.integral_div,
          MeasureTheory.integral_add hint4 (hint2.const_mul _),
          MeasureTheory.integral_const_mul]

/-! ## The sharp weighted `L²` per-mode bound -/

/-- **The sharp per-mode bound, squared form.**  Under the hypotheses of `modeWeightedEnergy`
together with the integrability of `c² w²` and the positivity of
`μ = lam − 3α² − 3α(5+α)/2`, one has `μ² ∫ a² w² ≤ ∫ c² w²`. -/
theorem modeWeightedEnergy_sq {α lam : ℝ} (hα : 0 < α) {a c : ℝ → ℝ}
    (hac : ContinuousOn a (Set.Ioi 0))
    (ha : ∀ z, 0 < z → HasDerivAt a (deriv a z) z)
    (ha' : ∀ z, 0 < z → HasDerivAt (deriv a) (deriv (deriv a) z) z)
    (hode : ∀ z, 0 < z → α ^ 2 * z ^ 2 * deriv (deriv a) z + α * (5 + α) * z * deriv a z
        = lam * a z - c z)
    (hint1 : MeasureTheory.IntegrableOn
      (fun z => (z * deriv a z) ^ 2 * (Work.Spaces.w z) ^ 2) (Set.Ioi 0))
    (hint2 : MeasureTheory.IntegrableOn
      (fun z => (a z) ^ 2 * (Work.Spaces.w z) ^ 2) (Set.Ioi 0))
    (hint3 : MeasureTheory.IntegrableOn
      (fun z => c z * a z * (Work.Spaces.w z) ^ 2) (Set.Ioi 0))
    (hint4 : MeasureTheory.IntegrableOn
      (fun z => (c z) ^ 2 * (Work.Spaces.w z) ^ 2) (Set.Ioi 0))
    (hcont : ContinuousWithinAt (Work.FTS.ClassC.flux α a) (Set.Ici 0) 0)
    (hdec : Filter.Tendsto (Work.FTS.ClassC.flux α a) Filter.atTop (nhds 0))
    (hmu : 0 < lam - 3 * α ^ 2 - 3 * α * (5 + α) / 2) :
    (lam - 3 * α ^ 2 - 3 * α * (5 + α) / 2) ^ 2
        * (∫ z in Set.Ioi 0, (a z) ^ 2 * (Work.Spaces.w z) ^ 2)
      ≤ ∫ z in Set.Ioi 0, (c z) ^ 2 * (Work.Spaces.w z) ^ 2 := by
  have hbase := modeWeightedEnergy (α := α) (lam := lam) hα hac ha ha' hode hint1 hint2 hint3
    hcont hdec
  set mu := lam - 3 * α ^ 2 - 3 * α * (5 + α) / 2 with hmu_def
  set A := ∫ z in Set.Ioi 0, (a z) ^ 2 * (Work.Spaces.w z) ^ 2 with hA_def
  set B := ∫ z in Set.Ioi 0, (c z) ^ 2 * (Work.Spaces.w z) ^ 2 with hB_def
  set P := ∫ z in Set.Ioi 0, c z * a z * (Work.Spaces.w z) ^ 2 with hP_def
  have hmu_pos : 0 < mu := hmu
  have hgrad : 0 ≤ ∫ z in Set.Ioi 0, (z * deriv a z) ^ 2 * (Work.Spaces.w z) ^ 2 :=
    integral_grad_w_sq_nonneg a
  have hmuA : mu * A ≤ P := by
    have h2 : 0 ≤ α ^ 2 * (∫ z in Set.Ioi 0, (z * deriv a z) ^ 2 * (Work.Spaces.w z) ^ 2) :=
      mul_nonneg (sq_nonneg α) hgrad
    linarith
  have hamgm := integral_pairing_le hmu_pos hint3 hint2 hint4
  have h2μ : 0 < 2 * mu := by linarith
  rw [le_div_iff₀ h2μ] at hamgm
  nlinarith [hmuA, hamgm]

/-- **The sharp per-mode bound, normalised form**: `μ · ‖a w‖₂ ≤ ‖c w‖₂` with
`μ = lam − 3α² − 3α(5+α)/2 > 0` and `‖f w‖₂ = √(∫_0^∞ f² w²)`. -/
theorem modeWeightedEnergy_norm {α lam : ℝ} (hα : 0 < α) {a c : ℝ → ℝ}
    (hac : ContinuousOn a (Set.Ioi 0))
    (ha : ∀ z, 0 < z → HasDerivAt a (deriv a z) z)
    (ha' : ∀ z, 0 < z → HasDerivAt (deriv a) (deriv (deriv a) z) z)
    (hode : ∀ z, 0 < z → α ^ 2 * z ^ 2 * deriv (deriv a) z + α * (5 + α) * z * deriv a z
        = lam * a z - c z)
    (hint1 : MeasureTheory.IntegrableOn
      (fun z => (z * deriv a z) ^ 2 * (Work.Spaces.w z) ^ 2) (Set.Ioi 0))
    (hint2 : MeasureTheory.IntegrableOn
      (fun z => (a z) ^ 2 * (Work.Spaces.w z) ^ 2) (Set.Ioi 0))
    (hint3 : MeasureTheory.IntegrableOn
      (fun z => c z * a z * (Work.Spaces.w z) ^ 2) (Set.Ioi 0))
    (hint4 : MeasureTheory.IntegrableOn
      (fun z => (c z) ^ 2 * (Work.Spaces.w z) ^ 2) (Set.Ioi 0))
    (hcont : ContinuousWithinAt (Work.FTS.ClassC.flux α a) (Set.Ici 0) 0)
    (hdec : Filter.Tendsto (Work.FTS.ClassC.flux α a) Filter.atTop (nhds 0))
    (hmu : 0 < lam - 3 * α ^ 2 - 3 * α * (5 + α) / 2) :
    (lam - 3 * α ^ 2 - 3 * α * (5 + α) / 2)
        * Real.sqrt (∫ z in Set.Ioi 0, (a z) ^ 2 * (Work.Spaces.w z) ^ 2)
      ≤ Real.sqrt (∫ z in Set.Ioi 0, (c z) ^ 2 * (Work.Spaces.w z) ^ 2) := by
  have hsq := modeWeightedEnergy_sq hα hac ha ha' hode hint1 hint2 hint3 hint4 hcont hdec hmu
  set mu := lam - 3 * α ^ 2 - 3 * α * (5 + α) / 2 with hmu_def
  set A := ∫ z in Set.Ioi 0, (a z) ^ 2 * (Work.Spaces.w z) ^ 2 with hA_def
  set B := ∫ z in Set.Ioi 0, (c z) ^ 2 * (Work.Spaces.w z) ^ 2 with hB_def
  have hmu_pos : 0 < mu := hmu
  have h := Real.sqrt_le_sqrt hsq
  rw [Real.sqrt_mul (sq_nonneg mu), Real.sqrt_sq (le_of_lt hmu_pos)] at h
  exact h

end Work.FTS.ClassC
