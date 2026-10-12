import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixB2.DvApriori.MomBilDefs
import Submission.Work.BoseKinLoc.Kinetic.continuous_Qfree_L2
import Submission.Work.BoseKinLoc.Momentum.memLp_kinFT
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.Analysis.BoseBand.MomWordOffdiag.integrable_momProj_inner_fibre_bound`

**A uniform-in-`x` domination bound for the polarised large-momentum fibre integrand.**

For two smooth `n`-body states `A, B : X n → ℝ`, a slot `j : Fin n` and `x` in the centred
`n`-particle box `abox n ℓ`, the polarised large-momentum integrand of FS `eq:DefT`'s third
piece is

    `p ↦ momProj ℓ d p · ⟨kinFT (boxState ℓ 0 (fibre n j A x)) p ,
                          kinFT (boxState ℓ 0 (fibre n j B x)) p⟩`,

and this module proves that this `p`-section is integrable and that the integral of its norm
is bounded **uniformly over `x ∈ abox n ℓ`** by a single constant `K ≥ 0`.

## Why this is not a crude bound

`momProj ℓ d` is the indicator of the *unbounded* region `‖p‖ > (d²ℓ)⁻¹`, so a pointwise bound
on the integrand cannot work: the saving is the `L²` decay of the Fourier transform.  For each
`x` the localised mean-free box state `1_{Λ(0)}(ψ_x − m)` is supported in the compact cube
`Λ(0) = acube ℓ` and bounded, hence in `L¹ ∩ L²` (`boxState_memLp`, valid for an arbitrary
smooth `ψ`), and Plancherel (`kinFT_sq_of_memLp`) gives

    `(2π)⁻³ ∫_p ‖kinFT (boxState ψ_x) p‖² = ∫_z ‖boxState ψ_x z‖² = ∫_{acube ℓ} (Q₀ψ_x)²`.

For `x ∈ abox n ℓ` the first slot integral `∫_{acube ℓ}(Q₀ψ_x)²` is *continuous* in `x`
(`continuous_Qfree_L2` over the jointly continuous family `(x,z) ↦ Ψ(x_{j←z})`), hence bounded
on the compact `abox n ℓ`; this is the uniform constant.  The polarised integrand is then
dominated by `½·momProj·(‖F‖² + ‖G‖²)` (`‖⟨u,v⟩‖ ≤ ½(‖u‖²+‖v‖²)`), which is integrable.

## Contents

* `norm_mul_inner_le` — the pointwise polarisation bound;
* `lamBox_zero_eq_acube'` — the anchored moving box is the centred cube;
* `fibre_section_integrable` — Plancherel/`L²`: a single `p`-section is integrable;
* `fibre_section_bound` — the uniform-in-`x ∈ abox` bound on a single `p`-integral;
* `integrable_momProj_inner_fibre_bound` — the target.
-/

noncomputable section

open MeasureTheory
open scoped Real

namespace Work.Analysis.BoseBand.MomWordOffdiag

set_option maxHeartbeats 1000000
set_option linter.unusedVariables false

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-! ## 1. The pointwise polarisation bound -/

/-- For `m ≥ 0` and `z w : ℂ`, `‖m·⟨z,w⟩_ℝ‖ ≤ ½·m·(‖z‖² + ‖w‖²)`: the inner product is
dominated by `‖z‖‖w‖ ≤ ½(‖z‖² + ‖w‖²)`, and `m ≥ 0` passes through the norm. -/
private lemma norm_mul_inner_le (m : ℝ) (hm : 0 ≤ m) (z w : ℂ) :
    ‖m * (inner ℝ z w)‖ ≤ (1 / 2) * (m * ‖z‖ ^ 2 + m * ‖w‖ ^ 2) := by
  have h1 : ‖m * (inner ℝ z w)‖ = m * ‖inner ℝ z w‖ := by
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hm, Real.norm_eq_abs]
  have h2 : ‖inner ℝ z w‖ ≤ ‖z‖ * ‖w‖ := norm_inner_le_norm z w
  have h3 : ‖z‖ * ‖w‖ ≤ (‖z‖ ^ 2 + ‖w‖ ^ 2) / 2 := by
    nlinarith [sq_nonneg (‖z‖ - ‖w‖)]
  have h4 : m * (‖z‖ * ‖w‖) ≤ (1 / 2) * (m * ‖z‖ ^ 2 + m * ‖w‖ ^ 2) := by
    have h := mul_le_mul_of_nonneg_left h3 hm
    nlinarith [h]
  rw [h1]
  exact (mul_le_mul_of_nonneg_left h2 hm).trans h4

/-- The anchored moving box is the centred cube: `Λ(0) = acube ℓ`. -/
private lemma lamBox_zero_eq_acube' (ℓ : ℝ) :
    Work.BoseKinLoc.lamBox ℓ 0 = Submission.BoseGases.acube ℓ := by
  ext z
  simp [Work.BoseKinLoc.lamBox, Work.BSKinetic.bsBox]

/-! ## 2. The two pieces of the single-factor estimate -/

/-- **Plancherel/`L²`: a single `p`-section of one factor is integrable.**  The box state
`1_{Λ}(ψ_x − m)` lies in `L¹ ∩ L²` (`boxState_memLp`, which needs only smoothness of `ψ`),
so its `p`-convention Fourier transform has integrable squared modulus
(`kinFT_sq_of_memLp`), and `momProj ≤ 1` is a bounded multiplier. -/
private lemma fibre_section_integrable {ℓ d : ℝ} (hℓ : 0 < ℓ) {n : ℕ} (j : Fin n)
    {Ψ : Submission.BoseGases.X n → ℝ} (hΨ : ContDiff ℝ (⊤ : ℕ∞) Ψ)
    (x : Submission.BoseGases.X n) :
    Integrable (fun p : E3 => Work.BoseKinLoc.momProj ℓ d p *
        ‖Submission.BoseGases.kinFT (Work.BoseKinLoc.Kinetic.boxState ℓ 0
          (Work.BoseKinLoc.fibre n j Ψ x)) p‖ ^ 2) volume := by
  have hfib : ContDiff ℝ (⊤ : ℕ∞) (Work.BoseKinLoc.fibre n j Ψ x) :=
    hΨ.comp (contDiff_update (⊤ : ℕ∞) x j)
  obtain ⟨h1, h2⟩ :=
    Work.BoseKinLoc.Kinetic.boxState_memLp (ℓ := ℓ) hℓ 0 hfib
  obtain ⟨hint, _⟩ := Work.BoseKinLoc.Kinetic.kinFT_sq_of_memLp
    (F := Work.BoseKinLoc.Kinetic.boxState ℓ 0 (Work.BoseKinLoc.fibre n j Ψ x)) h1 h2
  refine hint.bdd_mul (c := 1) ?_ ?_
  · refine Measurable.aestronglyMeasurable ?_
    unfold Work.BoseKinLoc.momProj
    exact Measurable.ite (measurableSet_lt measurable_const measurable_norm)
      measurable_const measurable_const
  · filter_upwards with p
    rw [Real.norm_eq_abs, abs_of_nonneg (Work.BoseKinLoc.Kinetic.momProj_nonneg ℓ d p)]
    exact Work.BoseKinLoc.Kinetic.momProj_le_one ℓ d p

/-- **The uniform-in-`x ∈ abox` bound on the `p`-integral of one factor.**  By Plancherel the
`p`-integral is at most `(2π)³ ∫_{acube ℓ} (Q₀ψ_x)²`, and the latter is continuous in `x`
(`continuous_Qfree_L2`, applied to the jointly continuous family `(x,z) ↦ Ψ(x_{j←z})`), hence
bounded on the compact `abox n ℓ`. -/
private lemma fibre_section_bound {ℓ d : ℝ} (hℓ : 0 < ℓ) {n : ℕ} (j : Fin n)
    {Ψ : Submission.BoseGases.X n → ℝ} (hΨ : ContDiff ℝ (⊤ : ℕ∞) Ψ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ x ∈ Submission.BoseGases.abox n ℓ,
      ∫ p : E3, Work.BoseKinLoc.momProj ℓ d p *
        ‖Submission.BoseGases.kinFT (Work.BoseKinLoc.Kinetic.boxState ℓ 0
          (Work.BoseKinLoc.fibre n j Ψ x)) p‖ ^ 2 ≤ K := by
  have hK : Continuous (fun p : Submission.BoseGases.X n × E3 =>
      Ψ (Function.update p.1 j p.2)) :=
    hΨ.continuous.comp (continuous_update j)
  have hcont : Continuous (fun x : Submission.BoseGases.X n =>
      ∫ z in Submission.BoseGases.acube ℓ,
        (Work.BoseKinLoc.Qfree ℓ 0 (Work.BoseKinLoc.fibre n j Ψ x) z) ^ 2) :=
    Work.BoseKinLoc.Kinetic.continuous_Qfree_L2 (ℓ := ℓ) hℓ hK
  obtain ⟨C, hC⟩ :=
    (Submission.BoseGases.abox_compact n hℓ).exists_bound_of_continuousOn hcont.continuousOn
  refine ⟨(2 * Real.pi) ^ 3 * max C 0, by positivity, ?_⟩
  intro x hx
  have hbox : (∫ z in Submission.BoseGases.acube ℓ,
      (Work.BoseKinLoc.Qfree ℓ 0 (Work.BoseKinLoc.fibre n j Ψ x) z) ^ 2) ≤ max C 0 := by
    have hnn : 0 ≤ ∫ z in Submission.BoseGases.acube ℓ,
        (Work.BoseKinLoc.Qfree ℓ 0 (Work.BoseKinLoc.fibre n j Ψ x) z) ^ 2 :=
      integral_nonneg (fun z => sq_nonneg _)
    have hx' := hC x hx
    rw [Real.norm_eq_abs, abs_of_nonneg hnn] at hx'
    exact le_trans hx' (le_max_left _ _)
  have hfib : ContDiff ℝ (⊤ : ℕ∞) (Work.BoseKinLoc.fibre n j Ψ x) :=
    hΨ.comp (contDiff_update (⊤ : ℕ∞) x j)
  obtain ⟨h1, h2⟩ :=
    Work.BoseKinLoc.Kinetic.boxState_memLp (ℓ := ℓ) hℓ 0 hfib
  obtain ⟨hint, hplanch⟩ := Work.BoseKinLoc.Kinetic.kinFT_sq_of_memLp
    (F := Work.BoseKinLoc.Kinetic.boxState ℓ 0 (Work.BoseKinLoc.fibre n j Ψ x)) h1 h2
  have hmom := fibre_section_integrable (d := d) hℓ j hΨ x
  have hneg : (0 : ℝ) ≤ (2 * Real.pi) ^ 3 := by positivity
  have hne : (2 * Real.pi) ^ 3 ≠ 0 := by positivity
  calc ∫ p : E3, Work.BoseKinLoc.momProj ℓ d p *
        ‖Submission.BoseGases.kinFT (Work.BoseKinLoc.Kinetic.boxState ℓ 0
          (Work.BoseKinLoc.fibre n j Ψ x)) p‖ ^ 2
      ≤ ∫ p : E3, ‖Submission.BoseGases.kinFT (Work.BoseKinLoc.Kinetic.boxState ℓ 0
          (Work.BoseKinLoc.fibre n j Ψ x)) p‖ ^ 2 :=
        integral_mono hmom hint
          (fun p => mul_le_of_le_one_left (sq_nonneg _)
            (Work.BoseKinLoc.Kinetic.momProj_le_one ℓ d p))
    _ = (2 * Real.pi) ^ 3 * ∫ z in Submission.BoseGases.acube ℓ,
          (Work.BoseKinLoc.Qfree ℓ 0 (Work.BoseKinLoc.fibre n j Ψ x) z) ^ 2 := by
        have h3 := hplanch
        rw [Work.BoseKinLoc.Kinetic.integral_boxState_normSq,
          lamBox_zero_eq_acube'] at h3
        rw [← h3, ← mul_assoc, mul_inv_cancel₀ hne, one_mul]
    _ ≤ (2 * Real.pi) ^ 3 * max C 0 := mul_le_mul_of_nonneg_left hbox hneg

/-! ## 3. The target -/

theorem integrable_momProj_inner_fibre_bound {ℓ d : ℝ} (hℓ : 0 < ℓ) {n : ℕ} (j : Fin n)
    {A B : Submission.BoseGases.X n → ℝ}
    (hA : ContDiff ℝ (⊤ : ℕ∞) A) (hB : ContDiff ℝ (⊤ : ℕ∞) B) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ x ∈ Submission.BoseGases.abox n ℓ,
      MeasureTheory.Integrable (fun p : EuclideanSpace ℝ (Fin 3) =>
        Work.BoseKinLoc.momProj ℓ d p *
          inner ℝ (Submission.BoseGases.kinFT (Work.BoseKinLoc.Kinetic.boxState ℓ 0
              (Work.BoseKinLoc.fibre n j A x)) p)
            (Submission.BoseGases.kinFT (Work.BoseKinLoc.Kinetic.boxState ℓ 0
              (Work.BoseKinLoc.fibre n j B x)) p)) MeasureTheory.volume
      ∧ (∫ p : EuclideanSpace ℝ (Fin 3),
          ‖Work.BoseKinLoc.momProj ℓ d p *
            inner ℝ (Submission.BoseGases.kinFT (Work.BoseKinLoc.Kinetic.boxState ℓ 0
                (Work.BoseKinLoc.fibre n j A x)) p)
              (Submission.BoseGases.kinFT (Work.BoseKinLoc.Kinetic.boxState ℓ 0
                (Work.BoseKinLoc.fibre n j B x)) p)‖) ≤ K := by
  obtain ⟨KA, hKA0, hKA⟩ := fibre_section_bound (d := d) hℓ j hA
  obtain ⟨KB, hKB0, hKB⟩ := fibre_section_bound (d := d) hℓ j hB
  have hIntA : ∀ y : Submission.BoseGases.X n, Integrable (fun p : E3 =>
      Work.BoseKinLoc.momProj ℓ d p *
        ‖Submission.BoseGases.kinFT (Work.BoseKinLoc.Kinetic.boxState ℓ 0
          (Work.BoseKinLoc.fibre n j A y)) p‖ ^ 2) volume :=
    fun y => fibre_section_integrable (d := d) hℓ j hA y
  have hIntB : ∀ y : Submission.BoseGases.X n, Integrable (fun p : E3 =>
      Work.BoseKinLoc.momProj ℓ d p *
        ‖Submission.BoseGases.kinFT (Work.BoseKinLoc.Kinetic.boxState ℓ 0
          (Work.BoseKinLoc.fibre n j B y)) p‖ ^ 2) volume :=
    fun y => fibre_section_integrable (d := d) hℓ j hB y
  refine ⟨KA + KB, by linarith, fun x hx => ?_⟩
  -- the dominating function at the fixed point `x`
  have hdom : Integrable (fun p : E3 =>
      (1 / 2) * (Work.BoseKinLoc.momProj ℓ d p *
            ‖Submission.BoseGases.kinFT (Work.BoseKinLoc.Kinetic.boxState ℓ 0
              (Work.BoseKinLoc.fibre n j A x)) p‖ ^ 2
          + Work.BoseKinLoc.momProj ℓ d p *
            ‖Submission.BoseGases.kinFT (Work.BoseKinLoc.Kinetic.boxState ℓ 0
              (Work.BoseKinLoc.fibre n j B x)) p‖ ^ 2)) volume :=
    ((hIntA x).add (hIntB x)).const_mul (1 / 2)
  -- the pointwise polarisation bound
  have hpt : ∀ p : E3, ‖Work.BoseKinLoc.momProj ℓ d p *
        inner ℝ (Submission.BoseGases.kinFT (Work.BoseKinLoc.Kinetic.boxState ℓ 0
            (Work.BoseKinLoc.fibre n j A x)) p)
          (Submission.BoseGases.kinFT (Work.BoseKinLoc.Kinetic.boxState ℓ 0
            (Work.BoseKinLoc.fibre n j B x)) p)‖
      ≤ (1 / 2) * (Work.BoseKinLoc.momProj ℓ d p *
            ‖Submission.BoseGases.kinFT (Work.BoseKinLoc.Kinetic.boxState ℓ 0
              (Work.BoseKinLoc.fibre n j A x)) p‖ ^ 2
          + Work.BoseKinLoc.momProj ℓ d p *
            ‖Submission.BoseGases.kinFT (Work.BoseKinLoc.Kinetic.boxState ℓ 0
              (Work.BoseKinLoc.fibre n j B x)) p‖ ^ 2) :=
    fun p => norm_mul_inner_le _ (Work.BoseKinLoc.Kinetic.momProj_nonneg ℓ d p) _ _
  -- measurability of the integrand: both Fourier factors are continuous in `p`
  have hmomMeas : Measurable (fun p : E3 => Work.BoseKinLoc.momProj ℓ d p) := by
    have heq : (fun p : E3 => Work.BoseKinLoc.momProj ℓ d p)
        = fun p : E3 => if (d ^ 2 * ℓ)⁻¹ < ‖p‖ then (1 : ℝ) else 0 := by
      funext p; rfl
    rw [heq]
    exact Measurable.ite (measurableSet_lt measurable_const measurable_norm)
      measurable_const measurable_const
  have hAc : Continuous (fun p : E3 => Submission.BoseGases.kinFT
      (Work.BoseKinLoc.Kinetic.boxState ℓ 0 (Work.BoseKinLoc.fibre n j A x)) p) :=
    Work.BoseKinLoc.Momentum.continuous_kinFT_of_integrable
      (MeasureTheory.memLp_one_iff_integrable.mp
        (Work.BoseKinLoc.Kinetic.boxState_memLp (ℓ := ℓ) hℓ 0
          (hA.comp (contDiff_update (⊤ : ℕ∞) x j))).1)
  have hBc : Continuous (fun p : E3 => Submission.BoseGases.kinFT
      (Work.BoseKinLoc.Kinetic.boxState ℓ 0 (Work.BoseKinLoc.fibre n j B x)) p) :=
    Work.BoseKinLoc.Momentum.continuous_kinFT_of_integrable
      (MeasureTheory.memLp_one_iff_integrable.mp
        (Work.BoseKinLoc.Kinetic.boxState_memLp (ℓ := ℓ) hℓ 0
          (hB.comp (contDiff_update (⊤ : ℕ∞) x j))).1)
  have haesm : AEStronglyMeasurable (fun p : E3 => Work.BoseKinLoc.momProj ℓ d p *
        inner ℝ (Submission.BoseGases.kinFT (Work.BoseKinLoc.Kinetic.boxState ℓ 0
            (Work.BoseKinLoc.fibre n j A x)) p)
          (Submission.BoseGases.kinFT (Work.BoseKinLoc.Kinetic.boxState ℓ 0
            (Work.BoseKinLoc.fibre n j B x)) p)) volume :=
    (hmomMeas.mul (continuous_inner.measurable.comp
      (hAc.measurable.prodMk hBc.measurable))).aestronglyMeasurable
  have hInt : Integrable (fun p : E3 => Work.BoseKinLoc.momProj ℓ d p *
        inner ℝ (Submission.BoseGases.kinFT (Work.BoseKinLoc.Kinetic.boxState ℓ 0
            (Work.BoseKinLoc.fibre n j A x)) p)
          (Submission.BoseGases.kinFT (Work.BoseKinLoc.Kinetic.boxState ℓ 0
            (Work.BoseKinLoc.fibre n j B x)) p)) volume :=
    Integrable.mono' hdom haesm (Filter.Eventually.of_forall hpt)
  refine ⟨hInt, ?_⟩
  calc (∫ p : E3, ‖Work.BoseKinLoc.momProj ℓ d p *
        inner ℝ (Submission.BoseGases.kinFT (Work.BoseKinLoc.Kinetic.boxState ℓ 0
            (Work.BoseKinLoc.fibre n j A x)) p)
          (Submission.BoseGases.kinFT (Work.BoseKinLoc.Kinetic.boxState ℓ 0
            (Work.BoseKinLoc.fibre n j B x)) p)‖)
      ≤ ∫ p : E3, (1 / 2) * (Work.BoseKinLoc.momProj ℓ d p *
            ‖Submission.BoseGases.kinFT (Work.BoseKinLoc.Kinetic.boxState ℓ 0
              (Work.BoseKinLoc.fibre n j A x)) p‖ ^ 2
          + Work.BoseKinLoc.momProj ℓ d p *
            ‖Submission.BoseGases.kinFT (Work.BoseKinLoc.Kinetic.boxState ℓ 0
              (Work.BoseKinLoc.fibre n j B x)) p‖ ^ 2) :=
        integral_mono hInt.norm hdom hpt
    _ = (1 / 2) * ((∫ p : E3, Work.BoseKinLoc.momProj ℓ d p *
            ‖Submission.BoseGases.kinFT (Work.BoseKinLoc.Kinetic.boxState ℓ 0
              (Work.BoseKinLoc.fibre n j A x)) p‖ ^ 2)
          + (∫ p : E3, Work.BoseKinLoc.momProj ℓ d p *
            ‖Submission.BoseGases.kinFT (Work.BoseKinLoc.Kinetic.boxState ℓ 0
              (Work.BoseKinLoc.fibre n j B x)) p‖ ^ 2)) := by
        rw [MeasureTheory.integral_const_mul,
          MeasureTheory.integral_add (hIntA x) (hIntB x)]
    _ ≤ (1 / 2) * (KA + KB) := by
        have h1 := hKA x hx
        have h2 := hKB x hx
        linarith
    _ ≤ KA + KB := by linarith

end Work.Analysis.BoseBand.MomWordOffdiag
