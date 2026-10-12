import Mathlib.Tactic.Have
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixB2.DvApriori.neuFrac_bilinear
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixR.NeuFracFibreMeas`

**The anchored (`u = 0`) box Neumann-resolvent fraction of the slot-`i` fibre of a smooth
`(m+1)`-body state is a.e. measurable in the remaining coordinates.**

`Work.BoseKinLoc.neuFrac ℓ a² u ϕ` is FS `eq:DefT`'s first kinetic piece, the box
Neumann-resolvent fraction `A(A+a²)⁻¹` defined variationally as the `sInf` of the
Dirichlet-principle trial functional over smooth compactly supported trials (see
`Submission/Work/BoseKinLoc/Defs.lean`).  It is *not* manifestly an integral, so measurability
is not immediate.  The measurability statements already in the corpus assume either that the
state `Φ` be supported in the box (`Sector.aemeasurable_neuWord_zero_fibre`) or that it have
compact support (`Compare.neuFrac_fibre_aemeasurable_v2`); here `Φ` is only assumed smooth.

## Strategy: continuity

The proof shows that the map is *continuous*, which is strictly stronger:

* `continuous_genFibre_pair` — the slot-`i` fibre `(r,z) ↦ Φ(kcInsN i (z,r))` is jointly
  continuous; the parametric-integral theorem over the compact cube `acube ℓ` then gives
  `continuous_fibreMass` (the box `L²`-mass `∫_{acube ℓ} ψ_r²`) and
  `continuous_fibreDist` (the box `L²`-distance `∫_{acube ℓ} (ψ_r − ψ_{r₀})²`);
* the box-restricted Lipschitz estimate `Work.BoseFixB2.DvApriori.neuFrac_lipschitz_box`
  applies to *continuous* states (no global integrability!), so at every `r`

      |Q ψ_r − Q ψ_{r₀}| ≤ 6·R r·√(∫_{acube ℓ} (ψ_r − ψ_{r₀})²),

  with the radius `R r = 1 + √(∫ ψ_r²) + √(∫ ψ_{r₀}²)`, which dominates both box masses
  (so the Lipschitz estimate is available at *every* `r`, with no preliminary locality
  argument) and is continuous in `r`;
* the majorant `6·R r·√(∫(ψ_r−ψ_{r₀})²)` tends to `6·R r₀·0 = 0`, so `Q ψ_r → Q ψ_{r₀}`
  by squeezing.

This is the same shape as `Kinetic.continuous_neuFrac_anchored` (which treats the mean-free
fibre and consumes a Lipschitz estimate with local integrability hypotheses); the difference
here is that we work with the raw fibre and with the *proved* box Lipschitz bound of
`BoseFixB2.DvApriori.neuFrac_bilinear`.
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped Topology ContDiff ENNReal

namespace Work.BoseFixR

open Submission.BoseGases

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 800000

variable {n : ℕ}

/-! ## 1. The fibre and its box data -/

/-- **Joint continuity of the slot-`i` fibre.**  `(r, z) ↦ Φ (kcInsN n i (z, r))` is continuous
for a smooth `Φ`. -/
lemma continuous_genFibre_pair {Φ : Submission.BoseGases.X (n + 1) → ℝ}
    (hΦ : ContDiff ℝ (⊤ : ENat) Φ) (i : Fin (n + 1)) :
    Continuous (fun p : Submission.BoseGases.X n × ℝ³ =>
      Work.BoseKinLoc.Kinetic.genFibre i Φ p.1 p.2) :=
  hΦ.continuous.comp ((Work.BoseKinLoc.Kinetic.continuous_kcInsN_pair i).comp
    (continuous_snd.prodMk continuous_fst))

/-- The `L²`-mass of the slot-`i` fibre over the centred cube `acube ℓ` (the anchored box
`Λ(0) = acube ℓ`). -/
noncomputable def fibreMass (i : Fin (n + 1)) (Φ : Submission.BoseGases.X (n + 1) → ℝ)
    (ℓ : ℝ) (r : Submission.BoseGases.X n) : ℝ :=
  ∫ z in Submission.BoseGases.acube ℓ, (Work.BoseKinLoc.Kinetic.genFibre i Φ r z) ^ 2

/-- The `L²`-distance between two slot-`i` fibres, over the anchored box. -/
noncomputable def fibreDist (i : Fin (n + 1)) (Φ : Submission.BoseGases.X (n + 1) → ℝ)
    (ℓ : ℝ) (r₀ r : Submission.BoseGases.X n) : ℝ :=
  ∫ z in Submission.BoseGases.acube ℓ,
    (Work.BoseKinLoc.Kinetic.genFibre i Φ r z - Work.BoseKinLoc.Kinetic.genFibre i Φ r₀ z) ^ 2

/-- The radius used in the box Lipschitz bound at the pair `(r, r₀)`. -/
noncomputable def fibreRadius (i : Fin (n + 1)) (Φ : Submission.BoseGases.X (n + 1) → ℝ)
    (ℓ : ℝ) (r₀ r : Submission.BoseGases.X n) : ℝ :=
  1 + Real.sqrt (fibreMass i Φ ℓ r) + Real.sqrt (fibreMass i Φ ℓ r₀)

/-- **Continuity of the box `L²`-mass of the fibre.**  A parametric integral over the compact
cube `acube ℓ` of the jointly continuous integrand `(r,z) ↦ ψ_r(z)²`. -/
lemma continuous_fibreMass {ℓ : ℝ} (hℓ : 0 < ℓ)
    {Φ : Submission.BoseGases.X (n + 1) → ℝ} (hΦ : ContDiff ℝ (⊤ : ENat) Φ) (i : Fin (n + 1)) :
    Continuous (fibreMass i Φ ℓ) := by
  have hpair : Continuous (fun p : Submission.BoseGases.X n × ℝ³ =>
      Work.BoseKinLoc.Kinetic.genFibre i Φ p.1 p.2) := continuous_genFibre_pair hΦ i
  have hmain : Continuous (Function.uncurry fun r : Submission.BoseGases.X n =>
      fun z : ℝ³ => (Work.BoseKinLoc.Kinetic.genFibre i Φ r z) ^ 2) := hpair.pow 2
  exact continuous_parametric_integral_of_continuous (μ := (volume : Measure ℝ³)) hmain
    (Submission.BoseGases.acube_compact hℓ)

/-- **Continuity of the box `L²`-distance between the fibre and a fixed one.** -/
lemma continuous_fibreDist {ℓ : ℝ} (hℓ : 0 < ℓ)
    {Φ : Submission.BoseGases.X (n + 1) → ℝ} (hΦ : ContDiff ℝ (⊤ : ENat) Φ)
    (i : Fin (n + 1)) (r₀ : Submission.BoseGases.X n) :
    Continuous (fun r : Submission.BoseGases.X n => fibreDist i Φ ℓ r₀ r) := by
  have hpair : Continuous (fun p : Submission.BoseGases.X n × ℝ³ =>
      Work.BoseKinLoc.Kinetic.genFibre i Φ p.1 p.2) := continuous_genFibre_pair hΦ i
  have hfixed : Continuous (fun p : Submission.BoseGases.X n × ℝ³ =>
      Work.BoseKinLoc.Kinetic.genFibre i Φ r₀ p.2) :=
    hpair.comp (continuous_const.prodMk continuous_snd)
  have hmain : Continuous (Function.uncurry fun r : Submission.BoseGases.X n =>
      fun z : ℝ³ => (Work.BoseKinLoc.Kinetic.genFibre i Φ r z
        - Work.BoseKinLoc.Kinetic.genFibre i Φ r₀ z) ^ 2) := (hpair.sub hfixed).pow 2
  exact continuous_parametric_integral_of_continuous (μ := (volume : Measure ℝ³)) hmain
    (Submission.BoseGases.acube_compact hℓ)

/-! ## 2. The target -/

/-- **The anchored Neumann fraction along the slot-`i` fibre is a.e. measurable** for a smooth
(not necessarily compactly supported) `(m+1)`-body state. -/
theorem NeuFracFibreMeas {m : ℕ} {ℓ a2 : ℝ} (hℓ : 0 < ℓ) (ha2 : 0 < a2)
    {Φ : Submission.BoseGases.X (m + 1) → ℝ} (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ) (i : Fin (m + 1)) :
    AEMeasurable (fun r : Submission.BoseGases.X m =>
      Work.BoseKinLoc.neuFrac ℓ a2 0 (Work.BoseKinLoc.Kinetic.genFibre i Φ r))
      MeasureTheory.volume := by
  have hA : Continuous (fibreMass (n := m) i Φ ℓ) := continuous_fibreMass (n := m) hℓ hΦ i
  have hcont : Continuous (fun r : Submission.BoseGases.X m =>
      Work.BoseKinLoc.neuFrac ℓ a2 0 (Work.BoseKinLoc.Kinetic.genFibre i Φ r)) := by
    rw [continuous_iff_continuousAt]
    intro r₀
    show Tendsto (fun r : Submission.BoseGases.X m =>
        Work.BoseKinLoc.neuFrac ℓ a2 0 (Work.BoseKinLoc.Kinetic.genFibre i Φ r)) (𝓝 r₀)
      (𝓝 (Work.BoseKinLoc.neuFrac ℓ a2 0 (Work.BoseKinLoc.Kinetic.genFibre i Φ r₀)))
    rw [tendsto_iff_norm_sub_tendsto_zero]
    -- the pointwise box Lipschitz bound, at the radius `fibreRadius r₀ r`
    have hbound : ∀ r : Submission.BoseGases.X m,
        |Work.BoseKinLoc.neuFrac ℓ a2 0 (Work.BoseKinLoc.Kinetic.genFibre i Φ r)
          - Work.BoseKinLoc.neuFrac ℓ a2 0 (Work.BoseKinLoc.Kinetic.genFibre i Φ r₀)|
        ≤ 6 * fibreRadius (n := m) i Φ ℓ r₀ r * Real.sqrt (fibreDist (n := m) i Φ ℓ r₀ r) := by
      intro r
      have hAnn : 0 ≤ fibreMass (n := m) i Φ ℓ r := integral_nonneg fun z => sq_nonneg _
      have hA0nn : 0 ≤ fibreMass (n := m) i Φ ℓ r₀ := integral_nonneg fun z => sq_nonneg _
      have hRadpos : 0 < fibreRadius (n := m) i Φ ℓ r₀ r := by
        rw [fibreRadius]
        have h1 := Real.sqrt_nonneg (fibreMass (n := m) i Φ ℓ r)
        have h2 := Real.sqrt_nonneg (fibreMass (n := m) i Φ ℓ r₀)
        linarith
      have hRψ : ∫ z in Work.BoseKinLoc.lamBox ℓ 0,
          (Work.BoseKinLoc.Kinetic.genFibre i Φ r z) ^ 2
          ≤ fibreRadius (n := m) i Φ ℓ r₀ r ^ 2 := by
        rw [Work.BoseKinLoc.Kinetic.lamBox_zero_eq_acube, fibreRadius]
        calc fibreMass (n := m) i Φ ℓ r
            = (Real.sqrt (fibreMass (n := m) i Φ ℓ r)) ^ 2 := (Real.sq_sqrt hAnn).symm
          _ ≤ (1 + Real.sqrt (fibreMass (n := m) i Φ ℓ r)
                + Real.sqrt (fibreMass (n := m) i Φ ℓ r₀)) ^ 2 := by
              refine pow_le_pow_left₀ (Real.sqrt_nonneg _) ?_ 2
              have h := Real.sqrt_nonneg (fibreMass (n := m) i Φ ℓ r₀)
              linarith
      have hRψ' : ∫ z in Work.BoseKinLoc.lamBox ℓ 0,
          (Work.BoseKinLoc.Kinetic.genFibre i Φ r₀ z) ^ 2
          ≤ fibreRadius (n := m) i Φ ℓ r₀ r ^ 2 := by
        rw [Work.BoseKinLoc.Kinetic.lamBox_zero_eq_acube, fibreRadius]
        calc fibreMass (n := m) i Φ ℓ r₀
            = (Real.sqrt (fibreMass (n := m) i Φ ℓ r₀)) ^ 2 := (Real.sq_sqrt hA0nn).symm
          _ ≤ (1 + Real.sqrt (fibreMass (n := m) i Φ ℓ r)
                + Real.sqrt (fibreMass (n := m) i Φ ℓ r₀)) ^ 2 := by
              refine pow_le_pow_left₀ (Real.sqrt_nonneg _) ?_ 2
              have h := Real.sqrt_nonneg (fibreMass (n := m) i Φ ℓ r)
              linarith
      have h := Work.BoseFixB2.DvApriori.neuFrac_lipschitz_box (ℓ := ℓ) (a2 := a2)
        (R := fibreRadius (n := m) i Φ ℓ r₀ r) hℓ ha2 hRadpos (0 : ℝ³)
        (Work.BoseKinLoc.Kinetic.genFibre_contDiff hΦ i r).continuous
        (Work.BoseKinLoc.Kinetic.genFibre_contDiff hΦ i r₀).continuous hRψ hRψ'
      rwa [Work.BoseKinLoc.Kinetic.lamBox_zero_eq_acube] at h
    -- the distance tends to zero
    have hDlim : Tendsto (fun r : Submission.BoseGases.X m => fibreDist (n := m) i Φ ℓ r₀ r)
        (𝓝 r₀) (𝓝 0) := by
      have hc : Continuous (fun r : Submission.BoseGases.X m =>
          fibreDist (n := m) i Φ ℓ r₀ r) := continuous_fibreDist (n := m) hℓ hΦ i r₀
      have h0 : fibreDist (n := m) i Φ ℓ r₀ r₀ = 0 := by simp [fibreDist]
      rw [← h0]
      exact hc.continuousAt
    -- the radius is continuous
    have hRadlim : Tendsto (fun r : Submission.BoseGases.X m =>
        fibreRadius (n := m) i Φ ℓ r₀ r) (𝓝 r₀)
        (𝓝 (fibreRadius (n := m) i Φ ℓ r₀ r₀)) := by
      have h1 : Tendsto (fun r : Submission.BoseGases.X m =>
          1 + Real.sqrt (fibreMass (n := m) i Φ ℓ r)) (𝓝 r₀)
          (𝓝 (1 + Real.sqrt (fibreMass (n := m) i Φ ℓ r₀))) := by
        have ht : Tendsto (fibreMass (n := m) i Φ ℓ) (𝓝 r₀)
            (𝓝 (fibreMass (n := m) i Φ ℓ r₀)) := hA.continuousAt
        exact ht.sqrt.const_add 1
      have h3 : Tendsto (fun r : Submission.BoseGases.X m =>
          1 + Real.sqrt (fibreMass (n := m) i Φ ℓ r)
            + Real.sqrt (fibreMass (n := m) i Φ ℓ r₀)) (𝓝 r₀)
          (𝓝 (1 + Real.sqrt (fibreMass (n := m) i Φ ℓ r₀)
            + Real.sqrt (fibreMass (n := m) i Φ ℓ r₀))) :=
        h1.add tendsto_const_nhds
      simpa [fibreRadius] using h3
    -- the majorant tends to zero
    have hblim : Tendsto (fun r : Submission.BoseGases.X m =>
        6 * fibreRadius (n := m) i Φ ℓ r₀ r
        * Real.sqrt (fibreDist (n := m) i Φ ℓ r₀ r)) (𝓝 r₀) (𝓝 0) := by
      have hmul := hRadlim.mul hDlim.sqrt
      have h6 := hmul.const_mul 6
      have hz : (6 : ℝ) * (fibreRadius (n := m) i Φ ℓ r₀ r₀ * Real.sqrt 0) = 0 := by simp
      rw [hz] at h6
      simpa [mul_assoc] using h6
    refine squeeze_zero (f := fun r : Submission.BoseGases.X m =>
        ‖Work.BoseKinLoc.neuFrac ℓ a2 0 (Work.BoseKinLoc.Kinetic.genFibre i Φ r)
          - Work.BoseKinLoc.neuFrac ℓ a2 0 (Work.BoseKinLoc.Kinetic.genFibre i Φ r₀)‖)
      (g := fun r : Submission.BoseGases.X m =>
        6 * fibreRadius (n := m) i Φ ℓ r₀ r
        * Real.sqrt (fibreDist (n := m) i Φ ℓ r₀ r))
      (fun r => norm_nonneg _) (fun r => ?_) hblim
    rw [Real.norm_eq_abs]
    exact hbound r
  exact hcont.aemeasurable

end Work.BoseFixR
