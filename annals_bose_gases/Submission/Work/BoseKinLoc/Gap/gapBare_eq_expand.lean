import Mathlib.Tactic.Have
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseKinLoc.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

noncomputable section

open MeasureTheory
open scoped Topology ENNReal

namespace Work.BoseKinLoc.Gap

open Submission.BoseGases
open Work.BSKinetic

/-!
# `Work.BoseKinLoc.Gap.gapBare_eq_expand`

The *bare mean-free box mass* `gapBare ℓ u ψ = ∫_{Λ(u)} (Q_uψ)²` (FS `eq:DefT`'s second
piece before the prefactor `bℓ⁻²`) is the variance of `ψ` over the moving box `Λ(u) = ℓu + acube ℓ`:

    `gapBare ℓ u ψ = ∫_{Λ(u)} ψ² − |Λ(u)|·m_u(ψ)²`,   `m_u(ψ) = |Λ(u)|⁻¹∫_{Λ(u)}ψ`, `|Λ(u)| = ℓ³`.

This is the identity `∫ (f − ⨍f)² = ∫ f² − (⨍f)²·|Ω|` for the box `Λ(u)`; it rewrites the
`sInf`/window bookkeeping of `gapWord` into the mass and the square mass that the
`∫_u Q_udu` (BS `eq:Quav`) bounds act on.

## Contents

* `measurableSet_lamBox`, `isCompact_lamBox` — geometry of the moving box;
* `setIntegral_lamBox_eq_acube` — translation of a set integral from `Λ(u)` to the centred
  cube `acube ℓ` (the change of variables `z ↦ ℓu + z`);
* `gapBare_eq_expand` — the variance identity, in the exact form requested.
-/

/-! ## Geometry of the moving box `Λ(u) = ℓu + acube ℓ` -/

lemma measurableSet_lamBox (ℓ : ℝ) (u : ℝ³) :
    MeasurableSet (Work.BoseKinLoc.lamBox ℓ u) := by
  have h : Work.BoseKinLoc.lamBox ℓ u
      = (fun x : ℝ³ => x - ℓ • u) ⁻¹' acube ℓ := rfl
  rw [h]
  exact (acube_measurable ℓ).preimage (by fun_prop)

lemma isCompact_lamBox {ℓ : ℝ} (hℓ : 0 < ℓ) (u : ℝ³) :
    IsCompact (Work.BoseKinLoc.lamBox ℓ u) := by
  have h : Work.BoseKinLoc.lamBox ℓ u
      = (fun w : ℝ³ => w + ℓ • u) '' acube ℓ := by
    ext x
    constructor
    · intro hx
      exact ⟨x - ℓ • u, hx, by abel⟩
    · rintro ⟨w, hw, rfl⟩
      show w + ℓ • u - ℓ • u ∈ acube ℓ
      simpa only [add_sub_cancel_right] using hw
  rw [h]
  exact (acube_compact hℓ).image (continuous_id.add continuous_const)

/-- **Change of variables for the moving box**: `∫_{Λ(u)} G = ∫_{acube ℓ} G(ℓu + ·)`. -/
lemma setIntegral_lamBox_eq_acube (ℓ : ℝ) (u : ℝ³) (G : ℝ³ → ℝ) :
    (∫ z in Work.BoseKinLoc.lamBox ℓ u, G z) = ∫ z in acube ℓ, G (ℓ • u + z) := by
  classical
  have hmeasB : MeasurableSet (Work.BoseKinLoc.lamBox ℓ u) := measurableSet_lamBox ℓ u
  rw [← integral_indicator hmeasB, ← integral_indicator (acube_measurable ℓ)]
  rw [← integral_comp_add_left ((Work.BoseKinLoc.lamBox ℓ u).indicator G) (ℓ • u)]
  apply integral_congr_ae
  filter_upwards with z
  rw [Set.indicator_apply, Set.indicator_apply]
  by_cases hz : z ∈ acube ℓ
  · have hz' : ℓ • u + z ∈ Work.BoseKinLoc.lamBox ℓ u := by
      show ℓ • u + z - ℓ • u ∈ acube ℓ
      rwa [add_sub_cancel_left]
    rw [if_pos hz', if_pos hz]
  · have hz' : ℓ • u + z ∉ Work.BoseKinLoc.lamBox ℓ u := by
      show ¬ (ℓ • u + z - ℓ • u ∈ acube ℓ)
      rwa [add_sub_cancel_left]
    rw [if_neg hz', if_neg hz]

theorem gapBare_eq_expand (ℓ : ℝ) (hℓ : 0 < ℓ) (ψ : EuclideanSpace ℝ (Fin 3) → ℝ)
    (hψ : ContDiff ℝ (⊤ : ENat) ψ) (u : EuclideanSpace ℝ (Fin 3)) :
    Work.BoseKinLoc.gapBare ℓ u ψ
      = (∫ z in Work.BoseKinLoc.lamBox ℓ u, (ψ z) ^ 2)
        - ℓ ^ 3 * (Work.BSKinetic.bsMean ℓ u ψ) ^ 2 := by
  change (∫ z in Work.BoseKinLoc.lamBox ℓ u,
        (ψ z - Work.BSKinetic.bsMean ℓ u ψ) ^ 2)
      = (∫ z in Work.BoseKinLoc.lamBox ℓ u, (ψ z) ^ 2)
        - ℓ ^ 3 * (Work.BSKinetic.bsMean ℓ u ψ) ^ 2
  have hℓne : ℓ ≠ 0 := ne_of_gt hℓ
  have hℓ3ne : ℓ ^ 3 ≠ 0 := pow_ne_zero 3 hℓne
  have hs : MeasurableSet (Work.BoseKinLoc.lamBox ℓ u) := measurableSet_lamBox ℓ u
  have hcomp : IsCompact (Work.BoseKinLoc.lamBox ℓ u) := isCompact_lamBox hℓ u
  have hfin : (volume : Measure ℝ³) (Work.BoseKinLoc.lamBox ℓ u) ≠ ∞ :=
    hcomp.measure_lt_top.ne
  -- the volume of the moving box is `ℓ³`
  have hvol : (volume : Measure ℝ³).real (Work.BoseKinLoc.lamBox ℓ u) = ℓ ^ 3 := by
    have hacube : (volume : Measure ℝ³).real (acube ℓ) = ℓ ^ 3 := by
      have h := Submission.BoseGases.real_volume_acube ℓ hℓ.le
      rw [MeasureTheory.Measure.real_def, MeasureTheory.Measure.restrict_apply_univ] at h
      rwa [MeasureTheory.Measure.real_def]
    have e1 : (volume : Measure ℝ³).real (Work.BoseKinLoc.lamBox ℓ u)
        = ∫ z in Work.BoseKinLoc.lamBox ℓ u, (1 : ℝ) := by
      rw [MeasureTheory.setIntegral_const]; simp
    have e2 : (∫ z in acube ℓ, (1 : ℝ)) = (volume : Measure ℝ³).real (acube ℓ) := by
      rw [MeasureTheory.setIntegral_const]; simp
    rw [e1, setIntegral_lamBox_eq_acube ℓ u (fun _ => (1 : ℝ)), e2, hacube]
  -- the box integral of `ψ` is `ℓ³` times the box mean
  have hmean : (∫ z in Work.BoseKinLoc.lamBox ℓ u, ψ z)
      = ℓ ^ 3 * Work.BSKinetic.bsMean ℓ u ψ := by
    rw [setIntegral_lamBox_eq_acube ℓ u ψ]
    unfold Work.BSKinetic.bsMean
    rw [← mul_assoc, mul_inv_cancel₀ hℓ3ne, one_mul]
  have hcont : Continuous ψ := hψ.continuous
  have hIψ : IntegrableOn ψ (Work.BoseKinLoc.lamBox ℓ u) :=
    hcont.continuousOn.integrableOn_compact hcomp
  have hIψ2 : IntegrableOn (fun z => (ψ z) ^ 2) (Work.BoseKinLoc.lamBox ℓ u) :=
    (hcont.pow 2).continuousOn.integrableOn_compact hcomp
  have h2m : IntegrableOn (fun z => 2 * Work.BSKinetic.bsMean ℓ u ψ * ψ z)
      (Work.BoseKinLoc.lamBox ℓ u) :=
    hIψ.const_mul (2 * Work.BSKinetic.bsMean ℓ u ψ)
  have hIconst : IntegrableOn (fun _ : ℝ³ => (Work.BSKinetic.bsMean ℓ u ψ) ^ 2)
      (Work.BoseKinLoc.lamBox ℓ u) := MeasureTheory.integrableOn_const hfin
  -- pointwise expansion of the square
  have hcongr : (∫ z in Work.BoseKinLoc.lamBox ℓ u,
        (ψ z - Work.BSKinetic.bsMean ℓ u ψ) ^ 2)
      = ∫ z in Work.BoseKinLoc.lamBox ℓ u,
          ((ψ z) ^ 2 - 2 * Work.BSKinetic.bsMean ℓ u ψ * ψ z
            + (Work.BSKinetic.bsMean ℓ u ψ) ^ 2) := by
    apply MeasureTheory.setIntegral_congr_fun hs
    intro z _
    ring
  have hadd : (∫ z in Work.BoseKinLoc.lamBox ℓ u,
        ((ψ z) ^ 2 - 2 * Work.BSKinetic.bsMean ℓ u ψ * ψ z
          + (Work.BSKinetic.bsMean ℓ u ψ) ^ 2))
      = (∫ z in Work.BoseKinLoc.lamBox ℓ u,
            ((ψ z) ^ 2 - 2 * Work.BSKinetic.bsMean ℓ u ψ * ψ z))
        + ∫ z in Work.BoseKinLoc.lamBox ℓ u, (Work.BSKinetic.bsMean ℓ u ψ) ^ 2 :=
    MeasureTheory.integral_add
      (f := fun z => (ψ z) ^ 2 - 2 * Work.BSKinetic.bsMean ℓ u ψ * ψ z)
      (g := fun _ => (Work.BSKinetic.bsMean ℓ u ψ) ^ 2)
      (hIψ2.sub h2m) hIconst
  have hsub : (∫ z in Work.BoseKinLoc.lamBox ℓ u,
        ((ψ z) ^ 2 - 2 * Work.BSKinetic.bsMean ℓ u ψ * ψ z))
      = (∫ z in Work.BoseKinLoc.lamBox ℓ u, (ψ z) ^ 2)
        - 2 * Work.BSKinetic.bsMean ℓ u ψ
          * ∫ z in Work.BoseKinLoc.lamBox ℓ u, ψ z := by
    rw [MeasureTheory.integral_sub
          (f := fun z => (ψ z) ^ 2)
          (g := fun z => 2 * Work.BSKinetic.bsMean ℓ u ψ * ψ z) hIψ2 h2m,
      MeasureTheory.integral_const_mul (2 * Work.BSKinetic.bsMean ℓ u ψ) ψ]
  have hconst : (∫ z in Work.BoseKinLoc.lamBox ℓ u, (Work.BSKinetic.bsMean ℓ u ψ) ^ 2)
      = ℓ ^ 3 * (Work.BSKinetic.bsMean ℓ u ψ) ^ 2 := by
    rw [MeasureTheory.setIntegral_const, hvol, smul_eq_mul]
  rw [hcongr, hadd, hsub, hconst, hmean]
  ring

end Work.BoseKinLoc.Gap
