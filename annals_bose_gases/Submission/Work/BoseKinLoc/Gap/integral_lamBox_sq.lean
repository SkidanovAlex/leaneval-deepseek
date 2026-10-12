import Mathlib.Tactic.Have
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Submission.Work.BoseKinLoc.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseKinLoc.Gap.integral_lamBox_sq`

**The moving-box family `{Λ(u)}_u` is a partition of `ℝ³` of multiplicity one.**  For the
family `Λ(u) = ℓu + [−ℓ/2,ℓ/2]³ = lamBox ℓ u` (FS's big box `Λ(u)`),

    `∫_u ∫_{Λ(u)} ψ² = ∫_{ℝ³} ψ²`   (`0 < ℓ`, `ψ` smooth with compact support),

i.e. each point of `ℝ³` is covered by exactly one box *on average*: the family is a partition
of unity with constant multiplicity `1` (the measure of `{u | x ∈ Λ(u)} = {u | x − ℓu ∈ acube ℓ}`
is `ℓ⁻³·vol(acube ℓ) = 1`).  This is the mass-preservation companion of the `L²`-normalisation
of the window family (`Work.UBBInputs9.B.integral_chiScale_sub_smul_sq`), and is the input the
`∫_u Q_u`-type bounds of the localised box analysis need in order not to lose a volume factor.

## Proof

1. *Per-`u` change of variables* (`private setIntegral_lamBox_eq_acube`): translating the box to
   the centred cube, `∫_{Λ(u)} f = ∫_{acube ℓ} f(ℓu + ·)`.
2. *Fubini* in `(u,z)` at the measure `volume.prod (volume.restrict (acube ℓ))`; the joint
   integrand `(u,z) ↦ f(ℓu + z)` is integrable because for a.e. `z` the `u`-slice is integrable
   (`Integrable.comp_smul`, `Integrable.comp_add_right`) and the sliced norm integral is the
   constant `ℓ⁻³∫‖f‖` (`Measure.integral_comp_smul_of_nonneg`, translation invariance), which is
   integrable on the finite measure `volume.restrict (acube ℓ)` (`integrable_prod_iff'`).
3. *The `u`-integral* `∫_u f(ℓu + z) = ℓ⁻³∫ f` (`Measure.integral_comp_smul_of_nonneg` together
   with translation invariance), constant in `z`.
4. *Conclusion*: `∫_u∫_{Λ(u)} f = ∫_{z∈acube ℓ} ℓ⁻³∫f = ℓ⁻³·ℓ³·∫f = ∫f`, using
   `vol(acube ℓ) = ℓ³` (`acube_volume`).

## Contents

* `private measurableSet_lamBox`, `private setIntegral_lamBox_eq_acube` — geometry of the box;
  (the non-private versions of these two live in the sibling module
  `Submission.Work.BoseKinLoc.Gap.gapBare_eq_expand`, so these are kept local);
* `private integrable_lamBox_kernel` — the Fubini hypothesis;
* `integral_lamBox_sq` — the requested identity.
-/

noncomputable section

open MeasureTheory
open scoped ContDiff Topology Real BigOperators ENNReal

set_option autoImplicit false
set_option linter.style.haveILetI false

namespace Work.BoseKinLoc.Gap

open Submission.BoseGases

/-! ## Geometry of the moving box -/

/-- The moving box `Λ(u) = ℓu + acube ℓ` is measurable. -/
private lemma measurableSet_lamBox (ℓ : ℝ) (u : ℝ³) : MeasurableSet (lamBox ℓ u) := by
  have h : lamBox ℓ u = (fun z : ℝ³ => z - ℓ • u) ⁻¹' acube ℓ := rfl
  rw [h]
  exact (acube_measurable ℓ).preimage (by fun_prop)

/-- **Change of variables for the moving box**: `∫_{Λ(u)} f = ∫_{acube ℓ} f(ℓ•u + ·)`. -/
private lemma setIntegral_lamBox_eq_acube (ℓ : ℝ) (u : ℝ³) (f : ℝ³ → ℝ) :
    (∫ z in lamBox ℓ u, f z) = ∫ z in acube ℓ, f (ℓ • u + z) := by
  classical
  rw [← MeasureTheory.integral_indicator (measurableSet_lamBox ℓ u),
      ← MeasureTheory.integral_indicator (acube_measurable ℓ)]
  rw [← MeasureTheory.integral_add_left_eq_self ((lamBox ℓ u).indicator f) (ℓ • u)]
  apply MeasureTheory.integral_congr_ae
  filter_upwards with z
  rw [Set.indicator_apply, Set.indicator_apply]
  by_cases hz : z ∈ acube ℓ
  · have hz' : ℓ • u + z ∈ lamBox ℓ u := by
      show ℓ • u + z - ℓ • u ∈ acube ℓ
      rwa [add_sub_cancel_left]
    rw [if_pos hz', if_pos hz]
  · have hz' : ℓ • u + z ∉ lamBox ℓ u := by
      show ¬ (ℓ • u + z - ℓ • u ∈ acube ℓ)
      rwa [add_sub_cancel_left]
    rw [if_neg hz', if_neg hz]

/-! ## The Fubini hypothesis -/

/-- **Joint integrability of the kernel `(u,z) ↦ f(ℓ•u + z)`** on
`volume.prod (volume.restrict (acube ℓ))`, for `f` measurable and integrable.  Slicing in the
`u`-variable first (`integrable_prod_iff'`): every slice `u ↦ f(ℓ•u + z)` is integrable
(`Integrable.comp_smul` after the shift `Integrable.comp_add_right`), and the sliced norm
integral is the constant `ℓ⁻³∫‖f‖ ∈ ℝ` — an integrable function of `z` because the restricted
measure of the cube is finite. -/
private lemma integrable_lamBox_kernel (ℓ : ℝ) (hℓ : 0 < ℓ) {f : ℝ³ → ℝ}
    (hfmeas : Measurable f) (hfint : Integrable f) :
    Integrable (Function.uncurry (fun u z : ℝ³ => f (ℓ • u + z)))
      ((volume : Measure ℝ³).prod ((volume : Measure ℝ³).restrict (acube ℓ))) := by
  rw [MeasureTheory.integrable_prod_iff']
  · constructor
    · -- every `u`-slice is integrable
      filter_upwards with z
      show Integrable (fun u : ℝ³ => f (ℓ • u + z)) volume
      have h1 : (fun u : ℝ³ => f (ℓ • u + z)) = fun u => (fun y : ℝ³ => f (y + z)) (ℓ • u) :=
        rfl
      rw [h1]
      exact (hfint.comp_add_right z).comp_smul hℓ.ne'
    · -- the sliced norm integral is the constant `ℓ⁻³ ∫ ‖f‖`
      have hconst : ∀ z : ℝ³, (∫ u : ℝ³, ‖f (ℓ • u + z)‖)
          = (ℓ ^ 3)⁻¹ * ∫ y : ℝ³, ‖f y‖ := by
        intro z
        have h1 : (fun u : ℝ³ => ‖f (ℓ • u + z)‖)
            = fun u => (fun y : ℝ³ => ‖f (y + z)‖) (ℓ • u) := rfl
        rw [h1, Measure.integral_comp_smul_of_nonneg (volume : Measure ℝ³)
          (fun y : ℝ³ => ‖f (y + z)‖) ℓ (hR := le_of_lt hℓ)]
        rw [show ℓ ^ Module.finrank ℝ ℝ³ = ℓ ^ 3 by
          rw [finrank_euclideanSpace, Fintype.card_fin]]
        rw [MeasureTheory.integral_add_right_eq_self (fun y : ℝ³ => ‖f y‖) z, smul_eq_mul]
      haveI hfin : IsFiniteMeasure ((volume : Measure ℝ³).restrict (acube ℓ)) :=
        ⟨by rw [Measure.restrict_apply_univ]; exact acube_lt_top ℓ hℓ.le⟩
      refine Integrable.congr (integrable_const ((ℓ ^ 3)⁻¹ * ∫ y : ℝ³, ‖f y‖)) ?_
      filter_upwards with z
      exact (hconst z).symm
  · -- measurability of the joint integrand
    have hcont : Continuous (fun p : ℝ³ × ℝ³ => ℓ • p.1 + p.2) := by fun_prop
    exact (hfmeas.comp hcont.measurable).aestronglyMeasurable

/-! ## The partition-of-unity identity -/

theorem integral_lamBox_sq (ℓ : ℝ) (hℓ : 0 < ℓ) (ψ : EuclideanSpace ℝ (Fin 3) → ℝ)
    (hψ : ContDiff ℝ (⊤ : ENat) ψ) (hcs : HasCompactSupport ψ) :
    (∫ u : EuclideanSpace ℝ (Fin 3), ∫ z in Work.BoseKinLoc.lamBox ℓ u, (ψ z) ^ 2)
      = ∫ z : EuclideanSpace ℝ (Fin 3), (ψ z) ^ 2 := by
  -- `f := ψ²` is continuous with compact support, hence integrable
  have hcont : Continuous (fun z : ℝ³ => (ψ z) ^ 2) := hψ.continuous.pow 2
  have hcs2 : HasCompactSupport (fun z : ℝ³ => (ψ z) ^ 2) :=
    hcs.comp_left (g := fun t : ℝ => t ^ 2) (by norm_num)
  have hint : Integrable (fun z : ℝ³ => (ψ z) ^ 2) :=
    hcont.integrable_of_hasCompactSupport hcs2
  -- change variables in each box integral
  have hstep1 : (∫ u : ℝ³, ∫ z in lamBox ℓ u, (ψ z) ^ 2)
      = ∫ u : ℝ³, ∫ z in acube ℓ, (ψ (ℓ • u + z)) ^ 2 := by
    apply integral_congr_ae
    filter_upwards with u
    exact setIntegral_lamBox_eq_acube ℓ u (fun z => (ψ z) ^ 2)
  rw [hstep1]
  -- Fubini in `(u,z)`
  rw [MeasureTheory.integral_integral_swap (f := fun u z : ℝ³ => (ψ (ℓ • u + z)) ^ 2)
      (integrable_lamBox_kernel ℓ hℓ hcont.measurable hint)]
  -- the `u`-integral is the constant `ℓ⁻³ ∫ψ²`
  have hinner : ∀ z : ℝ³, (∫ u : ℝ³, (ψ (ℓ • u + z)) ^ 2) = (ℓ ^ 3)⁻¹ * ∫ y, (ψ y) ^ 2 := by
    intro z
    have h1 : (fun u : ℝ³ => (ψ (ℓ • u + z)) ^ 2)
        = fun u => (fun y : ℝ³ => (ψ (y + z)) ^ 2) (ℓ • u) := rfl
    rw [h1, Measure.integral_comp_smul_of_nonneg (volume : Measure ℝ³)
      (fun y : ℝ³ => (ψ (y + z)) ^ 2) ℓ (hR := le_of_lt hℓ)]
    rw [show ℓ ^ Module.finrank ℝ ℝ³ = ℓ ^ 3 by
      rw [finrank_euclideanSpace, Fintype.card_fin]]
    rw [MeasureTheory.integral_add_right_eq_self (fun y : ℝ³ => (ψ y) ^ 2) z, smul_eq_mul]
  rw [show (∫ z in acube ℓ, ∫ u : ℝ³, (ψ (ℓ • u + z)) ^ 2)
      = ∫ z in acube ℓ, (ℓ ^ 3)⁻¹ * ∫ y, (ψ y) ^ 2 from by
    apply integral_congr_ae
    filter_upwards with z
    exact hinner z]
  -- evaluate the cube integral of the constant: `vol(acube ℓ) = ℓ³`
  rw [MeasureTheory.integral_const_mul]
  rw [MeasureTheory.setIntegral_const]
  rw [Measure.real_def, acube_volume ℓ hℓ.le, ENNReal.toReal_ofReal (by positivity), smul_eq_mul]
  rw [← mul_assoc, inv_mul_cancel₀ (pow_ne_zero 3 hℓ.ne'), one_mul]

end Work.BoseKinLoc.Gap
