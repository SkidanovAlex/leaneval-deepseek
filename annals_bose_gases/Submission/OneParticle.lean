import Mathlib.Order.CompletePartialOrder
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.InnerProductSpace.Laplacian
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import ChallengeDeps
import Submission.LapScale
import Submission.OneParticlePos
import Submission.OneParticleSupp
import Submission.Potential
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
One-particle trial states for the a priori upper bound on `boxEnergy`.

This module constructs, for every box side `L ≥ 1`, a normalized smooth bump
`oneParticle L : ℝ³ → ℝ` supported strictly inside the cube `cube L`, with a
universal sup-bound and a universal kinetic bound:

    ‖oneParticle L‖₂² = 1 ,   (oneParticle L x)² ≤ supC / L³ ,
    ∫ |oneParticle L x · Δ (oneParticle L) x| ≤ kinC / L² .

The single target lemma of this file is `oneParticle_facts` below.

CONSTRUCTION (realised in `Submission.OneParticleDefs`):

1.  Base bump in the unit cube: the `ContDiffBump` `unitBumpData` with radii
    `rIn = 1/8 < rOut = 1/4` centred at `unitCentre = (1/2,1/2,1/2)`, coerced
    to the function `unitBump`.  `ContDiffBump` provides
    `unitBumpData.contDiff`, `.nonneg`, `.le_one`, and
    `tsupport unitBump = closedBall unitCentre (1/4)`
    (`ContDiffBump.tsupport_eq`).

2.  `unitNorm := ∫ x, (unitBump x)² > 0` (`OneParticlePos.unitNorm_pos`):
    `unitBump = 1` on `closedBall unitCentre (1/8)` so its support has positive
    volume.

3.  The state:
        oneCoeff L := (Real.sqrt (L³ · unitNorm))⁻¹
        oneParticle L x := oneCoeff L * unitBump (L⁻¹ • x)
    - support inside `interior (cube L)` is proved in
      `OneParticleSupp.tsupport_oneParticle_subset_openCube` (the topological
      support lies in the closed ball of radius `L/4` about `L • unitCentre`,
      coordinatewise strictly inside `[0,L]³`);
    - normalization, sup bound and kinetic bound follow from the measure
      scaling `∫ f (L⁻¹ • x) = L³ ∫ f` and the homothety rule
      `Δ (f (c • ·)) = c² · (Δ f) (c • ·)` (`LapScale`).
-/

namespace Submission

open _root_.BoseGases
open _root_.BoseGases.CInfty0Box
open Submission.LapScale
set_option autoImplicit false

namespace BoseGases

open Filter Metric MeasureTheory Laplacian
open scoped ContDiff Topology Real InnerProductSpace Laplacian

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-- the one-particle facts bundle -/
structure OneParticleFacts (L : ℝ) : Prop where
  contDiff : ContDiff ℝ ∞ (oneParticle L)
  tsupp : tsupport (oneParticle L) ⊆ interior (cube L)
  norm : (∫ x : ℝ³, (oneParticle L x) ^ 2) = 1
  supC_nonneg : 0 ≤ supC
  sq_bound : ∀ x : ℝ³, (oneParticle L x) ^ 2 ≤ supC / L ^ 3
  kin_bound : (∫ x : ℝ³, |oneParticle L x * Δ (oneParticle L) x|) ≤ kinC / L ^ 2

/-! ## Smoothness -/

@[fun_prop]
lemma unitBump_contDiff : ContDiff ℝ ∞ unitBump := by
  exact unitBumpData.contDiff

/-- A finite smoothness order below infinity. -/
lemma contDiff_two_le_top : (2 : ℕ∞ω) ≤ (∞ : ℕ∞ω) :=
  WithTop.coe_le_coe.mpr (by exact (le_top : (2 : ℕ∞) ≤ ⊤))

lemma oneParticle_contDiff {L : ℝ} : ContDiff ℝ ∞ (oneParticle L) := by
  unfold oneParticle
  fun_prop

lemma unitBump_contDiff_two : ContDiff ℝ 2 unitBump := by
  exact unitBump_contDiff.of_le contDiff_two_le_top

lemma oneParticle_contDiff_two {L : ℝ} : ContDiff ℝ 2 (oneParticle L) := by
  exact oneParticle_contDiff.of_le contDiff_two_le_top

/-! ## The open cube is open and inside `cube` -/

lemma isOpen_openCube (L : ℝ) : IsOpen (openCube L) := by
  rw [show openCube L = ⋂ m : Fin 3, (fun y : ℝ³ => y m) ⁻¹' Set.Ioo 0 L by
    ext y; simp [openCube]]
  exact isOpen_iInter_of_finite
    (fun m : Fin 3 => isOpen_Ioo.preimage (by fun_prop : Continuous fun y : ℝ³ => y m))

lemma openCube_subset_cube (L : ℝ) : openCube L ⊆ cube L := by
  intro y hy m
  exact Set.Ioo_subset_Icc_self (hy m)

lemma openCube_subset_interior_cube (L : ℝ) : openCube L ⊆ interior (cube L) := by
  exact interior_maximal (openCube_subset_cube L) (isOpen_openCube L)

/-! ## Measure scaling on ℝ³ -/

lemma integral_scaling (f : ℝ³ → ℝ) {L : ℝ} (hL : 0 ≤ L) :
    (∫ x : ℝ³, f (L⁻¹ • x)) = L ^ 3 * (∫ x : ℝ³, f x) := by
  have h := MeasureTheory.Measure.integral_comp_inv_smul_of_nonneg
    (μ := (volume : Measure ℝ³)) (f := f) (R := L) hL
  have hfin : Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 3 := by simp [EuclideanSpace]
  rw [hfin] at h
  simpa [smul_eq_mul] using h

lemma integral_scaling_const (a : ℝ) (f : ℝ³ → ℝ) {L : ℝ} (hL : 0 ≤ L) :
    (∫ x : ℝ³, a * f (L⁻¹ • x)) = a * (L ^ 3 * (∫ x : ℝ³, f x)) := by
  calc
    (∫ x : ℝ³, a * f (L⁻¹ • x)) = a * (∫ x : ℝ³, f (L⁻¹ • x)) := by
      rw [MeasureTheory.integral_const_mul]
    _ = a * (L ^ 3 * (∫ x : ℝ³, f x)) := by rw [integral_scaling f hL]

/-! ## Laplacian of the scaled bump -/

lemma laplacian_unitBump_scaled {L : ℝ} :
    Δ (fun z : ℝ³ => unitBump (L⁻¹ • z)) =
      fun z : ℝ³ => (L⁻¹ : ℝ) ^ 2 * (Δ unitBump) (L⁻¹ • z) :=
  laplacian_comp_homothetic (f := unitBump) (c := L⁻¹) unitBump_contDiff_two

lemma laplacian_oneParticle_apply {L : ℝ} (x : ℝ³) :
    Δ (oneParticle L) x = oneCoeff L * ((L⁻¹ : ℝ) ^ 2) * (Δ unitBump) (L⁻¹ • x) := by
  unfold oneParticle
  have hf : ContDiff ℝ 2 (fun z : ℝ³ => unitBump (L⁻¹ • z)) := by
    have h : ContDiff ℝ ∞ (fun z : ℝ³ => unitBump (L⁻¹ • z)) := by fun_prop
    exact h.of_le contDiff_two_le_top
  have hA : Δ (fun y : ℝ³ => oneCoeff L * unitBump (L⁻¹ • y)) =
      fun y : ℝ³ => oneCoeff L * (Δ (fun z : ℝ³ => unitBump (L⁻¹ • z))) y :=
    laplacian_const_mul (f := fun z : ℝ³ => unitBump (L⁻¹ • z)) hf (oneCoeff L)
  rw [hA]
  change oneCoeff L * ((Δ (fun z : ℝ³ => unitBump (L⁻¹ • z))) x) =
    oneCoeff L * ((L⁻¹ : ℝ) ^ 2) * (Δ unitBump) (L⁻¹ • x)
  have hB : (Δ (fun z : ℝ³ => unitBump (L⁻¹ • z))) x =
      (L⁻¹ : ℝ) ^ 2 * (Δ unitBump) (L⁻¹ • x) := by
    simpa using congrFun (laplacian_unitBump_scaled (L := L)) x
  rw [hB]
  ring

/-! ## Pointwise estimates for the bump -/

lemma unitBump_sq_le_one (x : ℝ³) : (unitBump x) ^ 2 ≤ 1 := by
  exact pow_le_one₀ unitBumpData.nonneg unitBumpData.le_one

lemma unitBump_nonneg (x : ℝ³) : 0 ≤ unitBump x :=
  unitBumpData.nonneg

/-! ## Algebra of the normalising coefficient -/

lemma oneCoeff_sq_eq {L : ℝ} (hL : 0 < L) : (oneCoeff L) ^ 2 = (L ^ 3 * unitNorm)⁻¹ := by
  unfold oneCoeff
  rw [inv_pow]
  congr 1
  exact Real.sq_sqrt (mul_nonneg (pow_nonneg hL.le 3) unitNorm_pos.le)

/-! ## Normalization -/

lemma norm_oneParticle {L : ℝ} (hL : 0 < L) :
    (∫ x : ℝ³, (oneParticle L x) ^ 2) = 1 := by
  have hsc := integral_scaling (f := fun y : ℝ³ => (unitBump y) ^ 2) (L := L) hL.le
  calc
    (∫ x : ℝ³, (oneParticle L x) ^ 2)
        = ∫ x : ℝ³, (oneCoeff L * unitBump (L⁻¹ • x)) ^ 2 := by rfl
    _ = (oneCoeff L) ^ 2 * (∫ x : ℝ³, (unitBump (L⁻¹ • x)) ^ 2) := by
      calc
        (∫ x : ℝ³, (oneCoeff L * unitBump (L⁻¹ • x)) ^ 2)
            = ∫ x : ℝ³, (oneCoeff L) ^ 2 * (unitBump (L⁻¹ • x)) ^ 2 := by
              apply integral_congr_ae
              filter_upwards with x
              ring
        _ = (oneCoeff L) ^ 2 * (∫ x : ℝ³, (unitBump (L⁻¹ • x)) ^ 2) := by
              rw [MeasureTheory.integral_const_mul]
    _ = (oneCoeff L) ^ 2 * (L ^ 3 * ∫ x : ℝ³, (unitBump x) ^ 2) := by
      rw [hsc]
    _ = 1 := by
      have hcoef : (oneCoeff L) ^ 2 * (L ^ 3 * unitNorm) = 1 := by
        rw [oneCoeff_sq_eq hL]
        exact inv_mul_cancel₀ (mul_ne_zero (pow_ne_zero 3 hL.ne') unitNorm_pos.ne')
      simpa [unitNorm, mul_assoc] using hcoef

/-! ## Sup bound -/

lemma supC_nonneg : 0 ≤ supC := by
  unfold supC
  exact div_nonneg (by norm_num) unitNorm_pos.le

lemma sq_bound_oneParticle {L : ℝ} (hL : 0 < L) (x : ℝ³) :
    (oneParticle L x) ^ 2 ≤ supC / L ^ 3 := by
  have hsup : (oneCoeff L) ^ 2 = supC / L ^ 3 := by
    unfold supC
    rw [oneCoeff_sq_eq hL]
    field_simp [unitNorm_pos.ne', hL.ne']
  calc
    (oneParticle L x) ^ 2 = (oneCoeff L * unitBump (L⁻¹ • x)) ^ 2 := by rfl
    _ = (oneCoeff L) ^ 2 * (unitBump (L⁻¹ • x)) ^ 2 := by ring
    _ ≤ (oneCoeff L) ^ 2 * 1 :=
      mul_le_mul_of_nonneg_left (unitBump_sq_le_one (L⁻¹ • x)) (sq_nonneg _)
    _ = supC / L ^ 3 := by simpa using hsup

/-! ## Kinetic bound -/

lemma kineticIntegrand {L : ℝ} (x : ℝ³) :
    oneParticle L x * Δ (oneParticle L) x =
      (oneCoeff L) ^ 2 * (L⁻¹ : ℝ) ^ 2 *
        (unitBump (L⁻¹ • x) * (Δ unitBump) (L⁻¹ • x)) := by
  simp [oneParticle, laplacian_oneParticle_apply, mul_assoc]
  ring

lemma abs_kineticIntegrand {L : ℝ} (x : ℝ³) :
    |oneParticle L x * Δ (oneParticle L) x| =
      (oneCoeff L) ^ 2 * (L⁻¹ : ℝ) ^ 2 *
        |unitBump (L⁻¹ • x) * (Δ unitBump) (L⁻¹ • x)| := by
  rw [kineticIntegrand]
  have ha : 0 ≤ (oneCoeff L) ^ 2 * (L⁻¹ : ℝ) ^ 2 :=
    mul_nonneg (sq_nonneg _) (sq_nonneg _)
  rw [abs_mul, abs_of_nonneg ha]

lemma kin_integral_eq {L : ℝ} (hL : 0 < L) :
    (∫ x : ℝ³, |oneParticle L x * Δ (oneParticle L) x|) = kinC / L ^ 2 := by
  have hsc := integral_scaling_const ((oneCoeff L) ^ 2 * (L⁻¹ : ℝ) ^ 2)
    (f := fun y : ℝ³ => |unitBump y * (Δ unitBump) y|) hL.le
  calc
    (∫ x : ℝ³, |oneParticle L x * Δ (oneParticle L) x|)
        = ∫ x : ℝ³, (oneCoeff L) ^ 2 * (L⁻¹ : ℝ) ^ 2 *
            |unitBump (L⁻¹ • x) * (Δ unitBump) (L⁻¹ • x)| := by
            apply integral_congr_ae
            filter_upwards with x
            exact abs_kineticIntegrand x
    _ = (oneCoeff L) ^ 2 * (L⁻¹ : ℝ) ^ 2 * (L ^ 3 *
          (∫ x : ℝ³, |unitBump x * (Δ unitBump) x|)) := hsc
    _ = (∫ x : ℝ³, |unitBump x * (Δ unitBump) x|) / unitNorm / L ^ 2 := by
      have hcoef : (oneCoeff L) ^ 2 = (L ^ 3 * unitNorm)⁻¹ := oneCoeff_sq_eq hL
      rw [hcoef]
      field_simp [unitNorm_pos.ne', hL.ne']
    _ = kinC / L ^ 2 := by rfl

/-- For every side length `L ≥ 1` the scaled unit bump gives a smooth function
supported inside the cube with `L²`-norm one, sup bound `supC / L³` and kinetic
bound `kinC / L²`. -/
lemma oneParticle_facts {L : ℝ} (hL : 1 ≤ L) : OneParticleFacts L := by
  have hLpos : 0 < L := lt_of_lt_of_le zero_lt_one hL
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact oneParticle_contDiff
  · exact (tsupport_oneParticle_subset_openCube hLpos).trans
      (openCube_subset_interior_cube L)
  · exact norm_oneParticle hLpos
  · exact supC_nonneg
  · intro x
    exact sq_bound_oneParticle hLpos x
  · exact le_of_eq (kin_integral_eq hLpos)

end BoseGases

end Submission
