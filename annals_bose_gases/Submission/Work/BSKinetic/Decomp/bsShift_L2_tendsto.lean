import Mathlib.Tactic.Have
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Submission.Work.BSKinetic.Decomp.ShiftDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `bsShift_L2_tendsto` — `L²`-continuity of the shifted big-box state in the shift

The shifted one-body big-box state `bsShift ℓ ψ u` (see `ShiftDefs`) is the localised mean-free
state transported to the origin, and it is compactly supported in the fixed box `acube ℓ`
uniformly in `u`.  This module proves that the map `u ↦ bsShift ℓ ψ u` is continuous at every
point `u₀` in the `L²` sense: the `L²` mass of the difference tends to `0`,

    `u ↦ ∫_z (bsShift ℓ ψ u z − bsShift ℓ ψ u₀ z)² ⟶ 0`   as `u → u₀`,

equivalently `bsL2 (bsShift ℓ ψ u − bsShift ℓ ψ u₀) ⟶ 0`.

The proof is a dominated-convergence argument.  Writing

    `bsShift ℓ ψ u z = χ_ℓ(z)·(ψ(z + ℓ•u) − bsMean ℓ u ψ)`,

both factors converge pointwise as `u → u₀`:
* `z ↦ ψ(z + ℓ•u) → ψ(z + ℓ•u₀)` by continuity of `ψ` (composition with a continuous affine map);
* `u ↦ bsMean ℓ u ψ → bsMean ℓ u₀ ψ` by continuity of the moving-box mean, which is itself a
  dominated-convergence argument over the finite measure `volume.restrict (acube ℓ)`
  (`continuous_bsMean` below).

Since `ψ` is bounded (`C`, from `Continuous` + `HasCompactSupport`) the box mean is bounded by the
same `C` (`|bsMean ℓ u ψ| ≤ C`), so `|bsShift ℓ ψ u z| ≤ 2C·|χ_ℓ z|` uniformly in `u`, giving the
integrable dominating function `z ↦ (4C·χ_ℓ z)²` of the difference-squared.
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped Topology Real BigOperators ENNReal

namespace Work.BSKinetic.Decomp

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

open Submission.BoseGases
open Work.BSKinetic

set_option autoImplicit false
set_option maxHeartbeats 800000

/-- **The moving-box mean is continuous in the shift.**  For a continuous, compactly supported
`ψ`, the map `u ↦ bsMean ℓ u ψ = (ℓ³)⁻¹ ∫_{acube ℓ} ψ(ℓ•u + z) dz` is continuous on `ℝ³`.

Indeed `|ψ| ≤ C` for some `C ≥ 0`, and for `z` in the bounded set `acube ℓ` the function
`u ↦ ψ(ℓ•u + z)` is continuous and dominated by the constant `C`, which is integrable for the
finite measure `volume.restrict (acube ℓ)`; dominated convergence over that measure gives
continuity of `u ↦ ∫_{acube ℓ} ψ(ℓ•u + z) dz`, and multiplying by `(ℓ³)⁻¹` preserves it. -/
theorem continuous_bsMean {ℓ : ℝ} {ψ : ℝ³ → ℝ}
    (hψ : Continuous ψ) (hcs : HasCompactSupport ψ) :
    Continuous (fun u : ℝ³ => bsMean ℓ u ψ) := by
  obtain ⟨C, hC⟩ := hψ.bounded_above_of_compact_support hcs
  have hCabs : ∀ x, |ψ x| ≤ C := fun x => by simpa [Real.norm_eq_abs] using hC x
  rw [continuous_iff_continuousAt]
  intro v
  rw [ContinuousAt, bsMean]
  have hmain : Tendsto (fun u : ℝ³ => ∫ z in acube ℓ, ψ (ℓ • u + z)) (nhds v)
      (nhds (∫ z in acube ℓ, ψ (ℓ • v + z))) := by
    apply tendsto_integral_filter_of_dominated_convergence (bound := fun _ => C)
    · filter_upwards with u
      exact (hψ.comp (continuous_const.add continuous_id)).aestronglyMeasurable
    · filter_upwards with u
      apply ae_of_all
      intro z
      rw [Real.norm_eq_abs]
      exact hCabs _
    · exact integrable_const C
    · apply ae_of_all
      intro z
      exact (hψ.comp ((continuous_const_smul ℓ).add continuous_const)).tendsto v
  exact hmain.const_mul ((ℓ ^ 3)⁻¹)

theorem bsShift_L2_tendsto {ℓ : ℝ} (hℓ : 0 < ℓ) {ψ : EuclideanSpace ℝ (Fin 3) → ℝ}
    (hψ : ContDiff ℝ (⊤ : ENat) ψ) (hcs : HasCompactSupport ψ)
    (u₀ : EuclideanSpace ℝ (Fin 3)) :
    Filter.Tendsto (fun u : EuclideanSpace ℝ (Fin 3) =>
        Work.BSKinetic.Decomp.bsL2 (fun z : EuclideanSpace ℝ (Fin 3) =>
          Work.BSKinetic.Decomp.bsShift ℓ ψ u z
            - Work.BSKinetic.Decomp.bsShift ℓ ψ u₀ z))
      (nhds u₀) (nhds 0) := by
  obtain ⟨C, hC⟩ := hψ.continuous.bounded_above_of_compact_support hcs
  have hCabs : ∀ x, |ψ x| ≤ C := fun x => by simpa [Real.norm_eq_abs] using hC x
  -- the box mean is bounded by the same `C`
  have hMb : ∀ u, |bsMean ℓ u ψ| ≤ C := by
    intro u
    rw [bsMean]
    have hvol : (volume : Measure ℝ³) (acube ℓ) < ∞ := acube_lt_top ℓ (le_of_lt hℓ)
    have hreal : (volume : Measure ℝ³).real (acube ℓ) = ℓ ^ 3 := by
      rw [Measure.real_def, acube_volume ℓ (le_of_lt hℓ),
          ENNReal.toReal_ofReal (pow_nonneg (le_of_lt hℓ) 3)]
    have hI := norm_setIntegral_le_of_norm_le_const (μ := (volume : Measure ℝ³)) (s := acube ℓ)
      (f := fun z : ℝ³ => ψ (ℓ • u + z)) (C := C) hvol (fun z _ => by
        rw [Real.norm_eq_abs]; exact hCabs _)
    simp only [Real.norm_eq_abs] at hI
    rw [hreal] at hI
    rw [abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ (ℓ ^ 3)⁻¹)]
    calc (ℓ ^ 3)⁻¹ * |∫ z in acube ℓ, ψ (ℓ • u + z)|
        ≤ (ℓ ^ 3)⁻¹ * (C * ℓ ^ 3) := mul_le_mul_of_nonneg_left hI (by positivity)
      _ = C := by field_simp
  have hMeanCont : Continuous (fun u : ℝ³ => bsMean ℓ u ψ) :=
    continuous_bsMean hψ.continuous hcs
  -- uniform bound for the shifted state
  have hbsb : ∀ u z, |bsShift ℓ ψ u z| ≤ 2 * C * |chiScale ℓ z| := by
    intro u z
    rw [bsShift_apply, abs_mul]
    have h1 : |ψ (z + ℓ • u) - bsMean ℓ u ψ| ≤ 2 * C := by
      calc |ψ (z + ℓ • u) - bsMean ℓ u ψ| ≤ |ψ (z + ℓ • u)| + |bsMean ℓ u ψ| := abs_sub _ _
        _ ≤ C + C := add_le_add (hCabs _) (hMb u)
        _ = 2 * C := by ring
    calc |chiScale ℓ z| * |ψ (z + ℓ • u) - bsMean ℓ u ψ|
        ≤ |chiScale ℓ z| * (2 * C) := mul_le_mul_of_nonneg_left h1 (abs_nonneg _)
      _ = 2 * C * |chiScale ℓ z| := by ring
  -- pointwise bound of the (squared) difference by an integrable function
  have hbound_pt : ∀ u z,
      ‖(bsShift ℓ ψ u z - bsShift ℓ ψ u₀ z)^2‖ ≤ (4 * C * chiScale ℓ z)^2 := by
    intro u z
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    have h2 : |bsShift ℓ ψ u z - bsShift ℓ ψ u₀ z| ≤ 4 * C * |chiScale ℓ z| := by
      calc |bsShift ℓ ψ u z - bsShift ℓ ψ u₀ z|
          ≤ |bsShift ℓ ψ u z| + |bsShift ℓ ψ u₀ z| := abs_sub _ _
        _ ≤ 2 * C * |chiScale ℓ z| + 2 * C * |chiScale ℓ z| := add_le_add (hbsb u z) (hbsb u₀ z)
        _ = 4 * C * |chiScale ℓ z| := by ring
    calc (bsShift ℓ ψ u z - bsShift ℓ ψ u₀ z)^2
        = |bsShift ℓ ψ u z - bsShift ℓ ψ u₀ z|^2 := (sq_abs _).symm
      _ ≤ (4 * C * |chiScale ℓ z|)^2 := pow_le_pow_left₀ (abs_nonneg _) h2 2
      _ = (4 * C * chiScale ℓ z)^2 := by rw [abs_of_nonneg (chiScale_nonneg ℓ z)]
  have hbound_int : Integrable (fun z : ℝ³ => (4 * C * chiScale ℓ z)^2) := by
    have hcont : Continuous (fun z : ℝ³ => (4 * C * chiScale ℓ z)^2) :=
      (continuous_const.mul (chiScale_continuous ℓ)).pow 2
    have hcs' : HasCompactSupport (fun z : ℝ³ => (4 * C * chiScale ℓ z)^2) := by
      have h1 : HasCompactSupport (fun z : ℝ³ => 4 * C * chiScale ℓ z) :=
        (chiScale_hasCompactSupport (ne_of_gt hℓ)).mul_left
      exact h1.comp_left (g := fun x : ℝ => x ^ 2) (by norm_num)
    exact hcont.integrable_of_hasCompactSupport hcs'
  -- the shifted state is continuous in `z` for fixed `u`
  have hcu : ∀ u, Continuous (fun z : ℝ³ => bsShift ℓ ψ u z) := by
    intro u
    rw [show (fun z : ℝ³ => bsShift ℓ ψ u z)
        = fun z => chiScale ℓ z * (ψ (z + ℓ • u) - bsMean ℓ u ψ) from rfl]
    exact (chiScale_continuous ℓ).mul
      ((hψ.continuous.comp (continuous_id.add continuous_const)).sub continuous_const)
  -- ... and continuous in `u` for fixed `z`
  have hcont_z : ∀ z, Continuous (fun u : ℝ³ => bsShift ℓ ψ u z) := by
    intro z
    exact continuous_const.mul
      ((hψ.continuous.comp (continuous_const.add (continuous_const_smul ℓ))).sub hMeanCont)
  -- dominated convergence
  have hmain := tendsto_integral_filter_of_dominated_convergence
    (μ := (volume : Measure ℝ³)) (l := nhds u₀)
    (F := fun u z => (bsShift ℓ ψ u z - bsShift ℓ ψ u₀ z)^2)
    (f := fun _ => (0 : ℝ))
    (bound := fun z => (4 * C * chiScale ℓ z)^2)
    (by filter_upwards with u; exact ((hcu u).sub (hcu u₀)).pow 2 |>.aestronglyMeasurable)
    (by filter_upwards with u; apply ae_of_all; exact hbound_pt u)
    hbound_int
    (by
      apply ae_of_all
      intro z
      have hg : Tendsto (fun u : ℝ³ => bsShift ℓ ψ u z - bsShift ℓ ψ u₀ z) (nhds u₀) (nhds 0) := by
        simpa using (hcont_z z).tendsto u₀ |>.sub_const (bsShift ℓ ψ u₀ z)
      simpa using hg.pow 2)
  simpa [bsL2] using hmain

end Work.BSKinetic.Decomp
