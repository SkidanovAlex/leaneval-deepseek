import Mathlib.Tactic.Have
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Submission.Work.BSKinetic.Decomp.abs_integral_mul_le_sqrt_mul_sqrt
import Submission.Work.BSKinetic.Decomp.bsDir_le_of_bounded_support
import Submission.Work.BSKinetic.Decomp.bsL2_le_of_bounded_support
import Submission.Work.BSKinetic.Decomp.continuous_bsPsi
import Submission.Work.BSKinetic.Decomp.exists_bound_fderiv
import Submission.Work.BSKinetic.Decomp.integrable_fsKinCoeff_mul_bsPsi_sq
import Submission.Work.BSKinetic.abs_bsMean_le
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `ShiftAux` — the two contract-differential inputs of `continuous_bsOneBody`, in their own module

`continuous_bsOneBody` needs, on top of `ShiftDefs` and the three sibling modules
`bsShift_L2_tendsto` (L²-continuity), `bsShift_H1_bounded` (uniform H¹ bound) and
`bsW_le_L2_Dir` (weighted Plancherel bound), two further facts about the shifted state
`bsShift ℓ ψ u`:

* `bsShift_H1_tendsto`: the `H¹`-continuity of `u ↦ bsShift ℓ ψ u` — the Dirichlet word
  `bsDir (bsShift ℓ ψ u − bsShift ℓ ψ u₀)` tends to `0`;
* `bsW_sub_abs_le`: the difference-of-quadratic-forms (weighted Cauchy–Schwarz) estimate for
  `bsW`.

Both are stated and proved here for the shifted family, in the auxiliary namespace
`Work.BSKinetic.Decomp.Aux` (so that they coexist with any sibling module stating the same
facts), and the main module `Work.BSKinetic.Decomp.continuous_bsOneBody` imports them from here.
The proofs are the standard ones: the Leibniz formula for `∂_k (bsShift ℓ ψ u)`, uniform bounds
on `ψ`, `∂_kψ` and the box mean, and the dominated convergence theorem; respectively the weighted
Cauchy–Schwarz inequality combined with `integrable_fsKinCoeff_mul_bsPsi_sq`.
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped ContDiff Topology Real BigOperators ENNReal

namespace Work.BSKinetic.Decomp

namespace Aux

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

open Submission.BoseGases
open Work.BSKinetic

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

/-! ## 0. The box mean is bounded uniformly in the box position -/

/-- The box mean `bsMean ℓ u ψ` of a continuous compactly supported state is bounded uniformly
in `u` (the boxes all have the same volume `ℓ³`). -/
lemma exists_abs_bsMean_le {ℓ : ℝ} (hℓ : ℓ ≠ 0) {ψ : ℝ³ → ℝ}
    (hψ : Continuous ψ) (hcs : HasCompactSupport ψ) :
    ∃ M : ℝ, ∀ u : ℝ³, |bsMean ℓ u ψ| ≤ M := by
  obtain ⟨Mψ, hMψ⟩ := hcs.exists_bound_of_continuous hψ
  have hcomp : IsCompact (acube ℓ) := Work.UBBInputs9.B.acube_isCompact ℓ
  have hvol : (volume : Measure ℝ³) (acube ℓ) < (⊤ : ℝ≥0∞) := hcomp.measure_lt_top
  refine ⟨|(ℓ ^ 3)⁻¹| * (Mψ * (volume : Measure ℝ³).real (acube ℓ)), fun u => ?_⟩
  have h1 : |∫ z in acube ℓ, ψ (ℓ • u + z)| ≤ Mψ * (volume : Measure ℝ³).real (acube ℓ) := by
    rw [← Real.norm_eq_abs]
    exact norm_setIntegral_le_of_norm_le_const hvol (fun z _ => hMψ _)
  rw [bsMean, abs_mul]
  exact mul_le_mul_of_nonneg_left h1 (abs_nonneg _)

/-! ## 1. The derivative of the shifted state -/

/-- **Leibniz formula for `bsShift`**: the derivative of
`bsShift ℓ ψ u = chiScale ℓ * (ψ (· + ℓ•u) − bsMean ℓ u ψ)` is

    `∂(bsShift ℓ ψ u)(z) = χ_ℓ(z)·∂ψ(z + ℓu) + (ψ(z + ℓu) − bsMean ℓ u ψ)·∂χ_ℓ(z)`. -/
lemma fderiv_bsShift_apply {ℓ : ℝ} (hℓ : ℓ ≠ 0) {ψ : ℝ³ → ℝ} (hψ : ContDiff ℝ (⊤ : ENat) ψ)
    (u z v : ℝ³) :
    fderiv ℝ (bsShift ℓ ψ u) z v
      = chiScale ℓ z * fderiv ℝ ψ (z + ℓ • u) v
        + (ψ (z + ℓ • u) - bsMean ℓ u ψ) * fderiv ℝ (chiScale ℓ) z v := by
  have hχ : Differentiable ℝ (chiScale ℓ) := (chiScale_contDiff hℓ).differentiable (by simp)
  have hψd : Differentiable ℝ ψ := hψ.differentiable (by simp)
  have hsh : DifferentiableAt ℝ (fun z : ℝ³ => z + ℓ • u) z := (differentiableAt_id).add_const _
  have hA : DifferentiableAt ℝ (fun z : ℝ³ => ψ (z + ℓ • u) - bsMean ℓ u ψ) z :=
    (hψd.differentiableAt.comp z hsh).sub (differentiableAt_const _)
  rw [show bsShift ℓ ψ u
      = chiScale ℓ * (fun z : ℝ³ => ψ (z + ℓ • u) - bsMean ℓ u ψ) from rfl]
  rw [fderiv_mul (hχ.differentiableAt) hA]
  simp only [add_apply, smul_apply, smul_eq_mul]
  congr 1
  rw [fderiv_sub_const, fderiv_comp_add_right]

/-- The derivative of the *difference* `bsShift ℓ ψ u − bsShift ℓ ψ u₀`. -/
lemma fderiv_bsShift_sub_apply {ℓ : ℝ} (hℓ : 0 < ℓ) {ψ : ℝ³ → ℝ}
    (hψ : ContDiff ℝ (⊤ : ENat) ψ) (u u₀ z : ℝ³) (k : Fin 3) :
    fderiv ℝ (fun z : ℝ³ => bsShift ℓ ψ u z - bsShift ℓ ψ u₀ z) z (kcStdBasis k)
      = fderiv ℝ (bsShift ℓ ψ u) z (kcStdBasis k)
        - fderiv ℝ (bsShift ℓ ψ u₀) z (kcStdBasis k) := by
  have hu : DifferentiableAt ℝ (bsShift ℓ ψ u) z :=
    ((contDiff_bsShift hℓ hψ u).differentiable (by simp)).differentiableAt
  have hu₀ : DifferentiableAt ℝ (bsShift ℓ ψ u₀) z :=
    ((contDiff_bsShift hℓ hψ u₀).differentiable (by simp)).differentiableAt
  rw [show (fun z : ℝ³ => bsShift ℓ ψ u z - bsShift ℓ ψ u₀ z)
      = bsShift ℓ ψ u - bsShift ℓ ψ u₀ from rfl]
  rw [fderiv_sub hu hu₀]
  rfl

/-! ## 2. Pointwise convergence in `u` -/

/-- The box mean is continuous in the box position. -/
lemma bsMean_tendsto {ℓ : ℝ} {ψ : ℝ³ → ℝ} (hψ : Continuous ψ) (u₀ : ℝ³) :
    Filter.Tendsto (fun u : ℝ³ => bsMean ℓ u ψ) (nhds u₀) (nhds (bsMean ℓ u₀ ψ)) := by
  have hF : Continuous (Function.uncurry (fun u z : ℝ³ => ψ (ℓ • u + z))) := by
    apply hψ.comp; fun_prop
  have hcont : Continuous (fun u : ℝ³ => ∫ z in acube ℓ, ψ (ℓ • u + z)) :=
    Commons.Analysis.Calculus.continuous_setIntegral_isCompact
      (Work.UBBInputs9.B.acube_isCompact ℓ) hF
  have h2 : Continuous (fun u : ℝ³ => (ℓ ^ 3)⁻¹ * ∫ z in acube ℓ, ψ (ℓ • u + z)) :=
    hcont.const_mul _
  simpa only [bsMean] using h2.tendsto u₀

/-- Pointwise convergence of the derivative of the shifted state. -/
lemma bsShift_fderiv_tendsto {ℓ : ℝ} (hℓ : 0 < ℓ) {ψ : ℝ³ → ℝ}
    (hψ : ContDiff ℝ (⊤ : ENat) ψ) (k : Fin 3) (z u₀ : ℝ³) :
    Filter.Tendsto (fun u : ℝ³ => fderiv ℝ (bsShift ℓ ψ u) z (kcStdBasis k)) (nhds u₀)
      (nhds (fderiv ℝ (bsShift ℓ ψ u₀) z (kcStdBasis k))) := by
  have hℓne : ℓ ≠ 0 := ne_of_gt hℓ
  have hfd : Continuous (fun w : ℝ³ => fderiv ℝ ψ w (kcStdBasis k)) :=
    (hψ.continuous_fderiv (by simp)).clm_apply continuous_const
  have h1 : Continuous (fun u : ℝ³ => fderiv ℝ ψ (z + ℓ • u) (kcStdBasis k)) :=
    hfd.comp (by fun_prop)
  have hψshift : Continuous (fun u : ℝ³ => ψ (z + ℓ • u)) := hψ.continuous.comp (by fun_prop)
  have h2 := h1.tendsto u₀
  have h3 := hψshift.tendsto u₀
  have h4 := bsMean_tendsto (ℓ := ℓ) hψ.continuous u₀
  have hmain : Filter.Tendsto (fun u : ℝ³ => chiScale ℓ z * fderiv ℝ ψ (z + ℓ • u) (kcStdBasis k)
      + (ψ (z + ℓ • u) - bsMean ℓ u ψ) * fderiv ℝ (chiScale ℓ) z (kcStdBasis k))
      (nhds u₀)
      (nhds (chiScale ℓ z * fderiv ℝ ψ (z + ℓ • u₀) (kcStdBasis k)
      + (ψ (z + ℓ • u₀) - bsMean ℓ u₀ ψ) * fderiv ℝ (chiScale ℓ) z (kcStdBasis k))) :=
    (h2.const_mul _).add ((h3.sub h4).mul_const _)
  rw [show (fun u : ℝ³ => fderiv ℝ (bsShift ℓ ψ u) z (kcStdBasis k))
      = fun u => chiScale ℓ z * fderiv ℝ ψ (z + ℓ • u) (kcStdBasis k)
          + (ψ (z + ℓ • u) - bsMean ℓ u ψ) * fderiv ℝ (chiScale ℓ) z (kcStdBasis k) from by
    funext u; exact fderiv_bsShift_apply hℓne hψ u z (kcStdBasis k),
    show (fderiv ℝ (bsShift ℓ ψ u₀) z (kcStdBasis k))
      = chiScale ℓ z * fderiv ℝ ψ (z + ℓ • u₀) (kcStdBasis k)
          + (ψ (z + ℓ • u₀) - bsMean ℓ u₀ ψ) * fderiv ℝ (chiScale ℓ) z (kcStdBasis k) from
    fderiv_bsShift_apply hℓne hψ u₀ z (kcStdBasis k)]
  exact hmain

/-! ## 3. A uniform integrable bound on the derivative -/

/-- **Uniform integrable bound on `∂_k(bsShift ℓ ψ u)`.**  For every `k` there is an integrable
`B` (compactly supported, continuous) dominating the squared difference of the `k`-th directional
derivative for arbitrary pairs `u₁, u₂`. -/
lemma bsShift_fderiv_bound {ℓ : ℝ} (hℓ : 0 < ℓ) {ψ : ℝ³ → ℝ}
    (hψ : ContDiff ℝ (⊤ : ENat) ψ) (hcs : HasCompactSupport ψ) (k : Fin 3) :
    ∃ B : ℝ³ → ℝ, Integrable B ∧
      ∀ u₁ u₂ z : ℝ³,
        ‖fderiv ℝ (bsShift ℓ ψ u₁) z (kcStdBasis k)
          - fderiv ℝ (bsShift ℓ ψ u₂) z (kcStdBasis k)‖ ^ 2 ≤ B z := by
  have hℓne : ℓ ≠ 0 := ne_of_gt hℓ
  obtain ⟨Cψ, hCψ⟩ := hcs.exists_bound_of_continuous hψ.continuous
  obtain ⟨Cmean, hCmean⟩ := exists_abs_bsMean_le hℓne hψ.continuous hcs
  have hfderiv_cs : HasCompactSupport (fun w : ℝ³ => fderiv ℝ ψ w (kcStdBasis k)) :=
    hcs.fderiv_apply ℝ (kcStdBasis k)
  have hfderiv_cont : Continuous (fun w : ℝ³ => fderiv ℝ ψ w (kcStdBasis k)) :=
    (hψ.continuous_fderiv (by simp)).clm_apply continuous_const
  obtain ⟨Cf, hCf⟩ := hfderiv_cs.exists_bound_of_continuous hfderiv_cont
  have hχcs : HasCompactSupport (chiScale ℓ) := chiScale_hasCompactSupport hℓne
  have hχc : Continuous (chiScale ℓ) := (chiScale_contDiff hℓne).continuous
  have hDcs : HasCompactSupport (fun z : ℝ³ => fderiv ℝ (chiScale ℓ) z (kcStdBasis k)) :=
    hχcs.fderiv_apply ℝ (kcStdBasis k)
  have hDc : Continuous (fun z : ℝ³ => fderiv ℝ (chiScale ℓ) z (kcStdBasis k)) :=
    ((chiScale_contDiff hℓne).continuous_fderiv (by simp)).clm_apply continuous_const
  -- nonnegativity of the constants
  have hCf_nn : 0 ≤ Cf := le_trans (norm_nonneg _) (hCf 0)
  have hCψ_nn : 0 ≤ Cψ := le_trans (norm_nonneg _) (hCψ 0)
  have hCmean_nn : 0 ≤ Cmean := le_trans (abs_nonneg _) (hCmean 0)
  -- the dominating weight
  set W : ℝ³ → ℝ := fun z => |chiScale ℓ z| + |fderiv ℝ (chiScale ℓ) z (kcStdBasis k)|
  have hWcs : HasCompactSupport W := hχcs.abs.add hDcs.abs
  have hWc : Continuous W := (continuous_abs.comp hχc).add (continuous_abs.comp hDc)
  have hW2cs : HasCompactSupport (fun z : ℝ³ => W z ^ 2) :=
    hWcs.comp_left (g := fun t : ℝ => t ^ 2) (by simp)
  have hW2c : Continuous (fun z : ℝ³ => W z ^ 2) := hWc.pow 2
  have hW2int : Integrable (fun z : ℝ³ => W z ^ 2) :=
    hW2c.integrable_of_hasCompactSupport hW2cs
  refine ⟨fun z => (2 * (Cf + (Cψ + Cmean))) ^ 2 * W z ^ 2, hW2int.const_mul _, fun u₁ u₂ z => ?_⟩
  have hstep : ∀ u : ℝ³,
      ‖fderiv ℝ (bsShift ℓ ψ u) z (kcStdBasis k)‖ ≤ (Cf + (Cψ + Cmean)) * W z := by
    intro u
    rw [fderiv_bsShift_apply hℓne hψ u z (kcStdBasis k), Real.norm_eq_abs]
    have h1 : ‖fderiv ℝ ψ (z + ℓ • u) (kcStdBasis k)‖ ≤ Cf := hCf _
    have h2 : ‖ψ (z + ℓ • u) - bsMean ℓ u ψ‖ ≤ Cψ + Cmean := by
      rw [Real.norm_eq_abs]
      calc |ψ (z + ℓ • u) - bsMean ℓ u ψ|
          ≤ |ψ (z + ℓ • u)| + |bsMean ℓ u ψ| := abs_sub _ _
        _ ≤ Cψ + Cmean := by
            have := hCψ (z + ℓ • u); rw [Real.norm_eq_abs] at this; linarith [hCmean u]
    calc |chiScale ℓ z * fderiv ℝ ψ (z + ℓ • u) (kcStdBasis k)
            + (ψ (z + ℓ • u) - bsMean ℓ u ψ) * fderiv ℝ (chiScale ℓ) z (kcStdBasis k)|
        ≤ |chiScale ℓ z * fderiv ℝ ψ (z + ℓ • u) (kcStdBasis k)|
          + |(ψ (z + ℓ • u) - bsMean ℓ u ψ) * fderiv ℝ (chiScale ℓ) z (kcStdBasis k)| :=
          abs_add_le _ _
      _ = |chiScale ℓ z| * |fderiv ℝ ψ (z + ℓ • u) (kcStdBasis k)|
          + |ψ (z + ℓ • u) - bsMean ℓ u ψ| * |fderiv ℝ (chiScale ℓ) z (kcStdBasis k)| := by
          rw [abs_mul, abs_mul]
      _ ≤ Cf * |chiScale ℓ z| + (Cψ + Cmean) * |fderiv ℝ (chiScale ℓ) z (kcStdBasis k)| := by
          have hrw : |chiScale ℓ z| * |fderiv ℝ ψ (z + ℓ • u) (kcStdBasis k)|
              = |fderiv ℝ ψ (z + ℓ • u) (kcStdBasis k)| * |chiScale ℓ z| := mul_comm _ _
          rw [hrw]
          exact add_le_add
            (mul_le_mul_of_nonneg_right h1 (abs_nonneg _))
            (mul_le_mul_of_nonneg_right (by rw [Real.norm_eq_abs] at h2; exact h2) (abs_nonneg _))
      _ ≤ (Cf + (Cψ + Cmean)) * W z := by
          rw [show W z = |chiScale ℓ z| + |fderiv ℝ (chiScale ℓ) z (kcStdBasis k)| from rfl,
            add_mul]
          nlinarith [abs_nonneg (chiScale ℓ z),
            abs_nonneg (fderiv ℝ (chiScale ℓ) z (kcStdBasis k)),
            mul_nonneg hCf_nn (abs_nonneg (chiScale ℓ z)),
            mul_nonneg hCmean_nn (abs_nonneg (fderiv ℝ (chiScale ℓ) z (kcStdBasis k))),
            mul_nonneg hCψ_nn (abs_nonneg (fderiv ℝ (chiScale ℓ) z (kcStdBasis k))),
            mul_nonneg hCf_nn (abs_nonneg (fderiv ℝ (chiScale ℓ) z (kcStdBasis k)))]
  have hK : ‖fderiv ℝ (bsShift ℓ ψ u₁) z (kcStdBasis k)
      - fderiv ℝ (bsShift ℓ ψ u₂) z (kcStdBasis k)‖
      ≤ 2 * (Cf + (Cψ + Cmean)) * W z := by
    calc _ ≤ ‖fderiv ℝ (bsShift ℓ ψ u₁) z (kcStdBasis k)‖
            + ‖fderiv ℝ (bsShift ℓ ψ u₂) z (kcStdBasis k)‖ := norm_sub_le _ _
      _ ≤ (Cf + (Cψ + Cmean)) * W z + (Cf + (Cψ + Cmean)) * W z :=
          add_le_add (hstep u₁) (hstep u₂)
      _ = 2 * (Cf + (Cψ + Cmean)) * W z := by ring
  have hnn : 0 ≤ 2 * (Cf + (Cψ + Cmean)) * W z :=
    le_trans (norm_nonneg _) hK
  calc ‖fderiv ℝ (bsShift ℓ ψ u₁) z (kcStdBasis k)
          - fderiv ℝ (bsShift ℓ ψ u₂) z (kcStdBasis k)‖ ^ 2
      ≤ (2 * (Cf + (Cψ + Cmean)) * W z) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hK 2
    _ = (2 * (Cf + (Cψ + Cmean))) ^ 2 * W z ^ 2 := by ring

/-! ## 4. The abstract `L²` convergence lemma -/

/-- **Dominated-convergence lemma.**  If `f u → f u₀` pointwise, all `f u` are measurable, and
the squared differences are dominated by an integrable `bound`, then `∫ (f u − f u₀)² → 0`. -/
lemma tendsto_integral_sq_sub {ι : Type*} {l : Filter ι} [l.IsCountablyGenerated]
    {f : ι → ℝ³ → ℝ} {u₀ : ι} {bound : ℝ³ → ℝ}
    (hmeas : ∀ u, AEStronglyMeasurable (f u) (volume : Measure ℝ³))
    (hbound : ∀ᶠ u in l, ∀ᵐ z ∂(volume : Measure ℝ³), ‖f u z - f u₀ z‖ ^ 2 ≤ bound z)
    (hbound_int : Integrable bound (volume : Measure ℝ³))
    (hlim : ∀ᵐ z ∂(volume : Measure ℝ³), Tendsto (fun u => f u z) l (nhds (f u₀ z))) :
    Tendsto (fun u => ∫ z, (f u z - f u₀ z) ^ 2) l (nhds 0) := by
  have h := tendsto_integral_filter_of_dominated_convergence (l := l)
      (F := fun u z => (f u z - f u₀ z) ^ 2) (f := fun _ : ℝ³ => (0 : ℝ)) bound ?_ ?_ hbound_int ?_
  · simpa using h
  · filter_upwards with u
    exact ((hmeas u).sub (hmeas u₀)).pow 2
  · filter_upwards [hbound] with u hu
    filter_upwards [hu] with z hz
    have hthis : ‖(f u z - f u₀ z) ^ 2‖ = ‖f u z - f u₀ z‖ ^ 2 := by
      rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), sq_abs]
    rw [hthis]; exact hz
  · filter_upwards [hlim] with z hz
    have h2 := (hz.sub_const (f u₀ z)).pow 2
    simpa using h2

/-! ## 5. The main theorem -/

theorem bsShift_H1_tendsto {ℓ : ℝ} (hℓ : 0 < ℓ) {ψ : EuclideanSpace ℝ (Fin 3) → ℝ}
    (hψ : ContDiff ℝ (⊤ : ENat) ψ) (hcs : HasCompactSupport ψ)
    (u₀ : EuclideanSpace ℝ (Fin 3)) :
    Filter.Tendsto (fun u : EuclideanSpace ℝ (Fin 3) =>
        Work.BSKinetic.Decomp.bsDir (fun z : EuclideanSpace ℝ (Fin 3) =>
          Work.BSKinetic.Decomp.bsShift ℓ ψ u z
            - Work.BSKinetic.Decomp.bsShift ℓ ψ u₀ z))
      (nhds u₀) (nhds 0) := by
  have hu : ∀ u : ℝ³,
      bsDir (fun z : ℝ³ => bsShift ℓ ψ u z - bsShift ℓ ψ u₀ z)
        = ∑ k : Fin 3,
            ∫ z : ℝ³, (fderiv ℝ (fun z : ℝ³ => bsShift ℓ ψ u z - bsShift ℓ ψ u₀ z) z
              (kcStdBasis k)) ^ 2 := fun u => rfl
  simp only [hu]
  rw [show (0 : ℝ) = ∑ _k : Fin 3, (0 : ℝ) by simp]
  apply tendsto_finsetSum
  intro k _
  -- the pointwise-convergence + domination data for the `k`-th directional derivative
  obtain ⟨B, hBint, hB⟩ := bsShift_fderiv_bound hℓ hψ hcs k
  have hmeas : ∀ u : ℝ³,
      AEStronglyMeasurable (fun z : ℝ³ => fderiv ℝ (bsShift ℓ ψ u) z (kcStdBasis k))
        (volume : Measure ℝ³) := fun u =>
    (((contDiff_bsShift hℓ hψ u).continuous_fderiv (by simp)).clm_apply continuous_const).aestronglyMeasurable
  have hlim : ∀ᵐ z ∂(volume : Measure ℝ³),
      Tendsto (fun u : ℝ³ => fderiv ℝ (bsShift ℓ ψ u) z (kcStdBasis k)) (nhds u₀)
        (nhds (fderiv ℝ (bsShift ℓ ψ u₀) z (kcStdBasis k))) :=
    Eventually.of_forall fun z => bsShift_fderiv_tendsto hℓ hψ k z u₀
  have hbdd : ∀ᶠ u in (nhds u₀), ∀ᵐ z ∂(volume : Measure ℝ³),
      ‖fderiv ℝ (bsShift ℓ ψ u) z (kcStdBasis k)
        - fderiv ℝ (bsShift ℓ ψ u₀) z (kcStdBasis k)‖ ^ 2 ≤ B z :=
    Eventually.of_forall fun u => Eventually.of_forall fun z => hB u u₀ z
  have hk := tendsto_integral_sq_sub (l := nhds u₀)
    (f := fun u : ℝ³ => fun z : ℝ³ => fderiv ℝ (bsShift ℓ ψ u) z (kcStdBasis k))
    (u₀ := u₀) (bound := B) hmeas hbdd hBint hlim
  -- identify the two integrands
  have heq : (fun u : ℝ³ => ∫ z : ℝ³,
        (fderiv ℝ (fun z : ℝ³ => bsShift ℓ ψ u z - bsShift ℓ ψ u₀ z) z (kcStdBasis k)) ^ 2)
      = (fun u : ℝ³ => ∫ z : ℝ³,
        (fderiv ℝ (bsShift ℓ ψ u) z (kcStdBasis k)
          - fderiv ℝ (bsShift ℓ ψ u₀) z (kcStdBasis k)) ^ 2) := by
    funext u
    apply integral_congr_ae
    filter_upwards with z
    rw [fderiv_bsShift_sub_apply hℓ hψ u u₀ z k]
  rw [heq]
  exact hk

/-! ## 1. Weighted Cauchy–Schwarz -/

/-- Weighted Cauchy–Schwarz: for `w ≥ 0` and `√w·f, √w·g ∈ L²`,
`|∫ w·f·g| ≤ √(∫ w f²)·√(∫ w g²)`. -/
lemma weighted_cs {α : Type*} [MeasurableSpace α] {μ : Measure α} {w f g : α → ℝ}
    (hw : ∀ x, 0 ≤ w x)
    (hmf : MemLp (fun x => Real.sqrt (w x) * f x) 2 μ)
    (hmg : MemLp (fun x => Real.sqrt (w x) * g x) 2 μ) :
    |∫ x, w x * f x * g x ∂μ|
      ≤ Real.sqrt (∫ x, w x * f x ^ 2 ∂μ) * Real.sqrt (∫ x, w x * g x ^ 2 ∂μ) := by
  have h1 : ∀ x, (Real.sqrt (w x) * f x) * (Real.sqrt (w x) * g x) = w x * f x * g x := by
    intro x
    have hsq : Real.sqrt (w x) * Real.sqrt (w x) = w x := by
      simpa [pow_two] using Real.sq_sqrt (hw x)
    calc (Real.sqrt (w x) * f x) * (Real.sqrt (w x) * g x)
        = (Real.sqrt (w x) * Real.sqrt (w x)) * f x * g x := by ring
      _ = w x * f x * g x := by rw [hsq]
  have h2 : ∀ x, (Real.sqrt (w x) * f x) ^ 2 = w x * f x ^ 2 := by
    intro x
    rw [mul_pow, Real.sq_sqrt (hw x)]
  have h3 : ∀ x, (Real.sqrt (w x) * g x) ^ 2 = w x * g x ^ 2 := by
    intro x
    rw [mul_pow, Real.sq_sqrt (hw x)]
  have hcs := abs_integral_mul_le_sqrt_mul_sqrt hmf hmg
  have hL : (∫ x, (Real.sqrt (w x) * f x) * (Real.sqrt (w x) * g x) ∂μ)
      = ∫ x, w x * f x * g x ∂μ := integral_congr_ae (Filter.Eventually.of_forall h1)
  have hF : (∫ x, (Real.sqrt (w x) * f x) ^ 2 ∂μ) = ∫ x, w x * f x ^ 2 ∂μ :=
    integral_congr_ae (Filter.Eventually.of_forall h2)
  have hG : (∫ x, (Real.sqrt (w x) * g x) ^ 2 ∂μ) = ∫ x, w x * g x ^ 2 ∂μ :=
    integral_congr_ae (Filter.Eventually.of_forall h3)
  calc |∫ x, w x * f x * g x ∂μ|
      = |∫ x, (Real.sqrt (w x) * f x) * (Real.sqrt (w x) * g x) ∂μ| := by rw [hL]
    _ ≤ Real.sqrt (∫ x, (Real.sqrt (w x) * f x) ^ 2 ∂μ)
          * Real.sqrt (∫ x, (Real.sqrt (w x) * g x) ^ 2 ∂μ) := hcs
    _ = Real.sqrt (∫ x, w x * f x ^ 2 ∂μ) * Real.sqrt (∫ x, w x * g x ^ 2 ∂μ) := by
        rw [hF, hG]

/-! ## 2. The weighted quadratic difference estimate -/

/-- **The weighted quadratic inequality.**  For `w ≥ 0` and `|a − b| ≤ d` pointwise, with the
three weighted integrals finite,

`|∫ w a² − ∫ w b²| ≤ √(∫ w d²) · √(2∫ w a² + 2∫ w b²)`. -/
lemma abs_wquad_sub_le {α : Type*} [MeasurableSpace α] {μ : Measure α} {w a b d : α → ℝ}
    (hw : ∀ x, 0 ≤ w x) (hd : ∀ x, |a x - b x| ≤ d x)
    (ha : Integrable (fun x => w x * a x ^ 2) μ)
    (hb : Integrable (fun x => w x * b x ^ 2) μ)
    (hdint : Integrable (fun x => w x * d x ^ 2) μ)
    (hmf : AEStronglyMeasurable (fun x => Real.sqrt (w x) * (a x - b x)) μ)
    (hmg : AEStronglyMeasurable (fun x => Real.sqrt (w x) * (a x + b x)) μ) :
    |∫ x, w x * a x ^ 2 ∂μ - ∫ x, w x * b x ^ 2 ∂μ|
      ≤ Real.sqrt (∫ x, w x * d x ^ 2 ∂μ)
        * Real.sqrt (2 * ∫ x, w x * a x ^ 2 ∂μ + 2 * ∫ x, w x * b x ^ 2 ∂μ) := by
  have hsq : ∀ x, (a x - b x) ^ 2 ≤ d x ^ 2 := by
    intro x
    rw [← sq_abs (a x - b x)]
    exact pow_le_pow_left₀ (abs_nonneg _) (hd x) 2
  have hsum : ∀ x, (a x + b x) ^ 2 ≤ 2 * a x ^ 2 + 2 * b x ^ 2 := by
    intro x
    nlinarith [sq_nonneg (a x - b x)]
  have hFint : Integrable (fun x => w x * (a x - b x) ^ 2) μ := by
    refine Integrable.mono' hdint ((hmf.pow 2).congr ?_)
      (Filter.Eventually.of_forall fun x => ?_)
    · exact Filter.Eventually.of_forall fun x => by
        show (Real.sqrt (w x) * (a x - b x)) ^ 2 = w x * (a x - b x) ^ 2
        rw [mul_pow, Real.sq_sqrt (hw x)]
    · rw [Real.norm_of_nonneg (mul_nonneg (hw x) (sq_nonneg _))]
      exact mul_le_mul_of_nonneg_left (hsq x) (hw x)
  have hDomint : Integrable (fun x => 2 * (w x * a x ^ 2) + 2 * (w x * b x ^ 2)) μ :=
    (ha.const_mul 2).add (hb.const_mul 2)
  have hGint : Integrable (fun x => w x * (a x + b x) ^ 2) μ := by
    refine Integrable.mono' hDomint ((hmg.pow 2).congr ?_)
      (Filter.Eventually.of_forall fun x => ?_)
    · exact Filter.Eventually.of_forall fun x => by
        show (Real.sqrt (w x) * (a x + b x)) ^ 2 = w x * (a x + b x) ^ 2
        rw [mul_pow, Real.sq_sqrt (hw x)]
    · rw [Real.norm_of_nonneg (mul_nonneg (hw x) (sq_nonneg _))]
      calc w x * (a x + b x) ^ 2 ≤ w x * (2 * a x ^ 2 + 2 * b x ^ 2) :=
            mul_le_mul_of_nonneg_left (hsum x) (hw x)
        _ = 2 * (w x * a x ^ 2) + 2 * (w x * b x ^ 2) := by ring
  have hFmem : MemLp (fun x => Real.sqrt (w x) * (a x - b x)) 2 μ :=
    (memLp_two_iff_integrable_sq hmf).mpr (hFint.congr (Filter.Eventually.of_forall fun x => by
      show w x * (a x - b x) ^ 2 = (Real.sqrt (w x) * (a x - b x)) ^ 2
      rw [mul_pow, Real.sq_sqrt (hw x)]))
  have hGmem : MemLp (fun x => Real.sqrt (w x) * (a x + b x)) 2 μ :=
    (memLp_two_iff_integrable_sq hmg).mpr (hGint.congr (Filter.Eventually.of_forall fun x => by
      show w x * (a x + b x) ^ 2 = (Real.sqrt (w x) * (a x + b x)) ^ 2
      rw [mul_pow, Real.sq_sqrt (hw x)]))
  have hdiff : ∫ x, w x * a x ^ 2 ∂μ - ∫ x, w x * b x ^ 2 ∂μ
      = ∫ x, w x * (a x - b x) * (a x + b x) ∂μ := by
    rw [← integral_sub ha hb]
    exact integral_congr_ae (Filter.Eventually.of_forall fun x => by ring)
  rw [hdiff]
  refine (weighted_cs hw hFmem hGmem).trans ?_
  have hN : (∫ x, w x * (a x - b x) ^ 2 ∂μ) ≤ ∫ x, w x * d x ^ 2 ∂μ :=
    integral_mono_ae hFint hdint
      (Filter.Eventually.of_forall fun x => mul_le_mul_of_nonneg_left (hsq x) (hw x))
  have hP : (∫ x, w x * (a x + b x) ^ 2 ∂μ)
      ≤ 2 * ∫ x, w x * a x ^ 2 ∂μ + 2 * ∫ x, w x * b x ^ 2 ∂μ := by
    have h := integral_mono_ae hGint hDomint (Filter.Eventually.of_forall fun x =>
      calc w x * (a x + b x) ^ 2 ≤ w x * (2 * a x ^ 2 + 2 * b x ^ 2) :=
            mul_le_mul_of_nonneg_left (hsum x) (hw x)
        _ = 2 * (w x * a x ^ 2) + 2 * (w x * b x ^ 2) := by ring)
    rwa [integral_add (ha.const_mul 2) (hb.const_mul 2), integral_const_mul,
      integral_const_mul] at h
  exact mul_le_mul (Real.sqrt_le_sqrt hN) (Real.sqrt_le_sqrt hP)
    (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)

/-! ## 3. The estimate for `bsW` -/

theorem bsW_sub_abs_le {c : ℝ} {h₁ h₂ : EuclideanSpace ℝ (Fin 3) → ℝ}
    (h₁d : ContDiff ℝ (⊤ : ENat) h₁) (h₁c : HasCompactSupport h₁)
    (h₂d : ContDiff ℝ (⊤ : ENat) h₂) (h₂c : HasCompactSupport h₂) :
    |Work.BSKinetic.Decomp.bsW (Submission.BoseGases.fsKinCoeff c) h₁
        - Work.BSKinetic.Decomp.bsW (Submission.BoseGases.fsKinCoeff c) h₂|
      ≤ Real.sqrt (Work.BSKinetic.Decomp.bsW (Submission.BoseGases.fsKinCoeff c)
            (fun z => h₁ z - h₂ z))
        * Real.sqrt (2 * Work.BSKinetic.Decomp.bsW (Submission.BoseGases.fsKinCoeff c) h₁
            + 2 * Work.BSKinetic.Decomp.bsW (Submission.BoseGases.fsKinCoeff c) h₂) := by
  have hsd : ContDiff ℝ (⊤ : ENat) (fun z : ℝ³ => h₁ z - h₂ z) := h₁d.sub h₂d
  have hsc : HasCompactSupport (fun z : ℝ³ => h₁ z - h₂ z) := h₁c.sub h₂c
  have hcont₁ : Continuous (fun p : ℝ³ => ‖bsPsi h₁ p‖) := (continuous_bsPsi h₁d h₁c).norm
  have hcont₂ : Continuous (fun p : ℝ³ => ‖bsPsi h₂ p‖) := (continuous_bsPsi h₂d h₂c).norm
  have hwcont : Continuous (fun p : ℝ³ => Submission.BoseGases.fsKinCoeff c ‖p‖) := by
    simp only [Submission.BoseGases.fsKinCoeff]
    fun_prop
  exact abs_wquad_sub_le (μ := (volume : Measure ℝ³))
    (w := fun p : ℝ³ => Submission.BoseGases.fsKinCoeff c ‖p‖)
    (a := fun p : ℝ³ => ‖bsPsi h₁ p‖)
    (b := fun p : ℝ³ => ‖bsPsi h₂ p‖)
    (d := fun p : ℝ³ => ‖bsPsi (fun z => h₁ z - h₂ z) p‖)
    (fun p => Submission.BoseGases.fsKinCoeff_nonneg c ‖p‖)
    (fun p => by
      rw [bsPsi_sub h₁d h₁c h₂d h₂c p]
      exact abs_norm_sub_norm_le _ _)
    (integrable_fsKinCoeff_mul_bsPsi_sq h₁d h₁c)
    (integrable_fsKinCoeff_mul_bsPsi_sq h₂d h₂c)
    (integrable_fsKinCoeff_mul_bsPsi_sq hsd hsc)
    (((Real.continuous_sqrt.comp hwcont).mul (hcont₁.sub hcont₂)).aestronglyMeasurable)
    (((Real.continuous_sqrt.comp hwcont).mul (hcont₁.add hcont₂)).aestronglyMeasurable)

/-! ## 0'. Uniform `L²`/`H¹` bound for the shifted state -/

/-- Triangle inequality in the form `|a - b| ≤ |a| + |b|`. -/
lemma abs_sub_le_abs_add_abs (a b : ℝ) : |a - b| ≤ |a| + |b| := by
  rw [sub_eq_add_neg]
  simpa using abs_add_le a (-b)

/-- `bsShift ℓ ψ u` vanishes off the centred cube `acube ℓ`: its window `chiScale ℓ` does. -/
lemma bsShift_eq_zero_of_not_mem_acube {ℓ : ℝ} (hℓ : 0 < ℓ) {ψ : ℝ³ → ℝ} (u : ℝ³) :
    ∀ z : ℝ³, z ∉ acube ℓ → bsShift ℓ ψ u z = 0 := by
  intro z hz
  rw [bsShift_apply, Work.UBBInputs9.B.chiScale_eq_zero_of_not_mem_acube hℓ hz, zero_mul]

/-- The chain/product rule for `bsShift`: the derivative of
`z ↦ χ_ℓ(z)·(ψ(z + ℓ•u) − ⨍ψ)` is `χ_ℓ(z)·dψ(z+ℓ•u) + (ψ(z+ℓ•u) − ⨍ψ)·dχ_ℓ(z)`. -/
lemma fderiv_bsShift_apply_pos {ℓ : ℝ} (hℓ : 0 < ℓ) {ψ : ℝ³ → ℝ} (hψ : ContDiff ℝ (⊤ : ENat) ψ)
    (u z v : ℝ³) :
    fderiv ℝ (bsShift ℓ ψ u) z v
      = chiScale ℓ z * fderiv ℝ ψ (z + ℓ • u) v
        + (ψ (z + ℓ • u) - bsMean ℓ u ψ) * fderiv ℝ (chiScale ℓ) z v := by
  have hχ : HasFDerivAt (chiScale ℓ) (fderiv ℝ (chiScale ℓ) z) z :=
    ((chiScale_contDiff (ne_of_gt hℓ)).contDiffAt.differentiableAt (by simp)).hasFDerivAt
  have hψat : HasFDerivAt ψ (fderiv ℝ ψ (z + ℓ • u)) (z + ℓ • u) :=
    (hψ.contDiffAt.differentiableAt (by simp)).hasFDerivAt
  have h1 : HasFDerivAt (fun w : ℝ³ => ψ (w + ℓ • u)) (fderiv ℝ ψ (z + ℓ • u)) z :=
    (hasFDerivAt_comp_add_right (ℓ • u)).2 hψat
  have hG : HasFDerivAt (fun w : ℝ³ => ψ (w + ℓ • u) - bsMean ℓ u ψ)
      (fderiv ℝ ψ (z + ℓ • u)) z := h1.sub_const _
  have hmul : HasFDerivAt (fun w : ℝ³ => chiScale ℓ w * (ψ (w + ℓ • u) - bsMean ℓ u ψ))
      ((chiScale ℓ z) • fderiv ℝ ψ (z + ℓ • u)
        + (ψ (z + ℓ • u) - bsMean ℓ u ψ) • fderiv ℝ (chiScale ℓ) z) z := hχ.mul hG
  rw [show bsShift ℓ ψ u
        = (fun w : ℝ³ => chiScale ℓ w * (ψ (w + ℓ • u) - bsMean ℓ u ψ)) from rfl, hmul.fderiv]
  simp [add_apply, smul_apply, smul_eq_mul]

/-! ## The main statement -/

theorem bsShift_H1_bounded {ℓ : ℝ} (hℓ : 0 < ℓ) {ψ : EuclideanSpace ℝ (Fin 3) → ℝ}
    (hψ : ContDiff ℝ (⊤ : ENat) ψ) (hcs : HasCompactSupport ψ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ u : EuclideanSpace ℝ (Fin 3),
      Work.BSKinetic.Decomp.bsL2 (Work.BSKinetic.Decomp.bsShift ℓ ψ u) ≤ K
        ∧ Work.BSKinetic.Decomp.bsDir (Work.BSKinetic.Decomp.bsShift ℓ ψ u) ≤ K := by
  -- uniform bounds for the state `ψ` and for the window `chiScale ℓ`
  obtain ⟨Mψ, hMψ0, hMψ, hdMψ⟩ := exists_bound_fderiv hψ hcs
  have hχcd : ContDiff ℝ (⊤ : ENat) (chiScale ℓ) := chiScale_contDiff (ne_of_gt hℓ)
  have hχcs : HasCompactSupport (chiScale ℓ) := chiScale_hasCompactSupport (ne_of_gt hℓ)
  obtain ⟨Mχ, hMχ0, hMχ, hdMχ⟩ := exists_bound_fderiv hχcd hχcs
  have hwindow : ∀ x : ℝ³, |chiScale ℓ x| ≤ chiSup := fun x => abs_chiScale_le_chiSup ℓ x
  have hbk : ∀ k : Fin 3, ‖kcStdBasis k‖ = 1 := by
    intro k; simp [kcStdBasis]
  -- the two constants
  have hC0 : 0 ≤ chiSup * (Mψ + Mψ) := by nlinarith [hMψ0, chiSup_pos]
  have hD0 : 0 ≤ chiSup * Mψ + (Mψ + Mψ) * Mχ :=
    add_nonneg (mul_nonneg chiSup_pos.le (by linarith))
      (mul_nonneg (by linarith) hMχ0)
  refine ⟨max ((chiSup * (Mψ + Mψ)) ^ 2 * ℓ ^ 3)
      (3 * ((chiSup * Mψ + (Mψ + Mψ) * Mχ) ^ 2 * ℓ ^ 3)),
    le_max_of_le_left (mul_nonneg (sq_nonneg _) (pow_pos hℓ 3).le), ?_⟩
  intro u
  have hzb : ∀ z : ℝ³, z ∉ acube ℓ → bsShift ℓ ψ u z = 0 :=
    bsShift_eq_zero_of_not_mem_acube hℓ u
  have hmean : |bsMean ℓ u ψ| ≤ Mψ := Work.BSKinetic.abs_bsMean_le hℓ hMψ u
  -- pointwise bound on the state
  have hbL2 : ∀ z : ℝ³, |bsShift ℓ ψ u z| ≤ chiSup * (Mψ + Mψ) := by
    intro z
    rw [bsShift_apply, abs_mul]
    calc |chiScale ℓ z| * |ψ (z + ℓ • u) - bsMean ℓ u ψ|
        ≤ chiSup * (|ψ (z + ℓ • u)| + |bsMean ℓ u ψ|) :=
          mul_le_mul (hwindow z) (abs_sub_le_abs_add_abs _ _) (abs_nonneg _) chiSup_pos.le
      _ ≤ chiSup * (Mψ + Mψ) :=
          mul_le_mul_of_nonneg_left (add_le_add (hMψ _) hmean) chiSup_pos.le
  -- pointwise bound on the derivative
  have hbD : ∀ (k : Fin 3) (z : ℝ³),
      |fderiv ℝ (bsShift ℓ ψ u) z (kcStdBasis k)| ≤ chiSup * Mψ + (Mψ + Mψ) * Mχ := by
    intro k z
    rw [fderiv_bsShift_apply_pos hℓ hψ u z (kcStdBasis k)]
    have h1 : |chiScale ℓ z * fderiv ℝ ψ (z + ℓ • u) (kcStdBasis k)| ≤ chiSup * Mψ := by
      rw [abs_mul]
      calc |chiScale ℓ z| * |fderiv ℝ ψ (z + ℓ • u) (kcStdBasis k)|
          ≤ chiSup * (Mψ * ‖kcStdBasis k‖) :=
            mul_le_mul (hwindow z) (by rw [← Real.norm_eq_abs]; exact hdMψ _ _)
              (abs_nonneg _) chiSup_pos.le
        _ = chiSup * Mψ := by rw [hbk k, mul_one]
    have h2 : |(ψ (z + ℓ • u) - bsMean ℓ u ψ) * fderiv ℝ (chiScale ℓ) z (kcStdBasis k)|
        ≤ (Mψ + Mψ) * Mχ := by
      rw [abs_mul]
      calc |ψ (z + ℓ • u) - bsMean ℓ u ψ| * |fderiv ℝ (chiScale ℓ) z (kcStdBasis k)|
          ≤ (Mψ + Mψ) * (Mχ * ‖kcStdBasis k‖) :=
            mul_le_mul ((abs_sub_le_abs_add_abs _ _).trans (add_le_add (hMψ _) hmean))
              (by rw [← Real.norm_eq_abs]; exact hdMχ _ _) (abs_nonneg _) (by linarith)
        _ = (Mψ + Mψ) * Mχ := by rw [hbk k, mul_one]
    exact (abs_add_le _ _).trans (add_le_add h1 h2)
  exact ⟨(bsL2_le_of_bounded_support hℓ hC0 hbL2 hzb).trans (le_max_left _ _),
    (bsDir_le_of_bounded_support hℓ hD0 hbD hzb).trans (le_max_right _ _)⟩

end Aux

end Work.BSKinetic.Decomp
