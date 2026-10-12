import Mathlib.Tactic.Have
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BSKinetic.bsW_fsKinCoeff_le
import Submission.Work.BlockBound4.chiScale_grad_bound
import Submission.Work.BoseFixB1.Core.MM.bsW_chiB_sub_aestronglyMeasurable
import Submission.Work.BoseFixB1S.corrMarg.support_u
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The `u`-integrability of the sliding cut kinetic word `χ_{B(u)}·(g − ρ u)`

The lemma of this file is the `u`-marginal integrability of the cut one-body kinetic word

    `u ↦ bsW (fsKinCoeff c) (fun z => chiB ℓ d u z * (g z − ρ u))`

on `ℝ³` (Lebesgue measure), for `0 < ℓ`, `0 < d`, a smooth profile `g` and a measurable,
uniformly bounded shift `ρ`.

The mechanism is the three-step standard argument for this family:

* **a.e. strong measurability.**  `kinFT` and `bsW` are *parametric Bochner integrals* over all
  of `ℝ³` with no integrability hypothesis on the integrand, so the joint-measurability device
  `MeasureTheory.StronglyMeasurable.integral_prod_right'` is used twice; this is the module
  `Submission.Work.BoseFixB1.Core.MM.bsW_chiB_sub_aestronglyMeasurable`
  (`bsW_chiB_sub_aestronglyMeasurable`), which needs from `ρ` only measurability.

* **a uniform-in-`u` bound.**  `χ_{B(u)}(z) = chiScale ℓ z · chiScale (ℓd)(z − (ℓd)•u)` is
  supported in the *fixed* box `acube ℓ` for every `u`, and on that fixed box the state
  `z ↦ χ_{B(u)}(z)(g z − ρ u)`, together with its first partial derivatives, is bounded
  uniformly in `u` — the sup-bound comes from `|χ_B| ≤ chiSup²`, `|g| ≤ S` and `|ρ| ≤ Cp`, the
  derivative bound from Leibniz and the uniform window-gradient bound
  `Σ_k (∂_k chiScale s)² ≤ K/s²` of `Work.BlockBound4.chiScale_grad_bound`.  The box-supported
  a priori estimate `Work.BSKinetic.bsW_fsKinCoeff_le` then turns these into a constant bound
  `|bsW …| ≤ B` *uniform in* `u`.

* **the support in `u`.**  `χ_{B(u)}` vanishes identically as soon as the sliding centre leaves
  the fixed cube `acube ((1+d)/d)` (`Work.BoseFixB1S.chiB_mul_eq_zero_of_not_mem_acube_u`), a
  measurable set of finite Lebesgue measure; hence off it the whole integrand is `0`.  With the
  two previous steps, `MeasureTheory.Integrable.mono'` against the indicator of that cube
  finishes the proof.
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped Topology Real BigOperators

namespace Work.BoseFixB1.Core.MM

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

open Submission.BoseGases

set_option autoImplicit false
set_option maxHeartbeats 800000

/-! ## An auxiliary: the window-gradient bound in the form needed below -/

/-- The per-coordinate form of the uniform window-gradient bound
`Σ_k (∂_k chiScale s)² ≤ K/s²` (`Work.BlockBound4.chiScale_grad_bound`): every coordinate
partial derivative of the window is bounded by `√K/s`. -/
private lemma abs_fderiv_chiScale_basis_le_sqrt {K : ℝ}
    (hKb : ∀ (s : ℝ), 0 < s → ∀ x : EuclideanSpace ℝ (Fin 3),
      ∑ k : Fin 3, (fderiv ℝ (chiScale s) x (kcStdBasis k)) ^ 2 ≤ K / s ^ 2)
    {s : ℝ} (hs : 0 < s) (y : EuclideanSpace ℝ (Fin 3)) (k : Fin 3) :
    |fderiv ℝ (chiScale s) y (kcStdBasis k)| ≤ Real.sqrt K / s := by
  have h1 : (fderiv ℝ (chiScale s) y (kcStdBasis k)) ^ 2 ≤ K / s ^ 2 :=
    le_trans (Finset.single_le_sum (s := Finset.univ)
      (f := fun j : Fin 3 => (fderiv ℝ (chiScale s) y (kcStdBasis j)) ^ 2)
      (fun j _ => sq_nonneg _) (Finset.mem_univ k)) (hKb s hs y)
  have h2 : Real.sqrt ((fderiv ℝ (chiScale s) y (kcStdBasis k)) ^ 2)
      ≤ Real.sqrt (K / s ^ 2) :=
    Real.sqrt_le_sqrt h1
  rwa [Real.sqrt_sq_eq_abs, Real.sqrt_div' K (sq_nonneg s), Real.sqrt_sq (le_of_lt hs)] at h2

/-! ## The target -/

theorem integrable_bsW_chiB {ℓ d c : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d)
    {g : EuclideanSpace ℝ (Fin 3) → ℝ} (hg : ContDiff ℝ (⊤ : ENat) g)
    {ρ : EuclideanSpace ℝ (Fin 3) → ℝ} (hρ : Measurable ρ)
    (hρb : ∃ C : ℝ, ∀ u : EuclideanSpace ℝ (Fin 3), |ρ u| ≤ C) :
    MeasureTheory.Integrable (fun u : EuclideanSpace ℝ (Fin 3) =>
      Work.BSKinetic.Decomp.bsW (Submission.BoseGases.fsKinCoeff c)
        (fun z : EuclideanSpace ℝ (Fin 3) =>
          Submission.BoseGases.chiB ℓ d u z * (g z - ρ u))) := by
  -- ## 1. a.e. strong measurability (parametric-integral device, jointly measurable kernel)
  have hA : AEStronglyMeasurable (fun u : ℝ³ =>
      Work.BSKinetic.Decomp.bsW (fsKinCoeff c)
        (fun z : ℝ³ => chiB ℓ d u z * (g z - ρ u))) volume :=
    bsW_chiB_sub_aestronglyMeasurable (ℓ := ℓ) (d := d) (c := c) hg.continuous hρ
  -- ## 2. uniform bounds for `g`, `ρ` and the window gradient
  obtain ⟨S₀, hS₀⟩ := (acube_compact hℓ).exists_bound_of_continuousOn hg.continuous.continuousOn
  obtain ⟨M₀, hM₀⟩ := (acube_compact hℓ).exists_bound_of_continuousOn
    ((hg.continuous_fderiv (by simp)).norm.continuousOn)
  obtain ⟨Cρ, hCρ⟩ := hρb
  obtain ⟨K, _hK0, hKb⟩ := Work.BlockBound4.chiScale_grad_bound
  set S : ℝ := max S₀ 0 with hSdef
  set M : ℝ := max M₀ 0 with hMdef
  set Cp : ℝ := max Cρ 0 with hCpdef
  have hS0 : 0 ≤ S := le_max_right _ _
  have hM0 : 0 ≤ M := le_max_right _ _
  have hCp0 : 0 ≤ Cp := le_max_right _ _
  have hgb : ∀ z ∈ acube ℓ, |g z| ≤ S := fun z hz => by
    rw [← Real.norm_eq_abs]
    exact le_trans (hS₀ z hz) (le_max_left _ _)
  have hMb : ∀ z ∈ acube ℓ, ‖fderiv ℝ g z‖ ≤ M := fun z hz =>
    le_trans (by simpa using hM₀ z hz) (le_max_left _ _)
  have hρC : ∀ u : ℝ³, |ρ u| ≤ Cp := fun u => le_trans (hCρ u) (le_max_left _ _)
  have hDil : ∀ (s : ℝ), 0 < s → ∀ (y : ℝ³) (k : Fin 3),
      |fderiv ℝ (chiScale s) y (kcStdBasis k)| ≤ Real.sqrt K / s := fun s hs =>
    abs_fderiv_chiScale_basis_le_sqrt hKb hs
  -- ## 3. the constants of the estimate
  set Dχ : ℝ := chiSup * (Real.sqrt K / (ℓ * d)) + chiSup * (Real.sqrt K / ℓ) with hDχdef
  have hDχ0 : 0 ≤ Dχ := by
    rw [hDχdef]
    exact add_nonneg
      (mul_nonneg (le_of_lt chiSup_pos) (div_nonneg (Real.sqrt_nonneg K) (by positivity)))
      (mul_nonneg (le_of_lt chiSup_pos) (div_nonneg (Real.sqrt_nonneg K) (by positivity)))
  set C₁ : ℝ := chiSup ^ 2 * (S + Cp) with hC₁def
  have hC₁0 : 0 ≤ C₁ := by
    rw [hC₁def]
    exact mul_nonneg (sq_nonneg _) (add_nonneg hS0 hCp0)
  set D : ℝ := chiSup ^ 2 * M + (S + Cp) * Dχ with hDdef
  have hD0 : 0 ≤ D := by
    rw [hDdef]
    exact add_nonneg (mul_nonneg (sq_nonneg _) hM0)
      (mul_nonneg (add_nonneg hS0 hCp0) hDχ0)
  set B : ℝ := (2 * Real.pi) ^ 3
    * (2 * c ^ 2 * (C₁ ^ 2 * ℓ ^ 3) + 2 * (3 * (D ^ 2 * ℓ ^ 3))) with hBdef
  have hB0 : 0 ≤ B := by
    rw [hBdef]
    exact mul_nonneg (by positivity) (add_nonneg (by positivity) (by positivity))
  -- ## 4. the uniform-in-`u` pointwise bound
  have hpoint : ∀ u : ℝ³,
      |Work.BSKinetic.Decomp.bsW (fsKinCoeff c)
        (fun z : ℝ³ => chiB ℓ d u z * (g z - ρ u))| ≤ B := by
    intro u
    have hcont : ContDiff ℝ (⊤ : ENat) (fun z : ℝ³ => chiB ℓ d u z * (g z - ρ u)) :=
      (Work.SmallBoxTBWord.contDiff_chiB hℓ hd u).mul (hg.sub contDiff_const)
    have hcs : HasCompactSupport (fun z : ℝ³ => chiB ℓ d u z * (g z - ρ u)) :=
      (Work.SmallBoxTBWord.hasCompactSupport_chiB hℓ hd u).mul_right
    have hzero : ∀ z : ℝ³, z ∉ acube ℓ → chiB ℓ d u z * (g z - ρ u) = 0 := by
      intro z hz
      have h1 : chiScale ℓ z = 0 := by
        by_contra hc
        exact hz (chiScale_mem_acube hℓ hc)
      simp only [chiB, h1, zero_mul]
    -- sup bound for the state
    have hb : ∀ z : ℝ³, |chiB ℓ d u z * (g z - ρ u)| ≤ C₁ := by
      intro z
      by_cases hz : z ∈ acube ℓ
      · rw [abs_mul, hC₁def]
        refine mul_le_mul (Work.SmallBoxTBWord.abs_chiB_le_chiSup_sq u z) ?_
          (abs_nonneg _) (sq_nonneg _)
        refine le_trans (abs_sub _ _) (add_le_add (hgb z hz) (hρC u))
      · rw [hzero z hz, abs_zero, hC₁def]
        exact mul_nonneg (sq_nonneg _) (add_nonneg hS0 hCp0)
    -- derivative bound for the state
    have hb' : ∀ (k : Fin 3) (z : ℝ³),
        |fderiv ℝ (fun z : ℝ³ => chiB ℓ d u z * (g z - ρ u)) z (kcStdBasis k)| ≤ D := by
      intro k z
      by_cases hz : z ∈ acube ℓ
      · -- inside the box: Leibniz plus the uniform bounds
        have hχd : DifferentiableAt ℝ (fun y : ℝ³ => chiB ℓ d u y) z :=
          ((Work.SmallBoxTBWord.contDiff_chiB hℓ hd u).contDiffAt).differentiableAt (by simp)
        have hWd : DifferentiableAt ℝ (fun y : ℝ³ => g y - ρ u) z :=
          ((hg.sub contDiff_const).contDiffAt).differentiableAt (by simp)
        have hWderiv : fderiv ℝ (fun y : ℝ³ => g y - ρ u) z = fderiv ℝ g z :=
          fderiv_sub_const (ρ u)
        have hχderiv : (fderiv ℝ (fun y : ℝ³ => chiB ℓ d u y) z) (kcStdBasis k)
            = chiScale ℓ z * (fderiv ℝ (chiScale (ℓ * d)) (z - (ℓ * d) • u)
                (kcStdBasis k))
              + chiScale (ℓ * d) (z - (ℓ * d) • u)
                * (fderiv ℝ (chiScale ℓ) z (kcStdBasis k)) :=
          Work.UBBInputs9.C.fderiv_chiB_apply ℓ d (ne_of_gt hℓ) (ne_of_gt hd) u z
            (kcStdBasis k)
        have hleib : (fderiv ℝ (fun y : ℝ³ => chiB ℓ d u y * (g y - ρ u)) z) (kcStdBasis k)
            = chiB ℓ d u z * (fderiv ℝ g z (kcStdBasis k))
              + (g z - ρ u) * (chiScale ℓ z
                  * (fderiv ℝ (chiScale (ℓ * d)) (z - (ℓ * d) • u) (kcStdBasis k))
                + chiScale (ℓ * d) (z - (ℓ * d) • u)
                  * (fderiv ℝ (chiScale ℓ) z (kcStdBasis k))) := by
          rw [show (fun y : ℝ³ => chiB ℓ d u y * (g y - ρ u))
              = (fun y : ℝ³ => chiB ℓ d u y) * (fun y : ℝ³ => g y - ρ u) from rfl,
            fderiv_mul hχd hWd]
          simp only [add_apply, smul_apply, smul_eq_mul, hWderiv, hχderiv]
        rw [hleib, hDdef]
        refine le_trans (abs_add_le _ _) (add_le_add ?_ ?_)
        · -- the `∂g`-term
          rw [abs_mul]
          exact mul_le_mul (Work.SmallBoxTBWord.abs_chiB_le_chiSup_sq u z)
            (by
              calc |fderiv ℝ g z (kcStdBasis k)|
                  = ‖fderiv ℝ g z (kcStdBasis k)‖ := Real.norm_eq_abs _
                _ ≤ ‖fderiv ℝ g z‖ * ‖kcStdBasis k‖ := ContinuousLinearMap.le_opNorm _ _
                _ = ‖fderiv ℝ g z‖ := by
                    rw [show ‖kcStdBasis k‖ = 1 from by simp [kcStdBasis], mul_one]
                _ ≤ M := hMb z hz)
            (abs_nonneg _) (sq_nonneg _)
        · -- the `(g − ρ u)·∂χ`-term
          rw [abs_mul]
          refine mul_le_mul (le_trans (abs_sub _ _) (add_le_add (hgb z hz) (hρC u))) ?_
            (abs_nonneg _) (add_nonneg hS0 hCp0)
          refine le_trans (abs_add_le _ _) ?_
          rw [hDχdef]
          exact add_le_add
            (by rw [abs_mul]
                exact mul_le_mul (abs_chiScale_le_chiSup ℓ z)
                  (hDil (ℓ * d) (by positivity) (z - (ℓ * d) • u) k) (abs_nonneg _)
                  (le_of_lt chiSup_pos))
            (by rw [abs_mul]
                exact mul_le_mul (abs_chiScale_le_chiSup (ℓ * d) (z - (ℓ * d) • u))
                  (hDil ℓ hℓ z k) (abs_nonneg _) (le_of_lt chiSup_pos))
      · -- outside the closed box the state vanishes on a neighbourhood, so its derivative is `0`
        have hev : (fun y : ℝ³ => chiB ℓ d u y * (g y - ρ u))
            =ᶠ[𝓝 z] Function.const ℝ³ (0 : ℝ) := by
          rw [Filter.eventuallyEq_iff_exists_mem]
          obtain ⟨ε, hε, hsub⟩ := Metric.isOpen_iff.mp
            (acube_isClosed ℓ).isOpen_compl z hz
          exact ⟨Metric.ball z ε, Metric.ball_mem_nhds z hε, fun y hy => by
            rw [Function.const_apply]
            exact hzero y (hsub hy)⟩
        have h1 : fderiv ℝ (fun y : ℝ³ => chiB ℓ d u y * (g y - ρ u)) z
            = fderiv ℝ (Function.const ℝ³ (0 : ℝ)) z :=
          Filter.EventuallyEq.fderiv_eq (𝕜 := ℝ) hev
        rw [h1, fderiv_const]
        simpa using hD0
    -- the box-supported a priori estimate for the cutoff kinetic symbol
    have hbs := Work.BSKinetic.bsW_fsKinCoeff_le (ℓ := ℓ) (c := c) hℓ hcont hcs hzero hb hb'
    have hnn : 0 ≤ Work.BSKinetic.Decomp.bsW (fsKinCoeff c)
        (fun z : ℝ³ => chiB ℓ d u z * (g z - ρ u)) := by
      rw [Work.BSKinetic.Decomp.bsW]
      exact integral_nonneg (fun p =>
        mul_nonneg (fsKinCoeff_nonneg c ‖p‖) (sq_nonneg _))
    have hπ : 0 < (2 * Real.pi) ^ 3 := by positivity
    have hmul := mul_le_mul_of_nonneg_left hbs (le_of_lt hπ)
    have hid : (2 * Real.pi) ^ 3
          * (((2 * Real.pi) ^ 3)⁻¹ * Work.BSKinetic.Decomp.bsW (fsKinCoeff c)
              (fun z : ℝ³ => chiB ℓ d u z * (g z - ρ u)))
        = Work.BSKinetic.Decomp.bsW (fsKinCoeff c)
            (fun z : ℝ³ => chiB ℓ d u z * (g z - ρ u)) := by
      rw [← mul_assoc, mul_inv_cancel₀ (ne_of_gt hπ), one_mul]
    rw [hid] at hmul
    rw [hBdef, abs_of_nonneg hnn]
    exact hmul
  -- ## 5. the dominating function and the comparison
  have hfin : (volume : Measure ℝ³) (acube ((1 + d) / d)) ≠ ⊤ :=
    ne_of_lt (acube_lt_top _ (by positivity))
  have hdom : Integrable ((acube ((1 + d) / d)).indicator (fun _ : ℝ³ => B)) volume := by
    rw [integrable_indicator_iff (acube_measurable _)]
    exact integrableOn_const hfin (by simp)
  refine Integrable.mono' hdom hA ?_
  filter_upwards with u
  by_cases hu : u ∈ acube ((1 + d) / d)
  · rw [Set.indicator_of_mem hu, Real.norm_eq_abs]
    exact hpoint u
  · rw [Set.indicator_of_notMem hu]
    have h0 : (fun z : ℝ³ => chiB ℓ d u z * (g z - ρ u)) = 0 :=
      Work.BoseFixB1S.chiB_mul_eq_zero_of_not_mem_acube_u hℓ hd hu g (ρ u)
    rw [h0]
    simp [Work.BSKinetic.Decomp.bsW, Work.BSKinetic.Decomp.bsPsi,
      Submission.BoseGases.kinFT]

end Work.BoseFixB1.Core.MM
