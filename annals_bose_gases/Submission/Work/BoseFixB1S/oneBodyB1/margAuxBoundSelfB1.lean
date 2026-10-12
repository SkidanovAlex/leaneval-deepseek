import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixB1S.corrMarg.support_u
import Submission.Work.BoseFixB1S.oneBodyB1.corrInterface
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB1S.oneBodyB1.margAuxBoundSelfB1`

A self-contained proof of the uniform-in-`u` bound for the windowed state
`χ_{B(u)}·(w − c₀ u)` (`|c₀ u| ≤ C`), used as a fallback for the delegated `margAuxBoundB1`.

The state is supported in the *fixed* box `acube ℓ` and (in the cube) bounded by `chiSup²(S + C)`,
where `S := sup_{acube ℓ}|w|`; its first partials are bounded by
`D := chiSup²·W₁ + (S + C)·(chiSup·(1 + K/(ℓd)²) + chiSup·(1 + K/ℓ²))`,
where `W₁` bounds `|∂_k w|` on the cube and `K` is the uniform window-gradient constant of
`Work.BlockBound4.chiScale_grad_bound` (`Σ_k(∂_k χ_s)² ≤ K/s²`); off the closed cube the state
vanishes on a neighbourhood of every point, so its derivative vanishes there.
`Work.BSKinetic.bsW_fsKinCoeff_le` (weighted Plancherel `[r−c]₊² ≤ 2r² + 2c²` plus the box-supported
`L²`/Dirichlet a priori bounds) then gives a constant bound for `bsW`.
-/

noncomputable section

open MeasureTheory Filter
open scoped Topology

namespace Work.BoseFixB1S.oneBodyB1

local notation "E3" => EuclideanSpace ℝ (Fin 3)

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 800000

/-- The supremum of `|w|` and of the first partials of `w` on the compact box `acube ℓ`. -/
private lemma exists_bounds_on_acubeB1 {ℓ : ℝ} (hℓ : 0 < ℓ) {w : E3 → ℝ}
    (hw : ContDiff ℝ (⊤ : ENat) w) :
    ∃ S W₁ : ℝ, 0 ≤ S ∧ 0 ≤ W₁ ∧
      (∀ z ∈ Submission.BoseGases.acube ℓ, |w z| ≤ S) ∧
      (∀ (k : Fin 3) (z : E3), z ∈ Submission.BoseGases.acube ℓ →
        |fderiv ℝ w z (Submission.BoseGases.kcStdBasis k)| ≤ W₁) := by
  obtain ⟨S₀, hS₀⟩ := (Submission.BoseGases.acube_compact hℓ).exists_bound_of_continuousOn
    hw.continuous.continuousOn
  have hfw : ∀ k : Fin 3, Continuous
      (fun z : E3 => fderiv ℝ w z (Submission.BoseGases.kcStdBasis k)) := fun k =>
    (hw.continuous_fderiv (by simp)).clm_apply continuous_const
  choose b hb using fun k : Fin 3 =>
    (Submission.BoseGases.acube_compact hℓ).exists_bound_of_continuousOn (hfw k).continuousOn
  refine ⟨max S₀ 0, ∑ k : Fin 3, max (b k) 0, le_max_right _ _,
    Finset.sum_nonneg (s := Finset.univ) (fun k _ => le_max_right _ _), ?_, ?_⟩
  · intro z hz
    have h := hS₀ z hz
    rw [Real.norm_eq_abs] at h
    exact le_trans h (le_max_left _ _)
  · intro k z hz
    have h1 : |fderiv ℝ w z (Submission.BoseGases.kcStdBasis k)| ≤ b k := by
      have h := hb k z hz
      rwa [Real.norm_eq_abs] at h
    refine le_trans h1 (le_trans (le_max_left (b k) 0) ?_)
    exact Finset.single_le_sum (s := Finset.univ) (f := fun j : Fin 3 => max (b j) 0)
      (fun j _ => le_max_right _ _) (Finset.mem_univ k)

/-- **Uniform-in-`u` `bsW`-bound for `χ_{B(u)}·(w − c₀ u)`.** -/
theorem margAuxBoundSelfB1 {ℓ d c C : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d) (hC : 0 ≤ C)
    {w : E3 → ℝ} (hw : ContDiff ℝ (⊤ : ENat) w)
    {c₀ : E3 → ℝ} (hc₀ : ∀ u : E3, |c₀ u| ≤ C) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ u : E3,
      |Work.BSKinetic.Decomp.bsW (Submission.BoseGases.fsKinCoeff c)
        (fun z : E3 => Submission.BoseGases.chiB ℓ d u z * (w z - c₀ u))| ≤ B := by
  obtain ⟨S, W₁, hS0, hW10, hS, hW1⟩ := exists_bounds_on_acubeB1 hℓ hw
  obtain ⟨K, hK0, hK⟩ := Work.BlockBound4.chiScale_grad_bound
  have hld : 0 < ℓ * d := mul_pos hℓ hd
  have hχpos : 0 < Submission.BoseGases.chiSup := Submission.BoseGases.chiSup_pos
  -- the elementary partial-derivative bound for the dilates of the bump
  have hDilate : ∀ (s : ℝ), 0 < s → ∀ (y : E3) (k : Fin 3),
      |fderiv ℝ (Submission.BoseGases.chiScale s) y (Submission.BoseGases.kcStdBasis k)|
        ≤ 1 + K / s ^ 2 := by
    intro s hs y k
    have h1 : (fderiv ℝ (Submission.BoseGases.chiScale s) y
          (Submission.BoseGases.kcStdBasis k)) ^ 2 ≤ K / s ^ 2 :=
      le_trans (Finset.single_le_sum (s := Finset.univ)
        (f := fun j : Fin 3 => (fderiv ℝ (Submission.BoseGases.chiScale s) y
          (Submission.BoseGases.kcStdBasis j)) ^ 2)
        (fun j _ => sq_nonneg _) (Finset.mem_univ k)) (hK s hs y)
    have h2 : |fderiv ℝ (Submission.BoseGases.chiScale s) y
        (Submission.BoseGases.kcStdBasis k)| ^ 2 ≤ K / s ^ 2 := by
      rw [sq_abs]; exact h1
    nlinarith [abs_nonneg (fderiv ℝ (Submission.BoseGases.chiScale s) y
      (Submission.BoseGases.kcStdBasis k)), h2]
  -- the constants of the estimate
  set C₁ : ℝ := Submission.BoseGases.chiSup ^ 2 * (S + C) with hC₁
  set D : ℝ := Submission.BoseGases.chiSup ^ 2 * W₁
      + (S + C) * (Submission.BoseGases.chiSup * (1 + K / (ℓ * d) ^ 2)
          + Submission.BoseGases.chiSup * (1 + K / ℓ ^ 2)) with hD
  have hSC : 0 ≤ S + C := add_nonneg hS0 hC
  have hk1 : (0 : ℝ) ≤ 1 + K / (ℓ * d) ^ 2 := by positivity
  have hk2 : (0 : ℝ) ≤ 1 + K / ℓ ^ 2 := by positivity
  have hC₁0 : 0 ≤ C₁ := by
    rw [hC₁]; exact mul_nonneg (sq_nonneg _) hSC
  have hD0 : 0 ≤ D := by
    rw [hD]
    exact add_nonneg (mul_nonneg (sq_nonneg _) hW10)
      (mul_nonneg hSC (add_nonneg (mul_nonneg hχpos.le hk1) (mul_nonneg hχpos.le hk2)))
  have hB0 : 0 ≤ (2 * Real.pi) ^ 3
      * (2 * c ^ 2 * (C₁ ^ 2 * ℓ ^ 3) + 2 * (3 * (D ^ 2 * ℓ ^ 3))) := by
    have h3 : (0 : ℝ) ≤ 2 * c ^ 2 * (C₁ ^ 2 * ℓ ^ 3) := by positivity
    have h4 : (0 : ℝ) ≤ 2 * (3 * (D ^ 2 * ℓ ^ 3)) := by positivity
    exact mul_nonneg (by positivity) (add_nonneg h3 h4)
  refine ⟨(2 * Real.pi) ^ 3 * (2 * c ^ 2 * (C₁ ^ 2 * ℓ ^ 3) + 2 * (3 * (D ^ 2 * ℓ ^ 3))),
    hB0, fun u => ?_⟩
  -- the state
  have hcont : ContDiff ℝ (⊤ : ENat)
      (fun z : E3 => Submission.BoseGases.chiB ℓ d u z * (w z - c₀ u)) :=
    (Work.SmallBoxTBWord.contDiff_chiB hℓ hd u).mul (hw.sub contDiff_const)
  have hcs : HasCompactSupport
      (fun z : E3 => Submission.BoseGases.chiB ℓ d u z * (w z - c₀ u)) :=
    (Work.SmallBoxTBWord.hasCompactSupport_chiB hℓ hd u).mul_right
  have hχeq0 : ∀ z : E3, z ∉ Submission.BoseGases.acube ℓ →
      Submission.BoseGases.chiB ℓ d u z = 0 := by
    intro z hz
    have h1 : Submission.BoseGases.chiScale ℓ z = 0 := by
      by_contra hc
      exact hz (Submission.BoseGases.chiScale_mem_acube hℓ hc)
    simp only [Submission.BoseGases.chiB, h1, zero_mul]
  have hzero : ∀ z : E3, z ∉ Submission.BoseGases.acube ℓ →
      Submission.BoseGases.chiB ℓ d u z * (w z - c₀ u) = 0 := by
    intro z hz
    rw [hχeq0 z hz, zero_mul]
  have hb : ∀ z : E3, |Submission.BoseGases.chiB ℓ d u z * (w z - c₀ u)| ≤ C₁ := by
    intro z
    by_cases hz : z ∈ Submission.BoseGases.acube ℓ
    · rw [abs_mul, hC₁]
      exact mul_le_mul (Work.SmallBoxTBWord.abs_chiB_le_chiSup_sq (ℓ := ℓ) (d := d) u z)
        (le_trans (abs_sub _ _) (add_le_add (hS z hz) (hc₀ u))) (abs_nonneg _) (sq_nonneg _)
    · rw [hzero z hz, abs_zero, hC₁]
      exact mul_nonneg (sq_nonneg _) hSC
  have hb' : ∀ (k : Fin 3) (z : E3),
      |fderiv ℝ (fun z : E3 => Submission.BoseGases.chiB ℓ d u z * (w z - c₀ u)) z
        (Submission.BoseGases.kcStdBasis k)| ≤ D := by
    intro k z
    by_cases hz : z ∈ Submission.BoseGases.acube ℓ
    · -- inside the box: Leibniz rule, with all factors bounded on the box
      have hχd : DifferentiableAt ℝ (fun y : E3 => Submission.BoseGases.chiB ℓ d u y) z :=
        ((Work.SmallBoxTBWord.contDiff_chiB hℓ hd u).contDiffAt).differentiableAt (by simp)
      have hWd : DifferentiableAt ℝ (fun y : E3 => w y - c₀ u) z :=
        ((hw.sub contDiff_const).contDiffAt).differentiableAt (by simp)
      have hWderiv : fderiv ℝ (fun y : E3 => w y - c₀ u) z = fderiv ℝ w z :=
        fderiv_sub_const (f := w) (x := z) (c₀ u)
      have hχderiv : (fderiv ℝ (fun y : E3 => Submission.BoseGases.chiB ℓ d u y) z)
            (Submission.BoseGases.kcStdBasis k)
          = Submission.BoseGases.chiScale ℓ z *
              (fderiv ℝ (Submission.BoseGases.chiScale (ℓ * d)) (z - (ℓ * d) • u)
                (Submission.BoseGases.kcStdBasis k))
            + Submission.BoseGases.chiScale (ℓ * d) (z - (ℓ * d) • u) *
              (fderiv ℝ (Submission.BoseGases.chiScale ℓ) z
                (Submission.BoseGases.kcStdBasis k)) :=
        Work.UBBInputs9.C.fderiv_chiB_apply ℓ d (ne_of_gt hℓ) (ne_of_gt hd) u z
          (Submission.BoseGases.kcStdBasis k)
      have hleib : (fderiv ℝ
            (fun y : E3 => Submission.BoseGases.chiB ℓ d u y * (w y - c₀ u)) z)
            (Submission.BoseGases.kcStdBasis k)
          = Submission.BoseGases.chiB ℓ d u z
              * (fderiv ℝ w z (Submission.BoseGases.kcStdBasis k))
            + (w z - c₀ u) * (Submission.BoseGases.chiScale ℓ z *
                (fderiv ℝ (Submission.BoseGases.chiScale (ℓ * d)) (z - (ℓ * d) • u)
                  (Submission.BoseGases.kcStdBasis k))
              + Submission.BoseGases.chiScale (ℓ * d) (z - (ℓ * d) • u) *
                (fderiv ℝ (Submission.BoseGases.chiScale ℓ) z
                  (Submission.BoseGases.kcStdBasis k))) := by
        rw [show (fun y : E3 => Submission.BoseGases.chiB ℓ d u y * (w y - c₀ u))
            = (fun y : E3 => Submission.BoseGases.chiB ℓ d u y) *
              (fun y : E3 => w y - c₀ u) from rfl]
        rw [fderiv_mul hχd hWd]
        simp only [add_apply, smul_apply, smul_eq_mul, hWderiv, hχderiv]
      rw [hleib, hD]
      have hχz : |Submission.BoseGases.chiB ℓ d u z| ≤ Submission.BoseGases.chiSup ^ 2 :=
        Work.SmallBoxTBWord.abs_chiB_le_chiSup_sq (ℓ := ℓ) (d := d) u z
      have hWz : |w z - c₀ u| ≤ S + C :=
        le_trans (abs_sub _ _) (add_le_add (hS z hz) (hc₀ u))
      have hgw : |fderiv ℝ w z (Submission.BoseGases.kcStdBasis k)| ≤ W₁ := hW1 k z hz
      have hd1 : |fderiv ℝ (Submission.BoseGases.chiScale (ℓ * d)) (z - (ℓ * d) • u)
          (Submission.BoseGases.kcStdBasis k)| ≤ 1 + K / (ℓ * d) ^ 2 :=
        hDilate (ℓ * d) hld (z - (ℓ * d) • u) k
      have hd2 : |fderiv ℝ (Submission.BoseGases.chiScale ℓ) z
          (Submission.BoseGases.kcStdBasis k)| ≤ 1 + K / ℓ ^ 2 :=
        hDilate ℓ hℓ z k
      have hsplit1 : |Submission.BoseGases.chiB ℓ d u z
          * (fderiv ℝ w z (Submission.BoseGases.kcStdBasis k))| ≤
          Submission.BoseGases.chiSup ^ 2 * W₁ := by
        rw [abs_mul]
        exact mul_le_mul hχz hgw (abs_nonneg _) (sq_nonneg _)
      have hsplit2 : |(w z - c₀ u) * (Submission.BoseGases.chiScale ℓ z *
                (fderiv ℝ (Submission.BoseGases.chiScale (ℓ * d)) (z - (ℓ * d) • u)
                  (Submission.BoseGases.kcStdBasis k))
              + Submission.BoseGases.chiScale (ℓ * d) (z - (ℓ * d) • u) *
                (fderiv ℝ (Submission.BoseGases.chiScale ℓ) z
                  (Submission.BoseGases.kcStdBasis k)))| ≤
          (S + C) * (Submission.BoseGases.chiSup * (1 + K / (ℓ * d) ^ 2)
            + Submission.BoseGases.chiSup * (1 + K / ℓ ^ 2)) := by
        rw [abs_mul]
        refine mul_le_mul hWz ?_ (abs_nonneg _) hSC
        refine le_trans (abs_add_le _ _) ?_
        refine add_le_add ?_ ?_
        · rw [abs_mul]
          exact mul_le_mul
            (Submission.BoseGases.abs_chiScale_le_chiSup ℓ z) hd1 (abs_nonneg _) hχpos.le
        · rw [abs_mul]
          exact mul_le_mul
            (Submission.BoseGases.abs_chiScale_le_chiSup (ℓ * d) _) hd2 (abs_nonneg _) hχpos.le
      exact le_trans (abs_add_le _ _) (add_le_add hsplit1 hsplit2)
    · -- outside the closed box the state vanishes on a neighbourhood, so its derivative is zero
      have hev : (fun y : E3 => Submission.BoseGases.chiB ℓ d u y * (w y - c₀ u))
          =ᶠ[𝓝 z] Function.const E3 (0 : ℝ) := by
        rw [Filter.eventuallyEq_iff_exists_mem]
        have hopen : IsOpen (Submission.BoseGases.acube ℓ)ᶜ :=
          (Submission.BoseGases.acube_isClosed ℓ).isOpen_compl
        obtain ⟨ε, hε, hsub⟩ := Metric.isOpen_iff.mp hopen z hz
        exact ⟨Metric.ball z ε, Metric.ball_mem_nhds z hε, fun y hy => by
          rw [Function.const_apply]
          exact hzero y (hsub hy)⟩
      have h1 : fderiv ℝ (fun y : E3 => Submission.BoseGases.chiB ℓ d u y * (w y - c₀ u)) z
          = fderiv ℝ (Function.const E3 (0 : ℝ)) z :=
        Filter.EventuallyEq.fderiv_eq (𝕜 := ℝ) hev
      rw [h1, fderiv_const]
      simpa using hD0
  -- the a priori bound for the cutoff kinetic symbol
  have hfin := Work.BSKinetic.bsW_fsKinCoeff_le (ℓ := ℓ) (c := c) hℓ hcont hcs hzero hb hb'
  have hnn : 0 ≤ Work.BSKinetic.Decomp.bsW (Submission.BoseGases.fsKinCoeff c)
      (fun z : E3 => Submission.BoseGases.chiB ℓ d u z * (w z - c₀ u)) := by
    rw [Work.BSKinetic.Decomp.bsW]
    exact integral_nonneg (fun p =>
      mul_nonneg (Submission.BoseGases.fsKinCoeff_nonneg c ‖p‖) (sq_nonneg _))
  have hπ : 0 < (2 * Real.pi) ^ 3 := by positivity
  have hmul := mul_le_mul_of_nonneg_left hfin (le_of_lt hπ)
  have hid : (2 * Real.pi) ^ 3 * (((2 * Real.pi) ^ 3)⁻¹
      * Work.BSKinetic.Decomp.bsW (Submission.BoseGases.fsKinCoeff c)
          (fun z : E3 => Submission.BoseGases.chiB ℓ d u z * (w z - c₀ u)))
      = Work.BSKinetic.Decomp.bsW (Submission.BoseGases.fsKinCoeff c)
          (fun z : E3 => Submission.BoseGases.chiB ℓ d u z * (w z - c₀ u)) := by
    rw [← mul_assoc, mul_inv_cancel₀ (ne_of_gt hπ), one_mul]
  rw [hid] at hmul
  rw [abs_of_nonneg hnn]
  exact hmul

end Work.BoseFixB1S.oneBodyB1
