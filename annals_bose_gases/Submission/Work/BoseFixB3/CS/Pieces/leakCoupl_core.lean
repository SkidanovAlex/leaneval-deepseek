import Mathlib.Topology.UniformSpace.Uniformizable
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Submission.Work.BoseFixB3.CS.Pieces.bumpProd_bound
import Submission.Work.BoseFixB3.CS.Pieces.chi_lipschitz
import Submission.Work.BoseFixB3.CS.Pieces.highpass_content_small
import Submission.Work.BoseFixB3.CS.Pieces.integral_leakFn_mul_eq
import Submission.Work.BoseFixB3.CS.Pieces.leakCoupl_swap
import Submission.Work.BoseFixB3.CS.Pieces.leakFn_abs_le
import Submission.Work.BoseFixB3.Conv.chi_highpass_decay
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB3.CS.Pieces.leakCoupl_core`

The **core leakage coupling bound** of the `CS` step of the `B3` chapter: for every cut-off
`fc`, every `κ, ℓ > 0`, every `R > 0` with `R ≤ ℓ/8` and every integrable `F` vanishing
outside the ball of radius `R`,

    |∫_Λ leakFn fc κ ℓ y · (∫_Λ χ_Λ(x) F(x−y) χ_Λ(y) dx) dy|
      ≤ C·((ℓκ)^{-40} + R/ℓ)·ℓ³·∫‖F‖,

with `Λ = acube ℓ`, `χ_Λ = chiU ℓ 0` and `leakFn = 1 − f_L(√−Δ)1`.

## Route

1. `leakCoupl_swap` (delegated) removes the inner `x`-integral by the substitution
   `x = y + z` and Fubini, leaving the integral of `F` against the *weight*
   `J(z) = ∫_Λ leakFn(y)χ_Λ(y)χ_Λ(y+z) dy`;
2. `leakWeight_abs_le` (this file) bounds `|J(z)|` uniformly in `z` by the high-pass
   content of the bump product `χ_Λ·χ_Λ(·+z)`: the self-adjointness identity
   `integral_leakFn_mul_eq` identifies `J(z)` with `∫_Λ(ψ_z − f_L ψ_z)`, and
   `highpass_content_small` bounds the latter by `C·M·ℓ³/(ℓκ)^{40}` where `M` controls the
   derivatives of `ψ_z` up to order `40` (`bumpProd_bound`, delegated);
3. `fubini`-free conclusion: `|∫ F·J| ≤ ∫‖F‖·sup|J|`.

Note: the high-pass content of the bump product is super-polynomially small *uniformly in
`z`*, so the `R/ℓ` summand of the statement is not needed; it is dominated by the
`(ℓκ)^{-40}` term (using `R ≤ ℓ/8 < ℓ`).
-/

noncomputable section

open MeasureTheory Filter Metric
open scoped Real Topology BigOperators ENNReal

namespace Work.BoseFixB3.CS.Pieces

local notation "E3" => EuclideanSpace ℝ (Fin 3)

set_option maxHeartbeats 1600000

/-! ## 1. The corpus bump `χ` at scale `ℓ` -/

/-- The base bump vanishes on the complement of the open ball of radius `1/2`. -/
lemma chiBase_eq_zero_of_half_le_norm {x : E3} (hx : 1 / 2 ≤ ‖x‖) :
    Submission.BoseGases.chiBase x = 0 := by
  have h : Submission.BoseGases.chiBump.rOut ≤ dist x (0 : E3) := by
    simpa [Submission.BoseGases.chiBump, dist_eq_norm] using hx
  exact Submission.BoseGases.chiBump.zero_of_le_dist h

/-- `χ` vanishes on the complement of the open ball of radius `1/2`. -/
lemma chi_eq_zero_of_half_le_norm {x : E3} (hx : 1 / 2 ≤ ‖x‖) :
    Submission.BoseGases.chi x = 0 := by
  rw [Submission.BoseGases.chi, chiBase_eq_zero_of_half_le_norm hx, zero_div]

/-- `chiU ℓ 0 y = χ(ℓ⁻¹ • y)`. -/
lemma chiU_zero_apply (ℓ : ℝ) (y : E3) :
    Submission.BoseGases.chiU ℓ 0 y = Submission.BoseGases.chi ((ℓ⁻¹) • y) := by
  simp [Submission.BoseGases.chiU]

/-- `chiU ℓ 0` vanishes off the ball of radius `ℓ/2`. -/
lemma chiU_eq_zero_of_half_le_norm {ℓ : ℝ} (hℓ : 0 < ℓ) {y : E3} (hy : ℓ / 2 ≤ ‖y‖) :
    Submission.BoseGases.chiU ℓ 0 y = 0 := by
  rw [chiU_zero_apply]
  refine chi_eq_zero_of_half_le_norm ?_
  rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hℓ.le)]
  have h2 : ℓ⁻¹ * (ℓ / 2) = 1 / 2 := by field_simp
  rw [← h2]
  exact mul_le_mul_of_nonneg_left hy (inv_nonneg.mpr hℓ.le)

/-- A point outside the centred cube `acube ℓ` is at distance more than `ℓ/2` from the
origin. -/
lemma half_lt_norm_of_notMem_acube {ℓ : ℝ} {y : E3}
    (hy : y ∉ Submission.BoseGases.acube ℓ) : ℓ / 2 < ‖y‖ := by
  rw [Submission.BoseGases.mem_acube_iff] at hy
  obtain ⟨m, hm⟩ := not_forall.mp hy
  rw [Set.mem_Icc] at hm
  have h1 : ℓ / 2 < |y m| := by
    by_contra hcon
    rw [not_lt] at hcon
    rw [abs_le] at hcon
    exact hm ⟨by linarith [hcon.1], hcon.2⟩
  exact lt_of_lt_of_le h1 (Submission.BoseGases.abs_coord_le_norm y m)

/-- `y ↦ chiU ℓ 0 y` is `C^∞`. -/
lemma contDiff_chiU (ℓ : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (fun y : E3 => Submission.BoseGases.chiU ℓ 0 y) := by
  have hchi : ContDiff ℝ (⊤ : ℕ∞) Submission.BoseGases.chi :=
    Submission.BoseGases.chi_contDiff
  have hlin : ContDiff ℝ (⊤ : ℕ∞) (fun y : E3 => (ℓ⁻¹ : ℝ) • y) :=
    (contDiff_id (𝕜 := ℝ) (n := (⊤ : ℕ∞))).const_smul (ℓ⁻¹)
  have hcomp : ContDiff ℝ (⊤ : ℕ∞)
      (Submission.BoseGases.chi ∘ fun y : E3 => (ℓ⁻¹ : ℝ) • y) := hchi.comp hlin
  rw [show (fun y : E3 => Submission.BoseGases.chiU ℓ 0 y)
      = Submission.BoseGases.chi ∘ fun y : E3 => (ℓ⁻¹ : ℝ) • y from by
    funext y
    simp [Submission.BoseGases.chiU]]
  exact hcomp

/-- `y ↦ chiU ℓ 0 (y + z)` is `C^∞`. -/
lemma contDiff_chiU_shift (ℓ : ℝ) (z : E3) :
    ContDiff ℝ (⊤ : ℕ∞) (fun y : E3 => Submission.BoseGases.chiU ℓ 0 (y + z)) := by
  have hchi : ContDiff ℝ (⊤ : ℕ∞) Submission.BoseGases.chi :=
    Submission.BoseGases.chi_contDiff
  have h1 : ContDiff ℝ (⊤ : ℕ∞) (fun y : E3 => y + z) :=
    (contDiff_id (𝕜 := ℝ) (n := (⊤ : ℕ∞))).add contDiff_const
  have hlin : ContDiff ℝ (⊤ : ℕ∞) (fun y : E3 => (ℓ⁻¹ : ℝ) • (y + z)) :=
    h1.const_smul (ℓ⁻¹)
  have hcomp : ContDiff ℝ (⊤ : ℕ∞)
      (Submission.BoseGases.chi ∘ fun y : E3 => (ℓ⁻¹ : ℝ) • (y + z)) := hchi.comp hlin
  rw [show (fun y : E3 => Submission.BoseGases.chiU ℓ 0 (y + z))
      = Submission.BoseGases.chi ∘ fun y : E3 => (ℓ⁻¹ : ℝ) • (y + z) from by
    funext y
    simp [Submission.BoseGases.chiU]]
  exact hcomp

/-! ## 2. The leakage weight is uniformly small -/

/-- **The leakage weight bound.**  For a cut-off `fc`, `κ, ℓ > 0`, an exponent bound `M` for
the bump product `ψ_z = χ_Λ·χ_Λ(·+z)` and any pointwise bound `B` for `leakFn`,

    |∫_Λ leakFn(y)·χ_Λ(y)·χ_Λ(y+z) dy| ≤ C·M·ℓ³/(ℓκ)^{40}    for every `z`,

where `C` is the constant of the high-pass bound `hhp` (the conclusion of
`highpass_content_small`). -/
lemma leakWeight_abs_le (C : ℝ)
    (hhp : ∀ (fc : Work.BoseBoxFix.LowCut) (κ ℓ : ℝ), 0 < κ → 0 < ℓ →
      ∀ (ψ : E3 → ℝ), ContDiff ℝ (⊤ : ℕ∞) ψ →
        (∀ y : E3, ℓ / 2 ≤ ‖y‖ → ψ y = 0) →
        ∀ M : ℝ, 0 ≤ M → (∀ y : E3, |ψ y| ≤ M) →
          (∀ (j : ℕ), j ≤ 40 → ∀ y : E3, ‖iteratedFDeriv ℝ j ψ y‖ ≤ M / ℓ ^ j) →
          |∫ y in Submission.BoseGases.acube ℓ,
              (ψ y - Work.BoseBoxFix.lowMult fc κ ℓ ψ y)|
            ≤ C * M * ℓ ^ 3 / (ℓ * κ) ^ 40)
    (M : ℝ) (hM : 0 ≤ M)
    (hder : ∀ (z : E3) (ℓ : ℝ), 0 < ℓ →
      (∀ y : E3,
        |Submission.BoseGases.chiU ℓ 0 y * Submission.BoseGases.chiU ℓ 0 (y + z)| ≤ M) ∧
      (∀ (j : ℕ), j ≤ 40 → ∀ y : E3,
        ‖iteratedFDeriv ℝ j (fun y : E3 =>
          Submission.BoseGases.chiU ℓ 0 y * Submission.BoseGases.chiU ℓ 0 (y + z)) y‖
          ≤ M / ℓ ^ j))
    (fc : Work.BoseBoxFix.LowCut) {κ ℓ B : ℝ} (hκ : 0 < κ) (hℓ : 0 < ℓ)
    (hB : ∀ y : E3, |Work.BoseFixB3.CS.leakFn fc κ ℓ y| ≤ B) (z : E3) :
    |∫ y in Submission.BoseGases.acube ℓ,
        Work.BoseFixB3.CS.leakFn fc κ ℓ y * Submission.BoseGases.chiU ℓ 0 y *
          Submission.BoseGases.chiU ℓ 0 (y + z)|
      ≤ C * M * ℓ ^ 3 / (ℓ * κ) ^ 40 := by
  classical
  have hℓ0 : (0 : ℝ) ≤ ℓ := hℓ.le
  set ψ : E3 → ℝ :=
    fun y => Submission.BoseGases.chiU ℓ 0 y * Submission.BoseGases.chiU ℓ 0 (y + z) with hψ
  have hψsupp : ∀ y : E3, ℓ / 2 ≤ ‖y‖ → ψ y = 0 := by
    intro y hy
    rw [hψ]
    simp [chiU_eq_zero_of_half_le_norm hℓ hy]
  have hψcd : ContDiff ℝ (⊤ : ℕ∞) ψ := by
    rw [hψ]
    exact (contDiff_chiU ℓ).mul (contDiff_chiU_shift ℓ z)
  have hψcont : Continuous ψ := hψcd.continuous
  have hψcs : HasCompactSupport ψ :=
    HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall (0 : E3) (ℓ / 2))
      (fun y hy => by
        rw [Metric.mem_closedBall, dist_eq_norm, sub_zero]
        exact le_of_not_gt (fun hlt => hy (hψsupp y hlt.le)))
  have hψint : Integrable ψ := hψcont.integrable_of_hasCompactSupport hψcs
  have hψtsupp : tsupport ψ ⊆ Submission.BoseGases.acube ℓ := by
    have h1 : tsupport ψ ⊆ Metric.closedBall (0 : E3) (ℓ / 2) :=
      closure_minimal (fun y hy => by
        rw [Metric.mem_closedBall, dist_eq_norm, sub_zero]
        exact le_of_not_gt (fun hlt => hy (hψsupp y hlt.le))) Metric.isClosed_closedBall
    intro y hy
    have hy' := h1 hy
    rw [Metric.mem_closedBall, dist_eq_norm, sub_zero] at hy'
    exact Submission.BoseGases.mem_acube_of_norm_le hℓ0 hy'
  have hψbd : ∀ y : E3, |ψ y| ≤ M := by
    intro y
    rw [hψ]
    exact (hder z ℓ hℓ).1 y
  have hψder : ∀ (j : ℕ), j ≤ 40 → ∀ y : E3, ‖iteratedFDeriv ℝ j ψ y‖ ≤ M / ℓ ^ j := by
    intro j hj y
    rw [hψ]
    exact (hder z ℓ hℓ).2 j hj y
  -- integrability of `leakFn · ψ`
  have hBmax : 0 ≤ max B 0 := le_max_right _ _
  have hBb : ∀ y : E3, |Work.BoseFixB3.CS.leakFn fc κ ℓ y| ≤ max B 0 :=
    fun y => le_trans (hB y) (le_max_left _ _)
  have hΛtop : (volume : Measure E3) (Submission.BoseGases.acube ℓ) < ⊤ :=
    Submission.BoseGases.acube_lt_top ℓ hℓ0
  have hdom : Integrable (fun y : E3 => max B 0 * M *
      (Submission.BoseGases.acube ℓ).indicator (fun _ : E3 => (1 : ℝ)) y) := by
    have h1 : Integrable (fun y : E3 =>
        (Submission.BoseGases.acube ℓ).indicator (fun _ : E3 => (1 : ℝ)) y) :=
      MeasureTheory.memLp_one_iff_integrable.mp
        (MeasureTheory.memLp_indicator_const (μ := (volume : Measure E3)) 1
          (Submission.BoseGases.acube_measurable ℓ) (1 : ℝ) (Or.inr hΛtop.ne))
    exact h1.const_mul (max B 0 * M)
  have hpt : ∀ y : E3, ‖Work.BoseFixB3.CS.leakFn fc κ ℓ y * ψ y‖
      ≤ max B 0 * M *
          (Submission.BoseGases.acube ℓ).indicator (fun _ : E3 => (1 : ℝ)) y := by
    intro y
    by_cases hy : y ∈ Submission.BoseGases.acube ℓ
    · rw [Set.indicator_of_mem hy, mul_one, norm_mul, Real.norm_eq_abs]
      exact mul_le_mul (hBb y) (hψbd y) (abs_nonneg _) hBmax
    · rw [Set.indicator_of_notMem hy]
      have h0 : ψ y = 0 := hψsupp y (le_of_lt (half_lt_norm_of_notMem_acube hy))
      rw [h0]
      simp
  have hmeas : AEStronglyMeasurable
      (fun y : E3 => Work.BoseFixB3.CS.leakFn fc κ ℓ y * ψ y) (volume : Measure E3) := by
    have hL : StronglyMeasurable (fun y : E3 => Work.BoseFixB3.CS.leakFn fc κ ℓ y) := by
      have h1 : StronglyMeasurable
          (fun y : E3 => Work.BoseBoxFix.lowMult fc κ ℓ Work.BoseFixB3.CS.oneFn y) :=
        Work.BoseFixB3.Conv.stronglyMeasurable_lowMult
          (show Measurable (fun _ : E3 => (1 : ℝ)) from measurable_const)
      have h2 : StronglyMeasurable (fun y : E3 =>
          (1 : ℝ) - Work.BoseBoxFix.lowMult fc κ ℓ Work.BoseFixB3.CS.oneFn y) :=
        stronglyMeasurable_const.sub h1
      have heq : (fun y : E3 => Work.BoseFixB3.CS.leakFn fc κ ℓ y) = fun y : E3 =>
          (1 : ℝ) - Work.BoseBoxFix.lowMult fc κ ℓ Work.BoseFixB3.CS.oneFn y := by
        funext y
        unfold Work.BoseFixB3.CS.leakFn
        rfl
      rw [heq]
      exact h2
    exact (hL.mul hψcont.stronglyMeasurable).aestronglyMeasurable
  have hInt : Integrable (fun y : E3 => Work.BoseFixB3.CS.leakFn fc κ ℓ y * ψ y) :=
    Integrable.mono' hdom hmeas (Eventually.of_forall hpt)
  -- the self-adjointness identity and the high-pass content
  have hid : ∫ y in Submission.BoseGases.acube ℓ, Work.BoseFixB3.CS.leakFn fc κ ℓ y * ψ y
      = ∫ y in Submission.BoseGases.acube ℓ,
          (ψ y - Work.BoseBoxFix.lowMult fc κ ℓ ψ y) :=
    integral_leakFn_mul_eq (fc := fc) hκ hℓ hψint hψtsupp hInt
  have hcon : (∫ y in Submission.BoseGases.acube ℓ,
        Work.BoseFixB3.CS.leakFn fc κ ℓ y * Submission.BoseGases.chiU ℓ 0 y *
          Submission.BoseGases.chiU ℓ 0 (y + z))
      = ∫ y in Submission.BoseGases.acube ℓ, Work.BoseFixB3.CS.leakFn fc κ ℓ y * ψ y := by
    apply integral_congr_ae
    filter_upwards with y
    rw [hψ]
    ring
  rw [hcon, hid]
  exact hhp fc κ ℓ hκ hℓ ψ hψcd hψsupp M hM hψbd hψder

/-! ## 3. The assembly -/

/-- **The core leakage coupling bound**, assembled from the Fubini identity `hswap` (see
`leakCoupl_swap`), the pointwise bounds `hbd` for `leakFn` (see `leakFn_abs_le`) and the
derivative bounds `hbump` for the bump product (see `bumpProd_bound`). -/
lemma leakCoupl_of_swaps
    (hbump : ∃ M : ℝ, 0 ≤ M ∧
      ∀ (z : E3) (ℓ : ℝ), 0 < ℓ →
        (∀ y : E3,
          |Submission.BoseGases.chiU ℓ 0 y * Submission.BoseGases.chiU ℓ 0 (y + z)| ≤ M) ∧
        (∀ (j : ℕ), j ≤ 40 → ∀ y : E3,
          ‖iteratedFDeriv ℝ j (fun y : E3 =>
            Submission.BoseGases.chiU ℓ 0 y * Submission.BoseGases.chiU ℓ 0 (y + z)) y‖
            ≤ M / ℓ ^ j))
    (hswap : ∀ (fc : Work.BoseBoxFix.LowCut) (κ ℓ B : ℝ), 0 < κ → 0 < ℓ →
      (∀ y : E3, |Work.BoseFixB3.CS.leakFn fc κ ℓ y| ≤ B) →
      ∀ (F : E3 → ℝ), MeasureTheory.Integrable F →
        (∫ y in Submission.BoseGases.acube ℓ,
            Work.BoseFixB3.CS.leakFn fc κ ℓ y *
              (∫ x in Submission.BoseGases.acube ℓ,
                Submission.BoseGases.chiU ℓ 0 x * F (x - y) * Submission.BoseGases.chiU ℓ 0 y))
          = ∫ z : E3, F z *
              (∫ y in Submission.BoseGases.acube ℓ,
                Work.BoseFixB3.CS.leakFn fc κ ℓ y * Submission.BoseGases.chiU ℓ 0 y *
                  Submission.BoseGases.chiU ℓ 0 (y + z)))
    (hbd : ∀ (fc : Work.BoseBoxFix.LowCut) (κ ℓ : ℝ), 0 < κ → 0 < ℓ → ∀ y : E3,
      |Work.BoseFixB3.CS.leakFn fc κ ℓ y|
        ≤ 1 + ((2 * Real.pi) ^ 3)⁻¹ * ℓ ^ 3 *
            (MeasureTheory.volume (Metric.closedBall (0 : E3) (2 * κ))).toReal) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (fc : Work.BoseBoxFix.LowCut) (κ ℓ R : ℝ), 0 < κ → 0 < ℓ → 0 < R → R ≤ ℓ / 8 →
        ∀ (F : E3 → ℝ), MeasureTheory.Integrable F →
          (∀ z : E3, R ≤ ‖z‖ → F z = 0) →
          |∫ y in Submission.BoseGases.acube ℓ, Work.BoseFixB3.CS.leakFn fc κ ℓ y *
              (∫ x in Submission.BoseGases.acube ℓ,
                Submission.BoseGases.chiU ℓ 0 x * F (x - y) * Submission.BoseGases.chiU ℓ 0 y)|
            ≤ C * ((ℓ * κ) ^ (-(40 : ℝ)) + R / ℓ) * ℓ ^ 3
                * ∫ z : E3, ‖F z‖ := by
  obtain ⟨C_hp, hC_hp_nn, hhp⟩ := highpass_content_small
  obtain ⟨M, hM_nn, hder⟩ := hbump
  refine ⟨C_hp * M, mul_nonneg hC_hp_nn hM_nn, ?_⟩
  intro fc κ ℓ R hκ hℓ hR hRℓ F hF hFsupp
  set B : ℝ := 1 + ((2 * Real.pi) ^ 3)⁻¹ * ℓ ^ 3 *
      (MeasureTheory.volume (Metric.closedBall (0 : E3) (2 * κ))).toReal with hBdef
  have hB : ∀ y : E3, |Work.BoseFixB3.CS.leakFn fc κ ℓ y| ≤ B := fun y =>
    hbd fc κ ℓ hκ hℓ y
  rw [hswap fc κ ℓ B hκ hℓ hB F hF]
  have hJ : ∀ z : E3,
      |∫ y in Submission.BoseGases.acube ℓ,
        Work.BoseFixB3.CS.leakFn fc κ ℓ y * Submission.BoseGases.chiU ℓ 0 y *
          Submission.BoseGases.chiU ℓ 0 (y + z)|
      ≤ C_hp * M * ℓ ^ 3 / (ℓ * κ) ^ 40 :=
    fun z => leakWeight_abs_le C_hp hhp M hM_nn hder fc hκ hℓ hB z
  have hKnn : 0 ≤ C_hp * M * ℓ ^ 3 / (ℓ * κ) ^ 40 := by positivity
  have hstep : |∫ z : E3, F z * (∫ y in Submission.BoseGases.acube ℓ,
        Work.BoseFixB3.CS.leakFn fc κ ℓ y * Submission.BoseGases.chiU ℓ 0 y *
          Submission.BoseGases.chiU ℓ 0 (y + z))|
      ≤ (C_hp * M * ℓ ^ 3 / (ℓ * κ) ^ 40) * ∫ z : E3, ‖F z‖ := by
    calc |∫ z : E3, F z * (∫ y in Submission.BoseGases.acube ℓ,
          Work.BoseFixB3.CS.leakFn fc κ ℓ y * Submission.BoseGases.chiU ℓ 0 y *
            Submission.BoseGases.chiU ℓ 0 (y + z))|
        = ‖∫ z : E3, F z * (∫ y in Submission.BoseGases.acube ℓ,
            Work.BoseFixB3.CS.leakFn fc κ ℓ y * Submission.BoseGases.chiU ℓ 0 y *
              Submission.BoseGases.chiU ℓ 0 (y + z))‖ := by rw [Real.norm_eq_abs]
      _ ≤ ∫ z : E3, ‖F z * (∫ y in Submission.BoseGases.acube ℓ,
            Work.BoseFixB3.CS.leakFn fc κ ℓ y * Submission.BoseGases.chiU ℓ 0 y *
              Submission.BoseGases.chiU ℓ 0 (y + z))‖ :=
          norm_integral_le_integral_norm _
      _ = ∫ z : E3, ‖F z‖ *
            |∫ y in Submission.BoseGases.acube ℓ,
              Work.BoseFixB3.CS.leakFn fc κ ℓ y * Submission.BoseGases.chiU ℓ 0 y *
                Submission.BoseGases.chiU ℓ 0 (y + z)| := by
          apply integral_congr_ae
          filter_upwards with z
          simp only [norm_mul, Real.norm_eq_abs]
      _ ≤ ∫ z : E3, ‖F z‖ * (C_hp * M * ℓ ^ 3 / (ℓ * κ) ^ 40) := by
          refine integral_mono_of_nonneg (Eventually.of_forall fun z => by positivity) ?_
            (Eventually.of_forall fun z => ?_)
          · simpa [mul_comm] using (hF.norm).const_mul (C_hp * M * ℓ ^ 3 / (ℓ * κ) ^ 40)
          · exact mul_le_mul_of_nonneg_left (hJ z) (norm_nonneg _)
      _ = (C_hp * M * ℓ ^ 3 / (ℓ * κ) ^ 40) * ∫ z : E3, ‖F z‖ := by
          rw [MeasureTheory.integral_mul_const]
          ring
  -- arithmetic: `ℓ³/(ℓκ)⁴⁰ = (ℓκ)^{-40}ℓ³ ≤ ((ℓκ)^{-40} + R/ℓ)ℓ³`
  have hAeq : (ℓ * κ) ^ (-(40 : ℝ)) = 1 / (ℓ * κ) ^ 40 := by
    rw [show (-(40 : ℝ)) = -(40 : ℕ) by norm_num, Real.rpow_neg_natCast, zpow_neg,
      zpow_natCast, inv_eq_one_div]
  have hKle : C_hp * M * ℓ ^ 3 / (ℓ * κ) ^ 40
      ≤ C_hp * M * ((ℓ * κ) ^ (-(40 : ℝ)) + R / ℓ) * ℓ ^ 3 := by
    rw [hAeq]
    have h1 : 0 ≤ C_hp * M := mul_nonneg hC_hp_nn hM_nn
    have h2 : 0 ≤ ℓ ^ 3 := by positivity
    have h3 : 0 ≤ R / ℓ := by positivity
    calc C_hp * M * ℓ ^ 3 / (ℓ * κ) ^ 40
        = C_hp * M * ℓ ^ 3 * (1 / (ℓ * κ) ^ 40) := by ring
      _ ≤ C_hp * M * ℓ ^ 3 * (1 / (ℓ * κ) ^ 40 + R / ℓ) :=
          mul_le_mul_of_nonneg_left (le_add_of_nonneg_right h3) (mul_nonneg h1 h2)
      _ = C_hp * M * (1 / (ℓ * κ) ^ 40 + R / ℓ) * ℓ ^ 3 := by ring
  have hI : 0 ≤ ∫ z : E3, ‖F z‖ := integral_nonneg fun z => norm_nonneg _
  calc |∫ z : E3, F z * (∫ y in Submission.BoseGases.acube ℓ,
        Work.BoseFixB3.CS.leakFn fc κ ℓ y * Submission.BoseGases.chiU ℓ 0 y *
          Submission.BoseGases.chiU ℓ 0 (y + z))|
      ≤ (C_hp * M * ℓ ^ 3 / (ℓ * κ) ^ 40) * ∫ z : E3, ‖F z‖ := hstep
    _ ≤ C_hp * M * ((ℓ * κ) ^ (-(40 : ℝ)) + R / ℓ) * ℓ ^ 3 * ∫ z : E3, ‖F z‖ :=
        mul_le_mul_of_nonneg_right hKle hI

/-- The pointwise bound on `leakFn` in the shape of the `hbd` hypothesis of
`leakCoupl_of_swaps` (from `leakFn_abs_le`). -/
lemma leakFn_pointwise_bound (fc : Work.BoseBoxFix.LowCut) (κ ℓ : ℝ) (hκ : 0 < κ) (hℓ : 0 < ℓ) :
    ∀ y : E3, |Work.BoseFixB3.CS.leakFn fc κ ℓ y|
      ≤ 1 + ((2 * Real.pi) ^ 3)⁻¹ * ℓ ^ 3 *
          (MeasureTheory.volume (Metric.closedBall (0 : E3) (2 * κ))).toReal :=
  fun y => leakFn_abs_le (κ := κ) (ℓ := ℓ) fc hκ hℓ y

/-- **The leakage coupling core bound** (the requested statement). -/
theorem leakCoupl_core :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (fc : Work.BoseBoxFix.LowCut) (κ ℓ R : ℝ), 0 < κ → 0 < ℓ → 0 < R → R ≤ ℓ / 8 →
        ∀ (F : EuclideanSpace ℝ (Fin 3) → ℝ), MeasureTheory.Integrable F →
          (∀ z : EuclideanSpace ℝ (Fin 3), R ≤ ‖z‖ → F z = 0) →
          |∫ y in Submission.BoseGases.acube ℓ, Work.BoseFixB3.CS.leakFn fc κ ℓ y *
              (∫ x in Submission.BoseGases.acube ℓ,
                Submission.BoseGases.chiU ℓ 0 x * F (x - y) * Submission.BoseGases.chiU ℓ 0 y)|
            ≤ C * ((ℓ * κ) ^ (-(40 : ℝ)) + R / ℓ) * ℓ ^ 3
                * ∫ z : EuclideanSpace ℝ (Fin 3), ‖F z‖ :=
  leakCoupl_of_swaps bumpProd_bound leakCoupl_swap leakFn_pointwise_bound

end Work.BoseFixB3.CS.Pieces
