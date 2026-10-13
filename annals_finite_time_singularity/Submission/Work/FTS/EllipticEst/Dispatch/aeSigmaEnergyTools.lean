/-
Copyright: work module for the Elgindi finite-time singularity project.

# `aeSigmaEnergyTools` — the `σ`-weighted truncated radial energy identity, sliced

This module prepares the proof of `Work.FTS.EllipticEst.Dispatch.aeSigmaEnergyD`, namely

`α² HkSq α 0 (z ∂_z u) ≤ C (HkSq α 0 G + HkSq α 0 u)`

for data in the almost-everywhere class `Work.FTS.EllipticEst.H2W.Ae.AeData α u G`.

## Contents

* the `z`-slice functionals `sigR, sigZ, sigG, sigS, sigL, sigP` (the `σ`-weighted angular
  integrals of the four `ℋ⁰` slots and of the two pairings);
* `sigTruncIbpD`: the `σ`-weighted *radial* integration by parts identity, integrated in `θ`
  against `σ = sin(2θ)^{-η}` — it is `Honest.zIBP_compact` applied to each `θ`-slice and
  Fubini'd, so that everything is expressed with the `z`-slice functionals above.

The five joint-integrability inputs of the Fubini step are kept as explicit hypotheses here; they
are discharged from the `ℋ⁰`-membership of `u`, `G`, `z ∂_zu` and `z²∂_zzu` in the consumer.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Prod
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.EllipticEst.StraightDefs
import Submission.Work.Elliptic.Defs
import Submission.Work.FTS.EllipticEst.Honest.omegaW_deriv_bounds
import Submission.Work.FTS.EllipticEst.Honest.zIBP_compact
import Submission.Work.FTS.EllipticEst.AngAWeak.aeTruncIdent
import Submission.Work.FTS.EllipticEst.AngAWeak.AeTruncWDefs
import Submission.Work.FTS.EllipticEst.AngAWeak.aeEnergyWAux

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology ENNReal
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.Dispatch

set_option autoImplicit false
set_option maxHeartbeats 1600000

local notation "Iθ" => Work.Spaces.Iθ
local notation "Iz" => Work.Spaces.Iz
local notation "sg" => Work.FTS.EllipticEst.sEta

/-- The radial weight of the truncated identity: `om W z = W z · w z ²`. -/
def om (W : ℝ → ℝ) : ℝ → ℝ := fun z => W z * (Work.Spaces.w z) ^ 2

/-- `om W z · z²`, the weight of `∂_zzu`. -/
def om2 (W : ℝ → ℝ) : ℝ → ℝ := fun z => om W z * z ^ 2

/-- `om W z · z`, the weight of `∂_zu`. -/
def om1 (W : ℝ → ℝ) : ℝ → ℝ := fun z => om W z * z

@[simp] theorem om_apply (W : ℝ → ℝ) (z : ℝ) : om W z = W z * (Work.Spaces.w z) ^ 2 := rfl
@[simp] theorem om2_apply (W : ℝ → ℝ) (z : ℝ) : om2 W z = om W z * z ^ 2 := rfl
@[simp] theorem om1_apply (W : ℝ → ℝ) (z : ℝ) : om1 W z = om W z * z := rfl

/-- The product measure `dz dθ` over `Iz × Iθ`. -/
abbrev msig : MeasureTheory.Measure (ℝ × ℝ) :=
  (MeasureTheory.volume.restrict Iz).prod (MeasureTheory.volume.restrict Iθ)

/-! ## The `z`-slice functionals of the `σ`-weighted analysis -/

/-- `sigR u z = ∫_θ σ θ · u(z,θ)²`. -/
def sigR (u : ℝ → ℝ → ℝ) (z : ℝ) : ℝ := ∫ θ in Iθ, sg θ * (u z θ) ^ 2

/-- `sigZ u z = ∫_θ σ θ · (z ∂_zu(z,θ))²`. -/
def sigZ (u : ℝ → ℝ → ℝ) (z : ℝ) : ℝ :=
  ∫ θ in Iθ, sg θ * (z * Work.Spaces.pz u z θ) ^ 2

/-- `sigG G z = ∫_θ σ θ · G(z,θ)²`. -/
def sigG (G : ℝ → ℝ → ℝ) (z : ℝ) : ℝ := ∫ θ in Iθ, sg θ * (G z θ) ^ 2

/-- `sigS G u z = ∫_θ σ θ · G(z,θ)·u(z,θ)`. -/
def sigS (G u : ℝ → ℝ → ℝ) (z : ℝ) : ℝ := ∫ θ in Iθ, sg θ * (G z θ * u z θ)

/-- `sigL u z = ∫_θ σ θ · (Lzero u)(z,θ)·u(z,θ)`. -/
def sigL (u : ℝ → ℝ → ℝ) (z : ℝ) : ℝ :=
  ∫ θ in Iθ, sg θ * (Work.Elliptic.Lzero u z θ * u z θ)

/-- `sigP α u z = ∫_θ σ θ · ((α²z²∂_zzu + α(5+α)z∂_zu)(z,θ))·u(z,θ)`. -/
def sigP (α : ℝ) (u : ℝ → ℝ → ℝ) (z : ℝ) : ℝ :=
  ∫ θ in Iθ, sg θ *
    ((α ^ 2 * z ^ 2 * Work.Spaces.pzIter 2 u z θ
      + (α * (5 + α) * z) * Work.Spaces.pz u z θ) * u z θ)

/-! ## Nonnegativity of the `ℋ⁰` slots -/

theorem sEta_nonneg_of_mem {θ : ℝ} (hθ : θ ∈ Iθ) : 0 ≤ sg θ := by
  rw [Work.FTS.EllipticEst.sEta]
  exact Real.rpow_nonneg
    (Real.sin_nonneg_of_mem_Icc ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩) _

theorem sigR_nonneg (u : ℝ → ℝ → ℝ) (z : ℝ) : 0 ≤ sigR u z := by
  rw [sigR]
  exact MeasureTheory.setIntegral_nonneg measurableSet_Icc
    (fun θ hθ => mul_nonneg (sEta_nonneg_of_mem hθ) (sq_nonneg _))

theorem sigZ_nonneg (u : ℝ → ℝ → ℝ) (z : ℝ) : 0 ≤ sigZ u z := by
  rw [sigZ]
  exact MeasureTheory.setIntegral_nonneg measurableSet_Icc
    (fun θ hθ => mul_nonneg (sEta_nonneg_of_mem hθ) (sq_nonneg _))

theorem sigG_nonneg (G : ℝ → ℝ → ℝ) (z : ℝ) : 0 ≤ sigG G z := by
  rw [sigG]
  exact MeasureTheory.setIntegral_nonneg measurableSet_Icc
    (fun θ hθ => mul_nonneg (sEta_nonneg_of_mem hθ) (sq_nonneg _))


/-- Linearity of the Bochner integral in the `c₁f₁ + f₂ - c₃f₃ + c₄f₄` shape. -/
theorem integral_lin4 {μ : MeasureTheory.Measure ℝ} {f1 f2 f3 f4 : ℝ → ℝ} {c1 c3 c4 : ℝ}
    (h1 : MeasureTheory.Integrable f1 μ) (h2 : MeasureTheory.Integrable f2 μ)
    (h3 : MeasureTheory.Integrable f3 μ) (h4 : MeasureTheory.Integrable f4 μ) :
    (∫ x, (c1 * f1 x + f2 x - c3 * f3 x + c4 * f4 x) ∂μ)
      = c1 * (∫ x, f1 x ∂μ) + (∫ x, f2 x ∂μ) - c3 * (∫ x, f3 x ∂μ)
        + c4 * (∫ x, f4 x ∂μ) := by
  have hAB : MeasureTheory.Integrable (fun x => c1 * f1 x + f2 x) μ :=
    (h1.const_mul c1).add h2
  have hC : MeasureTheory.Integrable (fun x => c3 * f3 x) μ := h3.const_mul c3
  have hD : MeasureTheory.Integrable (fun x => c4 * f4 x) μ := h4.const_mul c4
  have hABC : MeasureTheory.Integrable (fun x => c1 * f1 x + f2 x - c3 * f3 x) μ :=
    hAB.sub hC
  rw [MeasureTheory.integral_add hABC hD, MeasureTheory.integral_sub hAB hC,
    MeasureTheory.integral_add (h1.const_mul c1) h2,
    MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul,
    MeasureTheory.integral_const_mul]

/-! ## The `σ`-weighted truncated radial energy identity -/

/-- **The `σ`-weighted truncated radial identity.**  This is the identity
`aeTruncIdent_core` of the colleague's module with the angular integration weighted by
`σ = sin(2θ)^{-η}` instead of being unweighted: it is `Honest.zIBP_compact` applied to each
`θ`-slice and then Fubini'd against `σ`.

The five joint-integrability inputs are kept as hypotheses; they are discharged from the
`ℋ⁰`-membership of `u`, `G`, `z ∂_zu` and `z²∂_zzu` in the consumer. -/
theorem sigTruncIdentD (α : ℝ) (u G : ℝ → ℝ → ℝ) (W : ℝ → ℝ) (hW2 : ContDiff ℝ 2 W)
    (hWcpt : HasCompactSupport W) (hW0 : ∃ δ : ℝ, 0 < δ ∧ ∀ z, z ≤ δ → W z = 0)
    (heq : ∀ z, 0 < z → ∀ θ, 0 < θ → θ < Real.pi / 2 →
      Work.Elliptic.bslOp α u z θ = G z θ)
    (hJ1 : MeasureTheory.Integrable (fun p : ℝ × ℝ => om W p.1 *
      (sg p.2 * (Work.Elliptic.bslOp α u p.1 p.2 * u p.1 p.2))) msig)
    (hJ2 : MeasureTheory.Integrable (fun p : ℝ × ℝ => sg p.2 *
      (om W p.1 * (p.1 * Work.Spaces.pz u p.1 p.2) ^ 2)) msig)
    (hJ3 : MeasureTheory.Integrable (fun p : ℝ × ℝ => sg p.2 *
      (deriv (deriv (om2 W)) p.1 * (u p.1 p.2) ^ 2)) msig)
    (hJ4 : MeasureTheory.Integrable (fun p : ℝ × ℝ => sg p.2 *
      (deriv (om1 W) p.1 * (u p.1 p.2) ^ 2)) msig)
    (hJ5 : MeasureTheory.Integrable (fun p : ℝ × ℝ => om W p.1 *
      (sg p.2 * (Work.Elliptic.Lzero u p.1 p.2 * u p.1 p.2))) msig)
    (hsl : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      ContDiffOn ℝ 2 (fun z => u z θ) (Set.Ioi 0)) :
    (∫ z in Iz, om W z * (∫ θ in Iθ, sg θ * (G z θ * u z θ)))
      = α ^ 2 * (∫ z in Iz, om2 W z * (∫ θ in Iθ, sg θ * (Work.Spaces.pz u z θ) ^ 2))
        + (∫ z in Iz, om W z * (∫ θ in Iθ, sg θ * (Work.Elliptic.Lzero u z θ * u z θ)))
        - (α ^ 2 / 2) * (∫ z in Iz, deriv (deriv (om2 W)) z *
            (∫ θ in Iθ, sg θ * (u z θ) ^ 2))
        + (α * (5 + α) / 2) * (∫ z in Iz, deriv (om1 W) z *
            (∫ θ in Iθ, sg θ * (u z θ) ^ 2)) := by
  obtain ⟨δ, hδ0, hδW⟩ := hW0
  obtain ⟨R, hR0, hRW⟩ := Work.FTS.EllipticEst.AngAWeak.exists_bound_W W hWcpt
  have hδR : min δ R ≤ R := min_le_right _ _
  have hδmin0 : 0 < min δ R := lt_min hδ0 hR0
  have hδminW : ∀ z, z ≤ min δ R → W z = 0 := fun z hz =>
    hδW z (le_trans hz (min_le_left _ _))
  -- ## Step 1: replace `G` by `bslOp α u` on the left-hand side
  have hbsl : (∫ z in Iz, om W z * (∫ θ in Iθ, sg θ * (G z θ * u z θ)))
      = ∫ z in Iz, om W z *
          (∫ θ in Iθ, sg θ * (Work.Elliptic.bslOp α u z θ * u z θ)) := by
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Ici fun z _ => ?_
    by_cases hzδ : z ≤ min δ R
    · have h0 : om W z = 0 := by rw [om, hδminW z hzδ]; ring
      rw [h0, zero_mul, zero_mul]
    · have hz0 : 0 < z := lt_trans hδmin0 (lt_of_not_ge hzδ)
      congr 1
      refine MeasureTheory.integral_congr_ae ?_
      filter_upwards [Work.FTS.EllipticEst.Honest.ae_mem_Ioo_Iθ] with θ hθ
      show sg θ * (G z θ * u z θ) = sg θ * (Work.Elliptic.bslOp α u z θ * u z θ)
      rw [heq z hz0 θ hθ.1 hθ.2]
  -- ## Step 2: Fubini on the left-hand side
  have hfub1 : (∫ z in Iz, om W z *
        (∫ θ in Iθ, sg θ * (Work.Elliptic.bslOp α u z θ * u z θ)))
      = ∫ θ in Iθ, sg θ *
          (∫ z in Iz, om W z * (Work.Elliptic.bslOp α u z θ * u z θ)) := by
    have h1 : (∫ z in Iz, om W z *
          (∫ θ in Iθ, sg θ * (Work.Elliptic.bslOp α u z θ * u z θ)))
        = ∫ z in Iz, ∫ θ in Iθ,
            om W z * (sg θ * (Work.Elliptic.bslOp α u z θ * u z θ)) := by
      refine MeasureTheory.setIntegral_congr_fun measurableSet_Ici fun z _ => ?_
      rw [MeasureTheory.integral_const_mul]
    rw [h1, MeasureTheory.integral_integral_swap
      (f := fun z θ => om W z * (sg θ * (Work.Elliptic.bslOp α u z θ * u z θ)))
      (μ := MeasureTheory.volume.restrict Iz)
      (ν := MeasureTheory.volume.restrict Iθ) hJ1]
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Icc fun θ _ => ?_
    rw [show (fun z => om W z * (sg θ * (Work.Elliptic.bslOp α u z θ * u z θ)))
        = fun z => sg θ * (om W z * (Work.Elliptic.bslOp α u z θ * u z θ)) from by
      funext z; ring]
    rw [MeasureTheory.integral_const_mul]
  -- ## Step 3: the per-`θ` identity, a.e. in `θ`
  have hJ5' : MeasureTheory.Integrable (fun p : ℝ × ℝ => om W p.1 *
      (sg p.2 * (Work.Elliptic.Lzero u p.1 p.2 * u p.1 p.2))) msig := hJ5
  have hslice_lz : ∀ᵐ θ ∂(MeasureTheory.volume.restrict Iθ), MeasureTheory.IntegrableOn
      (fun z => om W z * (Work.Elliptic.Lzero u z θ * u z θ)) Iz := by
    filter_upwards [hJ5.prod_left_ae, Work.FTS.EllipticEst.Honest.ae_mem_Ioo_Iθ]
      with θ hJ hθ
    have hne : sg θ ≠ 0 := by
      have h1 := Work.FTS.EllipticEst.Honest.one_le_sEta_of_mem_Ioo hθ
      linarith
    have h3 := hJ.const_mul ((sg θ)⁻¹)
    refine h3.congr (Filter.Eventually.of_forall fun z => ?_)
    show (sg θ)⁻¹ * (om W z * (sg θ * (Work.Elliptic.Lzero u z θ * u z θ)))
      = om W z * (Work.Elliptic.Lzero u z θ * u z θ)
    rw [show (sg θ)⁻¹ * (om W z * (sg θ * (Work.Elliptic.Lzero u z θ * u z θ)))
        = ((sg θ)⁻¹ * sg θ) * (om W z * (Work.Elliptic.Lzero u z θ * u z θ)) from by ring,
      inv_mul_cancel₀ hne, one_mul]
  have hper : ∀ᵐ θ ∂(MeasureTheory.volume.restrict Iθ),
      (∫ z in Iz, om W z * (Work.Elliptic.bslOp α u z θ * u z θ))
        = α ^ 2 * (∫ z in Iz, om2 W z * (Work.Spaces.pz u z θ) ^ 2)
          + (∫ z in Iz, om W z * (Work.Elliptic.Lzero u z θ * u z θ))
          - (α ^ 2 / 2) * (∫ z in Iz, deriv (deriv (om2 W)) z * (u z θ) ^ 2)
          + (α * (5 + α) / 2) * (∫ z in Iz, deriv (om1 W) z * (u z θ) ^ 2) := by
    filter_upwards [hslice_lz, Work.FTS.EllipticEst.Honest.ae_mem_Ioo_Iθ] with θ hlz hθ
    exact Work.FTS.EllipticEst.AngAWeak.sliceIBP α u W hW2 hδmin0 hδR hθ hδminW hRW
      (hsl θ hθ) hlz
  -- ## Step 4: integrate in `θ` and use linearity
  have hJ2'' : MeasureTheory.Integrable (fun p : ℝ × ℝ =>
      sg p.2 * (om2 W p.1 * (Work.Spaces.pz u p.1 p.2) ^ 2)) msig :=
    hJ2.congr (Filter.Eventually.of_forall fun p => by
      simp only [om2_apply, om_apply]; ring)
  have hI2 : MeasureTheory.Integrable
      (fun θ => sg θ * (∫ z in Iz, om2 W z * (Work.Spaces.pz u z θ) ^ 2))
      (MeasureTheory.volume.restrict Iθ) := by
    refine hJ2''.integral_prod_right.congr ?_
    filter_upwards with θ
    rw [MeasureTheory.integral_const_mul]
  have hJ5'' : MeasureTheory.Integrable (fun p : ℝ × ℝ =>
      sg p.2 * (om W p.1 * (Work.Elliptic.Lzero u p.1 p.2 * u p.1 p.2))) msig :=
    hJ5.congr (Filter.Eventually.of_forall fun p => by ring)
  have hI5 : MeasureTheory.Integrable
      (fun θ => sg θ * (∫ z in Iz, om W z * (Work.Elliptic.Lzero u z θ * u z θ)))
      (MeasureTheory.volume.restrict Iθ) := by
    refine hJ5''.integral_prod_right.congr ?_
    filter_upwards with θ
    rw [MeasureTheory.integral_const_mul]
  have hI3 : MeasureTheory.Integrable
      (fun θ => sg θ * (∫ z in Iz, deriv (deriv (om2 W)) z * (u z θ) ^ 2))
      (MeasureTheory.volume.restrict Iθ) := by
    refine hJ3.integral_prod_right.congr ?_
    filter_upwards with θ
    rw [MeasureTheory.integral_const_mul]
  have hI4 : MeasureTheory.Integrable
      (fun θ => sg θ * (∫ z in Iz, deriv (om1 W) z * (u z θ) ^ 2))
      (MeasureTheory.volume.restrict Iθ) := by
    refine hJ4.integral_prod_right.congr ?_
    filter_upwards with θ
    rw [MeasureTheory.integral_const_mul]
  have hcomb : (∫ θ in Iθ, sg θ *
        (∫ z in Iz, om W z * (Work.Elliptic.bslOp α u z θ * u z θ)))
      = ∫ θ in Iθ,
          (α ^ 2 * (sg θ * (∫ z in Iz, om2 W z * (Work.Spaces.pz u z θ) ^ 2))
            + (sg θ * (∫ z in Iz, om W z * (Work.Elliptic.Lzero u z θ * u z θ)))
            - (α ^ 2 / 2) * (sg θ * (∫ z in Iz, deriv (deriv (om2 W)) z * (u z θ) ^ 2))
            + (α * (5 + α) / 2) * (sg θ * (∫ z in Iz, deriv (om1 W) z * (u z θ) ^ 2))) := by
    refine MeasureTheory.integral_congr_ae ?_
    filter_upwards [hper] with θ hθ
    rw [hθ]
    ring
  have hlin : (∫ θ in Iθ,
          (α ^ 2 * (sg θ * (∫ z in Iz, om2 W z * (Work.Spaces.pz u z θ) ^ 2))
            + (sg θ * (∫ z in Iz, om W z * (Work.Elliptic.Lzero u z θ * u z θ)))
            - (α ^ 2 / 2) * (sg θ * (∫ z in Iz, deriv (deriv (om2 W)) z * (u z θ) ^ 2))
            + (α * (5 + α) / 2) * (sg θ * (∫ z in Iz, deriv (om1 W) z * (u z θ) ^ 2))))
      = α ^ 2 * (∫ θ in Iθ, sg θ * (∫ z in Iz, om2 W z * (Work.Spaces.pz u z θ) ^ 2))
        + (∫ θ in Iθ, sg θ * (∫ z in Iz, om W z * (Work.Elliptic.Lzero u z θ * u z θ)))
        - (α ^ 2 / 2) * (∫ θ in Iθ, sg θ *
            (∫ z in Iz, deriv (deriv (om2 W)) z * (u z θ) ^ 2))
        + (α * (5 + α) / 2) * (∫ θ in Iθ, sg θ *
            (∫ z in Iz, deriv (om1 W) z * (u z θ) ^ 2)) :=
    integral_lin4 hI2 hI5 hI3 hI4
  -- ## Step 5: Fubini back for the four terms
  have f1 : (∫ θ in Iθ, sg θ * (∫ z in Iz, om2 W z * (Work.Spaces.pz u z θ) ^ 2))
      = ∫ z in Iz, om2 W z * (∫ θ in Iθ, sg θ * (Work.Spaces.pz u z θ) ^ 2) := by
    have h1 : (∫ θ in Iθ, sg θ * (∫ z in Iz, om2 W z * (Work.Spaces.pz u z θ) ^ 2))
        = ∫ θ in Iθ, ∫ z in Iz, sg θ * (om2 W z * (Work.Spaces.pz u z θ) ^ 2) := by
      refine MeasureTheory.setIntegral_congr_fun measurableSet_Icc fun θ _ => ?_
      rw [← MeasureTheory.integral_const_mul]
    rw [h1, ← MeasureTheory.integral_integral_swap (f := fun z θ =>
      sg θ * (om2 W z * (Work.Spaces.pz u z θ) ^ 2))
      (μ := MeasureTheory.volume.restrict Iz)
      (ν := MeasureTheory.volume.restrict Iθ) hJ2'']
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Ici fun z _ => ?_
    rw [show (fun θ => sg θ * (om2 W z * (Work.Spaces.pz u z θ) ^ 2))
        = fun θ => om2 W z * (sg θ * (Work.Spaces.pz u z θ) ^ 2) from by funext θ; ring,
      MeasureTheory.integral_const_mul]
  have f2 : (∫ θ in Iθ, sg θ *
        (∫ z in Iz, om W z * (Work.Elliptic.Lzero u z θ * u z θ)))
      = ∫ z in Iz, om W z * (∫ θ in Iθ, sg θ * (Work.Elliptic.Lzero u z θ * u z θ)) := by
    have h1 : (∫ θ in Iθ, sg θ * (∫ z in Iz, om W z * (Work.Elliptic.Lzero u z θ * u z θ)))
        = ∫ θ in Iθ, ∫ z in Iz, sg θ * (om W z * (Work.Elliptic.Lzero u z θ * u z θ)) := by
      refine MeasureTheory.setIntegral_congr_fun measurableSet_Icc fun θ _ => ?_
      rw [← MeasureTheory.integral_const_mul]
    rw [h1, ← MeasureTheory.integral_integral_swap (f := fun z θ =>
      sg θ * (om W z * (Work.Elliptic.Lzero u z θ * u z θ)))
      (μ := MeasureTheory.volume.restrict Iz)
      (ν := MeasureTheory.volume.restrict Iθ) hJ5'']
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Ici fun z _ => ?_
    rw [show (fun θ => sg θ * (om W z * (Work.Elliptic.Lzero u z θ * u z θ)))
        = fun θ => om W z * (sg θ * (Work.Elliptic.Lzero u z θ * u z θ)) from by
      funext θ; ring,
      MeasureTheory.integral_const_mul]
  have f3 : (∫ θ in Iθ, sg θ * (∫ z in Iz, deriv (deriv (om2 W)) z * (u z θ) ^ 2))
      = ∫ z in Iz, deriv (deriv (om2 W)) z * (∫ θ in Iθ, sg θ * (u z θ) ^ 2) := by
    have h1 : (∫ θ in Iθ, sg θ * (∫ z in Iz, deriv (deriv (om2 W)) z * (u z θ) ^ 2))
        = ∫ θ in Iθ, ∫ z in Iz, sg θ * (deriv (deriv (om2 W)) z * (u z θ) ^ 2) := by
      refine MeasureTheory.setIntegral_congr_fun measurableSet_Icc fun θ _ => ?_
      rw [← MeasureTheory.integral_const_mul]
    rw [h1, ← MeasureTheory.integral_integral_swap (f := fun z θ =>
      sg θ * (deriv (deriv (om2 W)) z * (u z θ) ^ 2))
      (μ := MeasureTheory.volume.restrict Iz)
      (ν := MeasureTheory.volume.restrict Iθ) hJ3]
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Ici fun z _ => ?_
    rw [show (fun θ => sg θ * (deriv (deriv (om2 W)) z * (u z θ) ^ 2))
        = fun θ => deriv (deriv (om2 W)) z * (sg θ * (u z θ) ^ 2) from by funext θ; ring,
      MeasureTheory.integral_const_mul]
  have f4 : (∫ θ in Iθ, sg θ * (∫ z in Iz, deriv (om1 W) z * (u z θ) ^ 2))
      = ∫ z in Iz, deriv (om1 W) z * (∫ θ in Iθ, sg θ * (u z θ) ^ 2) := by
    have h1 : (∫ θ in Iθ, sg θ * (∫ z in Iz, deriv (om1 W) z * (u z θ) ^ 2))
        = ∫ θ in Iθ, ∫ z in Iz, sg θ * (deriv (om1 W) z * (u z θ) ^ 2) := by
      refine MeasureTheory.setIntegral_congr_fun measurableSet_Icc fun θ _ => ?_
      rw [← MeasureTheory.integral_const_mul]
    rw [h1, ← MeasureTheory.integral_integral_swap (f := fun z θ =>
      sg θ * (deriv (om1 W) z * (u z θ) ^ 2))
      (μ := MeasureTheory.volume.restrict Iz)
      (ν := MeasureTheory.volume.restrict Iθ) hJ4]
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Ici fun z _ => ?_
    rw [show (fun θ => sg θ * (deriv (om1 W) z * (u z θ) ^ 2))
        = fun θ => deriv (om1 W) z * (sg θ * (u z θ) ^ 2) from by funext θ; ring,
      MeasureTheory.integral_const_mul]
  rw [hbsl, hfub1, hcomb, hlin, f1, f2, f3, f4]

end Work.FTS.EllipticEst.Dispatch
