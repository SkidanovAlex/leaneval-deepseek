import Submission.FUP.Spec
import Submission.FUP.Growth
import Mathlib.Topology.Semicontinuity.Defs
import Mathlib.Analysis.Analytic.Basic
import Mathlib.Analysis.Fourier.LpSpace
import Mathlib.Analysis.Real.Pi.Bounds

open FractalUncertainty MeasureTheory FourierTransform Metric
open scoped ENNReal BigOperators FourierTransform Real
open Submission.FUP

set_option autoImplicit false
variable {d : ℕ}
local notation "ℝᵈ" => EuclideanSpace ℝ (Fin d)
local notation "ℂᵈ" => (Fin d → ℂ)

namespace Submission.FUP

/-!
# Reduction of Cohen's higher-dimensional Beurling–Malliavin theorem to its two steps

Section 2 of Cohen's paper proves `thm:higher_dim_BM` by combining two propositions with the
classical Paley–Wiener criterion:

* `prop:BM_step1_prop` (Proposition `BM_step1_statement` below, proved in §3–§4): a weight `ω`
  satisfying the hypotheses of the Beurling–Malliavin theorem has a *continuous plurisubharmonic*
  extension `u` to `ℂᵈ` with `u ≤ ω` on `ℝᵈ`, `u = 0` on `B₂`, `u` Lipschitz on `ℝᵈ`, and
  `u(x) ≤ u(x + iy) ≤ u(x) + ρ|y|`;
* `prop:psh_to_bounded_fourier` (Proposition `psh_to_bounded_fourier_statement` below, proved in
  §5 via Hörmander's `L²` theory of the `∂̄` equation and the pointwise bound coming from
  subharmonicity): such a `u` produces an entire function `F` with the exponential bound
  `|F(z)| ≤ Ae^{2ρ|Im z|}`, the lower bound `|F| ≥ 1/2` on a ball, the upper bound
  `|F(x)| ≤ Ce^{u(x)}` on `ℝᵈ`, and `F|_{ℝᵈ} ∈ L²`;
* the Paley–Wiener criterion (`paley_wiener_statement`): an entire function with
  `|F(z)| ≤ Ae^{σ|Im z|}` whose restriction to `ℝᵈ` is in `L²` has Fourier transform supported
  in the ball of radius `σ/2π`.

The main result of this module, `higher_dim_BM_of_components`, derives
`Spec.higher_dim_BM_statement` from these three inputs by the rescaling argument of §2:
`u` is replaced by `u_σ = (σ/C_*)u` with `C_* = max(C_Lip, ρ)`, so that its Lipschitz constant
and its `y`-growth constant are both `≤ σ`; the resulting entire function has growth `e^{2σ|y|}`,
so Paley–Wiener gives Fourier support in the ball of radius `σ/π ≤ σ`, and
`|F(x)| ≤ Ce^{u_σ(x)} ≤ Ce^{(σ/C_*)ω(x)}`.

## Conventions

`ℂᵈ = Fin d → ℂ` is used with its usual (sup) norm; the only norms entering the statements are
the Euclidean norms of the real and imaginary parts, which are formed with `reVec` and `imVec`.
-/

section Basic

/-- The inclusion `ℝᵈ ↪ ℂᵈ`. -/
def toCpx (x : ℝᵈ) : ℂᵈ := fun i => (x i : ℂ)

/-- The real part of `z ∈ ℂᵈ`, as a vector of `ℝᵈ`. -/
noncomputable def reVec (z : ℂᵈ) : ℝᵈ :=
  (EuclideanSpace.equiv (Fin d) ℝ).symm fun i => (z i).re

/-- The imaginary part of `z ∈ ℂᵈ`, as a vector of `ℝᵈ`. -/
noncomputable def imVec (z : ℂᵈ) : ℝᵈ :=
  (EuclideanSpace.equiv (Fin d) ℝ).symm fun i => (z i).im

lemma reVec_toCpx (x : ℝᵈ) : reVec (toCpx x) = x := by
  ext i; simp [reVec, toCpx]

lemma imVec_toCpx (x : ℝᵈ) : imVec (toCpx x) = 0 := by
  ext i; simp [imVec, toCpx]

@[simp] lemma reVec_apply (z : ℂᵈ) (i : Fin d) : reVec z i = (z i).re := rfl

@[simp] lemma imVec_apply (z : ℂᵈ) (i : Fin d) : imVec z i = (z i).im := rfl

lemma toCpx_apply (x : ℝᵈ) (i : Fin d) : toCpx x i = (x i : ℂ) := rfl

lemma toCpx_injective : Function.Injective (toCpx : ℝᵈ → ℂᵈ) := by
  intro x y h
  ext i
  have := congrFun h i
  simpa [toCpx] using this

/-- The point `e^{iθ} v` of the complex disk centred at `z`. -/
noncomputable def circlePt (θ : ℝ) (v : ℂᵈ) : ℂᵈ := fun i => Complex.exp (θ * Complex.I) * v i

@[simp] lemma circlePt_apply (θ : ℝ) (v : ℂᵈ) (i : Fin d) :
    circlePt θ v i = Complex.exp (θ * Complex.I) * v i := rfl

lemma zero_mem_ball_of_le {r : ℝ} (hr : 0 < r) : (0 : ℝᵈ) ∈ ball 0 r := by
  simp [Metric.mem_ball, hr]

/-- The sub-mean-value property on complex disks: `u z ≤ ⨍_0^{2π} u(z + e^{iθ}v) dθ`
(equation (3.1) of the paper). -/
def SubMeanValue (u : ℂᵈ → ℝ) : Prop :=
  ∀ z v, u z ≤ (∫ θ in (0 : ℝ)..(2 * π), u (z + circlePt θ v)) / (2 * π)

/-- A function on `ℂᵈ` is plurisubharmonic if it is upper semicontinuous and satisfies the
sub-mean-value property on complex disks (Hörmander, *Notions of convexity*, Theorem 4.1.11). -/
def IsPSH (u : ℂᵈ → ℝ) : Prop :=
  UpperSemicontinuous u ∧ SubMeanValue u

/-- Plurisubharmonicity is preserved by multiplication by a nonnegative constant. -/
lemma IsPSH.const_mul {u : ℂᵈ → ℝ} (h : IsPSH u) {c : ℝ} (hc : 0 ≤ c) :
    IsPSH (fun z => c * u z) := by
  obtain ⟨husc, hsmv⟩ := h
  refine ⟨?_, ?_⟩
  · rw [UpperSemicontinuous] at husc ⊢
    intro z y hy
    rcases eq_or_lt_of_le hc with hc0 | hc0
    · subst hc0
      have hy' : (0 : ℝ) < y := by simpa using hy
      exact Filter.Eventually.of_forall (fun w => by simpa using hy')
    · have hlt : u z < y / c := by rw [lt_div_iff₀ hc0]; linarith
      filter_upwards [husc z (y / c) hlt] with w hw
      calc c * u w < c * (y / c) := mul_lt_mul_of_pos_left hw hc0
        _ = y := by field_simp
  · intro z v
    have h1 := hsmv z v
    have h2 : (∫ θ in (0 : ℝ)..(2 * π), c * u (z + circlePt θ v)) / (2 * π)
        = c * ((∫ θ in (0 : ℝ)..(2 * π), u (z + circlePt θ v)) / (2 * π)) := by
      rw [intervalIntegral.integral_const_mul]
      ring
    calc c * u z = c * u z := rfl
      _ ≤ c * ((∫ θ in (0 : ℝ)..(2 * π), u (z + circlePt θ v)) / (2 * π)) :=
          mul_le_mul_of_nonneg_left h1 hc
      _ = (∫ θ in (0 : ℝ)..(2 * π), c * u (z + circlePt θ v)) / (2 * π) := h2.symm

end Basic

section Statements

/-! The growth functional `growthFunctional` and the hypothesis `HasFiniteGrowth` now live in
`Submission.FUP.Growth` (so that the specification layer can use them). -/

/-- **`prop:BM_step1_prop`** (Cohen, §3–§4).  A weight `ω` satisfying the hypotheses of the
higher-dimensional Beurling–Malliavin theorem has a plurisubharmonic extension `u` to `ℂᵈ` with

* `u ≤ ω` on `ℝᵈ` and `u = 0` on `B₂`,
* `u` Lipschitz with a constant `C_Lip` that only depends on `C_reg` and `d`,
* `u(x) ≤ u(x + iy) ≤ u(x) + ρ|y|` with `ρ` depending only on `C_reg, C_gr` and `d`.

The two constants do not depend on `ω`. -/
def BM_step1_statement : Prop :=
  ∀ (Creg Cgr : ℝ), 0 < Creg → 0 < Cgr →
    ∃ (CLip ρ : ℝ), 0 < CLip ∧ 0 < ρ ∧
      ∀ (ω : ℝᵈ → ℝ), (∀ x, ω x ≤ 0) → (∀ x, ‖x‖ ≤ 2 → ω x = 0) →
        ContDiff ℝ 3 ω →
        (∀ (a : ℕ), a ≤ 3 → ∀ x : ℝᵈ,
          ‖iteratedFDeriv ℝ a ω x‖ ≤ Creg * (1 + ‖x‖ ^ 2) ^ ((1 - (a : ℝ)) / 2)) →
        HasFiniteGrowth ω Cgr →
        ∃ u : ℂᵈ → ℝ, IsPSH u ∧ (∀ x, u (toCpx x) ≤ ω x) ∧
          (∀ x, ‖x‖ ≤ 2 → u (toCpx x) = 0) ∧
          (∀ x₁ x₂, |u (toCpx x₁) - u (toCpx x₂)| ≤ CLip * ‖x₁ - x₂‖) ∧
          (∀ z, u (toCpx (reVec z)) ≤ u z ∧ u z ≤ u (toCpx (reVec z)) + ρ * ‖imVec z‖)

/-- **`prop:psh_to_bounded_fourier`** (Cohen, §5, after Bourgain).  A plurisubharmonic function `u`
on `ℂᵈ` with `u ≤ 0` on `ℝᵈ`, `u = 0` on `B₂`, Lipschitz constant `C_Lip` on `ℝᵈ` and
`u(x) ≤ u(x + iy) ≤ u(x) + ρ|y|` produces an entire function `F` with

* `|F(z)| ≤ A e^{2ρ|Im z|}`,
* `|F| ≥ 1/2` on `B_{r_min}`,
* `|F(x)| ≤ C e^{u(x)}` on `ℝᵈ`,
* `F|_{ℝᵈ} ∈ L²(ℝᵈ)`,

where `r_min, A, C` depend only on `C_Lip, ρ` and `d` (not on `u`). -/
def psh_to_bounded_fourier_statement : Prop :=
  ∀ (CLip ρ : ℝ), 0 < CLip → 0 < ρ →
    ∃ (rmin A C : ℝ), 0 < rmin ∧ 0 < A ∧ 0 < C ∧
      ∀ (u : ℂᵈ → ℝ), IsPSH u → (∀ x, u (toCpx x) ≤ 0) →
        (∀ x, ‖x‖ ≤ 2 → u (toCpx x) = 0) →
        (∀ x₁ x₂, |u (toCpx x₁) - u (toCpx x₂)| ≤ CLip * ‖x₁ - x₂‖) →
        (∀ z, u (toCpx (reVec z)) ≤ u z ∧ u z ≤ u (toCpx (reVec z)) + ρ * ‖imVec z‖) →
        ∃ F : ℂᵈ → ℂ, Differentiable ℂ F ∧
          (∀ z, ‖F z‖ ≤ A * Real.exp (2 * ρ * ‖imVec z‖)) ∧
          (∀ x, ‖x‖ ≤ rmin → (1 / 2 : ℝ) ≤ ‖F (toCpx x)‖) ∧
          (∀ x, ‖F (toCpx x)‖ ≤ C * Real.exp (u (toCpx x))) ∧
          MemLp (fun x : ℝᵈ => F (toCpx x)) 2 (volume : Measure ℝᵈ)

/-- **The Paley–Wiener criterion** (Appendix A.3 of the paper; Hörmander, *The Analysis of Linear
Partial Differential Operators I*, Theorem 7.3.1).  An entire function on `ℂᵈ` whose growth in the
imaginary direction is `e^{σ|Im z|}` has, after restriction to `ℝᵈ`, Fourier transform supported
in the ball of radius `σ/2π`. -/
def paley_wiener_statement : Prop :=
  ∀ (F : ℂᵈ → ℂ), Differentiable ℂ F → ∀ (σ A : ℝ), 0 < σ → 0 < A →
    (∀ z, ‖F z‖ ≤ A * Real.exp (σ * ‖imVec z‖)) →
    ∀ (g : Lp ℂ 2 (volume : Measure ℝᵈ)),
      (g =ᵐ[volume] fun x : ℝᵈ => F (toCpx x)) →
      (∀ᵐ ξ ∂(volume : Measure ℝᵈ), ξ ∉ closedBall (0 : ℝᵈ) (σ / (2 * π)) →
        ((𝓕 g : Lp ℂ 2 (volume : Measure ℝᵈ)) : ℝᵈ → ℂ) ξ = 0)

end Statements

section Reduction

/-- **Section 2 of the paper**: the higher-dimensional Beurling–Malliavin theorem follows from
`prop:BM_step1_prop`, `prop:psh_to_bounded_fourier` and the Paley–Wiener criterion. -/
theorem higher_dim_BM_of_components
    (hBM1 : BM_step1_statement (d := d))
    (hBM2 : psh_to_bounded_fourier_statement (d := d))
    (hPW : paley_wiener_statement (d := d)) :
    Spec.higher_dim_BM_statement (d := d) := by
  intro Creg Cgr hCreg hCgr σ hσ0 hσ1
  obtain ⟨CLip, ρ, hCLip, hρ, hstep1⟩ := hBM1 Creg Cgr hCreg hCgr
  -- apply the second step with the constants `C_Lip' = ρ' = σ`, as in §2
  obtain ⟨rmin, A, C, hrmin, hA, hC, hstep2⟩ := hBM2 σ σ hσ0 hσ0
  set Cstar : ℝ := max CLip ρ with hCstar
  have hCstar_pos : 0 < Cstar := lt_of_lt_of_le hCLip (le_max_left _ _)
  have hCLip_le : CLip ≤ Cstar := le_max_left _ _
  have hρ_le : ρ ≤ Cstar := le_max_right _ _
  refine ⟨1 / Cstar, rmin, C, by positivity, hrmin, hC, ?_⟩
  intro ω hωnonpos hωzero hωcont hωreg hωgrowth
  obtain ⟨u, hupsh, hu_le, hu_zero, hu_lip, hu_growth⟩ :=
    hstep1 ω hωnonpos hωzero hωcont hωreg hωgrowth
  set uσ : ℂᵈ → ℝ := fun z => (σ / Cstar) * u z with huσ
  have hσC : 0 < σ / Cstar := div_pos hσ0 hCstar_pos
  have huσ_psh : IsPSH uσ := hupsh.const_mul hσC.le
  have huσ_le : ∀ x, uσ (toCpx x) ≤ 0 := by
    intro x
    simp only [huσ]
    exact mul_nonpos_of_nonneg_of_nonpos hσC.le (le_trans (hu_le x) (hωnonpos x))
  have huσ_zero : ∀ x, ‖x‖ ≤ 2 → uσ (toCpx x) = 0 := by
    intro x hx
    simp only [huσ, hu_zero x hx, mul_zero]
  have hratio_lip : (σ / Cstar) * CLip ≤ σ := by
    rw [div_mul_eq_mul_div, div_le_iff₀ hCstar_pos]
    nlinarith [hCLip_le, hσ0]
  have hratio_growth : (σ / Cstar) * ρ ≤ σ := by
    rw [div_mul_eq_mul_div, div_le_iff₀ hCstar_pos]
    nlinarith [hρ_le, hσ0]
  have huσ_lip : ∀ x₁ x₂, |uσ (toCpx x₁) - uσ (toCpx x₂)| ≤ σ * ‖x₁ - x₂‖ := by
    intro x₁ x₂
    have h1 : uσ (toCpx x₁) - uσ (toCpx x₂)
        = (σ / Cstar) * (u (toCpx x₁) - u (toCpx x₂)) := by
      simp only [huσ]; ring
    rw [h1, abs_mul, abs_of_pos hσC]
    calc (σ / Cstar) * |u (toCpx x₁) - u (toCpx x₂)|
        ≤ (σ / Cstar) * (CLip * ‖x₁ - x₂‖) := mul_le_mul_of_nonneg_left (hu_lip x₁ x₂) hσC.le
      _ = ((σ / Cstar) * CLip) * ‖x₁ - x₂‖ := by ring
      _ ≤ σ * ‖x₁ - x₂‖ := mul_le_mul_of_nonneg_right hratio_lip (norm_nonneg _)
  have huσ_growth : ∀ z, uσ (toCpx (reVec z)) ≤ uσ z ∧
      uσ z ≤ uσ (toCpx (reVec z)) + σ * ‖imVec z‖ := by
    intro z
    obtain ⟨h1, h2⟩ := hu_growth z
    constructor
    · simp only [huσ]; exact mul_le_mul_of_nonneg_left h1 hσC.le
    · have h4 : (σ / Cstar) * (u (toCpx (reVec z)) + ρ * ‖imVec z‖)
          = uσ (toCpx (reVec z)) + ((σ / Cstar) * ρ) * ‖imVec z‖ := by
        simp only [huσ]; ring
      calc uσ z = (σ / Cstar) * u z := rfl
        _ ≤ (σ / Cstar) * (u (toCpx (reVec z)) + ρ * ‖imVec z‖) :=
            mul_le_mul_of_nonneg_left h2 hσC.le
        _ = uσ (toCpx (reVec z)) + ((σ / Cstar) * ρ) * ‖imVec z‖ := h4
        _ ≤ uσ (toCpx (reVec z)) + σ * ‖imVec z‖ := by
            have := mul_le_mul_of_nonneg_right hratio_growth (norm_nonneg (imVec z))
            linarith
  obtain ⟨F, hFdiff, hFgrowth, hFlow, hFup, hFmem⟩ :=
    hstep2 uσ huσ_psh huσ_le huσ_zero huσ_lip huσ_growth
  obtain ⟨g, hgeq⟩ : ∃ g : Lp ℂ 2 (volume : Measure ℝᵈ),
      g =ᵐ[volume] fun x : ℝᵈ => F (toCpx x) :=
    ⟨hFmem.toLp _, hFmem.coeFn_toLp⟩
  have hPWsupp := hPW F hFdiff (2 * σ) A (by positivity) hA hFgrowth g hgeq
  have hsupple : 2 * σ / (2 * π) ≤ σ := by
    rw [div_le_iff₀ (by positivity)]
    nlinarith [Real.pi_gt_three, hσ0]
  refine ⟨g, ?_, ?_, ?_⟩
  · filter_upwards [hPWsupp] with ξ hξ hξσ
    refine hξ (fun hmem => hξσ (closedBall_subset_closedBall hsupple hmem))
  · filter_upwards [ae_restrict_of_ae hgeq, ae_restrict_mem measurableSet_closedBall]
      with x hx hxmem
    rw [hx]
    refine hFlow x ?_
    rwa [mem_closedBall, dist_zero_right] at hxmem
  · filter_upwards [hgeq] with x hx
    rw [hx]
    calc ‖F (toCpx x)‖ ≤ C * Real.exp (uσ (toCpx x)) := hFup x
      _ ≤ C * Real.exp ((σ / Cstar) * ω x) := by
          refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) hC.le
          exact mul_le_mul_of_nonneg_left (hu_le x) hσC.le
      _ = C * Real.exp (1 / Cstar * σ * ω x) := by
          congr 2; ring

end Reduction

end Submission.FUP
