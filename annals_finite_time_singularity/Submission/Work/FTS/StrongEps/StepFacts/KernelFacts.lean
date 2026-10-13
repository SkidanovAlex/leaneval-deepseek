/-
Copyright: work module for the Elgindi finite-time singularity project.

# `Submission/Work/FTS/StrongEps/StepFacts/KernelFacts.lean`

The kernel bookkeeping of the **one-order smoothing estimate** for the log-coordinate mollifier
`J_ε` (`Work.FTS.StrongEps.HkSq_Jeps_step_le`).

The routed derivative identities (child modules `mixed_Jeps_route_z`, `DthIter_Jeps_route_theta`)
express a slot of `J_ε u` of order `m` as `∫ ∂_{p_i}(Jker ρ ε)(p) · (slot of u of order m-1)(shift p) dp`,
i.e. against the *derivative* of the kernel.  The mass of such a derivative density is `ε⁻¹` times
the mass of the corresponding derivative of `ρ`, and this is where the two powers of `ε⁻¹` of the
estimate come from.

To keep the measurability bookkeeping of the `p`-integration in one piece, the densities are
repackaged as *one* rescaled kernel: with

  `ρ̃ = ρ + |∂_1ρ| + |∂_2ρ|`,   `Ψ p = ε⁻¹ · Jker ρ̃ ε p`,

one has `Jker ρ ε ≤ Ψ`, `|∂_1 Jker ρ ε| ≤ Ψ`, `|∂_2 Jker ρ ε| ≤ Ψ` pointwise (the identity
`Jker ρ̃ ε = Jker ρ ε + ε (|∂_1Jker ρ ε| + |∂_2Jker ρ ε|)` is `abs_deriv_Jker`), so every routed
density is dominated by `Mmax · Ψ` where `Mmax = max 1 (max M₁ (4 M₂))` collects the masses of
the two derivative densities.  This module records the definitions, the domination, the bound
`Mmax ≤ ε⁻¹ Dm` and the moment bound for `Ψ`, plus the joint measurability of the shifted
integrand against `Ψ`.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.StrongEps.Basic
import Submission.Work.FTS.StrongEps.Kernel
import Submission.Work.FTS.StrongEps.HkSqAux.aemeasurable_shift_pair
import Submission.Work.FTS.StrongEps.StepFacts.OfRealTools
import Submission.Work.FTS.StrongEps.StepFacts.abs_deriv_Jker
import Submission.Work.FTS.StrongEps.StepFacts.Jker_moment_le

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.StepFacts

set_option autoImplicit false

/-! ## The two derivative densities and the combined kernel -/

/-- The `p₁`-derivative density of the kernel: `|∂_{p₁}ρ|`. -/
def sigma1 (ρ : ℝ × ℝ → ℝ) : ℝ × ℝ → ℝ := fun q => |deriv (fun s : ℝ => ρ (s, q.2)) q.1|

/-- The `p₂`-derivative density of the kernel: `|∂_{p₂}ρ|`. -/
def sigma2 (ρ : ℝ × ℝ → ℝ) : ℝ × ℝ → ℝ := fun q => |deriv (fun t : ℝ => ρ (q.1, t)) q.2|

/-- The combined kernel `ρ̃ = ρ + |∂₁ρ| + |∂₂ρ|`, whose rescaled version dominates the kernel and
both of its partial derivatives. -/
def rhoTilde (ρ : ℝ × ℝ → ℝ) : ℝ × ℝ → ℝ := fun p => ρ p + sigma1 ρ p + sigma2 ρ p

/-- The mass of the `p₁`-derivative density: `|∂_{p₁}Jker ρ ε| = K1`. -/
def K1 (ρ : ℝ × ℝ → ℝ) (ε : ℝ) (p : ℝ × ℝ) : ℝ :=
  ε⁻¹ * Work.FTS.StrongEps.Jker (sigma1 ρ) ε p

/-- The mass of the `p₂`-derivative density: `|∂_{p₂}Jker ρ ε| = K2`. -/
def K2 (ρ : ℝ × ℝ → ℝ) (ε : ℝ) (p : ℝ × ℝ) : ℝ :=
  ε⁻¹ * Work.FTS.StrongEps.Jker (sigma2 ρ) ε p

/-- The combined density `Ψ = ε⁻¹ · Jker ρ̃ ε` dominating the kernel and its two partial
derivatives, and carrying the `ε⁻¹` of one routed derivative. -/
def Psi (ρ : ℝ × ℝ → ℝ) (ε : ℝ) (p : ℝ × ℝ) : ℝ :=
  ε⁻¹ * Work.FTS.StrongEps.Jker (rhoTilde ρ) ε p

/-- `Ψ` as a single rescaled kernel: `Ψ = Jker (ε⁻¹ · ρ̃) ε`. -/
theorem Psi_eq_Jker (ρ : ℝ × ℝ → ℝ) (ε : ℝ) (p : ℝ × ℝ) :
    Psi ρ ε p = Work.FTS.StrongEps.Jker (fun q : ℝ × ℝ => ε⁻¹ * rhoTilde ρ q) ε p := by
  simp only [Psi, Work.FTS.StrongEps.Jker]
  ring

/-- The total mass `∫ |∂_{p₁}Jker ρ ε|`. -/
def M1 (ρ : ℝ × ℝ → ℝ) (ε : ℝ) : ℝ := ∫ p, K1 ρ ε p

/-- The total mass `∫ |∂_{p₂}Jker ρ ε|`. -/
def M2 (ρ : ℝ × ℝ → ℝ) (ε : ℝ) : ℝ := ∫ p, K2 ρ ε p

/-- The largest of the three masses that can occur for a routed slot. -/
def Mmax (ρ : ℝ × ℝ → ℝ) (ε : ℝ) : ℝ := max 1 (max (M1 ρ ε) (4 * M2 ρ ε))

/-- The `ε`-free bound `ε⁻¹ Dm` for `Mmax`. -/
def Dm (ρ : ℝ × ℝ → ℝ) : ℝ := max 1 (max (∫ p, sigma1 ρ p) (4 * ∫ p, sigma2 ρ p))

/-- The `γ`-moment of the combined kernel `ρ̃`, i.e. the mass of `Ψ` seen with the shift gain
`e^{γ|p|}`. -/
def Dmass (ρ : ℝ × ℝ → ℝ) (γ : ℝ) : ℝ :=
  ∫ t : ℝ × ℝ, rhoTilde ρ t * Real.exp (γ * (|t.1| + |t.2|))

/-! ## Elementary properties -/

theorem sigma1_nonneg (ρ : ℝ × ℝ → ℝ) (p : ℝ × ℝ) : 0 ≤ sigma1 ρ p := abs_nonneg _

theorem sigma2_nonneg (ρ : ℝ × ℝ → ℝ) (p : ℝ × ℝ) : 0 ≤ sigma2 ρ p := abs_nonneg _

theorem rhoTilde_nonneg (ρ : ℝ × ℝ → ℝ) (hρ : ∀ p, 0 ≤ ρ p) (p : ℝ × ℝ) :
    0 ≤ rhoTilde ρ p := by
  refine add_nonneg (add_nonneg (hρ p) (sigma1_nonneg ρ p)) (sigma2_nonneg ρ p)

theorem rho_le_rhoTilde_pt (ρ : ℝ × ℝ → ℝ) (hρ : ∀ p, 0 ≤ ρ p) (p : ℝ × ℝ) :
    ρ p ≤ rhoTilde ρ p := by
  have h1 : ρ p ≤ ρ p + sigma1 ρ p := le_add_of_nonneg_right (sigma1_nonneg ρ p)
  have h2 : ρ p + sigma1 ρ p ≤ ρ p + sigma1 ρ p + sigma2 ρ p :=
    le_add_of_nonneg_right (sigma2_nonneg ρ p)
  exact le_trans h1 h2

theorem sigma1_le_rhoTilde (ρ : ℝ × ℝ → ℝ) (hρ : ∀ p, 0 ≤ ρ p) (p : ℝ × ℝ) :
    sigma1 ρ p ≤ rhoTilde ρ p := by
  have h1 : sigma1 ρ p ≤ ρ p + sigma1 ρ p := le_add_of_nonneg_left (hρ p)
  have h2 : ρ p + sigma1 ρ p ≤ ρ p + sigma1 ρ p + sigma2 ρ p :=
    le_add_of_nonneg_right (sigma2_nonneg ρ p)
  exact le_trans h1 h2

theorem sigma2_le_rhoTilde (ρ : ℝ × ℝ → ℝ) (hρ : ∀ p, 0 ≤ ρ p) (p : ℝ × ℝ) :
    sigma2 ρ p ≤ rhoTilde ρ p := by
  have h1 : sigma2 ρ p ≤ ρ p + sigma2 ρ p := le_add_of_nonneg_left (hρ p)
  have h2 : ρ p + sigma2 ρ p ≤ ρ p + sigma1 ρ p + sigma2 ρ p := by linarith [sigma1_nonneg ρ p]
  exact le_trans h1 h2

/-- The rescaled kernel is monotone in the density. -/
theorem Jker_mono {σ τ : ℝ × ℝ → ℝ} (h : ∀ p, σ p ≤ τ p) (ε : ℝ) (p : ℝ × ℝ) :
    Work.FTS.StrongEps.Jker σ ε p ≤ Work.FTS.StrongEps.Jker τ ε p :=
  mul_le_mul_of_nonneg_left (h (ε⁻¹ • p)) (sq_nonneg _)

theorem Jker_nonneg_of_nonneg {σ : ℝ × ℝ → ℝ} (h : ∀ p, 0 ≤ σ p) (ε : ℝ) (p : ℝ × ℝ) :
    0 ≤ Work.FTS.StrongEps.Jker σ ε p :=
  mul_nonneg (sq_nonneg _) (h (ε⁻¹ • p))

theorem Jker_pos_of_pos {σ : ℝ × ℝ → ℝ} (h : ∀ p, 0 < σ p) {ε : ℝ} (hε : 0 < ε)
    (p : ℝ × ℝ) : 0 < Work.FTS.StrongEps.Jker σ ε p :=
  mul_pos (by positivity) (h (ε⁻¹ • p))

/-! ## The identification of the routed densities -/

/-- `K1` is the absolute value of the `p₁`-derivative of the kernel. -/
theorem K1_eq_abs_deriv (ρ : ℝ × ℝ → ℝ) (hρ : IsSmoothKernel ρ) {ε : ℝ} (hε : 0 < ε)
    (p : ℝ × ℝ) :
    K1 ρ ε p = |deriv (fun s : ℝ => Work.FTS.StrongEps.Jker ρ ε (s, p.2)) p.1| :=
  ((abs_deriv_Jker ρ hρ hε).1 p).symm

/-- `K2` is the absolute value of the `p₂`-derivative of the kernel. -/
theorem K2_eq_abs_deriv (ρ : ℝ × ℝ → ℝ) (hρ : IsSmoothKernel ρ) {ε : ℝ} (hε : 0 < ε)
    (p : ℝ × ℝ) :
    K2 ρ ε p = |deriv (fun t : ℝ => Work.FTS.StrongEps.Jker ρ ε (p.1, t)) p.2| :=
  ((abs_deriv_Jker ρ hρ hε).2.1 p).symm

theorem K1_nonneg (ρ : ℝ × ℝ → ℝ) {ε : ℝ} (hε : 0 ≤ ε) (p : ℝ × ℝ) : 0 ≤ K1 ρ ε p :=
  mul_nonneg (by positivity) (Jker_nonneg_of_nonneg (sigma1_nonneg ρ) ε p)

theorem K2_nonneg (ρ : ℝ × ℝ → ℝ) {ε : ℝ} (hε : 0 ≤ ε) (p : ℝ × ℝ) : 0 ≤ K2 ρ ε p :=
  mul_nonneg (by positivity) (Jker_nonneg_of_nonneg (sigma2_nonneg ρ) ε p)

/-! ## The domination of the three densities by `Ψ` -/

theorem Jker_le_Psi (ρ : ℝ × ℝ → ℝ) (hρ0 : ∀ p, 0 ≤ ρ p) {ε : ℝ} (hε : 0 < ε)
    (hε1 : ε ≤ 1) (p : ℝ × ℝ) :
    Work.FTS.StrongEps.Jker ρ ε p ≤ Psi ρ ε p := by
  have hle : Work.FTS.StrongEps.Jker ρ ε p
      ≤ Work.FTS.StrongEps.Jker (rhoTilde ρ) ε p :=
    Jker_mono (rho_le_rhoTilde_pt ρ hρ0) ε p
  have h0 : 0 ≤ Work.FTS.StrongEps.Jker ρ ε p := Jker_nonneg_of_nonneg hρ0 ε p
  have h1 : (1 : ℝ) ≤ ε⁻¹ := by
    rw [← one_div]
    exact one_le_one_div hε hε1
  calc Work.FTS.StrongEps.Jker ρ ε p ≤ 1 * Work.FTS.StrongEps.Jker (rhoTilde ρ) ε p := by
        rw [one_mul]; exact hle
    _ ≤ ε⁻¹ * Work.FTS.StrongEps.Jker (rhoTilde ρ) ε p :=
        mul_le_mul_of_nonneg_right h1 (Jker_nonneg_of_nonneg (rhoTilde_nonneg ρ hρ0) ε p)
    _ = Psi ρ ε p := rfl

theorem K1_le_Psi (ρ : ℝ × ℝ → ℝ) (hρ0 : ∀ p, 0 ≤ ρ p) {ε : ℝ} (hε : 0 < ε) (p : ℝ × ℝ) :
    K1 ρ ε p ≤ Psi ρ ε p := by
  have hle : Work.FTS.StrongEps.Jker (sigma1 ρ) ε p
      ≤ Work.FTS.StrongEps.Jker (rhoTilde ρ) ε p :=
    Jker_mono (sigma1_le_rhoTilde ρ hρ0) ε p
  exact mul_le_mul_of_nonneg_left hle (by positivity)

theorem K2_le_Psi (ρ : ℝ × ℝ → ℝ) (hρ0 : ∀ p, 0 ≤ ρ p) {ε : ℝ} (hε : 0 < ε) (p : ℝ × ℝ) :
    K2 ρ ε p ≤ Psi ρ ε p := by
  have hle : Work.FTS.StrongEps.Jker (sigma2 ρ) ε p
      ≤ Work.FTS.StrongEps.Jker (rhoTilde ρ) ε p :=
    Jker_mono (sigma2_le_rhoTilde ρ hρ0) ε p
  exact mul_le_mul_of_nonneg_left hle (by positivity)

/-! ## Continuity, nonnegativity and support of the derived densities -/

theorem rhoTilde_continuous (ρ : ℝ × ℝ → ℝ) (hρ : IsSmoothKernel ρ) :
    Continuous (rhoTilde ρ) := by
  have h := abs_deriv_Jker ρ hρ (ε := 1) zero_lt_one
  exact (hρ.moll.cont.add h.2.2.1.abs).add h.2.2.2.1.abs

theorem rhoTilde_support (ρ : ℝ × ℝ → ℝ) (hρ : IsSmoothKernel ρ) {p : ℝ × ℝ}
    (hp : rhoTilde ρ p ≠ 0) : p.1 ^ 2 + p.2 ^ 2 ≤ 1 := by
  have h := abs_deriv_Jker ρ hρ (ε := 1) zero_lt_one
  have hρ0 := hρ.moll.nonneg
  have hs1 : 0 ≤ sigma1 ρ p := sigma1_nonneg ρ p
  have hs2 : 0 ≤ sigma2 ρ p := sigma2_nonneg ρ p
  have hsum : ρ p + sigma1 ρ p + sigma2 ρ p ≠ 0 := hp
  rcases eq_or_lt_of_le (hρ0 p) with h0 | h0
  · rcases eq_or_lt_of_le hs1 with h1 | h1
    · have h2 : sigma2 ρ p ≠ 0 := by
        intro hh
        exact hsum (by rw [← h0, ← h1, hh, add_zero, zero_add])
      exact h.2.2.2.2.2 p (by simpa [sigma2] using h2)
    · exact h.2.2.2.2.1 p (by simpa [sigma1] using h1.ne')
  · exact hρ.moll.support p h0.ne'

theorem sigma1_support (ρ : ℝ × ℝ → ℝ) (hρ : IsSmoothKernel ρ) {p : ℝ × ℝ}
    (hp : sigma1 ρ p ≠ 0) : p.1 ^ 2 + p.2 ^ 2 ≤ 1 :=
  (abs_deriv_Jker ρ hρ (ε := 1) zero_lt_one).2.2.2.2.1 p (by simpa [sigma1] using hp)

theorem sigma2_support (ρ : ℝ × ℝ → ℝ) (hρ : IsSmoothKernel ρ) {p : ℝ × ℝ}
    (hp : sigma2 ρ p ≠ 0) : p.1 ^ 2 + p.2 ^ 2 ≤ 1 :=
  (abs_deriv_Jker ρ hρ (ε := 1) zero_lt_one).2.2.2.2.2 p (by simpa [sigma2] using hp)

theorem sigma1_continuous (ρ : ℝ × ℝ → ℝ) (hρ : IsSmoothKernel ρ) : Continuous (sigma1 ρ) :=
  ((abs_deriv_Jker ρ hρ (ε := 1) zero_lt_one).2.2.1).abs

theorem sigma2_continuous (ρ : ℝ × ℝ → ℝ) (hρ : IsSmoothKernel ρ) : Continuous (sigma2 ρ) :=
  ((abs_deriv_Jker ρ hρ (ε := 1) zero_lt_one).2.2.2.1).abs

/-! ## The mass bounds -/

/-- The mass of `K1` is at most `ε⁻¹` times the mass of `|∂₁ρ|`. -/
theorem M1_le (ρ : ℝ × ℝ → ℝ) (hρ : IsSmoothKernel ρ) {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    M1 ρ ε ≤ ε⁻¹ * ∫ p, sigma1 ρ p := by
  have hmom := (Jker_moment_le (sigma1 ρ) (sigma1_nonneg ρ) (sigma1_continuous ρ hρ)
    (fun p hp => sigma1_support ρ hρ hp) (ε := ε) (γ := 0) hε hε1 le_rfl).2
  simp only [zero_mul, mul_zero, Real.exp_zero, mul_one] at hmom
  have hconst : (∫ p : ℝ × ℝ, K1 ρ ε p)
      = ε⁻¹ * ∫ p : ℝ × ℝ, Work.FTS.StrongEps.Jker (sigma1 ρ) ε p := by
    simp only [K1]
    exact MeasureTheory.integral_const_mul _ _
  rw [M1, hconst]
  exact mul_le_mul_of_nonneg_left hmom (by positivity)

/-- The mass of `K2` is at most `ε⁻¹` times the mass of `|∂₂ρ|`. -/
theorem M2_le (ρ : ℝ × ℝ → ℝ) (hρ : IsSmoothKernel ρ) {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    M2 ρ ε ≤ ε⁻¹ * ∫ p, sigma2 ρ p := by
  have hmom := (Jker_moment_le (sigma2 ρ) (sigma2_nonneg ρ) (sigma2_continuous ρ hρ)
    (fun p hp => sigma2_support ρ hρ hp) (ε := ε) (γ := 0) hε hε1 le_rfl).2
  simp only [zero_mul, mul_zero, Real.exp_zero, mul_one] at hmom
  have hconst : (∫ p : ℝ × ℝ, K2 ρ ε p)
      = ε⁻¹ * ∫ p : ℝ × ℝ, Work.FTS.StrongEps.Jker (sigma2 ρ) ε p := by
    simp only [K2]
    exact MeasureTheory.integral_const_mul _ _
  rw [M2, hconst]
  exact mul_le_mul_of_nonneg_left hmom (by positivity)

/-- **`Mmax ≤ ε⁻¹ Dm`**: the three masses of the routed slots are bounded by `ε⁻¹` times the
`ε`-free quantity `Dm`. -/
theorem Mmax_le (ρ : ℝ × ℝ → ℝ) (hρ : IsSmoothKernel ρ) {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    Mmax ρ ε ≤ ε⁻¹ * Dm ρ := by
  have h1 := M1_le ρ hρ hε hε1
  have h2 := M2_le ρ hρ hε hε1
  have h0 : (0 : ℝ) < ε⁻¹ := by positivity
  have hDm1 : (1 : ℝ) ≤ Dm ρ := le_max_left _ _
  have hDm2 : (∫ p, sigma1 ρ p) ≤ Dm ρ := le_trans (le_max_left _ _) (le_max_right _ _)
  have hDm3 : 4 * ∫ p, sigma2 ρ p ≤ Dm ρ := le_trans (le_max_right _ _) (le_max_right _ _)
  have hnn1 : 0 ≤ ∫ p, sigma1 ρ p :=
    integral_nonneg fun p => sigma1_nonneg ρ p
  have hnn2 : 0 ≤ ∫ p, sigma2 ρ p :=
    integral_nonneg fun p => sigma2_nonneg ρ p
  have hεinv1 : (1 : ℝ) ≤ ε⁻¹ := by
    rw [← one_div]
    exact one_le_one_div hε hε1
  rw [Mmax]
  refine max_le ?_ (max_le ?_ ?_)
  · calc (1 : ℝ) ≤ ε⁻¹ * 1 := by rw [mul_one]; exact hεinv1
      _ ≤ ε⁻¹ * Dm ρ := mul_le_mul_of_nonneg_left hDm1 (by positivity)
  · exact h1.trans (mul_le_mul_of_nonneg_left hDm2 (by positivity))
  · calc 4 * M2 ρ ε ≤ 4 * (ε⁻¹ * ∫ p, sigma2 ρ p) :=
          mul_le_mul_of_nonneg_left h2 (by norm_num)
      _ = ε⁻¹ * (4 * ∫ p, sigma2 ρ p) := by ring
      _ ≤ ε⁻¹ * Dm ρ := mul_le_mul_of_nonneg_left hDm3 (by positivity)

/-- **The moment bound for the combined density**: `∫ Ψ p e^{γ|p|} dp ≤ ε⁻¹ Dmass`. -/
theorem Psi_mass (ρ : ℝ × ℝ → ℝ) (hρ : IsSmoothKernel ρ) {ε γ : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hγ : 0 ≤ γ) :
    (∫ p : ℝ × ℝ, Psi ρ ε p * Real.exp (γ * (|p.1| + |p.2|)))
      ≤ ε⁻¹ * Dmass ρ γ := by
  have hmom := (Jker_moment_le (rhoTilde ρ) (rhoTilde_nonneg ρ hρ.moll.nonneg)
    (rhoTilde_continuous ρ hρ) (fun p hp => rhoTilde_support ρ hρ hp)
    (ε := ε) (γ := γ) hε hε1 hγ).2
  rw [Dmass]
  calc (∫ p : ℝ × ℝ, Psi ρ ε p * Real.exp (γ * (|p.1| + |p.2|)))
      = ∫ p : ℝ × ℝ, ε⁻¹ * (Work.FTS.StrongEps.Jker (rhoTilde ρ) ε p
          * Real.exp (γ * (|p.1| + |p.2|))) := by
        refine MeasureTheory.integral_congr_ae (Eventually.of_forall fun p => ?_)
        simp only [Psi]
        ring
    _ = ε⁻¹ * ∫ p : ℝ × ℝ,
          Work.FTS.StrongEps.Jker (rhoTilde ρ) ε p * Real.exp (γ * (|p.1| + |p.2|)) :=
        MeasureTheory.integral_const_mul _ _
    _ ≤ ε⁻¹ * ∫ t : ℝ × ℝ, rhoTilde ρ t * Real.exp (γ * (|t.1| + |t.2|)) :=
        mul_le_mul_of_nonneg_left hmom (by positivity)

/-- The moment integrand of `Ψ` is integrable. -/
theorem Psi_moment_integrable (ρ : ℝ × ℝ → ℝ) (hρ : IsSmoothKernel ρ) {ε γ : ℝ}
    (hε : 0 < ε) (hε1 : ε ≤ 1) (hγ : 0 ≤ γ) :
    Integrable (fun p : ℝ × ℝ => Psi ρ ε p * Real.exp (γ * (|p.1| + |p.2|))) := by
  have hint := (Jker_moment_le (rhoTilde ρ) (rhoTilde_nonneg ρ hρ.moll.nonneg)
    (rhoTilde_continuous ρ hρ) (fun p hp => rhoTilde_support ρ hρ hp)
    (ε := ε) (γ := γ) hε hε1 hγ).1
  refine (hint.const_mul ε⁻¹).congr (Eventually.of_forall fun p => ?_)
  simp only [Psi]
  ring

/-! ## Measurability of the shifted integrand against `Ψ` -/

/-- **Joint a.e. measurability of the density-times-shifted-integrand**, in the exact shape in
which the Tonelli step of the chain lemma uses it. -/
theorem aemeasurable_Psi_shift {ρ : ℝ × ℝ → ℝ} (hρ : IsSmoothKernel ρ) {ε c : ℝ}
    {α : ℝ} {k : ℕ} {u : ℝ → ℝ → ℝ}
    (hu : ContinuousOn (fun q : ℝ × ℝ => Work.Spaces.HkIntegrand α k u q.1 q.2)
      Work.FTS.StrongEps.Quad) :
    AEMeasurable (fun q : (ℝ × ℝ) × (ℝ × ℝ) =>
        ENNReal.ofReal (Psi ρ ε q.2)
          * ENNReal.ofReal (Real.exp (2 * c * (|q.2.1| + |q.2.2|)))
          * ENNReal.ofReal (Work.Spaces.HkIntegrand α k u
              (Work.FTS.StrongEps.zShift q.1.1 q.2.1)
              (Work.FTS.StrongEps.thShift q.1.2 q.2.2)))
      (((volume.restrict Work.Spaces.Iz).prod
          (volume.restrict Work.Spaces.Iθ)).prod volume) := by
  have hτc : Continuous (rhoTilde ρ) := rhoTilde_continuous ρ hρ
  have hbase := HkSqAux.aemeasurable_shift_pair
    (G := fun z θ => Work.Spaces.HkIntegrand α k u z θ) hu
    (fun q : ℝ × ℝ => ε⁻¹ * rhoTilde ρ q) (hτc.const_mul _) ε
  have hcont_exp : Continuous fun q : (ℝ × ℝ) × (ℝ × ℝ) =>
      Real.exp (2 * c * (|q.2.1| + |q.2.2|)) := by
    refine Real.continuous_exp.comp ?_
    refine Continuous.mul continuous_const (Continuous.add ?_ ?_)
    · exact continuous_abs.comp (continuous_fst.comp continuous_snd)
    · exact continuous_abs.comp (continuous_snd.comp continuous_snd)
  have hexp : AEMeasurable (fun q : (ℝ × ℝ) × (ℝ × ℝ) =>
      ENNReal.ofReal (Real.exp (2 * c * (|q.2.1| + |q.2.2|))))
      (((volume.restrict Work.Spaces.Iz).prod
          (volume.restrict Work.Spaces.Iθ)).prod volume) :=
    (ENNReal.measurable_ofReal.comp hcont_exp.measurable).aemeasurable
  refine (hbase.mul hexp).congr (Eventually.of_forall fun q => ?_)
  simp only [Pi.mul_apply, Psi_eq_Jker]
  ring

end Work.FTS.StrongEps.StepFacts
