/-
# Auxiliary definitions for the `T4` estimate of `thetaDerivative`

The `D_θΓ`-term of `D_θ(𝓛_Γ^T f)` coming from the projector is

  `T4 α f z θ = (D_θΓ(θ)/c) · (2z²/(1+z)³) · L₁₂(Transport f)(0)`,

see `Work.Coercivity.thetaAux`.  This file fixes the pieces into which it factors, so
that the `L²` estimate `wip_T4_ge` can be stated in terms of them:

* `T4g` is the radial factor `2z²/(1+z)³`;
* `T4h α θ = sin(2θ)^{-γ/2}` is the "half" angular weight whose square is
  `sin(2θ)^{-γ}` (`rpow_neg_sq`);
* `T4A α p` and `T4B α p` are the two `L²` factors of the Cauchy–Schwarz estimate:
  `T4A α p = Γ(p.2)·g(p.1)·sin(2p.2)^{-γ/2}·w(p.1)` carries the angular data and the
  radial weight, `T4B α f p = sin(2p.2)^{-γ/2}·w(p.1)·D_θ f(p)` carries the unknown
  `D_θ f`; their product is (up to the a.e. identity `rpow_neg_sq`)
  `Γ(θ)·g(z)·sin(2θ)^{-γ}·w(z)²·D_θ f(z,θ)`;
* `T4W α f p` is the integrand of `wip (thetaW α) (T4 α f) (Dth f)` divided by
  `C0 f / c α`, i.e. `D_θΓ(z,θ)·g(z)·sin(2θ)^{-γ}·w(z)²·D_θ f(z,θ)`;
* `T4P` is the product of the two restricted Lebesgue measures on `Iz` and `Iθ` (the
  natural measure of the quadrant, cf. `volume_restrict_prod`), and `T4J α` is the
  angular quantity `∫_θ Γ(θ)² sin(2θ)^{-γ}` which bounds the `L²` norm of `T4A`.
-/
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.Coercivity.thetaAux
import Submission.Work.Coercivity.rpow_neg_sq

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.Coercivity

set_option autoImplicit false

/-- The radial factor `2z²/(1+z)³` of `T4`. -/
def T4g (z : ℝ) : ℝ := 2 * z ^ 2 / (1 + z) ^ 3

/-- The half angular weight `sin(2θ)^{-γ/2}`, whose square is `sin(2θ)^{-γ}`. -/
def T4h (α θ : ℝ) : ℝ := (Real.sin (2 * θ)) ^ (-(Spaces.gam α / 2))

/-- The `L²` factor of the Cauchy–Schwarz estimate carrying the angular data and the
radial weight: `Γ(θ)·g(z)·sin(2θ)^{-γ/2}·w(z)`. -/
def T4A (α : ℝ) (p : ℝ × ℝ) : ℝ :=
  Spaces.Gam α p.2 * T4g p.1 * T4h α p.2 * Spaces.w p.1

/-- The `L²` factor of the Cauchy–Schwarz estimate carrying the unknown:
`sin(2θ)^{-γ/2}·w(z)·D_θ f(z,θ)`. -/
def T4B (α : ℝ) (f : ℝ → ℝ → ℝ) (p : ℝ × ℝ) : ℝ :=
  T4h α p.2 * Spaces.w p.1 * Spaces.Dth f p.1 p.2

/-- The integrand `D_θΓ(z,θ)·g(z)·sin(2θ)^{-γ}·w(z)²·D_θ f(z,θ)`: this is
`T4 α f z θ · D_θ f z θ · thetaW α z θ` divided by `C0 f / c α`. -/
def T4W (α : ℝ) (f : ℝ → ℝ → ℝ) (p : ℝ × ℝ) : ℝ :=
  DthGam α p.1 p.2 * T4g p.1 * (Real.sin (2 * p.2)) ^ (-(Spaces.gam α))
    * (Spaces.w p.1) ^ 2 * Spaces.Dth f p.1 p.2

/-- The measure of the quadrant: the product of the restrictions of Lebesgue measure
to `Iz = [0,∞)` and `Iθ = [0,π/2]`. -/
def T4P : MeasureTheory.Measure (ℝ × ℝ) :=
  (MeasureTheory.volume.restrict Spaces.Iz).prod (MeasureTheory.volume.restrict Spaces.Iθ)

/-- The angular quantity `∫_θ Γ(θ)² sin(2θ)^{-γ}` controlling the `L²` norm of `T4A`. -/
def T4J (α : ℝ) : ℝ :=
  ∫ θ in Spaces.Iθ, (Spaces.Gam α θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Spaces.gam α))

/-! ## Elementary properties -/

theorem T4g_nonneg {z : ℝ} (hz : 0 ≤ z) : 0 ≤ T4g z := by
  rw [T4g]
  exact div_nonneg (by positivity) (by positivity)

theorem T4h_sq (α θ : ℝ) (hθ : 0 ≤ Real.sin (2 * θ)) :
    (T4h α θ) ^ 2 = (Real.sin (2 * θ)) ^ (-(Spaces.gam α)) := by
  rw [T4h]
  exact rpow_neg_sq _ _ hθ

theorem T4h_nonneg (α θ : ℝ) (hθ : 0 ≤ Real.sin (2 * θ)) : 0 ≤ T4h α θ := by
  rw [T4h]
  exact Real.rpow_nonneg hθ _

/-- Pointwise description of `(T4A α p)²` as a product of a function of `p.1` and a
function of `p.2`, on the angular interval. -/
theorem T4A_sq_eq (α : ℝ) {p : ℝ × ℝ} (hθ : p.2 ∈ Spaces.Iθ) :
    (T4A α p) ^ 2 = ((T4g p.1) ^ 2 * (Spaces.w p.1) ^ 2)
      * ((Spaces.Gam α p.2) ^ 2 * (Real.sin (2 * p.2)) ^ (-(Spaces.gam α))) := by
  have hsin : 0 ≤ Real.sin (2 * p.2) :=
    Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])
  rw [T4A, mul_pow, mul_pow, mul_pow, T4h_sq α p.2 hsin]
  ring

/-- Pointwise description of `(T4B α f p)²`. -/
theorem T4B_sq_eq (α : ℝ) (f : ℝ → ℝ → ℝ) {p : ℝ × ℝ} (hθ : p.2 ∈ Spaces.Iθ) :
    (T4B α f p) ^ 2
      = Spaces.Dth f p.1 p.2 * Spaces.Dth f p.1 p.2 * (Spaces.w p.1) ^ 2
        * (Real.sin (2 * p.2)) ^ (-(Spaces.gam α)) := by
  have hsin : 0 ≤ Real.sin (2 * p.2) :=
    Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])
  rw [T4B, mul_pow, mul_pow, T4h_sq α p.2 hsin]
  ring

/-- Pointwise description of the product `T4A α p · T4B α f p`, i.e. the
Cauchy–Schwarz pairing without the `D_θΓ` factor. -/
theorem T4A_mul_T4B (α : ℝ) (f : ℝ → ℝ → ℝ) {p : ℝ × ℝ} (hθ : p.2 ∈ Spaces.Iθ) :
    T4A α p * T4B α f p
      = Spaces.Gam α p.2 * T4g p.1 * (Real.sin (2 * p.2)) ^ (-(Spaces.gam α))
        * (Spaces.w p.1) ^ 2 * Spaces.Dth f p.1 p.2 := by
  have hsin : 0 ≤ Real.sin (2 * p.2) :=
    Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])
  rw [T4A, T4B, ← T4h_sq α p.2 hsin]
  ring

/-! ## Measurability -/

theorem measurable_T4g : Measurable T4g := by
  unfold T4g
  exact (measurable_const.mul (measurable_id.pow_const (2 : ℕ))).div
    ((measurable_const.add measurable_id).pow_const (3 : ℕ))

theorem measurable_T4h (α : ℝ) : Measurable (T4h α) := by
  unfold T4h
  exact (Real.measurable_sin.comp (measurable_const.mul measurable_id)).pow_const _

theorem measurable_w : Measurable Spaces.w := by
  unfold Spaces.w
  exact ((measurable_const.add measurable_id).pow_const (2 : ℕ)).div
    (measurable_id.pow_const (2 : ℕ))

theorem measurable_Gam (α : ℝ) : Measurable (fun θ : ℝ => Spaces.Gam α θ) := by
  unfold Spaces.Gam
  exact (Real.measurable_sin.mul (Real.measurable_cos.pow_const (2 : ℕ))).pow_const (α / 3)

theorem measurable_DthGam (α : ℝ) : Measurable (fun θ : ℝ => DthGam α 0 θ) := by
  have h : (fun θ : ℝ => DthGam α 0 θ)
      = fun θ => Real.sin (2 * θ) * deriv (fun t => Spaces.Gam α t) θ := by
    funext θ
    rw [DthGam_eq]
  rw [h]
  exact (Real.measurable_sin.comp (measurable_const.mul measurable_id)).mul (measurable_deriv _)

theorem measurable_DthGam_prod (α : ℝ) : Measurable (fun p : ℝ × ℝ => DthGam α p.1 p.2) := by
  have h : (fun p : ℝ × ℝ => DthGam α p.1 p.2)
      = fun p => Real.sin (2 * p.2) * deriv (fun t => Spaces.Gam α t) p.2 := by
    funext p
    rw [DthGam_eq]
  rw [h]
  exact (Real.measurable_sin.comp (measurable_const.mul measurable_snd)).mul
    ((measurable_deriv _).comp measurable_snd)

theorem aesm_T4A (α : ℝ) : AEStronglyMeasurable (T4A α) T4P := by
  have h1 : Measurable (fun p : ℝ × ℝ => Spaces.Gam α p.2) :=
    (measurable_Gam α).comp measurable_snd
  have h2 : Measurable (fun p : ℝ × ℝ => T4g p.1) := measurable_T4g.comp measurable_fst
  have h3 : Measurable (fun p : ℝ × ℝ => T4h α p.2) := (measurable_T4h α).comp measurable_snd
  have h4 : Measurable (fun p : ℝ × ℝ => Spaces.w p.1) := measurable_w.comp measurable_fst
  have hm : Measurable (fun p : ℝ × ℝ =>
      Spaces.Gam α p.2 * T4g p.1 * T4h α p.2 * Spaces.w p.1) :=
    ((h1.mul h2).mul h3).mul h4
  have hfun : T4A α = fun p : ℝ × ℝ => Spaces.Gam α p.2 * T4g p.1 * T4h α p.2 * Spaces.w p.1 := rfl
  rw [hfun]
  exact hm.aestronglyMeasurable

end Work.Coercivity
