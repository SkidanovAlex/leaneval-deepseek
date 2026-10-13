/-
Copyright: work module for the Elgindi finite-time singularity project.

# Vocabulary for the interpolation lemma `interpGamma`

This file fixes the three weighted functionals in which the analytic core of
`Work.FTS.EllipticEst.TT.interpGamma` is phrased, together with the elementary facts about the
angular weight `sigA α θ = sin(2θ)^{2-γ(α)}` and the identification of the two sides of the
target with those functionals.

Recall `γ(α) = 1 + α/10` (`Work.Spaces.gam`) and `η = 99/100` (`Work.Spaces.eta`), and
`Iθ = [0,π/2]`, `Iz = [0,∞)`, `w z = (1+z)²/z²`.

The functionals are

* `Xint α G   = ∫∫ (D_z∂_θG)² w² sin(2θ)^{2-γ}`  (the left-hand side, with the *light* weight
  `σ_a = sin^{2-γ}`, which vanishes at both angular endpoints);
* `DDint α G  = ∫∫ (D_z²G + b D_zG)² w² sin(2θ)^{2-γ}` with `b z = (z-3)/(1+z)` (the radial
  T-adjoint combination);
* `TTint α G  = ∫∫ (∂_θ²G)² w² sin(2θ)^{2-γ}`.

Everything in this file is `sorry`-free.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.EllipticEst.OpenQDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.TT

set_option autoImplicit false

/-- The angular weight `σ_a(θ) = sin(2θ)^{2-γ(α)}` of the fixed-weight interpolation: the
exponent `2 - γ(α) = 1 - α/10` lies in `[0.975, 1)`, so the weight is bounded on `Iθ` and
vanishes at both endpoints.  This is the weight carried by the left-hand side of `interpGamma`. -/
def sigA (α θ : ℝ) : ℝ := (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α)

/-- The T-adjoint coefficient `b z = (z-3)/(1+z)`, `|b| ≤ 3`. -/
def bcoef (z : ℝ) : ℝ := (z - 3) / (1 + z)

/-- `Xint α G = ∫∫ (D_z∂_θG)² w² σ_a`: the left-hand side of the interpolation. -/
def Xint (α : ℝ) (G : ℝ → ℝ → ℝ) : ℝ :=
  ∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
    (Work.Spaces.Dz (Work.Spaces.pth G) z θ) ^ 2 * (Work.Spaces.w z) ^ 2 * sigA α θ

/-- `DDint α G = ∫∫ (D_z²G + b D_zG)² w² σ_a`: the radial slot produced by the radial
integration by parts. -/
def DDint (α : ℝ) (G : ℝ → ℝ → ℝ) : ℝ :=
  ∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
    (Work.Spaces.Dz (Work.Spaces.Dz G) z θ + bcoef z * Work.Spaces.Dz G z θ) ^ 2
      * (Work.Spaces.w z) ^ 2 * sigA α θ

/-- `TTint α G = ∫∫ (∂_θ²G)² w² σ_a`: the angular slot. -/
def TTint (α : ℝ) (G : ℝ → ℝ → ℝ) : ℝ :=
  ∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
    (Work.Spaces.pthIter 2 G z θ) ^ 2 * (Work.Spaces.w z) ^ 2 * sigA α θ

/-! ## Elementary facts about the angular weights -/

theorem sin_two_nonneg_of_mem_Iθ {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) : 0 ≤ Real.sin (2 * θ) :=
  Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])

theorem sin_two_pos_of_mem_Ioo {θ : ℝ} (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    0 < Real.sin (2 * θ) :=
  Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])

theorem gam_sub_two_exponent (α : ℝ) : 2 - Work.Spaces.gam α = 1 - α / 10 := by
  rw [Work.Spaces.gam]; ring

/-- On `Iθ` the weight `σ_a = sin(2θ)^{2-γ}` is nonnegative. -/
theorem sigA_nonneg (α θ : ℝ) (hθ : θ ∈ Work.Spaces.Iθ) : 0 ≤ sigA α θ :=
  Real.rpow_nonneg (sin_two_nonneg_of_mem_Iθ hθ) _

/-- On the open interval the weight `σ_a` is strictly positive. -/
theorem sigA_pos (α θ : ℝ) (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) : 0 < sigA α θ :=
  Real.rpow_pos_of_pos (sin_two_pos_of_mem_Ioo hθ) _

/-- On `Iθ` the weight `σ_a` is bounded by `1` (as `2 - γ ≥ 0`). -/
theorem sigA_le_one {α θ : ℝ} (hα : α ≤ 10) (hθ : θ ∈ Work.Spaces.Iθ) : sigA α θ ≤ 1 := by
  have hs0 : 0 ≤ Real.sin (2 * θ) := sin_two_nonneg_of_mem_Iθ hθ
  have hs1 : Real.sin (2 * θ) ≤ 1 := Real.sin_le_one _
  have hexp : 0 ≤ 2 - Work.Spaces.gam α := by
    rw [gam_sub_two_exponent]; linarith
  simpa [sigA] using Real.rpow_le_one hs0 hs1 hexp

/-- **The key weight comparison.**  For `α ≤ 1` one has `sin(2θ)^{2-γ} ≤ sin(2θ)^{-η}` on `Iθ`:
the light weight of the interpolation is dominated by the heavy weight `σ_η` of the `ℋ^k`
norms.  (`2 - γ ≥ -η` because `γ = 1 + α/10 ≤ 2 + η`.) -/
theorem sigA_le_sEta {α θ : ℝ} (hα : α ≤ 1) (hθ : θ ∈ Work.Spaces.Iθ) :
    sigA α θ ≤ (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) := by
  have hs0 : 0 ≤ Real.sin (2 * θ) := sin_two_nonneg_of_mem_Iθ hθ
  rcases eq_or_lt_of_le hs0 with h0 | hpos
  · -- at the two endpoints both weights vanish
    rw [sigA, ← h0]
    refine le_of_eq ?_
    rw [Real.zero_rpow (by rw [gam_sub_two_exponent]; linarith),
      Real.zero_rpow (by rw [Work.Spaces.eta]; norm_num)]
  · have hs1 : Real.sin (2 * θ) ≤ 1 := Real.sin_le_one _
    have hgam : Work.Spaces.gam α ≤ 2 + Work.Spaces.eta := by
      rw [Work.Spaces.gam, Work.Spaces.eta]; linarith
    refine Real.rpow_le_rpow_of_exponent_ge hpos hs1 ?_
    linarith

/-- The squared half-weight identity `(sin(2θ)^{(2-γ)/2})² = sin(2θ)^{2-γ}`. -/
theorem sin_rpow_half_sq {α θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    ((Real.sin (2 * θ)) ^ ((2 - Work.Spaces.gam α) / 2)) ^ 2 = sigA α θ := by
  have hs : 0 ≤ Real.sin (2 * θ) := sin_two_nonneg_of_mem_Iθ hθ
  have h2 : ((Real.sin (2 * θ)) ^ ((2 - Work.Spaces.gam α) / 2)) ^ 2
      = (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α) := by
    calc ((Real.sin (2 * θ)) ^ ((2 - Work.Spaces.gam α) / 2)) ^ 2
        = ((Real.sin (2 * θ)) ^ ((2 - Work.Spaces.gam α) / 2)) ^ (2 : ℝ) :=
          (Real.rpow_natCast _ 2).symm
      _ = (Real.sin (2 * θ)) ^ (((2 - Work.Spaces.gam α) / 2) * 2) :=
          (Real.rpow_mul hs _ _).symm
      _ = (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α) := by
          congr 1; ring
  rw [sigA, h2]

/-- The squared half-weight identity `(sin(2θ)^{η/2})² = sin(2θ)^{η}`. -/
theorem sin_rpow_half_sq_eta {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    ((Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)) ^ 2
      = (Real.sin (2 * θ)) ^ Work.Spaces.eta := by
  have hs : 0 ≤ Real.sin (2 * θ) := sin_two_nonneg_of_mem_Iθ hθ
  calc ((Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)) ^ 2
      = ((Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)) ^ (2 : ℝ) :=
        (Real.rpow_natCast _ 2).symm
    _ = (Real.sin (2 * θ)) ^ ((Work.Spaces.eta / 2) * 2) := (Real.rpow_mul hs _ _).symm
    _ = (Real.sin (2 * θ)) ^ Work.Spaces.eta := by congr 1; ring

/-- **The left-hand side is `Xint`.** -/
theorem L2Sq_eq_Xint (α : ℝ) (G : ℝ → ℝ → ℝ) :
    Work.Spaces.L2Sq (fun z θ => Work.Spaces.Dz (Work.Spaces.pth G) z θ
        * (Real.sin (2 * θ)) ^ ((2 - Work.Spaces.gam α) / 2) * Work.Spaces.w z)
      = Xint α G := by
  rw [Work.Spaces.L2Sq, Xint]
  refine MeasureTheory.setIntegral_congr_fun measurableSet_Ici (fun z _ => ?_)
  refine MeasureTheory.setIntegral_congr_fun measurableSet_Icc (fun θ hθ => ?_)
  rw [mul_pow, mul_pow, sin_rpow_half_sq (α := α) hθ]
  ring

/-- At `k = 0` the `ℋ^k`-integrand is the single square `(f · w / sin(2θ)^{η/2})²`. -/
theorem hkIntegrand_zero_eq (α : ℝ) (f : ℝ → ℝ → ℝ) (z θ : ℝ) :
    Work.Spaces.HkIntegrand α 0 f z θ
      = (f z θ * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 := by
  simp [Work.Spaces.HkIntegrand]

/-- **The `k = 0` integrand is `f² w² σ_η`.** -/
theorem hkIntegrand_zero_eq' (α : ℝ) (f : ℝ → ℝ → ℝ) {z θ : ℝ}
    (hθ : θ ∈ Work.Spaces.Iθ) :
    Work.Spaces.HkIntegrand α 0 f z θ
      = (f z θ) ^ 2 * (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) := by
  have hs : 0 ≤ Real.sin (2 * θ) := sin_two_nonneg_of_mem_Iθ hθ
  have h1 : (((Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))⁻¹) ^ 2
      = ((Real.sin (2 * θ)) ^ Work.Spaces.eta)⁻¹ := by
    rw [inv_pow, sin_rpow_half_sq_eta hθ]
  rw [hkIntegrand_zero_eq, div_eq_mul_inv, mul_pow, mul_pow, h1, ← Real.rpow_neg hs]
  ring

/-- **`HkSq α 0 f` is the `σ_η`-weighted iterated integral of `f²`.** -/
theorem HkSq_zero_eq_integral (α : ℝ) (f : ℝ → ℝ → ℝ) :
    Work.Spaces.HkSq α 0 f
      = ∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
          (f z θ) ^ 2 * (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) := by
  rw [Work.Spaces.HkSq]
  refine MeasureTheory.setIntegral_congr_fun measurableSet_Ici (fun z _ => ?_)
  exact MeasureTheory.setIntegral_congr_fun measurableSet_Icc
    (fun θ hθ => hkIntegrand_zero_eq' α f hθ)

/-! ## Dominating the light-weight integrals by the heavy-weight ones

The three `ℋ⁰`-slots of `interpGamma` are integrals against `σ_η = sin(2θ)^{-η}`, and `HkMem`
makes them honest.  Because `σ_a ≤ σ_η` pointwise on `Iθ`, every nonnegative integrand has its
`σ_a`-integral bounded by the `σ_η`-one; this is the only place where the two weights are
compared.
-/

theorem aemeasurable_sigA (α : ℝ) (hα : α ≤ 10) :
    AEMeasurable (fun θ : ℝ => sigA α θ) (volume.restrict Work.Spaces.Iθ) := by
  have hcont : ContinuousOn (fun θ : ℝ => sigA α θ) Work.Spaces.Iθ := by
    have hsin : ContinuousOn (fun θ : ℝ => Real.sin (2 * θ)) Work.Spaces.Iθ :=
      (Real.continuous_sin.comp (continuous_const.mul continuous_id)).continuousOn
    refine hsin.rpow_const (fun x hx => Or.inr ?_)
    have := Work.Spaces.gam_sub_one α
    linarith
  exact hcont.aemeasurable measurableSet_Icc

/-- **Slicewise domination.**  For a nonnegative angular function whose product with the heavy
weight `σ_η` is integrable, the product with the light weight `σ_a` is integrable and its
integral is bounded by the heavy one. -/
theorem integral_sigA_le_sEta {α : ℝ} (hα : α ≤ 1) {f : ℝ → ℝ}
    (hη : IntegrableOn (fun θ : ℝ => f θ * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
      Work.Spaces.Iθ)
    (haf : AEStronglyMeasurable f (volume.restrict Work.Spaces.Iθ))
    (hf0 : ∀ θ ∈ Work.Spaces.Iθ, 0 ≤ f θ) :
    (∫ θ in Work.Spaces.Iθ, f θ * sigA α θ)
      ≤ ∫ θ in Work.Spaces.Iθ, f θ * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) := by
  have hle : ∀ θ ∈ Work.Spaces.Iθ, f θ * sigA α θ
      ≤ f θ * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) := fun θ hθ =>
    mul_le_mul_of_nonneg_left (sigA_le_sEta hα hθ) (hf0 θ hθ)
  have haesm : AEStronglyMeasurable (fun θ : ℝ => f θ * sigA α θ)
      (volume.restrict Work.Spaces.Iθ) :=
    haf.mul (aemeasurable_sigA α (by linarith)).aestronglyMeasurable
  have hg : IntegrableOn (fun θ : ℝ => f θ * sigA α θ) Work.Spaces.Iθ := by
    refine Integrable.mono' hη haesm ?_
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with θ hθ
    have h0 : 0 ≤ sigA α θ := sigA_nonneg α θ hθ
    have h1 : 0 ≤ f θ * sigA α θ := mul_nonneg (hf0 θ hθ) h0
    have h2 : 0 ≤ f θ * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) :=
      mul_nonneg (hf0 θ hθ) (Real.rpow_nonneg (sin_two_nonneg_of_mem_Iθ hθ) _)
    simpa only [Real.norm_of_nonneg h1, Real.norm_of_nonneg h2] using hle θ hθ
  exact integral_mono_ae hg hη (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc hle)

end Work.FTS.EllipticEst.TT
