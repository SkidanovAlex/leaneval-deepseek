/-
# Elementaries for the `§6` fibre-coefficient identity (`hiFibreCoeff_ident`)

Generic helpers used by the proof of the arithmetic-quadrature identity
`Work.KMTAreas.A7.hiFibreCoeff_ident`:

* the algebra of the character `ee x = exp (2π i x)`: `ee_add`, `norm_ee`;
* the iterated-integral collapse `∫θ₁ ∫θ₂ f θ₁ g θ₂ = (∫ f)(∫ g)` for the Lebesgue
  integral on `ℝ` (unconditional in Mathlib's Bochner integral);
* `bumpFT` as an integral with the argument on the left (`∫ θ, φ θ * ee (θ * y)`);
* integrability of `φ · ee (· * y)` when `φ` is integrable;
* periodicity of the arithmetic character `acCoefW` in the modulus `q`;
* the interval substitution `∫_t φ (N t) = N⁻¹ ∫_u φ(u)`.
-/
import Mathlib
import Submission.Work.KMTAreas.A7.HiFibreDefs
import Submission.Work.A7.varphiN_integrable_measurable
import Submission.Work.A7.varphitildeN_integrable_measurable

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Work.KMTAreas.A7

noncomputable section

open MeasureTheory Polynomial Finset Filter Topology
open scoped ENNReal NNReal BigOperators
open PointwiseErgodicTheorems Submission.PointwiseErgodicTheorems
open Work.Analysis.IonescuWainger

/-! ## The character `ee` -/

/-- `ee` is continuous. -/
lemma continuous_ee : Continuous ee := by
  unfold ee
  exact Complex.continuous_exp.comp (continuous_const.mul (Complex.continuous_ofReal))

/-- `‖ee x‖ = 1`. -/
lemma norm_ee (x : ℝ) : ‖ee x‖ = 1 := by
  unfold ee
  rw [Complex.norm_exp]
  have h : (2 * (Real.pi : ℂ) * Complex.I * (x : ℂ)).re = 0 := by
    simp [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im]
  rw [h, Real.exp_zero]

/-- `ee 0 = 1`. -/
lemma ee_zero : ee 0 = 1 := by simp [ee]

/-- `ee (x + y) = ee x * ee y`. -/
lemma ee_add (x y : ℝ) : ee (x + y) = ee x * ee y := by
  unfold ee
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- `ee (-x) = (ee x)⁻¹`. -/
lemma ee_neg (x : ℝ) : ee (-x) = (ee x)⁻¹ := by
  unfold ee
  rw [show 2 * ↑Real.pi * Complex.I * ↑(-x) = -(2 * ↑Real.pi * Complex.I * ↑x) by
    push_cast; ring]
  rw [Complex.exp_neg]

/-- `ee (-(x + y)) = ee (-x) * ee (-y)`. -/
lemma ee_neg_add (x y : ℝ) : ee (-(x + y)) = ee (-x) * ee (-y) := by
  rw [show -(x + y) = (-x) + (-y) by ring, ee_add]

/-! ## `bumpFT` with the argument on the left -/

/-- `bumpFT` written with the frequency argument on the left. -/
lemma bumpFT_eq (φ : ℝ → ℂ) (y : ℝ) :
    bumpFT φ y = ∫ θ : ℝ, φ θ * ee (θ * y) := by
  rw [bumpFT]
  refine integral_congr_ae (Filter.Eventually.of_forall (fun θ => ?_))
  show φ θ * ee (y * θ) = φ θ * ee (θ * y)
  rw [show y * θ = θ * y by ring]

/-! ## The iterated integral of a separated product -/

/-- **The iterated integral of a separated product.**  For the Lebesgue integral on `ℝ`,
`∫θ₁ ∫θ₂ f θ₁ g θ₂ = (∫ f)(∫ g)`.  (No integrability hypothesis: both sides are the
Bochner integral, and `MeasureTheory.integral_const_mul`/`integral_mul_const` are
unconditional.) -/
theorem integral_integral_mul_sep (f g : ℝ → ℂ) :
    (∫ θ₁ : ℝ, ∫ θ₂ : ℝ, f θ₁ * g θ₂) = (∫ θ₁ : ℝ, f θ₁) * (∫ θ₂ : ℝ, g θ₂) := by
  have h1 : ∀ θ₁ : ℝ, (∫ θ₂ : ℝ, f θ₁ * g θ₂) = f θ₁ * (∫ θ₂ : ℝ, g θ₂) :=
    fun θ₁ => integral_const_mul (f θ₁) g
  simp_rw [h1]
  exact integral_mul_const _ f

/-! ## Integrability of `φ · ee (· * y)` -/

/-- If `φ` is integrable then so is `θ ↦ φ θ * ee (θ * y)`. -/
lemma integrable_mul_ee {φ : ℝ → ℂ} (hφ : Integrable φ) (y : ℝ) :
    Integrable (fun θ : ℝ => φ θ * ee (θ * y)) :=
  hφ.mul_bdd ((continuous_ee.comp (continuous_id.mul continuous_const)).aestronglyMeasurable)
    (ae_of_all _ (fun θ => by rw [norm_ee]))

/-- Integrability of `varphiN N k` times a character. -/
lemma integrable_varphiN_mul_ee (N k : ℕ) (y : ℝ) :
    Integrable (fun θ : ℝ => varphiN N k θ * ee (θ * y)) :=
  integrable_mul_ee (Work.A7.varphiN_integrable_measurable N k).1 y

/-- Integrability of `varphitildeN d N k` times a character. -/
lemma integrable_varphitildeN_mul_ee (d N k : ℕ) (y : ℝ) :
    Integrable (fun θ : ℝ => varphitildeN d N k θ * ee (θ * y)) :=
  integrable_mul_ee (Work.A7.varphitildeN_integrable_measurable d N k).1 y

/-- Measurability of `varphiN N k` times a character. -/
lemma aestronglyMeasurable_varphiN_mul_ee (N k : ℕ) (y : ℝ) :
    AEStronglyMeasurable (fun θ : ℝ => varphiN N k θ * ee (θ * y)) :=
  ((Work.A7.varphiN_integrable_measurable N k).2.aestronglyMeasurable).mul
    ((continuous_ee.comp (continuous_id.mul continuous_const)).aestronglyMeasurable)

/-- Measurability of `varphitildeN d N k` times a character. -/
lemma aestronglyMeasurable_varphitildeN_mul_ee (d N k : ℕ) (y : ℝ) :
    AEStronglyMeasurable (fun θ : ℝ => varphitildeN d N k θ * ee (θ * y)) :=
  ((Work.A7.varphitildeN_integrable_measurable d N k).2.aestronglyMeasurable).mul
    ((continuous_ee.comp (continuous_id.mul continuous_const)).aestronglyMeasurable)

/-! ## Periodicity of the arithmetic character -/

/-- `acCoefW` agrees with `Work.A7.arithW`. -/
lemma acCoefW_eq_arithW (P : Polynomial ℤ) (α₁ α₂ : Work.Analysis.IonescuWainger.Circle) (n : ℤ) :
    acCoefW P α₁ α₂ n = Work.A7.arithW P α₁ α₂ n := rfl

/-- **`q`-periodicity of the arithmetic character**: if `q • α₁ = q • α₂ = 0` then
`acCoefW P α₁ α₂ (n + q) = acCoefW P α₁ α₂ n`. -/
lemma acCoefW_period (P : Polynomial ℤ) (q : ℕ) (α₁ α₂ : Work.Analysis.IonescuWainger.Circle)
    (h₁ : q • α₁ = 0) (h₂ : q • α₂ = 0) (n : ℤ) :
    acCoefW P α₁ α₂ (n + q) = acCoefW P α₁ α₂ n :=
  Work.A7.arithW_period P q α₁ α₂ h₁ h₂ n

/-- `acCoefW P α₁ α₂ (n + q * m) = acCoefW P α₁ α₂ n`. -/
lemma acCoefW_period_mul (P : Polynomial ℤ) (q : ℕ) (α₁ α₂ : Work.Analysis.IonescuWainger.Circle)
    (h₁ : q • α₁ = 0) (h₂ : q • α₂ = 0) (n m : ℤ) :
    acCoefW P α₁ α₂ (n + q * m) = acCoefW P α₁ α₂ n :=
  Work.A7.arithW_period_mul P q α₁ α₂ h₁ h₂ n m

/-- **The natural-number form of the periodicity**: for `0 < q` a period of both characters,
`acCoefW P α₁ α₂ n = acCoefW P α₁ α₂ (n % q)`. -/
lemma acCoefW_nat_mod (P : Polynomial ℤ) (q : ℕ) (hq : 0 < q)
    (α₁ α₂ : Work.Analysis.IonescuWainger.Circle)
    (h₁ : q • α₁ = 0) (h₂ : q • α₂ = 0) (n : ℕ) :
    acCoefW P α₁ α₂ (n : ℤ) = acCoefW P α₁ α₂ ((n % q : ℕ) : ℤ) := by
  have h : (n : ℤ) = ((n % q : ℕ) : ℤ) + (q : ℤ) * ((n / q : ℕ) : ℤ) := by
    exact_mod_cast (Nat.mod_add_div n q).symm
  rw [h]
  exact acCoefW_period_mul P q α₁ α₂ h₁ h₂ ((n % q : ℕ) : ℤ) ((n / q : ℕ) : ℤ)

/-! ## `mZ` as an average of the arithmetic character -/

/-- **`mZ` is the average of the arithmetic character over a period**:
`m_Ẑ(α₁,α₂) = q⁻¹ ∑_{r<q} acCoefW P α₁ α₂ r`. -/
theorem mZ_eq_sum_acCoefW (P : Polynomial ℤ) (q : ℕ) (α₁ α₂ : Work.Analysis.IonescuWainger.Circle) :
    mZ P q α₁ α₂ = (q : ℂ)⁻¹ * ∑ r ∈ Finset.range q, acCoefW P α₁ α₂ (r : ℤ) := by
  simp only [mZ, acCoefW]

/-! ## The interval substitution `u = N t` -/

/-- **The interval substitution**: `∫_{1/2}^1 Ψ (N t) dt = N⁻¹ ∫_{N/2}^{N} Ψ(u) du`. -/
theorem intervalIntegral_comp_mul_N (N : ℕ) (hN : 1 ≤ N) (Ψ : ℝ → ℂ) :
    (∫ t in (1 / 2 : ℝ)..(1 : ℝ), Ψ ((N : ℝ) * t))
      = ((N : ℂ))⁻¹ * ∫ u in ((N : ℝ) / 2)..((N : ℝ)), Ψ u := by
  have hc : (N : ℝ) ≠ 0 := by positivity
  rw [intervalIntegral.integral_comp_mul_left Ψ hc]
  have h1 : (N : ℝ) * (1 / 2 : ℝ) = (N : ℝ) / 2 := by ring
  have h2 : (N : ℝ) * 1 = (N : ℝ) := by ring
  rw [h1, h2]
  rw [Complex.real_smul, Complex.ofReal_inv, Complex.ofReal_natCast]

end

end Work.KMTAreas.A7
