import Mathlib
import Submission.Work.KMTPlan.A6.weylAvg_shift_eq_halfSym

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Work.KMTAreas.A7

noncomputable section

open MeasureTheory Finset
open scoped BigOperators

/-! ## Elementary facts about the character `ee` -/

/-- `ee x = exp (2πix)` is continuous. -/
lemma continuous_ee : Continuous ee := by
  unfold ee
  fun_prop

/-- `ee` is an additive character (local copy; the defining module was pruned from the closure). -/
private lemma ee_add (x y : ℝ) : ee (x + y) = ee x * ee y := by
  rw [ee, ee, ee, ← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- The character of a difference: `ee a * ee (-b) = ee (a + -b)`. -/
lemma ee_mul_ee_neg (a b : ℝ) : ee a * ee (-b) = ee (a + -b) := by
  rw [← ee_add]

/-- The character of a sum of two blocks: `ee (-(c + d)) = ee (-c) * ee (-d)`. -/
lemma ee_neg_add (c d : ℝ) : ee (-(c + d)) = ee (-c) * ee (-d) := by
  rw [show -(c + d) = -c + -d by ring, ee_add]

/-- Distributing a product over a finite sum, with the constant `k` kept inside the summand.
`a * (k * ∑ n, M n) * e = ∑ n, k * (a * M n * e)`. -/
lemma mul_const_sum_mul {ι : Type*} (s : Finset ι) (a k e : ℂ) (M : ι → ℂ) :
    a * (k * ∑ n ∈ s, M n) * e = ∑ n ∈ s, k * (a * M n * e) := by
  rw [Finset.mul_sum, Finset.mul_sum, Finset.sum_mul]
  exact Finset.sum_congr rfl (fun n _ => by ring)

/-! ## The two one-dimensional factors of the `n`-th summand -/

/-- The `ξ₁`-factor of the `n`-th summand of `weylAvg`, twisted by `ee (-j ξ₁)`. -/
noncomputable def thetaU (φ : ℝ → ℂ) (j : ℤ) : ℕ → ℝ → ℂ :=
  fun n ξ => φ ξ * (ee (ξ * ((n : ℤ) : ℝ)) * ee (-((j : ℝ) * ξ)))

/-- The `ξ₂`-factor of the `n`-th summand of `weylAvg`, twisted by `ee (-j ξ₂)`. -/
noncomputable def thetaV (ψ : ℝ → ℂ) (P : Polynomial ℤ) (j : ℤ) : ℕ → ℝ → ℂ :=
  fun n ξ => ψ ξ * (ee (ξ * PevalR P ((n : ℤ) : ℝ)) * ee (-((j : ℝ) * ξ)))

/-- The arithmetic factor of the `n`-th summand of `weylAvg`. -/
noncomputable def thetaC (P : Polynomial ℤ) (α₁ α₂ : Work.Analysis.IonescuWainger.Circle) :
    ℕ → ℂ :=
  fun n => fourier (T := 1) (n : ℤ) α₁ * fourier (T := 1) (P.eval (n : ℤ)) α₂

/-! ## Integrability -/

lemma integrable_thetaU {φ : ℝ → ℂ} (hφ : Integrable φ) (j : ℤ) (n : ℕ) :
    Integrable (thetaU φ j n) := by
  rw [show thetaU φ j n
      = fun ξ : ℝ => φ ξ * (ee (ξ * ((n : ℤ) : ℝ)) * ee (-((j : ℝ) * ξ))) from rfl]
  refine hφ.mul_bdd (c := 1) ?_ ?_
  · exact ((continuous_ee.comp (continuous_id.mul continuous_const)).mul
      (continuous_ee.comp (continuous_const.mul continuous_id).neg)).aestronglyMeasurable
  · filter_upwards with ξ
    rw [norm_mul, norm_ee, norm_ee, mul_one]

lemma integrable_thetaV {ψ : ℝ → ℂ} (hψ : Integrable ψ) (P : Polynomial ℤ) (j : ℤ) (n : ℕ) :
    Integrable (thetaV ψ P j n) := by
  rw [show thetaV ψ P j n
      = fun ξ : ℝ => ψ ξ * (ee (ξ * PevalR P ((n : ℤ) : ℝ)) * ee (-((j : ℝ) * ξ))) from rfl]
  refine hψ.mul_bdd (c := 1) ?_ ?_
  · exact ((continuous_ee.comp (continuous_id.mul continuous_const)).mul
      (continuous_ee.comp (continuous_const.mul continuous_id).neg)).aestronglyMeasurable
  · filter_upwards with ξ
    rw [norm_mul, norm_ee, norm_ee, mul_one]

/-! ## The one-dimensional integrals -/

lemma integral_thetaU (φ : ℝ → ℂ) (j : ℤ) (n : ℕ) :
    ∫ θ : ℝ, thetaU φ j n θ = cw φ (j - (n : ℤ)) := by
  rw [cw]
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun θ => ?_)
  rw [show thetaU φ j n θ
      = φ θ * (ee (θ * ((n : ℤ) : ℝ)) * ee (-((j : ℝ) * θ))) from rfl]
  rw [ee_mul_ee_neg]
  exact congrArg (fun z : ℂ => φ θ * z) (congrArg ee (by push_cast; ring))

lemma integral_thetaV (ψ : ℝ → ℂ) (P : Polynomial ℤ) (j : ℤ) (n : ℕ) :
    ∫ θ : ℝ, thetaV ψ P j n θ = cw ψ (j - P.eval (n : ℤ)) := by
  rw [cw]
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun θ => ?_)
  rw [show thetaV ψ P j n θ
      = ψ θ * (ee (θ * PevalR P ((n : ℤ) : ℝ)) * ee (-((j : ℝ) * θ))) from rfl]
  rw [Work.KMTPlan.A6.symp_PevalR_intCast P (n : ℤ)]
  rw [ee_mul_ee_neg]
  exact congrArg (fun z : ℂ => ψ θ * z) (congrArg ee (by push_cast; ring))

/-! ## Fubini for a finite sum of products -/

/-- For a finite family of products of an `x`-function and a `y`-function,
`∫ x, ∫ y, ∑_n c n (u n x * v n y) = ∑_n c n (∫ u n) (∫ v n)`. -/
theorem integral_integral_finset_sum_prod {ι : Type*} (s : Finset ι) (c : ι → ℂ)
    (u v : ι → ℝ → ℂ) (hu : ∀ n ∈ s, Integrable (u n)) (hv : ∀ n ∈ s, Integrable (v n)) :
    (∫ θ₁ : ℝ, ∫ θ₂ : ℝ, ∑ n ∈ s, c n * (u n θ₁ * v n θ₂))
      = ∑ n ∈ s, c n * (∫ θ₁ : ℝ, u n θ₁) * (∫ θ₂ : ℝ, v n θ₂) := by
  have h1 : ∀ θ₁ : ℝ, (∫ θ₂ : ℝ, ∑ n ∈ s, c n * (u n θ₁ * v n θ₂))
      = ∑ n ∈ s, c n * (u n θ₁ * ∫ θ₂ : ℝ, v n θ₂) := by
    intro θ₁
    rw [MeasureTheory.integral_finsetSum s
      (fun n hn => ((hv n hn).const_mul (u n θ₁)).const_mul (c n))]
    refine Finset.sum_congr rfl (fun n _ => ?_)
    rw [MeasureTheory.integral_const_mul (c n), MeasureTheory.integral_const_mul (u n θ₁)]
  calc
    (∫ θ₁ : ℝ, ∫ θ₂ : ℝ, ∑ n ∈ s, c n * (u n θ₁ * v n θ₂))
        = ∫ θ₁ : ℝ, ∑ n ∈ s, c n * (u n θ₁ * ∫ θ₂ : ℝ, v n θ₂) :=
          MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall h1)
    _ = ∑ n ∈ s, c n * (∫ θ₁ : ℝ, u n θ₁) * (∫ θ₂ : ℝ, v n θ₂) := by
        rw [MeasureTheory.integral_finsetSum s
          (fun n hn => ((hu n hn).mul_const (∫ θ₂ : ℝ, v n θ₂)).const_mul (c n))]
        refine Finset.sum_congr rfl (fun n _ => ?_)
        rw [MeasureTheory.integral_const_mul (c n),
          MeasureTheory.integral_mul_const (∫ θ₂ : ℝ, v n θ₂)]
        ring

/-! ## The expanded integrand -/

/-- **The integrand of `theta_double_cw`, expanded into a finite sum of products of a
`θ₁`-factor and a `θ₂`-factor.** -/
lemma weylAvg_integrand_eq (P : Polynomial ℤ) (N : ℕ) (j₁ j₂ : ℤ)
    (α₁ α₂ : Work.Analysis.IonescuWainger.Circle) (φ ψ : ℝ → ℂ) (θ₁ θ₂ : ℝ) :
    φ θ₁ * ψ θ₂ * weylAvg P N α₁ α₂ θ₁ θ₂ * ee (-((j₁ : ℝ) * θ₁ + (j₂ : ℝ) * θ₂))
      = ∑ n ∈ Finset.Ioc (N / 2) N,
          ((N : ℂ)⁻¹ * thetaC P α₁ α₂ n) * (thetaU φ j₁ n θ₁ * thetaV ψ P j₂ n θ₂) := by
  simp only [weylAvg]
  rw [mul_const_sum_mul (Finset.Ioc (N / 2) N) (φ θ₁ * ψ θ₂) ((N : ℂ)⁻¹)
        (ee (-((j₁ : ℝ) * θ₁ + (j₂ : ℝ) * θ₂)))
        (fun n => momPhase P N α₁ α₂ θ₁ θ₂ (n : ℤ))]
  refine Finset.sum_congr rfl (fun n _ => ?_)
  simp only [momPhase, thetaC, thetaU, thetaV]
  rw [ee_add (θ₁ * ((n : ℤ) : ℝ)) (θ₂ * PevalR P ((n : ℤ) : ℝ)),
      ee_neg_add ((j₁ : ℝ) * θ₁) ((j₂ : ℝ) * θ₂)]
  ring

/-! ## The main identity -/

/-- **The double integral of the discrete average against a pair of bumps.**

For integrable bumps `φ`, `ψ : ℝ → ℂ` and arithmetic frequencies `α₁`, `α₂ ∈ ℝ/ℤ`, the iterated
integral of `φ(θ₁) ψ(θ₂) · weylAvg P N α₁ α₂ θ₁ θ₂ · e(-(j₁θ₁ + j₂θ₂))` over `ℝ²` equals the
finite average `N⁻¹ ∑_{n ∈ Ioc (N/2) N}` over `n ∈ {N/2+1, …, N}` of

`fourier n α₁ · fourier (P.eval n) α₂ · cw φ (j₁-n) · cw ψ (j₂-P.eval n)`.

Here `weylAvg P N α₁ α₂ ξ₁ ξ₂ = N⁻¹ ∑_{n ∈ Ioc (N/2) N} momPhase P N α₁ α₂ ξ₁ ξ₂ n` and
`momPhase P N α₁ α₂ ξ₁ ξ₂ n = fourier n α₁ * fourier (P.eval n) α₂ * ee (ξ₁ n + ξ₂ PevalR P n)`,
`ee x = exp (2πix)`, `cw m j = ∫ θ, m θ * ee (-(j:ℝ) * θ)`, all from
`Submission/Work/KMTAreas/A7/ModelApproxDefs.lean` and `.../Large/Defs.lean`. -/
theorem theta_double_cw (P : Polynomial ℤ) (N : ℕ) (j₁ j₂ : ℤ) {φ ψ : ℝ → ℂ}
    (hφ : MeasureTheory.Integrable φ) (hψ : MeasureTheory.Integrable ψ)
    (α₁ α₂ : Work.Analysis.IonescuWainger.Circle) :
    (∫ θ₁ : ℝ, ∫ θ₂ : ℝ,
        φ θ₁ * ψ θ₂ * Work.KMTAreas.A7.weylAvg P N α₁ α₂ θ₁ θ₂
          * Work.KMTAreas.A7.ee (-((j₁ : ℝ) * θ₁ + (j₂ : ℝ) * θ₂)))
      = ((N : ℂ))⁻¹ * ∑ n ∈ Finset.Ioc (N / 2) N,
          fourier (T := 1) (n : ℤ) α₁ * fourier (T := 1) (P.eval (n : ℤ)) α₂
            * Work.KMTAreas.A7.cw φ (j₁ - (n : ℤ)) * Work.KMTAreas.A7.cw ψ (j₂ - P.eval (n : ℤ)) := by
  calc
    (∫ θ₁ : ℝ, ∫ θ₂ : ℝ,
        φ θ₁ * ψ θ₂ * weylAvg P N α₁ α₂ θ₁ θ₂ * ee (-((j₁ : ℝ) * θ₁ + (j₂ : ℝ) * θ₂)))
        = ∫ θ₁ : ℝ, ∫ θ₂ : ℝ, ∑ n ∈ Finset.Ioc (N / 2) N,
            ((N : ℂ)⁻¹ * thetaC P α₁ α₂ n) * (thetaU φ j₁ n θ₁ * thetaV ψ P j₂ n θ₂) := by
          refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun θ₁ => ?_)
          refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun θ₂ => ?_)
          exact weylAvg_integrand_eq P N j₁ j₂ α₁ α₂ φ ψ θ₁ θ₂
    _ = ∑ n ∈ Finset.Ioc (N / 2) N,
          ((N : ℂ)⁻¹ * thetaC P α₁ α₂ n) * (∫ θ₁ : ℝ, thetaU φ j₁ n θ₁)
            * (∫ θ₂ : ℝ, thetaV ψ P j₂ n θ₂) :=
        integral_integral_finset_sum_prod (Finset.Ioc (N / 2) N)
          (fun n => (N : ℂ)⁻¹ * thetaC P α₁ α₂ n) (thetaU φ j₁) (thetaV ψ P j₂)
          (fun n _ => integrable_thetaU hφ j₁ n) (fun n _ => integrable_thetaV hψ P j₂ n)
    _ = ((N : ℂ))⁻¹ * ∑ n ∈ Finset.Ioc (N / 2) N,
          fourier (T := 1) (n : ℤ) α₁ * fourier (T := 1) (P.eval (n : ℤ)) α₂
            * cw φ (j₁ - (n : ℤ)) * cw ψ (j₂ - P.eval (n : ℤ)) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun n _ => ?_)
        rw [integral_thetaU, integral_thetaV]
        simp only [thetaC]
        ring

end

end Work.KMTAreas.A7
