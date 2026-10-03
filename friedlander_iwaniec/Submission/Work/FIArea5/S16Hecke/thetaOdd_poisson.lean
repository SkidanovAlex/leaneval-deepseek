import Mathlib
import Submission.Work.FIArea5.S16Hecke.ThetaDefs
import Submission.Work.FIArea5.S16Hecke.thetaOdd_aux
import Submission.Work.FIArea5.S16.poisson_periodic_2d
import Submission.Work.FIArea5.S16.holoGaussian2d

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace Work.FIArea5.S16Hecke

open Finset
open scoped BigOperators
open Work.FIPlan

attribute [local instance] Classical.propDecidable

noncomputable section

/-! ## Elementary rewritings of the Gaussian kernels -/

theorem gnorm_cast_complex (z : GaussianInt) :
    ((gnorm z : ℕ) : ℂ) = (z.re : ℂ) ^ 2 + (z.im : ℂ) ^ 2 := by
  rw [← Complex.ofReal_natCast, gnorm_cast_real]
  push_cast
  ring

theorem cexp_neg_pi_sq (u : ℝ) (x : ℤ) :
    Complex.exp (-Real.pi * u * ((x : ℂ) ^ 2))
      = ((Real.exp (-(Real.pi * u) * (x : ℝ) ^ 2) : ℝ) : ℂ) := by
  rw [Complex.ofReal_exp]
  congr 1
  push_cast
  ring

theorem cexp_neg_pi_gnorm (u : ℝ) (p : ℤ × ℤ) :
    Complex.exp (-Real.pi * u * (gnorm (⟨p.1, p.2⟩ : GaussianInt) : ℝ))
      = ((Real.exp (-(Real.pi * u) * ((p.1 : ℝ) ^ 2 + (p.2 : ℝ) ^ 2)) : ℝ) : ℂ) := by
  rw [Complex.ofReal_exp]
  congr 1
  rw [gnorm_cast_real]
  push_cast
  ring

/-! ## Poisson summation for a single pair of exponents -/

theorem poisson_single_l (d : ℕ) (hd : 1 ≤ d) (chi : GaussianInt → ℂ)
    (hchi : IsCharMod4dStrict d chi) (m l : ℕ) (hl : l ≤ m) {u : ℝ} (hu : 0 < u) :
    (∑' p : ℤ × ℤ, chiOdd chi ⟨p.1, p.2⟩ *
        ((((p.1 : ℂ) ^ (m - l)) * Complex.exp (-Real.pi * u * ((p.1 : ℂ) ^ 2)))
          * (((p.2 : ℂ) ^ l) * Complex.exp (-Real.pi * u * ((p.2 : ℂ) ^ 2)))))
      = (1 / (((4 * d : ℕ) : ℂ) ^ 2)) *
          ∑' ξ : ℤ × ℤ, gaussSum d chi ⟨ξ.1, ξ.2⟩ *
            ((FourierTransform.fourier (fun x : ℝ => ((x : ℂ) ^ (m - l)) *
                Complex.exp (-Real.pi * u * (x : ℂ) ^ 2))) ((ξ.1 : ℝ) / ((4 * d : ℕ) : ℝ))
              * (FourierTransform.fourier (fun y : ℝ => ((y : ℂ) ^ l) *
                Complex.exp (-Real.pi * u * (y : ℂ) ^ 2))) ((ξ.2 : ℝ) / ((4 * d : ℕ) : ℝ))) := by
  have hq : 0 < 4 * d := by omega
  have hpois := Work.FIArea5.S16.poisson_periodic_2d (4 * d) hq (chiOdd chi)
    (chiOdd_periodic d chi hchi.1)
    (fun x : ℝ => ((x : ℂ) ^ (m - l)) * Complex.exp (-Real.pi * u * (x : ℂ) ^ 2))
    (fun y : ℝ => ((y : ℂ) ^ l) * Complex.exp (-Real.pi * u * (y : ℂ) ^ 2))
    (continuous_kernel u (m - l)) (continuous_kernel u l)
    (by norm_num : (1 : ℝ) < 2)
    (kernel_isBigO u hu (m - l) (b := 2)) (fourier_kernel_isBigO u hu (m - l) (b := 2))
    (kernel_isBigO u hu l (b := 2)) (fourier_kernel_isBigO u hu l (b := 2))
  have hgs : ∀ ξ : ℤ × ℤ, (∑ α ∈ (Finset.range (4 * d)).product (Finset.range (4 * d)),
        chiOdd chi ⟨α.1, α.2⟩ * Complex.exp (2 * Real.pi * Complex.I *
          ((((α.1 * ξ.1 + α.2 * ξ.2 : ℤ)) : ℂ) / ((4 * d : ℕ) : ℂ))))
      = gaussSum d chi ⟨ξ.1, ξ.2⟩ := by
    intro ξ
    rw [gaussSum]
    refine Finset.sum_congr rfl (fun α _ => ?_)
    by_cases h : isOddG (⟨α.1, α.2⟩ : GaussianInt)
    · rw [chiOdd, if_pos h, if_pos h]
    · rw [chiOdd, if_neg h, if_neg h, zero_mul]
  simp only [Complex.ofReal_intCast, Complex.ofReal_natCast] at hpois
  rw [hpois]
  congr 1
  apply tsum_congr
  intro ξ
  rw [hgs]



/-! ## Swapping a finite sum with an infinite sum -/

private lemma sum_tsum_swap (s : Finset ℕ) (F : ℕ → ℤ × ℤ → ℂ) (c : ℕ → ℂ) (C : ℂ)
    (hh : ∀ l ∈ s, Summable (fun ξ => c l * F l ξ)) :
    (∑ l ∈ s, c l * (C * ∑' ξ, F l ξ)) = C * ∑' ξ, ∑ l ∈ s, c l * F l ξ := by
  have h1 : (∑ l ∈ s, c l * (C * ∑' ξ, F l ξ)) = C * ∑ l ∈ s, c l * ∑' ξ, F l ξ := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun l _ => by ring_nf)
  have h3 : ∀ l ∈ s, c l * (∑' ξ, F l ξ) = ∑' ξ, c l * F l ξ := by
    intro l _
    rw [tsum_mul_left]
  have h2 : (∑ l ∈ s, c l * ∑' ξ, F l ξ) = ∑' ξ, ∑ l ∈ s, c l * F l ξ := by
    rw [Finset.sum_congr rfl h3, ← Summable.tsum_finsetSum hh]
  rw [h1, h2]

/-! ## The binomial expansion of the holomorphic weight -/

private lemma binomial_expansion (m : ℕ) (u : ℝ) (p : ℤ × ℤ) :
    ((⟨p.1, p.2⟩ : GaussianInt) : ℂ) ^ m
        * Complex.exp (-Real.pi * u * (gnorm (⟨p.1, p.2⟩ : GaussianInt) : ℝ))
      = ∑ l ∈ Finset.range (m + 1), ((m.choose l : ℂ) * Complex.I ^ l) *
          ((((p.1 : ℂ) ^ (m - l)) * Complex.exp (-Real.pi * u * ((p.1 : ℂ) ^ 2)))
            * (((p.2 : ℂ) ^ l) * Complex.exp (-Real.pi * u * ((p.2 : ℂ) ^ 2)))) := by
  rw [cexp_neg_pi_gnorm, GaussianInt.toComplex_def, cexp_neg_pi_sq, cexp_neg_pi_sq]
  have hE : ((Real.exp (-(Real.pi * u) * ((p.1 : ℝ) ^ 2 + (p.2 : ℝ) ^ 2)) : ℝ) : ℂ)
      = ((Real.exp (-(Real.pi * u) * (p.1 : ℝ) ^ 2) : ℝ) : ℂ)
        * ((Real.exp (-(Real.pi * u) * (p.2 : ℝ) ^ 2) : ℝ) : ℂ) := by
    rw [← Complex.ofReal_mul, ← Real.exp_add, Complex.ofReal_inj]
    congr 1
    ring
  have hkey : (∑ l ∈ Finset.range (m + 1),
        (p.1 : ℂ) ^ (m - l) * (p.2 : ℂ) ^ l * Complex.I ^ l * (m.choose l : ℂ))
      = ((p.1 : ℂ) + (p.2 : ℂ) * Complex.I) ^ m := by
    have h2 : ((p.1 : ℂ) + (p.2 : ℂ) * Complex.I) ^ m
        = ∑ l ∈ Finset.range (m + 1),
            ((p.2 : ℂ) * Complex.I) ^ l * (p.1 : ℂ) ^ (m - l) * (m.choose l : ℂ) := by
      rw [add_comm (p.1 : ℂ), add_pow]
    rw [h2]
    refine Finset.sum_congr rfl (fun l _ => ?_)
    rw [mul_pow]
    ring
  rw [hE]
  calc ((p.1 : ℂ) + (p.2 : ℂ) * Complex.I) ^ m
        * (((Real.exp (-(Real.pi * u) * (p.1 : ℝ) ^ 2) : ℝ) : ℂ)
            * ((Real.exp (-(Real.pi * u) * (p.2 : ℝ) ^ 2) : ℝ) : ℂ))
      = (∑ l ∈ Finset.range (m + 1),
          (p.1 : ℂ) ^ (m - l) * (p.2 : ℂ) ^ l * Complex.I ^ l * (m.choose l : ℂ))
        * (((Real.exp (-(Real.pi * u) * (p.1 : ℝ) ^ 2) : ℝ) : ℂ)
            * ((Real.exp (-(Real.pi * u) * (p.2 : ℝ) ^ 2) : ℝ) : ℂ)) := by rw [hkey]
    _ = ∑ l ∈ Finset.range (m + 1),
          ((m.choose l : ℂ) * Complex.I ^ l) *
            ((((p.1 : ℂ) ^ (m - l))
                * ((Real.exp (-(Real.pi * u) * (p.1 : ℝ) ^ 2) : ℝ) : ℂ))
              * (((p.2 : ℂ) ^ l)
                * ((Real.exp (-(Real.pi * u) * (p.2 : ℝ) ^ 2) : ℝ) : ℂ))) := by
        rw [Finset.sum_mul]
        exact Finset.sum_congr rfl (fun l _ => by ring)

/-! ## The frequency-side Gaussian and summand -/

/-- The Gaussian factor of the frequency-side summand. -/
def freqGauss (d : ℕ) (u : ℝ) (ξ : ℤ × ℤ) : ℂ :=
  Complex.exp (-Real.pi *
    (((ξ.1 : ℂ) ^ 2 + (ξ.2 : ℂ) ^ 2) / ((u : ℂ) * (((4 * d : ℕ) : ℂ)) ^ 2)))

/-- The involution `(a,b) ↦ (a,-b)` of `ℤ²`. -/
def negImEquiv : ℤ × ℤ ≃ ℤ × ℤ :=
  Equiv.mk (fun p : ℤ × ℤ => (p.1, -p.2)) (fun p : ℤ × ℤ => (p.1, -p.2))
    (fun p => by ext <;> simp) (fun p => by ext <;> simp)

@[simp] theorem negImEquiv_apply (p : ℤ × ℤ) : negImEquiv p = (p.1, -p.2) := rfl

/-- The frequency-side summand of the theta transformation. -/
def dualSummand (d : ℕ) (chi : GaussianInt → ℂ) (m : ℕ) (u : ℝ) (ξ : ℤ × ℤ) : ℂ :=
  gaussSum d chi ⟨ξ.1, ξ.2⟩
    * ((((ξ.1 : ℂ) + Complex.I * (ξ.2 : ℂ)) / (((4 * d : ℕ) : ℂ))) ^ m)
    * freqGauss d u ξ

/-! ## The one-frequency identity (holomorphic Gaussian Fourier transform) -/

private lemma per_xi_identity (d : ℕ) (hd : 1 ≤ d) (m : ℕ) {u : ℝ} (hu : 0 < u) (ξ : ℤ × ℤ) :
    (∑ l ∈ Finset.range (m + 1), ((m.choose l : ℂ) * Complex.I ^ l) *
        ((FourierTransform.fourier (fun x : ℝ => ((x : ℂ) ^ (m - l)) *
              Complex.exp (-Real.pi * u * (x : ℂ) ^ 2))) ((ξ.1 : ℝ) / ((4 * d : ℕ) : ℝ))
          * (FourierTransform.fourier (fun y : ℝ => ((y : ℂ) ^ l) *
              Complex.exp (-Real.pi * u * (y : ℂ) ^ 2))) ((ξ.2 : ℝ) / ((4 * d : ℕ) : ℝ))))
      = (-Complex.I) ^ m * ((u : ℂ) ^ (m + 1))⁻¹ *
          ((((ξ.1 : ℂ) + Complex.I * (ξ.2 : ℂ)) / (((4 * d : ℕ) : ℂ))) ^ m *
            Complex.exp (-Real.pi * (((ξ.1 : ℂ) ^ 2 + (ξ.2 : ℂ) ^ 2)
              / ((u : ℂ) * (((4 * d : ℕ) : ℂ)) ^ 2)))) := by
  have hqpos : (0 : ℝ) < ((4 * d : ℕ) : ℝ) := by
    have : 0 < 4 * d := by omega
    exact_mod_cast this
  have hQ : (((4 * d : ℕ) : ℂ)) ≠ 0 := by
    rw [← Complex.ofReal_natCast]
    exact Complex.ofReal_ne_zero.mpr (ne_of_gt hqpos)
  have hu0 : (u : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt hu)
  have hcast1 : Complex.ofReal ((ξ.1 : ℝ) / ((4 * d : ℕ) : ℝ))
      = (ξ.1 : ℂ) / (((4 * d : ℕ) : ℂ)) := by
    rw [Complex.ofReal_div, Complex.ofReal_intCast, Complex.ofReal_natCast]
  have hcast2 : Complex.ofReal ((ξ.2 : ℝ) / ((4 * d : ℕ) : ℝ))
      = (ξ.2 : ℂ) / (((4 * d : ℕ) : ℂ)) := by
    rw [Complex.ofReal_div, Complex.ofReal_intCast, Complex.ofReal_natCast]
  have h1 : (∑ l ∈ Finset.range (m + 1), ((m.choose l : ℂ) * Complex.I ^ l) *
        ((FourierTransform.fourier (fun x : ℝ => ((x : ℂ) ^ (m - l)) *
              Complex.exp (-Real.pi * u * (x : ℂ) ^ 2))) ((ξ.1 : ℝ) / ((4 * d : ℕ) : ℝ))
          * (FourierTransform.fourier (fun y : ℝ => ((y : ℂ) ^ l) *
              Complex.exp (-Real.pi * u * (y : ℂ) ^ 2))) ((ξ.2 : ℝ) / ((4 * d : ℕ) : ℝ))))
      = (∑ l ∈ Finset.range (m + 1), (m.choose l : ℂ) * Complex.I ^ l *
          (FourierTransform.fourier (fun x : ℝ => ((x : ℂ) ^ (m - l)) *
              Complex.exp (-Real.pi * u * (x : ℂ) ^ 2))) ((ξ.1 : ℝ) / ((4 * d : ℕ) : ℝ))
          * (FourierTransform.fourier (fun y : ℝ => ((y : ℂ) ^ l) *
              Complex.exp (-Real.pi * u * (y : ℂ) ^ 2))) ((ξ.2 : ℝ) / ((4 * d : ℕ) : ℝ))) := by
    exact Finset.sum_congr rfl (fun l _ => by ring)
  rw [h1, Work.FIArea5.S16.holoGaussian2d m hu ((ξ.1 : ℝ) / ((4 * d : ℕ) : ℝ))
    ((ξ.2 : ℝ) / ((4 * d : ℕ) : ℝ))]
  have hp : (Complex.ofReal ((ξ.1 : ℝ) / ((4 * d : ℕ) : ℝ))
        + Complex.I * Complex.ofReal ((ξ.2 : ℝ) / ((4 * d : ℕ) : ℝ))) ^ m
      = (((ξ.1 : ℂ) + Complex.I * (ξ.2 : ℂ)) / (((4 * d : ℕ) : ℂ))) ^ m := by
    rw [hcast1, hcast2]
    congr 1
    field_simp
  have he : Complex.exp (-Real.pi * (Complex.ofReal ((ξ.1 : ℝ) / ((4 * d : ℕ) : ℝ)) ^ 2
        + Complex.ofReal ((ξ.2 : ℝ) / ((4 * d : ℕ) : ℝ)) ^ 2) / (u : ℂ))
      = Complex.exp (-Real.pi * (((ξ.1 : ℂ) ^ 2 + (ξ.2 : ℂ) ^ 2)
          / ((u : ℂ) * (((4 * d : ℕ) : ℂ)) ^ 2))) := by
    rw [hcast1, hcast2]
    congr 1
    field_simp
  rw [hp, he]
  ring

/-! ## The Poisson form of `thetaOdd` -/

theorem thetaOdd_eq_poisson_form (d : ℕ) (hd : 1 ≤ d) (chi : GaussianInt → ℂ)
    (hchi : IsCharMod4dStrict d chi) (m : ℕ) {u : ℝ} (hu : 0 < u) :
    thetaOdd chi m u
      = (1 / (((4 * d : ℕ) : ℂ) ^ 2)) * (-Complex.I) ^ m * ((u : ℂ) ^ (m + 1))⁻¹ *
          ∑' ξ : ℤ × ℤ,
            gaussSum d chi ⟨ξ.1, ξ.2⟩
              * ((((ξ.1 : ℂ) + Complex.I * (ξ.2 : ℂ)) / (((4 * d : ℕ) : ℂ))) ^ m)
              * Complex.exp (-Real.pi *
                  (((ξ.1 : ℂ) ^ 2 + (ξ.2 : ℂ) ^ 2) / ((u : ℂ) * (((4 * d : ℕ) : ℂ)) ^ 2))) := by
  have hqpos : (0 : ℝ) < ((4 * d : ℕ) : ℝ) := by
    have : 0 < 4 * d := by omega
    exact_mod_cast this
  rw [thetaOdd_eq_tsum_Z2]
  have h1 : ∀ p : ℤ × ℤ, thetaOddSummand chi m u (gaussToProd.symm p)
      = ∑ l ∈ Finset.range (m + 1), ((m.choose l : ℂ) * Complex.I ^ l) *
          (chiOdd chi ⟨p.1, p.2⟩ *
            ((((p.1 : ℂ) ^ (m - l)) * Complex.exp (-Real.pi * u * ((p.1 : ℂ) ^ 2)))
              * (((p.2 : ℂ) ^ l) * Complex.exp (-Real.pi * u * ((p.2 : ℂ) ^ 2))))) := by
    intro p
    rw [thetaOddSummand_symm, binomial_expansion, Finset.mul_sum]
    exact Finset.sum_congr rfl (fun l _ => by ring)
  rw [tsum_congr h1]
  have hs1 : ∀ l ∈ Finset.range (m + 1), Summable (fun p : ℤ × ℤ =>
      ((m.choose l : ℂ) * Complex.I ^ l) *
        (chiOdd chi ⟨p.1, p.2⟩ *
          ((((p.1 : ℂ) ^ (m - l)) * Complex.exp (-Real.pi * u * ((p.1 : ℂ) ^ 2)))
            * (((p.2 : ℂ) ^ l) * Complex.exp (-Real.pi * u * ((p.2 : ℂ) ^ 2)))))) :=
    fun l _ => (summable_chiOdd_poly_gauss d chi hchi.1 hu (m - l) l).mul_left _
  rw [Summable.tsum_finsetSum hs1]
  have h3 : ∀ l ∈ Finset.range (m + 1),
      (∑' p : ℤ × ℤ, ((m.choose l : ℂ) * Complex.I ^ l) *
        (chiOdd chi ⟨p.1, p.2⟩ *
          ((((p.1 : ℂ) ^ (m - l)) * Complex.exp (-Real.pi * u * ((p.1 : ℂ) ^ 2)))
            * (((p.2 : ℂ) ^ l) * Complex.exp (-Real.pi * u * ((p.2 : ℂ) ^ 2))))))
      = ((m.choose l : ℂ) * Complex.I ^ l) *
          ((1 / (((4 * d : ℕ) : ℂ) ^ 2)) *
            ∑' ξ : ℤ × ℤ, gaussSum d chi ⟨ξ.1, ξ.2⟩ *
              ((FourierTransform.fourier (fun x : ℝ => ((x : ℂ) ^ (m - l)) *
                    Complex.exp (-Real.pi * u * (x : ℂ) ^ 2))) ((ξ.1 : ℝ) / ((4 * d : ℕ) : ℝ))
                * (FourierTransform.fourier (fun y : ℝ => ((y : ℂ) ^ l) *
                    Complex.exp (-Real.pi * u * (y : ℂ) ^ 2))) ((ξ.2 : ℝ) / ((4 * d : ℕ) : ℝ)))) := by
    intro l hl
    rw [tsum_mul_left,
      poisson_single_l d hd chi hchi m l (Nat.lt_succ_iff.mp (Finset.mem_range.mp hl)) hu]
  rw [Finset.sum_congr rfl h3]
  have hs2 : ∀ l ∈ Finset.range (m + 1), Summable (fun ξ : ℤ × ℤ =>
      ((m.choose l : ℂ) * Complex.I ^ l) *
        (gaussSum d chi ⟨ξ.1, ξ.2⟩ *
          ((FourierTransform.fourier (fun x : ℝ => ((x : ℂ) ^ (m - l)) *
                Complex.exp (-Real.pi * u * (x : ℂ) ^ 2))) ((ξ.1 : ℝ) / ((4 * d : ℕ) : ℝ))
            * (FourierTransform.fourier (fun y : ℝ => ((y : ℂ) ^ l) *
                Complex.exp (-Real.pi * u * (y : ℂ) ^ 2))) ((ξ.2 : ℝ) / ((4 * d : ℕ) : ℝ))))) :=
    fun l _ => (summable_gaussSum_fourier_kernel d chi hchi.1 hu hqpos (m - l) l).mul_left _
  rw [sum_tsum_swap (Finset.range (m + 1))
      (fun l ξ => gaussSum d chi ⟨ξ.1, ξ.2⟩ *
        ((FourierTransform.fourier (fun x : ℝ => ((x : ℂ) ^ (m - l)) *
              Complex.exp (-Real.pi * u * (x : ℂ) ^ 2))) ((ξ.1 : ℝ) / ((4 * d : ℕ) : ℝ))
          * (FourierTransform.fourier (fun y : ℝ => ((y : ℂ) ^ l) *
              Complex.exp (-Real.pi * u * (y : ℂ) ^ 2))) ((ξ.2 : ℝ) / ((4 * d : ℕ) : ℝ))))
      (fun l => (m.choose l : ℂ) * Complex.I ^ l) (1 / (((4 * d : ℕ) : ℂ) ^ 2)) hs2]
  have hfin : (∑' ξ : ℤ × ℤ, ∑ l ∈ Finset.range (m + 1), ((m.choose l : ℂ) * Complex.I ^ l) *
        (gaussSum d chi ⟨ξ.1, ξ.2⟩ *
          ((FourierTransform.fourier (fun x : ℝ => ((x : ℂ) ^ (m - l)) *
                Complex.exp (-Real.pi * u * (x : ℂ) ^ 2))) ((ξ.1 : ℝ) / ((4 * d : ℕ) : ℝ))
            * (FourierTransform.fourier (fun y : ℝ => ((y : ℂ) ^ l) *
                Complex.exp (-Real.pi * u * (y : ℂ) ^ 2))) ((ξ.2 : ℝ) / ((4 * d : ℕ) : ℝ)))))
      = (-Complex.I) ^ m * ((u : ℂ) ^ (m + 1))⁻¹ *
          ∑' ξ : ℤ × ℤ, gaussSum d chi ⟨ξ.1, ξ.2⟩ *
            ((((ξ.1 : ℂ) + Complex.I * (ξ.2 : ℂ)) / (((4 * d : ℕ) : ℂ))) ^ m *
              Complex.exp (-Real.pi * (((ξ.1 : ℂ) ^ 2 + (ξ.2 : ℂ) ^ 2)
                / ((u : ℂ) * (((4 * d : ℕ) : ℂ)) ^ 2)))) := by
    have key : ∀ ξ : ℤ × ℤ,
        (∑ l ∈ Finset.range (m + 1), ((m.choose l : ℂ) * Complex.I ^ l) *
          (gaussSum d chi ⟨ξ.1, ξ.2⟩ *
            ((FourierTransform.fourier (fun x : ℝ => ((x : ℂ) ^ (m - l)) *
                  Complex.exp (-Real.pi * u * (x : ℂ) ^ 2))) ((ξ.1 : ℝ) / ((4 * d : ℕ) : ℝ))
              * (FourierTransform.fourier (fun y : ℝ => ((y : ℂ) ^ l) *
                  Complex.exp (-Real.pi * u * (y : ℂ) ^ 2))) ((ξ.2 : ℝ) / ((4 * d : ℕ) : ℝ)))))
        = gaussSum d chi ⟨ξ.1, ξ.2⟩ *
            (∑ l ∈ Finset.range (m + 1), ((m.choose l : ℂ) * Complex.I ^ l) *
              ((FourierTransform.fourier (fun x : ℝ => ((x : ℂ) ^ (m - l)) *
                    Complex.exp (-Real.pi * u * (x : ℂ) ^ 2))) ((ξ.1 : ℝ) / ((4 * d : ℕ) : ℝ))
                * (FourierTransform.fourier (fun y : ℝ => ((y : ℂ) ^ l) *
                    Complex.exp (-Real.pi * u * (y : ℂ) ^ 2))) ((ξ.2 : ℝ) / ((4 * d : ℕ) : ℝ)))) := by
      intro ξ
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun l _ => by ring)
    have hmid : (∑' ξ : ℤ × ℤ, ∑ l ∈ Finset.range (m + 1), ((m.choose l : ℂ) * Complex.I ^ l) *
          (gaussSum d chi ⟨ξ.1, ξ.2⟩ *
            ((FourierTransform.fourier (fun x : ℝ => ((x : ℂ) ^ (m - l)) *
                  Complex.exp (-Real.pi * u * (x : ℂ) ^ 2))) ((ξ.1 : ℝ) / ((4 * d : ℕ) : ℝ))
              * (FourierTransform.fourier (fun y : ℝ => ((y : ℂ) ^ l) *
                  Complex.exp (-Real.pi * u * (y : ℂ) ^ 2))) ((ξ.2 : ℝ) / ((4 * d : ℕ) : ℝ)))))
        = ∑' ξ : ℤ × ℤ, (-Complex.I) ^ m * ((u : ℂ) ^ (m + 1))⁻¹ *
            (gaussSum d chi ⟨ξ.1, ξ.2⟩ *
              ((((ξ.1 : ℂ) + Complex.I * (ξ.2 : ℂ)) / (((4 * d : ℕ) : ℂ))) ^ m *
                Complex.exp (-Real.pi * (((ξ.1 : ℂ) ^ 2 + (ξ.2 : ℂ) ^ 2)
                  / ((u : ℂ) * (((4 * d : ℕ) : ℂ)) ^ 2))))) := by
      refine tsum_congr (fun ξ => ?_)
      rw [key ξ, per_xi_identity d hd m hu ξ]
      ring
    rw [hmid, tsum_mul_left]
  rw [hfin]
  simp only [mul_assoc]
/-! ## The dual form -/

theorem poisson_form_dual (d : ℕ) (hd : 1 ≤ d) (chi : GaussianInt → ℂ)
    (hchi : IsCharMod4dStrict d chi) (m : ℕ) {u : ℝ} (hu : 0 < u) (G : ℂ)
    (hG : ∀ ξ : GaussianInt, gaussSum d chi ξ = G * star (chi ⟨ξ.re, -ξ.im⟩)) :
    (∑' ξ : ℤ × ℤ, dualSummand d chi m u ξ)
      = G * ((4 * d : ℕ) : ℂ) ^ (-(m : ℤ)) *
          star (thetaOdd chi m (1 / (16 * (d : ℝ) ^ 2 * u))) := by
  have hQ : (((4 * d : ℕ) : ℂ)) ≠ 0 := by
    have h : (0 : ℝ) < ((4 * d : ℕ) : ℝ) := by
      have : 0 < 4 * d := by omega
      exact_mod_cast this
    rw [← Complex.ofReal_natCast]
    exact Complex.ofReal_ne_zero.mpr (ne_of_gt h)
  have hU : ((u : ℂ) * (((4 * d : ℕ) : ℂ)) ^ 2)⁻¹
      = ((1 / (16 * (d : ℝ) ^ 2 * u) : ℝ) : ℂ) := by
    rw [inv_eq_one_div]
    exact inv_u_mul_four_d_sq d u
  have hEE : ∀ p : ℤ × ℤ, freqGauss d u (p.1, -p.2) = freqGauss d u p := by
    intro p
    simp only [freqGauss]
    congr 1
    push_cast
    ring
  have hconv : ∀ p : ℤ × ℤ, freqGauss d u p
      = Complex.exp (-(Real.pi : ℂ) * (((1 / (16 * (d : ℝ) ^ 2 * u) : ℝ)) : ℂ)
          * ((((gnorm (⟨p.1, p.2⟩ : GaussianInt) : ℕ) : ℝ)) : ℂ)) := by
    intro p
    simp only [freqGauss]
    congr 1
    rw [div_eq_mul_inv, hU]
    rw [gnorm_cast_real]
    push_cast
    ring
  rw [star_thetaOdd_eq d chi hchi m (1 / (16 * (d : ℝ) ^ 2 * u))]
  have hL : (∑' ξ : ℤ × ℤ, dualSummand d chi m u ξ)
      = G * (((((4 * d : ℕ) : ℂ)) ^ m)⁻¹ *
          ∑' ξ : ℤ × ℤ, thetaOddStarSummand chi m (1 / (16 * (d : ℝ) ^ 2 * u)) ξ) := by
    have hA : (∑' ξ : ℤ × ℤ, dualSummand d chi m u ξ)
        = (∑' ξ : ℤ × ℤ, (G * star (chi ⟨ξ.1, -ξ.2⟩)) *
            ((((ξ.1 : ℂ) + Complex.I * (ξ.2 : ℂ)) / (((4 * d : ℕ) : ℂ))) ^ m * freqGauss d u ξ)) := by
      refine tsum_congr (fun ξ => ?_)
      simp only [dualSummand]
      rw [hG]
      dsimp only
      ring
    have hB : (∑' ξ : ℤ × ℤ, (G * star (chi ⟨ξ.1, -ξ.2⟩)) *
            ((((ξ.1 : ℂ) + Complex.I * (ξ.2 : ℂ)) / (((4 * d : ℕ) : ℂ))) ^ m * freqGauss d u ξ))
        = (∑' ξ : ℤ × ℤ, (G * star (chi ⟨ξ.1, ξ.2⟩)) *
            ((((ξ.1 : ℂ) - Complex.I * (ξ.2 : ℂ)) / (((4 * d : ℕ) : ℂ))) ^ m * freqGauss d u ξ)) := by
      refine (tsum_congr (fun ξ => ?_)).trans (Equiv.tsum_eq negImEquiv
        (fun p : ℤ × ℤ => (G * star (chi ⟨p.1, p.2⟩)) *
          ((((p.1 : ℂ) - Complex.I * (p.2 : ℂ)) / (((4 * d : ℕ) : ℂ))) ^ m * freqGauss d u p)))
      simp only [negImEquiv_apply]
      rw [hEE ξ]
      rw [show ((ξ.1 : ℂ) - Complex.I * ((((-ξ.2 : ℤ)) : ℂ)))
          = ((ξ.1 : ℂ) + Complex.I * (ξ.2 : ℂ)) by push_cast; ring]
    have hC : (∑' ξ : ℤ × ℤ, (G * star (chi ⟨ξ.1, ξ.2⟩)) *
            ((((ξ.1 : ℂ) - Complex.I * (ξ.2 : ℂ)) / (((4 * d : ℕ) : ℂ))) ^ m * freqGauss d u ξ))
        = G * (((((4 * d : ℕ) : ℂ)) ^ m)⁻¹ *
            ∑' ξ : ℤ × ℤ, thetaOddStarSummand chi m (1 / (16 * (d : ℝ) ^ 2 * u)) ξ) := by
      have hpt : ∀ ξ : ℤ × ℤ, (G * star (chi ⟨ξ.1, ξ.2⟩)) *
            ((((ξ.1 : ℂ) - Complex.I * (ξ.2 : ℂ)) / (((4 * d : ℕ) : ℂ))) ^ m * freqGauss d u ξ)
          = G * (((((4 * d : ℕ) : ℂ)) ^ m)⁻¹ *
              thetaOddStarSummand chi m (1 / (16 * (d : ℝ) ^ 2 * u)) ξ) := by
        intro ξ
        rw [thetaOddStarSummand, ← hconv ξ, div_pow, div_eq_mul_inv]
        ring
      rw [tsum_congr hpt, tsum_mul_left, tsum_mul_left]
    rw [hA, hB, hC]
  rw [hL]
  have hzp : (((4 * d : ℕ) : ℂ)) ^ (-(m : ℤ)) = ((((4 * d : ℕ) : ℂ)) ^ m)⁻¹ := by
    rw [zpow_neg, zpow_natCast]
  rw [hzp]
  ring

/-! ## The theta transformation -/

theorem thetaOdd_poisson (d : ℕ) (hd : 1 ≤ d) (chi : GaussianInt → ℂ)
    (hchi : IsCharMod4dStrict d chi) (m : ℕ) {u : ℝ} (hu : 0 < u) (G : ℂ)
    (hG : ∀ ξ : GaussianInt, gaussSum d chi ξ = G * star (chi ⟨ξ.re, -ξ.im⟩)) :
    thetaOdd chi m u
      = ((((4 * d : ℕ)) : ℂ) ^ (-(m : ℤ) - 2)) * (-Complex.I) ^ m * ((u : ℂ) ^ (m + 1))⁻¹ * G *
          star (thetaOdd chi m (1 / (16 * (d : ℝ) ^ 2 * u))) := by
  have hQ : (((4 * d : ℕ) : ℂ)) ≠ 0 := by
    have h : (0 : ℝ) < ((4 * d : ℕ) : ℝ) := by
      have : 0 < 4 * d := by omega
      exact_mod_cast this
    rw [← Complex.ofReal_natCast]
    exact Complex.ofReal_ne_zero.mpr (ne_of_gt h)
  have hsplit : (((4 * d : ℕ) : ℂ)) ^ (-(m : ℤ) - 2)
      = (1 / ((((4 * d : ℕ) : ℂ)) ^ 2)) * (((4 * d : ℕ) : ℂ)) ^ (-(m : ℤ)) := by
    have h1 : (((4 * d : ℕ) : ℂ)) ^ (-(m : ℤ) - 2)
        = ((((4 * d : ℕ) : ℂ)) ^ (-(m : ℤ))) * ((((4 * d : ℕ) : ℂ)) ^ (-2 : ℤ)) := by
      rw [show (-(m : ℤ) - 2 : ℤ) = (-(m : ℤ)) + (-2) by ring, zpow_add₀ hQ]
    have h2 : (((4 * d : ℕ) : ℂ)) ^ (-2 : ℤ) = 1 / ((((4 * d : ℕ) : ℂ)) ^ 2) := by
      rw [show (-2 : ℤ) = -((2 : ℕ) : ℤ) by norm_num, zpow_neg, zpow_natCast]
      ring
    rw [h1, h2]
    ring
  rw [thetaOdd_eq_poisson_form d hd chi hchi m hu]
  rw [show (∑' ξ : ℤ × ℤ, gaussSum d chi ⟨ξ.1, ξ.2⟩
        * ((((ξ.1 : ℂ) + Complex.I * (ξ.2 : ℂ)) / (((4 * d : ℕ) : ℂ))) ^ m)
        * Complex.exp (-Real.pi *
            (((ξ.1 : ℂ) ^ 2 + (ξ.2 : ℂ) ^ 2) / ((u : ℂ) * (((4 * d : ℕ) : ℂ)) ^ 2))))
      = (∑' ξ : ℤ × ℤ, dualSummand d chi m u ξ) from rfl]
  rw [poisson_form_dual d hd chi hchi m hu G hG, hsplit]
  ring

end

end Work.FIArea5.S16Hecke
