/-
# `Submission.Work.FIArea6Hecke.R.allZThetaLawClean`

A copy of the fleet's `FIArea6Hecke/allZThetaLaw` with

* every top-level declaration renamed with the prefix `azc_`, so that this module can coexist with
  the original in one import closure, and
* the two remaining *temporary copies* of the delegated helpers (`allZSummable`,
  `tsumGconjEqStarAllZTheta`) replaced by **imports** of the files in which those helpers are now
  proved.

This makes the all-`z` theta transformation law available (a `sorry`-free module) independently of
the original file: it is the analytic input of the *corrected* conductor-normalised Hecke
functional equation (`R/NOTES_FEStrictConductor.md` §12), hence of `R/zerosInStrip` and
`R/baseLowerNegTwoUniform`.
-/
import Mathlib
import Submission.Work.FIArea6Hecke.R.ConductorThetaDefs
import Submission.Work.FIArea5.S16Hecke.thetaOdd_poisson
import Submission.Work.FIArea4.GaussMoebiusCore
import Submission.Work.FIArea6Hecke.allZGaussKernelSummable
import Submission.Work.FIArea6Hecke.allZSummable
import Submission.Work.FIArea6Hecke.tsumGconjEqStarAllZTheta
import Submission.Work.FIArea6Hecke.tsumIdeal
import Submission.Work.FIArea6Hecke.allZPeriodic
import Submission.Work.FIArea6Hecke.allZPerXi

set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace Work.FIArea6Hecke

open scoped BigOperators
open Work.FIArea6Hecke.R
open Work.FIPlan

noncomputable section

attribute [local instance] Classical.propDecidable

/-! ## Temporary copies of the delegated lemmas (replaced by imports at the end) -/

/-! ## Elementary rewritings and abbreviations -/

/-- The summand of `allZTheta`. -/
def azc_allZSummand (chi₀ : GaussianInt → ℂ) (m : ℕ) (u : ℝ) (z : GaussianInt) : ℂ :=
  chi₀ z * (z.toComplex) ^ m * Complex.exp (-(Real.pi * u * (gnorm z : ℝ)))

/-- The level `q = N(M) = gnorm M` of the theta transformation, as a complex number. -/
def azc_lvl (M : GaussianInt) : ℂ := ((gnorm M : ℕ) : ℂ)

/-- The level `q = N(M) = gnorm M` of the theta transformation, as a real number. -/
def azc_lvlR (M : GaussianInt) : ℝ := ((gnorm M : ℕ) : ℝ)

/-- The pair of one-dimensional Fourier kernels of the theta transformation, at the dual
frequency `ξ/q`. -/
def azc_fkPair (q u : ℝ) (a b : ℕ) (ξ : ℤ × ℤ) : ℂ :=
  (FourierTransform.fourier (fun x : ℝ => ((x : ℂ) ^ a) * Complex.exp (-Real.pi * u * (x : ℂ) ^ 2)))
      ((ξ.1 : ℝ) / q)
    * (FourierTransform.fourier (fun y : ℝ => ((y : ℂ) ^ b) *
        Complex.exp (-Real.pi * u * (y : ℂ) ^ 2))) ((ξ.2 : ℝ) / q)

/-- The dual (frequency-side) summand of the theta transformation, in `ℤ²` coordinates. -/
def azc_fdual (M : GaussianInt) (m : ℕ) (u : ℝ) (ξ : ℤ × ℤ) : ℂ :=
  (((ξ.1 : ℂ) + Complex.I * (ξ.2 : ℂ)) / azc_lvl M) ^ m *
    Complex.exp (-Real.pi * (((ξ.1 : ℂ) ^ 2 + (ξ.2 : ℂ) ^ 2) / ((u : ℂ) * (azc_lvl M) ^ 2)))

/-- The dual (frequency-side) summand of the theta transformation, in `ℤ[i]` coordinates. -/
def azc_fdualG (M : GaussianInt) (m : ℕ) (u : ℝ) (η : GaussianInt) : ℂ :=
  ((η : ℂ) / azc_lvl M) ^ m *
    Complex.exp (-Real.pi * (((η.re : ℂ) ^ 2 + (η.im : ℂ) ^ 2) / ((u : ℂ) * (azc_lvl M) ^ 2)))

/-- The Gaussian factor of the dual summand after the substitution `ξ = M·γ`. -/
def azc_dualExp (M : GaussianInt) (u : ℝ) (γ : GaussianInt) : ℂ :=
  Complex.exp (Complex.ofReal (-(Real.pi * ((1 : ℝ) / (azc_lvlR M * u)) * (gnorm γ : ℝ))))

theorem azc_allZTheta_eq_tsum_summand (chi₀ : GaussianInt → ℂ) (m : ℕ) (u : ℝ) :
    allZTheta chi₀ m u = ∑' z : GaussianInt, azc_allZSummand chi₀ m u z := rfl

theorem azc_allZTheta_eq_tsum_Z2 (chi₀ : GaussianInt → ℂ) (m : ℕ) (u : ℝ) :
    allZTheta chi₀ m u = ∑' p : ℤ × ℤ, azc_allZSummand chi₀ m u (⟨p.1, p.2⟩ : GaussianInt) := by
  rw [azc_allZTheta_eq_tsum_summand]
  rw [(Equiv.tsum_eq (Work.FIArea5.S16Hecke.gaussToProd)
    (fun p : ℤ × ℤ => azc_allZSummand chi₀ m u (⟨p.1, p.2⟩ : GaussianInt))).symm]
  exact tsum_congr (fun z => by simp [Work.FIArea5.S16Hecke.gaussToProd])

/-- **The binomial expansion of the holomorphic weight**, in `ℤ²` coordinates. -/
theorem azc_allZExpansion (chi₀ : GaussianInt → ℂ) (m : ℕ) (u : ℝ) (p : ℤ × ℤ) :
    azc_allZSummand chi₀ m u (⟨p.1, p.2⟩ : GaussianInt)
      = ∑ l ∈ Finset.range (m + 1), ((m.choose l : ℂ) * Complex.I ^ l) *
          (chi₀ (⟨p.1, p.2⟩ : GaussianInt) *
            ((((p.1 : ℂ) ^ (m - l)) * Complex.exp (-Real.pi * u * ((p.1 : ℂ) ^ 2)))
              * (((p.2 : ℂ) ^ l) * Complex.exp (-Real.pi * u * ((p.2 : ℂ) ^ 2))))) := by
  have hE : Complex.exp (-(Real.pi * u * (gnorm (⟨p.1, p.2⟩ : GaussianInt) : ℝ)))
      = Complex.exp (-Real.pi * u * (gnorm (⟨p.1, p.2⟩ : GaussianInt) : ℝ)) := by
    congr 1
    ring
  rw [azc_allZSummand, hE]
  rw [Work.FIArea5.S16Hecke.cexp_neg_pi_gnorm, GaussianInt.toComplex_def,
    Work.FIArea5.S16Hecke.cexp_neg_pi_sq, Work.FIArea5.S16Hecke.cexp_neg_pi_sq]
  have hEs : ((Real.exp (-(Real.pi * u) * ((p.1 : ℝ) ^ 2 + (p.2 : ℝ) ^ 2)) : ℝ) : ℂ)
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
  rw [hEs, ← hkey, ← mul_assoc, Finset.mul_sum, Finset.sum_mul, Finset.sum_mul]
  exact Finset.sum_congr rfl (fun l _ => by ring)

/-- **Poisson summation for a single pair of exponents.** -/
theorem azc_allZ_poisson_single (M : GaussianInt) (chi₀ : GaussianInt → ℂ) (hM : M ≠ 0)
    (hchi : IsCharModStrict M chi₀) (m l : ℕ) (_hl : l ≤ m) {u : ℝ} (hu : 0 < u) :
    (∑' p : ℤ × ℤ, chi₀ (⟨p.1, p.2⟩ : GaussianInt) *
        ((((p.1 : ℂ) ^ (m - l)) * Complex.exp (-Real.pi * u * ((p.1 : ℂ) ^ 2)))
          * (((p.2 : ℂ) ^ l) * Complex.exp (-Real.pi * u * ((p.2 : ℂ) ^ 2)))))
      = (1 / (azc_lvl M) ^ 2) *
          ∑' ξ : ℤ × ℤ, condGaussSum M chi₀ (⟨ξ.1, ξ.2⟩ : GaussianInt) *
            azc_fkPair (azc_lvlR M) u (m - l) l ξ := by
  have hq : 0 < gnorm M := Work.FIArea4.gnorm_pos hM
  have hpois := Work.FIArea5.S16.poisson_periodic_2d (gnorm M) hq (fun z : GaussianInt => chi₀ z)
    (allZPeriodic M chi₀ hchi)
    (fun x : ℝ => ((x : ℂ) ^ (m - l)) * Complex.exp (-Real.pi * u * (x : ℂ) ^ 2))
    (fun y : ℝ => ((y : ℂ) ^ l) * Complex.exp (-Real.pi * u * (y : ℂ) ^ 2))
    (Work.FIArea5.S16Hecke.continuous_kernel u (m - l))
    (Work.FIArea5.S16Hecke.continuous_kernel u l)
    (by norm_num : (1 : ℝ) < 2)
    (Work.FIArea5.S16Hecke.kernel_isBigO u hu (m - l) (b := 2))
    (Work.FIArea5.S16Hecke.fourier_kernel_isBigO u hu (m - l) (b := 2))
    (Work.FIArea5.S16Hecke.kernel_isBigO u hu l (b := 2))
    (Work.FIArea5.S16Hecke.fourier_kernel_isBigO u hu l (b := 2))
  have hgs : ∀ ξ : ℤ × ℤ,
      (∑ α ∈ (Finset.range (gnorm M)).product (Finset.range (gnorm M)),
          chi₀ (⟨α.1, α.2⟩ : GaussianInt) * Complex.exp (2 * Real.pi * Complex.I *
            ((((α.1 * ξ.1 + α.2 * ξ.2 : ℤ)) : ℂ) / (((gnorm M : ℕ)) : ℂ))))
        = condGaussSum M chi₀ (⟨ξ.1, ξ.2⟩ : GaussianInt) := by
    intro ξ
    rw [condGaussSum, Finset.product_eq_sprod, Finset.sum_product]
  simp only [Complex.ofReal_intCast] at hpois
  rw [hpois]
  congr 1
  refine tsum_congr (fun ξ => ?_)
  rw [hgs ξ]
  simp only [azc_fkPair, azc_lvlR]

/-- **The Poisson form of `allZTheta`.** -/
theorem azc_allZ_poisson_form (M : GaussianInt) (chi₀ : GaussianInt → ℂ) (hM : M ≠ 0) (m : ℕ)
    (hchi : IsCharModStrict M chi₀) {u : ℝ} (hu : 0 < u) :
    allZTheta chi₀ m u =
      (1 / (azc_lvl M) ^ 2) * (-Complex.I) ^ m * ((u : ℂ) ^ (m + 1))⁻¹ *
        ∑' ξ : ℤ × ℤ, condGaussSum M chi₀ (⟨ξ.1, ξ.2⟩ : GaussianInt) * azc_fdual M m u ξ := by
  have hq : 0 < gnorm M := Work.FIArea4.gnorm_pos hM
  rw [azc_allZTheta_eq_tsum_Z2]
  rw [tsum_congr (fun p => azc_allZExpansion chi₀ m u p)]
  have hs1 : ∀ l ∈ Finset.range (m + 1),
      Summable (fun p : ℤ × ℤ => ((m.choose l : ℂ) * Complex.I ^ l) *
          (chi₀ (⟨p.1, p.2⟩ : GaussianInt) *
            ((((p.1 : ℂ) ^ (m - l)) * Complex.exp (-Real.pi * u * ((p.1 : ℂ) ^ 2)))
              * (((p.2 : ℂ) ^ l) * Complex.exp (-Real.pi * u * ((p.2 : ℂ) ^ 2)))))) :=
    fun l _ => (allZSummable M chi₀ hchi hu (m - l) l).mul_left _
  rw [Summable.tsum_finsetSum hs1]
  have h3 : ∀ l ∈ Finset.range (m + 1),
      (∑' p : ℤ × ℤ, ((m.choose l : ℂ) * Complex.I ^ l) *
          (chi₀ (⟨p.1, p.2⟩ : GaussianInt) *
            ((((p.1 : ℂ) ^ (m - l)) * Complex.exp (-Real.pi * u * ((p.1 : ℂ) ^ 2)))
              * (((p.2 : ℂ) ^ l) * Complex.exp (-Real.pi * u * ((p.2 : ℂ) ^ 2))))))
      = ((m.choose l : ℂ) * Complex.I ^ l) * ((1 / (azc_lvl M) ^ 2) *
          ∑' ξ : ℤ × ℤ, condGaussSum M chi₀ (⟨ξ.1, ξ.2⟩ : GaussianInt) *
            azc_fkPair (azc_lvlR M) u (m - l) l ξ) := by
    intro l hl
    rw [tsum_mul_left]
    rw [azc_allZ_poisson_single M chi₀ hM hchi m l
      (Nat.lt_succ_iff.mp (Finset.mem_range.mp hl)) hu]
  rw [Finset.sum_congr rfl h3]
  have hfk : ∀ a b : ℕ, Summable (fun ξ : ℤ × ℤ =>
      condGaussSum M chi₀ (⟨ξ.1, ξ.2⟩ : GaussianInt) * azc_fkPair (azc_lvlR M) u a b ξ) := by
    intro a b
    refine (allZGaussKernelSummable M chi₀ hchi hu hq a b).congr (fun ξ => ?_)
    simp only [azc_fkPair, azc_lvlR]
  have hsummable_l : ∀ l ∈ Finset.range (m + 1),
      Summable (fun ξ : ℤ × ℤ => ((m.choose l : ℂ) * Complex.I ^ l) *
          (condGaussSum M chi₀ (⟨ξ.1, ξ.2⟩ : GaussianInt) *
            azc_fkPair (azc_lvlR M) u (m - l) l ξ)) :=
    fun l _ => (hfk (m - l) l).mul_left _
  have hswap : (∑ l ∈ Finset.range (m + 1), ((m.choose l : ℂ) * Complex.I ^ l) *
        ((1 / (azc_lvl M) ^ 2) *
          ∑' ξ : ℤ × ℤ, condGaussSum M chi₀ (⟨ξ.1, ξ.2⟩ : GaussianInt) *
            azc_fkPair (azc_lvlR M) u (m - l) l ξ))
      = (1 / (azc_lvl M) ^ 2) * ∑' ξ : ℤ × ℤ,
          ∑ l ∈ Finset.range (m + 1), ((m.choose l : ℂ) * Complex.I ^ l) *
            (condGaussSum M chi₀ (⟨ξ.1, ξ.2⟩ : GaussianInt) *
              azc_fkPair (azc_lvlR M) u (m - l) l ξ) := by
    have step1 : (∑ l ∈ Finset.range (m + 1), ((m.choose l : ℂ) * Complex.I ^ l) *
          ((1 / (azc_lvl M) ^ 2) *
            ∑' ξ : ℤ × ℤ, condGaussSum M chi₀ (⟨ξ.1, ξ.2⟩ : GaussianInt) *
              azc_fkPair (azc_lvlR M) u (m - l) l ξ))
        = (1 / (azc_lvl M) ^ 2) * ∑ l ∈ Finset.range (m + 1),
            (((m.choose l : ℂ) * Complex.I ^ l) *
              ∑' ξ : ℤ × ℤ, condGaussSum M chi₀ (⟨ξ.1, ξ.2⟩ : GaussianInt) *
                azc_fkPair (azc_lvlR M) u (m - l) l ξ) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun l _ => by ring)
    rw [step1]
    congr 1
    have step2 : (∑ l ∈ Finset.range (m + 1), ((m.choose l : ℂ) * Complex.I ^ l) *
          ∑' ξ : ℤ × ℤ, condGaussSum M chi₀ (⟨ξ.1, ξ.2⟩ : GaussianInt) *
            azc_fkPair (azc_lvlR M) u (m - l) l ξ)
        = ∑ l ∈ Finset.range (m + 1), ∑' ξ : ℤ × ℤ, ((m.choose l : ℂ) * Complex.I ^ l) *
            (condGaussSum M chi₀ (⟨ξ.1, ξ.2⟩ : GaussianInt) *
              azc_fkPair (azc_lvlR M) u (m - l) l ξ) := by
      refine Finset.sum_congr rfl (fun l hl => ?_)
      exact (Summable.tsum_mul_left _ (hfk (m - l) l)).symm
    rw [step2, (Summable.tsum_finsetSum hsummable_l).symm]
  rw [hswap]
  have hcoll : ∀ ξ : ℤ × ℤ,
      (∑ l ∈ Finset.range (m + 1), ((m.choose l : ℂ) * Complex.I ^ l) *
          (condGaussSum M chi₀ (⟨ξ.1, ξ.2⟩ : GaussianInt) *
            azc_fkPair (azc_lvlR M) u (m - l) l ξ))
      = condGaussSum M chi₀ (⟨ξ.1, ξ.2⟩ : GaussianInt) * (-Complex.I) ^ m *
          ((u : ℂ) ^ (m + 1))⁻¹ * azc_fdual M m u ξ := by
    intro ξ
    have h := allZPerXi M (fun _ : GaussianInt => condGaussSum M chi₀ (⟨ξ.1, ξ.2⟩ : GaussianInt))
      m hu hq ξ
    simpa only [azc_fkPair, azc_fdual, azc_lvl, azc_lvlR] using h
  rw [tsum_congr hcoll]
  have hreorder : (∑' ξ : ℤ × ℤ, condGaussSum M chi₀ (⟨ξ.1, ξ.2⟩ : GaussianInt) *
        (-Complex.I) ^ m * ((u : ℂ) ^ (m + 1))⁻¹ * azc_fdual M m u ξ)
      = ∑' ξ : ℤ × ℤ, (-Complex.I) ^ m * (((u : ℂ) ^ (m + 1))⁻¹ *
          (condGaussSum M chi₀ (⟨ξ.1, ξ.2⟩ : GaussianInt) * azc_fdual M m u ξ)) := by
    refine tsum_congr (fun ξ => ?_)
    ring
  rw [hreorder, tsum_mul_left, tsum_mul_left]
  ring

/-! ## The dual step -/

theorem azc_allZ_dual_Z2 (M : GaussianInt) (m : ℕ) (u : ℝ) (ξ : ℤ × ℤ) :
    azc_fdual M m u ξ = azc_fdualG M m u (⟨ξ.1, ξ.2⟩ : GaussianInt) := by
  have h1 : ((ξ.1 : ℂ) + Complex.I * (ξ.2 : ℂ)) = ((⟨ξ.1, ξ.2⟩ : GaussianInt) : ℂ) := by
    rw [GaussianInt.toComplex_def]
    ring
  have h2 : ((ξ.1 : ℂ) ^ 2 + (ξ.2 : ℂ) ^ 2)
      = (((⟨ξ.1, ξ.2⟩ : GaussianInt).re : ℂ) ^ 2
        + ((⟨ξ.1, ξ.2⟩ : GaussianInt).im : ℂ) ^ 2) := by
    norm_num
  simp only [azc_fdual, azc_fdualG, h1, h2]

/-- **The change of variables `η ↦ M·γ` in the dual kernel.** -/
theorem azc_fdualG_mul (M : GaussianInt) (m : ℕ) {u : ℝ} (hu : 0 < u) (hM : M ≠ 0) (γ : GaussianInt) :
    azc_fdualG M m u (M * γ) = ((M : ℂ) / azc_lvl M) ^ m * ((γ : ℂ) ^ m * azc_dualExp M u γ) := by
  have hq : 0 < gnorm M := Work.FIArea4.gnorm_pos hM
  have hqR : (0 : ℝ) < ((gnorm M : ℕ) : ℝ) := by exact_mod_cast hq
  have hexp : (-Real.pi * (((gnorm (M * γ) : ℕ) : ℂ) / ((u : ℂ) * (azc_lvl M) ^ 2)))
      = Complex.ofReal (-(Real.pi * ((1 : ℝ) / (azc_lvlR M * u)) * (gnorm γ : ℝ))) := by
    simp only [azc_lvl, azc_lvlR]
    rw [Work.FIArea4.gnorm_mul, Nat.cast_mul,
      show (((gnorm M : ℕ) : ℂ)) = (((gnorm M : ℕ) : ℝ) : ℂ) from (Complex.ofReal_natCast _).symm,
      show (((gnorm γ : ℕ) : ℂ)) = (((gnorm γ : ℕ) : ℝ) : ℂ) from (Complex.ofReal_natCast _).symm]
    rw [← Complex.ofReal_neg]
    simp only [← Complex.ofReal_mul, ← Complex.ofReal_div, ← Complex.ofReal_pow]
    rw [Complex.ofReal_inj]
    field_simp
  simp only [azc_fdualG, GaussianInt.toComplex_mul,
    ← Work.FIArea5.S16Hecke.gnorm_cast_complex (M * γ), azc_dualExp]
  rw [hexp, ← div_mul_eq_mul_div, mul_pow]
  ring

theorem azc_allZ_poisson_dual (M : GaussianInt) (chi₀ : GaussianInt → ℂ) (m : ℕ) (τ : ℂ) (hM : M ≠ 0)
    (_hchi : IsCharModStrict M chi₀)
    (hsupp : ∀ ξ : GaussianInt, ¬ (M ∣ ξ) → condGaussSum M chi₀ ξ = 0)
    (hdual : ∀ γ : GaussianInt, condGaussSum M chi₀ (M * γ) =
      azc_lvl M * τ * star (chi₀ (gconjInt γ)))
    {u : ℝ} (hu : 0 < u) :
    (∑' ξ : ℤ × ℤ, condGaussSum M chi₀ (⟨ξ.1, ξ.2⟩ : GaussianInt) * azc_fdual M m u ξ)
      = azc_lvl M * τ * ((M : ℂ) / azc_lvl M) ^ m *
          star (allZTheta chi₀ m (1 / ((gnorm M : ℕ) * u))) := by
  rw [tsum_congr (fun ξ => by rw [azc_allZ_dual_Z2])]
  have hZ2 : (∑' ξ : ℤ × ℤ, condGaussSum M chi₀ (⟨ξ.1, ξ.2⟩ : GaussianInt) *
        azc_fdualG M m u (⟨ξ.1, ξ.2⟩ : GaussianInt))
      = ∑' η : GaussianInt, condGaussSum M chi₀ η * azc_fdualG M m u η := by
    rw [← Equiv.tsum_eq (Work.FIArea5.S16Hecke.gaussToProd.symm)
      (fun η : GaussianInt => condGaussSum M chi₀ η * azc_fdualG M m u η)]
    refine tsum_congr (fun ξ => ?_)
    simp [Work.FIArea5.S16Hecke.gaussToProd_symm_apply]
  rw [hZ2]
  have hA : (∑' η : GaussianInt, condGaussSum M chi₀ η * azc_fdualG M m u η)
      = ∑' η : GaussianInt, ({η : GaussianInt | M ∣ η} : Set GaussianInt).indicator
          (fun η => condGaussSum M chi₀ η * azc_fdualG M m u η) η := by
    refine tsum_congr (fun η => ?_)
    rw [Set.indicator_apply]
    by_cases h : η ∈ ({η : GaussianInt | M ∣ η} : Set GaussianInt)
    · rw [if_pos h]
    · rw [if_neg h, hsupp η (by simpa using h), zero_mul]
  rw [hA, ← tsumIdeal M hM (fun η => condGaussSum M chi₀ η * azc_fdualG M m u η)]
  rw [tsum_congr (fun γ => by rw [hdual γ])]
  rw [tsum_congr (fun γ => by rw [azc_fdualG_mul M m hu hM γ])]
  have hshape : (∑' γ : GaussianInt, (azc_lvl M * τ * star (chi₀ (gconjInt γ))) *
        (((M : ℂ) / azc_lvl M) ^ m * ((γ : ℂ) ^ m * azc_dualExp M u γ)))
      = azc_lvl M * τ * (((M : ℂ) / azc_lvl M) ^ m *
          (∑' γ : GaussianInt, star (chi₀ (gconjInt γ)) * (γ : ℂ) ^ m * azc_dualExp M u γ)) := by
    have hinner : (∑' γ : GaussianInt, star (chi₀ (gconjInt γ)) *
          ((γ : ℂ) ^ m * azc_dualExp M u γ))
        = (∑' γ : GaussianInt, star (chi₀ (gconjInt γ)) * (γ : ℂ) ^ m * azc_dualExp M u γ) := by
      refine tsum_congr (fun γ => ?_)
      ring
    have h1 : (∑' γ : GaussianInt, (azc_lvl M * τ * star (chi₀ (gconjInt γ))) *
          (((M : ℂ) / azc_lvl M) ^ m * ((γ : ℂ) ^ m * azc_dualExp M u γ)))
        = (∑' γ : GaussianInt, azc_lvl M * (τ * (((M : ℂ) / azc_lvl M) ^ m *
            (star (chi₀ (gconjInt γ)) * ((γ : ℂ) ^ m * azc_dualExp M u γ))))) := by
      refine tsum_congr (fun γ => ?_)
      ring
    rw [h1, tsum_mul_left, tsum_mul_left, tsum_mul_left, hinner]
    ring
  rw [hshape]
  have hconv : (∑' γ : GaussianInt, star (chi₀ (gconjInt γ)) * (γ : ℂ) ^ m * azc_dualExp M u γ)
      = (∑' γ : GaussianInt, star (chi₀ (gconjInt γ)) * (γ : ℂ) ^ m *
          Complex.exp (-(Real.pi * (Complex.ofReal (1 / ((gnorm M : ℕ) * u)))
            * (gnorm γ : ℝ)))) := by
    refine tsum_congr (fun γ => ?_)
    simp only [azc_dualExp, azc_lvlR, Complex.ofReal_neg, Complex.ofReal_mul]
  rw [hconv, tsumGconjEqStarAllZTheta chi₀ m (1 / ((gnorm M : ℕ) * u))]
  ring

/-! ## The theta transformation law -/

theorem azc_allZThetaLaw (M : GaussianInt) (hM : M ≠ 0) (chi₀ : GaussianInt → ℂ) (m : ℕ)
    (hchi : Work.FIArea6Hecke.R.IsCharModStrict M chi₀) (τ : ℂ) (hτ : τ ≠ 0)
    (hsupp : ∀ ξ : GaussianInt, ¬ (M ∣ ξ) → Work.FIArea6Hecke.R.condGaussSum M chi₀ ξ = 0)
    (hdual : ∀ γ : GaussianInt, Work.FIArea6Hecke.R.condGaussSum M chi₀ (M * γ) =
      ((Work.FIPlan.gnorm M : ℕ) : ℂ) * τ * star (chi₀ (Work.FIArea6Hecke.R.gconjInt γ)))
    (hne : ∃ u : ℝ, 0 < u ∧ Work.FIArea6Hecke.R.allZTheta chi₀ m u ≠ 0) :
    ∃ A : ℂ, A ≠ 0 ∧ ∀ u : ℝ, 0 < u →
      Work.FIArea6Hecke.R.allZTheta chi₀ m u = A * ((u : ℂ) ^ (-(m : ℤ) - 1)) *
        star (Work.FIArea6Hecke.R.allZTheta chi₀ m (1 / ((Work.FIPlan.gnorm M : ℕ) * u))) := by
  refine ⟨((Work.FIPlan.gnorm M : ℕ) : ℂ) ^ (-(m : ℤ) - 1) * τ * (-Complex.I) ^ m *
    ((M : ℂ)) ^ m, ?_, ?_⟩
  · have hq : 0 < gnorm M := Work.FIArea4.gnorm_pos hM
    have hqR : (0 : ℝ) < ((gnorm M : ℕ) : ℝ) := by exact_mod_cast hq
    have hqC : (((gnorm M : ℕ)) : ℂ) ≠ 0 := by
      rw [← Complex.ofReal_natCast]
      exact Complex.ofReal_ne_zero.mpr (ne_of_gt hqR)
    refine mul_ne_zero (mul_ne_zero (mul_ne_zero ?_ hτ) ?_) ?_
    · exact zpow_ne_zero _ hqC
    · exact pow_ne_zero _ (neg_ne_zero.mpr Complex.I_ne_zero)
    · refine pow_ne_zero _ ?_
      rw [Ne, GaussianInt.toComplex_eq_zero]
      exact hM
  · intro u hu
    rw [azc_allZ_poisson_form M chi₀ hM m hchi hu]
    rw [show (1 / (azc_lvl M) ^ 2) * (-Complex.I) ^ m * ((u : ℂ) ^ (m + 1))⁻¹ *
        (∑' ξ : ℤ × ℤ, condGaussSum M chi₀ (⟨ξ.1, ξ.2⟩ : GaussianInt) * azc_fdual M m u ξ) =
          (1 / (azc_lvl M) ^ 2) * (-Complex.I) ^ m * ((u : ℂ) ^ (m + 1))⁻¹ *
            (azc_lvl M * τ * ((M : ℂ) / azc_lvl M) ^ m *
              star (allZTheta chi₀ m (1 / ((gnorm M : ℕ) * u))))
        from by rw [azc_allZ_poisson_dual M chi₀ m τ hM hchi hsupp hdual hu]]
    have huz : (u : ℂ) ^ (-(m : ℤ) - 1) = ((u : ℂ) ^ (m + 1))⁻¹ := by
      rw [show (-(m : ℤ) - 1) = -(((m + 1 : ℕ)) : ℤ) by push_cast; ring, zpow_neg, zpow_natCast]
    have hqz : ((((gnorm M : ℕ)) : ℂ)) ^ (-(m : ℤ) - 1) = ((((gnorm M : ℕ)) : ℂ) ^ (m + 1))⁻¹ := by
      rw [show (-(m : ℤ) - 1) = -(((m + 1 : ℕ)) : ℤ) by push_cast; ring, zpow_neg, zpow_natCast]
    rw [huz, hqz, azc_lvl]
    have hq : 0 < gnorm M := Work.FIArea4.gnorm_pos hM
    have hqR : (0 : ℝ) < ((gnorm M : ℕ) : ℝ) := by exact_mod_cast hq
    have hqC : (((gnorm M : ℕ)) : ℂ) ≠ 0 := by
      rw [← Complex.ofReal_natCast]
      exact Complex.ofReal_ne_zero.mpr (ne_of_gt hqR)
    have huC : (u : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hu)
    have hup : (u : ℂ) ^ (m + 1) ≠ 0 := pow_ne_zero _ huC
    have hqp : (((gnorm M : ℕ)) : ℂ) ^ (m + 1) ≠ 0 := pow_ne_zero _ hqC
    have hqm : (((gnorm M : ℕ)) : ℂ) ^ m ≠ 0 := pow_ne_zero _ hqC
    rw [div_pow]
    field_simp
    ring

end

end Work.FIArea6Hecke
