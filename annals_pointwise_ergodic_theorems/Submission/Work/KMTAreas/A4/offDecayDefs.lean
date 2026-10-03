/-
# Shared definitions for the off-diagonal decay of the Ionescu--Wainger projections

The rescaled cutoffs `bmp j = η_{≤j}`, their kernels `lam j = 𝓕⁻η_{≤j}`, the pointwise product
`mS` and the convolution `cS` of two complex Schwartz functions, together with their elementary
properties.  These are the objects in terms of which the decomposition of `kmtProj ρ l k` in
`Work.KMTAreas.A4.offDecay` is phrased.
-/
import Mathlib
import Submission.Work.KMTAreas.A7.EtaMult

set_option autoImplicit false
set_option maxHeartbeats 1000000

open MeasureTheory
open scoped ENNReal NNReal BigOperators FourierTransform

namespace Work.KMTAreas.A4

open Work.Analysis.IonescuWainger
open Work.Analysis.IWMultiplier

noncomputable section

/-- The rescaled cutoff `η_{≤j}` (`θ ↦ η(θ / 2^j)`) as a Schwartz function. -/
def bmp (j : ℤ) : SchwartzMap ℝ ℂ := Work.KMTAreas.A7.etaMult_etaCutSch j

/-- The kernel `λ_j = 𝓕⁻ η_{≤j}` of the rescaled cutoff. -/
def lam (j : ℤ) : SchwartzMap ℝ ℂ := FourierTransformInv.fourierInv (bmp j)

/-- Pointwise product of two complex Schwartz functions. -/
def mS (u v : SchwartzMap ℝ ℂ) : SchwartzMap ℝ ℂ :=
  SchwartzMap.pairing (ContinuousLinearMap.mul ℂ ℂ) u v

/-- Convolution of two complex Schwartz functions. -/
def cS (u v : SchwartzMap ℝ ℂ) : SchwartzMap ℝ ℂ :=
  SchwartzMap.convolution (ContinuousLinearMap.mul ℂ ℂ) u v

theorem bmp_coe (j : ℤ) : ((bmp j : SchwartzMap ℝ ℂ) : ℝ → ℂ)
    = etaCut Work.KMTContract.kmtEta j :=
  funext (Work.KMTAreas.A7.etaMult_etaCutSch_coe j)

theorem lam_eq_etaMult_K (j : ℤ) : lam j = Work.KMTAreas.A7.etaMult_K j := rfl

theorem lam_fourier (j : ℤ) : 𝓕 (lam j) = bmp j :=
  FourierInvPair.fourier_fourierInv_eq (bmp j)

theorem bmp_neg_apply (j : ℤ) (x : ℝ) : (bmp j) (-x) = (bmp j) x := by
  have h1 : (bmp j) (-x) = etaCut Work.KMTContract.kmtEta j (-x) := congrFun (bmp_coe j) (-x)
  have h2 : (bmp j) x = etaCut Work.KMTContract.kmtEta j x := congrFun (bmp_coe j) x
  rw [h1, h2]
  show Work.KMTContract.kmtEta ((-x) / (2 : ℝ) ^ j) = Work.KMTContract.kmtEta (x / (2 : ℝ) ^ j)
  rw [neg_div]
  exact Work.KMTContract.kmtEta_neg _

theorem fourier_bmp (j : ℤ) : 𝓕 (bmp j) = lam j := by
  ext x
  rw [SchwartzMap.fourier_coe, lam, SchwartzMap.fourierInv_coe,
    Real.fourierInv_eq_fourier_comp_neg]
  have hfun : (fun y : ℝ => (bmp j) (-y)) = (bmp j : ℝ → ℂ) := by
    funext y
    exact bmp_neg_apply j y
  rw [hfun]

theorem mS_apply (u v : SchwartzMap ℝ ℂ) (x : ℝ) : (mS u v) x = u x * v x := rfl

theorem cS_eq (u v : SchwartzMap ℝ ℂ) : cS u v
    = SchwartzMap.convolution (ContinuousLinearMap.mul ℂ ℂ) u v := rfl

/-- The product of `𝓕 u` and `𝓕 v` (the Fourier transforms of two Schwartz functions) is the
Fourier transform of the convolution. -/
theorem fourier_cS (u v : SchwartzMap ℝ ℂ) :
    𝓕 (cS u v) = mS (𝓕 u) (𝓕 v) := by
  have h := SchwartzMap.fourier_convolution (𝕜 := ℂ) (E := ℝ)
    (ContinuousLinearMap.mul ℂ ℂ) u v
  simpa [cS, mS] using h

/-- Pointwise description of the rescaled cutoff. -/
theorem bmp_eq_ofReal (j : ℤ) (x : ℝ) :
    (bmp j) x = (((Work.KMTContract.kmtBump (x / (2 : ℝ) ^ j) : ℝ)) : ℂ) := rfl

theorem bmp_re_mem (j : ℤ) (x : ℝ) :
    ((bmp j) x).re ∈ Set.Icc (0 : ℝ) 1 ∧ ((bmp j) x).im = 0 := by
  rw [bmp_eq_ofReal]
  refine ⟨⟨?_, ?_⟩, by simp⟩
  · exact_mod_cast Work.KMTContract.kmtEta_nonneg _
  · exact_mod_cast Work.KMTContract.kmtEta_le_one _

theorem norm_one_sub_bmp_le (j : ℤ) (x : ℝ) : ‖1 - (bmp j) x‖ ≤ 1 := by
  have hx : (bmp j) x = (((Work.KMTContract.kmtBump (x / (2 : ℝ) ^ j) : ℝ)) : ℂ) := rfl
  rw [hx, ← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
  have h0 : 0 ≤ Work.KMTContract.kmtBump (x / (2 : ℝ) ^ j) := Work.KMTContract.kmtEta_nonneg _
  have h1 : Work.KMTContract.kmtBump (x / (2 : ℝ) ^ j) ≤ 1 := Work.KMTContract.kmtEta_le_one _
  rw [abs_le]
  constructor <;> linarith

theorem bmp_support (j : ℤ) {x : ℝ} (h : (bmp j) x ≠ 0) : |x| ≤ (2 : ℝ) ^ j := by
  by_contra hc
  exact h ((Work.KMTContract.etaCutRegular j).2.2 x (le_of_lt (not_le.mp hc)))

theorem bmp_one_of_le (j : ℤ) {x : ℝ} (h : |x| ≤ (2 : ℝ) ^ (j - 1)) : (bmp j) x = 1 := by
  rw [bmp_coe]
  show Work.KMTContract.kmtEta (x / (2 : ℝ) ^ j) = 1
  refine Work.KMTContract.kmtEta_one ?_
  rw [abs_div]
  have h2 : (0 : ℝ) < (2 : ℝ) ^ j := zpow_pos (by norm_num) j
  rw [abs_of_pos h2, div_le_iff₀ h2]
  have h3 : (2 : ℝ) ^ (j - 1) = (2 : ℝ) ^ j / 2 := by
    rw [zpow_sub_one₀ (by norm_num : (2 : ℝ) ≠ 0)]
    ring
  rw [h3] at h
  linarith

/-- The mass of the rescaled kernel is `1`. -/
theorem integral_lam (j : ℤ) : ∫ x : ℝ, lam j x = 1 := by
  have h : (𝓕 ((lam j : SchwartzMap ℝ ℂ) : ℝ → ℂ)) 0 = ∫ x : ℝ, lam j x := by
    rw [Real.fourier_real_eq]
    simp
  rw [← h, ← SchwartzMap.fourier_coe, lam_fourier]
  rw [bmp_coe]
  show Work.KMTContract.kmtEta (0 / (2 : ℝ) ^ j) = 1
  rw [zero_div]
  exact Work.KMTContract.kmtEta_one (by norm_num)

end

end Work.KMTAreas.A4
