import Mathlib
import Submission.Work.KMTAreas.A7Hi.LowpassDefs
import Submission.Work.KMTAreas.A7.cwEtaCutDefs
import Submission.Work.KMTAreas.A7Hi.DilVar

/-!
# Definitions for the a priori finiteness of the chain part of the low-pass family

The target `Work.KMTAreas.A7Hi.lpf_chainPart_finite` asks for `∫⁻ (chainPart)^p < ⊤` for the
low-pass Ionescu--Wainger family `lpf ρ l₁ m₀ m f = kmtProj ρ l₁ (-(m₀ + m)) f`.  The route taken
here is:

* the operator `kmtProj ρ l₁ k` is the sum over the arithmetic frequencies `α ∈ (ℚ/ℤ)_{≤l₁}` of the
  *modulated* pure dilation operators (kernel `j ↦ star (fourier j α) · 2^k · φ(2^k j)` with
  `φ = 𝓕 η` the fixed Fourier profile of the KMT cutoff) — `lpf_eq_sum_charMul_dilFam`;
* the `r`-variation of a sum of `#A` families is at most the sum of the `r`-variations
  (`chainPart_finset_sum_le`), and the variation is invariant under multiplication by a
  modulus-one function (`chainPart_const_mul`), so the chain part of `lpf` is dominated by the sum
  over `α` of the variation of the *pure dilation family* applied to `y ↦ fourier y α · f y`;
* the pure dilation family is exactly the family of the Jones--Seeger--Wright / Lépingle
  lacunary variational estimate `Work.KMTAreas.A7Hi.DilVar` (PROVED), applied with the Schwartz
  kernel `K = 𝓕η` and the `2`-lacunary scales `σ_m = 2^{m₀+m}`.

This file only fixes the vocabulary: the Schwartz kernel `kmtPhiSch` (whose underlying function is
`Work.KMTAreas.A7.kmtPhi = 𝓕 kmtEta`), the pure dilation family `dilFam`, the scales `lpfScale`
and the modulation `charMul`.
-/

set_option autoImplicit false

open MeasureTheory
open scoped ENNReal NNReal BigOperators FourierTransform

namespace Work.KMTAreas.A7Hi

/-- The Fourier profile `φ = 𝓕 η` of the KMT cutoff `η = kmtEta`, as a **Schwartz function**.
The `j`-th Fourier coefficient of the rescaled cutoff `η_{≤k}` is the dilate `2^k φ(2^k j)`
(`Work.KMTAreas.A7.cwEtaCutDiff_dilate`), i.e. the `j`-th entry of the convolution kernel of the
pure dilation family at scale `2^{-k}`. -/
noncomputable def kmtPhiSch : SchwartzMap ℝ ℂ :=
  FourierTransform.fourier Work.KMTAreas.A7.etaMult_kmtEtaSch

/-- The underlying function of `kmtPhiSch` is `Work.KMTAreas.A7.kmtPhi = 𝓕 kmtEta`. -/
theorem kmtPhiSch_coe (x : ℝ) : kmtPhiSch x = Work.KMTAreas.A7.kmtPhi x := by
  have h : (⇑Work.KMTAreas.A7.etaMult_kmtEtaSch : ℝ → ℂ) = Work.KMTContract.kmtEta :=
    funext (fun y => Work.KMTAreas.A7.etaMult_kmtEtaSch_coe y)
  rw [kmtPhiSch, Work.KMTAreas.A7.kmtPhi, SchwartzMap.fourier_coe, h]

/-- **The pure dilation family** with kernel `K` and integer scales `σ`: the `n`-th member is the
convolution `x ↦ Σ'_j (1/σ_n) · K(j/σ_n) · g(x - j)`.  This is the family of
`Work.KMTAreas.A7Hi.DilVar`. -/
noncomputable def dilFam (K : SchwartzMap ℝ ℂ) (σ : ℕ → ℕ) (g : ℤ → ℂ) (m : ℕ) (x : ℤ) : ℂ :=
  ∑' j : ℤ, (1 / (σ m : ℝ)) * K ((j : ℝ) / (σ m)) * g (x - j)

/-- The reciprocal of the IW scale of the `m`-th low-pass operator: `σ_m = 2^{m₀+m}`.  The
underlying frequency scale is `k_m = -(m₀+m)`, so `2^{k_m} = 1/σ_m = 1/lpfScale m₀ m`. -/
def lpfScale (m₀ : ℕ) (m : ℕ) : ℕ := 2 ^ (m₀ + m)

theorem lpfScale_pos (m₀ m : ℕ) : 1 ≤ lpfScale m₀ m :=
  Nat.one_le_two_pow

theorem lpfScale_lacunary (m₀ m : ℕ) : 2 * lpfScale m₀ m ≤ lpfScale m₀ (m + 1) := by
  rw [lpfScale, lpfScale, show m₀ + (m + 1) = (m₀ + m) + 1 from by omega, pow_succ]
  omega

theorem lpfScale_cast (m₀ m : ℕ) : ((lpfScale m₀ m : ℕ) : ℝ) = (2 : ℝ) ^ (m₀ + m) := by
  rw [lpfScale]; push_cast; ring

/-- The modulation `g ↦ (y ↦ fourier y α · g y)` by the character attached to the arithmetic
frequency `α`. -/
noncomputable def charMul (α : Work.Analysis.IonescuWainger.Circle) (g : ℤ → ℂ) : ℤ → ℂ :=
  fun y => fourier y α * g y

@[simp] theorem charMul_apply (α : Work.Analysis.IonescuWainger.Circle) (g : ℤ → ℂ) (y : ℤ) :
    charMul α g y = fourier y α * g y := rfl

theorem norm_fourier_int (α : Work.Analysis.IonescuWainger.Circle) (y : ℤ) :
    ‖fourier y α‖ = 1 := by
  rw [fourier_apply, Circle.norm_coe]

theorem norm_charMul (α : Work.Analysis.IonescuWainger.Circle) (g : ℤ → ℂ) (y : ℤ) :
    ‖charMul α g y‖ = ‖g y‖ := by
  rw [charMul_apply, norm_mul, norm_fourier_int, one_mul]

end Work.KMTAreas.A7Hi
