import Mathlib
import Submission.Work.KMTAreas.ADev.Defs

/-!
# Real-scale lacunary dilation families on `ℤ`: vocabulary

This module fixes the objects of `Work.A7Hi2.dilVarRealScale` — the **real-scale** form of the
JSW/Lépingle lacunary dilation variational estimate `Work.KMTAreas.A7Hi.DilVarClean` — in the shape
in which its proof is decomposed.

For a Schwartz kernel `K` and real positive scales:

* `bumpKernR K σ j = (1/σ) · K (j/σ)` — the sampled dilation kernel of `K` at the real scale `σ`;
* `bumpOpR K σ f x = ∑'_j bumpKernR K σ j · f (x - j)` — the corresponding convolution operator;
* `diffKernR K σ ρ j = bumpKernR K σ j - bumpKernR K ρ j` — the kernel of the difference of the two
  dilations at the **comparable** real scales `σ`, `ρ`;
* `diffOpR K σ ρ f x = ∑'_j diffKernR K σ ρ j · f (x - j)` — the difference operator;
* `linDiffKernR K σ ρ U ω` — the signed (linearised) sum `∑_{n ∈ U} ω_n diffKernR K (σ n) (ρ n)`
  of the difference kernels along a lacunary family of scale pairs;
* `symDiffR K σ ρ θ = ∑'_j diffKernR K σ ρ j · e^{2πijθ}` — its symbol (Fourier series);
* `bumpSymR K σ θ = ∑'_k 𝓕K (σ (k - θ))` — the Poisson-summation form of the symbol of `bumpKernR`;
* `levR σ = ⌊log₂ σ⌋` and `intScaleR σ = 2 ^ levR σ` — the dyadic level of a real scale and its
  **integer surrogate** `2 ^ ⌊log₂ σ⌋ ∈ [σ/2, σ]`, which is 2-lacunary along a lacunary family and
  is the scale at which the *proved* integer-scale estimate `DilVarClean` is applied.

## The strategy of the proof of `dilVarRealScale`

Write `A_σ` for `bumpOpR K σ` and `ρ_n = intScaleR (σ n)`.  Since `A_{σ_n} = A_{ρ_n} + (A_{σ_n} −
A_{ρ_n})` and the variational norm is subadditive,

  `Vʳ(A_{σ_n} f) ≤ Vʳ(A_{ρ_n} f) + Vʳ((A_{σ_n} − A_{ρ_n}) f) ≤ Vʳ(A_{ρ_n} f) + D · (Σ_n |(A_{σ_n} − A_{ρ_n}) f|²)^{1/2}`,

where the second inequality is the pointwise *values* square-function bound `variationalNorm_le_sqSum`
for the band-pass (mean-zero) difference family.  The first term is bounded on `ℓᵖ` by
`Work.KMTAreas.A7Hi.DilVarClean` (the integer-scale estimate, applied to the integer sequence `ρ`),
and the second by the square-function bound for the difference family, whose three analytic inputs
(symbol/overlap bound, size and Hörmander conditions, `ℓ²` bound) are the content of the modules
`RealScaleSymBound`, `RealScaleKernelBound`, `RealScaleL2Bound` and `RealScaleSqSumAssembly`.
-/

set_option autoImplicit false

namespace Work.A7Hi2

open MeasureTheory Finset
open scoped ENNReal NNReal BigOperators FourierTransform

noncomputable section

/-- The sampled dilation kernel of `K` at the real scale `σ`: `j ↦ (1/σ) · K (j/σ)`. -/
def bumpKernR (K : SchwartzMap ℝ ℂ) (σ : ℝ) (j : ℤ) : ℂ := (1 / σ) * K ((j : ℝ) / σ)

/-- The kernel of the difference of the two dilations of `K` at the real scales `σ` and `ρ`. -/
def diffKernR (K : SchwartzMap ℝ ℂ) (σ ρ : ℝ) (j : ℤ) : ℂ :=
  bumpKernR K σ j - bumpKernR K ρ j

/-- The bump (dilation) convolution operator at the real scale `σ`. -/
def bumpOpR (K : SchwartzMap ℝ ℂ) (σ : ℝ) (f : ℤ → ℂ) : ℤ → ℂ :=
  fun x => ∑' j : ℤ, bumpKernR K σ j * f (x - j)

/-- The difference of the two dilation operators at the comparable real scales `σ`, `ρ`. -/
def diffOpR (K : SchwartzMap ℝ ℂ) (σ ρ : ℝ) (f : ℤ → ℂ) : ℤ → ℂ :=
  fun x => ∑' j : ℤ, diffKernR K σ ρ j * f (x - j)

/-- The signed (linearised) sum of the difference kernels over the indices `n ∈ U`. -/
def linDiffKernR (K : SchwartzMap ℝ ℂ) (σ ρ : ℕ → ℝ) (U : Finset ℕ) (ω : ℕ → Bool) : ℤ → ℂ :=
  fun j => ∑ n ∈ U, Work.KMTAreas.ADev.bSign ω n * diffKernR K (σ n) (ρ n) j

/-- The symbol of the difference of two dilations: the Fourier series of `diffKernR K σ ρ`. -/
def symDiffR (K : SchwartzMap ℝ ℂ) (σ ρ : ℝ) (θ : ℝ) : ℂ :=
  ∑' j : ℤ, diffKernR K σ ρ j * Work.KMTAreas.ADev.chr j θ

/-- The symbol of the bump at a real scale, in Poisson-summation form:
`∑'_k 𝓕K (σ (k - θ))`. -/
def bumpSymR (K : SchwartzMap ℝ ℂ) (σ : ℝ) (θ : ℝ) : ℂ :=
  ∑' k : ℤ, FourierTransform.fourier (K : ℝ → ℂ) (σ * ((k : ℝ) - θ))

/-- The dyadic level of a real scale: `⌊log₂ (⌊σ⌋)⌋ = Nat.log 2 ⌊σ⌋`. -/
def levR (σ : ℝ) : ℕ := Nat.log 2 ⌊σ⌋₊

/-- The integer surrogate of a real scale: `2 ^ levR σ`.  For `1 ≤ σ` it satisfies
`intScaleR σ ≤ σ < 2 * intScaleR σ`. -/
def intScaleR (σ : ℝ) : ℕ := 2 ^ levR σ

/-! ## Elementary facts about the level function -/

lemma one_le_intScaleR (σ : ℝ) : 1 ≤ intScaleR σ :=
  Nat.one_le_two_pow

/-- `2 ^ levR σ ≤ ⌊σ⌋`, hence `≤ σ`. -/
lemma intScaleR_le {σ : ℝ} (hσ : 1 ≤ σ) : (intScaleR σ : ℝ) ≤ σ := by
  have h1 : (⌊σ⌋₊ : ℝ) ≤ σ := Nat.floor_le (by linarith)
  have h2 : (1 : ℕ) ≤ ⌊σ⌋₊ := Nat.le_floor (by simpa using hσ)
  have h3 : 2 ^ levR σ ≤ ⌊σ⌋₊ := by
    simpa only [levR] using
      Nat.pow_log_le_self (b := 2) (ne_of_gt (lt_of_lt_of_le Nat.zero_lt_one h2))
  exact le_trans (by exact_mod_cast h3) h1

/-- `σ < 2 * intScaleR σ`. -/
lemma lt_two_mul_intScaleR {σ : ℝ} (hσ : 1 ≤ σ) : σ < 2 * (intScaleR σ : ℝ) := by
  have h3 : ⌊σ⌋₊ < 2 ^ (levR σ + 1) := by
    simpa only [levR] using Nat.lt_pow_succ_log_self (b := 2) (by norm_num) ⌊σ⌋₊
  have h4 : σ < (⌊σ⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one σ
  have h5 : (⌊σ⌋₊ : ℝ) + 1 ≤ ((2 ^ (levR σ + 1) : ℕ) : ℝ) := by
    have h := Nat.succ_le_of_lt h3
    push_cast
    exact_mod_cast h
  have h6 : ((2 ^ (levR σ + 1) : ℕ) : ℝ) = 2 * (intScaleR σ : ℝ) := by
    simp only [intScaleR, pow_succ]
    push_cast
    ring
  linarith [h4, h5, h6.le]

/-- The integer surrogates of a `2`-lacunary real scale family are themselves `2`-lacunary. -/
lemma intScaleR_lacunary {σ : ℕ → ℝ} (hσ1 : ∀ n, 1 ≤ σ n)
    (hσ2 : ∀ n, 2 * σ n ≤ σ (n + 1)) (n : ℕ) :
    2 * intScaleR (σ n) ≤ intScaleR (σ (n + 1)) := by
  have hm : ⌊σ n⌋₊ * 2 ≤ ⌊σ (n + 1)⌋₊ := by
    have h2 : ⌊σ n⌋₊ * 2 ≤ ⌊(2 : ℝ) * σ n⌋₊ := by
      apply Nat.le_floor
      push_cast
      nlinarith [Nat.floor_le (show (0 : ℝ) ≤ σ n by linarith [hσ1 n])]
    exact le_trans h2 (Nat.floor_mono (hσ2 n))
  have hlog : levR (σ n) + 1 ≤ levR (σ (n + 1)) := by
    have hmn : ⌊σ n⌋₊ ≠ 0 := by
      have h : (1 : ℕ) ≤ ⌊σ n⌋₊ := Nat.le_floor (by simpa using hσ1 n)
      omega
    have h4 : Nat.log 2 (⌊σ n⌋₊ * 2) ≤ Nat.log 2 ⌊σ (n + 1)⌋₊ := Nat.log_mono_right hm
    rw [Nat.log_mul_base (by norm_num) hmn] at h4
    simpa only [levR] using h4
  calc 2 * intScaleR (σ n) = 2 ^ (levR (σ n) + 1) := by
        simp only [intScaleR, pow_succ]
        ring
    _ ≤ 2 ^ levR (σ (n + 1)) := Nat.pow_le_pow_right (by norm_num) hlog
    _ = intScaleR (σ (n + 1)) := by simp only [intScaleR]

end

end Work.A7Hi2
