/-
# The symbols of the two columns of the small-scale model approximation (low case of A6)

This module fixes the *frequency-side* vocabulary of the proof of
`Work.KMTPlan.A6.lowSmallModelApprox`: both sides of the estimate are bilinear convolution
operators on `ℤ` (`Work.KMTAreas.A7.bilinOp`), so by the paper's `crude-mult`(ii)
(`Work.KMTPlan.A6.SymToolbox_tsum_coeff2_le`) the whole estimate is a bound on the
`ξ`-derivatives of the symbol of the *difference* of the two operators.

* `symC` — the symbol of the concrete column `colSmall`: the product
  `(symbol of Ã_N) · (symbol of T^{l₁}_{ψ₁}) · (symbol of T^{l₂}_{ψ₂})`, where `Ã_N` has the
  discrete symbol `halfSym N P` and the exact-height Ionescu--Wainger multiplier
  `T^l_ψ` has the Fourier-coefficient kernel `tmKer ρ l ψ`.
* `symM` — the symbol of the model column `lowModel`: the `t`-integral of the product of the
  symbol of the twisted bilinear multiplier `BtwistEx` with the symbols of the two *modulated*
  exact-height multipliers `T^{l₁}_{φ_{N,t}}`, `T^{l₂}_{φ̃_{N,t}}`.
* `symD` — the symbol of the *difference*, in the form in which the paper's Proposition
  `mod-approx` provides it: the fibre sum over the exact-height arithmetic frequencies
  `γ ∈ (ℚ/ℤ)_{l₁} × (ℚ/ℤ)_{l₂}` of the paper's symbol difference
  `M₀ = E_{n∈[N]}e(α₁n+α₂P(n))e(ξ₁n+ξ₂P(n))1_{n>N/2} − m_Ẑ(α₁,α₂)m̃_{N,ℝ}(ξ₁,ξ₂)`
  (`Work.KMTAreas.A7.M0`) times the two §5 bumps `φ_N`, `φ̃_N`, summed over the representatives
  `θ - γ + m` of the aliasing fibre.

The identification `symC − symM = symD` (under the non-aliasing of the arithmetic frequencies at
the arc radius `2^{-2u}`, `u = uScale ρ L`) is the paper's `mod-approx`; the derivative bounds
for `symD` are the paper's single-scale symbol estimate, supplied by
`Work.A7.M0SharpBound` / `Work.A7.ModelApproxCore_M0_deriv_bound`.
-/
import Mathlib
import Submission.Work.KMTPlan.A6.SymSeq
import Submission.Work.KMTAreas.A7.ModelApproxDefs
import Submission.Work.KMTPlan.A6.LowSmallDefs

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Work.KMTPlan.A6

noncomputable section

open MeasureTheory Polynomial Finset Filter Topology
open scoped ENNReal NNReal BigOperators
open Work.Analysis.IonescuWainger
open Work.Analysis.IWMultiplier
open PointwiseErgodicTheorems Submission.PointwiseErgodicTheorems
open Work.KMTContract
open Work.KMTAreas.A7

/-- The real coordinate of a point of the circle `ℝ/ℤ`, i.e. its canonical representative in
`[0,1)`: the frequency variable attached to an arithmetic frequency `γ ∈ (ℚ/ℤ)_{l}` when the
symbol is written as a `1`-periodic function of a *real* variable. -/
noncomputable def gamR (ξ : AddCircle (1 : ℝ)) : ℝ := (AddCircle.equivIco (1 : ℝ) 0 ξ).val

/-- The kernel of the exact-height Ionescu--Wainger multiplier `T^l_φ = Tm ρ l φ`: the Fourier
coefficients of the symbol `iwSymbolSet ((ℚ/ℤ)_l) (periodize φ)`. -/
noncomputable def tmKer (ρ : ℝ) (l : ℕ) (φ : ℝ → ℂ) : ℤ → ℂ :=
  iwKernel (iwSymbolSet (diffFreqs ρ l) (periodize φ))

/-- `Tm ρ l φ` is the convolution operator with the kernel `tmKer ρ l φ` (definitional). -/
theorem Tm_eq_convOp (ρ : ℝ) (l : ℕ) (φ : ℝ → ℂ) (u : ℤ → ℂ) :
    Tm ρ l φ u = convOp (tmKer ρ l φ) u := rfl

/-- The arithmetic/`m_*` kernel of the twisted bilinear multiplier `BtwistEx`: the double Fourier
coefficient family of `arithKernelEx · cw m_* ⊗ cw m_*`. -/
noncomputable def arithKerM (ρ : ℝ) (P : ℤ[X]) (l₁ l₂ k₁ k₂ : ℕ) : ℤ → ℤ → ℂ :=
  fun a b =>
    arithKernelEx ρ P (arithQ ρ (max l₁ l₂)) l₁ l₂ a b
      * cw (mStarF (uScale ρ (lcL l₁ l₂ k₁ k₂))) a
      * cw (mStargF P.natDegree (uScale ρ (lcL l₁ l₂ k₁ k₂))) b

/-- `BtwistEx` is the bilinear convolution operator with the kernel `arithKerM` (definitional). -/
theorem BtwistEx_eq_bilinOp (ρ : ℝ) (P : ℤ[X]) (l₁ l₂ k₁ k₂ : ℕ) (h k : ℤ → ℂ) (x : ℤ) :
    BtwistEx ρ P l₁ l₂
      (mStarF (uScale ρ (lcL l₁ l₂ k₁ k₂)))
      (mStargF P.natDegree (uScale ρ (lcL l₁ l₂ k₁ k₂))) h k x
      = bilinOp (arithKerM ρ P l₁ l₂ k₁ k₂) h k x := rfl

/-- **The symbol of the concrete column** `colSmall`: the discrete symbol `halfSym N P` of the
halved average `Ã_N` times the symbols of the two exact-height multipliers `T^{l_i}_{ψ_i}`,
with `ψ₁ = φ_N`, `ψ₂ = φ̃_N` the §5 bumps. -/
noncomputable def symC (ρ : ℝ) (P : ℤ[X]) (N l₁ l₂ k₁ k₂ : ℕ) : ℝ → ℝ → ℂ :=
  fun x y =>
    symSeq (tmKer ρ l₁ (varphiN N k₁)) x
      * symSeq (tmKer ρ l₂ (varphitildeN P.natDegree N k₂)) y
      * halfSym N P x y

/-- **The symbol of the model column** `lowModel`: the `t`-integral of the symbol of the twisted
bilinear multiplier `BtwistEx` times the symbols of the two modulated exact-height multipliers. -/
noncomputable def symM (ρ : ℝ) (P : ℤ[X]) (N l₁ l₂ k₁ k₂ : ℕ) : ℝ → ℝ → ℂ :=
  fun x y =>
    ∫ t in (1 / 2 : ℝ)..1,
      symSeq2 (arithKerM ρ P l₁ l₂ k₁ k₂) x y
        * symSeq (tmKer ρ l₁ (varphiNt N k₁ t)) x
        * symSeq (tmKer ρ l₂ (varphitildeNt P P.natDegree N k₂ t)) y

/-- The period of the pair of arithmetic frequencies `(γ₁,γ₂)` used in the arithmetic symbol
`m_Ẑ`: the least common multiple of their additive orders.  For `γ ∈ (ℚ/ℤ)_{l}` the additive order
is at most `2^{C_ρ 2^{ρl}}` (the paper's Lemma `mag-lem`(ii)), so this is the *fibre-wise* period
of the paper's Proposition `mod-approx`, as opposed to the (doubly exponentially large) common
denominator `arithQ` of the whole frequency set. -/
noncomputable def perQ (γ₁ γ₂ : AddCircle (1 : ℝ)) : ℕ :=
  Nat.lcm (addOrderOf γ₁) (addOrderOf γ₂)

/-- **The symbol of the difference**, in the fibre form of the paper's Proposition `mod-approx`:
the sum over the exact-height arithmetic frequencies of the paper's `M₀` times the two bumps,
summed over the representatives `θ - γ + m` of the aliasing fibre. -/
noncomputable def symD (ρ : ℝ) (P : ℤ[X]) (N l₁ l₂ k₁ k₂ : ℕ) : ℝ → ℝ → ℂ :=
  fun x y =>
    ∑ γ₁ ∈ diffFreqs ρ l₁, ∑ γ₂ ∈ diffFreqs ρ l₂,
      ∑' m₁ : ℤ, ∑' m₂ : ℤ,
        M0 P N (perQ γ₁ γ₂) γ₁ γ₂ (x - gamR γ₁ + m₁) (y - gamR γ₂ + m₂)
          * varphiN N k₁ (x - gamR γ₁ + m₁)
          * varphitildeN P.natDegree N k₂ (y - gamR γ₂ + m₂)

end

end Work.KMTPlan.A6
