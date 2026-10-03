/-
# The two-dimensional Fourier coefficient of a mixed partial derivative (`j ≤ 2` version)

This is the `C^4`, `j₁, j₂ ≤ 2` instance of the elementary dictionary of
`Work.KMTPlan.A6.SymToolbox` between a `1`-periodic symbol `σ : ℝ → ℝ → ℂ` and its Fourier
coefficients on the unit square: differentiating the symbol in its two variables multiplies the
`(p₁,p₂)`-th coefficient by the corresponding frequencies,

  `coeff2 (∂₁^{j₁} ∂₂^{j₂} σ) p₁ p₂ = (2πi p₁)^{j₁} (2πi p₂)^{j₂} coeff2 σ p₁ p₂`.

The general statement (with joint smoothness `C^{j₁+j₂}` and arbitrary `j₁, j₂`) is proved in
`Work.KMTPlan.A6.SymToolbox_coeff2_dp` (integration by parts in each variable against the
character, the inner one pointwise in the outer variable and the outer one after the Fubini
identity `SymToolbox_coeff2_swap`, with the joint regularity of the iterated partials supplied by
`cdp_contDiff_dp1_iter` / `cdp_contDiff_dp2_iter`).  Since `j₁, j₂ ≤ 2` and `ContDiff ℝ 4` imply
`ContDiff ℝ (j₁ + j₂)`, the present lemma is that theorem with the smoothness hypothesis
downgraded by `ContDiff.of_le`.

The point of this specialised form is that its hypotheses are exactly the ones available in the
applications (the §6 model symbol is `C^4`, and only two derivatives in each variable are ever
needed), so that callers do not have to bookkeep the `j₁ + j₂` smoothness budget.
-/
import Mathlib
import Submission.Work.KMTPlan.A6.SymToolbox_coeff2_dp

namespace Work.KMTPlan.A6

theorem coeff2_dp_id (σ : ℝ → ℝ → ℂ)
    (hper1 : ∀ x y, σ (x + 1) y = σ x y) (hper2 : ∀ x y, σ x (y + 1) = σ x y)
    (hsm : ContDiff ℝ 4 (fun p : ℝ × ℝ => σ p.1 p.2))
    {j₁ j₂ : ℕ} (hj₁ : j₁ ≤ 2) (hj₂ : j₂ ≤ 2) (p₁ p₂ : ℤ) :
    Work.KMTPlan.A6.coeff2 (Work.KMTPlan.A6.dp j₁ j₂ σ) p₁ p₂
      = (2 * (Real.pi : ℂ) * Complex.I * (p₁ : ℂ)) ^ j₁
        * (2 * (Real.pi : ℂ) * Complex.I * (p₂ : ℂ)) ^ j₂
        * Work.KMTPlan.A6.coeff2 σ p₁ p₂ := by
  -- `C^4` implies the `C^{j₁+j₂}` joint smoothness requested by the general statement.
  have h : ContDiff ℝ (((j₁ + j₂ : ℕ)) : WithTop ℕ∞) (fun p : ℝ × ℝ => σ p.1 p.2) :=
    hsm.of_le (by exact_mod_cast (by omega : j₁ + j₂ ≤ 4))
  exact SymToolbox_coeff2_dp σ j₁ j₂ hper1 hper2 h p₁ p₂

end Work.KMTPlan.A6
