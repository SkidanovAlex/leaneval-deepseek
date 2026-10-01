/-
# ZeroFreeTables/HB95h2/pointwise — the five-term positivity of the `P₃` functional

The pointwise (in the Dirichlet series) non-negativity of the five-term combination

`14379·Σ(σ,1) + 24480·Σ(σ+iγ,χ₁) + 14900·Σ(σ+2iγ,1) + 6000·Σ(σ+3iγ,χ₁) + 1250·Σ(σ+4iγ,1)`

of Heath-Brown's smoothing functional `Σ(s,ψ) = SigmaP3L q (log q) ψ s a λ₁` (HB (8.4) with the
coefficient-correct weight `u(y) = α + α²y + (1/3)α³y²`, `α = a + λ₁`), for a *real* character
`χ₁` (`χ₁² = 1`).

## Mechanism

Write `α = a + λ₁ ≥ 0`.  The `n`-th summand of `SigmaP3L q L ψ s a λ₁` is
`Λ(n)·Re(ψ(n)/n^s)·u(log n / L)`, where `u(y) = α(1 + αy + α²y²/3) ≥ 0` for `α ≥ 0` (the
quadratic has discriminant `-1/3 < 0`; for `α = 0` the weight vanishes identically, in which case
every `Σ` is `0` and the claim is trivial).  Since `χ₁² = 1`, the characters `χ₁^k`, `k = 0,…,4`,
are `1, χ₁, 1, χ₁, 1`, and for a unit `n` of `ZMod q` the point `w = χ₁(n)·n^{-iγ}` lies on the
unit circle with `Re(w^k) = T_k(Re w)`.  So the whole combination is the finite `k`-sum attached to
the Chebyshev combination

`14379 T₀ + 24480 T₁ + 14900 T₂ + 6000 T₃ + 1250 T₄ = (100x² + 120x + 27)² ≥ 0`,

which is exactly the pointwise non-negativity `ksum_trigPoly_pointwise` supplies; the additional
input for the *non*-compactly-supported weight `u` is the absolute convergence of the five
`Σ`-summands at `Re s > 1` (`XY.SummableSigmaP3L`), which lets the `tsum`s be linearised.

This is the `L = log q` instance of `Work.ZeroFreeTables.XY.ChenSumNonneg2` (`0 < a + λ₁`), with
the degenerate `a + λ₁ = 0` case and the `2 ≤ q` hypothesis (`log q > 0`) handled separately.
-/
import Mathlib
import Submission.Work.ZeroFreeTables.P3.DefsL
import Submission.Work.ZeroFreeTables.P9.HbCombinationL_nonneg
import Submission.Work.ZeroFreeTables.XY.ChenSumNonneg2

open DirichletCharacter
open scoped Classical BigOperators

noncomputable section

namespace Work.ZeroFreeTables.HB95h2

/-- At `α = a + λ₁ = 0` the smoothing weight `u(y) = α + α²y + (1/3)α³y²` vanishes identically. -/
lemma hbWL_eq_zero_of {L a lam₁ : ℝ} (h : a + lam₁ = 0) (n : ℕ) :
    Work.ZeroFreeTables.hbWL L a lam₁ n = 0 := by
  simp only [Work.ZeroFreeTables.hbWL, h]
  ring

/-- Consequently every `SigmaP3L` vanishes at `α = a + λ₁ = 0`. -/
lemma SigmaP3L_eq_zero_of {q : ℕ} [NeZero q] {L a lam₁ : ℝ} (h : a + lam₁ = 0)
    (ψ : DirichletCharacter ℂ q) (s : ℂ) :
    Work.ZeroFreeTables.SigmaP3L q L ψ s a lam₁ = 0 := by
  rw [Work.ZeroFreeTables.SigmaP3L_eq_tsum]
  have hfun : (fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℝ) *
      (ψ (n : ZMod q) / (n : ℂ) ^ s).re * Work.ZeroFreeTables.hbWL L a lam₁ n)
      = fun _ => (0 : ℝ) := by
    funext n
    rw [hbWL_eq_zero_of h n, mul_zero]
  rw [hfun]
  simp

theorem pointwise {q : ℕ} [NeZero q] (χ₁ : DirichletCharacter ℂ q) (hχ₁ : χ₁ ^ 2 = 1)
    {a lam₁ σ γ : ℝ} (hα : 0 ≤ a + lam₁) (hσ : 1 < σ) (hq : 2 ≤ q) :
    0 ≤ 14379 * Work.ZeroFreeTables.SigmaP3L q (Real.log q) 1 (σ : ℂ) a lam₁
      + 24480 * Work.ZeroFreeTables.SigmaP3L q (Real.log q) χ₁ ((σ : ℂ) + (γ : ℂ) * Complex.I) a lam₁
      + 14900 * Work.ZeroFreeTables.SigmaP3L q (Real.log q) 1 ((σ : ℂ) + (((2 : ℝ) * γ) : ℂ) * Complex.I) a lam₁
      + 6000 * Work.ZeroFreeTables.SigmaP3L q (Real.log q) χ₁ ((σ : ℂ) + (((3 : ℝ) * γ) : ℂ) * Complex.I) a lam₁
      + 1250 * Work.ZeroFreeTables.SigmaP3L q (Real.log q) 1 ((σ : ℂ) + (((4 : ℝ) * γ) : ℂ) * Complex.I) a lam₁ := by
  by_cases hα0 : a + lam₁ = 0
  · -- degenerate case: the weight vanishes identically, so every term is `0`
    have hz : ∀ (ψ : DirichletCharacter ℂ q) (s : ℂ),
        Work.ZeroFreeTables.SigmaP3L q (Real.log q) ψ s a lam₁ = 0 :=
      fun ψ s => SigmaP3L_eq_zero_of hα0 ψ s
    simp [hz]
  · have hαpos : 0 < a + lam₁ := lt_of_le_of_ne hα (Ne.symm hα0)
    have hlogq : 0 < Real.log (q : ℝ) :=
      Real.log_pos (by exact_mod_cast (show 1 < q by omega))
    have h := Work.ZeroFreeTables.XY.ChenSumNonneg2 q χ₁ hχ₁
      (σ := σ) (γ := γ) (a := a) (lam := lam₁) (L := Real.log q) hlogq hσ hαpos
    -- the two point-forms `(σ:ℂ) + (k*γ : ℝ) * I` and `(σ:ℂ) + k * (γ:ℂ) * I` agree:
    -- normalising the casts on both sides brings them to the same term
    push_cast
    exact h

end Work.ZeroFreeTables.HB95h2
