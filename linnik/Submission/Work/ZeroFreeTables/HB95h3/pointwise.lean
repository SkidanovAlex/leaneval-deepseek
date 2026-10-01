/-
# ZeroFreeTables/HB95h3/pointwise — the five-term positivity of the `P₃` functional (cubic χ₁)

The pointwise (in the Dirichlet series) non-negativity of the five-term combination

`14379·Σ(σ,1) + 24480·Σ(σ+iγ,χ₁) + 14900·Σ(σ+2iγ,χ₁²) + 6000·Σ(σ+3iγ,1) + 1250·Σ(σ+4iγ,χ₁)`

of Heath-Brown's smoothing functional `Σ(s,ψ) = SigmaP3L q (log q) ψ s a λ₁` (HB (8.4) with the
coefficient-correct weight `u(y) = α + α²y + (1/3)α³y²`, `α = a + λ₁`), in the case where `χ₁` is
a *cubic* character (`χ₁³ = 1`), so that `χ₁^k` cycles `1, χ₁, χ₁², 1, χ₁` for `k = 0,…,4`.

## Mechanism

Write `α = a + λ₁ ≥ 0`.  The `n`-th summand of `SigmaP3L q L ψ s a λ₁` is
`Λ(n)·Re(ψ(n)/n^s)·u(log n / L)`, where `u(y) = α(1 + αy + α²y²/3) ≥ 0` for `α ≥ 0` (the
quadratic has discriminant `-1/3 < 0`; for `α = 0` the weight vanishes identically, in which case
every `Σ` is `0` and the claim is trivial).  For a unit `n` of `ZMod q` the point
`w = χ₁(n)·n^{-iγ}` lies on the unit circle, and since `χ₁` has order dividing `3` its non-trivial
powers are the order-`3` character `χ₁`, `χ₁²`; the `k`-th value is `χ₁^k = χ₁(n)^k` with
`Re(w^k) = T_k(Re w)`.  So the whole combination is the finite `k`-sum attached to the Chebyshev
combination

`14379 T₀ + 24480 T₁ + 14900 T₂ + 6000 T₃ + 1250 T₄ = (100x² + 120x + 27)² ≥ 0`,

which is exactly the pointwise non-negativity supplied by the general five-term engine
`XY.chenSumNonneg_k` / `ksum_trigPoly_pointwise`.  The only extra input for the
*non*-compactly-supported weight `u` is the absolute convergence of the five `Σ`-summands at
`Re s > 1` (`XY.SummableSigmaP3L`), which lets the `tsum`s be linearised.

This is the `χ₁³ = 1` companion of `Work.ZeroFreeTables.HB95h2.pointwise` (`χ₁² = 1`); the same
five coefficients are used, only the middle character `χ₁²` replaces `1`, and the rewriting
`χ₁³ = 1`, `χ₁⁴ = χ₁` produces the stated combination.
-/
import Mathlib
import Submission.Work.ZeroFreeTables.P3.DefsL
import Submission.Work.ZeroFreeTables.HB95h2.pointwise
import Submission.Work.ZeroFreeTables.XY.ChenSumNonneg2
import Submission.Work.ZeroFreeTables.XY.SummableSigmaP3L

open DirichletCharacter
open scoped Classical BigOperators

noncomputable section

namespace Work.ZeroFreeTables.HB95h3

theorem pointwise {q : ℕ} [NeZero q] (χ₁ : DirichletCharacter ℂ q) (hχ₁ : χ₁ ^ 3 = 1)
    {a lam₁ σ γ : ℝ} (hα : 0 ≤ a + lam₁) (hσ : 1 < σ) (hq : 2 ≤ q) :
    0 ≤ 14379 * Work.ZeroFreeTables.SigmaP3L q (Real.log q) 1 (σ : ℂ) a lam₁
      + 24480 * Work.ZeroFreeTables.SigmaP3L q (Real.log q) χ₁
          ((σ : ℂ) + (γ : ℂ) * Complex.I) a lam₁
      + 14900 * Work.ZeroFreeTables.SigmaP3L q (Real.log q) (χ₁ ^ 2)
          ((σ : ℂ) + (((2 : ℝ) * γ) : ℂ) * Complex.I) a lam₁
      + 6000 * Work.ZeroFreeTables.SigmaP3L q (Real.log q) 1
          ((σ : ℂ) + (((3 : ℝ) * γ) : ℂ) * Complex.I) a lam₁
      + 1250 * Work.ZeroFreeTables.SigmaP3L q (Real.log q) χ₁
          ((σ : ℂ) + (((4 : ℝ) * γ) : ℂ) * Complex.I) a lam₁ := by
  by_cases hα0 : a + lam₁ = 0
  · -- degenerate case: the weight vanishes identically, so every term is `0`
    have hz : ∀ (ψ : DirichletCharacter ℂ q) (s : ℂ),
        Work.ZeroFreeTables.SigmaP3L q (Real.log q) ψ s a lam₁ = 0 :=
      fun ψ s => Work.ZeroFreeTables.HB95h2.SigmaP3L_eq_zero_of hα0 ψ s
    simp [hz]
  · have hαpos : 0 < a + lam₁ := lt_of_le_of_ne hα (Ne.symm hα0)
    have hlogq : 0 < Real.log (q : ℝ) :=
      Real.log_pos (by exact_mod_cast (show 1 < q by omega))
    -- absolute convergence of the five summands at `Re s > 1`
    have hsumm : ∀ k, Summable (Work.ZeroFreeTables.XY.chenG q χ₁ σ γ a lam₁ (Real.log q) k) := by
      intro k
      have h := Work.ZeroFreeTables.XY.SummableSigmaP3L (χ₁ ^ k) (σ := σ) (Δ := (k : ℝ) * γ)
        (a := a) (lam := lam₁) (L := Real.log q) hσ hlogq
      rw [show Work.ZeroFreeTables.XY.chenG q χ₁ σ γ a lam₁ (Real.log q) k
          = (fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℝ) *
              ((χ₁ ^ k) (n : ZMod q) / ((n : ℂ) ^ ((σ : ℂ) + (((k : ℝ) * γ : ℝ) : ℂ) * Complex.I))).re *
              Work.ZeroFreeTables.hbWL (Real.log q) a lam₁ n) from by
        funext n
        simp only [Work.ZeroFreeTables.XY.chenG, Work.ZeroFreeTables.XY.chenPt]
        push_cast
        ring]
      exact h
    -- the general five-term engine, valid for an arbitrary character `χ₁`
    have h := Work.ZeroFreeTables.XY.chenSumNonneg_k χ₁ hlogq hαpos hsumm
    -- rewrite `∑_k chenC k · Σ(χ₁^k, σ+i k γ)` using `χ₁³ = 1`, `χ₁⁴ = χ₁`
    have hsum_eq : (∑ k ∈ Finset.range (4 + 1), Work.ZeroFreeTables.XY.chenC k *
        Work.ZeroFreeTables.SigmaP3L q (Real.log q) (χ₁ ^ k)
          (Work.ZeroFreeTables.XY.chenPt σ γ k) a lam₁)
        = 14379 * Work.ZeroFreeTables.SigmaP3L q (Real.log q) 1 (σ : ℂ) a lam₁
          + 24480 * Work.ZeroFreeTables.SigmaP3L q (Real.log q) χ₁
              ((σ : ℂ) + (γ : ℂ) * Complex.I) a lam₁
          + 14900 * Work.ZeroFreeTables.SigmaP3L q (Real.log q) (χ₁ ^ 2)
              ((σ : ℂ) + (((2 : ℝ) * γ) : ℂ) * Complex.I) a lam₁
          + 6000 * Work.ZeroFreeTables.SigmaP3L q (Real.log q) 1
              ((σ : ℂ) + (((3 : ℝ) * γ) : ℂ) * Complex.I) a lam₁
          + 1250 * Work.ZeroFreeTables.SigmaP3L q (Real.log q) χ₁
              ((σ : ℂ) + (((4 : ℝ) * γ) : ℂ) * Complex.I) a lam₁ := by
      have h4 : χ₁ ^ 4 = χ₁ := by rw [show (4 : ℕ) = 3 + 1 from rfl, pow_succ, hχ₁, one_mul]
      have e0 : Work.ZeroFreeTables.XY.chenPt σ γ 0 = (σ : ℂ) := by
        simp [Work.ZeroFreeTables.XY.chenPt]
      have e1 : Work.ZeroFreeTables.XY.chenPt σ γ 1 = (σ : ℂ) + (γ : ℂ) * Complex.I := by
        simp [Work.ZeroFreeTables.XY.chenPt]
      have e2 : Work.ZeroFreeTables.XY.chenPt σ γ 2
          = (σ : ℂ) + (((2 : ℝ) * γ) : ℂ) * Complex.I := by
        simp only [Work.ZeroFreeTables.XY.chenPt]; push_cast; ring
      have e3 : Work.ZeroFreeTables.XY.chenPt σ γ 3
          = (σ : ℂ) + (((3 : ℝ) * γ) : ℂ) * Complex.I := by
        simp only [Work.ZeroFreeTables.XY.chenPt]; push_cast; ring
      have e4 : Work.ZeroFreeTables.XY.chenPt σ γ 4
          = (σ : ℂ) + (((4 : ℝ) * γ) : ℂ) * Complex.I := by
        simp only [Work.ZeroFreeTables.XY.chenPt]; push_cast; ring
      simp only [Finset.sum_range_succ, Finset.sum_range_zero,
        Work.ZeroFreeTables.XY.chenC, pow_zero, pow_one, hχ₁, h4]
      rw [e0, e1, e2, e3, e4]
      ring
    rw [← hsum_eq]
    exact h

end Work.ZeroFreeTables.HB95h3
