/-
# ZeroFreeTables/XY/ChenSumNonneg2

`ChenSumNonneg2`: the five-term Chen combination

`14379·Σ(σ,1) + 24480·Σ(σ+iγ,χ) + 14900·Σ(σ+2iγ,1) + 6000·Σ(σ+3iγ,χ) + 1250·Σ(σ+4iγ,1)`

of the Heath-Brown smoothing functional `SigmaP3L` is **non-negative**, for a real character
`χ` (`χ² = 1`), `0 < L`, `1 < σ` and `0 < a + lam`.

## Mechanism

Write `α = a + lam > 0` and `u(y) = α + α²y + (1/3)α³y²`, so that the `n`-th summand of
`SigmaP3L q L ψ s a lam` is `Λ(n) Re(ψ(n)/n^s) u(log n / L)`.  Because `α > 0` the quadratic
`u` is non-negative on all of `ℝ`, and because `χ² = 1` the character `χ^k` is `1, χ, 1, χ, 1`
for `k = 0,…,4`.  So the whole combination is the finite `k`-sum attached to the Chebyshev
combination

`14379 T₀ + 24480 T₁ + 14900 T₂ + 6000 T₃ + 1250 T₄ = (100x² + 120x + 27)² ≥ 0`,

which is exactly the pointwise non-negativity `ksum_trigPoly_pointwise` supplies (the point
`w = χ(n) n^{-iγ}` on the unit circle has `Re(w^k) = T_k(Re w)`; at non-units every character
value vanishes).  The only extra input here — compared with the compactly supported
`Ksum`-version `ksum_trigPoly_nonneg` — is the absolute convergence of the five `Σ`-summands at
`Re s > 1` (`SummableSigmaP3L`), which lets the `tsum`s be linearised.
-/
import Mathlib
import Submission.Work.ZeroFreeTables.P3.DefsL
import Submission.Work.ZeroFreeTables.P9.Defs
import Submission.Work.ZeroFreeTables.P9.SigmaP3LChangeLevelAux
import Submission.Work.ZeroFreeTables.ksum_trigPoly_pointwise
import Submission.Work.ZeroFreeTables.P3.Pointwise91
import Submission.Work.ZeroFreeTables.XY.SummableSigmaP3L

open DirichletCharacter Complex
open scoped Classical BigOperators

namespace Work.ZeroFreeTables.XY

noncomputable section

/-- Coefficient vector `(14379, 24480, 14900, 6000, 1250)` of the five-term Chen combination. -/
def chenC : ℕ → ℝ
  | 0 => 14379
  | 1 => 24480
  | 2 => 14900
  | 3 => 6000
  | 4 => 1250
  | _ => 0

/-- The `k`-th evaluation point `σ + i k γ`. -/
def chenPt (σ γ : ℝ) (k : ℕ) : ℂ := (σ : ℂ) + ((k : ℝ) : ℂ) * (γ : ℂ) * Complex.I

/-- The `n`-th summand of the `k`-th `SigmaP3L` of the Chen combination. -/
def chenG (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (σ γ a lam L : ℝ) (k n : ℕ) : ℝ :=
  (ArithmeticFunction.vonMangoldt n : ℝ) *
    ((χ ^ k) (n : ZMod q) / (n : ℂ) ^ (chenPt σ γ k)).re * Work.ZeroFreeTables.hbWL L a lam n

/-! ## The Chebyshev identity -/

lemma chebyshevT_3_eq :
    Polynomial.Chebyshev.T ℝ 3 = 2 * Polynomial.X * Polynomial.Chebyshev.T ℝ 2
      - Polynomial.Chebyshev.T ℝ 1 := by
  have := Polynomial.Chebyshev.T_eq ℝ 3
  norm_num at this ⊢
  exact this

lemma chebyshevT_4_eq :
    Polynomial.Chebyshev.T ℝ 4 = 2 * Polynomial.X * Polynomial.Chebyshev.T ℝ 3
      - Polynomial.Chebyshev.T ℝ 2 := by
  have := Polynomial.Chebyshev.T_eq ℝ 4
  norm_num at this ⊢
  exact this

/-- `14379 T₀ + 24480 T₁ + 14900 T₂ + 6000 T₃ + 1250 T₄ = (100x² + 120x + 27)²`. -/
lemma chenC_cheb (x : ℝ) :
    (∑ k ∈ Finset.range (4 + 1), chenC k * (Polynomial.Chebyshev.T ℝ (k : ℤ)).eval x)
      = (100 * x ^ 2 + 120 * x + 27) ^ 2 := by
  have h0 : (Polynomial.Chebyshev.T ℝ 0).eval x = 1 := by
    rw [Polynomial.Chebyshev.T_zero]; simp
  have h1 : (Polynomial.Chebyshev.T ℝ 1).eval x = x := by
    rw [Polynomial.Chebyshev.T_one]; simp
  have h2 : (Polynomial.Chebyshev.T ℝ 2).eval x = 2 * x ^ 2 - 1 := by
    rw [Polynomial.Chebyshev.T_two]; simp
  have h3 : (Polynomial.Chebyshev.T ℝ 3).eval x = 4 * x ^ 3 - 3 * x := by
    rw [chebyshevT_3_eq, Polynomial.Chebyshev.T_two, Polynomial.Chebyshev.T_one]; simp; ring
  have h4 : (Polynomial.Chebyshev.T ℝ 4).eval x = 8 * x ^ 4 - 8 * x ^ 2 + 1 := by
    rw [chebyshevT_4_eq, chebyshevT_3_eq, Polynomial.Chebyshev.T_two,
      Polynomial.Chebyshev.T_one]
    simp; ring
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, chenC]
  push_cast
  rw [h0, h1, h2, h3, h4]
  ring

/-! ## Pointwise non-negativity -/

/-- The pointwise (single `n`) non-negativity of the Chen combination, valid for `n ≥ 1`:
the weight `u(log n / L)` is non-negative (`0 < a + lam`) and the Chebyshev combination of the
character values is a square. -/
lemma chenPointwise {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    {σ γ a lam L : ℝ} (hα : 0 < a + lam) {n : ℕ} (hn : 1 ≤ n) :
    0 ≤ ∑ k ∈ Finset.range (4 + 1), chenC k * chenG q χ σ γ a lam L k n := by
  have hf : ∀ t : ℝ, 0 ≤ (fun y : ℝ => (a + lam) + (a + lam) ^ 2 * y
      + (1/3) * (a + lam) ^ 3 * y ^ 2) t := by
    intro t
    change 0 ≤ (a + lam) + (a + lam) ^ 2 * t + (1/3) * (a + lam) ^ 3 * t ^ 2
    have hthis : (a + lam) + (a + lam) ^ 2 * t + (1/3) * (a + lam) ^ 3 * t ^ 2
        = (a + lam) * (1 + (a + lam) * t + (1/3) * (a + lam) ^ 2 * t ^ 2) := by ring
    rw [hthis]
    refine mul_nonneg hα.le ?_
    nlinarith [sq_nonneg ((a + lam) * t + 3/2)]
  have hP : ∀ x ∈ Set.Icc (-1 : ℝ) 1,
      0 ≤ ∑ k ∈ Finset.range (4 + 1), chenC k * (Polynomial.Chebyshev.T ℝ (k : ℤ)).eval x := by
    intro x _
    rw [chenC_cheb x]
    nlinarith [sq_nonneg (100 * x ^ 2 + 120 * x + 27)]
  have h := ksum_trigPoly_pointwise (f := fun y : ℝ => (a + lam) + (a + lam) ^ 2 * y
      + (1/3) * (a + lam) ^ 3 * y ^ 2) hf (L := L) (β := σ) (γ := γ) (c := chenC) (d := 4)
      hP χ hn
  simpa only [chenG, chenPt, Work.ZeroFreeTables.hbWL] using h

/-- `chenPt` in the form used by `SummableSigmaP3L`. -/
lemma chenPt_eq' (σ γ : ℝ) (k : ℕ) :
    chenPt σ γ k = (σ : ℂ) + (((k : ℝ) * γ : ℝ) : ℂ) * Complex.I := by
  simp only [chenPt]
  push_cast
  ring

/-- `SigmaP3L` is `L⁻¹` times the `tsum` of `chenG`. -/
lemma chenG_tsum (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (σ γ a lam L : ℝ) (k : ℕ) :
    SigmaP3L q L (χ ^ k) (chenPt σ γ k) a lam = L⁻¹ * ∑' n, chenG q χ σ γ a lam L k n := rfl

/-! ## Assembly -/

/-- The `k`-sum form of `ChenSumNonneg2`. -/
lemma chenSumNonneg_k {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    {σ γ a lam L : ℝ} (hL : 0 < L) (hα : 0 < a + lam)
    (hsumm : ∀ k, Summable (chenG q χ σ γ a lam L k)) :
    0 ≤ ∑ k ∈ Finset.range (4 + 1), chenC k * SigmaP3L q L (χ ^ k) (chenPt σ γ k) a lam := by
  have step1 : ∑ k ∈ Finset.range (4 + 1), chenC k * SigmaP3L q L (χ ^ k) (chenPt σ γ k) a lam
      = L⁻¹ * ∑ k ∈ Finset.range (4 + 1),
          chenC k * (∑' n, chenG q χ σ γ a lam L k n) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [chenG_tsum]
    ring
  rw [step1, Work.ZeroFreeTables.P3.tsum_finset_lincomb (Finset.range (4 + 1))
        (chenG q χ σ γ a lam L) chenC (fun k _ => hsumm k)]
  refine mul_nonneg (inv_nonneg.mpr hL.le) (tsum_nonneg (fun n => ?_))
  rcases Nat.eq_zero_or_pos n with h0 | hpos
  · subst h0
    have hΛ : ArithmeticFunction.vonMangoldt 0 = 0 := by
      rw [ArithmeticFunction.vonMangoldt_eq_zero_iff]; exact not_isPrimePow_zero
    simp [chenG, hΛ]
  · exact chenPointwise χ hα hpos

theorem ChenSumNonneg2 :
    ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ ^ 2 = 1 →
      ∀ {σ γ a lam L : ℝ}, 0 < L → 1 < σ → 0 < a + lam →
      0 ≤ 14379 * Work.ZeroFreeTables.SigmaP3L q L (1 : DirichletCharacter ℂ q) ((σ : ℂ)) a lam
        + 24480 * Work.ZeroFreeTables.SigmaP3L q L χ ((σ : ℂ) + (γ : ℂ) * Complex.I) a lam
        + 14900 * Work.ZeroFreeTables.SigmaP3L q L (1 : DirichletCharacter ℂ q)
            ((σ : ℂ) + 2 * (γ : ℂ) * Complex.I) a lam
        + 6000 * Work.ZeroFreeTables.SigmaP3L q L χ
            ((σ : ℂ) + 3 * (γ : ℂ) * Complex.I) a lam
        + 1250 * Work.ZeroFreeTables.SigmaP3L q L (1 : DirichletCharacter ℂ q)
            ((σ : ℂ) + 4 * (γ : ℂ) * Complex.I) a lam := by
  intro q _ χ hχ σ γ a lam L hL hσ hα
  have hsumm : ∀ k, Summable (chenG q χ σ γ a lam L k) := by
    intro k
    have h := SummableSigmaP3L (χ ^ k) (σ := σ) (Δ := (k : ℝ) * γ) (a := a) (lam := lam)
      (L := L) hσ hL
    rw [show chenG q χ σ γ a lam L k = (fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℝ) *
        ((χ ^ k) (n : ZMod q) / (n : ℂ) ^ ((σ : ℂ) + (((k : ℝ) * γ : ℝ) : ℂ) * Complex.I)).re *
        Work.ZeroFreeTables.hbWL L a lam n) from by
      funext n
      simp only [chenG, chenPt_eq']]
    exact h
  have h := chenSumNonneg_k χ hL hα hsumm
  have hsum_eq : (∑ k ∈ Finset.range (4 + 1),
        chenC k * Work.ZeroFreeTables.SigmaP3L q L (χ ^ k) (chenPt σ γ k) a lam)
      = 14379 * Work.ZeroFreeTables.SigmaP3L q L (1 : DirichletCharacter ℂ q) ((σ : ℂ)) a lam
        + 24480 * Work.ZeroFreeTables.SigmaP3L q L χ
            ((σ : ℂ) + (γ : ℂ) * Complex.I) a lam
        + 14900 * Work.ZeroFreeTables.SigmaP3L q L (1 : DirichletCharacter ℂ q)
            ((σ : ℂ) + 2 * (γ : ℂ) * Complex.I) a lam
        + 6000 * Work.ZeroFreeTables.SigmaP3L q L χ
            ((σ : ℂ) + 3 * (γ : ℂ) * Complex.I) a lam
        + 1250 * Work.ZeroFreeTables.SigmaP3L q L (1 : DirichletCharacter ℂ q)
            ((σ : ℂ) + 4 * (γ : ℂ) * Complex.I) a lam := by
    have h2 : χ ^ 2 = 1 := hχ
    have h3 : χ ^ 3 = χ := by rw [show (3 : ℕ) = 2 + 1 from rfl, pow_succ, hχ, one_mul]
    have h4 : χ ^ 4 = 1 := by rw [show (4 : ℕ) = 2 + 2 from rfl, pow_add, hχ, one_mul]
    have e0 : chenPt σ γ 0 = (σ : ℂ) := by simp [chenPt]
    have e1 : chenPt σ γ 1 = (σ : ℂ) + (γ : ℂ) * Complex.I := by simp [chenPt]
    have e2 : chenPt σ γ 2 = (σ : ℂ) + 2 * (γ : ℂ) * Complex.I := by simp [chenPt]
    have e3 : chenPt σ γ 3 = (σ : ℂ) + 3 * (γ : ℂ) * Complex.I := by simp [chenPt]
    have e4 : chenPt σ γ 4 = (σ : ℂ) + 4 * (γ : ℂ) * Complex.I := by simp [chenPt]
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, chenC, pow_zero, pow_one,
      h2, h3, h4]
    rw [e0, e1, e2, e3, e4]
    ring
  rw [← hsum_eq]
  exact h

end

end Work.ZeroFreeTables.XY
