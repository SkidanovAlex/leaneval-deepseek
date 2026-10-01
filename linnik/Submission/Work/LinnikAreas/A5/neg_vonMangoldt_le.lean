import Mathlib

namespace Work.LinnikAreas.A5

open ArithmeticFunction

/-- Pointwise (termwise) comparison underlying `neg_vonMangoldt_le`: for any `c ≥ 0` and `n`,
`-Λ(n)·Re(χ(n)/n^σ)·c ≤ Λ(n)·n^{-σ}·c`.

For `n = 0` both sides vanish because `Λ 0 = 0`.  For `n ≥ 1` we combine the elementary bound
`-Re(z) ≤ ‖z‖ ≤ n^{-σ}` for `z = χ(n)/n^σ` with `Λ n ≥ 0` and `c ≥ 0`. -/
lemma vonMangoldt_termwise {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {σ : ℝ}
    {c : ℝ} (hc : 0 ≤ c) (n : ℕ) :
    -((ArithmeticFunction.vonMangoldt n : ℝ) *
        ((χ (n : ZMod q) / (n : ℂ) ^ ((σ : ℂ))).re) * c)
      ≤ (ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-σ) * c := by
  rcases Nat.eq_zero_or_pos n with hn0 | hn
  · subst hn0
    simp [ArithmeticFunction.vonMangoldt_apply]
  · have hn0' : (0 : ℝ) < n := by exact_mod_cast hn
    have hcomplex : -((χ (n : ZMod q) / (n : ℂ) ^ ((σ : ℂ))).re) ≤ (n : ℝ) ^ (-σ) := by
      have h1 : -((χ (n : ZMod q) / (n : ℂ) ^ ((σ : ℂ))).re)
          ≤ ‖χ (n : ZMod q) / (n : ℂ) ^ ((σ : ℂ))‖ := by
        have h := Complex.re_le_norm (-(χ (n : ZMod q) / (n : ℂ) ^ ((σ : ℂ))))
        simpa using h
      have hnorm : ‖((n : ℂ) ^ ((σ : ℂ)))‖ = (n : ℝ) ^ σ := by
        have h2 := Complex.norm_cpow_eq_rpow_re_of_pos hn0' ((σ : ℂ))
        simpa using h2
      have h2 : ‖χ (n : ZMod q) / (n : ℂ) ^ ((σ : ℂ))‖ ≤ (n : ℝ) ^ (-σ) := by
        rw [Complex.norm_div, hnorm, Real.rpow_neg (le_of_lt hn0'), div_eq_mul_inv]
        simpa using mul_le_mul_of_nonneg_right (DirichletCharacter.norm_le_one χ (n : ZMod q))
          (inv_nonneg.mpr (le_of_lt (Real.rpow_pos_of_pos hn0' σ)))
      linarith
    have hw : (0 : ℝ) ≤ (ArithmeticFunction.vonMangoldt n : ℝ) :=
      ArithmeticFunction.vonMangoldt_nonneg
    have step1 : (ArithmeticFunction.vonMangoldt n : ℝ) *
          (-((χ (n : ZMod q) / (n : ℂ) ^ ((σ : ℂ))).re))
        ≤ (ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-σ) :=
      mul_le_mul_of_nonneg_left hcomplex hw
    have step2 : (ArithmeticFunction.vonMangoldt n : ℝ) *
            (-((χ (n : ZMod q) / (n : ℂ) ^ ((σ : ℂ))).re)) * c
        ≤ (ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-σ) * c :=
      mul_le_mul_of_nonneg_right step1 hc
    have heq : -((ArithmeticFunction.vonMangoldt n : ℝ) *
          ((χ (n : ZMod q) / (n : ℂ) ^ ((σ : ℂ))).re) * c)
        = (ArithmeticFunction.vonMangoldt n : ℝ) *
            (-((χ (n : ZMod q) / (n : ℂ) ^ ((σ : ℂ))).re)) * c := by
      ring
    rw [heq]
    exact step2

/-
The elementary pointwise step of HB Lemma 13.3 (the passage from the smoothing estimate at
`s = σ ∈ (0,1]` to the Chebyshev-ψ/Lambert input): for a non-negative weight `f ≥ 0` supported in
`(-∞,K]` and `σ > 0`, the von Mangoldt series twisted by the character is bounded below by minus
the principal (untwisted) series.  Termwise this is
`-Re(χ(a)/n^σ) ≤ |χ(a)|/n^σ ≤ n^{-σ}` for `n ≥ 1` (`DirichletCharacter.norm_le_one` and
`Complex.norm_cpow_eq_rpow_re_of_pos`), and the cases `n = 0, 1` are trivial because
`Λ 0 = Λ 1 = 0` (note `Real.log 0 = Real.log 1 = 0`, so the argument of `f` is always `≥ 0`).
Both series are finitely supported (`f (log n / L) = 0` for `log n ≥ K*L`), so summability and
the termwise comparison are available.
-/
theorem neg_vonMangoldt_le {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {K L σ : ℝ}
    (hL : 0 < L) (hσ : 0 < σ) {f : ℝ → ℝ} (hsupp : ∀ t : ℝ, K ≤ t → f t = 0)
    (hnn : ∀ t : ℝ, 0 ≤ f t) :
    -(∑' n : ℕ, (ArithmeticFunction.vonMangoldt n : ℝ) *
        ((χ (n : ZMod q) / (n : ℂ) ^ ((σ : ℂ))).re) * f (Real.log n / L))
      ≤ ∑' n : ℕ, (ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-σ) *
          f (Real.log n / L) := by
  -- both series are supported where `f (log n / L) ≠ 0`, which forces `n` bounded.
  obtain ⟨N, hN⟩ : ∃ N : ℕ, ∀ n : ℕ, N ≤ n → f (Real.log n / L) = 0 := by
    refine ⟨max 1 ⌈Real.exp (K * L)⌉₊, fun n hn => hsupp _ ?_⟩
    rw [le_div_iff₀ hL]
    have hineq : K * L ≤ Real.log (↑(max 1 ⌈Real.exp (K * L)⌉₊) : ℝ) := by
      have h1 : Real.exp (K * L) ≤ (⌈Real.exp (K * L)⌉₊ : ℝ) := Nat.le_ceil _
      have h2 : (⌈Real.exp (K * L)⌉₊ : ℝ) ≤ (↑(max 1 ⌈Real.exp (K * L)⌉₊) : ℝ) := by
        exact_mod_cast le_max_right 1 ⌈Real.exp (K * L)⌉₊
      calc K * L = Real.log (Real.exp (K * L)) := (Real.log_exp _).symm
        _ ≤ Real.log (↑(max 1 ⌈Real.exp (K * L)⌉₊) : ℝ) :=
            Real.log_le_log (Real.exp_pos _) (le_trans h1 h2)
    have hNpos : (0 : ℝ) < (↑(max 1 ⌈Real.exp (K * L)⌉₊) : ℝ) := by
      have : (0 : ℕ) < max 1 ⌈Real.exp (K * L)⌉₊ :=
        lt_of_lt_of_le Nat.zero_lt_one (le_max_left _ _)
      exact_mod_cast this
    have hmono : Real.log (↑(max 1 ⌈Real.exp (K * L)⌉₊) : ℝ) ≤ Real.log n :=
      Real.log_le_log hNpos (by exact_mod_cast hn)
    linarith
  have hA : ∀ n : ℕ, n ∉ Finset.range N →
      (ArithmeticFunction.vonMangoldt n : ℝ) *
        ((χ (n : ZMod q) / (n : ℂ) ^ ((σ : ℂ))).re) * f (Real.log n / L) = 0 := by
    intro n hn
    simp only [Finset.mem_range, not_lt] at hn
    rw [hN n hn, mul_zero]
  have hB : ∀ n : ℕ, n ∉ Finset.range N →
      (ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-σ) *
        f (Real.log n / L) = 0 := by
    intro n hn
    simp only [Finset.mem_range, not_lt] at hn
    rw [hN n hn, mul_zero]
  rw [tsum_eq_sum hA, tsum_eq_sum hB, ← Finset.sum_neg_distrib]
  exact Finset.sum_le_sum fun n _ => vonMangoldt_termwise χ (hnn _) n

end Work.LinnikAreas.A5
