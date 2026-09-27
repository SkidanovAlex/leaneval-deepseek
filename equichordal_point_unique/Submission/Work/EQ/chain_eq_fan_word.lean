import Mathlib
import Submission.Work.EQ.H0_fibre_defs
import Submission.Work.EQ.DefsCore

namespace Work.EQ

/-- **A chain is the fan read off from its branch word.**

Context (`Work.EQ.H0_fibre_defs`).  `chainWord a p : ℤ → Bool` is the branch word of `p`
(`chainWord a p n = true` iff `p.1 n` is the principal backward branch `invBranch a true` of
`p.1 (n+1)`), `chainWord_spec` gives `p.1 n = invBranch a (chainWord a p n) (p.1 (n+1))` for a
chain, and `fanWord σ m j` is the list `[σ m, σ (m+1), …, σ (m+j-1)]` of `j` successive signs.
`fan a h ε u` is Rychlik's stable fan, defined by `fan a h [] u = germC a h u` and
`fan a h (s :: ε) u = invBranch a s (fan a h ε ((eqLam a) * u))`.

Hypothesis `hN`: from index `N` on, the chain is the stable germ tail,
`p.1 n = germC a h (λ^n * ψ₁)` (`ψ₁ = p.2.1`, `λ = eqLam a`).  Conclusion: for every number `j` of
steps and every starting index `m` whose `j`-th successor `m + j` is at least `N`,
`p.1 m = fan a h [σ m, …, σ (m+j-1)] (λ^m * ψ₁)`.

This is an induction on `j` using the recursion of `fan`: at `j+1` the induction hypothesis at
`m+1` gives `p.1 (m+1) = fan a h (fanWord σ (m+1) j) (λ^(m+1) * ψ₁)`, and
`chainWord_spec` at `m` gives `p.1 m = invBranch a (σ m) (p.1 (m+1))`; the exponent identity
`λ^(m+1) = λ * λ^m` (`zpow_add₀`, needs `λ ≠ 0`, which `0 < a < 1` supplies) then matches the
`fan` recursion, and `fanWord σ m (j+1) = σ m :: fanWord σ (m+1) j` is definitional. -/
theorem chain_eq_fan_word {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {h : ℂ → ℂ} {p : ChainData}
    (hp : IsChain a h p) {N : ℤ}
    (hN : ∀ n : ℤ, N ≤ n → p.1 n = germC a h ((eqLam a : ℂ) ^ n * p.2.1)) :
    ∀ (j : ℕ) (m : ℤ), N ≤ m + (j : ℤ) →
      p.1 m = fan a h (fanWord (chainWord a p) m j) ((eqLam a : ℂ) ^ m * p.2.1) := by
  have hlam : (eqLam a : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (ne_of_gt (eqLam_pos' ha0 ha1))
  intro j
  induction j with
  | zero =>
      intro m hm
      have hm' : N ≤ m := by simpa using hm
      rw [hN m hm']
      rfl
  | succ j ih =>
      intro m hm
      have hle : N ≤ (m + 1) + (j : ℤ) := by
        have h1 : (m + 1) + (j : ℤ) = m + ((j + 1 : ℕ) : ℤ) := by push_cast; ring
        rw [h1]; exact hm
      have hIH := ih (m + 1) hle
      have harg : (eqLam a : ℂ) ^ (m + 1) * p.2.1 =
          (eqLam a : ℂ) * ((eqLam a : ℂ) ^ m * p.2.1) := by
        rw [zpow_add₀ hlam m 1, zpow_one]; ring
      rw [harg] at hIH
      rw [fanWord_succ]
      show p.1 m = invBranch a (chainWord a p m)
        (fan a h (fanWord (chainWord a p) (m + 1) j)
          ((eqLam a : ℂ) * ((eqLam a : ℂ) ^ m * p.2.1)))
      rw [chainWord_spec hp m, hIH]

end Work.EQ
