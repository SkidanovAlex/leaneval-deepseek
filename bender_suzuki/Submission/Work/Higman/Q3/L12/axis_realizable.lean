import Mathlib
import Submission.Work.Higman.Q3.cocycle_diagonal_pinning

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.Higman.Q3.L12

-- `haveI` here genuinely installs a local `Fintype` instance used by later elaboration.
set_option linter.style.haveILetI false in

/-- **Axis realizability (`X = ⟨U,W⟩` is `A(n,θ)` or abelian).**

Let `B : 𝔽 × 𝔽 → 𝔽` (`𝔽 = 𝔽_{2ⁿ}`, `n ≥ 1`) be biadditive and equivariant for
`(α,γ) ↦ (ν α, ν γ)` with multiplier `lam`, and suppose some diagonal value `B α α` is nonzero.
Then `ν ^ (2 ^ i) * ν ^ (2 ^ j) = lam` for some `i, j < n`: the axis has a nonzero bidegree
`(i,j)`, i.e. the axis exponent is a sum of two Frobenius powers.

Proof: `B` is a sum of Frobenius monomials `Σ e_{ij} α^{2^i} γ^{2^j}`
(`Work.Higman.Q3.bivariate_additive_frob`, with `hcard : Fintype.card 𝔽 = 2 ^ n`, available from
`GaloisField.card 2 n hn0` for `n ≠ 0`); a nonzero diagonal forces some `e_{ij} ≠ 0` (otherwise
`B ≡ 0`), and equivariance then gives the resonance `ν^{2^i} * ν^{2^j} = lam`
(`Work.Higman.Q3.bivariate_frob_resonance`). -/
theorem axis_realizable {n : ℕ} (hn : 1 ≤ n)
    {ν lam : GaloisField 2 n}
    (B : GaloisField 2 n → GaloisField 2 n → GaloisField 2 n)
    (h1 : ∀ β α α', B (α + α') β = B α β + B α' β)
    (h2 : ∀ α β β', B α (β + β') = B α β + B α β')
    (heq : ∀ α β, B (ν * α) (ν * β) = lam * B α β)
    (hne : ∃ α : GaloisField 2 n, B α α ≠ 0) :
    ∃ i j : ℕ, i < n ∧ j < n ∧ ν ^ (2 ^ i) * ν ^ (2 ^ j) = lam := by
  classical
  have hn0 : n ≠ 0 := by omega
  haveI : Fintype (GaloisField 2 n) := Fintype.ofFinite _
  have hcard : Fintype.card (GaloisField 2 n) = 2 ^ n := by
    rw [← Nat.card_eq_fintype_card]; exact GaloisField.card 2 n hn0
  -- expand the biadditive `B` in the basis of Frobenius monomials
  obtain ⟨e, hexp⟩ := Work.Higman.Q3.bivariate_additive_frob hcard B h1 h2
  -- a nonzero diagonal value forces some coefficient to be nonzero
  have hne_coeff : ∃ k l, k < n ∧ l < n ∧ e k l ≠ 0 := by
    by_contra hcon
    obtain ⟨α, hα⟩ := hne
    apply hα
    have heq0 : ∀ k l, k < n → l < n → e k l = 0 := by
      intro k l hk hl
      by_contra hne'
      exact hcon ⟨k, l, hk, hl, hne'⟩
    rw [hexp α α]
    apply Finset.sum_eq_zero
    intro k hk
    apply Finset.sum_eq_zero
    intro l hl
    simp [heq0 k l (Finset.mem_range.mp hk) (Finset.mem_range.mp hl)]
  obtain ⟨k, l, hk, hl, hkel⟩ := hne_coeff
  -- equivariance evaluates the resonance at the nonzero bidegree
  exact ⟨k, l, hk, hl,
    Work.Higman.Q3.bivariate_frob_resonance hcard (ν := ν) (ν' := ν) (lam := lam) B e hexp heq
      k l hk hl hkel⟩

end Work.Higman.Q3.L12
