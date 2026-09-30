import Mathlib
import Submission.Work.BMF.N4chain.linnik_newton_defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BMF.N4chain

open Polynomial Finset

/-- **Vieta's formula for `polyOf`.**  The monic polynomial whose roots are the entries of `v` is
the alternating sum of the elementary symmetric evaluations:
`polyOf v = ∑_{j ≤ k} (-1)^j * esymmEval v j * X^(k-j)`. -/
lemma polyOf_eq_sum_esymm {p k : ℕ} (v : Fin k → ZMod p) :
    polyOf v = ∑ j ∈ Finset.range (k + 1),
      (-1 : Polynomial (ZMod p)) ^ j * (Polynomial.C (esymmEval v j) * Polynomial.X ^ (k - j)) := by
  classical
  set s : Multiset (ZMod p) := (Finset.univ : Finset (Fin k)).val.map v with hs
  have hcard : s.card = k := by simp [hs]
  have hesymm : ∀ j, s.esymm j = esymmEval v j := by
    intro j
    rw [esymmEval, MvPolynomial.aeval_esymm_eq_multiset_esymm]
  have hL : (s.map fun t => X - C t).prod = polyOf v := by
    simp [hs, polyOf, Finset.prod_eq_multiset_prod, Function.comp_def]
  have h := Multiset.prod_X_sub_X_eq_sum_esymm s
  rw [hcard] at h
  rw [← hL]
  simp only [← hesymm]
  exact h

/-- If an injective tuple `w` has the same elementary symmetric evaluations as `v` (in all degrees
`m ≤ k`), then `w` is a permutation of `v`. -/
theorem perm_of_esymmEval {p k : ℕ} (hp : p.Prime) {v w : Fin k → ZMod p}
    (hw : Function.Injective w)
    (h : ∀ m, m ≤ k → Work.BMF.N4chain.esymmEval v m = Work.BMF.N4chain.esymmEval w m) :
    ∃ σ : Equiv.Perm (Fin k), ∀ i, w i = v (σ i) := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  -- The elementary symmetric evaluations determine the monic polynomial with roots the entries.
  have hpoly : polyOf v = polyOf w := by
    rw [polyOf_eq_sum_esymm v, polyOf_eq_sum_esymm w]
    refine Finset.sum_congr rfl fun m hm => ?_
    rw [Finset.mem_range] at hm
    rw [h m (Nat.le_of_lt_succ hm)]
  -- Every entry of `w` is a root of `polyOf v`, hence is an entry of `v` (`ZMod p` is a domain).
  have key : ∀ i, ∃ r, w i = v r := by
    intro i
    have h1 : Polynomial.eval (w i) (polyOf w) = 0 := by
      simp only [polyOf]
      rw [Polynomial.eval_prod]
      exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp)
    have h2 : Polynomial.eval (w i) (polyOf v) = ∏ r, (w i - v r) := by
      simp only [polyOf]
      rw [Polynomial.eval_prod]
      simp
    rw [hpoly] at h2
    rw [h2] at h1
    obtain ⟨r, -, hr⟩ := Finset.prod_eq_zero_iff.mp h1
    exact ⟨r, sub_eq_zero.mp hr⟩
  choose σ hσ using key
  -- `σ` is injective because `w` is, hence a bijection of the finite type `Fin k`.
  have hinj : Function.Injective σ := by
    intro i j hij
    apply hw
    rw [hσ i, hσ j, hij]
  exact ⟨Equiv.ofBijective σ ⟨hinj, (Finite.injective_iff_surjective.mp hinj)⟩, hσ⟩

end Work.BMF.N4chain
