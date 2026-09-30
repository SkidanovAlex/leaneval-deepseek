import Mathlib
import Submission.Work.BMF.mr_direct.primePolyWindow_defs
import Submission.Work.BMF.mr_direct.primePoly_pow_eq

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# `Work.BMF.mr_direct.winPow_eq`

The `k`-th power of the window-supported Dirichlet polynomial
`winDirPoly c A B t = Σ_{p ∈ winSet A B} c p · p^{-(1+it)}` is again a Dirichlet polynomial,

`(winDirPoly c A B t)^k = Σ_{1 ≤ n ≤ ⌊B⌋₊^k} winPowCoeff c A B k n · n^{-it}`,

and every `n` with `winPowCoeff c A B k n ≠ 0` lies in `[⌈A⌉₊^k, ⌊B⌋₊^k]`.

The expansion is the `k`-fold product rule, identical to the dyadic case
(`primePoly_pow_eq`): the abstract expansion `primePoly.sum_pow_expand` is applied to the
window set `winSet A B` and the coefficients `p ↦ c p / p`, and the range/support statements
are the product bounds `winSet_piFinset_prod_bounds`.
-/

set_option autoImplicit false

namespace Work.BMF.mr_direct

open Finset
open scoped BigOperators

namespace primePolyWindow

/-- Every tuple of primes drawn from the window prime set `winSet A B` has a product that is
`≥ 1`, at least `⌈A⌉₊ ^ k` and at most `⌊B⌋₊ ^ k`. -/
theorem winSet_piFinset_prod_bounds (A B : ℝ) (k : ℕ) {f : Fin k → ℕ}
    (hf : f ∈ Fintype.piFinset (fun _ : Fin k => winSet A B)) :
    1 ≤ ∏ j, f j ∧ ⌈A⌉₊ ^ k ≤ ∏ j, f j ∧ ∏ j, f j ≤ ⌊B⌋₊ ^ k := by
  have hmem : ∀ j, f j ∈ winSet A B := fun j => (Fintype.mem_piFinset.mp hf) j
  have hprime : ∀ j, Nat.Prime (f j) := fun j => (mem_winSet (hmem j)).1
  have hlo : ∀ j, ⌈A⌉₊ ≤ f j := fun j => (mem_winSet (hmem j)).2.1
  have hhi : ∀ j, f j ≤ ⌊B⌋₊ := fun j => (mem_winSet (hmem j)).2.2
  refine ⟨?_, ?_, ?_⟩
  · exact Finset.one_le_prod (fun j _ => (hprime j).one_le)
  · calc ⌈A⌉₊ ^ k = ∏ _j : Fin k, ⌈A⌉₊ := by
          rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
      _ ≤ ∏ j : Fin k, f j := Finset.prod_le_prod (fun j _ => hlo j)
  · calc ∏ j : Fin k, f j ≤ ∏ _j : Fin k, ⌊B⌋₊ :=
          Finset.prod_le_prod (fun j _ => hhi j)
      _ = ⌊B⌋₊ ^ k := by
          rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]

/-- If `winPowCoeff c A B k n` is non-zero, its defining sum has a non-empty index set:
there is a `k`-tuple `f` of primes in `winSet A B` whose product is `n`. -/
theorem winPowCoeff_support (A B : ℝ) (c : ℕ → ℂ) (k n : ℕ)
    (h : winPowCoeff c A B k n ≠ 0) :
    ∃ f ∈ Fintype.piFinset (fun _ : Fin k => winSet A B), ∏ j, f j = n := by
  rw [winPowCoeff] at h
  obtain ⟨f, hf, _⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
  exact ⟨f, (Finset.mem_filter.mp hf).1, (Finset.mem_filter.mp hf).2⟩

end primePolyWindow

theorem winPow_eq (A B : ℝ) (c : ℕ → ℂ) (k : ℕ) (hA : 2 ≤ A) (hAB : A ≤ B) (hk : 1 ≤ k) :
    (∀ t : ℝ,
        (Work.BMF.mr_direct.primePolyWindow.winDirPoly c A B t) ^ k
          = ∑ n ∈ Finset.Icc 1 (⌊B⌋₊ ^ k),
              Work.BMF.mr_direct.primePolyWindow.winPowCoeff c A B k n *
                (n : ℂ) ^ (-(Complex.I * (t : ℂ)))) ∧
      (∀ n : ℕ, Work.BMF.mr_direct.primePolyWindow.winPowCoeff c A B k n ≠ 0 →
        n ∈ Finset.Icc (⌈A⌉₊ ^ k) (⌊B⌋₊ ^ k)) := by
  have hsub : ∀ f ∈ Fintype.piFinset (fun _ : Fin k => primePolyWindow.winSet A B),
      (∏ j, f j) ∈ Finset.Icc 1 (⌊B⌋₊ ^ k) := by
    intro f hf
    have hb := primePolyWindow.winSet_piFinset_prod_bounds A B k hf
    exact Finset.mem_Icc.mpr ⟨hb.1, hb.2.2⟩
  constructor
  · intro t
    have hmain :
        (∑ p ∈ primePolyWindow.winSet A B,
            (c p * (p : ℂ)⁻¹) * (p : ℂ) ^ (-(Complex.I * (t : ℂ)))) ^ k
          = ∑ n ∈ Finset.Icc 1 (⌊B⌋₊ ^ k),
              (∑ f ∈ (Fintype.piFinset (fun _ : Fin k => primePolyWindow.winSet A B)).filter
                  (fun f => ∏ j, f j = n),
                ∏ j, (c (f j) * ((f j : ℂ))⁻¹)) *
                (n : ℂ) ^ (-(Complex.I * (t : ℂ))) :=
      primePoly.sum_pow_expand (primePolyWindow.winSet A B) (fun p => c p * (p : ℂ)⁻¹)
        (-(Complex.I * (t : ℂ))) (⌊B⌋₊ ^ k) k hsub
    rw [primePolyWindow.winDirPoly_eq_powForm, hmain]
    rfl
  · intro n hn
    obtain ⟨f, hfT, hfp⟩ := primePolyWindow.winPowCoeff_support A B c k n hn
    have hb := primePolyWindow.winSet_piFinset_prod_bounds A B k hfT
    rw [Finset.mem_Icc]
    exact ⟨hfp ▸ hb.2.1, hfp ▸ hb.2.2⟩

end Work.BMF.mr_direct
