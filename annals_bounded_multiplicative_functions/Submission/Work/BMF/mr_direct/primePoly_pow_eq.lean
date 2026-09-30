import Mathlib
import Submission.Work.BMF.mr_direct.primePoly_defs
import Submission.Work.BMF.mr_direct.cpow_prod_natCast
import Submission.Work.BMF.mr_direct.primeSet_piFinset_prod_bounds
import Submission.Work.BMF.mr_direct.powCoeff_support

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# `Work.BMF.mr_direct.primePoly_pow_eq`

The `k`-th power of the prime-supported Dirichlet polynomial
`primeDirPoly c P t = Σ_{p ∈ primeSet P} c p · p^{-(1+it)}` is again a Dirichlet polynomial,

`(primeDirPoly c P t)^k = Σ_{1 ≤ n ≤ ⌊2P⌋₊^k} powCoeff c P k n · n^{-it}`,

and every `n` with `powCoeff c P k n ≠ 0` lies in `[⌈P⌉₊^k, ⌊2P⌋₊^k]`.

The expansion is the `k`-fold product rule.  For a prime `p` one has
`p^{-(1+it)} = p^{-1} · p^{-it}`, and the powers of the individual factors of a product
combine, `∏_j p_j^{-it} = (∏_j p_j)^{-it}` (`cpow_prod_natCast`), because the `p_j` are
positive (real) integers.  Collecting the `k`-tuples of primes according to the value of
`∏_j p_j` then produces exactly the coefficient `powCoeff c P k n`; the range of the sum and
the support statement are the product bounds `primeSet_piFinset_prod_bounds`.
-/

set_option autoImplicit false

namespace Work.BMF.mr_direct

open Finset
open scoped BigOperators

namespace primePoly

/-- **Expansion of the `k`-th power of a finite Dirichlet polynomial.**

Let `S ⊆ ℕ` and let `d : ℕ → ℂ` be arbitrary coefficients.  Then the `k`-th power of
`Σ_{p ∈ S} d p · p^w` expands over the `k`-tuples of elements of `S`, and collecting the
tuples according to the value of `∏ j, f j` gives, for any `M` containing all these products,

`(Σ_{p ∈ S} d p · p^w)^k = Σ_{1 ≤ n ≤ M} (Σ_{∏ j, f j = n} ∏ j, d (f j)) · n^w`.

Here `w` is an arbitrary complex exponent; the hypothesis on `M` is exactly the range
statement, and `cpow_prod_natCast` (valid for arbitrary naturals) is what lets the powers of
the individual factors be combined. -/
lemma sum_pow_expand (S : Finset ℕ) (d : ℕ → ℂ) (w : ℂ) (M : ℕ) (k : ℕ)
    (hsub : ∀ f ∈ Fintype.piFinset (fun _ : Fin k => S), (∏ j, f j) ∈ Finset.Icc 1 M) :
    (∑ p ∈ S, d p * (p : ℂ) ^ w) ^ k =
      ∑ n ∈ Finset.Icc 1 M,
        (∑ f ∈ (Fintype.piFinset (fun _ : Fin k => S)).filter (fun f => ∏ j, f j = n),
            ∏ j, d (f j)) * (n : ℂ) ^ w := by
  classical
  rw [Finset.sum_pow']
  have h1 : ∀ f : Fin k → ℕ, (∏ i, (d (f i) * (f i : ℂ) ^ w))
      = (∏ i, d (f i)) * ((∏ i, f i : ℕ) : ℂ) ^ w := by
    intro f
    rw [Finset.prod_mul_distrib, cpow_prod_natCast Finset.univ f w]
  rw [Finset.sum_congr rfl (fun f _ => h1 f)]
  rw [← Finset.sum_fiberwise_of_maps_to (s := Fintype.piFinset (fun _ : Fin k => S))
      (t := Finset.Icc 1 M) (g := fun f => ∏ j, f j) hsub
      (fun f => (∏ i, d (f i)) * ((∏ i, f i : ℕ) : ℂ) ^ w)]
  refine Finset.sum_congr rfl (fun n _ => ?_)
  rw [Finset.sum_congr rfl (fun f hf => by rw [(Finset.mem_filter.mp hf).2]),
    ← Finset.sum_mul]

/-- `primeDirPoly` written with the `c`-coefficient and the factor `p^{-1}` combined, so that
it becomes a sum of `d p * p^w` with `w = -it`, ready for `sum_pow_expand`. -/
lemma primeDirPoly_eq_powForm (c : ℕ → ℂ) (P t : ℝ) :
    primeDirPoly c P t
      = ∑ p ∈ primeSet P, (c p * (p : ℂ)⁻¹) * (p : ℂ) ^ (-(Complex.I * (t : ℂ))) := by
  rw [primeDirPoly]
  refine Finset.sum_congr rfl (fun p hp => ?_)
  have hprime : Nat.Prime p := (Finset.mem_filter.mp hp).2
  have hp0 : (p : ℂ) ≠ 0 := by exact_mod_cast hprime.ne_zero
  rw [show -(1 + Complex.I * (t : ℂ)) = -1 + (-(Complex.I * (t : ℂ))) by ring,
    Complex.cpow_add _ _ hp0, Complex.cpow_neg_one]
  ring

end primePoly

theorem primePoly_pow_eq :
    ∀ (P : ℝ) (c : ℕ → ℂ) (k : ℕ), 2 ≤ P → 1 ≤ k →
      ((∀ t : ℝ,
          (Work.BMF.mr_direct.primePoly.primeDirPoly c P t) ^ k
            = ∑ n ∈ Finset.Icc 1 (⌊2 * P⌋₊ ^ k),
                Work.BMF.mr_direct.primePoly.powCoeff c P k n *
                  (n : ℂ) ^ (-(Complex.I * (t : ℂ)))) ∧
        (∀ n : ℕ, Work.BMF.mr_direct.primePoly.powCoeff c P k n ≠ 0 →
          n ∈ Finset.Icc (⌈P⌉₊ ^ k) (⌊2 * P⌋₊ ^ k))) := by
  intro P c k hP hk
  have hsub : ∀ f ∈ Fintype.piFinset (fun _ : Fin k => primePoly.primeSet P),
      (∏ j, f j) ∈ Finset.Icc 1 (⌊2 * P⌋₊ ^ k) := by
    intro f hf
    have hb := primeSet_piFinset_prod_bounds P k hf
    exact Finset.mem_Icc.mpr ⟨hb.1, hb.2.2⟩
  constructor
  · intro t
    have hmain :
        (∑ p ∈ primePoly.primeSet P, (c p * (p : ℂ)⁻¹) * (p : ℂ) ^ (-(Complex.I * (t : ℂ)))) ^ k
          = ∑ n ∈ Finset.Icc 1 (⌊2 * P⌋₊ ^ k),
              (∑ f ∈ (Fintype.piFinset (fun _ : Fin k => primePoly.primeSet P)).filter
                  (fun f => ∏ j, f j = n),
                ∏ j, (c (f j) * ((f j : ℂ))⁻¹)) *
                (n : ℂ) ^ (-(Complex.I * (t : ℂ))) :=
      primePoly.sum_pow_expand (primePoly.primeSet P) (fun p => c p * (p : ℂ)⁻¹)
        (-(Complex.I * (t : ℂ))) (⌊2 * P⌋₊ ^ k) k hsub
    rw [primePoly.primeDirPoly_eq_powForm, hmain]
    rfl
  · intro n hn
    obtain ⟨f, hfT, hfp⟩ := powCoeff_support P c k n hn
    have hb := primeSet_piFinset_prod_bounds P k hfT
    rw [Finset.mem_Icc]
    exact ⟨hfp ▸ hb.2.1, hfp ▸ hb.2.2⟩

end Work.BMF.mr_direct
