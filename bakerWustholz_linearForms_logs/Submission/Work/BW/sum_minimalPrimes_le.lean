import Mathlib
import Submission.Work.BW.refined_bezout
import Submission.Work.BW.DefsMult
import Submission.Work.BW.RB.A4
import Submission.Work.BW.RB.Basic

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The refined Bezout sum, restricted to a finite set of minimal primes

`sum_minimalPrimes_le` is the `Finset` form of Philippon's refined Bezout inequality
(`refined_bezout`): the minimal primes of `Ideal.span s` that meet the affine cone over
`G = G_a × G_m^N`, counted with the multiplicity `primLen` and with Philippon's degree
`rayDeg N D`, can only total at most `rayDeg N D ⊥`, the degree of `(ℙ¹)^{N+1}` in the
`O(D)`-embedding.

The point of the reduction is that a *finite* set `T` of such minimal primes contributes at most
the sum over *all* of them, because every summand is nonnegative: write the summand as `f`, the
total contribution of a prime `p` as the `finsum`
`g p = ∑ᶠ (_ : p ∈ I.minimalPrimes ∧ OnGPrime N p), f p` (whose support is contained in the finite
set of minimal primes of `I`), bound the `Finset` sum over `T` by the full `finsum` `∑ᶠ p, g p`,
and apply `refined_bezout`.

The auxiliary lemmas `rayDeg_nonneg_aux` and `summand_finiteSupport` are local copies of facts
about `rayDeg` and about the finiteness of the set of minimal primes, so that this file depends on
as few statements of the neighbouring modules as possible.
-/

namespace Work.BW

open MvPolynomial

/-- `rayDeg` is non-negative. -/
lemma rayDeg_nonneg_aux {N : ℕ} (D : Fin (N + 1) →₀ ℕ) (J : Ideal (MR N)) :
    0 ≤ rayDeg N D J := by
  rw [rayDeg]
  by_cases h : rayPoly N D J = 0
  · rw [h]; simp
  · obtain ⟨q, hq, _⟩ := (rb_rayPoly_ne_zero_iff (D := D) (I := J)).1 h
    rw [(rb_rayPoly_eq_iff (D := D) (I := J) ⟨q, hq⟩).2 hq]
    refine mul_nonneg (by positivity) (rb_leadingCoeff_nonneg_of_eventually ?_)
    filter_upwards [hq] with t ht
    rw [← ht]
    positivity

/-- The `finsum` giving the total contribution of a prime vanishes outside the (finite) set of
minimal primes, hence has finite support. -/
lemma summand_finiteSupport {N : ℕ} (D : Fin (N + 1) →₀ ℕ) (J : Ideal (MR N)) :
    Function.HasFiniteSupport (fun p : Ideal (MR N) =>
      ∑ᶠ (_ : p ∈ J.minimalPrimes ∧ ∃ x, OnG N x ∧ p ≤ ptIdeal N x),
        ((primLen J p).toNat : ℚ) * rayDeg N D p) := by
  rw [Function.HasFiniteSupport]
  refine (Ideal.finite_minimalPrimes_of_isNoetherianRing _ J).subset fun p hp => ?_
  by_contra h
  have h' : ¬ J.IsMinimalPrime p := h
  simp [h'] at hp

/-- The sum of the multiplicities times `rayDeg` over a finite set of minimal primes of
`Ideal.span s` meeting the cone over `G` is at most the degree `H(G; D) = rayDeg N D ⊥`.

This is the `Finset` form of Philippon's refined Bezout inequality. -/
theorem sum_minimalPrimes_le {N : ℕ} (D : Fin (N + 1) →₀ ℕ) (hD : ∀ i, 1 ≤ D i)
    (s : Set (MR N)) (hs : ∀ P ∈ s, P ∈ homPiece N D) (T : Finset (Ideal (MR N)))
    (hT : ∀ p ∈ T, p ∈ (Ideal.span s).minimalPrimes ∧ ∃ x, OnG N x ∧ p ≤ ptIdeal N x) :
    ∑ p ∈ T, ((primLen (Ideal.span s) p).toNat : ℚ) * rayDeg N D p ≤ rayDeg N D ⊥ := by
  classical
  -- the total contribution of a single prime, as a function of the prime
  set g : Ideal (MR N) → ℚ := fun p =>
    ∑ᶠ (_ : p ∈ (Ideal.span s).minimalPrimes ∧ ∃ x, OnG N x ∧ p ≤ ptIdeal N x),
      ((primLen (Ideal.span s) p).toNat : ℚ) * rayDeg N D p with hgdef
  -- every summand is nonnegative
  have hnn : ∀ p : Ideal (MR N), 0 ≤ ((primLen (Ideal.span s) p).toNat : ℚ) * rayDeg N D p :=
    fun p => mul_nonneg (by positivity) (rayDeg_nonneg_aux D p)
  have hgnn : ∀ p, 0 ≤ g p := fun p => finsum_nonneg (fun _ => hnn p)
  -- the total contribution has finite support
  have hg : Function.HasFiniteSupport g := by
    rw [hgdef]; exact summand_finiteSupport D (Ideal.span s)
  -- on `T`, the summand is the total contribution of that prime
  have hstep1 : ∑ p ∈ T, ((primLen (Ideal.span s) p).toNat : ℚ) * rayDeg N D p =
      ∑ p ∈ T, g p := by
    refine Finset.sum_congr rfl fun p hp => ?_
    rw [hgdef]
    have hc := hT p hp
    simp [hc]
  -- the `Finset` sum over `T` is at most the full `finsum`
  have hstep2 : ∑ p ∈ T, g p ≤ ∑ᶠ p, g p := by
    rw [finsum_eq_sum g hg]
    have h1 : ∑ p ∈ T, g p ≤ ∑ p ∈ T ∪ Set.Finite.toFinset hg, g p :=
      Finset.sum_le_sum_of_subset_of_nonneg Finset.subset_union_left
        (fun i _ _ => hgnn i)
    have h2 : ∑ p ∈ Set.Finite.toFinset hg, g p =
        ∑ p ∈ T ∪ Set.Finite.toFinset hg, g p :=
      Finset.sum_subset Finset.subset_union_right (fun x _ hx => ?_)
    · rw [h2]; exact h1
    · exact Function.notMem_support.mp fun hs => hx ((Set.Finite.mem_toFinset hg).mpr hs)
  -- Philippon's refined Bezout inequality
  rw [hstep1]
  exact le_trans hstep2 (refined_bezout D hD s hs)

/-- `sum_minimalPrimes_le` with the right-hand side expanded, using
`rayDeg N D ⊥ = (N+1)! ∏_i D_i`. -/
theorem sum_minimalPrimes_le_factorial {N : ℕ} (D : Fin (N + 1) →₀ ℕ) (hD : ∀ i, 1 ≤ D i)
    (s : Set (MR N)) (hs : ∀ P ∈ s, P ∈ homPiece N D) (T : Finset (Ideal (MR N)))
    (hT : ∀ p ∈ T, p ∈ (Ideal.span s).minimalPrimes ∧ ∃ x, OnG N x ∧ p ≤ ptIdeal N x) :
    ∑ p ∈ T, ((primLen (Ideal.span s) p).toNat : ℚ) * rayDeg N D p
      ≤ ((N + 1).factorial : ℚ) * ∏ i, (D i : ℚ) :=
  (sum_minimalPrimes_le D hD s hs T hT).trans_eq (rb_rayDeg_bot D hD).2.2

end Work.BW
