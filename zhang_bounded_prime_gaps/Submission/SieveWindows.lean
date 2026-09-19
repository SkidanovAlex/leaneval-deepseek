import Mathlib
import Submission.Commons.NumberTheory.CongruenceWindows.congruence_system_window_card_eq
import Submission.Commons.NumberTheory.CongruenceWindows.card_window_modEq_bounds
import Submission.Commons.NumberTheory.CongruenceWindows.add_mod_eq_zero_iff_neg_residue
import Submission.SieveSetup

open scoped BigOperators

/-!
# Sieve window counting (Polymath8a §4.1: the `S`-function)

The elementary counting backbone of the multidimensional Selberg sieve.  In
Polymath8a §4.1 the window sums over `x ≤ n ≤ 2x`, `n ≡ b (W)` of products of
divisor sums `λ_F(n+h)` are expanded into sums over divisor tuples whose weight
is

    S(d₁,…,d_k,d′₁,…,d′ₖ) := #{ n ∈ [N,2N] : n ≡ b (mod W) ∧
                                     n + h_i ≡ 0 (mod [d_i,d′_i]) for all i }

and the standard facts are:

  1. `S` vanishes unless the moduli `W, [d_i,d′_i] (i = 1..k)` are pairwise
     coprime (because a common prime `p | [d_i,d′_i]` and `p | [d_j,d′_j]`
     would force `p | h_i - h_j`, contradicting the distinctness/admissibility
     of the `h`'s and the choice of `b` with `(b + h_i, W) = 1`);
  2. in the coprime case the system collapses (CRT) to one residue class
     modulo `W·∏ᵢ [d_i,d′_i]`, and the window count is `N/(W·∏ᵢ [d_i,d′_i])
     + O(1)`.

The generic lemmas live in the shared commons, namespace
`Commons.NumberTheory.CongruenceWindows` (module
`Submission.Commons.NumberTheory.CongruenceWindows.<name>`):

  * `card_window_modEq_bounds` — `|#(window ∩ residue class mod M) − N/M| ≤ 2`;
  * `modEq_prod_iff_forall` — CRT uniqueness/product characterization;
  * `congruence_system_window_card_eq` — CRT: a system of pairwise-coprime
    congruences over a window is a single residue class modulo the product.

This file will hold the sieve-shaped consequences (specialized to moduli
`m_i := lcm (d i) (d′ i)` and to the Fin-indexed tuples used in the weight
expansions) once those commons lemmas exist.
-/

namespace Commons.NumberTheory.MaynardSieve

/-- The `S`-function count: numbers `n ∈ [N, 2N]` satisfying a system of
congruences `n ≡ a i (mod s i)` for `i ∈ t` together with `n ≡ b (mod W)`,
where the modulus `W` is given separately (index 0). -/
noncomputable def systemWindowCard {ι : Type*} (t : Finset ι) (s : ι → ℕ) (a : ι → ℕ)
    (W b N : ℕ) : ℕ :=
  ((Finset.Icc N (2 * N)).filter fun n =>
    n % W = b % W ∧ ∀ i ∈ t, n % s i = a i % s i).card



/-! The residue-translation lemmas connecting `m | n + h` to congruence targets
are being proven in the commons by the fleet; see
`Commons.NumberTheory.CongruenceWindows.add_mod_eq_zero_iff_neg_residue`. -/

/-! More SieveWindows content is being proven in the commons by the fleet:
per-coordinate divisor-sum expansion, CRT window counting, residue
translation; see `Commons.NumberTheory.CongruenceWindows.*` and
`Commons.NumberTheory.SieveWindows.*`. -/


/-! ## The `S`-function main term

A system of *pairwise-coprime* congruences inside a window `[N, 2N]` collapses
(CRT) to one residue class modulo the product of the moduli, so its cardinality
is `N/(∏ s i) + O(1)`.  This is Polymath8a §4.1: `S = x/(W·∏ [d_i,d′_i]) +
O(1)` in the coprime case. -/

/-- The number of `n ∈ [N, 2N]` with `n % s i = a i % s i` for all `i ∈ t`. -/
def congruenceCard (N : ℕ) {ι : Type*} (t : Finset ι) (s a : ι → ℕ) : ℕ :=
  ((Finset.Icc N (2 * N)).filter fun n => ∀ i ∈ t, n % s i = a i % s i).card

/-- A pairwise-coprime congruence system over a window counts the same as the
single residue class of its CRT solution modulo the product of the moduli. -/
theorem congruenceCard_eq_single_residue {ι : Type*} (a s : ι → ℕ) (t : Finset ι) (N : ℕ)
    (hs : ∀ i ∈ t, s i ≠ 0)
    (hcop : (t : Set ι).Pairwise (fun i j => Nat.Coprime (s i) (s j))) :
    congruenceCard N t s a =
      ((Finset.Icc N (2 * N)).filter
        (fun n => n % (t.prod s) =
          (Nat.chineseRemainderOfFinset a s t hs hcop).1 % (t.prod s))).card := by
  classical
  have hw : ((Finset.Icc N (2 * N)).filter (fun n => ∀ i ∈ t, n ≡ a i [MOD s i])).card =
      ((Finset.Icc N (2 * N)).filter
        (fun n => n % (t.prod s) =
          (Nat.chineseRemainderOfFinset a s t hs hcop).1 % (t.prod s))).card :=
    Commons.NumberTheory.CongruenceWindows.congruence_system_window_card_eq a s t N hs hcop
  have hfilter : (Finset.Icc N (2 * N)).filter (fun n => ∀ i ∈ t, n % s i = a i % s i) =
      (Finset.Icc N (2 * N)).filter (fun n => ∀ i ∈ t, n ≡ a i [MOD s i]) := by
    refine Finset.filter_congr (fun n hn => ?_)
    constructor
    · intro h i hi
      simpa [Nat.ModEq] using h i hi
    · intro h i hi
      simpa [Nat.ModEq] using h i hi
  rw [congruenceCard, hfilter]
  exact hw

/-- A pairwise-coprime congruence system over the window `[N, 2N]` has
cardinality `N/(∏ s i) + O(1)`. -/
theorem congruenceCard_window_bounds {ι : Type*} (a s : ι → ℕ) (t : Finset ι) (N : ℕ)
    (hs : ∀ i ∈ t, s i ≠ 0)
    (hcop : (t : Set ι).Pairwise (fun i j => Nat.Coprime (s i) (s j))) :
    |(congruenceCard N t s a : ℝ) - (N : ℝ) / ((t.prod s : ℕ) : ℝ)| ≤ 2 := by
  classical
  have hprod1 : 1 ≤ t.prod s := by
    by_cases ht : t = ∅
    · simp [ht]
    · have htpos : 0 < t.prod s := t.prod_pos (by intro i hi; exact Nat.pos_of_ne_zero (hs i hi))
      omega
  let M : ℕ := t.prod s
  let c : ℕ := (Nat.chineseRemainderOfFinset a s t hs hcop).1
  let r : ℕ := c % M
  have hr : r < M := by
    dsimp [r]
    apply Nat.mod_lt _ (by omega)
  have hL4 : |(((Finset.Icc N (2 * N)).filter fun n => n % M = r).card : ℝ) -
        (N : ℝ) / (M : ℝ)| ≤ 2 :=
    Commons.NumberTheory.CongruenceWindows.card_window_modEq_bounds (N := N) (M := M) (r := r)
      hprod1 hr
  have hEq : congruenceCard N t s a =
      ((Finset.Icc N (2 * N)).filter fun n => n % M = r).card := by
    rw [congruenceCard_eq_single_residue a s t N hs hcop]
  simpa [M, hEq] using hL4

end Commons.NumberTheory.MaynardSieve
