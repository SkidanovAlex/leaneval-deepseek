import Mathlib
import Submission.Work.BMF.recursion.Defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The level sets for Linnik's bound

We formalise the "p-adic level sets" that occur in the standard (Linnik / Wooley)
p-adic counting argument for the well-conditioned count of `k`-tuples with prescribed
power sums.

For a prime `p`, a length `k`, a level `m ≥ 0` and a prescribed sequence `H`, the set
`Lvl p k m H` consists of the tuples `b : Fin k → Fin (p^m)` (i.e. `k`-tuples of residues
modulo `p^m`) whose entries are pairwise distinct modulo `p` and whose power sums
`∑ᵢ bᵢ^j` are congruent to `H j` modulo `p ^ (min j m)` for every `1 ≤ j ≤ k`.

The three facts about these sets that the proof of `Work.BMF.recursion.linnik_shift`
uses are

* `linnik_lvl_one`  : `(Lvl p k 1 H).card ≤ k!` (the "mod p" base case, Newton's
  identities plus the fact that a monic polynomial over a field is determined by its
  multiset of roots);
* `linnik_step`     : `(Lvl p k (ℓ+1) H).card ≤ p^ℓ * (Lvl p k ℓ H).card` for `1 ≤ ℓ`
  (the digit-by-digit lifting step, whose fibre bound is a Vandermonde/moment matrix
  bound over `ZMod p`, stated as `linnik_fibre`);
* `linnik_reduce`   : the shuffling of the original count into `Lvl p k k H`, which is a
  pure consequence of `X < p^k`.

Multiplying the step bounds `p^ℓ`, `ℓ = 1, …, k-1`, gives the factor `p^{k(k-1)/2}`, and the
base case contributes `k!`.
-/

set_option autoImplicit false

namespace Work.BMF.recursion

open Finset

/-- `Lvl p k m H` is the "level `m`" set of `k`-tuples of residues modulo `p^m` with entries
pairwise distinct modulo `p` and with power sums `∑ᵢ bᵢ^j ≡ H j` modulo `p ^ (min j m)`
for every `1 ≤ j ≤ k`. -/
def Lvl (p k m : ℕ) (H : ℕ → ℕ) : Finset (Fin k → Fin (p ^ m)) :=
  Finset.univ.filter fun b =>
    (∀ i j : Fin k, i ≠ j → ((b i).val : ZMod p) ≠ ((b j).val : ZMod p)) ∧
    (∀ j : ℕ, 1 ≤ j → j ≤ k →
      (p : ℤ) ^ min j m ∣ (∑ i, ((b i).val : ℤ) ^ j) - (H j : ℤ))

end Work.BMF.recursion
