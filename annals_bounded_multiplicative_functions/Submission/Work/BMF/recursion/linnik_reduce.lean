import Mathlib
import Submission.Work.BMF.recursion.LinnikDefs
import Submission.Work.BMF.recursion.Defs
import Submission.Work.BMF.recursion.ShiftDefs
import Submission.Work.BMF.recursion.shiftMod_inj
import Submission.Work.BMF.recursion.shiftMod_zmod_ne
import Submission.Work.BMF.recursion.pow_sum_sub_modEq

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

namespace Work.BMF.recursion

open Finset
open scoped BigOperators

/-!
# Reduction of the shifted count to the p-adic level set

This file contains `Work.BMF.recursion.linnik_reduce`, the purely combinatorial shuffling step
of Linnik's bound: for `p` prime and `X < p^k`, the `k`-tuples `a` with entries in `[1,X]`,
pairwise distinct modulo `p`, and with prescribed power sums `∑ᵢ (aᵢ - y)^j ≡ H j (mod p^j)`,
are no more numerous than the p-adic level set `Lvl p k k H` of `LinnikDefs.lean`.

The map is `a ↦ (i ↦ (aᵢ - y) mod p^k)`, i.e. `aᵢ - y` reduced into `[0, p^k)` (`shiftMod` in
`ShiftDefs.lean`); since `X < p^k` it is injective on `[1,X]`, and it preserves all the
congruences modulo `p^j`, `j ≤ k`.  The three arithmetic inputs are the lemmas
`shiftMod_modEq` (`ShiftDefs`), `shiftMod_inj`, `shiftMod_zmod_ne` and `pow_sum_sub_modEq`.
-/

/-- The shuffle map of `linnik_reduce`: send `a` to the tuple of the representatives in
`[0, p^k)` of `aᵢ - y`. -/
def shiftTup (p k X y : ℕ) (hp : p.Prime) (a : Tup k X) : Fin k → Fin (p ^ k) :=
  fun i => ⟨shiftMod p k y (a i).1, shiftMod_lt p k y (a i).1 hp⟩

lemma shiftTup_apply (p k X y : ℕ) (hp : p.Prime) (a : Tup k X) (i : Fin k) :
    (shiftTup p k X y hp a i).val = shiftMod p k y (a i).1 := rfl

/-- The shuffle maps a tuple satisfying the two constraints of `linnik_reduce` into the level
set `Lvl p k k H`. -/
lemma shiftTup_mem_Lvl (p k X y : ℕ) (hp : p.Prime) (H : ℕ → ℕ) (a : Tup k X)
    (hdis : ∀ i j : Fin k, i ≠ j → ¬ (p : ℤ) ∣ (((a i).1 : ℤ) - ((a j).1 : ℤ)))
    (hdiv : ∀ j : ℕ, 1 ≤ j → j ≤ k →
      ((p : ℤ) ^ j) ∣ ((∑ i, (((a i).1 : ℤ) - (y : ℤ)) ^ j) - (H j : ℤ))) :
    shiftTup p k X y hp a ∈ Lvl p k k H := by
  simp only [Lvl, Finset.mem_filter, Finset.mem_univ, true_and]
  refine ⟨?_, ?_⟩
  · intro i j hij
    have hk : 1 ≤ k := by have := i.isLt; omega
    have hne := shiftMod_zmod_ne p k y (a i).1 (a j).1 hp hk (hdis i j hij)
    simpa only [shiftTup_apply] using hne
  · intro j hj1 hjk
    rw [Nat.min_eq_left hjk]
    have hmod := pow_sum_sub_modEq p (fun i => (((a i).1 : ℤ) - (y : ℤ)))
      (fun i => (((shiftTup p k X y hp a i).val : ℕ) : ℤ)) H
      (fun i => by simpa only [shiftTup_apply] using shiftMod_modEq p k y (a i).1 hp) j hjk
    have hB : (p : ℤ) ^ j ∣ (∑ i, (((a i).1 : ℤ) - (y : ℤ)) ^ j) - (H j : ℤ) := hdiv j hj1 hjk
    have hBA : (p : ℤ) ^ j ∣ ((∑ i, (((a i).1 : ℤ) - (y : ℤ)) ^ j) - (H j : ℤ))
        - ((∑ i, (((shiftTup p k X y hp a i).val : ℕ) : ℤ) ^ j) - (H j : ℤ)) := hmod.dvd
    have := dvd_sub hB hBA
    rwa [sub_sub_cancel] at this

/-- The shuffle is injective on the tuples with entries in `[1,X]`, `X < p^k`. -/
lemma shiftTup_injOn (p k X y : ℕ) (hp : p.Prime) (hX : X < p ^ k) {a a' : Tup k X}
    (h : shiftTup p k X y hp a = shiftTup p k X y hp a') : a = a' := by
  funext i
  apply Subtype.ext
  have hlt : (a i).1 < p ^ k := lt_of_le_of_lt (Finset.mem_Icc.mp (a i).2).2 hX
  have hlt' : (a' i).1 < p ^ k := lt_of_le_of_lt (Finset.mem_Icc.mp (a' i).2).2 hX
  have hval : (shiftTup p k X y hp a i).val = (shiftTup p k X y hp a' i).val := by rw [h]
  have hmod : shiftMod p k y (a i).1 = shiftMod p k y (a' i).1 := by
    simpa only [shiftTup_apply] using hval
  exact shiftMod_inj p k y (a i).1 (a' i).1 hp hlt hlt' hmod

/-- **Reduction of the shifted count to the p-adic level set `Lvl p k k H`.**  Let `p` be a
prime and `X < p^k`.  Then the number of `k`-tuples `a` with entries in `[1,X]` (`Tup k X` is
`Fin k → Finset.Icc 1 X`, from `Submission/Work/BMF/recursion/Defs.lean`), pairwise distinct
modulo `p` and with `p^j ∣ ∑ᵢ (aᵢ - y)^j - H j` for `1 ≤ j ≤ k`, is at most the cardinality of
`Work.BMF.recursion.Lvl p k k H` (see `Submission/Work/BMF/recursion/LinnikDefs.lean`), i.e. of
the set of `b : Fin k → Fin (p^k)` with pairwise distinct entries modulo `p` and
`p^j ∣ ∑ᵢ bᵢ^j - H j` for `1 ≤ j ≤ k`.

Route.  Map `a` to `b` with `bᵢ = ((aᵢ).1 + p^k - y % p^k) % p^k ∈ [0, p^k)` (`p^k > 0` because
`p` is prime).  Then `bᵢ ≡ (aᵢ).1 - y (mod p^k)`.

* `bᵢ ≡ aᵢ - y (mod p)` and `bᵢ^j ≡ (aᵢ - y)^j (mod p^j)` for `j ≤ k`
  (`dvd_pow_sub_pow`-style: a congruence mod `p^k` descends to `p^j` and is preserved by taking
  `j`-th powers), so the divisibility hypotheses transfer to `b`.
* The distinctness transfers: if `((b i).val : ZMod p) = ((b j).val : ZMod p)` then
  `(a i).1 ≡ y ≡ (a j).1 (mod p)`, contradicting `¬ (p : ℤ) ∣ (a i).1 - (a j).1`.
* The map is injective on the whole of `(Icc 1 X)^k`: `b` determines `aᵢ - y` modulo `p^k`, so
  the `aᵢ` modulo `p^k`; and two elements of `[1,X] ⊆ [0,p^k)` congruent modulo `p^k > 0` are
  equal (`a = a'` by `Subtype.ext`, then `funext`).
* Conclude with `Finset.card_le_card_of_injOn` (the filter subset of `Tup k X` mapping into the
  filter defining `Lvl p k k H`). -/
theorem linnik_reduce (p k X y : ℕ) (hp : p.Prime) (hX : X < p ^ k) (H : ℕ → ℕ) :
    ((Finset.univ : Finset (Work.BMF.recursion.Tup k X)).filter (fun a =>
      (∀ i j : Fin k, i ≠ j → ¬ (p : ℤ) ∣ (((a i).1 : ℤ) - ((a j).1 : ℤ))) ∧
      (∀ j : ℕ, 1 ≤ j → j ≤ k →
        ((p : ℤ) ^ j) ∣ ((∑ i, (((a i).1 : ℤ) - (y : ℤ)) ^ j) - (H j : ℤ))))).card
    ≤ (Work.BMF.recursion.Lvl p k k H).card := by
  classical
  refine Finset.card_le_card_of_injOn (shiftTup p k X y hp) ?_ ?_
  · intro a ha
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at ha
    rw [Finset.mem_coe]
    exact shiftTup_mem_Lvl p k X y hp H a ha.1 ha.2
  · intro a _ a' _ heq
    exact shiftTup_injOn p k X y hp hX heq

end Work.BMF.recursion
