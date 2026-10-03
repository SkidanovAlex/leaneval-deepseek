/-
# Non-vanishing of a component of the root Fox vector at a letter of the root

Let `G = ⟨α | r⟩` with `r = u ^ l`, `u` cyclically reduced and not a proper power, and let `x` be a
letter occurring in `u`.  Then the `x`-component of the Fox vector of the *root* `u`,

`rootVec K r u x = presentAlg K r (∂u/∂x) ∈ K[G]`,

is non-zero.

This is the hypothesis `hβ0` of `Work.ORLyndon.annAt_of_torsionData` (and of the assembled route
`Work.ORLyndon.annAt_of_torsionData_root`): the Weinbaum input there is *only* the injectivity of the
support, and the non-vanishing of the vector is proved here.

## Argument

The Fox derivative of the root is the signed sum of the occurrence terms
(`Work.ORLyndon.rootVec_eq_sum_single`):

`rootVec K r u x = ∑ i, single (presentRho r (occTerm x (wordOf u) i)) (occEps K x (wordOf u) i)`,

the coefficient `occEps` being `±1` exactly at the occurrences of `x^{±1}` and `0` elsewhere.  If `x`
occurs in `u`, at least one occurrence index `i` carries a non-zero coefficient
(`exists_occSign_ne_zero_of_mem_relatorLetters`).  The occurrence terms are pairwise distinct in
`G` for *any* `K`: the quotient map `Work.ORLyndon.relRootHom r u l hpow : ⟨α | r⟩ →* ⟨α | u⟩`
(which exists because `r = u ^ l`) carries `presentRho r (occTerm … i)` to the class of the same term
in `⟨α | u⟩`, where Weinbaum's subword theorem
(`Work.ORLyndon.occTerm_distinct_clean`) makes the terms at non-vanishing positions pairwise
distinct.  Consequently the coefficient of `presentRho r (occTerm … i)` in the sum is exactly
`occEps K x (wordOf u) i ≠ 0`, so the sum — and hence `rootVec K r u x` — does not vanish.

Nothing is assumed about the characteristic of `K`: the argument is combinatorial and the
coefficients `±1` are non-zero in every field.

## Main declarations

* `Work.ORLyndon.exists_occSign_ne_zero_of_mem_relatorLetters` -- a letter of the relator has an
  occurrence with non-vanishing sign;
* `Work.ORLyndon.occTerm_presentRho_inj` -- the occurrence terms of `∂u/∂x` are pairwise distinct in
  `⟨α | r = u ^ l⟩` (Weinbaum, transported along the quotient map `⟨α | r⟩ →* ⟨α | u⟩`);
* `Work.ORLyndon.rootVec_ne_zero_of_mem_relatorLetters` -- the lemma above.
-/
import Mathlib
import Submission.Work.ORLyndon.annAtOfTorsionDataRoot
import Submission.Work.ORLyndon.occTerm_distinct_clean
import Submission.Work.ORLyndon.occDefs
import Submission.Work.OROneRel.Basic

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

namespace Work.ORLyndon

open MonoidAlgebra

universe u v

variable {α : Type u} [DecidableEq α] {K : Type v} [Field K]

/-- **A letter of a relator has an occurrence with non-vanishing sign.**  If `x` occurs in the
reduced word of `u` (`x ∈ relatorLetters u`), then some position of the reduced word
`Work.OROneRel.wordOf u` carries the letter `x^{±1}`, hence a non-zero occurrence sign. -/
theorem exists_occSign_ne_zero_of_mem_relatorLetters {u : FreeGroup α} {x : α}
    (hx : x ∈ Work.OROneRel.relatorLetters u) :
    ∃ i : Fin (Work.OROneRel.wordOf u).length, occSign x (Work.OROneRel.wordOf u) i ≠ 0 := by
  classical
  have hxw : ∃ b : Bool, (x, b) ∈ Work.OROneRel.wordOf u := by
    have hx' : ∃ b : Bool, (x, b) ∈ @FreeGroup.toWord α (Classical.decEq α) u := by
      simpa only [Work.OROneRel.relatorLetters, Set.mem_ofPred_eq] using hx
    rw [Work.ORLyndon.WB.classicalToWord_eq u] at hx'
    rwa [Work.ORLyndon.WB.wordOf_eq_toWord]
  obtain ⟨b, hb⟩ := hxw
  obtain ⟨i, hi⟩ := List.mem_iff_get.mp hb
  refine ⟨i, ?_⟩
  rw [occSign_ne_zero_iff]
  cases b
  · exact Or.inr hi
  · exact Or.inl hi

/-- **The occurrence terms of `∂u/∂x` are pairwise distinct in `G = ⟨α | r⟩`** for `r = u ^ l`,
`u` cyclically reduced and not a proper power: two occurrence positions with non-vanishing sign whose
attached prefixes are equal *in `G`* already coincide.  Weinbaum's subword theorem
(`Work.ORLyndon.occTerm_distinct_clean`, the occurrence terms are pairwise distinct in `⟨α | u⟩`)
is transported along the quotient map `⟨α | r⟩ →* ⟨α | u⟩`
(`Work.ORLyndon.relRootHom_presentRho`), which exists because `r = u ^ l`. -/
theorem occTerm_presentRho_inj {r u : FreeGroup α} {l : ℕ} (hpow : r = u ^ l)
    (hcyc : Work.OROneRel.IsCyclicallyReducedRelator u)
    (hpp : ¬ Work.OROneRel.IsProperPower u) {x : α}
    {i j : Fin (Work.OROneRel.wordOf u).length}
    (hi : occSign x (Work.OROneRel.wordOf u) i ≠ 0)
    (hj : occSign x (Work.OROneRel.wordOf u) j ≠ 0)
    (h : presentRho r (occTerm x (Work.OROneRel.wordOf u) i) =
      presentRho r (occTerm x (Work.OROneRel.wordOf u) j)) : i = j := by
  by_contra hij
  refine occTerm_distinct_clean u hcyc hpp hi hj hij ?_
  have hψ := congrArg (relRootHom r u l hpow) h
  rwa [relRootHom_presentRho r u l hpow, relRootHom_presentRho r u l hpow] at hψ

theorem rootVec_ne_zero_of_mem_relatorLetters {α : Type} [DecidableEq α] {K : Type} [Field K]
    (r u : FreeGroup α) (l : ℕ) (hpow : r = u ^ l)
    (hcyc : Work.OROneRel.IsCyclicallyReducedRelator u)
    (hpp : ¬ Work.OROneRel.IsProperPower u) {x : α}
    (hx : x ∈ Work.OROneRel.relatorLetters u) :
    Work.ORLyndon.rootVec K r u x ≠ 0 := by
  classical
  -- an occurrence of `x^{±1}` in the reduced word of the root
  obtain ⟨i, hsi⟩ := exists_occSign_ne_zero_of_mem_relatorLetters (u := u) hx
  -- the occurrence terms at non-vanishing positions are pairwise distinct in `G = ⟨α | r⟩`
  have hkey : ∀ j : Fin (Work.OROneRel.wordOf u).length,
      occSign x (Work.OROneRel.wordOf u) j ≠ 0 →
      presentRho r (occTerm x (Work.OROneRel.wordOf u) j) =
        presentRho r (occTerm x (Work.OROneRel.wordOf u) i) → j = i :=
    fun j hsj heq => occTerm_presentRho_inj hpow hcyc hpp hsj hsi heq
  rw [rootVec_eq_sum_single (K := K) (r := r) (u := u) x]
  intro hzero
  -- the candidate non-vanishing coefficient
  set a : OneRelatorGroup r := presentRho r (occTerm x (Work.OROneRel.wordOf u) i) with ha
  -- coefficient of the `j`-th summand at `a`
  have hterm : ∀ j : Fin (Work.OROneRel.wordOf u).length,
      ((MonoidAlgebra.single (presentRho r (occTerm x (Work.OROneRel.wordOf u) j))
        (occEps K x (Work.OROneRel.wordOf u) j)).coeff a)
      = if j = i then occEps K x (Work.OROneRel.wordOf u) i else 0 := by
    intro j
    rw [MonoidAlgebra.coeff_single, Finsupp.single_apply]
    by_cases hji : j = i
    · rw [if_pos (by rw [hji]), hji, if_pos rfl]
    · rw [if_neg hji]
      by_cases heq : presentRho r (occTerm x (Work.OROneRel.wordOf u) j) = a
      · rw [if_pos heq]
        by_contra hc
        exact hji (hkey j (occSign_ne_zero_of_occEps_ne_zero (K := K) x
          (Work.OROneRel.wordOf u) j hc) heq)
      · rw [if_neg heq]
  -- the coefficient of `a` in the occurrence sum
  have hcoeff : (∑ j : Fin (Work.OROneRel.wordOf u).length,
      MonoidAlgebra.single (presentRho r (occTerm x (Work.OROneRel.wordOf u) j))
        (occEps K x (Work.OROneRel.wordOf u) j)).coeff a
      = occEps K x (Work.OROneRel.wordOf u) i := by
    rw [MonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply]
    rw [Finset.sum_congr rfl (fun j _ => hterm j), Finset.sum_eq_single i]
    · rw [if_pos rfl]
    · intro j _ hji; rw [if_neg hji]
    · intro hi0; exact absurd (Finset.mem_univ i) hi0
  have hzero' : (∑ j : Fin (Work.OROneRel.wordOf u).length,
      MonoidAlgebra.single (presentRho r (occTerm x (Work.OROneRel.wordOf u) j))
        (occEps K x (Work.OROneRel.wordOf u) j)).coeff a = 0 := by
    rw [hzero, MonoidAlgebra.coeff_zero, Finsupp.zero_apply]
  rw [hcoeff] at hzero'
  exact (occEps_ne_zero_of_occSign_ne_zero (K := K) x (Work.OROneRel.wordOf u) i hsi) hzero'

end Work.ORLyndon
