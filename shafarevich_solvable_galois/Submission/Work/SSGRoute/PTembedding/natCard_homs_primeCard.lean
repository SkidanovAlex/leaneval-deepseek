import Mathlib
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute.PTembedding

open Subgroup

set_option linter.style.haveILetI false

/-- A group of prime order `p` admits exactly `p - 1` nontrivial homomorphisms into the
cyclic group `Multiplicative (ZMod p)` (which has order `p`): the hom-set bijects with the
target group via evaluation at a generator, and the unique trivial hom corresponds to `1`. -/
theorem natCard_homs_primeCard (p : ℕ) [Fact p.Prime] (Q : Type) [Group Q]
    (hQ : Nat.card Q = p) :
    Nat.card {φ : Q →* Multiplicative (ZMod p) // φ ≠ 1} = p - 1 := by
  have hp : p.Prime := Fact.out
  haveI : NeZero p := ⟨hp.ne_zero⟩
  -- A group of prime order is cyclic; pick a generator `g`.
  have hcyc : IsCyclic Q := isCyclic_of_prime_card hQ
  obtain ⟨g, hg⟩ := isCyclic_iff_exists_zpowers_eq_top.mp hcyc
  have hgmem : ∀ x : Q, x ∈ zpowers g := fun x => by rw [hg]; exact Subgroup.mem_top x
  have hordg : orderOf g = p := by rw [orderOf_eq_card_of_zpowers_eq_top hg, hQ]
  let T := Multiplicative (ZMod p)
  have hcardT : Nat.card T = p := by
    rw [Nat.card_eq_fintype_card, Fintype.card_multiplicative, ZMod.card]
  have hcardT' : Fintype.card T = p := by
    rw [Fintype.card_multiplicative, ZMod.card]
  -- Every element of the target has order dividing `p`.
  have hdivp : ∀ t : T, orderOf t ∣ p := by
    intro t
    have h : orderOf t ∣ Nat.card T := _root_.orderOf_dvd_natCard t
    rwa [hcardT] at h
  have hdiv : ∀ t : T, orderOf t ∣ orderOf g := fun t => by rw [hordg]; exact hdivp t
  -- Evaluation at the generator: bijection between nontrivial homs and non-identity elements.
  let fwd : {φ : Q →* T // φ ≠ 1} → {t : T // t ≠ 1} := fun φ =>
    ⟨φ.1 g, fun hc => φ.2 ((MonoidHom.eq_iff_eq_on_generator hgmem φ.1 1).mpr (by simpa using hc))⟩
  let inv : {t : T // t ≠ 1} → {φ : Q →* T // φ ≠ 1} := fun t =>
    ⟨monoidHomOfForallMemZpowers hgmem (hdiv t.1), fun hc => by
      have hval := monoidHomOfForallMemZpowers_apply_gen hgmem (hdiv t.1)
      rw [hc] at hval
      exact t.2 (by simpa using hval.symm)⟩
  have hleft : Function.LeftInverse inv fwd := fun φ => by
    apply Subtype.ext
    apply (MonoidHom.eq_iff_eq_on_generator hgmem _ _).mpr
    simp [fwd, inv, monoidHomOfForallMemZpowers_apply_gen]
  have hright : Function.RightInverse inv fwd := fun t => by
    apply Subtype.ext
    simp [fwd, inv, monoidHomOfForallMemZpowers_apply_gen]
  let e : {φ : Q →* T // φ ≠ 1} ≃ {t : T // t ≠ 1} := Equiv.ofBijective fwd
    ⟨hleft.injective, hright.surjective⟩
  have hS : Nat.card {t : T // t ≠ 1} = p - 1 := by
    rw [Nat.card_eq_fintype_card]
    rw [Fintype.card_subtype_compl (fun t : T => t = 1), Fintype.card_subtype_eq, hcardT']
  rw [Nat.card_congr e, hS]

end Work.SSGRoute.PTembedding
