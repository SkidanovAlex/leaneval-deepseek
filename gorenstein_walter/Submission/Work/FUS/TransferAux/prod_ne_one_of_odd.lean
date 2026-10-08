import Mathlib

namespace Work.FUS.TransferAux

/-- In a commutative monoid, if every value of `f` on `s` is either `1` or a fixed
element `g`, then the product of `f` over `s` is `g` raised to the number of indices
where `f` is non-trivial. -/
lemma prod_eq_pow_card_filter {G : Type*} [CommMonoid G] [DecidableEq G] {ι : Type*}
    (g : G) (f : ι → G) (h : ∀ i, f i = 1 ∨ f i = g) (s : Finset ι) :
    ∏ i ∈ s, f i = g ^ (s.filter (fun i => f i ≠ 1)).card := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, ih, Finset.filter_insert]
    by_cases hfa : f a = 1
    · simp [hfa]
    · have hga : f a = g := (h a).resolve_left hfa
      rw [ite_eq_left hfa, hga, Finset.card_insert_of_notMem (by
        intro hmem; exact ha (Finset.mem_filter.mp hmem).1), pow_succ']

/-- The product of a finite family of elements of the two-element group
`Multiplicative (ZMod 2)` is non-trivial whenever an odd number of them are
non-trivial. -/
theorem prod_ne_one_of_odd {ι : Type*} [Fintype ι] (f : ι → Multiplicative (ZMod 2))
    (h : Odd (Nat.card {i : ι // f i ≠ 1})) : ∏ i, f i ≠ 1 := by
  classical
  set g : Multiplicative (ZMod 2) := Multiplicative.ofAdd 1 with hgdef
  have hcases : ∀ x : Multiplicative (ZMod 2), x = 1 ∨ x = g := by
    intro x; rw [hgdef]; revert x; decide
  have hpow : ∀ n : ℕ, g ^ n = 1 ↔ Even n := by
    intro n
    have hg2 : g * g = 1 := by rw [hgdef]; decide
    have hg1 : g ≠ 1 := by rw [hgdef]; decide
    have hord : orderOf g = 2 := by
      have hdvd : orderOf g ∣ 2 := by
        rw [orderOf_dvd_iff_pow_eq_one]
        simpa only [pow_two] using hg2
      rcases (Nat.dvd_prime (by norm_num : Nat.Prime 2)).mp hdvd with hh | hh
      · exact absurd hh (by rw [orderOf_eq_one_iff]; exact hg1)
      · exact hh
    rw [← orderOf_dvd_iff_pow_eq_one, hord, even_iff_two_dvd]
  have hprod : ∏ i, f i = g ^ (Nat.card {i : ι // f i ≠ 1}) := by
    rw [prod_eq_pow_card_filter g f (fun i => hcases (f i)) Finset.univ]
    congr 1
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  rw [hprod]
  intro hcontra
  exact (Nat.not_even_iff_odd.mpr h) ((hpow _).mp hcontra)

end Work.FUS.TransferAux
