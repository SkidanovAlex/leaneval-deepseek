import Mathlib
import Submission.Work.Fitting.Main
import Submission.Work.ThmF.ChV12.Fitting_cyclic_fpf
import Submission.Work.ThmF.ChV12.irreducible_of_orderOf_prime
import Submission.Work.ThmF.ChV12.solvable_of_cyclic_normal_irreducible

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option linter.style.haveILetI false

namespace Work.ThmF.ChV12

/-!
# Orbit-stabiliser basics for a transitive action on `A ∖ {1}`

`A` is a finite elementary abelian `2`-group of order `2 ^ k` and `D` is a finite group acting
faithfully via `ρ : D →* MulAut A`, transitively on the nonidentity elements.

* `pow_two_sub_one_dvd_card` : `2 ^ k - 1 ∣ |D|` (orbit--stabiliser);
* `lt_prime_of_orderOf_two`  : `orderOf (2 : ZMod p) = k` forces `k < p`;
* `exists_orderOf_prime_of_transitive` : a primitive prime divisor of `2 ^ k - 1` yields an
  element of `D` of that order;
* `solvable_of_pCore_irreducible` : if the `q`-core of `D` is nontrivial and `q` is a primitive
  prime divisor of `2 ^ k - 1`, then `D` is solvable (App. X + `D / C_D(O_q(D)) ↪ Aut(O_q(D))`).

This module is `sorry`-free and is meant to be imported by the delegated pieces of
`Work.ThmF.ChV12.fitting_irreducible_of_transitive`.
-/

/-- **Orbit–stabiliser for the transitive action on `A ∖ {1}`.**  An elementary abelian 2-group `A`
of order `2 ^ k` (`k ≥ 1`) on which `D` acts transitively on the nonidentity elements satisfies
`2 ^ k - 1 ∣ |D|`. -/
theorem pow_two_sub_one_dvd_card {A D : Type} [Group A] [Group D] [Finite A] [Finite D]
    {k : ℕ} (hk1 : 1 ≤ k) (hk : Nat.card A = 2 ^ k)
    (ρ : D →* MulAut A) (htrans : ∀ a b : A, a ≠ 1 → b ≠ 1 → ∃ d : D, ρ d a = b) :
    2 ^ k - 1 ∣ Nat.card D := by
  classical
  letI : MulAction D A := MulAction.compHom A ρ
  haveI : Fintype A := Fintype.ofFinite A
  haveI : Fintype D := Fintype.ofFinite D
  have hcard_gt : 1 < Nat.card A := by
    rw [hk]
    calc 1 < 2 ^ 1 := by norm_num
      _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk1
  haveI : Nontrivial A :=
    (Fintype.one_lt_card_iff_nontrivial (α := A)).mp (by rwa [Nat.card_eq_fintype_card] at hcard_gt)
  obtain ⟨a, ha⟩ := exists_ne (1 : A)
  have horbit : MulAction.orbit D a = {b : A | b ≠ 1} := by
    ext b
    constructor
    · rintro ⟨d, rfl⟩
      intro h
      have h' : ρ d a = ρ d 1 := by rw [map_one]; exact h
      exact ha ((ρ d).injective h')
    · intro hb
      obtain ⟨d, hd⟩ := htrans a b ha hb
      exact ⟨d, hd⟩
  have hcard_orbit : Nat.card (MulAction.orbit D a) = 2 ^ k - 1 := by
    have hset : {b : A | b ≠ 1} = ({1} : Set A)ᶜ := by ext b; simp
    rw [horbit, hset, Nat.card_eq_fintype_card, Fintype.card_compl_set]
    have h1 : Fintype.card ↥({1} : Set A) = 1 := by
      haveI : Subsingleton ↥({1} : Set A) :=
        ⟨fun x y => Subtype.ext (by simpa using x.2.trans y.2.symm)⟩
      exact Fintype.card_ofSubsingleton ⟨1, rfl⟩
    rw [h1, ← hk, Nat.card_eq_fintype_card]
  have hstab : Nat.card (MulAction.orbit D a) * Nat.card (MulAction.stabilizer D a) =
      Nat.card D := by
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
    exact MulAction.card_orbit_mul_card_stabilizer_eq_card_group (G := D) a
  refine ⟨Nat.card ↥(MulAction.stabilizer D a), ?_⟩
  rw [hcard_orbit] at hstab
  exact hstab.symm

/-- If `p` is prime and `orderOf (2 : ZMod p) = k`, then `k < p`. -/
theorem lt_prime_of_orderOf_two {k p : ℕ} (hp : Nat.Prime p)
    (hord : orderOf (2 : ZMod p) = k) : k < p := by
  rcases eq_or_ne p 2 with hp2 | hp2
  · subst hp2
    have hz : (2 : ZMod 2) = 0 := (CharP.cast_eq_zero_iff (ZMod 2) 2 2).mpr (dvd_refl 2)
    have h0 : orderOf (0 : ZMod 2) = 0 := by
      rw [orderOf_eq_zero_iff, isOfFinOrder_iff_pow_eq_one]
      rintro ⟨n, hn, hpow⟩
      obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
      simp [pow_succ] at hpow
    rw [hz, h0] at hord
    omega
  · haveI : Fact p.Prime := ⟨hp⟩
    have hp3 : 2 < p := by
      have := hp.two_le
      omega
    have hne : (2 : ZMod p) ≠ 0 := by
      intro h
      have hdvd : p ∣ 2 := (CharP.cast_eq_zero_iff (ZMod p) p 2).mp h
      have := Nat.le_of_dvd (by norm_num) hdvd
      omega
    have hdvd : k ∣ p - 1 := by
      rw [← hord]
      exact orderOf_dvd_iff_pow_eq_one.mpr (ZMod.pow_card_sub_one_eq_one hne)
    have hp1 : p - 1 < p := Nat.sub_one_lt (by omega)
    exact lt_of_le_of_lt (Nat.le_of_dvd (by omega) hdvd) hp1

/-- **A primitive prime divisor of `2 ^ k - 1` provides an element of `D` of that order.** -/
theorem exists_orderOf_prime_of_transitive {A D : Type} [Group A] [Group D] [Finite A] [Finite D]
    {k p : ℕ} (hk1 : 1 ≤ k) (hk : Nat.card A = 2 ^ k) (hp : Nat.Prime p)
    (hord : orderOf (2 : ZMod p) = k)
    (ρ : D →* MulAut A) (htrans : ∀ a b : A, a ≠ 1 → b ≠ 1 → ∃ d : D, ρ d a = b) :
    ∃ x : D, orderOf x = p := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hp_dvd : p ∣ 2 ^ k - 1 := by
    have h1 : ((2 : ZMod p)) ^ k = 1 := by rw [← hord, pow_orderOf_eq_one]
    have h2 : ((2 ^ k : ℕ) : ZMod p) = 1 := by
      push_cast
      exact h1
    have h3 : ((2 ^ k - 1 : ℕ) : ZMod p) = 0 := by
      rw [Nat.cast_sub Nat.one_le_two_pow]
      simp [h2]
    exact (CharP.cast_eq_zero_iff (ZMod p) p (2 ^ k - 1)).mp h3
  have hpD : p ∣ Nat.card D :=
    dvd_trans hp_dvd (pow_two_sub_one_dvd_card hk1 hk ρ htrans)
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' p hpD
  exact ⟨x, hx⟩

/-- `q ∣ 2 ^ k - 1` whenever `orderOf (2 : ZMod q) = k` and `q` is a prime. -/
theorem prime_dvd_two_pow_sub_one_of_orderOf {k q : ℕ} (hq : Nat.Prime q)
    (hord : orderOf (2 : ZMod q) = k) : q ∣ 2 ^ k - 1 := by
  haveI : Fact q.Prime := ⟨hq⟩
  have h1 : ((2 : ZMod q)) ^ k = 1 := by rw [← hord, pow_orderOf_eq_one]
  have h2 : ((2 ^ k : ℕ) : ZMod q) = 1 := by
    push_cast
    exact h1
  have h3 : ((2 ^ k - 1 : ℕ) : ZMod q) = 0 := by
    rw [Nat.cast_sub Nat.one_le_two_pow]
    simp [h2]
  exact (CharP.cast_eq_zero_iff (ZMod q) q (2 ^ k - 1)).mp h3

/-- **Solvability of `D` from a nontrivial `q`-core, `q` a primitive prime divisor of `2 ^ k - 1`.**

`O_q(D)` is cyclic and fixed-point-free on `A` (Huppert's Appendix X, packaged as
`pCore_isCyclic_and_fpf_of_transitive`), and it contains an element `z` of order `q`; such an
element acts *irreducibly* on `A` (`irreducible_of_orderOf_prime`), so `A` is irreducible under the
cyclic normal subgroup `O_q(D)`.  `solvable_of_cyclic_normal_irreducible` then gives solvability of
`D`. -/
theorem solvable_of_pCore_irreducible {A D : Type} [Group A] [Group D] [Finite A] [Finite D]
    {k q : ℕ} (hA2 : ∀ x : A, x * x = 1) (hAc : ∀ x y : A, x * y = y * x)
    (hk1 : 1 ≤ k) (hk : Nat.card A = 2 ^ k) (hq : Nat.Prime q)
    (hord : orderOf (2 : ZMod q) = k) (hodd : Odd (Nat.card D))
    (ρ : D →* MulAut A) (hfaith : Function.Injective ρ)
    (htrans : ∀ a b : A, a ≠ 1 → b ≠ 1 → ∃ d : D, ρ d a = b)
    (hcore : Work.Fitting.pCore q D ≠ ⊥) : Group.IsSolvable D := by
  classical
  haveI : Fact q.Prime := ⟨hq⟩
  -- `q ∣ |D|`, so `q` is a prime factor of `|D|`
  have hqD : q ∣ Nat.card D :=
    dvd_trans (prime_dvd_two_pow_sub_one_of_orderOf hq hord)
      (pow_two_sub_one_dvd_card hk1 hk ρ htrans)
  have hqmem : q ∈ (Nat.card D).primeFactors := by
    haveI : Fintype D := Fintype.ofFinite D
    have hne : Nat.card D ≠ 0 := by
      rw [Nat.card_eq_fintype_card]
      exact Fintype.card_ne_zero
    exact Nat.mem_primeFactors.mpr ⟨hq, hqD, hne⟩
  -- `O_q(D)` is cyclic and fixed-point-free
  have hX := pCore_isCyclic_and_fpf_of_transitive hA2 hAc hodd ρ hfaith htrans q hqmem
  obtain ⟨hcyc, hfpf⟩ := hX
  -- an element of order `q` in the `q`-core
  have hqP : q ∣ Nat.card ↥(Work.Fitting.pCore q D) := by
    obtain ⟨n, hn⟩ := (Work.Fitting.isPGroup_pCore (G := D) hq).exists_card_eq
    have hn0 : n ≠ 0 := by
      rintro rfl
      rw [pow_zero] at hn
      exact hcore (Subgroup.eq_bot_of_card_eq _ (by rw [hn]))
    rw [hn]
    exact dvd_pow_self q hn0
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' q hqP
  -- `ρ z` acts irreducibly on `A`
  have hzD : orderOf (z : D) = q := by rw [Subgroup.orderOf_coe]; exact hz
  have hzord : orderOf (ρ (z : D)) = q :=
    (orderOf_injective ρ hfaith (z : D)).trans hzD
  have hirr : ∀ W : Subgroup A, W ≠ ⊥ →
      (∀ t ∈ Work.Fitting.pCore q D, ∀ x ∈ W, ρ t x ∈ W) → W = ⊤ := by
    intro W hWne hWinv
    exact irreducible_of_orderOf_prime hA2 hAc hk hq hord (ρ (z : D)) hzord W hWne
      (fun y hy => hWinv _ z.2 y hy)
  exact solvable_of_cyclic_normal_irreducible hA2 hAc ρ hfaith (Work.Fitting.pCore q D)
    inferInstance hcyc hirr

end Work.ThmF.ChV12
