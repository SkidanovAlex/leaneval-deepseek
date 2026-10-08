import Mathlib
import Submission.Work.A7.Defs

namespace Work.AUTA7.A7

/-! ## Auxiliary facts on cycle types of permutations of `Fin 7`

The target below is proved along Route 2 of its docstring: an `x` in the centralizer of the
`3`-cycle `c = (4 5 6)` with `orderOf x = 4` gives the element `c * x` of `A₇` whose order is `12`
(the orders `3` and `4` are coprime), so the only input needed from permutation theory is that no
element of `A₇` has order divisible by `12`.

The two facts established here are
* `exists_mem_of_prime_pow_dvd_multiset_lcm`: a nonzero prime power dividing `s.lcm` divides a
  member of `s` (for `s : Multiset ℕ`);
* `cycleType_facts_of_twelve_dvd_orderOf`: a permutation of `Fin 7` whose order is divisible by
  `12` has cycle type `{4, 3}` (a `4`-cycle times a disjoint `3`-cycle). -/

/-- For a prime `p`, a prime power `p ^ k` divides `Nat.lcm a b` if and only if it divides `a` or
`b`.  (The analogous statement for a composite modulus is false; it is the prime-power case that
holds.) -/
lemma prime_pow_dvd_lcm_iff {p k a b : ℕ} (hp : p.Prime) :
    p ^ k ∣ Nat.lcm a b ↔ p ^ k ∣ a ∨ p ^ k ∣ b := by
  constructor
  · intro h
    rcases eq_or_ne a 0 with rfl | ha
    · exact Or.inl (dvd_zero _)
    rcases eq_or_ne b 0 with rfl | hb
    · exact Or.inr (dvd_zero _)
    rw [Nat.Prime.pow_dvd_iff_le_factorization hp (Nat.lcm_ne_zero ha hb)] at h
    rw [Nat.factorization_lcm ha hb, Finsupp.sup_apply, le_max_iff] at h
    rcases h with h | h
    · exact Or.inl ((Nat.Prime.pow_dvd_iff_le_factorization hp ha).mpr h)
    · exact Or.inr ((Nat.Prime.pow_dvd_iff_le_factorization hp hb).mpr h)
  · rintro (h | h)
    · exact dvd_trans h (Nat.dvd_lcm_left a b)
    · exact dvd_trans h (Nat.dvd_lcm_right a b)

/-- If a nonzero prime power `p ^ k` divides the least common multiple of a multiset of naturals,
then it divides one of the members.  (The hypothesis `0 < k` is necessary: the empty multiset has
`lcm = 1`, and `1 ∣ 1` although it has no member.) -/
theorem exists_mem_of_prime_pow_dvd_multiset_lcm {p k : ℕ} (hp : p.Prime) (hk : 0 < k)
    {s : Multiset ℕ} (h : p ^ k ∣ s.lcm) : ∃ a ∈ s, p ^ k ∣ a := by
  induction s using Multiset.induction_on with
  | empty =>
    rw [Multiset.lcm_zero] at h
    rw [Nat.Prime.pow_dvd_iff_le_factorization hp (by norm_num : (1 : ℕ) ≠ 0)] at h
    simp at h
    omega
  | cons a t ih =>
    rw [Multiset.lcm_cons, lcm_eq_nat_lcm] at h
    rcases (prime_pow_dvd_lcm_iff hp).mp h with ha | ht
    · exact ⟨a, Multiset.mem_cons_self a t, ha⟩
    · obtain ⟨b, hb, hbd⟩ := ih ht
      exact ⟨b, Multiset.mem_cons_of_mem hb, hbd⟩

/-- A permutation of `Fin 7` whose order is divisible by `12` has cycle type `{4, 3}`: it is the
product of a `4`-cycle and a disjoint `3`-cycle.  Consequently `cycleType.sum = 7` (all seven
points are moved) and `cycleType.card = 2`.

Indeed `12 = lcm 4 3`, so `4 ∣ orderOf σ` forces a cycle length divisible by `4` and `3 ∣ orderOf σ`
forces a cycle length divisible by `3`; cycle lengths are at most `7`, so the former is `4` and the
latter is `3` or `6`, and `6` is excluded because `4 + 6 > 7 ≥ cycleType.sum`.  Since `4` and `3`
already account for the whole sum `7`, no further cycle (not even a fixed point) is present. -/
lemma cycleType_facts_of_twelve_dvd_orderOf (σ : Equiv.Perm (Fin 7))
    (h : (12 : ℕ) ∣ orderOf σ) :
    σ.cycleType = ({4, 3} : Multiset ℕ) ∧ σ.cycleType.sum = 7 ∧ σ.cycleType.card = 2 := by
  -- `4` and `3` divide the lcm of the cycle lengths, which is the order
  have h4 : (2 : ℕ) ^ 2 ∣ σ.cycleType.lcm := by
    rw [Equiv.Perm.lcm_cycleType]
    exact dvd_trans (by norm_num : (4 : ℕ) ∣ 12) h
  have h3 : (3 : ℕ) ^ 1 ∣ σ.cycleType.lcm := by
    rw [Equiv.Perm.lcm_cycleType]
    exact dvd_trans (by norm_num : (3 : ℕ) ∣ 12) h
  obtain ⟨a, ha_mem, ha4⟩ :=
    exists_mem_of_prime_pow_dvd_multiset_lcm (p := 2) (k := 2) (by norm_num) (by norm_num) h4
  obtain ⟨b, hb_mem, hb3⟩ :=
    exists_mem_of_prime_pow_dvd_multiset_lcm (p := 3) (k := 1) (by norm_num) (by norm_num) h3
  -- cycle lengths are `≥ 2` and their sum is at most `7`
  have hsum_le : σ.cycleType.sum ≤ 7 := by
    have := Equiv.Perm.sum_cycleType_le σ
    simpa using this
  have ha2 : 2 ≤ a := Equiv.Perm.two_le_of_mem_cycleType ha_mem
  have hb2 : 2 ≤ b := Equiv.Perm.two_le_of_mem_cycleType hb_mem
  have ha_le : a ≤ σ.cycleType.sum :=
    Multiset.single_le_sum (fun _ _ => Nat.zero_le _) a ha_mem
  have hb_le : b ≤ σ.cycleType.sum :=
    Multiset.single_le_sum (fun _ _ => Nat.zero_le _) b hb_mem
  -- `4 ∣ a` and `2 ≤ a ≤ 7` force `a = 4`
  have ha_eq : a = 4 := by
    obtain ⟨m, hm⟩ := ha4
    have hm' : a = 4 * m := by rw [hm]; norm_num
    omega
  -- `3 ∣ b` and `2 ≤ b ≤ 7` force `b ∈ {3, 6}`; and `b = 6` is impossible
  have hb_eq : b = 3 := by
    obtain ⟨m, hm⟩ := hb3
    have hm' : b = 3 * m := by rw [hm]; norm_num
    have hm12 : m = 1 ∨ m = 2 := by omega
    rcases hm12 with hm1 | hm2
    · omega
    · exfalso
      have hb6 : b = 6 := by omega
      have hba : b ≠ a := by omega
      have hbm : b ∈ σ.cycleType.erase a := (Multiset.mem_erase_of_ne hba).mpr hb_mem
      have hble : b ≤ (σ.cycleType.erase a).sum :=
        Multiset.single_le_sum (fun _ _ => Nat.zero_le _) b hbm
      have hse := Multiset.sum_erase ha_mem
      omega
  -- hence `3` and `4` are distinct members whose sum is already the full sum `7`
  have hba : b ≠ a := by omega
  have hbm : b ∈ σ.cycleType.erase a := (Multiset.mem_erase_of_ne hba).mpr hb_mem
  have h3mem : 3 ∈ σ.cycleType.erase a := by rw [← hb_eq]; exact hbm
  have h3le : 3 ≤ (σ.cycleType.erase a).sum := by
    rw [← hb_eq]
    exact Multiset.single_le_sum (fun _ _ => Nat.zero_le _) b hbm
  have herase_sum : (σ.cycleType.erase a).sum = 3 := by
    have hse := Multiset.sum_erase ha_mem
    omega
  -- erasing a further `3` leaves nothing
  have hzero : (σ.cycleType.erase a).erase 3 = 0 := by
    by_contra hne
    obtain ⟨x, hx⟩ := Multiset.exists_mem_of_ne_zero hne
    have hs0 : ((σ.cycleType.erase a).erase 3).sum = 0 := by
      have hse := Multiset.sum_erase h3mem
      omega
    have hxle : x ≤ ((σ.cycleType.erase a).erase 3).sum :=
      Multiset.single_le_sum (fun _ _ => Nat.zero_le _) x hx
    have hxc : x ∈ σ.cycleType :=
      Multiset.mem_of_mem_erase (Multiset.mem_of_mem_erase hx)
    have hx2 : 2 ≤ x := Equiv.Perm.two_le_of_mem_cycleType hxc
    omega
  have ht : σ.cycleType.erase a = ({3} : Multiset ℕ) := by
    rw [← Multiset.cons_erase h3mem, hzero]
    decide
  have hsum7 : σ.cycleType.sum = 7 := by
    have hse := Multiset.sum_erase ha_mem
    rw [herase_sum, ha_eq] at hse
    omega
  have hcard_t : (σ.cycleType.erase a).card = 1 := by
    conv_lhs => rw [← Multiset.cons_erase h3mem]
    rw [Multiset.card_cons, hzero, Multiset.card_zero]
  have hcard2 : σ.cycleType.card = 2 := by
    conv_lhs => rw [← Multiset.cons_erase ha_mem]
    rw [Multiset.card_cons, hcard_t]
  refine ⟨?_, hsum7, hcard2⟩
  rw [← Multiset.cons_erase ha_mem, ht, ha_eq]
  decide

/-- The alternating group `A₇` has no element whose order is divisible by `12`. -/
lemma no_dvd_twelve_orderOf_alternatingGroup (y : alternatingGroup (Fin 7)) :
    ¬ (12 : ℕ) ∣ orderOf y := by
  intro h
  have h12 : (12 : ℕ) ∣ orderOf (y : Equiv.Perm (Fin 7)) := by
    rw [Subgroup.orderOf_coe]
    exact h
  obtain ⟨-, hsum, hcard⟩ := cycleType_facts_of_twelve_dvd_orderOf (y : Equiv.Perm (Fin 7)) h12
  -- the sign formula gives `sign y = (-1)^(7 + 2) = -1`, so `y` is odd
  have hsign : Equiv.Perm.sign (y : Equiv.Perm (Fin 7)) = -1 := by
    rw [Equiv.Perm.sign_of_cycleType, hsum, hcard]
    decide
  have hone : Equiv.Perm.sign (y : Equiv.Perm (Fin 7)) = 1 :=
    Equiv.Perm.mem_alternatingGroup.mp y.2
  rw [hone] at hsign
  exact absurd hsign (by decide)

/-- No element of `C_{A₇}(a7K) = C_{A₇}((4 5 6))` has order `4`.

Route 1 (structure).  An `x` commuting with the `3`-cycle `c = (456)` preserves its support `{4,5,6}` (`Equiv.Perm.support_conj`, `support` of `c` is `{4,5,6}`), so `x = x|{0,1,2,3} · c^i`; the `{4,5,6}` part commutes with `c|{4,5,6}`, a `3`-cycle in `Sym {4,5,6}`, hence lies in `⟨c|⟩`, of order `3`.  If `orderOf x = 4` then the `{4,5,6}` part has order dividing `gcd(4,3)=1`, so `x` fixes `{4,5,6}` pointwise and `x` is a permutation of the four points `{0,1,2,3}` of order `4`, i.e. a `4`-cycle, hence odd — contradicting `x ∈ A₇`.  (`(4 5 6)` is even, so `x ∈ A₇` forces `x|{0,1,2,3}` even.)

Route 2 (order `12`).  If `orderOf x = 4` then with `c x = x c`, `orderOf (c * x) = 12` (`Commute.orderOf_mul_eq_mul_orderOf_of_coprime` for `orderOf c = 3`, or `Commute.orderOf_mul_eq_mul` with coprime orders `3` and `4`); but `A₇` has no element of order divisible by `12`: if `12 ∣ orderOf y` for a permutation `y` of `Fin 7`, then `4 ∣ y.cycleType.lcm` and `3 ∣ y.cycleType.lcm`, so some cycle has length `4` and some cycle has length `3` (a length divisible by `3` is `3` or `6`, and `6 + 4 > 7`); with `sum cycleType ≤ 7` this forces `cycleType = {4,3}`, and `Equiv.Perm.sign_of_cycleType` gives `sign y = (-1)^(7 + 2) = -1`, so `y ∉ A₇`.  See `Submission/Work/A7F/no_order_fifteen_perm.lean` for the same lcm/cycle-length technique on `15`. -/
theorem A7KNoOrderFour : ∀ x ∈ Subgroup.centralizer (Work.A7.a7K : Set (alternatingGroup (Fin 7))), orderOf x ≠ 4 := by
  intro x hx h4
  -- `x` commutes with the `3`-cycle generating `a7K`
  have hmem : Work.A7.a7ThreeCycle ∈ Work.A7.a7K := by
    rw [Work.A7.a7K]
    exact Subgroup.mem_zpowers _
  have hcx : Commute Work.A7.a7ThreeCycle x := (Subgroup.mem_centralizer_iff.mp hx) _ hmem
  -- so `(4 5 6) * x` has order `3 * 4 = 12`
  have h12 : orderOf (Work.A7.a7ThreeCycle * x) = 12 := by
    rw [hcx.orderOf_mul_eq_mul_orderOf_of_coprime
        (by rw [Work.A7.orderOf_a7ThreeCycle, h4]; norm_num),
      Work.A7.orderOf_a7ThreeCycle, h4]
  -- which is impossible in `A₇`
  exact no_dvd_twelve_orderOf_alternatingGroup (Work.A7.a7ThreeCycle * x) ⟨1, by simp [h12]⟩

end Work.AUTA7.A7
