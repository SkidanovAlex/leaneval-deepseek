import Mathlib
import Submission.Work.A7F.Defs

namespace Work.A7F

/-- If a prime divides the least common multiple of a multiset of naturals, then it divides
one of the members. -/
lemma exists_mem_of_prime_dvd_multiset_lcm {p : ℕ} (hp : p.Prime) {s : Multiset ℕ}
    (h : p ∣ s.lcm) : ∃ a ∈ s, p ∣ a := by
  induction s using Multiset.induction_on with
  | empty =>
    rw [Multiset.lcm_zero] at h
    exact absurd h hp.not_dvd_one
  | cons a t ih =>
    rw [Multiset.lcm_cons, lcm_eq_nat_lcm, hp.dvd_lcm] at h
    rcases h with h | h
    · exact ⟨a, Multiset.mem_cons_self a t, h⟩
    · obtain ⟨b, hb, hbd⟩ := ih h
      exact ⟨b, Multiset.mem_cons_of_mem hb, hbd⟩

/-- No permutation of a seven-element set has order divisible by `15`: the order of a permutation
is the least common multiple of its cycle lengths, so `3 | orderOf g` forces a cycle of length at
least `3` and `5 | orderOf g` forces a cycle of length at least `5`; distinct cycle factors have
disjoint supports, and `3 + 5 = 8 > 7`. -/
theorem no_order_fifteen_perm (g : Equiv.Perm (Fin 7)) : ¬ (15 ∣ orderOf g) := by
  intro h
  have h3 : 3 ∣ orderOf g := dvd_trans (by norm_num : (3 : ℕ) ∣ 15) h
  have h5 : 5 ∣ orderOf g := dvd_trans (by norm_num : (5 : ℕ) ∣ 15) h
  have h3l : 3 ∣ g.cycleType.lcm := by rw [Equiv.Perm.lcm_cycleType]; exact h3
  have h5l : 5 ∣ g.cycleType.lcm := by rw [Equiv.Perm.lcm_cycleType]; exact h5
  obtain ⟨c, hc_mem, hc3⟩ :=
    exists_mem_of_prime_dvd_multiset_lcm (by norm_num : Nat.Prime 3) h3l
  obtain ⟨d, hd_mem, hd5⟩ :=
    exists_mem_of_prime_dvd_multiset_lcm (by norm_num : Nat.Prime 5) h5l
  have hsum : g.cycleType.sum ≤ 7 := by
    have := Equiv.Perm.sum_cycleType_le g
    simpa using this
  have hc2 : 2 ≤ c := Equiv.Perm.two_le_of_mem_cycleType hc_mem
  have hd2 : 2 ≤ d := Equiv.Perm.two_le_of_mem_cycleType hd_mem
  rcases eq_or_ne c d with hcd | hcd
  · rw [← hcd] at hd5
    have h15 : 15 ∣ c := (by norm_num : Nat.Coprime 3 5).mul_dvd_of_dvd_of_dvd hc3 hd5
    have h15le : 15 ≤ c := Nat.le_of_dvd (by omega) h15
    have hcle : c ≤ g.cycleType.sum :=
      Multiset.single_le_sum (fun _ _ => Nat.zero_le _) c hc_mem
    omega
  · have h3le : 3 ≤ c := Nat.le_of_dvd (by omega) hc3
    have h5le : 5 ≤ d := Nat.le_of_dvd (by omega) hd5
    have hd_mem' : d ∈ g.cycleType.erase c :=
      (Multiset.mem_erase_of_ne (Ne.symm hcd)).mpr hd_mem
    have hdle : d ≤ (g.cycleType.erase c).sum :=
      Multiset.single_le_sum (fun _ _ => Nat.zero_le _) d hd_mem'
    have herase : c + (g.cycleType.erase c).sum = g.cycleType.sum :=
      Multiset.sum_erase hc_mem
    omega

end Work.A7F
