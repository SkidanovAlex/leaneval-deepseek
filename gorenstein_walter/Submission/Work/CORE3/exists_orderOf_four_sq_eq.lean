import Mathlib
import Submission.Work.CORE3.Defs

namespace Work.CORE3

/-- **Cyclic-group form.**  In a finite cyclic group whose order is divisible by `4`, every
element `t` of order `2` is the square of an element of order `4`: there is `s` with
`orderOf s = 4` and `s * s = t`.

This is the uniqueness of the involution (`IsCyclic.card_orderOf_eq_totient` with `d = 2` gives
`#{a | orderOf a = 2} = 1`) combined with the existence of an element of order `4`
(the same statement with `d = 4` gives `#{a | orderOf a = 4} = 2 ≠ 0`). -/
theorem exists_orderOf_four_sq_eq_of_cyclic {A : Type*} [Group A] [Finite A] [IsCyclic A]
    {t : A} (ht : orderOf t = 2) (h4 : 4 ∣ Nat.card A) :
    ∃ s : A, orderOf s = 4 ∧ s * s = t := by
  classical
  have hfin : Fintype A := Fintype.ofFinite A
  have h4' : 4 ∣ Fintype.card A := by rwa [Nat.card_eq_fintype_card] at h4
  have h2' : 2 ∣ Fintype.card A := (by norm_num : (2 : ℕ) ∣ 4).trans h4'
  -- there is an element of order `4`
  have hcard4 : (Finset.univ.filter (fun a : A => orderOf a = 4)).card = 2 := by
    rw [IsCyclic.card_orderOf_eq_totient (α := A) (d := 4) h4']
    decide
  have hpos : 0 < (Finset.univ.filter (fun a : A => orderOf a = 4)).card := by omega
  obtain ⟨s, hs⟩ := Finset.card_pos.mp hpos
  have hsord : orderOf s = 4 := (Finset.mem_filter.mp hs).2
  -- and the element of order `2` is unique
  have hcard2 : (Finset.univ.filter (fun a : A => orderOf a = 2)).card = 1 := by
    rw [IsCyclic.card_orderOf_eq_totient (α := A) (d := 2) h2', Nat.totient_two]
  have hss : orderOf (s * s) = 2 := by
    rw [← pow_two, orderOf_pow, hsord]
    norm_num
  have key : s * s = t := by
    refine Finset.card_le_one.mp (Nat.le_of_eq hcard2) (s * s) ?_ t ?_
    · simp [hss]
    · simp [ht]
  exact ⟨s, hsord, key⟩

theorem exists_orderOf_four_sq_eq {G : Type*} [Group G] [Finite G]
    {S S0 : Subgroup G} {t : G}
    (hS0le : S0 ≤ S) (hS2 : IsPGroup 2 S) (hS0cyc : IsCyclic S0)
    (ht : t ∈ S0) (htord : orderOf t = 2) (hcard : 4 ≤ Nat.card ↥S0) :
    ∃ s ∈ S0, orderOf s = 4 ∧ s * s = t := by
  classical
  have hcyc : IsCyclic ↥S0 := hS0cyc
  -- `S0`, a subgroup of the 2-group `S`, is a finite 2-group, so `|S0| = 2 ^ k`
  have hS0p : IsPGroup 2 ↥S0 := hS2.to_le hS0le
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card (p := 2) (G := ↥S0)).mp hS0p
  -- `4 ≤ |S0| = 2 ^ k` forces `k ≥ 2`
  have hk2 : 2 ≤ k := by
    by_contra h
    have h1 : k ≤ 1 := by omega
    have h2 : 2 ^ k ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) h1
    norm_num at h2
    omega
  -- hence `4 ∣ |S0|`
  have h4 : 4 ∣ Nat.card ↥S0 := by
    rw [hk]
    have : (4 : ℕ) = 2 ^ 2 := by norm_num
    rw [this]
    exact pow_dvd_pow 2 hk2
  -- apply the cyclic-group statement inside `S0`
  let t' : ↥S0 := ⟨t, ht⟩
  have ht'ord : orderOf t' = 2 := by
    rw [← Subgroup.orderOf_coe t']
    exact htord
  obtain ⟨s', hs'ord, hs't⟩ :=
    exists_orderOf_four_sq_eq_of_cyclic (A := ↥S0) (t := t') ht'ord h4
  refine ⟨(s' : G), s'.2, ?_, ?_⟩
  · rwa [Subgroup.orderOf_coe s']
  · have h := congrArg (Subtype.val : ↥S0 → G) hs't
    simpa using h

end Work.CORE3
