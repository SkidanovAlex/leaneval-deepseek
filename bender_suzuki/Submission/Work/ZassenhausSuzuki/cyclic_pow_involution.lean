import Mathlib

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option linter.style.haveILetI false

namespace Work.ZassenhausSuzuki

/-- In a cyclic group, there is at most one element of order two.  Hence if `s` is an
involution (`s ^ 2 = 1`, `s ≠ 1`) and `r` has order `2 ^ a` (`a ≥ 1`), then `s` equals the
unique element of order `2` inside `⟨r⟩`, namely `r ^ 2 ^ (a - 1)`. -/
theorem cyclic_pow_involution {B : Type} [Group B] [IsCyclic B] {s r : B} {a : ℕ}
    (hs2 : s ^ 2 = 1) (hs1 : s ≠ 1) (hr : orderOf r = 2 ^ a) (ha1 : 1 ≤ a) :
    s = r ^ 2 ^ (a - 1) := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := B)
  have hcard : orderOf g = Nat.card B := orderOf_eq_card_of_forall_mem_zpowers hg
  have h2a_pos : 0 < 2 ^ a := pow_pos (by norm_num) a
  have h2a_ne1 : 2 ^ a ≠ 1 := by
    have : 1 < 2 ^ a := Nat.one_lt_pow (by omega) (by norm_num)
    omega
  have hr_ne1 : r ≠ 1 := by
    intro h; rw [h, orderOf_one] at hr; exact h2a_ne1 hr.symm
  -- `B` is finite: otherwise `g` has infinite order and so does `r`, contradicting `orderOf r = 2 ^ a`.
  have hg0 : orderOf g ≠ 0 := by
    intro h0
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp (hg r)
    have hj0 : j ≠ 0 := by
      intro h; rw [h, zpow_zero] at hj; exact hr_ne1 hj.symm
    have hz := orderOf_zpow' g hj0
    rw [hj, h0, Nat.zero_div] at hz
    rw [hr] at hz
    exact h2a_pos.ne' hz
  haveI : Finite B := Nat.finite_of_card_ne_zero (by rw [← hcard]; exact hg0)
  haveI : Fintype B := Fintype.ofFinite B
  haveI : DecidableEq B := Classical.decEq B
  set t : B := r ^ 2 ^ (a - 1) with ht_def
  have ht2 : t ^ 2 = 1 := by
    rw [ht_def, ← pow_mul]
    have h2 : 2 ^ (a - 1) * 2 = 2 ^ a := by
      rw [← pow_succ]; congr 1; omega
    rw [h2, ← hr, pow_orderOf_eq_one]
  have ht_ne1 : t ≠ 1 := by
    rw [ht_def]
    intro h
    have hd : orderOf r ∣ 2 ^ (a - 1) := orderOf_dvd_iff_pow_eq_one.mpr h
    rw [hr] at hd
    have hpos : 0 < 2 ^ (a - 1) := by positivity
    have hle : 2 ^ a ≤ 2 ^ (a - 1) := Nat.le_of_dvd hpos hd
    have hlt : 2 ^ (a - 1) < 2 ^ a := by
      have h2 : 2 ^ a = 2 ^ (a - 1) * 2 := by
        rw [← pow_succ]; congr 1; omega
      rw [h2]; exact lt_mul_of_one_lt_right hpos (by norm_num)
    omega
  -- In a cyclic group, the number of solutions of `x ^ 2 = 1` is at most `2`.
  have hcard2 : (Finset.univ.filter (fun x : B => x ^ 2 = 1)).card ≤ 2 :=
    IsCyclic.card_pow_eq_one_le (α := B) (n := 2) (by norm_num)
  by_contra hst
  have hsub : ({1, s, t} : Finset B) ⊆ Finset.univ.filter (fun x : B => x ^ 2 = 1) := by
    intro x hx
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ x, ?_⟩
    have hx' : x = 1 ∨ x = s ∨ x = t := by simpa using hx
    rcases hx' with rfl | rfl | rfl
    · simp
    · exact hs2
    · exact ht2
  have h1 : (1 : B) ∉ ({s, t} : Finset B) := by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨Ne.symm hs1, Ne.symm ht_ne1⟩
  have h2 : s ∉ ({t} : Finset B) := by
    simp only [Finset.mem_singleton]
    exact hst
  have hcard3 : ({1, s, t} : Finset B).card = 3 := by
    rw [Finset.card_insert_of_notMem h1, Finset.card_insert_of_notMem h2, Finset.card_singleton]
  have := Finset.card_le_card hsub
  omega

end Work.ZassenhausSuzuki
