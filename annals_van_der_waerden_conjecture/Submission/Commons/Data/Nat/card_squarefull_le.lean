import Mathlib
import Submission.Commons.Data.Nat.exists_sq_mul_cube
import Submission.Commons.Data.Nat.ncard_pairs_sq_mul_cube_le

namespace Commons.Data.Nat

theorem card_squarefull_le (X : ℕ) :
    ({N : ℕ | N ≤ X ∧ ∀ p : ℕ, Nat.Prime p → p ∣ N → p ^ 2 ∣ N} : Set ℕ).ncard
      ≤ 4 * (Nat.sqrt X + 1) := by
  classical
  set S : Set ℕ := {N : ℕ | N ≤ X ∧ ∀ p : ℕ, Nat.Prime p → p ∣ N → p ^ 2 ∣ N} with hS
  have h0 : (0 : ℕ) ∈ S := by
    rw [hS]
    exact ⟨Nat.zero_le X, fun p _ _ => dvd_zero _⟩
  set S1 : Set ℕ := {N : ℕ | N ∈ S ∧ 1 ≤ N} with hS1
  have hsub : S ⊆ insert 0 S1 := by
    intro N hN
    rcases Nat.eq_zero_or_pos N with h | h
    · subst h; exact Set.mem_insert _ _
    · exact Set.mem_insert_iff.mpr (Or.inr ⟨hN, h⟩)
  have hSfin : S.Finite := by
    refine Set.Finite.subset (Set.finite_Iic X) ?_
    intro N hN
    rw [hS] at hN
    exact Set.mem_Iic.mpr hN.1
  have hS1fin : S1.Finite := hSfin.subset (fun N hN => hN.1)
  have hstep1 : S.ncard ≤ S1.ncard + 1 := by
    calc S.ncard ≤ (insert 0 S1).ncard := Set.ncard_le_ncard hsub (hS1fin.insert 0)
      _ ≤ S1.ncard + 1 := Set.ncard_insert_le 0 S1
  -- injection from S1 into pairs (a,b) with a^2 b^3 = N
  set T : Set (ℕ × ℕ) := {p : ℕ × ℕ | 1 ≤ p.1 ∧ 1 ≤ p.2 ∧ p.1 ^ 2 * p.2 ^ 3 ≤ X} with hT
  have hchoice : ∀ N ∈ S1, ∃ ab : ℕ × ℕ, ab.1 ^ 2 * ab.2 ^ 3 = N := by
    intro N hN
    have hNne : N ≠ 0 := by have := hN.2; omega
    have hpw : ∀ p : ℕ, Nat.Prime p → p ∣ N → p ^ 2 ∣ N := by
      have := hN.1; rw [hS] at this; exact this.2
    obtain ⟨a, b, hab⟩ := exists_sq_mul_cube N hNne hpw
    exact ⟨(a, b), hab⟩
  let f : ℕ → ℕ × ℕ := fun N => if h : N ∈ S1 then Classical.choose (hchoice N h) else (1, 1)
  have hf : ∀ N (hN : N ∈ S1), (f N).1 ^ 2 * (f N).2 ^ 3 = N := by
    intro N hN
    dsimp only [f]
    rw [dif_pos hN]
    exact Classical.choose_spec (hchoice N hN)
  have hmem : ∀ N ∈ S1, f N ∈ T := by
    intro N hN
    rw [hT]
    have hNX : N ≤ X := by have := hN.1; rw [hS] at this; exact this.1
    have hNpos : 1 ≤ N := hN.2
    have hfN := hf N hN
    refine ⟨?_, ?_, ?_⟩
    · by_contra hc
      have hc' : (f N).1 < 1 := not_le.mp hc
      have hz : (f N).1 = 0 := by omega
      rw [hz] at hfN
      simp at hfN
      omega
    · by_contra hc
      have hc' : (f N).2 < 1 := not_le.mp hc
      have hz : (f N).2 = 0 := by omega
      rw [hz] at hfN
      simp at hfN
      omega
    · rw [hfN]; exact hNX
  have hinj : Set.InjOn f S1 := by
    intro N1 hN1 N2 hN2 heq
    have e1 := hf N1 hN1
    have e2 := hf N2 hN2
    rw [← e1, heq, e2]
  have hTfin : T.Finite := by
    refine Set.Finite.subset (Set.Finite.prod (Set.finite_Iio (Nat.sqrt X + 1))
      (Set.finite_Iio (X + 1))) ?_
    intro p hp
    rw [hT] at hp
    obtain ⟨h1, h2, h3⟩ := hp
    rw [Set.mem_prod]
    refine ⟨?_, ?_⟩
    · rw [Set.mem_Iio]
      have hp1 : p.1 * p.1 ≤ X := by
        have hb : 1 ≤ p.2 ^ 3 := by
          calc (1:ℕ) = 1 ^ 3 := by norm_num
            _ ≤ p.2 ^ 3 := Nat.pow_le_pow_left h2 3
        calc p.1 * p.1 = p.1 ^ 2 := by ring
          _ = p.1 ^ 2 * 1 := by ring
          _ ≤ p.1 ^ 2 * p.2 ^ 3 := Nat.mul_le_mul_left _ hb
          _ ≤ X := h3
      exact Nat.lt_succ_of_le ((Nat.le_sqrt).mpr hp1)
    · rw [Set.mem_Iio]
      have hb : p.2 ≤ p.2 ^ 3 := Nat.le_self_pow (by norm_num) p.2
      have hp2 : p.2 ^ 3 ≤ X := by
        have ha : 1 ≤ p.1 ^ 2 := by
          calc (1:ℕ) = 1 ^ 2 := by norm_num
            _ ≤ p.1 ^ 2 := Nat.pow_le_pow_left h1 2
        calc p.2 ^ 3 = 1 * p.2 ^ 3 := by ring
          _ ≤ p.1 ^ 2 * p.2 ^ 3 := Nat.mul_le_mul_right _ ha
          _ ≤ X := h3
      exact Nat.lt_succ_of_le (le_trans hb hp2)
  have hS1Tle : S1.ncard ≤ T.ncard :=
    Set.ncard_le_ncard_of_injOn f hmem hinj hTfin
  have hTle : T.ncard ≤ 3 * (Nat.sqrt X + 1) := by
    rw [hT]
    exact ncard_pairs_sq_mul_cube_le X
  calc S.ncard ≤ S1.ncard + 1 := hstep1
    _ ≤ T.ncard + 1 := Nat.add_le_add_right hS1Tle 1
    _ ≤ 3 * (Nat.sqrt X + 1) + 1 := Nat.add_le_add_right hTle 1
    _ ≤ 4 * (Nat.sqrt X + 1) := by nlinarith [Nat.zero_le (Nat.sqrt X)]

end Commons.Data.Nat
