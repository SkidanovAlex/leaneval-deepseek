import Mathlib.Algebra.BigOperators.Ring.Finset
import Submission.Commons.NumberTheory.ZMod.card_int_abs_le_modEq
import Submission.Commons.NumberTheory.ZMod.natCast_eq_of_lt

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

set_option linter.style.haveILetI false

namespace Commons.NumberTheory.ZMod

/-- Divisibility of `a^2 + c^4` by `d`, reformulated inside `ZMod d`. -/
lemma int_dvd_pow4_iff_zmod (d c : ℕ) (a : ℤ) :
    (d : ℤ) ∣ a ^ 2 + (c : ℤ) ^ 4 ↔ (a : ZMod d) ^ 2 + (c : ZMod d) ^ 4 = 0 := by
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd (a ^ 2 + (c : ℤ) ^ 4) d]
  push_cast
  rfl

theorem card_int_abs_le_dvd_sq_add_pow4 (d c : ℕ) (hd : 1 ≤ d) (Y : ℝ) (hY : 0 ≤ Y) :
    ((Finset.filter (fun a : ℤ => |(a : ℝ)| ≤ Y ∧ ((d : ℤ) ∣ a ^ 2 + (c : ℤ) ^ 4))
        (Finset.Icc (-(⌊Y⌋₊ + 1 : ℤ)) (⌊Y⌋₊ + 1 : ℤ))).card : ℤ)
      = ∑ β ∈ (Finset.range d).filter (fun β : ℕ => ((d : ℤ) ∣ (β : ℤ) ^ 2 + (c : ℤ) ^ 4)),
          (⌊(Y - (β : ℝ)) / (d : ℝ)⌋ + ⌊(Y + (β : ℝ)) / (d : ℝ)⌋ + 1) := by
  classical
  have hd0 : d ≠ 0 := Nat.one_le_iff_ne_zero.mp hd
  haveI : NeZero d := ⟨hd0⟩
  set B : Finset ℕ :=
    (Finset.range d).filter (fun β : ℕ => ((d : ℤ) ∣ (β : ℤ) ^ 2 + (c : ℤ) ^ 4)) with hB
  set S : Finset ℤ :=
    Finset.filter (fun a : ℤ => |(a : ℝ)| ≤ Y ∧ ((d : ℤ) ∣ a ^ 2 + (c : ℤ) ^ 4))
      (Finset.Icc (-(⌊Y⌋₊ + 1 : ℤ)) (⌊Y⌋₊ + 1 : ℤ)) with hS
  set T : ℕ → Finset ℤ := fun β =>
    Finset.filter (fun a : ℤ => |(a : ℝ)| ≤ Y ∧ ((a : ZMod d) = ((β : ℤ) : ZMod d)))
      (Finset.Icc (-(⌊Y⌋₊ + 1 : ℤ)) (⌊Y⌋₊ + 1 : ℤ)) with hT
  have hS_eq : S = B.biUnion T := by
    ext a
    rw [hS, hT]
    constructor
    · intro ha
      rw [Finset.mem_filter] at ha
      obtain ⟨haI, habs, hdvd⟩ := ha
      have hval : ((((a : ZMod d).val : ℤ)) : ZMod d) = (a : ZMod d) := by
        push_cast
        exact ZMod.natCast_zmod_val (a : ZMod d)
      rw [Finset.mem_biUnion]
      refine ⟨(a : ZMod d).val, ?_, ?_⟩
      · rw [hB, Finset.mem_filter, Finset.mem_range]
        refine ⟨ZMod.val_lt (a : ZMod d), ?_⟩
        rw [int_dvd_pow4_iff_zmod, hval]
        exact (int_dvd_pow4_iff_zmod d c a).mp hdvd
      · rw [Finset.mem_filter]
        exact ⟨haI, habs, by rw [hval]⟩
    · intro ha
      rw [Finset.mem_biUnion] at ha
      obtain ⟨β, hβB, haT⟩ := ha
      rw [hB, Finset.mem_filter] at hβB
      obtain ⟨_, hβdvd⟩ := hβB
      rw [Finset.mem_filter] at haT
      obtain ⟨haI, habs, haeq⟩ := haT
      rw [Finset.mem_filter]
      refine ⟨haI, habs, ?_⟩
      rw [int_dvd_pow4_iff_zmod, haeq]
      exact (int_dvd_pow4_iff_zmod d c (β : ℤ)).mp hβdvd
  have hdisj : (B : Set ℕ).PairwiseDisjoint T := by
    rw [Finset.pairwiseDisjoint_iff]
    intro i hi j hj hne
    have hiB : i ∈ B := Finset.mem_coe.mp hi
    have hjB : j ∈ B := Finset.mem_coe.mp hj
    obtain ⟨a, ha⟩ := hne
    rw [Finset.mem_inter] at ha
    obtain ⟨hai, haj⟩ := ha
    rw [hT, Finset.mem_filter] at hai
    rw [hT, Finset.mem_filter] at haj
    obtain ⟨_, _, hi_eq⟩ := hai
    obtain ⟨_, _, hj_eq⟩ := haj
    have hild : i < d := by
      rw [hB, Finset.mem_filter, Finset.mem_range] at hiB; exact hiB.1
    have hjld : j < d := by
      rw [hB, Finset.mem_filter, Finset.mem_range] at hjB; exact hjB.1
    have heq : (i : ZMod d) = (j : ZMod d) := by
      have h1 : (((i : ℤ)) : ZMod d) = (((j : ℤ)) : ZMod d) := by
        rw [← hi_eq, ← hj_eq]
      simpa using h1
    exact (natCast_eq_of_lt hild hjld).mp heq
  rw [hS_eq, Finset.card_biUnion hdisj]
  push_cast
  refine Finset.sum_congr rfl (fun β hβ => ?_)
  have hβd : β < d := by
    rw [hB, Finset.mem_filter, Finset.mem_range] at hβ; exact hβ.1
  rw [hT]
  simpa using card_int_abs_le_modEq d hd β hβd Y hY

end Commons.NumberTheory.ZMod