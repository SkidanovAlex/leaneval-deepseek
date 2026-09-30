import Mathlib
import Submission.Work.BMF.mr_direct.card_sq_dvd_le
import Submission.Work.BMF.mr_direct.range_defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BMF.mr_direct

/-- Counting the integers of an arbitrary range `[A,B]` (with `A ≤ B ≤ 4A`) that are
divisible by the square of a prime of `primeSet P Q`, for `1 ≤ A` and `2 ≤ P ≤ Q`.

We split `[A,B] ⊆ [A,2A] ∪ [2A,4A]` and apply the dyadic count `card_sq_dvd_le` to each
half, giving `4A/P + 8A/P = 12A/P`. -/
lemma card_sq_dvd_range_le (A B P Q : ℝ) (hA : 1 ≤ A) (hAB : A ≤ B) (hB4 : B ≤ 4 * A)
    (hP : 2 ≤ P) (hPQ : P ≤ Q) :
    (((Work.BMF.natIcc A B).filter
        (fun n => ∃ p ∈ Work.BMF.mrDirect.primeSet P Q, p * p ∣ n)).card : ℝ)
      ≤ 12 * A / P := by
  classical
  set φ : ℕ → Prop := fun n => ∃ p ∈ Work.BMF.mrDirect.primeSet P Q, p * p ∣ n with hφ
  have hsub : (Work.BMF.natIcc A B).filter φ ⊆
      (Work.BMF.natIcc A (2*A)).filter φ ∪ (Work.BMF.natIcc (2*A) (4*A)).filter φ := by
    intro n hn
    rw [Finset.mem_filter] at hn
    obtain ⟨hnS, hnφ⟩ := hn
    simp only [Work.BMF.natIcc, Finset.mem_Icc] at hnS
    rw [Finset.mem_union]
    have h4 : n ≤ ⌊4*A⌋₊ := le_trans hnS.2 (Nat.floor_mono (by linarith))
    rcases le_or_gt n ⌊2*A⌋₊ with h2 | h2
    · exact Or.inl (by
        simp only [Finset.mem_filter, Work.BMF.natIcc, Finset.mem_Icc]
        exact ⟨⟨hnS.1, h2⟩, hnφ⟩)
    · have hcl : ⌈2*A⌉₊ ≤ ⌊2*A⌋₊ + 1 := Nat.ceil_le_floor_add_one (2*A)
      exact Or.inr (by
        simp only [Finset.mem_filter, Work.BMF.natIcc, Finset.mem_Icc]
        exact ⟨⟨by omega, h4⟩, hnφ⟩)
  have step1 : ((Work.BMF.natIcc A B).filter φ).card
      ≤ ((Work.BMF.natIcc A (2*A)).filter φ).card
        + ((Work.BMF.natIcc (2*A) (4*A)).filter φ).card :=
    (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
  have step1' : (((Work.BMF.natIcc A B).filter φ).card : ℝ)
      ≤ (((Work.BMF.natIcc A (2*A)).filter φ).card : ℝ)
        + (((Work.BMF.natIcc (2*A) (4*A)).filter φ).card : ℝ) := by
    exact_mod_cast step1
  have h1 : (((Work.BMF.natIcc A (2*A)).filter φ).card : ℝ) ≤ 4*A/P :=
    Work.BMF.mr_direct.card_sq_dvd_le A P Q hA hP hPQ
  have h2 : (((Work.BMF.natIcc (2*A) (4*A)).filter φ).card : ℝ) ≤ 8*A/P := by
    have hraw := Work.BMF.mr_direct.card_sq_dvd_le (2*A) P Q (by linarith) hP hPQ
    have heq : Work.BMF.natIcc (2*A) (2*(2*A)) = Work.BMF.natIcc (2*A) (4*A) := by
      simp only [Work.BMF.natIcc]
      rw [show (2:ℝ)*(2*A) = 4*A by ring]
    rw [heq] at hraw
    rw [show (4:ℝ)*(2*A)/P = 8*A/P by ring] at hraw
    exact hraw
  calc (((Work.BMF.natIcc A B).filter φ).card : ℝ)
      ≤ _ := step1'
    _ ≤ 4*A/P + 8*A/P := add_le_add h1 h2
    _ = 12*A/P := by ring

end Work.BMF.mr_direct
