import Mathlib
import Submission.Work.A7.grid_sum_bound

/-!
# A7 — the "grid sum" bound, real-valued counting function

This is the `N0 : ℕ → ℝ` version of `Work.A7.grid_sum_bound` (which is stated for
`N0 : ℕ → ℕ`).  The Abel-summation argument is identical; only the counting
function carries real values, which is what the area-7 assembly requires (the
`N0` there are real-valued analytic quantities, not integers).

The generic helper lemmas `Vf`, `abel_identity` and `level_pointwise` are imported
from `Submission.Work.A7.grid_sum_bound`.
-/

namespace Work.A7

theorem grid_sum_boundR {α : Type*} [DecidableEq α] (A L : Finset α) (g : α → ℝ)
    (Lam : ℕ → ℝ) (C : ℝ → ℝ) (N0 : ℕ → ℝ) (s : ℕ) (lamS : ℝ)
    (hLA : L ⊆ A)
    (hLg : ∀ a ∈ L, g a < lamS)
    (hA : ∀ a ∈ A, g a ≤ Lam 0 → lamS ≤ g a ∨ a ∈ L)
    (hLamS : lamS ≤ Lam s)
    (hdec : ∀ j, j < s → Lam (j+1) ≤ Lam j)
    (hmono : ∀ x y : ℝ, x ≤ y → C y ≤ C x)
    (hC0 : C (Lam 0) = 0)
    (hcount : ∀ j, j ≤ s → ((A.filter (fun a => g a ≤ Lam j)).card : ℝ) ≤ N0 j) :
    ∑ a ∈ A.filter (fun a => g a ≤ Lam 0), C (g a) ≤
      (∑ a ∈ L, C (g a)) + (N0 s - (L.card : ℝ)) * C lamS +
        ∑ j ∈ Finset.range s, (N0 j - N0 (j+1)) * C (Lam (j+1)) := by
  -- Monotonicity of `Lam` on the window `{0, …, s}`.
  have hLam_mono : ∀ i j, i ≤ j → j ≤ s → Lam j ≤ Lam i := by
    intro i j hij hj
    have aux : ∀ n, i + n ≤ s → Lam (i + n) ≤ Lam i := by
      intro n
      induction n with
      | zero => intro _; simp
      | succ n ih =>
        intro h
        have hle : i + n ≤ s := by omega
        have hlt : i + n < s := by omega
        have heq : i + (n+1) = i + n + 1 := Nat.add_succ i n
        rw [heq]
        calc Lam (i + n + 1) ≤ Lam (i + n) := hdec (i+n) hlt
          _ ≤ Lam i := ih hle
    obtain ⟨n, hn⟩ := Nat.exists_eq_add_of_le hij
    rw [hn] at hj ⊢
    exact aux n hj
  have hlamS0 : lamS ≤ Lam 0 := le_trans hLamS (hLam_mono 0 s (Nat.zero_le s) le_rfl)
  -- `L` lies inside the top box `A.filter (g ≤ Lam 0)`.
  have hLS0 : L ⊆ A.filter (fun a => g a ≤ Lam 0) := by
    intro a ha
    simp only [Finset.mem_filter]
    exact ⟨hLA ha, le_of_lt (lt_of_lt_of_le (hLg a ha) hlamS0)⟩
  -- The staircase `Vf` decreases by one step.
  have hVstep : ∀ i, i ≤ s → Vf Lam s lamS (i+1) ≤ Vf Lam s lamS i := by
    intro i hi
    by_cases h : i + 1 ≤ s
    · rw [Vf_of_le Lam s lamS h, Vf_of_le Lam s lamS hi]
      exact hdec i (by omega)
    · have his : i = s := by omega
      rw [his, Vf_of_gt Lam s lamS (by omega), Vf_of_le Lam s lamS (le_refl s)]
      exact hLamS
  -- Pointwise staircase domination on the complement of `L`.
  have hpoint : ∀ a ∈ (A.filter (fun a => g a ≤ Lam 0)) \ L,
      C (g a) ≤ ∑ i ∈ Finset.range (s+1),
        (C (Vf Lam s lamS (i+1)) - C (Vf Lam s lamS i)) * (if g a ≤ Vf Lam s lamS i then 1 else 0) := by
    intro a ha
    have h1 := Finset.mem_sdiff.mp ha
    have haA : a ∈ A := (Finset.mem_filter.mp h1.1).1
    have ha0 : g a ≤ Lam 0 := (Finset.mem_filter.mp h1.1).2
    have haL : a ∉ L := h1.2
    have hxa : lamS ≤ g a := by
      rcases hA a haA ha0 with h | h
      · exact h
      · exact absurd h haL
    exact level_pointwise Lam C s lamS hmono hC0 hLam_mono (g a) ha0 hxa
  -- Cardinality of the sub-level set inside `A \ L`.
  have hcardid : ∀ i, i ≤ s →
      ∑ a ∈ (A.filter (fun a => g a ≤ Lam 0)) \ L, (if g a ≤ Vf Lam s lamS i then 1 else 0)
        = ((A.filter (fun a => g a ≤ Lam i)).card : ℝ) - (L.card : ℝ) := by
    intro i hi
    rw [Vf_of_le Lam s lamS hi, Finset.sum_boole]
    have hLsub : L ⊆ A.filter (fun a => g a ≤ Lam i) := by
      intro a ha
      simp only [Finset.mem_filter]
      exact ⟨hLA ha, le_of_lt (lt_of_lt_of_le (hLg a ha) (le_trans hLamS (hLam_mono i s hi le_rfl)))⟩
    have hset : (A.filter (fun a => g a ≤ Lam 0) \ L).filter (fun a => g a ≤ Lam i)
        = A.filter (fun a => g a ≤ Lam i) \ L := by
      apply Finset.ext
      intro a
      simp only [Finset.mem_filter, Finset.mem_sdiff]
      constructor
      · rintro ⟨⟨⟨haA, h0⟩, haLi⟩, hai⟩
        exact ⟨⟨haA, hai⟩, haLi⟩
      · rintro ⟨⟨haA, hai⟩, haLi⟩
        exact ⟨⟨⟨haA, le_trans hai (hLam_mono 0 i (Nat.zero_le i) hi)⟩, haLi⟩, hai⟩
    rw [hset, Finset.card_sdiff_of_subset hLsub, Nat.cast_sub (Finset.card_le_card hLsub)]
  -- Abel summation / interchange of the two sums.
  have hmain : ∑ a ∈ (A.filter (fun a => g a ≤ Lam 0)) \ L, C (g a) ≤
      (N0 s - (L.card : ℝ)) * C lamS +
        ∑ j ∈ Finset.range s, (N0 j - N0 (j+1)) * C (Lam (j+1)) := by
    calc ∑ a ∈ (A.filter (fun a => g a ≤ Lam 0)) \ L, C (g a)
        ≤ ∑ a ∈ (A.filter (fun a => g a ≤ Lam 0)) \ L, ∑ i ∈ Finset.range (s+1),
            (C (Vf Lam s lamS (i+1)) - C (Vf Lam s lamS i)) * (if g a ≤ Vf Lam s lamS i then 1 else 0) :=
          Finset.sum_le_sum hpoint
      _ = ∑ i ∈ Finset.range (s+1), (C (Vf Lam s lamS (i+1)) - C (Vf Lam s lamS i)) *
            (∑ a ∈ (A.filter (fun a => g a ≤ Lam 0)) \ L, (if g a ≤ Vf Lam s lamS i then 1 else 0)) := by
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro i hi
          exact (Finset.mul_sum _ _ _).symm
      _ ≤ ∑ i ∈ Finset.range (s+1), (C (Vf Lam s lamS (i+1)) - C (Vf Lam s lamS i)) * (N0 i - (L.card : ℝ)) := by
          apply Finset.sum_le_sum
          intro i hi
          have hile : i ≤ s := by simp only [Finset.mem_range] at hi; omega
          apply mul_le_mul_of_nonneg_left
          · rw [hcardid i hile]; have hc := hcount i hile; linarith
          · exact sub_nonneg.mpr (hmono _ _ (hVstep i hile))
      _ = (N0 s - (L.card : ℝ)) * C lamS +
            ∑ j ∈ Finset.range s, (N0 j - N0 (j+1)) * C (Lam (j+1)) := by
          rw [abel_identity (fun i => C (Vf Lam s lamS i)) (fun i => N0 i - (L.card : ℝ)) s
                (by rw [Vf_of_le Lam s lamS (Nat.zero_le s), hC0])]
          rw [Vf_of_gt Lam s lamS (Nat.lt_succ_self s)]
          congr 1
          · ring
          · apply Finset.sum_congr rfl
            intro i hi
            have hi1 : i + 1 ≤ s := by simp only [Finset.mem_range] at hi; omega
            rw [Vf_of_le Lam s lamS hi1]
            ring
  -- Peel off the `L`-part of the top box.
  have hsd := Finset.sum_sdiff (f := fun a => C (g a)) hLS0
  rw [← hsd]
  linarith [hmain]

end Work.A7
