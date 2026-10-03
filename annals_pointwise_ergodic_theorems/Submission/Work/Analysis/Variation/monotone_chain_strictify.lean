import Mathlib

namespace Work.Analysis.Variation

/-- **Auxiliary strengthening.**  For a monotone `w : ℕ → ℕ` and a cost function `G` vanishing on
the diagonal, the chain `w 0, w 1, …, w J` can be replaced, at equal total cost, by a strictly
increasing chain `v` (on all of `ℕ`) whose first `J' + 1` values are values of `w` and whose last
value is `w J`.  Consecutive repetitions of `w` are simply dropped; the vanishing `G (a, a)` terms
make the total cost unchanged. -/
private theorem monotone_chain_strictify_aux {G : ℕ → ℕ → ENNReal} (hG : ∀ a, G a a = 0)
    (w : ℕ → ℕ) (hw : Monotone w) (J : ℕ) :
    ∃ (J' : ℕ) (v : ℕ → ℕ), StrictMono v ∧ (∀ i, i ≤ J' → ∃ j, v i = w j) ∧ v J' = w J ∧
      (∑ j ∈ Finset.range J, G (w j) (w (j + 1))) = ∑ i ∈ Finset.range J', G (v i) (v (i + 1)) := by
  induction J with
  | zero =>
    refine ⟨0, fun i => w 0 + i, ?_, ?_, ?_, ?_⟩
    · intro i j hij
      exact Nat.add_lt_add_left hij (w 0)
    · intro i hi
      have hi0 : i = 0 := Nat.eq_zero_of_le_zero hi
      subst hi0
      exact ⟨0, rfl⟩
    · rfl
    · simp
  | succ J IH =>
    obtain ⟨J', v, hv_mono, hv_w, hv_last, hv_sum⟩ := IH
    by_cases hJ : w J = w (J + 1)
    · -- the new term vanishes, keep the chain unchanged
      refine ⟨J', v, hv_mono, hv_w, ?_, ?_⟩
      · exact hv_last.trans hJ
      · rw [Finset.sum_range_succ, hJ, hG (w (J + 1)), add_zero]
        exact hv_sum
    · -- the new term is a genuine jump, extend the chain by one value
      have hlt : w J < w (J + 1) := lt_of_le_of_ne (hw (Nat.le_succ J)) hJ
      have hv'succ : ∀ i, v i < v (i + 1) := fun i => hv_mono (Nat.lt_succ_self i)
      obtain ⟨v', hv'⟩ : ∃ f : ℕ → ℕ, f = fun i => if i ≤ J' then v i else w (J + 1) + (i - J' - 1) :=
        ⟨_, rfl⟩
      have hv'lo : ∀ i, i ≤ J' → v' i = v i := by
        intro i hi
        simp only [hv']
        exact if_pos hi
      have hv'hi : ∀ i, J' < i → v' i = w (J + 1) + (i - J' - 1) := by
        intro i hi
        simp only [hv']
        exact if_neg (by omega)
      have hmono : StrictMono v' := by
        refine strictMono_nat_of_lt_succ ?_
        intro i
        by_cases hi : i ≤ J'
        · by_cases hi1 : i + 1 ≤ J'
          · rw [hv'lo i hi, hv'lo (i + 1) hi1]
            exact hv'succ i
          · have hie : i = J' := by omega
            rw [hie, hv'lo J' le_rfl, hv'hi (J' + 1) (by omega), hv_last]
            omega
        · rw [hv'hi i (by omega), hv'hi (i + 1) (by omega)]
          omega
      have hv'w : ∀ i, i ≤ J' + 1 → ∃ j, v' i = w j := by
        intro i hi
        by_cases hile : i ≤ J'
        · rw [hv'lo i hile]
          exact hv_w i hile
        · have hie : i = J' + 1 := by omega
          rw [hie, hv'hi (J' + 1) (by omega)]
          refine ⟨J + 1, ?_⟩
          omega
      have hv'last : v' (J' + 1) = w (J + 1) := by
        rw [hv'hi (J' + 1) (by omega)]
        omega
      have hb : ∀ i ∈ Finset.range J', G (v' i) (v' (i + 1)) = G (v i) (v (i + 1)) := by
        intro i hi
        have hi' : i < J' := Finset.mem_range.mp hi
        rw [hv'lo i (by omega), hv'lo (i + 1) (by omega)]
      have hv'sum : (∑ j ∈ Finset.range (J + 1), G (w j) (w (j + 1)))
          = ∑ i ∈ Finset.range (J' + 1), G (v' i) (v' (i + 1)) := by
        calc (∑ j ∈ Finset.range (J + 1), G (w j) (w (j + 1)))
            = (∑ j ∈ Finset.range J, G (w j) (w (j + 1))) + G (w J) (w (J + 1)) :=
              Finset.sum_range_succ _ _
          _ = (∑ i ∈ Finset.range J', G (v i) (v (i + 1))) + G (w J) (w (J + 1)) := by
              rw [hv_sum]
          _ = (∑ i ∈ Finset.range J', G (v' i) (v' (i + 1))) + G (v' J') (v' (J' + 1)) := by
              rw [Finset.sum_congr rfl hb, hv'lo J' le_rfl, hv'last, hv_last]
          _ = ∑ i ∈ Finset.range (J' + 1), G (v' i) (v' (i + 1)) :=
              (Finset.sum_range_succ _ _).symm
      exact ⟨J' + 1, v', hmono, hv'w, hv'last, hv'sum⟩

theorem monotone_chain_strictify {G : ℕ → ℕ → ENNReal} (hG : ∀ a, G a a = 0) {P : ℕ → Prop} (w : ℕ → ℕ) (hw : Monotone w) (hP : ∀ j, P (w j)) (J : ℕ) : ∃ (J' : ℕ) (v : ℕ → ℕ), StrictMono v ∧ (∀ i, i ≤ J' → P (v i)) ∧ (∑ j ∈ Finset.range J, G (w j) (w (j + 1))) = ∑ i ∈ Finset.range J', G (v i) (v (i + 1)) := by
  obtain ⟨J', v, hv_mono, hv_w, -, hv_sum⟩ := monotone_chain_strictify_aux hG w hw J
  refine ⟨J', v, hv_mono, ?_, hv_sum⟩
  intro i hi
  obtain ⟨j, hj⟩ := hv_w i hi
  rw [hj]
  exact hP j

end Work.Analysis.Variation
