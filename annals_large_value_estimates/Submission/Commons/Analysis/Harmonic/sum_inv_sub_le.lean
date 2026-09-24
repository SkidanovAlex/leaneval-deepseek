import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Data.Int.Star
import Submission.Commons.Analysis.Harmonic.sum_range_inv_add_le

namespace Commons.Analysis.Harmonic

open Finset Real

/-- For a strictly increasing enumeration `a : Fin n ↪o ℤ` with `n > 0`, the `i`-th value is at
least `a 0 + i`. -/
private lemma orderEmb_int_ge {n : ℕ} (a : Fin n ↪o ℤ) (hn : 0 < n) (i : Fin n) :
    a ⟨0, hn⟩ + ((i : ℕ) : ℤ) ≤ a i := by
  have key : ∀ m (hm : m < n), (a ⟨0, hn⟩ : ℤ) + (m : ℤ) ≤ a ⟨m, hm⟩ := by
    intro m
    induction m using Nat.strong_induction_on with
    | h m ih =>
      intro hm
      rcases Nat.eq_zero_or_pos m with h0 | hpos
      · subst h0
        simp
      · obtain ⟨m', rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.pos_iff_ne_zero.mp hpos)
        have hm' : m' < n := Nat.lt_of_succ_lt hm
        have ih' := ih m' (Nat.lt_succ_self m') hm'
        have hstep : a ⟨m', hm'⟩ + 1 ≤ a ⟨m' + 1, hm⟩ :=
          Int.add_one_le_iff.mpr (a.strictMono (by simp [Fin.lt_def]))
        calc (a ⟨0, hn⟩ : ℤ) + ((m' + 1 : ℕ) : ℤ)
            = ((a ⟨0, hn⟩ : ℤ) + (m' : ℤ)) + 1 := by push_cast; ring
          _ ≤ a ⟨m', hm'⟩ + 1 := by linarith
          _ ≤ a ⟨m' + 1, hm⟩ := hstep
  exact key i.val i.isLt

/-- Sum of `1/(k - x)` over a finite set of integers `k` whose shifts `k - x` are separated by at
least `1` (they are distinct integers) and lie in `[T, U]`, bounded by `1/T + log(1 + U/T)`. -/
lemma sum_inv_sub_le {s : Finset ℤ} {x T U : ℝ} (hT : 0 < T) (hU : 0 ≤ U)
    (hlo : ∀ k ∈ s, T ≤ (k : ℝ) - x) (hhi : ∀ k ∈ s, (k : ℝ) - x ≤ U) :
    (∑ k ∈ s, 1 / ((k : ℝ) - x)) ≤ 1 / T + Real.log (1 + U / T) := by
  rcases eq_or_ne s.card 0 with h0 | hpos
  · have hs : s = ∅ := Finset.card_eq_zero.mp h0
    rw [hs, Finset.sum_empty]
    have h1 : (0 : ℝ) < 1 / T := one_div_pos.mpr hT
    have h2 : (1 : ℝ) ≤ 1 + U / T := by
      have : (0 : ℝ) ≤ U / T := div_nonneg hU hT.le
      linarith
    have h3 : (0 : ℝ) ≤ Real.log (1 + U / T) := Real.log_nonneg h2
    linarith
  · have hn : 0 < s.card := Nat.pos_of_ne_zero hpos
    set a : Fin s.card ↪o ℤ := s.orderEmbOfFin rfl with ha
    have hmem : ∀ i : Fin s.card, a i ∈ s := by
      intro i
      rw [ha]
      exact Finset.orderEmbOfFin_mem s rfl i
    have himg : Finset.image a Finset.univ = s := by
      rw [ha]
      exact Finset.image_orderEmbOfFin_univ s rfl
    have hidx : s.card - 1 < s.card := Nat.sub_lt hn Nat.zero_lt_one
    have hterm : ∀ i : Fin s.card, 1 / ((a i : ℝ) - x) ≤ 1 / (T + (i : ℝ)) := by
      intro i
      have hTi : (0 : ℝ) < T + (i : ℝ) := by
        have hnn : (0 : ℝ) ≤ (i : ℝ) := Nat.cast_nonneg _
        linarith
      have h0 : T ≤ (a ⟨0, hn⟩ : ℝ) - x := hlo _ (hmem ⟨0, hn⟩)
      have hdec : (a ⟨0, hn⟩ : ℝ) + ((i : ℕ) : ℝ) ≤ (a i : ℝ) := by
        exact_mod_cast orderEmb_int_ge a hn i
      have hge : T + (i : ℝ) ≤ (a i : ℝ) - x := by linarith
      exact one_div_le_one_div_of_le hTi hge
    have hsum1 : ∑ k ∈ s, 1 / ((k : ℝ) - x) = ∑ i : Fin s.card, 1 / ((a i : ℝ) - x) := by
      conv_lhs => rw [← himg]
      have := Finset.sum_image (f := fun k : ℤ => 1 / ((k : ℝ) - x)) (g := a) (s := Finset.univ)
        (by intro p _ q _ hpq; exact a.injective hpq)
      simpa using this
    have hsum2 : ∑ i : Fin s.card, 1 / (T + (i : ℝ)) ≤
        1 / T + Real.log (1 + ((s.card - 1 : ℕ) : ℝ) / T) := by
      rw [Fin.sum_univ_eq_sum_range (fun i : ℕ => 1 / (T + (i : ℝ))) s.card]
      have hcard : s.card - 1 + 1 = s.card := by omega
      have hL := sum_range_inv_add_le hT (s.card - 1)
      rw [hcard] at hL
      exact hL
    have hlast : ((s.card - 1 : ℕ) : ℝ) ≤ U := by
      have h0 : T ≤ (a ⟨0, hn⟩ : ℝ) - x := hlo _ (hmem ⟨0, hn⟩)
      have hdec : (a ⟨0, hn⟩ : ℝ) + ((s.card - 1 : ℕ) : ℝ) ≤
          (a ⟨s.card - 1, hidx⟩ : ℝ) := by
        exact_mod_cast orderEmb_int_ge a hn ⟨s.card - 1, hidx⟩
      have hup : (a ⟨s.card - 1, hidx⟩ : ℝ) - x ≤ U := hhi _ (hmem ⟨s.card - 1, hidx⟩)
      have hnn : (0 : ℝ) ≤ ((s.card - 1 : ℕ) : ℝ) := Nat.cast_nonneg _
      linarith
    have hlog : Real.log (1 + ((s.card - 1 : ℕ) : ℝ) / T) ≤ Real.log (1 + U / T) := by
      apply Real.log_le_log
      · have : (0 : ℝ) ≤ ((s.card - 1 : ℕ) : ℝ) / T := div_nonneg (Nat.cast_nonneg _) hT.le
        linarith
      · have := div_le_div_of_nonneg_right hlast hT.le
        linarith
    calc ∑ k ∈ s, 1 / ((k : ℝ) - x)
        = ∑ i : Fin s.card, 1 / ((a i : ℝ) - x) := hsum1
      _ ≤ ∑ i : Fin s.card, 1 / (T + (i : ℝ)) := Finset.sum_le_sum (fun i _ => hterm i)
      _ ≤ 1 / T + Real.log (1 + ((s.card - 1 : ℕ) : ℝ) / T) := hsum2
      _ ≤ 1 / T + Real.log (1 + U / T) := by linarith [hlog]

end Commons.Analysis.Harmonic