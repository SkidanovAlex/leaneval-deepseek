import Mathlib.Algebra.CharP.Defs
import Mathlib.Analysis.Normed.Group.Basic

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.CoreResiduals

theorem norm_sub_le_of_step_bound {X E : Type*} [NormedAddCommGroup E]
    {f : X → ℝ → E} {a b δ N : ℝ} (hδ : 0 < δ)
    (hstep : ∀ t ∈ Set.Icc a b, ∀ t' ∈ Set.Icc a b, |t - t'| < δ →
      ∀ y : X, ‖f y t - f y t'‖ ≤ N * |t - t'|) :
    ∀ t ∈ Set.Icc a b, ∀ t' ∈ Set.Icc a b, ∀ y : X,
      ‖f y t - f y t'‖ ≤ N * |t - t'| := by
  -- Establish the bound under the extra assumption `t ≤ t'`, then use symmetry.
  have key : ∀ t ∈ Set.Icc a b, ∀ t' ∈ Set.Icc a b, t ≤ t' →
      ∀ y : X, ‖f y t - f y t'‖ ≤ N * |t - t'| := by
    intro t ht t' ht' hle y
    have hdnn : 0 ≤ t' - t := sub_nonneg.mpr hle
    have habs : |t - t'| = t' - t := by rw [abs_sub_comm]; exact abs_of_nonneg hdnn
    rw [habs]
    rcases lt_or_ge (t' - t) δ with hsmall | hbig
    · -- If the two points are already δ-close, this is exactly `hstep`.
      have := hstep t ht t' ht' (by rw [habs]; exact hsmall) y
      rwa [habs] at this
    · -- Otherwise subdivide the segment `[t, t']` into `n` equal pieces of length `< δ`.
      obtain ⟨n, hn⟩ := exists_nat_gt ((t' - t) / δ)
      have hn0 : (0:ℝ) < (n:ℝ) := lt_of_le_of_lt (div_nonneg hdnn hδ.le) hn
      have hnne : (n:ℝ) ≠ 0 := ne_of_gt hn0
      have hsteplen : (t' - t) / (n:ℝ) < δ := by
        rw [div_lt_iff₀ hn0]
        have h2 : (t' - t) < (n:ℝ) * δ := by
          have h3 := mul_lt_mul_of_pos_right hn hδ
          rwa [div_mul_cancel₀ (t' - t) (ne_of_gt hδ)] at h3
        linarith
      let s : ℕ → ℝ := fun k => t + (k:ℝ) * ((t' - t) / (n:ℝ))
      have hs0 : s 0 = t := by simp [s]
      have hsn : s n = t' := by
        simp only [s]
        rw [mul_div_cancel₀ (t' - t) hnne]
        ring
      have hsn_nonneg : 0 ≤ (t' - t) / (n:ℝ) := div_nonneg hdnn hn0.le
      -- All subdivision points stay inside `[a, b]`.
      have hmem : ∀ k, k ≤ n → s k ∈ Set.Icc a b := by
        intro k hk
        obtain ⟨ha, _⟩ := Set.mem_Icc.mp ht
        obtain ⟨_, hb'⟩ := Set.mem_Icc.mp ht'
        have hsk_ge : t ≤ s k := by
          simp only [s]
          have : 0 ≤ (k:ℝ) * ((t' - t) / (n:ℝ)) :=
            mul_nonneg (Nat.cast_nonneg k) hsn_nonneg
          linarith
        have hsk_le : s k ≤ t' := by
          simp only [s]
          have hkn : (k:ℝ) ≤ (n:ℝ) := by exact_mod_cast hk
          have hmul : (k:ℝ) * ((t' - t) / (n:ℝ)) ≤ (n:ℝ) * ((t' - t) / (n:ℝ)) :=
            mul_le_mul_of_nonneg_right hkn hsn_nonneg
          rw [mul_div_cancel₀ (t' - t) hnne] at hmul
          linarith
        exact ⟨le_trans ha hsk_ge, le_trans hsk_le hb'⟩
      -- Consecutive subdivision points are `< δ` apart.
      have hdiff : ∀ k, |s k - s (k+1)| = (t' - t) / (n:ℝ) := by
        intro k
        have hval : s k - s (k+1) = -((t' - t) / (n:ℝ)) := by
          simp only [s]
          push_cast
          ring
        rw [hval, abs_neg, abs_of_nonneg hsn_nonneg]
      -- Telescope and apply the local bound on each piece.
      calc ‖f y t - f y t'‖
          = ‖f y (s 0) - f y (s n)‖ := by rw [hs0, hsn]
        _ = ‖∑ k ∈ Finset.range n, (f y (s k) - f y (s (k+1)))‖ := by
              rw [Finset.sum_range_sub']
        _ ≤ ∑ k ∈ Finset.range n, ‖f y (s k) - f y (s (k+1))‖ := norm_sum_le _ _
        _ ≤ ∑ _k ∈ Finset.range n, N * ((t' - t) / (n:ℝ)) := by
              apply Finset.sum_le_sum
              intro k hk
              have hklt : k < n := Finset.mem_range.mp hk
              have hstep' := hstep (s k) (hmem k (le_of_lt hklt)) (s (k+1))
                (hmem (k+1) (Nat.succ_le_of_lt hklt))
                (by rw [hdiff k]; exact hsteplen) y
              rwa [hdiff k] at hstep'
        _ = (n:ℝ) * (N * ((t' - t) / (n:ℝ))) := by
              rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        _ = N * (t' - t) := by
              field_simp
  intro t ht t' ht' y
  rcases le_total t t' with hle | hle
  · exact key t ht t' ht' hle y
  · have h := key t' ht' t ht hle y
    rw [norm_sub_rev, abs_sub_comm]
    exact h

end Work.CoreResiduals
