import Mathlib
import Submission.Work.FatouCoord.Setup
import Submission.Work.FatouCoord.Estimate.coordError_bound
import Submission.Work.FatouCoord.Estimate.iterate_re_growth

namespace Work.FatouCoord.Estimate
open Work.FatouCoord

theorem summable_coordError {f h : ℂ → ℂ} {a : ℂ} {r A A' : ℝ} (hb : ParabolicBounds f h a r A A') :
    ∃ N : ℝ, 0 < N ∧ 1 / r < N ∧ ∀ w : ℂ, N < w.re →
      Summable (fun k : ℕ => ‖coordError f (1 - a) ((wMap f)^[k] w)‖) := by
  obtain ⟨N₁, B, hN₁pos, hBnn, hrN₁, hcErr⟩ := coordError_bound hb
  obtain ⟨N₂, hN₂pos, hrN₂, hgrowth⟩ := iterate_re_growth hb
  refine ⟨max N₁ N₂ + 1, ?_, ?_, ?_⟩
  · have hle : N₁ ≤ max N₁ N₂ := le_max_left _ _
    linarith
  · have hle : N₁ ≤ max N₁ N₂ := le_max_left _ _
    linarith
  · intro w hw
    have hw₁ : N₁ < w.re := by have hle : N₁ ≤ max N₁ N₂ := le_max_left _ _; linarith
    have hw₂ : N₂ < w.re := by have hle : N₂ ≤ max N₁ N₂ := le_max_right _ _; linarith
    obtain ⟨m, hm⟩ := exists_nat_gt (2 * (N₁ - N₂))
    set α : ℝ := N₂ + (m : ℝ) / 2 with hαdef
    have hαgrow : N₁ < α := by
      have h2 : 2 * (N₁ - N₂) < (m : ℝ) := hm
      rw [hαdef]; linarith
    have hαpos : 0 < α := lt_trans hN₁pos hαgrow
    set γ : ℝ := min α 1 with hγdef
    have hγpos : 0 < γ := by rw [hγdef]; exact lt_min hαpos one_pos
    have hkey : ∀ n : ℕ, (γ / 2) * ((n : ℝ) + 1) ≤ α + (n : ℝ) / 2 := by
      intro n
      have hn : (0:ℝ) ≤ (n:ℝ) := Nat.cast_nonneg n
      rcases lt_or_ge α 1 with h | h
      · have hγ : γ = α := by rw [hγdef]; exact min_eq_left (le_of_lt h)
        rw [hγ]; nlinarith [hn, h, hαpos]
      · have hγ : γ = 1 := by rw [hγdef]; exact min_eq_right h
        rw [hγ]; nlinarith [hn, h]
    have hle : ∀ n : ℕ,
        ‖coordError f (1 - a) ((wMap f)^[n + m] w)‖ ≤ (B / (γ / 2) ^ 2) / (((n + 1 : ℕ) : ℝ)) ^ 2 := by
      intro n
      set wk : ℂ := (wMap f)^[n + m] w with hwkdef
      have hgr : N₂ + ((n + m : ℕ) : ℝ) / 2 ≤ wk.re := by
        have h := hgrowth w hw₂ (n + m)
        rw [hwkdef]; exact h
      have hcast : ((n + m : ℕ) : ℝ) = (n : ℝ) + (m : ℝ) := by push_cast; ring
      have hwk_re : α + (n : ℝ) / 2 ≤ wk.re := by
        rw [hαdef]
        rw [hcast] at hgr
        linarith [hgr]
      have hN₁lt : N₁ < wk.re := by
        have hαle : α ≤ α + (n : ℝ) / 2 := le_add_of_nonneg_right (by positivity)
        linarith [hαgrow, hwk_re]
      have hb1 : ‖coordError f (1 - a) wk‖ ≤ B / ‖wk‖ ^ 2 := hcErr wk hN₁lt
      have hwk_norm : α + (n : ℝ) / 2 ≤ ‖wk‖ := le_trans hwk_re (Complex.re_le_norm wk)
      have hβpos : 0 < α + (n : ℝ) / 2 := lt_of_lt_of_le hαpos (le_add_of_nonneg_right (by positivity))
      have hsqq : (α + (n : ℝ) / 2) ^ 2 ≤ ‖wk‖ ^ 2 :=
        pow_le_pow_left₀ (le_of_lt hβpos) hwk_norm 2
      have hstep1 : B / ‖wk‖ ^ 2 ≤ B / (α + (n : ℝ) / 2) ^ 2 :=
        div_le_div_of_nonneg_left hBnn (pow_pos hβpos 2) hsqq
      have hstep2 : B / (α + (n : ℝ) / 2) ^ 2 ≤ (B / (γ / 2) ^ 2) / (((n + 1 : ℕ) : ℝ)) ^ 2 := by
        have hk := hkey n
        have hposL : 0 < (γ / 2) * ((n : ℝ) + 1) := by positivity
        have hsq2 : ((γ / 2) * ((n : ℝ) + 1)) ^ 2 ≤ (α + (n : ℝ) / 2) ^ 2 :=
          pow_le_pow_left₀ (le_of_lt hposL) hk 2
        have h2 : B / (α + (n : ℝ) / 2) ^ 2 ≤ B / ((γ / 2) * ((n : ℝ) + 1)) ^ 2 :=
          div_le_div_of_nonneg_left hBnn (pow_pos hposL 2) hsq2
        have hcast2 : (((n + 1 : ℕ)) : ℝ) = (n : ℝ) + 1 := by push_cast; ring
        have hden_eq : ((γ / 2) * ((n : ℝ) + 1)) ^ 2 = (γ / 2) ^ 2 * ((n : ℝ) + 1) ^ 2 :=
          mul_pow _ _ _
        have hgoal : (B / (γ / 2) ^ 2) / ((((n + 1 : ℕ)) : ℝ)) ^ 2
            = B / ((γ / 2) ^ 2 * ((n : ℝ) + 1) ^ 2) := by
          rw [hcast2, div_div]
        rw [hgoal, ← hden_eq]
        exact h2
      calc ‖coordError f (1 - a) wk‖ ≤ B / ‖wk‖ ^ 2 := hb1
        _ ≤ B / (α + (n : ℝ) / 2) ^ 2 := hstep1
        _ ≤ (B / (γ / 2) ^ 2) / (((n + 1 : ℕ) : ℝ)) ^ 2 := hstep2
    have hmaj : Summable (fun n : ℕ => (B / (γ / 2) ^ 2) / ((((n + 1 : ℕ)) : ℝ)) ^ 2) := by
      have h0 : Summable (fun n : ℕ => (1:ℝ) / (n:ℝ)^2) :=
        (Real.summable_one_div_nat_pow (p := 2)).mpr (by norm_num)
      have h1 : Summable (fun n : ℕ => (1:ℝ) / ((((n + 1 : ℕ)) : ℝ))^2) :=
        (summable_nat_add_iff (f := fun n : ℕ => (1:ℝ)/(n:ℝ)^2) 1).mpr h0
      have h2 := h1.mul_left (B / (γ / 2) ^ 2)
      refine h2.congr (fun n => ?_)
      ring
    have hFsum : Summable (fun n : ℕ => ‖coordError f (1 - a) ((wMap f)^[n + m] w)‖) :=
      Summable.of_nonneg_of_le (fun n => norm_nonneg _) (fun n => hle n) hmaj
    exact (summable_nat_add_iff (f := fun k : ℕ => ‖coordError f (1 - a) ((wMap f)^[k] w)‖) m).mp hFsum

end Work.FatouCoord.Estimate
