import Mathlib
import Submission.Work.FIPlan.Interface
import Submission.Work.FIArea7.card_filter_mul_le

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Work.FIArea7

open Finset
open scoped BigOperators

noncomputable section

/-! ## Elementary estimates for `∑ 1/b²`

The telescoping model sum `1/b² ≤ 2/(b(b+1)) = 2/b - 2/(b+1)` gives `∑_{b=1}^{N} 1/b² ≤ 2`. -/

private lemma sum_range_inv_sq_le_two (N : ℕ) :
    (∑ j ∈ Finset.range N, (1 : ℝ) / ((j : ℝ) + 1) ^ 2) ≤ 2 := by
  have hterm : ∀ j ∈ Finset.range N,
      (1 : ℝ) / ((j : ℝ) + 1) ^ 2
        ≤ 2 / ((j : ℝ) + 1) - 2 / (((j + 1 : ℕ) : ℝ) + 1) := by
    intro j _
    have hj1 : (((j + 1 : ℕ) : ℝ) + 1) = (j : ℝ) + 2 := by push_cast; ring
    rw [hj1]
    have hkey : 2 / ((j : ℝ) + 1) - 2 / ((j : ℝ) + 2)
        = 2 / (((j : ℝ) + 1) * ((j : ℝ) + 2)) := by
      field_simp
      ring
    rw [hkey]
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [(Nat.cast_nonneg j : (0 : ℝ) ≤ (j : ℝ))]
  calc (∑ j ∈ Finset.range N, (1 : ℝ) / ((j : ℝ) + 1) ^ 2)
      ≤ ∑ j ∈ Finset.range N, (2 / ((j : ℝ) + 1) - 2 / (((j + 1 : ℕ) : ℝ) + 1)) :=
        Finset.sum_le_sum hterm
    _ = 2 / (((0 : ℕ) : ℝ) + 1) - 2 / (((N : ℕ) : ℝ) + 1) := by
        have h := Finset.sum_range_sub' (fun k : ℕ => 2 / ((k : ℝ) + 1)) N
        simpa using h
    _ ≤ 2 := by
        have h0 : 2 / (((0 : ℕ) : ℝ) + 1) = 2 := by norm_num
        rw [h0]
        have : (0 : ℝ) ≤ 2 / ((N : ℝ) + 1) := by positivity
        linarith

private lemma sum_Icc_eq_range (f : ℕ → ℝ) (N : ℕ) :
    (∑ b ∈ Finset.Icc 1 N, f b) = ∑ j ∈ Finset.range N, f (j + 1) := by
  induction N with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_Icc_succ_top (show 1 ≤ n + 1 by omega) f, ih, Finset.sum_range_succ]

private lemma sum_Icc_inv_sq_le_two (N : ℕ) :
    (∑ b ∈ Finset.Icc 1 N, (1 : ℝ) / (b : ℝ) ^ 2) ≤ 2 := by
  rw [sum_Icc_eq_range]
  simp only [Nat.cast_add, Nat.cast_one]
  exact sum_range_inv_sq_le_two N

/-! ## The weight of a single pair `(z₁, z₂)` -/

/-- `pairW B0 X d` is the `(b,e)`-sum `∑_{b ≤ B0} ∑_{e ≤ X} (1/b) [4be ∣ d] / d`. -/
def pairW (B0 X : ℕ) (d : ℕ) : ℝ :=
  ∑ b ∈ Finset.Icc 1 B0, ∑ e ∈ Finset.Icc 1 X,
    (1 / (b : ℝ)) * (if 4 * b * e ∣ d then (1 : ℝ) else 0) * ((d : ℝ))⁻¹

/-- The key arithmetic estimate: each pair contributes at most `2`.  For `d > 0` the number of
`e` with `4be ∣ d` is at most `d/(4b)`, so the sum is bounded by `(d/4)∑ 1/b² ≤ d/2`. -/
lemma pairW_le_two (B0 X d : ℕ) : pairW B0 X d ≤ 2 := by
  rcases Nat.eq_zero_or_pos d with hd | hd
  · subst hd
    simp only [pairW]
    simp
  · have hdpos : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
    have hS : (∑ b ∈ Finset.Icc 1 B0, ∑ e ∈ Finset.Icc 1 X,
        (1 / (b : ℝ)) * (if 4 * b * e ∣ d then (1 : ℝ) else 0)) ≤ (d : ℝ) / 2 := by
      calc (∑ b ∈ Finset.Icc 1 B0, ∑ e ∈ Finset.Icc 1 X,
              (1 / (b : ℝ)) * (if 4 * b * e ∣ d then (1 : ℝ) else 0))
          = ∑ b ∈ Finset.Icc 1 B0, (1 / (b : ℝ)) *
              ((((Finset.Icc 1 X).filter (fun e => 4 * b * e ∣ d)).card : ℕ) : ℝ) := by
            apply Finset.sum_congr rfl; intro b _
            have hb : (∑ e ∈ Finset.Icc 1 X, (if 4 * b * e ∣ d then (1 : ℝ) else 0))
                = ((((Finset.Icc 1 X).filter (fun e => 4 * b * e ∣ d)).card : ℕ) : ℝ) :=
              Finset.sum_boole (fun e => 4 * b * e ∣ d) (Finset.Icc 1 X)
            rw [← Finset.mul_sum, hb]
        _ ≤ ∑ b ∈ Finset.Icc 1 B0, (1 / (b : ℝ)) * ((d : ℝ) / (4 * (b : ℝ))) := by
            apply Finset.sum_le_sum; intro b hb
            obtain ⟨hb1, _⟩ := Finset.mem_Icc.mp hb
            have hbpos : (0 : ℝ) < (b : ℝ) := by exact_mod_cast (by omega : 0 < b)
            have hcb : ((((Finset.Icc 1 X).filter (fun e => 4 * b * e ∣ d)).card : ℕ) : ℝ)
                ≤ (d : ℝ) / (4 * (b : ℝ)) := by
              have hsub : (Finset.Icc 1 X).filter (fun e => 4 * b * e ∣ d)
                  ⊆ (Finset.Icc 1 d).filter (fun e => e * (4 * b) ≤ d) := by
                intro e he
                rw [Finset.mem_filter] at he ⊢
                obtain ⟨heI, hedvd⟩ := he
                obtain ⟨he1, _⟩ := Finset.mem_Icc.mp heI
                have hle : 4 * b * e ≤ d := Nat.le_of_dvd hd hedvd
                have he_d : e ≤ d :=
                  Nat.le_of_dvd hd (Nat.dvd_trans ⟨4 * b, by ring⟩ hedvd)
                exact ⟨Finset.mem_Icc.mpr ⟨he1, he_d⟩,
                  by calc e * (4 * b) = 4 * b * e := Nat.mul_comm e (4 * b)
                        _ ≤ d := hle⟩
              calc ((((Finset.Icc 1 X).filter (fun e => 4 * b * e ∣ d)).card : ℕ) : ℝ)
                  ≤ ((((Finset.Icc 1 d).filter (fun e => e * (4 * b) ≤ d)).card : ℕ) : ℝ) := by
                    exact_mod_cast Finset.card_le_card hsub
                _ ≤ (d : ℝ) / ((4 * b : ℕ) : ℝ) := card_filter_mul_le d (4 * b) (by omega)
                _ = (d : ℝ) / (4 * (b : ℝ)) := by rw [Nat.cast_mul]; norm_num
            exact mul_le_mul_of_nonneg_left hcb (div_nonneg (by norm_num) (le_of_lt hbpos))
        _ = (d : ℝ) / 4 * ∑ b ∈ Finset.Icc 1 B0, (1 : ℝ) / (b : ℝ) ^ 2 := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl; intro b _
            ring
        _ ≤ (d : ℝ) / 4 * 2 :=
            mul_le_mul_of_nonneg_left (sum_Icc_inv_sq_le_two B0)
              (div_nonneg (by exact_mod_cast Nat.zero_le d) (by norm_num))
        _ = (d : ℝ) / 2 := by ring
    have hW : pairW B0 X d = (∑ b ∈ Finset.Icc 1 B0, ∑ e ∈ Finset.Icc 1 X,
        (1 / (b : ℝ)) * (if 4 * b * e ∣ d then (1 : ℝ) else 0)) * (d : ℝ)⁻¹ := by
      simp only [pairW, Finset.sum_mul]
    rw [hW, ← div_eq_mul_inv, div_le_iff₀ hdpos]
    linarith [hS, hdpos]

/-! ## Rearranging the fourfold sum -/

lemma sum_comm_three {α β γ : Type*} (s : Finset α) (t : Finset β) (G : Finset γ)
    (h : α → β → γ → ℝ) :
    (∑ a ∈ s, ∑ b ∈ t, ∑ c ∈ G, h a b c) = ∑ c ∈ G, ∑ a ∈ s, ∑ b ∈ t, h a b c := by
  calc ∑ a ∈ s, ∑ b ∈ t, ∑ c ∈ G, h a b c
      = ∑ a ∈ s, ∑ c ∈ G, ∑ b ∈ t, h a b c := by
        apply Finset.sum_congr rfl; intro a _
        exact Finset.sum_comm
    _ = ∑ c ∈ G, ∑ a ∈ s, ∑ b ∈ t, h a b c := Finset.sum_comm

lemma sum_comm_four {α β γ : Type*} (s : Finset α) (t : Finset β) (G : Finset γ)
    (f : α → β → γ → γ → ℝ) :
    (∑ b ∈ s, ∑ e ∈ t, ∑ z1 ∈ G, ∑ z2 ∈ G, f b e z1 z2)
      = ∑ z1 ∈ G, ∑ z2 ∈ G, ∑ b ∈ s, ∑ e ∈ t, f b e z1 z2 := by
  calc ∑ b ∈ s, ∑ e ∈ t, ∑ z1 ∈ G, ∑ z2 ∈ G, f b e z1 z2
      = ∑ b ∈ s, ∑ z1 ∈ G, ∑ e ∈ t, ∑ z2 ∈ G, f b e z1 z2 := by
        apply Finset.sum_congr rfl; intro b _
        exact Finset.sum_comm
    _ = ∑ z1 ∈ G, ∑ b ∈ s, ∑ e ∈ t, ∑ z2 ∈ G, f b e z1 z2 := Finset.sum_comm
    _ = ∑ z1 ∈ G, ∑ b ∈ s, ∑ z2 ∈ G, ∑ e ∈ t, f b e z1 z2 := by
        apply Finset.sum_congr rfl; intro z1 _
        apply Finset.sum_congr rfl; intro b _
        exact Finset.sum_comm
    _ = ∑ z1 ∈ G, ∑ z2 ∈ G, ∑ b ∈ s, ∑ e ∈ t, f b e z1 z2 := by
        apply Finset.sum_congr rfl; intro z1 _
        exact Finset.sum_comm

/-! ## The quadruple bound -/

theorem quadruple_le (B0 X : ℕ) (G : Finset GaussianInt) (β : GaussianInt → ℂ) :
    (∑ b ∈ Finset.Icc 1 B0, ∑ e ∈ Finset.Icc 1 X, ∑ z1 ∈ G, ∑ z2 ∈ G,
        (1 / (b : ℝ)) * (if 4 * b * e ∣ Work.FIPlan.absDelta z1 z2 then (1 : ℝ) else 0)
          * (((Work.FIPlan.absDelta z1 z2 : ℕ) : ℝ))⁻¹ * ‖β z1‖ * ‖β z2‖)
      ≤ 2 * (∑ z ∈ G, ‖β z‖) ^ 2 := by
  have hreorder :
      (∑ b ∈ Finset.Icc 1 B0, ∑ e ∈ Finset.Icc 1 X, ∑ z1 ∈ G, ∑ z2 ∈ G,
        (1 / (b : ℝ)) * (if 4 * b * e ∣ Work.FIPlan.absDelta z1 z2 then (1 : ℝ) else 0)
          * (((Work.FIPlan.absDelta z1 z2 : ℕ) : ℝ))⁻¹ * ‖β z1‖ * ‖β z2‖)
      = ∑ z1 ∈ G, ∑ z2 ∈ G, ∑ b ∈ Finset.Icc 1 B0, ∑ e ∈ Finset.Icc 1 X,
        (1 / (b : ℝ)) * (if 4 * b * e ∣ Work.FIPlan.absDelta z1 z2 then (1 : ℝ) else 0)
          * (((Work.FIPlan.absDelta z1 z2 : ℕ) : ℝ))⁻¹ * ‖β z1‖ * ‖β z2‖ :=
    sum_comm_four (Finset.Icc 1 B0) (Finset.Icc 1 X) G
      (fun b e z1 z2 =>
        (1 / (b : ℝ)) * (if 4 * b * e ∣ Work.FIPlan.absDelta z1 z2 then (1 : ℝ) else 0)
          * (((Work.FIPlan.absDelta z1 z2 : ℕ) : ℝ))⁻¹ * ‖β z1‖ * ‖β z2‖)
  rw [hreorder]
  calc (∑ z1 ∈ G, ∑ z2 ∈ G, ∑ b ∈ Finset.Icc 1 B0, ∑ e ∈ Finset.Icc 1 X,
        (1 / (b : ℝ)) * (if 4 * b * e ∣ Work.FIPlan.absDelta z1 z2 then (1 : ℝ) else 0)
          * (((Work.FIPlan.absDelta z1 z2 : ℕ) : ℝ))⁻¹ * ‖β z1‖ * ‖β z2‖)
      = ∑ z1 ∈ G, ∑ z2 ∈ G, pairW B0 X (Work.FIPlan.absDelta z1 z2) * ‖β z1‖ * ‖β z2‖ := by
        apply Finset.sum_congr rfl; intro z1 _
        apply Finset.sum_congr rfl; intro z2 _
        simp only [pairW, ← Finset.sum_mul]
    _ ≤ ∑ z1 ∈ G, ∑ z2 ∈ G, 2 * ‖β z1‖ * ‖β z2‖ := by
        apply Finset.sum_le_sum; intro z1 _
        apply Finset.sum_le_sum; intro z2 _
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (pairW_le_two B0 X (Work.FIPlan.absDelta z1 z2))
            (norm_nonneg _)) (norm_nonneg _)
    _ = 2 * (∑ z ∈ G, ‖β z‖) ^ 2 := by
        rw [pow_two, Finset.sum_mul_sum G G (fun z => ‖β z‖) (fun z => ‖β z‖)]
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl; intro z1 _
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl; intro z2 _
        ring

end

end Work.FIArea7
