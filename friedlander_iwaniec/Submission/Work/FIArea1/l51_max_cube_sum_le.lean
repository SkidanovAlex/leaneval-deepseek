import Mathlib

namespace Work.FIArea1

open Finset
open scoped BigOperators

/-! ### Two elementary auxiliary estimates

`fi_inner_split` splits, for a fixed `a ≥ 1`, the inner sum of `1/max(a,b)³` over a
finite set `s` into its `b ≤ a` part (contributing `1/a³`, i.e. one term) and its
`b > a` part (contributing `1/b³`).  `fi_sum_Icc_inv_sq_le_two` is the elementary
bound `∑_{a ≤ L} 1/a² ≤ 2`, obtained from the quadratic `p`-series estimate
`Finset.sum_Ioo_inv_sq_le`. -/

private lemma fi_inner_split (s : Finset ℕ) (a : ℕ) :
    (∑ b ∈ s, (1:ℝ) / ((max a b : ℕ) : ℝ)^3)
      = (∑ _b ∈ s.filter (fun b => b ≤ a), (1:ℝ) / (a:ℝ)^3)
        + (∑ b ∈ s.filter (fun b => a < b), (1:ℝ) / (b:ℝ)^3) := by
  rw [← Finset.sum_filter_add_sum_filter_not s (fun b => b ≤ a)
        (fun b => (1:ℝ) / ((max a b : ℕ) : ℝ)^3)]
  rw [Finset.filter_congr (s := s) (p := fun b => ¬ b ≤ a) (q := fun b => a < b)
        (fun _ _ => not_le)]
  congr 1
  · apply Finset.sum_congr rfl
    intro b hb
    rw [Finset.mem_filter] at hb
    rw [max_eq_left hb.2]
  · apply Finset.sum_congr rfl
    intro b hb
    rw [Finset.mem_filter] at hb
    rw [max_eq_right (le_of_lt hb.2)]

private lemma fi_sum_Icc_inv_sq_le_two (L : ℕ) :
    (∑ a ∈ Finset.Icc 1 L, (1:ℝ)/(a:ℝ)^2) ≤ 2 := by
  have hI : Finset.Icc 1 L = Finset.Ioo 0 (L+1) := by
    ext x; simp only [Finset.mem_Icc, Finset.mem_Ioo]; omega
  calc (∑ a ∈ Finset.Icc 1 L, (1:ℝ)/(a:ℝ)^2)
      = ∑ a ∈ Finset.Ioo 0 (L+1), ((a:ℝ)^2)⁻¹ := by
        rw [hI]; apply Finset.sum_congr rfl; intro a _; rw [one_div]
    _ ≤ 2 := by
        have h := sum_Ioo_inv_sq_le (α := ℝ) 0 (L+1)
        simpa using h

/-- **Cubic max-sum bound.** For every `L`, `Σ_{(a,b) ∈ [1,L]²} 1/max(a,b)³ ≤ 8`.

*Route.* Write `∑_{c} · = ∑_{a ∈ Icc 1 L} ∑_{b ∈ Icc 1 L} ·` (`Finset.sum_product`). For fixed `a ≥ 1`,
`1/max(a,b)³ = 1/a³` when `b ≤ a` and `= 1/b³` when `a < b`; split the inner sum with
`Finset.sum_filter_add_sum_filter_not`. The `b ≤ a` part contributes `#{b ∈ Icc 1 L : b ≤ a}/a³`
`= a/a³ = 1/a²` (the set is `Icc 1 a` since `a ≤ L`, via `Nat.card_Icc`). The `a < b` part is
`∑_{b ∈ Ioc a L} 1/b³ ≤ (1/a)·∑_{b ∈ Ioc a L} 1/b²` (as `1/b³ ≤ (1/a)·(1/b²)` for `b > a ≥ 1`), and
`∑_{b ∈ Ioc a L} 1/b² ≤ 1/a - 1/L ≤ 1/a` by `sum_Ioc_inv_sq_le_sub`. So the inner sum is `≤ 2/a²`.
Finally `∑_{a ∈ Icc 1 L} 2/a² ≤ 4` because `∑_{a ∈ Icc 1 L} 1/a² = 1 + ∑_{a ∈ Ioc 1 L} 1/a² ≤ 1 + 1 = 2`
(again `sum_Ioc_inv_sq_le_sub`, or `sum_Ioo_inv_sq_le`). Total `≤ 4 ≤ 8`. -/
theorem l51_max_cube_sum_le (L : ℕ) :
    (∑ c ∈ (Finset.Icc 1 L).product (Finset.Icc 1 L),
        (1 : ℝ) / ((max c.1 c.2 : ℕ) : ℝ) ^ 3) ≤ 8 := by
  classical
  rw [Finset.product_eq_sprod, Finset.sum_product]
  have hstep : (∑ a ∈ Finset.Icc 1 L, ∑ b ∈ Finset.Icc 1 L, (1:ℝ)/((max a b:ℕ):ℝ)^3)
      = (∑ a ∈ Finset.Icc 1 L, ∑ _b ∈ (Finset.Icc 1 L).filter (fun b => b ≤ a), (1:ℝ)/(a:ℝ)^3)
        + (∑ a ∈ Finset.Icc 1 L,
            ∑ b ∈ (Finset.Icc 1 L).filter (fun b => a < b), (1:ℝ)/(b:ℝ)^3) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro a _
    exact fi_inner_split (Finset.Icc 1 L) a
  rw [hstep]
  have hP1 : (∑ a ∈ Finset.Icc 1 L,
        ∑ _b ∈ (Finset.Icc 1 L).filter (fun b => b ≤ a), (1:ℝ)/(a:ℝ)^3)
      ≤ ∑ a ∈ Finset.Icc 1 L, (1:ℝ)/(a:ℝ)^2 := by
    apply Finset.sum_le_sum
    intro a ha
    have hcard : ((Finset.Icc 1 L).filter (fun b => b ≤ a)).card ≤ a := by
      have hsub : (Finset.Icc 1 L).filter (fun b => b ≤ a) ⊆ Finset.Icc 1 a := by
        intro b hb
        rw [Finset.mem_filter, Finset.mem_Icc] at hb
        exact Finset.mem_Icc.mpr ⟨hb.1.1, hb.2⟩
      calc ((Finset.Icc 1 L).filter (fun b => b ≤ a)).card
          ≤ (Finset.Icc 1 a).card := Finset.card_le_card hsub
        _ = a := by rw [Nat.card_Icc]; omega
    rw [Finset.sum_const, nsmul_eq_mul]
    have hcast : (((Finset.Icc 1 L).filter (fun b => b ≤ a)).card : ℝ) ≤ (a:ℝ) := by
      exact_mod_cast hcard
    calc (((Finset.Icc 1 L).filter (fun b => b ≤ a)).card : ℝ) * ((1:ℝ)/(a:ℝ)^3)
        ≤ (a:ℝ) * ((1:ℝ)/(a:ℝ)^3) := by
          apply mul_le_mul_of_nonneg_right hcast; positivity
      _ = (1:ℝ)/(a:ℝ)^2 := by
          have ha0 : (a:ℝ) ≠ 0 := by
            have h1 : 1 ≤ a := (Finset.mem_Icc.mp ha).1
            positivity
          field_simp
  have hP2 : (∑ a ∈ Finset.Icc 1 L,
        ∑ b ∈ (Finset.Icc 1 L).filter (fun b => a < b), (1:ℝ)/(b:ℝ)^3)
      ≤ 2 * ∑ a ∈ Finset.Icc 1 L, (1:ℝ)/(a:ℝ)^2 := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro a ha
    have ha1 : 1 ≤ a := (Finset.mem_Icc.mp ha).1
    have ha0 : (0:ℝ) < (a:ℝ) := by exact_mod_cast ha1
    have hsub : (Finset.Icc 1 L).filter (fun b => a < b) ⊆ Finset.Ioo a (L+1) := by
      intro b hb
      rw [Finset.mem_filter, Finset.mem_Icc] at hb
      exact Finset.mem_Ioo.mpr ⟨hb.2, by omega⟩
    have hA : (∑ b ∈ (Finset.Icc 1 L).filter (fun b => a < b), (1:ℝ)/(b:ℝ)^3)
        ≤ ∑ b ∈ Finset.Ioo a (L+1), (1:ℝ)/(b:ℝ)^3 :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)
    have hB : (∑ b ∈ Finset.Ioo a (L+1), (1:ℝ)/(b:ℝ)^3)
        ≤ (1/(a:ℝ)) * ∑ b ∈ Finset.Ioo a (L+1), (1:ℝ)/(b:ℝ)^2 := by
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro b hb
      rw [Finset.mem_Ioo] at hb
      have hb0 : (0:ℝ) < (b:ℝ) := by
        have h1 : 1 ≤ b := by omega
        exact_mod_cast h1
      have hle : (a:ℝ) ≤ (b:ℝ) := by exact_mod_cast le_of_lt hb.1
      have hmul : (a:ℝ) * (b:ℝ)^2 ≤ (b:ℝ)^3 := by
        calc (a:ℝ) * (b:ℝ)^2 ≤ (b:ℝ) * (b:ℝ)^2 :=
              mul_le_mul_of_nonneg_right hle (sq_nonneg _)
          _ = (b:ℝ)^3 := by ring
      have hkey := one_div_le_one_div_of_le
        (show (0:ℝ) < (a:ℝ)*(b:ℝ)^2 by positivity) hmul
      have h1 : (1/(a:ℝ)) * (1/(b:ℝ)^2) = (1:ℝ)/((a:ℝ)*(b:ℝ)^2) := by
        rw [div_mul_div_comm]; norm_num
      calc (1:ℝ)/(b:ℝ)^3 ≤ 1/((a:ℝ)*(b:ℝ)^2) := hkey
        _ = (1/(a:ℝ)) * (1/(b:ℝ)^2) := h1.symm
    have hC : (∑ b ∈ Finset.Ioo a (L+1), (1:ℝ)/(b:ℝ)^2) ≤ 2/((a:ℝ)+1) := by
      have h1 : (∑ b ∈ Finset.Ioo a (L+1), (1:ℝ)/(b:ℝ)^2)
          = ∑ b ∈ Finset.Ioo a (L+1), ((b:ℝ)^2)⁻¹ := by
        apply Finset.sum_congr rfl; intro b _; rw [one_div]
      rw [h1]
      exact sum_Ioo_inv_sq_le a (L+1)
    have hD : (1/(a:ℝ)) * (2/((a:ℝ)+1)) ≤ 2/(a:ℝ)^2 := by
      have h1 : (2:ℝ)/((a:ℝ)+1) ≤ 2/(a:ℝ) := by
        rw [div_le_div_iff₀ (by linarith) ha0]; linarith
      calc (1/(a:ℝ)) * (2/((a:ℝ)+1)) ≤ (1/(a:ℝ)) * (2/(a:ℝ)) :=
            mul_le_mul_of_nonneg_left h1 (by positivity)
        _ = 2/(a:ℝ)^2 := by
            have ha0' : (a:ℝ) ≠ 0 := ne_of_gt ha0
            field_simp
    calc (∑ b ∈ (Finset.Icc 1 L).filter (fun b => a < b), (1:ℝ)/(b:ℝ)^3)
        ≤ ∑ b ∈ Finset.Ioo a (L+1), (1:ℝ)/(b:ℝ)^3 := hA
      _ ≤ (1/(a:ℝ)) * ∑ b ∈ Finset.Ioo a (L+1), (1:ℝ)/(b:ℝ)^2 := hB
      _ ≤ (1/(a:ℝ)) * (2/((a:ℝ)+1)) := mul_le_mul_of_nonneg_left hC (by positivity)
      _ ≤ 2/(a:ℝ)^2 := hD
      _ = 2 * (1/(a:ℝ)^2) := by ring
  have hSq := fi_sum_Icc_inv_sq_le_two L
  linarith

end Work.FIArea1
