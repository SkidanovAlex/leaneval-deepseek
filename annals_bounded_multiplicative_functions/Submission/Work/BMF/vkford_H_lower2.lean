import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

set_option maxHeartbeats 1600000

namespace Work.BMF

/-- Sum of the identity over `range n`, in `ℝ`. -/
private lemma sum_range_cast_id (n : ℕ) :
    ∑ i ∈ Finset.range n, ((i : ℝ)) = (n : ℝ) * ((n : ℝ) - 1) / 2 := by
  induction n with
  | zero => simp
  | succ k ih => rw [Finset.sum_range_succ, ih]; push_cast; ring

/-- Sum of the identity over `Icc B g`, in `ℝ`. -/
private lemma sum_Icc_cast_id (B g : ℕ) (hBg : B ≤ g) :
    ∑ j ∈ Finset.Icc B g, (j : ℝ)
      = ((g + 1 - B : ℕ) : ℝ) * ((B : ℝ) + (g : ℝ)) / 2 := by
  rw [show Finset.Icc B g = Finset.Ico B (g+1) from by
        ext x; simp only [Finset.mem_Icc, Finset.mem_Ico]; omega]
  rw [Finset.sum_Ico_eq_sum_range]
  have hstep : ∀ t : ℕ, (((B + t : ℕ)) : ℝ) = (B : ℝ) + (t : ℝ) := by intro t; push_cast; ring
  simp_rw [hstep]
  rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  rw [sum_range_cast_id]
  have hM : ((g + 1 - B : ℕ) : ℝ) = (g : ℝ) + 1 - (B : ℝ) := by
    push_cast [Nat.cast_sub (by omega : B ≤ g + 1)]; ring
  rw [hM]
  ring

/-- Sum of an affine function over `Icc B g`. -/
private lemma sum_Icc_affine (B g : ℕ) (lam : ℝ) (hBg : B ≤ g) :
    ∑ j ∈ Finset.Icc B g, (lam - (j : ℝ) / 5)
      = ((g + 1 - B : ℕ) : ℝ) * (lam - ((B : ℝ) + (g : ℝ)) / 10) := by
  rw [Finset.sum_sub_distrib, ← Finset.sum_div, sum_Icc_cast_id B g hBg]
  rw [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul]
  have hcard : ((g + 1 - B : ℕ) : ℝ) = (g : ℝ) + 1 - (B : ℝ) := by
    push_cast [Nat.cast_sub (by omega : B ≤ g + 1)]; ring
  rw [hcard]
  ring

theorem vkford_H_lower2 (h g : ℕ) (μ₁ μ₂ lam : ℝ)
    (hlam : 1 ≤ lam) (hh1 : lam ≤ (h : ℝ)) (hh2 : (h : ℝ) ≤ lam + 1)
    (hg1 : 2 * lam + 1 ≤ (g : ℝ)) (hg2 : (g : ℝ) ≤ 6 * lam + 1)
    (hμ₁ : 2 / 5 ≤ μ₁) (hμ₂ : 2 / 5 ≤ μ₂) (hsum : μ₁ + μ₂ ≤ 17 / 20) :
    lam ^ 2 / 10 ≤ ∑ j ∈ Finset.Icc h g,
      min ((j : ℝ) * μ₂) (min ((j : ℝ) - lam) (lam - (j : ℝ) * (1 - μ₁ - μ₂))) := by
  have hc_le : 1 - μ₁ - μ₂ ≤ 1 / 5 := by linarith
  have hc_ge : (3 : ℝ) / 20 ≤ 1 - μ₁ - μ₂ := by linarith
  -- ## Step 1 : pointwise comparison of the summand with the `c = 1/5` summand
  have hpt : ∀ j : ℕ,
      min ((2 : ℝ) / 5 * (j : ℝ)) (min ((j : ℝ) - lam) (lam - (j : ℝ) / 5))
        ≤ min ((j : ℝ) * μ₂) (min ((j : ℝ) - lam) (lam - (j : ℝ) * (1 - μ₁ - μ₂))) := by
    intro j
    have hj : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
    refine min_le_min ?_ (min_le_min le_rfl ?_)
    · nlinarith [hμ₂, hj]
    · nlinarith [hc_le, hj]
  have hstep1 :
      ∑ j ∈ Finset.Icc h g, min ((2 : ℝ) / 5 * (j : ℝ)) (min ((j : ℝ) - lam) (lam - (j : ℝ) / 5))
        ≤ ∑ j ∈ Finset.Icc h g,
            min ((j : ℝ) * μ₂) (min ((j : ℝ) - lam) (lam - (j : ℝ) * (1 - μ₁ - μ₂))) :=
    Finset.sum_le_sum (fun j _ => hpt j)
  -- ## Step 2 : the cutoff `K1 = ⌊5λ/3⌋` and `B = max h (K1+1)`
  set K1 : ℕ := Nat.floor (5 * lam / 3) with hK1def
  have hK1le : (K1 : ℝ) ≤ 5 * lam / 3 := by
    rw [hK1def]; exact Nat.floor_le (by linarith)
  have hK1lt : 5 * lam / 3 < (K1 : ℝ) + 1 := by
    rw [hK1def]; exact Nat.lt_floor_add_one _
  set B : ℕ := max h (K1 + 1) with hBdef
  have hhB : h ≤ B := by rw [hBdef]; exact le_max_left _ _
  have hKB : K1 + 1 ≤ B := by rw [hBdef]; exact le_max_right _ _
  have hBg : B ≤ g := by
    rw [hBdef]
    apply max_le
    · exact_mod_cast (show (h : ℝ) ≤ (g : ℝ) by linarith)
    · have : ((K1 + 1 : ℕ) : ℝ) ≤ (g : ℝ) := by push_cast; linarith
      exact_mod_cast this
  have hside : Finset.Icc B g ⊆ Finset.Icc h g := by
    intro j hj
    rw [Finset.mem_Icc] at hj ⊢
    exact ⟨le_trans hhB hj.1, hj.2⟩
  -- ## Step 3 : the dropped terms `[h, B)` are nonnegative (`T j = j - lam ≥ 0` there)
  have hnonneg : ∀ j ∈ Finset.Icc h g, j ∉ Finset.Icc B g →
      0 ≤ min ((2 : ℝ) / 5 * (j : ℝ)) (min ((j : ℝ) - lam) (lam - (j : ℝ) / 5)) := by
    intro j hj hjB
    rw [Finset.mem_Icc] at hj
    obtain ⟨hhj, hjg⟩ := hj
    have hjB' : j < B := by
      rcases lt_or_ge j B with hlt | hge
      · exact hlt
      · exact absurd (Finset.mem_Icc.mpr ⟨hge, hjg⟩) hjB
    have hjK1 : j ≤ K1 := by
      have hBj : B ≤ K1 + 1 := by
        by_cases hhK : h ≤ K1 + 1
        · rw [hBdef]; exact le_of_eq (max_eq_right hhK)
        · exfalso
          rw [hBdef, max_eq_left (le_of_not_ge hhK)] at hjB'
          omega
      omega
    have hjK1R : (j : ℝ) ≤ (K1 : ℝ) := by exact_mod_cast hjK1
    have hjlam : lam ≤ (j : ℝ) := le_trans hh1 (by exact_mod_cast hhj)
    refine le_min (by positivity) (le_min (by linarith) ?_)
    linarith
  have hstep2 :
      ∑ j ∈ Finset.Icc B g, min ((2 : ℝ) / 5 * (j : ℝ)) (min ((j : ℝ) - lam) (lam - (j : ℝ) / 5))
        ≤ ∑ j ∈ Finset.Icc h g, min ((2 : ℝ) / 5 * (j : ℝ)) (min ((j : ℝ) - lam) (lam - (j : ℝ) / 5)) :=
    Finset.sum_le_sum_of_subset_of_nonneg hside hnonneg
  -- ## Step 4 : on `[B, g]` the summand is exactly `lam - j/5`
  have hcongr :
      ∑ j ∈ Finset.Icc B g, min ((2 : ℝ) / 5 * (j : ℝ)) (min ((j : ℝ) - lam) (lam - (j : ℝ) / 5))
        = ∑ j ∈ Finset.Icc B g, (lam - (j : ℝ) / 5) := by
    apply Finset.sum_congr rfl
    intro j hj
    rw [Finset.mem_Icc] at hj
    obtain ⟨hBj, hjg⟩ := hj
    have hj5 : 5 * lam / 3 < (j : ℝ) := by
      have : ((K1 + 1 : ℕ) : ℝ) ≤ (j : ℝ) := by exact_mod_cast (le_trans hKB hBj)
      push_cast at this
      linarith
    rw [← min_assoc]
    exact min_eq_right (le_min (by linarith) (by linarith))
  -- ## Step 5 : evaluate the sum
  have hP2 := sum_Icc_affine B g lam hBg
  -- ## Step 6 : the arithmetic
  set Bb : ℝ := 5 * lam / 3 + 1 with hBbdef
  have hBBb : (B : ℝ) ≤ Bb := by
    rw [hBbdef, hBdef, Nat.cast_max]
    apply max_le
    · linarith [hh2]
    · push_cast; linarith [hK1le]
  have hgcast : ((g + 1 - B : ℕ) : ℝ) = (g : ℝ) + 1 - (B : ℝ) := by
    push_cast [Nat.cast_sub (by omega : B ≤ g + 1)]; ring
  have keydiff : ((g + 1 - B : ℕ) : ℝ) * (lam - ((B : ℝ) + (g : ℝ)) / 10)
        - ((g : ℝ) + 1 - Bb) * (lam - (Bb + (g : ℝ)) / 10)
      = (Bb - (B : ℝ)) * (10 * lam + 1 - (B : ℝ) - Bb) / 10 := by
    rw [hgcast]; ring
  have hkeynn : 0 ≤ ((g + 1 - B : ℕ) : ℝ) * (lam - ((B : ℝ) + (g : ℝ)) / 10)
        - ((g : ℝ) + 1 - Bb) * (lam - (Bb + (g : ℝ)) / 10) := by
    rw [keydiff]
    apply div_nonneg _ (by norm_num)
    apply mul_nonneg (by linarith [hBBb])
    nlinarith [hBBb, hBbdef, hlam]
  have hfinal : lam ^ 2 / 10 ≤ ((g + 1 - B : ℕ) : ℝ) * (lam - ((B : ℝ) + (g : ℝ)) / 10) := by
    by_cases hle2 : lam ≤ 3 / 2
    · -- small λ : compare with the value at g = 6λ+1
      have hfac : ((g : ℝ) + 1 - Bb) * (lam - (Bb + (g : ℝ)) / 10)
            - ((6 * lam + 1 : ℝ) + 1 - Bb) * (lam - (Bb + (6 * lam + 1 : ℝ)) / 10)
          = ((g : ℝ) - (6 * lam + 1)) * (lam - ((g : ℝ) + (6 * lam + 1) + 1) / 10) := by ring
      have h1 : (g : ℝ) - (6 * lam + 1) ≤ 0 := by linarith [hg2]
      have h2 : lam - ((g : ℝ) + (6 * lam + 1) + 1) / 10 ≤ 0 := by
        have : 4 * lam - 2 ≤ (g : ℝ) := by linarith [hg1, hle2]
        linarith
      have hge : ((6 * lam + 1 : ℝ) + 1 - Bb) * (lam - (Bb + (6 * lam + 1 : ℝ)) / 10)
          ≤ ((g : ℝ) + 1 - Bb) * (lam - (Bb + (g : ℝ)) / 10) := by
        rw [← sub_nonneg, hfac]
        exact mul_nonneg_of_nonpos_of_nonpos h1 h2
      have hE : lam ^ 2 / 10 ≤ ((6 * lam + 1 : ℝ) + 1 - Bb) * (lam - (Bb + (6 * lam + 1 : ℝ)) / 10) := by
        have heq : ((6 * lam + 1 : ℝ) + 1 - Bb) * (lam - (Bb + (6 * lam + 1 : ℝ)) / 10)
            = (13 * lam / 3 + 1) * (7 * lam - 6) / 30 := by rw [hBbdef]; ring
        rw [heq]; nlinarith [hlam]
      linarith [hkeynn, hge, hE]
    · -- large λ : compare with the value at g = 2λ+1
      have hfac : ((g : ℝ) + 1 - Bb) * (lam - (Bb + (g : ℝ)) / 10)
            - ((2 * lam + 1 : ℝ) + 1 - Bb) * (lam - (Bb + (2 * lam + 1 : ℝ)) / 10)
          = ((g : ℝ) - (2 * lam + 1)) * (lam - ((g : ℝ) + (2 * lam + 1) + 1) / 10) := by ring
      have h1 : 0 ≤ (g : ℝ) - (2 * lam + 1) := by linarith [hg1]
      have h2 : 0 ≤ lam - ((g : ℝ) + (2 * lam + 1) + 1) / 10 := by
        have : (g : ℝ) ≤ 8 * lam - 2 := by linarith [hg2, not_le.mp hle2]
        linarith
      have hge : ((2 * lam + 1 : ℝ) + 1 - Bb) * (lam - (Bb + (2 * lam + 1 : ℝ)) / 10)
          ≤ ((g : ℝ) + 1 - Bb) * (lam - (Bb + (g : ℝ)) / 10) := by
        rw [← sub_nonneg, hfac]
        exact mul_nonneg h1 h2
      have hE : lam ^ 2 / 10 ≤ ((2 * lam + 1 : ℝ) + 1 - Bb) * (lam - (Bb + (2 * lam + 1 : ℝ)) / 10) := by
        have heq : ((2 * lam + 1 : ℝ) + 1 - Bb) * (lam - (Bb + (2 * lam + 1 : ℝ)) / 10)
            = (lam / 3 + 1) * (19 * lam - 6) / 30 := by rw [hBbdef]; ring
        rw [heq]; nlinarith [hlam]
      linarith [hkeynn, hge, hE]
  calc lam ^ 2 / 10
      ≤ ((g + 1 - B : ℕ) : ℝ) * (lam - ((B : ℝ) + (g : ℝ)) / 10) := hfinal
    _ = ∑ j ∈ Finset.Icc B g, (lam - (j : ℝ) / 5) := hP2.symm
    _ = ∑ j ∈ Finset.Icc B g, min ((2 : ℝ) / 5 * (j : ℝ)) (min ((j : ℝ) - lam) (lam - (j : ℝ) / 5)) := hcongr.symm
    _ ≤ ∑ j ∈ Finset.Icc h g, min ((2 : ℝ) / 5 * (j : ℝ)) (min ((j : ℝ) - lam) (lam - (j : ℝ) / 5)) := hstep2
    _ ≤ ∑ j ∈ Finset.Icc h g,
          min ((j : ℝ) * μ₂) (min ((j : ℝ) - lam) (lam - (j : ℝ) * (1 - μ₁ - μ₂))) := hstep1

end Work.BMF
