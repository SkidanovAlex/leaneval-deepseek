import Mathlib
import Submission.Work.BMF.Defs
import Submission.Work.BMF.discretise

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BMF

open Classical Polynomial Finset Real Complex
open BoundedMultiplicativeFunctions

/-! ## Telescoping a sum over a chain of integer intervals -/

lemma sum_Ico_eq_sum_range_Ico {α : Type*} [AddCommMonoid α] (f : ℤ → α) (c : ℕ → ℤ)
    (hmono : Monotone c) (M : ℕ) :
    ∑ n ∈ Finset.Ico (c 0) (c M), f n
      = ∑ j ∈ Finset.range M, ∑ n ∈ Finset.Ico (c j) (c (j+1)), f n := by
  induction M with
  | zero => simp
  | succ M ih =>
    rw [Finset.sum_range_succ, ← ih,
      ← Finset.sum_union (Finset.Ico_disjoint_Ico_consecutive _ _ _),
      Finset.Ico_union_Ico_eq_Ico (hmono (Nat.zero_le M)) (hmono (Nat.le_succ M))]

lemma Icc_eq_Ico_succ (a b : ℤ) : Finset.Icc a b = Finset.Ico a (b+1) := by
  ext n; simp only [Finset.mem_Icc, Finset.mem_Ico]; omega

lemma Ico_eq_Icc_pred (a b : ℤ) : Finset.Ico a b = Finset.Icc a (b-1) := by
  ext n; simp only [Finset.mem_Icc, Finset.mem_Ico]; omega

lemma Icc_split (p q r : ℤ) (hpq : p ≤ q) (hqr : q ≤ r + 1) :
    Finset.Icc p r = Finset.Icc p (q-1) ∪ Finset.Icc q r := by
  ext n; simp only [Finset.mem_Icc, Finset.mem_union]; omega

lemma card_Icc_le_one_real (q r : ℤ) (h : r ≤ q) : ((Finset.Icc q r).card : ℝ) ≤ 1 := by
  by_cases hqr : q ≤ r
  · have : r = q := le_antisymm h hqr
    subst this; simp
  · have : Finset.Icc q r = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro n hn; simp only [Finset.mem_Icc] at hn; omega
    rw [this]; simp

lemma card_Ico_le_real (p q : ℤ) (c : ℝ) (h : ((q - p : ℤ) : ℝ) ≤ c) (hc : 0 ≤ c) :
    ((Finset.Ico p q).card : ℝ) ≤ c := by
  rw [Int.card_Ico]
  by_cases hk : 0 ≤ q - p
  · rw [show (((q-p).toNat : ℕ) : ℝ) = ((q-p : ℤ) : ℝ) from by
      exact_mod_cast (Int.toNat_of_nonneg hk)]
    exact h
  · rw [Int.toNat_eq_zero.mpr (by omega)]; simp; exact hc

lemma norm_sum_le_card_real (f : ℤ → ℂ) (hf : ∀ n, ‖f n‖ ≤ 1) (s : Finset ℤ) :
    ‖∑ n ∈ s, f n‖ ≤ (s.card : ℝ) := by
  calc ‖∑ n ∈ s, f n‖ ≤ ∑ n ∈ s, ‖f n‖ := norm_sum_le _ _
    _ ≤ ∑ n ∈ s, (1:ℝ) := by
        apply Finset.sum_le_sum; intro n _; exact hf n
    _ = (s.card : ℝ) := by simp

/-! ## The core block decomposition -/

/-- Splitting a sum over `[⌈x⌉, ⌊x+H⌋]` into `m` block sums over the intervals
`[⌈x+jH'⌉, ⌊x+jH'+H'⌋]`, up to an error `m + H' + 2`. -/
lemma core_le_blocks (f : ℤ → ℂ) (hf : ∀ n, ‖f n‖ ≤ 1) (x H H' : ℝ) (hH : 0 < H)
    (hH' : 0 < H') (m : ℕ) (hm : H < (m:ℝ)*H') (hm₂ : (m:ℝ)*H' ≤ H + H') :
    ‖∑ n ∈ Finset.Icc ⌈x⌉ ⌊x+H⌋, f n‖ ≤
      ∑ j ∈ Finset.range m, ‖∑ n ∈ Finset.Icc ⌈x + (j:ℝ)*H'⌉ ⌊x + (j:ℝ)*H' + H'⌋, f n‖
      + ((m:ℝ) + H' + 2) := by
  set A : ℤ := ⌈x⌉ with hAdef
  set B : ℤ := ⌊x+H⌋ with hBdef
  set a : ℕ → ℤ := fun j => ⌈x + (j:ℝ)*H'⌉ with hadef
  set b : ℕ → ℤ := fun j => ⌊x + (j:ℝ)*H' + H'⌋ with hbdef
  have ha0 : a 0 = A := by simp [hadef, hAdef]
  have hmono : Monotone a := by
    intro i j hij
    simp only [hadef]
    apply Int.ceil_mono
    have h1 : (i:ℝ) ≤ (j:ℝ) := by exact_mod_cast hij
    have h2 : (i:ℝ)*H' ≤ (j:ℝ)*H' := mul_le_mul_of_nonneg_right h1 (le_of_lt hH')
    linarith
  have hB1 : B + 1 ≤ a m := by
    simp only [hBdef, hadef]
    have h : ((⌊x+H⌋ : ℤ) : ℝ) < x + (m:ℝ)*H' := by
      have h1 : ((⌊x+H⌋ : ℤ) : ℝ) ≤ x + H := Int.floor_le _
      have h2 : x + H < x + (m:ℝ)*H' := by linarith
      linarith
    have h3 := (Int.lt_ceil (z := ⌊x+H⌋) (a := x + (m:ℝ)*H')).mpr h
    omega
  have hAleB1 : A ≤ B + 1 := by
    simp only [hAdef, hBdef]
    have h : ((⌈x⌉ - 1 : ℤ) : ℝ) ≤ x + H := by
      have h1 := Int.ceil_lt_add_one x
      have h1' : ((⌈x⌉ : ℤ) : ℝ) < x + 1 := h1
      push_cast; linarith
    have h2 := (Int.le_floor (z := ⌈x⌉ - 1) (a := x + H)).mpr h
    omega
  have hnc : ∀ s : Finset ℤ, ‖∑ n ∈ s, f n‖ ≤ (s.card : ℝ) := norm_sum_le_card_real f hf
  have htel := sum_Ico_eq_sum_range_Ico f a hmono m
  have htel' : ∑ n ∈ Finset.Ico A (a m), f n
      = ∑ j ∈ Finset.range m, ∑ n ∈ Finset.Ico (a j) (a (j+1)), f n := by
    rw [← ha0]; exact htel
  have hsplit : ∑ n ∈ Finset.Ico A (a m), f n
      = ∑ n ∈ Finset.Ico A (B+1), f n + ∑ n ∈ Finset.Ico (B+1) (a m), f n := by
    rw [← Finset.sum_union (Finset.Ico_disjoint_Ico_consecutive A (B+1) (a m)),
      Finset.Ico_union_Ico_eq_Ico hAleB1 hB1]
  have htop : ∑ n ∈ Finset.Icc A B, f n = ∑ n ∈ Finset.Ico A (B+1), f n := by
    have : Finset.Icc A B = Finset.Ico A (B+1) := by
      ext n; simp only [Finset.mem_Icc, Finset.mem_Ico]; omega
    rw [this]
  have hZ : ‖∑ n ∈ Finset.Ico (B+1) (a m), f n‖ ≤ H' + 1 := by
    refine le_trans (hnc _) ?_
    refine card_Ico_le_real (B+1) (a m) (H'+1) ?_ (by linarith)
    rw [hadef, hBdef]
    have hfloor : x + H - 1 < ((⌊x+H⌋ : ℤ) : ℝ) := by
      have h := (Int.floor_lt (a := x+H) (z := ⌊x+H⌋ + 1)).mp (by omega : ⌊x+H⌋ < ⌊x+H⌋ + 1)
      push_cast at h; linarith
    have hceil : ((⌈x + (m:ℝ)*H'⌉ : ℤ) : ℝ) < x + (m:ℝ)*H' + 1 := Int.ceil_lt_add_one _
    push_cast
    linarith
  have hblock : ∀ j, ‖∑ n ∈ Finset.Ico (a j) (a (j+1)), f n‖
      ≤ ‖∑ n ∈ Finset.Icc (a j) (b j), f n‖ + 1 := by
    intro j
    have hle : a j ≤ a (j+1) := hmono (Nat.le_succ j)
    have hb_le : b j ≤ a (j+1) := by
      simp only [hbdef, hadef]
      have h2 : x + (j:ℝ)*H' + H' = x + ((j+1 : ℕ) : ℝ)*H' := by push_cast; ring
      rw [h2]
      exact Int.floor_le_ceil _
    have ha_le_b : a (j+1) - 1 ≤ b j := by
      have h := Int.ceil_le_floor_add_one (x + (j:ℝ)*H' + H')
      have h2 : x + (j:ℝ)*H' + H' = x + ((j+1 : ℕ) : ℝ)*H' := by push_cast; ring
      rw [h2] at h
      simp only [hbdef, hadef]
      rw [h2]
      linarith
    have hsum : ∑ n ∈ Finset.Icc (a j) (b j), f n
        = ∑ n ∈ Finset.Ico (a j) (a (j+1)), f n + ∑ n ∈ Finset.Icc (a (j+1)) (b j), f n := by
      rw [Icc_split (a j) (a (j+1)) (b j) hle (by omega), Finset.sum_union, Ico_eq_Icc_pred]
      rw [Finset.disjoint_left]
      intro n hn1 hn2
      simp only [Finset.mem_Icc] at hn1 hn2
      omega
    have heq : ∑ n ∈ Finset.Ico (a j) (a (j+1)), f n
        = ∑ n ∈ Finset.Icc (a j) (b j), f n - ∑ n ∈ Finset.Icc (a (j+1)) (b j), f n := by
      rw [hsum]; ring
    rw [heq]
    calc ‖∑ n ∈ Finset.Icc (a j) (b j), f n - ∑ n ∈ Finset.Icc (a (j+1)) (b j), f n‖
        ≤ ‖∑ n ∈ Finset.Icc (a j) (b j), f n‖ + ‖∑ n ∈ Finset.Icc (a (j+1)) (b j), f n‖ :=
          norm_sub_le _ _
      _ ≤ ‖∑ n ∈ Finset.Icc (a j) (b j), f n‖ + 1 := by
          have h2 : ‖∑ n ∈ Finset.Icc (a (j+1)) (b j), f n‖ ≤ 1 :=
            le_trans (hnc _) (card_Icc_le_one_real _ _ hb_le)
          linarith
  have hmain : ‖∑ n ∈ Finset.Icc A B, f n‖ ≤
      ∑ j ∈ Finset.range m, ‖∑ n ∈ Finset.Icc (a j) (b j), f n‖ + ((m:ℝ) + H' + 2) := by
    rw [htop]
    have heq1 : ∑ n ∈ Finset.Ico A (B+1), f n
        = ∑ n ∈ Finset.Ico A (a m), f n - ∑ n ∈ Finset.Ico (B+1) (a m), f n := by
      rw [hsplit]; ring
    calc ‖∑ n ∈ Finset.Ico A (B+1), f n‖
        = ‖∑ n ∈ Finset.Ico A (a m), f n - ∑ n ∈ Finset.Ico (B+1) (a m), f n‖ := by rw [heq1]
      _ ≤ ‖∑ n ∈ Finset.Ico A (a m), f n‖ + ‖∑ n ∈ Finset.Ico (B+1) (a m), f n‖ :=
            norm_sub_le _ _
      _ = ‖∑ j ∈ Finset.range m, ∑ n ∈ Finset.Ico (a j) (a (j+1)), f n‖
            + ‖∑ n ∈ Finset.Ico (B+1) (a m), f n‖ := by rw [htel']
      _ ≤ (∑ j ∈ Finset.range m, ‖∑ n ∈ Finset.Ico (a j) (a (j+1)), f n‖)
            + ‖∑ n ∈ Finset.Ico (B+1) (a m), f n‖ := by
          have h1 := norm_sum_le (Finset.range m)
            (fun j => ∑ n ∈ Finset.Ico (a j) (a (j+1)), f n)
          have h2 : (0:ℝ) ≤ ‖∑ n ∈ Finset.Ico (B+1) (a m), f n‖ := norm_nonneg _
          linarith
      _ ≤ (∑ j ∈ Finset.range m, (‖∑ n ∈ Finset.Icc (a j) (b j), f n‖ + 1)) + (H' + 1) := by
          have h1 : ∑ j ∈ Finset.range m, ‖∑ n ∈ Finset.Ico (a j) (a (j+1)), f n‖
              ≤ ∑ j ∈ Finset.range m, (‖∑ n ∈ Finset.Icc (a j) (b j), f n‖ + 1) :=
            Finset.sum_le_sum (fun j _ => hblock j)
          linarith
      _ = (∑ j ∈ Finset.range m, ‖∑ n ∈ Finset.Icc (a j) (b j), f n‖) + (m:ℝ) + (H' + 1) := by
          rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
          push_cast; ring
      _ ≤ (∑ j ∈ Finset.range m, ‖∑ n ∈ Finset.Icc (a j) (b j), f n‖) + ((m:ℝ) + H' + 2) := by
          linarith
  exact hmain



/-! ## The block-sum bound for the weak Gowers norm -/

theorem wgun_block_sum (k : ℕ) (g : ℤ → ℂ) (hg : ∀ n, ‖g n‖ ≤ 1) (x H H' : ℝ)
    (hH : 0 < H) (hH' : 0 < H') (m : ℕ) (hm : H < (m : ℝ) * H')
    (hm₂ : (m : ℝ) * H' ≤ H + H') :
    BoundedMultiplicativeFunctions.weakGowersUniformityNorm k x H g ≤
      (H' / H) * ∑ j ∈ Finset.range m,
        BoundedMultiplicativeFunctions.weakGowersUniformityNorm k (x + (j : ℝ) * H') H' g
      + ((m : ℝ) + H' + 2) / H := by
  have hL : weakGowersUniformityNorm k x H g
      = ⨆ P ∈ degreeLE ℝ (k : WithBot ℕ),
          1/H * ‖∑ n ∈ Finset.Icc ⌈x⌉ ⌊x+H⌋, g n * cexp (2 * π * I * -P.eval (n:ℝ))‖ := rfl
  rw [hL]
  apply iSup_Poly_le
  · have hS : 0 ≤ ∑ j ∈ Finset.range m,
        weakGowersUniformityNorm k (x + (j:ℝ)*H') H' g :=
      Finset.sum_nonneg (fun j _ => weakGowers_nonneg k H' hH' g hg _)
    have h1 : 0 ≤ H' / H := div_nonneg (le_of_lt hH') (le_of_lt hH)
    have h2 : 0 ≤ ((m:ℝ) + H' + 2) / H := by positivity
    exact add_nonneg (mul_nonneg h1 hS) h2
  · intro P hP
    have hf : ∀ n, ‖g n * cexp (2 * π * I * -P.eval (n:ℝ))‖ ≤ 1 := by
      intro n
      rw [norm_mul]
      have h1 : ‖cexp (2 * π * I * -P.eval (n:ℝ))‖ = 1 := by
        rw [Complex.norm_exp]
        have h2 : (2 * (π:ℂ) * I * -(P.eval (n:ℝ))).re = 0 := by
          simp [Complex.mul_re, Complex.mul_im]
        rw [h2, Real.exp_zero]
      rw [h1, mul_one]
      exact hg n
    have hcore := core_le_blocks (fun n => g n * cexp (2 * π * I * -P.eval (n:ℝ)))
      hf x H H' hH hH' m hm hm₂
    have hblock : ∀ j : ℕ, ‖∑ n ∈ Finset.Icc ⌈x + (j:ℝ)*H'⌉ ⌊x + (j:ℝ)*H' + H'⌋,
          g n * cexp (2 * π * I * -P.eval (n:ℝ))‖
        ≤ H' * weakGowersUniformityNorm k (x + (j:ℝ)*H') H' g := by
      intro j
      have hv : (1/H') * ‖∑ n ∈ Finset.Icc ⌈x + (j:ℝ)*H'⌉ ⌊x + (j:ℝ)*H' + H'⌋,
            g n * cexp (2 * π * I * -P.eval (n:ℝ))‖
          ≤ weakGowersUniformityNorm k (x + (j:ℝ)*H') H' g := by
        rw [weakGowersUniformityNorm]
        refine le_iSup_Poly (v := fun Q : ℝ[X] => 1/H' * ‖∑ n ∈ Finset.Icc ⌈x + (j:ℝ)*H'⌉
            ⌊x + (j:ℝ)*H' + H'⌋, g n * cexp (2 * π * I * -Q.eval (n:ℝ))‖)
          (c := (H'+2)/H') (by positivity) ?_ P hP
        intro Q hQ
        calc 1/H' * ‖∑ n ∈ Finset.Icc ⌈x + (j:ℝ)*H'⌉ ⌊x + (j:ℝ)*H' + H'⌋,
                g n * cexp (2 * π * I * -Q.eval (n:ℝ))‖
            ≤ 1/H' * ((Finset.Icc ⌈x + (j:ℝ)*H'⌉ ⌊x + (j:ℝ)*H' + H'⌋).card : ℝ) :=
              mul_le_mul_of_nonneg_left (norm_sum_cexp_le_card g hg Q _ _) (by positivity)
          _ ≤ 1/H' * (H' + 2) :=
              mul_le_mul_of_nonneg_left (card_Icc_ceil_floor_le _ H' (le_of_lt hH')) (by positivity)
          _ = (H'+2)/H' := by ring
      calc ‖∑ n ∈ Finset.Icc ⌈x + (j:ℝ)*H'⌉ ⌊x + (j:ℝ)*H' + H'⌋,
              g n * cexp (2 * π * I * -P.eval (n:ℝ))‖
          = H' * ((1/H') * ‖∑ n ∈ Finset.Icc ⌈x + (j:ℝ)*H'⌉ ⌊x + (j:ℝ)*H' + H'⌋,
              g n * cexp (2 * π * I * -P.eval (n:ℝ))‖) := by
            rw [← mul_assoc, one_div, mul_inv_cancel₀ (ne_of_gt hH'), one_mul]
        _ ≤ H' * weakGowersUniformityNorm k (x + (j:ℝ)*H') H' g :=
            mul_le_mul_of_nonneg_left hv (le_of_lt hH')
    have hstep : ∑ j ∈ Finset.range m, ‖∑ n ∈ Finset.Icc ⌈x + (j:ℝ)*H'⌉
            ⌊x + (j:ℝ)*H' + H'⌋, g n * cexp (2 * π * I * -P.eval (n:ℝ))‖
        ≤ ∑ j ∈ Finset.range m, H' * weakGowersUniformityNorm k (x + (j:ℝ)*H') H' g :=
      Finset.sum_le_sum (fun j _ => hblock j)
    calc 1/H * ‖∑ n ∈ Finset.Icc ⌈x⌉ ⌊x+H⌋, g n * cexp (2 * π * I * -P.eval (n:ℝ))‖
        ≤ 1/H * (∑ j ∈ Finset.range m, ‖∑ n ∈ Finset.Icc ⌈x + (j:ℝ)*H'⌉
              ⌊x + (j:ℝ)*H' + H'⌋, g n * cexp (2 * π * I * -P.eval (n:ℝ))‖
              + ((m:ℝ) + H' + 2)) :=
          mul_le_mul_of_nonneg_left hcore (by positivity)
      _ ≤ 1/H * (∑ j ∈ Finset.range m, H' * weakGowersUniformityNorm k (x + (j:ℝ)*H') H' g
              + ((m:ℝ) + H' + 2)) :=
          mul_le_mul_of_nonneg_left (add_le_add hstep le_rfl) (by positivity)
      _ = (H' / H) * ∑ j ∈ Finset.range m,
            weakGowersUniformityNorm k (x + (j:ℝ)*H') H' g
          + ((m:ℝ) + H' + 2) / H := by
          rw [← Finset.mul_sum]; ring

end Work.BMF
