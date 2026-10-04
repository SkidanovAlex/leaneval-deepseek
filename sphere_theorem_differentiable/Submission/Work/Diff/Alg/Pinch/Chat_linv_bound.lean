import Mathlib
import Submission.Work.Diff.Alg.Pinch.ChatDefs
import Submission.Work.Diff.Alg.Pinch.inPIC2_cone_basic
import Submission.Work.Diff.Alg.Pinch.Linv

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.Alg.Pinch



open Finset Submission.Diff.Alg

variable {n : ℕ}

/-! ## Elementary entrywise bounds for the sup norm on `Curv4 n` -/

/-- Each component of `Y : Curv4 n` is bounded by its sup norm. -/
lemma chat_linv_abs_comp (Y : Curv4 n) (a b c d : Fin n) : |Y a b c d| ≤ ‖Y‖ := by
  calc |Y a b c d| = ‖Y a b c d‖ := (Real.norm_eq_abs _).symm
    _ ≤ ‖Y a b c‖ := norm_le_pi_norm (Y a b c) d
    _ ≤ ‖Y a b‖ := norm_le_pi_norm (Y a b) c
    _ ≤ ‖Y a‖ := norm_le_pi_norm (Y a) b
    _ ≤ ‖Y‖ := norm_le_pi_norm Y a

/-- The Ricci tensor is bounded by `n * ‖Y‖` entrywise. -/
lemma chat_linv_abs_ric (Y : Curv4 n) (i j : Fin n) : |ric Y i j| ≤ (n : ℝ) * ‖Y‖ := by
  have h1 : |ric Y i j| ≤ ∑ k : Fin n, |Y k i k j| := by
    rw [ric]; exact Finset.abs_sum_le_sum_abs _ _
  have h2 : (∑ k : Fin n, |Y k i k j|) ≤ ∑ _k : Fin n, ‖Y‖ := by
    apply Finset.sum_le_sum
    intro k _
    calc |Y k i k j| = ‖Y k i k j‖ := (Real.norm_eq_abs _).symm
      _ ≤ ‖Y k i k‖ := norm_le_pi_norm (Y k i k) j
      _ ≤ ‖Y k i‖ := norm_le_pi_norm (Y k i) k
      _ ≤ ‖Y k‖ := norm_le_pi_norm (Y k) i
      _ ≤ ‖Y‖ := norm_le_pi_norm Y k
  have h3 : (∑ _k : Fin n, ‖Y‖) = (n : ℝ) * ‖Y‖ := by
    simp [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  linarith

/-- The scalar curvature is bounded by `n^2 * ‖Y‖`. -/
lemma chat_linv_abs_scalAlg (Y : Curv4 n) : |scalAlg Y| ≤ (n : ℝ) ^ 2 * ‖Y‖ := by
  have h1 : |scalAlg Y| ≤ ∑ i : Fin n, |∑ j : Fin n, Y i j i j| := by
    rw [scalAlg]; exact Finset.abs_sum_le_sum_abs _ _
  have h2 : ∀ i : Fin n, |∑ j : Fin n, Y i j i j| ≤ (n : ℝ) * ‖Y‖ := by
    intro i
    have h3 : |∑ j : Fin n, Y i j i j| ≤ ∑ j : Fin n, |Y i j i j| :=
      Finset.abs_sum_le_sum_abs _ _
    have h4 : (∑ j : Fin n, |Y i j i j|) ≤ ∑ _j : Fin n, ‖Y‖ := by
      apply Finset.sum_le_sum; intro j _
      calc |Y i j i j| = ‖Y i j i j‖ := (Real.norm_eq_abs _).symm
        _ ≤ ‖Y i j i‖ := norm_le_pi_norm (Y i j i) j
        _ ≤ ‖Y i j‖ := norm_le_pi_norm (Y i j) i
        _ ≤ ‖Y i‖ := norm_le_pi_norm (Y i) j
        _ ≤ ‖Y‖ := norm_le_pi_norm Y i
    have h5 : (∑ _j : Fin n, ‖Y‖) = (n : ℝ) * ‖Y‖ := by
      simp [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    linarith
  calc |scalAlg Y| ≤ ∑ i : Fin n, (n : ℝ) * ‖Y‖ := le_trans h1 (Finset.sum_le_sum (fun i _ => h2 i))
    _ = (n : ℝ) * ((n : ℝ) * ‖Y‖) := by simp [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    _ = (n : ℝ) ^ 2 * ‖Y‖ := by ring

/-- The Kronecker delta is bounded by `1`. -/
lemma chat_linv_abs_id2 (i j : Fin n) : |id2 n i j| ≤ 1 := by
  unfold id2; split <;> norm_num

/-- The traceless Ricci tensor is bounded by `2 n * ‖Y‖` entrywise. -/
lemma chat_linv_abs_ric0 (hn : 0 < n) (Y : Curv4 n) (i j : Fin n) :
    |ric0 Y i j| ≤ 2 * (n : ℝ) * ‖Y‖ := by
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hscal := chat_linv_abs_scalAlg Y
  have hid := chat_linv_abs_id2 (n := n) i j
  have h2 : |(scalAlg Y / (n : ℝ)) * id2 n i j| ≤ (n : ℝ) * ‖Y‖ := by
    rw [abs_mul]
    have hq : |scalAlg Y / (n : ℝ)| ≤ (n : ℝ) * ‖Y‖ := by
      rw [abs_div, abs_of_pos hnR, div_le_iff₀ hnR]
      nlinarith [hscal]
    calc |scalAlg Y / (n : ℝ)| * |id2 n i j| ≤ ((n : ℝ) * ‖Y‖) * 1 :=
          mul_le_mul hq hid (abs_nonneg _) (by positivity)
      _ = (n : ℝ) * ‖Y‖ := by ring
  have htri : |ric Y i j - (scalAlg Y / (n : ℝ)) * id2 n i j|
      ≤ |ric Y i j| + |(scalAlg Y / (n : ℝ)) * id2 n i j| := by
    have := abs_add_le (ric Y i j) (-((scalAlg Y / (n : ℝ)) * id2 n i j))
    rw [abs_neg] at this
    simpa [sub_eq_add_neg] using this
  rw [ric0]
  linarith [htri, chat_linv_abs_ric Y i j, h2]

/-- Four-term triangle inequality for the real numbers. -/
lemma chat_linv_abs4 (a b c d : ℝ) : |a - b - c + d| ≤ |a| + |b| + |c| + |d| := by
  have hsub : ∀ x y : ℝ, |x - y| ≤ |x| + |y| := by
    intro x y
    have := abs_add_le x (-y)
    rw [abs_neg] at this
    simpa [sub_eq_add_neg] using this
  have h1 : |a - b - c + d| ≤ |a - b - c| + |d| := abs_add_le (a - b - c) d
  have h2 : |a - b - c| ≤ |a - b| + |c| := hsub (a - b) c
  have h3 : |a - b| ≤ |a| + |b| := hsub a b
  linarith

/-- Componentwise bound for `knProd (ric0 Y) (id2 n)`. -/
lemma chat_linv_abs_knProd_ric0_id2 (hn : 0 < n) (Y : Curv4 n) (i j k l : Fin n) :
    |knProd (ric0 Y) (id2 n) i j k l| ≤ 8 * (n : ℝ) * ‖Y‖ := by
  have hb : ∀ p q r s : Fin n, |ric0 Y p q * id2 n r s| ≤ 2 * (n : ℝ) * ‖Y‖ := by
    intro p q r s
    rw [abs_mul]
    calc |ric0 Y p q| * |id2 n r s| ≤ (2 * (n : ℝ) * ‖Y‖) * 1 :=
          mul_le_mul (chat_linv_abs_ric0 hn Y p q) (chat_linv_abs_id2 (n := n) r s)
            (abs_nonneg _) (by positivity)
      _ = 2 * (n : ℝ) * ‖Y‖ := by ring
  rw [knProd]
  have h4 := chat_linv_abs4 (ric0 Y i k * id2 n j l) (ric0 Y i l * id2 n j k)
      (ric0 Y j k * id2 n i l) (ric0 Y j l * id2 n i k)
  nlinarith [h4, hb i k j l, hb i l j k, hb j k i l, hb j l i k]

/-- Componentwise bound for `knProd (id2 n) (id2 n)`. -/
lemma chat_linv_abs_knProd_id2_id2 (i j k l : Fin n) :
    |knProd (id2 n) (id2 n) i j k l| ≤ 4 := by
  have hb : ∀ p q r s : Fin n, |id2 n p q * id2 n r s| ≤ 1 := by
    intro p q r s
    rw [abs_mul]
    calc |id2 n p q| * |id2 n r s| ≤ 1 * 1 :=
          mul_le_mul (chat_linv_abs_id2 (n := n) p q) (chat_linv_abs_id2 (n := n) r s)
            (abs_nonneg _) (by norm_num)
      _ = 1 := by ring
  rw [knProd]
  have h4 := chat_linv_abs4 (id2 n i k * id2 n j l) (id2 n i l * id2 n j k)
      (id2 n j k * id2 n i l) (id2 n j l * id2 n i k)
  nlinarith [h4, hb i k j l, hb i l j k, hb j k i l, hb j l i k]

/-- `|x - y| ≤ |x| + |y|` for the real numbers. -/
lemma chat_linv_abs_sub (x y : ℝ) : |x - y| ≤ |x| + |y| := by
  have := abs_add_le x (-y)
  rw [abs_neg] at this
  simpa [sub_eq_add_neg] using this

/-- Componentwise expansion of `linv a b Y - Y` straight from the definition. -/
lemma chat_linv_sub_expand {n : ℕ} (a b : ℝ) (Y : Curv4 n) (i j k l : Fin n) :
    (linv a b Y - Y) i j k l
      = -(b / (1 + ((n : ℝ) - 2) * b)) * knProd (ric0 Y) (id2 n) i j k l
        - ((a / (n : ℝ)) / (1 + 2 * ((n : ℝ) - 1) * a) * scalAlg Y)
            * knProd (id2 n) (id2 n) i j k l := by
  simp only [linv, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  ring

/-- The Böhm–Wilking transform `linv (chatA n s) s` (the inverse of `ell (chatA n s) s`, the `0 < s ≤ 1/2` branch of the Brendle–Schoen family) is `O(s)`-close to the identity, with an explicit constant, componentwise:

`|(linv (chatA n s) s Y - Y) i j k l| ≤ (8 * n^2 + 16) * s * ‖Y‖` for `n ≥ 2`, `0 < s ≤ 1/2`.

Route: `linv a b Y - Y = -(b/(1+(n-2)b)) • knProd (ric0 Y) (id2 n) - (((a/n)/(1+2(n-1)a)) * scalAlg Y) • knProd (id2 n) (id2 n)` directly from the definition (`Diff/Alg/Pinch/Linv`), so it suffices to bound the two summands componentwise, using `|b/(1+(n-2)b)| ≤ b ≤ s` for `b = s > 0`, `n ≥ 2`; `chatA n s ≥ 0` and `chatA n s ≤ s * (1 + (n-2)/4)` (`chatA_nonneg`, `chatA_le` of `Diff/Alg/Pinch/ChatDefs`) so that `(chatA n s)/(1 + 2(n-1) chatA n s) ≤ chatA n s`; `|ric0 Y i j| ≤ 2 n ‖Y‖` (from `|Y i j k l| ≤ ‖Y‖`, which holds for the sup norm on `Curv4 n`), `|knProd (ric0 Y) (id2 n) i j k l| ≤ 4 * maxᵢⱼ |ric0 Y i j|` (four terms, each a product of one entry of `ric0 Y` and one Kronecker delta), `|scalAlg Y| ≤ n^2 ‖Y‖`, `|knProd (id2 n) (id2 n) i j k l| ≤ 4`.  Summing, the constant `8 n^2 + 16` dominates `n^2 + 10 n`. -/
theorem Chat_linv_bound {n : ℕ} (hn : 2 ≤ n) {s : ℝ} (hs : 0 < s) (hs2 : s ≤ 1 / 2)
    (Y : Submission.Diff.Alg.Curv4 n) (i j k l : Fin n) :
    |(Work.Diff.Alg.Pinch.linv (Work.Diff.Alg.Pinch.chatA n s) s Y - Y) i j k l|
      ≤ (8 * (n : ℝ) ^ 2 + 16) * s * ‖Y‖ := by
  have hn0 : 0 < n := by omega
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn0
  have hn2R : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hYnn : (0 : ℝ) ≤ ‖Y‖ := norm_nonneg Y
  have hAnn : (0 : ℝ) ≤ chatA n s := chatA_nonneg hn hs.le
  have hcn : (0 : ℝ) ≤ 2 * ((n : ℝ) - 1) := by linarith
  have hAden : (0 : ℝ) < 1 + 2 * ((n : ℝ) - 1) * chatA n s := by
    have := mul_nonneg hcn hAnn; linarith
  have hAle := chatA_le hn hs hs2
  -- entry bounds
  have hK1 : |knProd (ric0 Y) (id2 n) i j k l| ≤ 8 * (n : ℝ) * ‖Y‖ :=
    chat_linv_abs_knProd_ric0_id2 hn0 Y i j k l
  have hK2 : |knProd (id2 n) (id2 n) i j k l| ≤ 4 := chat_linv_abs_knProd_id2_id2 i j k l
  -- the factor `s/(1+(n-2)s)`
  have hc1 : |s / (1 + ((n : ℝ) - 2) * s)| ≤ s := by
    have hcn2 : (0 : ℝ) ≤ ((n : ℝ) - 2) := by linarith
    have hden : (0 : ℝ) < 1 + ((n : ℝ) - 2) * s := by
      have := mul_nonneg hcn2 hs.le; linarith
    rw [abs_of_nonneg (div_nonneg hs.le hden.le), div_le_iff₀ hden]
    nlinarith [mul_nonneg (mul_nonneg hcn2 hs.le) hs.le]
  -- the factor `(chatA n s / n)/(1+2(n-1)chatA n s) * scalAlg Y`
  have hq0 : (0 : ℝ) ≤ chatA n s / (n : ℝ) := div_nonneg hAnn hnR.le
  have hc2 : |(chatA n s / (n : ℝ)) / (1 + 2 * ((n : ℝ) - 1) * chatA n s) * scalAlg Y|
      ≤ chatA n s * (n : ℝ) * ‖Y‖ := by
    rw [abs_mul]
    have hq : |(chatA n s / (n : ℝ)) / (1 + 2 * ((n : ℝ) - 1) * chatA n s)| ≤ chatA n s / (n : ℝ) := by
      rw [abs_of_nonneg (div_nonneg hq0 hAden.le), div_le_iff₀ hAden]
      nlinarith [mul_nonneg hq0 (mul_nonneg hcn hAnn)]
    calc |(chatA n s / (n : ℝ)) / (1 + 2 * ((n : ℝ) - 1) * chatA n s)| * |scalAlg Y|
          ≤ (chatA n s / (n : ℝ)) * ((n : ℝ) ^ 2 * ‖Y‖) :=
          mul_le_mul hq (chat_linv_abs_scalAlg Y) (abs_nonneg _) hq0
      _ = chatA n s * (n : ℝ) * ‖Y‖ := by field_simp
  -- the two summands
  have hb1 : |-(s / (1 + ((n : ℝ) - 2) * s)) * knProd (ric0 Y) (id2 n) i j k l|
      ≤ s * (8 * (n : ℝ) * ‖Y‖) := by
    rw [abs_mul, abs_neg]
    exact mul_le_mul hc1 hK1 (abs_nonneg _) hs.le
  have hb2 : |((chatA n s / (n : ℝ)) / (1 + 2 * ((n : ℝ) - 1) * chatA n s) * scalAlg Y)
        * knProd (id2 n) (id2 n) i j k l|
      ≤ s * ((n : ℝ) ^ 2 + 2 * (n : ℝ)) * ‖Y‖ := by
    rw [abs_mul]
    have h4 : |(chatA n s / (n : ℝ)) / (1 + 2 * ((n : ℝ) - 1) * chatA n s) * scalAlg Y|
          * |knProd (id2 n) (id2 n) i j k l| ≤ (chatA n s * (n : ℝ) * ‖Y‖) * 4 :=
      mul_le_mul hc2 hK2 (abs_nonneg _) (by positivity)
    have h5 : (chatA n s * (n : ℝ) * ‖Y‖) * 4
        ≤ (s * (1 + ((n : ℝ) - 2) / 4) * (n : ℝ) * ‖Y‖) * 4 := by
      apply mul_le_mul_of_nonneg_right
      · apply mul_le_mul_of_nonneg_right
        · apply mul_le_mul_of_nonneg_right hAle
          positivity
        · exact norm_nonneg Y
      · norm_num
    calc |(chatA n s / (n : ℝ)) / (1 + 2 * ((n : ℝ) - 1) * chatA n s) * scalAlg Y|
          * |knProd (id2 n) (id2 n) i j k l| ≤ (chatA n s * (n : ℝ) * ‖Y‖) * 4 := h4
      _ ≤ (s * (1 + ((n : ℝ) - 2) / 4) * (n : ℝ) * ‖Y‖) * 4 := h5
      _ = s * ((n : ℝ) ^ 2 + 2 * (n : ℝ)) * ‖Y‖ := by ring
  -- assembly
  have hfinal : s * ((n : ℝ) ^ 2 + 2 * (n : ℝ)) * ‖Y‖ + s * (8 * (n : ℝ) * ‖Y‖)
      ≤ (8 * (n : ℝ) ^ 2 + 16) * s * ‖Y‖ := by
    have h1 : (n : ℝ) ^ 2 + 10 * (n : ℝ) ≤ 8 * (n : ℝ) ^ 2 + 16 := by
      nlinarith [sq_nonneg (7 * (n : ℝ) - 5)]
    have ht : (0 : ℝ) ≤ s * ‖Y‖ := mul_nonneg hs.le hYnn
    have := mul_le_mul_of_nonneg_left h1 ht
    nlinarith [this]
  rw [chat_linv_sub_expand]
  have htri : |-(s / (1 + ((n : ℝ) - 2) * s)) * knProd (ric0 Y) (id2 n) i j k l
      - ((chatA n s / (n : ℝ)) / (1 + 2 * ((n : ℝ) - 1) * chatA n s) * scalAlg Y)
          * knProd (id2 n) (id2 n) i j k l|
      ≤ |-(s / (1 + ((n : ℝ) - 2) * s)) * knProd (ric0 Y) (id2 n) i j k l|
        + |((chatA n s / (n : ℝ)) / (1 + 2 * ((n : ℝ) - 1) * chatA n s) * scalAlg Y)
          * knProd (id2 n) (id2 n) i j k l| := chat_linv_abs_sub _ _
  linarith [htri, hb1, hb2, hfinal]

end Work.Diff.Alg.Pinch
