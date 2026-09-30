import Mathlib.Analysis.SpecialFunctions.Pow.Real

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

set_option linter.unusedVariables false

namespace Commons.Analysis.Convolution

/-- Purely numerical core: if `0 < b ≤ 2 a` then `a ^ (-A) ≤ 2 ^ A * b ^ (-A)`. -/
lemma rpow_neg_le_of_le_two_mul {A a b : ℝ} (hA : 0 < A) (ha : 0 < a) (hb : 0 < b)
    (h : b ≤ 2 * a) : a ^ (-A) ≤ 2 ^ A * b ^ (-A) := by
  have haA : 0 < a ^ A := Real.rpow_pos_of_pos ha A
  have hbA : 0 < b ^ A := Real.rpow_pos_of_pos hb A
  have hba : b ^ A ≤ 2 ^ A * a ^ A := by
    have h1 : b ^ A ≤ (2 * a) ^ A := Real.rpow_le_rpow (le_of_lt hb) h (le_of_lt hA)
    have h2 : (2 * a) ^ A = 2 ^ A * a ^ A := Real.mul_rpow (by norm_num) (le_of_lt ha)
    rwa [h2] at h1
  rw [Real.rpow_neg (le_of_lt ha), Real.rpow_neg (le_of_lt hb)]
  rw [inv_eq_one_div, ← div_eq_mul_inv]
  rw [div_le_div_iff₀ haA hbA]
  simpa using hba

theorem itent_comparison (k : ℕ) (hk : 1 ≤ k) {A δ : ℝ} (hA : 0 < A) (hδ : 0 < δ)
    (x y z : Fin k → ℝ) (h : ∀ i : Fin k, |δ ^ (i.val + 1) * (x i - y i)| ≤ 1) :
    (max 1 ((Finset.univ : Finset (Fin k)).sup' ⟨⟨0, hk⟩, Finset.mem_univ _⟩
        fun i => |δ ^ (i.val + 1) * (x - z) i|)) ^ (-A)
      ≤ 2 ^ A * (max 1 ((Finset.univ : Finset (Fin k)).sup' ⟨⟨0, hk⟩, Finset.mem_univ _⟩
        fun i => |δ ^ (i.val + 1) * (y - z) i|)) ^ (-A) := by
  set sx : ℝ := (Finset.univ : Finset (Fin k)).sup' ⟨⟨0, hk⟩, Finset.mem_univ _⟩
      fun i => |δ ^ (i.val + 1) * (x - z) i| with hsx
  set sy : ℝ := (Finset.univ : Finset (Fin k)).sup' ⟨⟨0, hk⟩, Finset.mem_univ _⟩
      fun i => |δ ^ (i.val + 1) * (y - z) i| with hsy
  have hPpos : 0 < max 1 sx := lt_of_lt_of_le one_pos (le_max_left 1 sx)
  have hQpos : 0 < max 1 sy := lt_of_lt_of_le one_pos (le_max_left 1 sy)
  have hsyle : sy ≤ 2 * max 1 sx := by
    rw [hsy]
    apply Finset.sup'_le
    intro i _
    have hxi : |δ ^ (i.val + 1) * (x - z) i| ≤ sx := by
      rw [hsx]
      exact Finset.le_sup' (fun j => |δ ^ (j.val + 1) * (x - z) j|) (Finset.mem_univ i)
    have hxile : |δ ^ (i.val + 1) * (x - z) i| ≤ max 1 sx :=
      le_trans hxi (le_max_right 1 sx)
    have hyx : |δ ^ (i.val + 1) * (y i - x i)| ≤ 1 := by
      have he : δ ^ (i.val + 1) * (y i - x i) = -(δ ^ (i.val + 1) * (x i - y i)) := by ring
      rw [he, abs_neg]
      exact h i
    calc |δ ^ (i.val + 1) * (y - z) i|
        = |δ ^ (i.val + 1) * (y i - x i) + δ ^ (i.val + 1) * (x i - z i)| := by
          simp only [Pi.sub_apply]
          congr 1
          ring
      _ ≤ |δ ^ (i.val + 1) * (y i - x i)| + |δ ^ (i.val + 1) * (x i - z i)| := abs_add_le _ _
      _ ≤ 1 + max 1 sx := add_le_add hyx hxile
      _ ≤ 2 * max 1 sx := by linarith [le_max_left (1:ℝ) sx]
  have hQle : max 1 sy ≤ 2 * max 1 sx := max_le (by linarith [le_max_left (1:ℝ) sx]) hsyle
  exact rpow_neg_le_of_le_two_mul hA hPpos hQpos hQle

end Commons.Analysis.Convolution