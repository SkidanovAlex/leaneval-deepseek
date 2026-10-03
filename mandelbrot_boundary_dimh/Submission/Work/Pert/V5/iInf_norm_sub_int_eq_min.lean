import Mathlib

namespace Work.Pert.V5

/-- If `0 ≤ a ≤ 1/2` then `|a| ≤ |a - j|` for every integer `j`; in squared form. -/
lemma sq_le_sq_sub_int_of_le (a : ℝ) (ha0 : 0 ≤ a) (ha1 : a ≤ 1 / 2) (j : ℤ) :
    a ^ 2 ≤ (a - (j : ℝ)) ^ 2 := by
  rw [sq_le_sq, abs_of_nonneg ha0]
  by_cases hj : j ≤ 0
  · have hj' : (j : ℝ) ≤ 0 := by exact_mod_cast hj
    rw [abs_of_nonneg (by linarith)]
    linarith
  · have hj1 : (1 : ℤ) ≤ j := by omega
    have hj1' : (1 : ℝ) ≤ (j : ℝ) := by exact_mod_cast hj1
    rw [abs_of_neg (by linarith : a - (j : ℝ) < 0)]
    linarith

/-- If `1/2 ≤ a ≤ 3/2` then `|a - 1| ≤ |a - j|` for every integer `j`; in squared form. -/
lemma sq_le_sq_sub_int_of_ge (a : ℝ) (ha0 : 1 / 2 ≤ a) (ha1 : a ≤ 3 / 2) (j : ℤ) :
    (a - 1) ^ 2 ≤ (a - (j : ℝ)) ^ 2 := by
  rw [sq_le_sq]
  have h1 : |a - 1| ≤ 1 / 2 := by rw [abs_le]; constructor <;> linarith
  by_cases hj : j ≤ 0
  · have hj' : (j : ℝ) ≤ 0 := by exact_mod_cast hj
    rw [abs_of_nonneg (by linarith : 0 ≤ a - (j : ℝ))]
    linarith
  · by_cases hj1 : j = 1
    · subst hj1; norm_num
    · have hj2 : (2 : ℤ) ≤ j := by omega
      have hj2' : (2 : ℝ) ≤ (j : ℝ) := by exact_mod_cast hj2
      rw [abs_of_nonpos (by linarith : a - (j : ℝ) ≤ 0)]
      linarith

/-- Monotonicity of the norm on `ℂ` from an inequality of squared norms. -/
lemma norm_le_norm_of_sq_le {z w : ℂ} (h : ‖z‖ ^ 2 ≤ ‖w‖ ^ 2) : ‖z‖ ≤ ‖w‖ := by
  have := Real.sqrt_le_sqrt h
  rwa [Real.sqrt_sq (norm_nonneg z), Real.sqrt_sq (norm_nonneg w)] at this

/-- The closest point of `ℤ ⊆ ℂ` to `v` is `0` or `1` when `0 ≤ v.re ≤ 3/2`:
every `‖v - j‖`, `j ∈ ℤ`, is at least `min ‖v‖ ‖v - 1‖`. -/
lemma min_norm_le_norm_sub_int (v : ℂ) (h0 : 0 ≤ v.re) (h1 : v.re ≤ 3 / 2) (j : ℤ) :
    min ‖v‖ ‖v - (1 : ℂ)‖ ≤ ‖v - ((j : ℤ) : ℂ)‖ := by
  have hs1 : ‖v‖ ^ 2 = v.re ^ 2 + v.im ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]; ring
  have hs2 : ‖v - (1 : ℂ)‖ ^ 2 = (v.re - 1) ^ 2 + v.im ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.one_re,
      Complex.one_im, sub_zero]
    ring
  have hs3 : ‖v - ((j : ℤ) : ℂ)‖ ^ 2 = (v.re - (j : ℝ)) ^ 2 + v.im ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
      Complex.intCast_re, Complex.intCast_im, sub_zero]
    ring
  rw [min_le_iff]
  by_cases ha : v.re ≤ 1 / 2
  · left
    apply norm_le_norm_of_sq_le
    rw [hs1, hs3]
    have := sq_le_sq_sub_int_of_le v.re h0 ha j
    linarith
  · right
    have ha' : 1 / 2 ≤ v.re := by linarith
    apply norm_le_norm_of_sq_le
    rw [hs2, hs3]
    have := sq_le_sq_sub_int_of_ge v.re ha' h1 j
    linarith

theorem iInf_norm_sub_int_eq_min {w : ℂ} {m : ℤ} (h1 : (m : ℝ) ≤ w.re) (h2 : w.re ≤ (m : ℝ) + 3 / 2) :
    (⨅ k : ℤ, ‖w - (k : ℂ)‖) = min ‖w - (m : ℂ)‖ ‖w - ((m + 1 : ℤ) : ℂ)‖ := by
  have hbb : BddBelow (Set.range (fun k : ℤ => ‖w - (k : ℂ)‖)) :=
    ⟨0, by rintro _ ⟨k, rfl⟩; exact norm_nonneg _⟩
  apply le_antisymm
  · -- the infimum is at most each of the two candidate values
    apply le_min
    · exact ciInf_le hbb m
    · exact ciInf_le hbb (m + 1)
  · -- and every value of the family dominates the smaller candidate
    apply le_ciInf
    intro k
    have h0 : 0 ≤ (w - (m : ℂ)).re := by rw [Complex.sub_re, Complex.intCast_re]; linarith
    have h1' : (w - (m : ℂ)).re ≤ 3 / 2 := by rw [Complex.sub_re, Complex.intCast_re]; linarith
    have hkey := min_norm_le_norm_sub_int (w - (m : ℂ)) h0 h1' (k - m)
    have e1 : ‖(w - (m : ℂ)) - (1 : ℂ)‖ = ‖w - ((m + 1 : ℤ) : ℂ)‖ := by
      congr 1; push_cast; ring
    have e2 : ‖(w - (m : ℂ)) - (((k - m : ℤ)) : ℂ)‖ = ‖w - (k : ℂ)‖ := by
      congr 1; push_cast; ring
    simpa [e1, e2] using hkey

end Work.Pert.V5
