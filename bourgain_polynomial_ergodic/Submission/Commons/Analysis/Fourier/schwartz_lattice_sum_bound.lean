import Mathlib.Analysis.PSeries
import Submission.Commons.Analysis.Fourier.aniso_gauge_bump

set_option linter.unusedSimpArgs false

open scoped BigOperators

namespace Commons.Analysis.Fourier

/-- The fundamental `p`-series bound over `ℤ`, with the `+1` shift that removes the
singularity at the origin: `∑' n, 1 / |n - 1/2| ^ 2` converges. -/
lemma summable_int_one_div_abs_sub_half_sq :
    Summable (fun n : ℤ => 1 / |(n:ℝ) - 1/2| ^ (2:ℝ)) := by
  have h := (Real.summable_one_div_int_add_rpow (-(1/2)) 2).mpr (by norm_num : (1:ℝ) < 2)
  refine h.congr (fun n => ?_)
  simp only [sub_eq_add_neg]

/-- Translation of the previous summable kernel by an arbitrary integer shift. -/
lemma summable_int_one_div_abs_shift_half_sq (k : ℤ) :
    Summable (fun n : ℤ => 1 / |(n:ℝ) - (k:ℝ) - 1/2| ^ (2:ℝ)) := by
  refine ((Equiv.summable_iff (Equiv.subRight k)).mpr summable_int_one_div_abs_sub_half_sq).congr ?_
  intro n
  simp [Function.comp_apply, Equiv.subRight_apply, Int.cast_sub, sub_eq_add_neg]

/-- The sum of the translated kernel is independent of the integer shift. -/
lemma tsum_int_one_div_abs_shift_half_sq (k : ℤ) :
    ∑' n : ℤ, 1 / |(n:ℝ) - (k:ℝ) - 1/2| ^ (2:ℝ)
      = ∑' m : ℤ, 1 / |(m:ℝ) - 1/2| ^ (2:ℝ) := by
  rw [← Equiv.tsum_eq (Equiv.subRight k) (fun m : ℤ => 1 / |(m:ℝ) - 1/2| ^ (2:ℝ))]
  refine tsum_congr (fun n => ?_)
  simp [Equiv.subRight_apply, sub_eq_add_neg]

/-- An integer is never equal to `1/2`. -/
lemma int_abs_sub_half_ne_zero (M : ℤ) : ((M:ℝ) - 1/2) ≠ 0 := by
  rcases lt_or_ge (0:ℤ) M with hM | hM
  · have hM1 : (1:ℤ) ≤ M := by omega
    have hM1' : (1:ℝ) ≤ ((M:ℤ):ℝ) := by exact_mod_cast hM1
    linarith
  · have hM0 : ((M:ℤ):ℝ) ≤ 0 := by exact_mod_cast hM
    linarith

/-- Every integer is at positive distance from `1/2`. -/
lemma int_abs_sub_half_pos (M : ℤ) : 0 < |(M:ℝ) - 1/2| :=
  abs_pos.mpr (int_abs_sub_half_ne_zero M)

/-- The key geometric estimate: for a real `s ∈ [0,1)` and an integer `M`,
`|M - 1/2| ≤ 1 + |s - M|`.  This is what makes the sum over the lattice of a
`(1 + |t - n|)^{-2}` weight uniform in `t`. -/
lemma int_abs_sub_half_upper (M : ℤ) (s : ℝ) (hs0 : 0 ≤ s) (hs1 : s < 1) :
    |(M:ℝ) - 1/2| ≤ 1 + |s - (M:ℝ)| := by
  rcases lt_or_ge (0:ℤ) M with hM | hM
  · have hM1 : (1:ℤ) ≤ M := by omega
    have hM1' : (1:ℝ) ≤ ((M:ℤ):ℝ) := by exact_mod_cast hM1
    have hs : s - (M:ℝ) ≤ 0 := by linarith
    rw [abs_of_nonneg (by linarith : (0:ℝ) ≤ ((M:ℤ):ℝ) - 1/2), abs_of_nonpos hs]
    linarith
  · have hM0 : ((M:ℤ):ℝ) ≤ 0 := by exact_mod_cast hM
    have hs : 0 ≤ s - (M:ℝ) := by linarith
    rw [abs_of_nonpos (by linarith : ((M:ℤ):ℝ) - 1/2 ≤ 0), abs_of_nonneg hs]
    linarith

/-- Pointwise domination of the `t`-shifted decaying weight by the integer-shifted
kernel `|n - ⌊t⌋ - 1/2|^{-2}`. -/
lemma lattice_decay_pointwise (t : ℝ) (n : ℤ) :
    (1 + |t - (n:ℝ)|) ^ (-(2:ℝ))
      ≤ 1 / |(n:ℝ) - (⌊t⌋:ℝ) - 1/2| ^ (2:ℝ) := by
  set M : ℤ := n - ⌊t⌋ with hMdef
  have hMcast : ((M:ℤ):ℝ) = (n:ℝ) - (⌊t⌋:ℝ) := by simp [hMdef, Int.cast_sub]
  have hs0 : 0 ≤ t - (⌊t⌋:ℝ) := by
    have := Int.floor_le t; linarith
  have hs1 : t - (⌊t⌋:ℝ) < 1 := by
    have := Int.lt_floor_add_one t; linarith
  have htn : t - (n:ℝ) = (t - (⌊t⌋:ℝ)) - ((M:ℤ):ℝ) := by rw [hMcast]; ring
  have hle : |((M:ℤ):ℝ) - 1/2| ≤ 1 + |t - (n:ℝ)| := by
    have h := int_abs_sub_half_upper M (t - (⌊t⌋:ℝ)) hs0 hs1
    rwa [← htn] at h
  have hb1 : 0 < (1 + |t - (n:ℝ)|) := by positivity
  have hb2 : 0 < |((M:ℤ):ℝ) - 1/2| := int_abs_sub_half_pos M
  have hrpow : |((M:ℤ):ℝ) - 1/2| ^ (2:ℝ) ≤ (1 + |t - (n:ℝ)|) ^ (2:ℝ) :=
    Real.rpow_le_rpow (le_of_lt hb2) hle (by norm_num : (0:ℝ) ≤ 2)
  have hden : (n:ℝ) - (⌊t⌋:ℝ) - 1/2 = ((M:ℤ):ℝ) - 1/2 := by rw [hMcast]
  rw [hden, one_div, Real.rpow_neg (le_of_lt hb1)]
  exact (inv_le_inv₀ (Real.rpow_pos_of_pos hb1 2) (Real.rpow_pos_of_pos hb2 2)).mpr hrpow

/-- The sum over the integer lattice of the decaying weight `(1 + |t - n|) ^ (-2)`
is bounded uniformly in `t`. -/
theorem schwartz_lattice_sum_bound (ψ : SchwartzMap ℝ ℂ) :
    ∃ M : ℝ, 0 < M ∧ ∀ t : ℝ, ∑' n : ℤ, ‖ψ (t - n)‖ ≤ M := by
  obtain ⟨B, hBpos, hBdecay⟩ := schwartzMap_real_decay ψ 2
  have hsum0 := summable_int_one_div_abs_sub_half_sq
  set K : ℝ := ∑' n : ℤ, 1 / |(n:ℝ) - 1/2| ^ (2:ℝ) with hKdef
  have hK0 : 0 ≤ K := by rw [hKdef]; exact tsum_nonneg (fun n => by positivity)
  refine ⟨B * K + 1, by linarith [mul_nonneg hBpos.le hK0], fun t => ?_⟩
  have hsumB : Summable (fun n : ℤ => 1 / |(n:ℝ) - (⌊t⌋:ℝ) - 1/2| ^ (2:ℝ)) :=
    summable_int_one_div_abs_shift_half_sq ⌊t⌋
  have hpoint : ∀ n : ℤ, (1 + |t - (n:ℝ)|) ^ (-(2:ℝ))
      ≤ 1 / |(n:ℝ) - (⌊t⌋:ℝ) - 1/2| ^ (2:ℝ) := lattice_decay_pointwise t
  have hsumA : Summable (fun n : ℤ => (1 + |t - (n:ℝ)|) ^ (-(2:ℝ))) :=
    Summable.of_nonneg_of_le (fun n => Real.rpow_nonneg (by positivity) _) hpoint hsumB
  have hle1 : ∑' n : ℤ, (1 + |t - (n:ℝ)|) ^ (-(2:ℝ)) ≤ K := by
    rw [hKdef]
    exact (Summable.tsum_le_tsum hpoint hsumA hsumB).trans
      (le_of_eq (tsum_int_one_div_abs_shift_half_sq ⌊t⌋))
  have hdec : ∀ n : ℤ, ‖ψ (t - n)‖ ≤ B * (1 + |t - (n:ℝ)|) ^ (-(2:ℝ)) :=
    fun n => hBdecay (t - n)
  have hsumG : Summable (fun n : ℤ => ‖ψ (t - n)‖) :=
    Summable.of_nonneg_of_le (fun n => norm_nonneg _) hdec (hsumA.mul_left B)
  have hfin : ∑' n : ℤ, ‖ψ (t - n)‖ ≤ B * K := by
    have h2 := Summable.tsum_le_tsum hdec hsumG (hsumA.mul_left B)
    rw [Summable.tsum_mul_left B hsumA] at h2
    exact h2.trans (mul_le_mul_of_nonneg_left hle1 hBpos.le)
  linarith

end Commons.Analysis.Fourier