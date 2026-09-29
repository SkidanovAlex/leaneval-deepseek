import Mathlib
import Submission.Work.Resample.sliceA1defs
import Submission.Work.ResMath.resA_norm_le

/-!
# The summed weights of the 1-D Gaussian resampling word (paper Lemma 4.9)

This module collects the *scalar* facts about the weights `slA p α s t k i`
(the real parts of the entries of the rounded resampling matrix `resA s t α`)
that the cost/correctness proof of the resampling word needs:

* each weight lies in `[0,1]`;
* the weights of output `k` over one full period `s` sum to the row sum of `resA`,
  and that row sum is at most `3/4` (paper Lemma 4.5, `Work.ResMath.resA_rowsum_le`);
* the rounded integer weights `slW = ⌊2^p·slA⌉` satisfy `|slW/2^p - slA| ≤ 2^{-(p+1)}`.

The only non-elementary ingredient is the row-sum bound for `resA`, which is
`Work.ResMath.resA_norm_le`.
-/

set_option autoImplicit false

namespace Work.Resample

open HvdH

/-- The real part of an entry of `resA s t α = (1/2)·S` is nonnegative: it is
`(1/2)(1/α)·Σ_q exp(-π(α²/s²)…)` with every term of the sum nonnegative. -/
lemma resA_re_nonneg (s t α : ℕ) (hα : 0 < α) (k : Fin t) (j : Fin s) :
    0 ≤ (HvdH.resA s t α k j).re := by
  have hαR : (0:ℝ) < (α:ℝ) := by exact_mod_cast hα
  rw [HvdH.resA, Matrix.smul_apply, smul_eq_mul, Work.ResMath.resSmat_apply]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]
  rw [show ((1/2:ℂ)).re = 1/2 by norm_num [Complex.div_re],
      show ((1/2:ℂ)).im = 0 by norm_num [Complex.div_re]]
  have h1 : 0 ≤ 1 / (α:ℝ) * ∑' q : ℤ, Real.exp (-(Real.pi * (s:ℝ)^2 / (α:ℝ)^2) *
      ((k:ℝ)/(t:ℝ) - (j:ℝ)/(s:ℝ) - (q:ℝ))^2) := by positivity
  linarith

/-- Unfolding of `slA`: as soon as `k < t` and `s > 0` the two guards of the
`if` in the definition are satisfied, so the `i`-th weight is the real part of
the matrix entry with column `(slK + s - slH + i) mod s`. -/
lemma slA_eq (p α s t k i : ℕ) (hk : k < t) (hs : 0 < s) :
    slA p α s t k i = ((HvdH.resA s t α) ⟨k, hk⟩
      ⟨((slK s t k + s - slH p α s) + i) % s, Nat.mod_lt _ hs⟩).re := by
  have hHs : slH p α s ≤ s := by
    rw [slH]; exact le_trans (Nat.div_le_self _ _) (Nat.min_le_left _ _)
  have hH : slH p α s ≤ slK s t k + s := by omega
  have hidx : (slK s t k + i + s - slH p α s) % s = ((slK s t k + s - slH p α s) + i) % s := by
    have h2 : slK s t k + i + s - slH p α s = (slK s t k + s - slH p α s) + i := by
      rw [show slK s t k + i + s = i + (slK s t k + s) by omega]
      rw [Nat.add_sub_assoc hH, Nat.add_comm]
    rw [h2]
  simp only [slA]
  have hcond : k < t ∧ (slK s t k + i + s - slH p α s) % s < s := ⟨hk, Nat.mod_lt _ hs⟩
  rw [dite_eq_left hcond]
  simp only [hidx]

/-- Each weight is nonnegative. -/
lemma slA_nonneg (p α s t k i : ℕ) (hk : k < t) (hs : 0 < s) (hα : 0 < α) :
    0 ≤ slA p α s t k i := by
  rw [slA_eq p α s t k i hk hs]
  exact resA_re_nonneg s t α hα _ _

/-- Each weight is at most `1` (in fact at most `3/4`): it is dominated, via the
norm, by the row sum of `resA`. -/
lemma slA_le_one (p α s t k i : ℕ) (hk : k < t) (hs : 0 < s) (hα : 2 ≤ α) :
    slA p α s t k i ≤ 1 := by
  rw [slA_eq p α s t k i hk hs]
  set j : Fin s := ⟨((slK s t k + s - slH p α s) + i) % s, Nat.mod_lt _ hs⟩ with hj
  have h1 : ((HvdH.resA s t α) ⟨k, hk⟩ j).re ≤ ‖(HvdH.resA s t α) ⟨k, hk⟩ j‖ :=
    Complex.re_le_norm _
  have h2 : ‖(HvdH.resA s t α) ⟨k, hk⟩ j‖ ≤ ∑ j' : Fin s, ‖(HvdH.resA s t α) ⟨k, hk⟩ j'‖ :=
    Finset.single_le_sum (fun j' _ => norm_nonneg _) (Finset.mem_univ j)
  have h3 : ∑ j' : Fin s, ‖(HvdH.resA s t α) ⟨k, hk⟩ j'‖ ≤ 3/4 :=
    Work.ResMath.resA_rowsum_le s t α hs hα ⟨k, hk⟩
  linarith

/-- Rotation identity: summing a function of `Fin s` along the cyclic shift
`i ↦ c + i` gives the plain sum. -/
lemma sum_fin_mod_shift (s c : ℕ) (hs : 0 < s) (F : Fin s → ℝ) :
    ∑ i : Fin s, F ⟨(c + (i:ℕ)) % s, Nat.mod_lt _ hs⟩ = ∑ j : Fin s, F j := by
  set φ : Fin s → Fin s := fun i => ⟨(c + (i:ℕ)) % s, Nat.mod_lt _ hs⟩ with hφ
  have hinj : Function.Injective φ := by
    intro i i' h
    have h' : (c + (i:ℕ)) % s = (c + (i':ℕ)) % s := congrArg Fin.val h
    have hmod := Nat.ModEq.add_left_cancel (Nat.ModEq.refl c) h'
    exact Fin.ext (Nat.ModEq.eq_of_lt_of_lt hmod i.isLt i'.isLt)
  have himg : Finset.univ.image φ = Finset.univ := by
    refine Finset.eq_of_subset_of_card_le (Finset.subset_univ _) ?_
    exact (Finset.card_image_of_injOn hinj.injOn).symm.le
  calc ∑ i : Fin s, F (φ i) = ∑ i ∈ Finset.univ, F (φ i) := rfl
    _ = ∑ j ∈ Finset.univ.image φ, F j := (Finset.sum_image hinj.injOn).symm
    _ = ∑ j : Fin s, F j := by rw [himg]

/-- The weights of output `k`, summed over one full period `s`, equal the sum of
the real parts of the `k`-th row of `resA`. -/
lemma sum_range_slA_eq (p α s t k : ℕ) (hk : k < t) (hs : 0 < s) :
    ∑ i ∈ Finset.range s, slA p α s t k i = ∑ j : Fin s, ((HvdH.resA s t α) ⟨k, hk⟩ j).re := by
  rw [← Fin.sum_univ_eq_sum_range (fun i => slA p α s t k i) s]
  have hstep : ∀ i : Fin s, slA p α s t k (i:ℕ) = ((HvdH.resA s t α) ⟨k, hk⟩
      ⟨((slK s t k + s - slH p α s) + (i:ℕ)) % s, Nat.mod_lt _ hs⟩).re :=
    fun i => slA_eq p α s t k (i:ℕ) hk hs
  rw [Finset.sum_congr rfl (fun i _ => hstep i)]
  exact sum_fin_mod_shift s (slK s t k + s - slH p α s) hs
    (fun j => ((HvdH.resA s t α) ⟨k, hk⟩ j).re)

/-- `⌊y + 1/2⌋` is within `1/2` of `y`: the rounding error of `HvdH.rnd`. -/
lemma abs_rnd_sub_le (y : ℝ) : |((HvdH.rnd y : ℤ) : ℝ) - y| ≤ 1/2 := by
  have h1 : ((HvdH.rnd y : ℤ) : ℝ) ≤ y + 1/2 := by
    have := Int.floor_le (y + 1/2)
    simpa only [HvdH.rnd] using this
  have h2 : y - 1/2 < ((HvdH.rnd y : ℤ) : ℝ) := by
    have := Int.lt_floor_add_one (y + 1/2)
    simp only [HvdH.rnd]
    linarith
  rw [abs_le]; constructor <;> linarith

/-- The rounded weight `slW = ⌊2^p·slA⌉` reconstructs `slA` up to `2^{-(p+1)}`. -/
lemma slW_round (p α s t k i : ℕ) :
    |((slW p α s t k i : ℝ) / (2:ℝ)^p - slA p α s t k i)| ≤ 1/(2:ℝ)^(p+1) := by
  have hp2 : (0:ℝ) < (2:ℝ)^p := by positivity
  have hpne : (2:ℝ)^p ≠ 0 := ne_of_gt hp2
  rw [slW]
  rw [show ((HvdH.rnd ((2:ℝ)^p * slA p α s t k i) : ℤ) : ℝ) / (2:ℝ)^p - slA p α s t k i
      = ((((HvdH.rnd ((2:ℝ)^p * slA p α s t k i) : ℤ) : ℝ) - (2:ℝ)^p * slA p α s t k i))
        / (2:ℝ)^p by
    rw [sub_div, mul_div_cancel_left₀ _ hpne]]
  rw [abs_div, abs_of_pos hp2]
  calc |((HvdH.rnd ((2:ℝ)^p * slA p α s t k i) : ℤ) : ℝ) - (2:ℝ)^p * slA p α s t k i| / (2:ℝ)^p
      ≤ (1/2) / (2:ℝ)^p := div_le_div_of_nonneg_right (abs_rnd_sub_le _) hp2.le
    _ = 1/(2:ℝ)^(p+1) := by rw [div_div, ← pow_succ']

theorem sliceA1Sum (p α s t : ℕ) (hs : 2 ≤ s) (hα : 2 ≤ α) (k : ℕ) (hk : k < t) :
    (∀ i, 0 ≤ Work.Resample.slA p α s t k i) ∧
    (∀ i, Work.Resample.slA p α s t k i ≤ 1) ∧
    (∑ i ∈ Finset.range s, Work.Resample.slA p α s t k i =
      ∑ j : Fin s, ((HvdH.resA s t α) ⟨k, hk⟩ j).re) ∧
    (∑ i ∈ Finset.range s, Work.Resample.slA p α s t k i ≤ 3 / 4) ∧
    (∑ i ∈ Finset.range (Work.Resample.slL p α s), Work.Resample.slA p α s t k i ≤ 3 / 4) ∧
    (∀ i, |((Work.Resample.slW p α s t k i : ℝ) / (2 : ℝ) ^ p -
        Work.Resample.slA p α s t k i)| ≤ 1 / (2 : ℝ) ^ (p + 1)) := by
  have hs0 : 0 < s := by omega
  have hα0 : 0 < α := by omega
  have hsum := sum_range_slA_eq p α s t k hk hs0
  have hrow : ∑ j : Fin s, ((HvdH.resA s t α) ⟨k, hk⟩ j).re ≤ 3/4 := by
    calc ∑ j : Fin s, ((HvdH.resA s t α) ⟨k, hk⟩ j).re
        ≤ ∑ j : Fin s, ‖(HvdH.resA s t α) ⟨k, hk⟩ j‖ :=
          Finset.sum_le_sum (fun j _ => Complex.re_le_norm _)
      _ ≤ 3/4 := Work.ResMath.resA_rowsum_le s t α hs0 hα ⟨k, hk⟩
  have h4 : ∑ i ∈ Finset.range s, Work.Resample.slA p α s t k i ≤ 3/4 := hsum.trans_le hrow
  have h5 : ∑ i ∈ Finset.range (Work.Resample.slL p α s),
      Work.Resample.slA p α s t k i ≤ 3/4 := by
    calc ∑ i ∈ Finset.range (slL p α s), slA p α s t k i
        ≤ ∑ i ∈ Finset.range s, slA p α s t k i :=
          Finset.sum_le_sum_of_subset_of_nonneg
            (Finset.range_subset_range.mpr (Nat.min_le_left _ _))
            (fun i _ _ => slA_nonneg p α s t k i hk hs0 hα0)
      _ ≤ 3/4 := h4
  exact ⟨fun i => slA_nonneg p α s t k i hk hs0 hα0,
         fun i => slA_le_one p α s t k i hk hs0 hα,
         hsum, h4, h5, fun i => slW_round p α s t k i⟩

end Work.Resample
