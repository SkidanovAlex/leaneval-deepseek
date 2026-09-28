import Mathlib
import Submission.Work.HP.Defs

/-!
# `Work.HP.EEupper.exists_int_reduce_dot`

Reduction of a lattice vector modulo a primitive vector: given `u ≠ 0` and any `w`, there is an
integer `k` such that the inner product of `u` with `w - k • u` is at most `‖u‖²/2` in absolute
value.  (This is just rounding `⟨u,w⟩ / ‖u‖²` to the nearest integer.)

Used in the proof of Minkowski's second theorem (`Work.HP.EEupper.minkowski_two`): it lets one
replace a shortest vector `w` of a rank-2 lattice by `w - k • u`, whose length is at least the
first minimum, while controlling the angle between `u` and `w`.
-/

set_option autoImplicit false

noncomputable section

open Finset

namespace Work.HP.EEupper

open Work.HP

variable {ι : Type*} [Fintype ι]

/-- Every real number is within `1/2` of an integer (rounding to nearest, ties to the floor of
`x + 1/2`). -/
private lemma exists_int_abs_sub_le_half (x : ℝ) : ∃ k : ℤ, |x - (k : ℝ)| ≤ 1 / 2 := by
  refine ⟨⌊x + 1 / 2⌋, ?_⟩
  have h1 : ((⌊x + 1 / 2⌋ : ℤ) : ℝ) ≤ x + 1 / 2 := Int.floor_le _
  have h2 : x + 1 / 2 < ((⌊x + 1 / 2⌋ : ℤ) : ℝ) + 1 := Int.lt_floor_add_one _
  rw [abs_le]
  constructor <;> linarith

/-- The inner product of `toR u` with `toR (w - k • u)` computed in coordinates. -/
private lemma dotR_toR_sub_smul_eq (u w : ι → ℤ) (k : ℤ) :
    dotR (toR u) (toR (w - k • u))
      = (∑ i, (u i : ℝ) * (w i : ℝ)) - (k : ℝ) * (∑ i, ((u i : ℝ)) ^ 2) := by
  simp only [dotR, toR]
  have hterm : ∀ i, (u i : ℝ) * (((w - k • u) i : ℤ) : ℝ)
      = (u i : ℝ) * (w i : ℝ) - (k : ℝ) * ((u i : ℝ) ^ 2) := by
    intro i
    have hi : (w - k • u) i = w i - k * u i := rfl
    rw [hi]; push_cast; ring
  rw [Finset.sum_congr rfl (fun i _ => hterm i), Finset.sum_sub_distrib, Finset.mul_sum]

/-- **Rounding reduction.**  For a primitive (nonzero) integer vector `u` and any integer vector
`w`, some integer translate `w - k • u` has inner product with `u` bounded by `‖u‖² / 2`. -/
theorem exists_int_reduce_dot {ι : Type*} [Fintype ι] (u w : ι → ℤ) (hu : u ≠ 0) :
    ∃ k : ℤ, |Work.HP.dotR (Work.HP.toR u) (Work.HP.toR (w - k • u))| * 2 ≤ Work.HP.eNorm u ^ 2 := by
  -- some coordinate of `u` is nonzero
  obtain ⟨i, hi⟩ : ∃ i, u i ≠ 0 := by
    by_contra h
    push Not at h
    exact hu (funext fun j => h j)
  have hApos : 0 < ∑ j, ((u j : ℝ)) ^ 2 := by
    have hs := Finset.single_le_sum (f := fun j => ((u j : ℝ)) ^ 2)
      (fun j _ => sq_nonneg _) (Finset.mem_univ i)
    have hi2 : 0 < ((u i : ℝ)) ^ 2 :=
      sq_pos_of_ne_zero (Int.cast_ne_zero.mpr hi)
    linarith
  have hAne : (∑ j, ((u j : ℝ)) ^ 2) ≠ 0 := ne_of_gt hApos
  obtain ⟨k, hk⟩ := exists_int_abs_sub_le_half
    ((∑ j, (u j : ℝ) * (w j : ℝ)) / (∑ j, ((u j : ℝ)) ^ 2))
  refine ⟨k, ?_⟩
  rw [dotR_toR_sub_smul_eq u w k]
  have heNorm_sq : eNorm u ^ 2 = ∑ j, ((u j : ℝ)) ^ 2 := by
    rw [eNorm]; exact Real.sq_sqrt hApos.le
  have hBA : (∑ j, (u j : ℝ) * (w j : ℝ)) - (k : ℝ) * (∑ j, ((u j : ℝ)) ^ 2)
      = (∑ j, ((u j : ℝ)) ^ 2)
        * ((∑ j, (u j : ℝ) * (w j : ℝ)) / (∑ j, ((u j : ℝ)) ^ 2) - k) := by
    rw [mul_sub, mul_div_cancel₀ _ hAne]
    ring
  rw [hBA, abs_mul, abs_of_nonneg hApos.le, heNorm_sq]
  have := mul_le_mul_of_nonneg_left hk hApos.le
  nlinarith [this]

end Work.HP.EEupper
