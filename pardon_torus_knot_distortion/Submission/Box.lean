import Mathlib
import ChallengeDeps
import Submission.Work.Core.Torus
import Submission.Work.CoreTopology.Winding

/-!
# Pardon's self-similar box

Pardon's proof of the torus-knot distortion bound uses the family of boxes

`Box(r) = {|x| < r, |y| < 2^{1/3} r, |z| < 2^{2/3} r}`

(the `2`-nd coordinate being the "long" direction), whose halves cut by a plane perpendicular
to the long direction are congruent to `Box(2^{-1/3} r)`, so that cutting a box by a plane
produces a box of strictly smaller side length when the three side lengths `1, 2^{1/3},
2^{2/3}` are recycled by a cyclic permutation of the coordinates.

This file sets up the box vocabulary used by the assembly of the final theorem:

* `Submission.boxSide` -- the three side lengths `1, 2^{1/3}, 2^{2/3}`;
* `Submission.PBox r c σ` -- the open box with centre `c`, side lengths `boxSide i * r`, the
  three coordinate directions permuted by `σ` ("a box congruent to `Box(r)`");
* the constants `eps = 2/13`, `shrinkFactor = 2^{-1/3}(1+eps) + eps/2 < 1` and
  `countConst = 20(1+1/eps) = 150 < 160` of Pardon's argument;
* the *geometry* of the halving: the two halves of `PBox r c 1` cut by the plane
  `{y 2 = c 2 + s}` with `|s| < eps * r` both fit inside `PBox (b * r + |s|/2) c' cycPerm`,
  where `b = 2^{-1/3}`.
-/

namespace Submission

open LeanEval.KnotTheory.PardonDistortion
open Set

noncomputable section

/-- The side lengths `1, 2^{1/3}, 2^{2/3}` of Pardon's box `Box(1)`. -/
def boxSide (i : Fin 3) : ℝ :=
  if i.val = 0 then 1 else if i.val = 1 then (2 : ℝ) ^ (1 / 3 : ℝ)
  else (2 : ℝ) ^ (2 / 3 : ℝ)

@[simp] theorem boxSide_zero : boxSide 0 = 1 := by simp [boxSide]
@[simp] theorem boxSide_one : boxSide 1 = (2 : ℝ) ^ (1 / 3 : ℝ) := by simp [boxSide]
@[simp] theorem boxSide_two : boxSide 2 = (2 : ℝ) ^ (2 / 3 : ℝ) := by simp [boxSide]

theorem boxSide_pos (i : Fin 3) : 0 < boxSide i := by
  fin_cases i <;> simp [boxSide] <;> positivity

theorem rpow_third_le_two : (2 : ℝ) ^ (1 / 3 : ℝ) ≤ 2 := by
  calc (2 : ℝ) ^ (1 / 3 : ℝ) ≤ (2 : ℝ) ^ (1 : ℝ) :=
        Real.rpow_le_rpow_left_iff (by norm_num) |>.mpr (by norm_num)
    _ = 2 := by simp

theorem rpow_two_thirds_le_two : (2 : ℝ) ^ (2 / 3 : ℝ) ≤ 2 := by
  calc (2 : ℝ) ^ (2 / 3 : ℝ) ≤ (2 : ℝ) ^ (1 : ℝ) :=
        Real.rpow_le_rpow_left_iff (by norm_num) |>.mpr (by norm_num)
    _ = 2 := by simp

theorem one_le_rpow_third : (1 : ℝ) ≤ 2 ^ (1 / 3 : ℝ) := by
  have h : (2 : ℝ) ^ (0 : ℝ) ≤ (2 : ℝ) ^ (1 / 3 : ℝ) :=
    Real.rpow_le_rpow_left_iff (by norm_num) |>.mpr (by norm_num)
  simpa using h

theorem one_le_rpow_two_thirds : (1 : ℝ) ≤ 2 ^ (2 / 3 : ℝ) := by
  have h : (2 : ℝ) ^ (0 : ℝ) ≤ (2 : ℝ) ^ (2 / 3 : ℝ) :=
    Real.rpow_le_rpow_left_iff (by norm_num) |>.mpr (by norm_num)
  simpa using h

theorem boxSide_le_two (i : Fin 3) : boxSide i ≤ 2 := by
  unfold boxSide
  split_ifs
  · norm_num
  · exact rpow_third_le_two
  · exact rpow_two_thirds_le_two

theorem one_le_boxSide (i : Fin 3) : 1 ≤ boxSide i := by
  unfold boxSide
  split_ifs
  · norm_num
  · exact one_le_rpow_third
  · exact one_le_rpow_two_thirds

/-- **Pardon's box** with centre `c`, size `r` and coordinate permutation `σ`: the open box
whose coordinate `σ i` has half-length `boxSide i * r`. -/
def PBox (r : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) : Set R3 :=
  {y | ∀ i : Fin 3, |y (σ i) - c (σ i)| < boxSide i * r}

theorem mem_PBox {r : ℝ} {c : R3} {σ : Equiv.Perm (Fin 3)} {y : R3} :
    y ∈ PBox r c σ ↔ ∀ i : Fin 3, |y (σ i) - c (σ i)| < boxSide i * r := Iff.rfl

/-- The **box norm** centred at `c` with coordinate permutation `σ`: the size parameter `s` for
which `y` lies on the boundary of `PBox s c σ`. -/
def boxNorm (c : R3) (σ : Equiv.Perm (Fin 3)) (y : R3) : ℝ :=
  max (max (|y (σ 0) - c (σ 0)| / boxSide 0) (|y (σ 1) - c (σ 1)| / boxSide 1))
    (|y (σ 2) - c (σ 2)| / boxSide 2)

theorem boxNorm_nonneg (c : R3) (σ : Equiv.Perm (Fin 3)) (y : R3) : 0 ≤ boxNorm c σ y := by
  rw [boxNorm]
  exact le_trans (div_nonneg (abs_nonneg _) (le_of_lt (boxSide_pos 0)))
    (le_trans (le_max_left _ _) (le_max_left _ _))

/-- `y` lies in `PBox s c σ` exactly when its box norm is below `s`. -/
theorem mem_PBox_iff (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (y : R3) :
    y ∈ PBox s c σ ↔ boxNorm c σ y < s := by
  rw [mem_PBox, boxNorm, max_lt_iff, max_lt_iff]
  constructor
  · intro h
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · rw [div_lt_iff₀ (boxSide_pos 0)]; simpa [mul_comm] using h 0
    · rw [div_lt_iff₀ (boxSide_pos 1)]; simpa [mul_comm] using h 1
    · rw [div_lt_iff₀ (boxSide_pos 2)]; simpa [mul_comm] using h 2
  · intro h i
    fin_cases i
    · have h1 := h.1.1; rw [div_lt_iff₀ (boxSide_pos 0)] at h1; simpa [mul_comm] using h1
    · have h1 := h.1.2; rw [div_lt_iff₀ (boxSide_pos 1)] at h1; simpa [mul_comm] using h1
    · have h1 := h.2; rw [div_lt_iff₀ (boxSide_pos 2)] at h1; simpa [mul_comm] using h1

theorem PBox_mono {r r' : ℝ} (h : r ≤ r') {c : R3} {σ : Equiv.Perm (Fin 3)} :
    PBox r c σ ⊆ PBox r' c σ := by
  intro y hy i
  exact lt_of_lt_of_le (hy i) (mul_le_mul_of_nonneg_left h (le_of_lt (boxSide_pos i)))

theorem rpow_two_thirds_lt : (2 : ℝ) ^ (2 / 3 : ℝ) < 8 / 5 := by
  have hcube : ((2 : ℝ) ^ (2 / 3 : ℝ)) ^ 3 = 4 := by
    rw [← Real.rpow_natCast ((2 : ℝ) ^ (2 / 3 : ℝ)) 3,
      ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num
  by_contra h
  push Not at h
  have h4 : (8 / 5 : ℝ) ^ 3 ≤ ((2 : ℝ) ^ (2 / 3 : ℝ)) ^ 3 :=
    pow_le_pow_left₀ (by norm_num) h 3
  rw [hcube] at h4
  norm_num at h4

theorem rpow_four_thirds_lt : (2 : ℝ) ^ (4 / 3 : ℝ) < 3 := by
  have hsq : (2 : ℝ) ^ (4 / 3 : ℝ) = ((2 : ℝ) ^ (2 / 3 : ℝ)) ^ 2 := by
    rw [← Real.rpow_natCast ((2 : ℝ) ^ (2 / 3 : ℝ)) 2,
      ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num
  rw [hsq]
  have h := rpow_two_thirds_lt
  nlinarith [h, show (0:ℝ) < (2:ℝ)^(2/3:ℝ) by positivity]

theorem sum_boxSide_sq_lt : ∑ i : Fin 3, boxSide i ^ 2 < 25 / 4 := by
  rw [Fin.sum_univ_three, boxSide_zero, boxSide_one, boxSide_two]
  have hsq : ((2 : ℝ) ^ (1 / 3 : ℝ)) ^ 2 = (2 : ℝ) ^ (2 / 3 : ℝ) := by
    rw [← Real.rpow_natCast ((2 : ℝ) ^ (1 / 3 : ℝ)) 2,
      ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num
  rw [hsq]
  have h1 := rpow_two_thirds_lt
  have h2 : (0 : ℝ) < (2 : ℝ) ^ (2 / 3 : ℝ) := by positivity
  nlinarith [h1, h2, sq_nonneg ((2 : ℝ) ^ (2 / 3 : ℝ))]

/-- Every point of `PBox r c σ` is within distance `5/2 * r` of the centre. -/
theorem PBox_subset_ball (r : ℝ) (hr : 0 ≤ r) (c : R3) (σ : Equiv.Perm (Fin 3)) :
    PBox r c σ ⊆ Metric.ball c ((5 / 2) * r) := by
  intro y hy
  rw [Metric.mem_ball, dist_eq_norm]
  have hr' : 0 < r := by
    rcases eq_or_lt_of_le hr with h | h
    · exfalso
      have h0 := hy 0
      rw [← h, boxSide_zero, mul_zero] at h0
      exact absurd h0 (not_lt.mpr (abs_nonneg _))
    · exact h
  have hcoord : ∀ i : Fin 3, (y i - c i) ^ 2 < (boxSide (σ.symm i) * r) ^ 2 := by
    intro i
    have h := hy (σ.symm i)
    simp only [Equiv.apply_symm_apply] at h
    have h4 := abs_lt.mp h
    nlinarith [h4.1, h4.2, hr]
  have hnorm : ‖y - c‖ ^ 2 = ∑ i : Fin 3, (y i - c i) ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq]
    exact Finset.sum_congr rfl fun i _ => by rw [PiLp.sub_apply, Real.norm_eq_abs, sq_abs]
  have hsum : ∑ i : Fin 3, (y i - c i) ^ 2 < ∑ i : Fin 3, (boxSide (σ.symm i) * r) ^ 2 :=
    Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty (fun i _ => hcoord i)
  have hperm : ∑ i : Fin 3, (boxSide (σ.symm i) * r) ^ 2 = (∑ i : Fin 3, boxSide i ^ 2) * r ^ 2 := by
    rw [Equiv.sum_comp σ.symm (fun i => (boxSide i * r) ^ 2), Finset.sum_mul]
    exact Finset.sum_congr rfl fun i _ => by ring
  have hlt : ‖y - c‖ ^ 2 < ((5 / 2) * r) ^ 2 := by
    rw [hnorm]
    have hsq := sum_boxSide_sq_lt
    rw [hperm] at hsum
    nlinarith [hsum, hsq, hr]
  have hpos : 0 < (5 / 2) * r := by linarith
  nlinarith [norm_nonneg (y - c), hlt, hpos]

/-- The diameter of the image of a curve contained in `PBox r c σ` is at most `5 * r`. -/
theorem diam_range_le_of_subset_PBox {r : ℝ} (hr : 0 ≤ r) {c : R3} {σ : Equiv.Perm (Fin 3)}
    {γ : ℝ → R3} (hγ : ∀ t, γ t ∈ PBox r c σ) :
    Metric.diam (Set.range γ) ≤ 5 * r := by
  refine Metric.diam_le_of_forall_dist_le (by linarith) ?_
  rintro x ⟨s, rfl⟩ y ⟨t, rfl⟩
  have hs := PBox_subset_ball r hr c σ (hγ s)
  have ht := PBox_subset_ball r hr c σ (hγ t)
  rw [Metric.mem_ball, dist_eq_norm] at hs ht
  calc dist (γ s) (γ t) = ‖γ s - γ t‖ := dist_eq_norm _ _
    _ ≤ ‖γ s - c‖ + ‖γ t - c‖ := by
        rw [show γ s - γ t = (γ s - c) - (γ t - c) by abel]
        exact norm_sub_le _ _
    _ ≤ (5 / 2) * r + (5 / 2) * r := add_le_add (le_of_lt hs) (le_of_lt ht)
    _ = 5 * r := by ring

/-! ## Pardon's numerical constants -/

/-- The relative trimming `ε = 2/13` of Pardon's argument. -/
def eps : ℝ := 2 / 13

/-- `b = 2^{-1/3}`, the half-length of the "short" direction of a half-box. -/
def b : ℝ := (2 : ℝ) ^ (-1 / 3 : ℝ)

/-- The shrink factor `2^{-1/3}(1+ε) + ε/2 = (15 b + 1)/13` of Pardon's argument; it is `< 1`. -/
def shrinkFactor : ℝ := (15 * b + 1) / 13

/-- The constant `20 (1 + 1/ε) = 150` multiplying the distortion bound in the intersection
count; it is `< 160`. -/
def countConst : ℝ := 150

theorem eps_pos : 0 < eps := by norm_num [eps]

theorem b_pos : 0 < b := by rw [b]; positivity

theorem b_mul_boxSide_one : b * boxSide 1 = 1 := by
  rw [b, boxSide_one, ← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
  norm_num

theorem b_mul_boxSide_two : b * boxSide 2 = boxSide 1 := by
  rw [b, boxSide_one, boxSide_two, ← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
  norm_num

theorem two_mul_b : 2 * b = boxSide 2 := by
  have h : (2 : ℝ) ^ (1 : ℝ) * (2 : ℝ) ^ (-1 / 3 : ℝ) = (2 : ℝ) ^ (2 / 3 : ℝ) := by
    rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
    norm_num
  simpa [b, boxSide_two] using h

theorem shrinkFactor_eq_expansion :
    shrinkFactor = (2 : ℝ) ^ (-1 / 3 : ℝ) * (1 + eps) + eps / 2 := by
  rw [shrinkFactor, eps, b]; ring

theorem b_lt_four_fifths : b < 4 / 5 := by
  by_contra h
  push Not at h
  have hb3 : b ^ 3 = 1 / 2 := by
    rw [b]
    rw [← Real.rpow_natCast ((2 : ℝ) ^ (-1 / 3 : ℝ)) 3,
      ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num
  have h4 : (4 / 5 : ℝ) ^ 3 ≤ b ^ 3 := pow_le_pow_left₀ (by norm_num) h 3
  rw [hb3] at h4
  norm_num at h4

theorem shrinkFactor_pos : 0 < shrinkFactor := by
  rw [shrinkFactor]; have := b_pos; positivity

theorem shrinkFactor_lt_one : shrinkFactor < 1 := by
  rw [shrinkFactor, div_lt_one (by norm_num : (0 : ℝ) < 13)]
  have := b_lt_four_fifths
  linarith

/-! ## The halving geometry -/

/-- The translation by `d` in the third coordinate. -/
def shiftV (d : ℝ) : R3 := WithLp.toLp 2 (fun i : Fin 3 => if i.val = 2 then d else 0)

@[simp] theorem add_shiftV_zero (d : ℝ) (c : R3) : (c + shiftV d) 0 = c 0 := by
  simp [shiftV]
@[simp] theorem add_shiftV_one (d : ℝ) (c : R3) : (c + shiftV d) 1 = c 1 := by
  simp [shiftV]
@[simp] theorem add_shiftV_two (d : ℝ) (c : R3) : (c + shiftV d) 2 = c 2 + d := by
  simp [shiftV]

/-- The cyclic permutation `(0 ↦ 2, 1 ↦ 0, 2 ↦ 1)` of the three coordinates. -/
def cycPerm : Equiv.Perm (Fin 3) where
  toFun := ![2, 0, 1]
  invFun := ![1, 2, 0]
  left_inv := by intro i; fin_cases i <;> rfl
  right_inv := by intro i; fin_cases i <;> rfl

@[simp] theorem cycPerm_zero : cycPerm 0 = 2 := rfl
@[simp] theorem cycPerm_one : cycPerm 1 = 0 := rfl
@[simp] theorem cycPerm_two : cycPerm 2 = 1 := rfl

/-- Assembling a `mem` for `PBox _ _ cycPerm` from the three component bounds. -/
theorem mem_PBox_cycPerm {a : ℝ} {c' y : R3}
    (h0 : |y 2 - c' 2| < a) (h1 : |y 0 - c' 0| < boxSide 1 * a)
    (h2 : |y 1 - c' 1| < boxSide 2 * a) : y ∈ PBox a c' cycPerm := by
  intro i
  fin_cases i
  · simpa [cycPerm, boxSide] using h0
  · simpa [cycPerm, boxSide] using h1
  · simpa [cycPerm, boxSide] using h2

/-- **The upper half of Pardon's box fits in a permuted box.**  Cutting `PBox r c 1` by the
plane `{y 2 = c 2 + s}` with `|s| < 2^{2/3} r`, the upper half `{y 2 < c 2 + s}` is contained in
the box `PBox (b * r + |s|/2) (c + shiftV ((s - 2^{2/3} r)/2)) cycPerm`. -/
theorem halfBox_upper_subset (r s : ℝ) (hr : 0 < r) (hs : |s| < boxSide 2 * r) (c : R3) :
    {y : R3 | y ∈ PBox r c 1 ∧ y 2 < c 2 + s} ⊆
      PBox (b * r + |s| / 2) (c + shiftV ((s - boxSide 2 * r) / 2)) cycPerm := by
  intro y hy
  obtain ⟨hybox, hy2⟩ := hy
  have h0 : |y 0 - c 0| < r := by simpa using hybox 0
  have h1 : |y 1 - c 1| < boxSide 1 * r := by simpa using hybox 1
  have h2 : |y 2 - c 2| < boxSide 2 * r := by simpa using hybox 2
  have h2lo : -(boxSide 2 * r) < y 2 - c 2 := (abs_lt.mp h2).1
  have h2hi : y 2 - c 2 < s := by linarith [hy2]
  have hslo : -(boxSide 2 * r) < s := (abs_lt.mp hs).1
  have hb2 : boxSide 2 = 2 * b := two_mul_b.symm
  have key0 : |y 2 - (c + shiftV ((s - boxSide 2 * r) / 2)) 2| < b * r + |s| / 2 := by
    simp only [add_shiftV_two]
    rw [abs_lt]
    have hle : (boxSide 2 * r + s) / 2 ≤ b * r + |s| / 2 := by
      rw [hb2]; have := le_abs_self s; linarith
    constructor <;> linarith
  have key1 : |y 0 - (c + shiftV ((s - boxSide 2 * r) / 2)) 0| <
      boxSide 1 * (b * r + |s| / 2) := by
    simp only [add_shiftV_zero]
    have hb1 : boxSide 1 * b = 1 := by rw [mul_comm, b_mul_boxSide_one]
    have hle : r ≤ boxSide 1 * (b * r + |s| / 2) := by
      nlinarith [hb1, boxSide_pos 1, hr, abs_nonneg s]
    linarith [abs_lt.mp h0]
  have key2 : |y 1 - (c + shiftV ((s - boxSide 2 * r) / 2)) 1| <
      boxSide 2 * (b * r + |s| / 2) := by
    simp only [add_shiftV_one]
    have hb : boxSide 2 * b = boxSide 1 := by rw [mul_comm, b_mul_boxSide_two]
    have hle : boxSide 1 * r ≤ boxSide 2 * (b * r + |s| / 2) := by
      have h : boxSide 2 * (b * r) = boxSide 1 * r := by rw [← mul_assoc, hb]
      nlinarith [h, boxSide_pos 2, hr, abs_nonneg s]
    linarith [abs_lt.mp h1]
  exact mem_PBox_cycPerm key0 key1 key2

/-- **The lower half of Pardon's box fits in a permuted box.**  Cutting `PBox r c 1` by the
plane `{y 2 = c 2 + s}` with `|s| < 2^{2/3} r`, the lower half `{c 2 + s < y 2}` is contained in
the box `PBox (b * r + |s|/2) (c + shiftV ((s + 2^{2/3} r)/2)) cycPerm`. -/
theorem halfBox_lower_subset (r s : ℝ) (hr : 0 < r) (hs : |s| < boxSide 2 * r) (c : R3) :
    {y : R3 | y ∈ PBox r c 1 ∧ c 2 + s < y 2} ⊆
      PBox (b * r + |s| / 2) (c + shiftV ((s + boxSide 2 * r) / 2)) cycPerm := by
  intro y hy
  obtain ⟨hybox, hy2⟩ := hy
  have h0 : |y 0 - c 0| < r := by simpa using hybox 0
  have h1 : |y 1 - c 1| < boxSide 1 * r := by simpa using hybox 1
  have h2 : |y 2 - c 2| < boxSide 2 * r := by simpa using hybox 2
  have h2hi : y 2 - c 2 < boxSide 2 * r := (abs_lt.mp h2).2
  have h2lo : s < y 2 - c 2 := by linarith
  have hshi : s < boxSide 2 * r := (abs_lt.mp hs).2
  have hb2 : boxSide 2 = 2 * b := two_mul_b.symm
  have key0 : |y 2 - (c + shiftV ((s + boxSide 2 * r) / 2)) 2| < b * r + |s| / 2 := by
    simp only [add_shiftV_two]
    rw [abs_lt]
    have hle : (boxSide 2 * r - s) / 2 ≤ b * r + |s| / 2 := by
      rw [hb2]; have := neg_le_abs s; linarith
    constructor <;> linarith
  have key1 : |y 0 - (c + shiftV ((s + boxSide 2 * r) / 2)) 0| <
      boxSide 1 * (b * r + |s| / 2) := by
    simp only [add_shiftV_zero]
    have hb1 : boxSide 1 * b = 1 := by rw [mul_comm, b_mul_boxSide_one]
    have hle : r ≤ boxSide 1 * (b * r + |s| / 2) := by
      nlinarith [hb1, boxSide_pos 1, hr, abs_nonneg s]
    linarith [abs_lt.mp h0]
  have key2 : |y 1 - (c + shiftV ((s + boxSide 2 * r) / 2)) 1| <
      boxSide 2 * (b * r + |s| / 2) := by
    simp only [add_shiftV_one]
    have hb : boxSide 2 * b = boxSide 1 := by rw [mul_comm, b_mul_boxSide_two]
    have hle : boxSide 1 * r ≤ boxSide 2 * (b * r + |s| / 2) := by
      have h : boxSide 2 * (b * r) = boxSide 1 * r := by rw [← mul_assoc, hb]
      nlinarith [h, boxSide_pos 2, hr, abs_nonneg s]
    linarith [abs_lt.mp h1]
  exact mem_PBox_cycPerm key0 key1 key2

end

end Submission
