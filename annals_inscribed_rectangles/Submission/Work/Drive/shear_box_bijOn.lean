import Mathlib
import Submission.Work.Drive.encodedShear

/-!
# `shear_box_bijOn`: the clamped cross-shear is a box self-bijection with face preservation

`Work.Drive.shear q` is the cross-shear of `encodedShear.lean`,
`(y₀, y₁) ↦ (y₀ + C(y₁) hb y₀, y₁ + D(y₀') hb y₁)` with
`C (t) = a₀ (1 - 2t) + a₂ hb t`, `D (t) = a₁ (1 - 2t) + a₃ hb t` and `a = ballClamp q`,
`‖a‖ < 1/2`.

This file proves that `shear q` is a bijection of the unit box onto itself preserving each face
(`shear q y i = 0 ↔ y i = 0`, `shear q y i = 1 ↔ y i = 1`) — exactly the `hbij`/`hface` data of
`Work.Drive.meet3Hyp_of_boxReparam`.

The mathematics is the elementary one-dimensional observation that for a *real* `c` with `|c| < 1`
the map `x ↦ x + c · hb x = x + c x (1 - x)` is a strictly increasing bijection of `[0,1]`
(difference quotient `(x' - x)(1 + c (1 - x - x'))` with `|1 - x - x'| ≤ 1`), whose only fixed
points of the boundary values are `0` and `1`.  The coefficient bound
`|a_i (1 - 2t) + a_j hb t| ≤ |a_i| + |a_j|/4 < 1/2 + 1/8 < 1` for `t ∈ [0,1]` is what makes the
clamping (`‖ballClamp q‖ < 1/2`) the right choice, and it is uniform in `q`.
-/

namespace Work.Drive

open Set

noncomputable section

/-! ## 1. The one-dimensional shear `x ↦ x + c · hb x` -/

/-- The difference quotient of the one-dimensional shear:
`f x' - f x = (x' - x) (1 + c (1 - x - x'))` for `f x = x + c · hb x`. -/
lemma shearBox_oneD_sub (c x x' : ℝ) :
    (x' + c * hb x') - (x + c * hb x) = (x' - x) * (1 + c * (1 - x - x')) := by
  simp only [hb]; ring

/-- For `|c| < 1` the one-dimensional shear `x ↦ x + c · hb x` is strictly increasing on `[0,1]`:
the difference quotient is `(x' - x)(1 + c(1 - x - x'))` with `x' - x > 0` and
`1 + c(1 - x - x') ≥ 1 - |c| > 0`. -/
lemma shearBox_oneD_strictMonoOn {c : ℝ} (hc : |c| < 1) :
    StrictMonoOn (fun x : ℝ => x + c * hb x) (Set.Icc (0 : ℝ) 1) := by
  intro x hx x' hx' hlt
  have h1 : |1 - x - x'| ≤ 1 := by
    rw [abs_le]; constructor <;> linarith [hx.1, hx.2, hx'.1, hx'.2]
  have h2 : |c * (1 - x - x')| < 1 := by
    rw [abs_mul]
    calc |c| * |1 - x - x'| ≤ |c| * 1 := mul_le_mul_of_nonneg_left h1 (abs_nonneg c)
      _ = |c| := by ring
      _ < 1 := hc
  have h3 : 0 < 1 + c * (1 - x - x') := by
    have h4 := (abs_lt.mp h2).1
    linarith
  have hpos : 0 < (x' + c * hb x') - (x + c * hb x) := by
    rw [shearBox_oneD_sub]
    exact mul_pos (by linarith) h3
  linarith

lemma shearBox_oneD_injOn {c : ℝ} (hc : |c| < 1) :
    InjOn (fun x : ℝ => x + c * hb x) (Set.Icc (0 : ℝ) 1) :=
  (shearBox_oneD_strictMonoOn hc).injOn

lemma shearBox_oneD_monotoneOn {c : ℝ} (hc : |c| < 1) :
    MonotoneOn (fun x : ℝ => x + c * hb x) (Set.Icc (0 : ℝ) 1) :=
  (shearBox_oneD_strictMonoOn hc).monotoneOn

/-- The one-dimensional shear maps `[0,1]` into itself: `f 0 = 0`, `f 1 = 1` and `f` is monotone. -/
lemma shearBox_oneD_mapsTo {c : ℝ} (hc : |c| < 1) :
    MapsTo (fun x : ℝ => x + c * hb x) (Set.Icc (0 : ℝ) 1) (Set.Icc (0 : ℝ) 1) := by
  intro x hx
  have hm := shearBox_oneD_monotoneOn hc
  exact ⟨by simpa using hm (by norm_num) hx hx.1, by simpa using hm hx (by norm_num) hx.2⟩

/-- The one-dimensional shear maps `[0,1]` **onto** `[0,1]`: it is continuous with `f 0 = 0`,
`f 1 = 1`, so the intermediate value theorem applies. -/
lemma shearBox_oneD_surjOn (c : ℝ) :
    SurjOn (fun x : ℝ => x + c * hb x) (Set.Icc (0 : ℝ) 1) (Set.Icc (0 : ℝ) 1) := by
  have hcont : Continuous (fun x : ℝ => x + c * hb x) := by
    simp only [hb]; fun_prop
  have hiv := intermediate_value_Icc (by norm_num : (0 : ℝ) ≤ 1) hcont.continuousOn
  intro t ht
  exact hiv (by simpa using ht)

/-- The one-dimensional shear vanishes at `x ∈ [0,1]` only at `x = 0`. -/
lemma shearBox_oneD_eq_zero_iff {c : ℝ} (hc : |c| < 1) {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    x + c * hb x = 0 ↔ x = 0 := by
  have h1 : |1 - x| ≤ 1 := by
    rw [abs_le]; constructor <;> linarith [hx.1, hx.2]
  have h2 : |c * (1 - x)| < 1 := by
    rw [abs_mul]
    calc |c| * |1 - x| ≤ |c| * 1 := mul_le_mul_of_nonneg_left h1 (abs_nonneg c)
      _ = |c| := by ring
      _ < 1 := hc
  have hne : (1 : ℝ) + c * (1 - x) ≠ 0 := by
    intro hh
    have : c * (1 - x) = -1 := by linarith
    rw [this] at h2
    norm_num at h2
  have hfac : x + c * hb x = x * (1 + c * (1 - x)) := by simp only [hb]; ring
  rw [hfac]
  constructor
  · intro h; exact (mul_eq_zero.mp h).resolve_right hne
  · intro h; rw [h]; ring

/-- The one-dimensional shear takes the value `1` at `x ∈ [0,1]` only at `x = 1`. -/
lemma shearBox_oneD_eq_one_iff {c : ℝ} (hc : |c| < 1) {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    x + c * hb x = 1 ↔ x = 1 := by
  have h1 : |x| ≤ 1 := by
    rw [abs_le]; constructor <;> linarith [hx.1, hx.2]
  have h2 : |c * x| < 1 := by
    rw [abs_mul]
    calc |c| * |x| ≤ |c| * 1 := mul_le_mul_of_nonneg_left h1 (abs_nonneg c)
      _ = |c| := by ring
      _ < 1 := hc
  have hne : (1 : ℝ) - c * x ≠ 0 := by
    intro hh
    have : c * x = 1 := by linarith
    rw [this] at h2
    norm_num at h2
  have hfac : (1 : ℝ) - (x + c * hb x) = (1 - x) * (1 - c * x) := by simp only [hb]; ring
  constructor
  · intro h
    have h0 : (1 - x) * (1 - c * x) = 0 := by rw [← hfac, h]; ring
    rcases mul_eq_zero.mp h0 with h' | h'
    · linarith
    · exact absurd h' hne
  · intro h; rw [h, hb_one]; ring

/-! ## 2. The coefficients of the two triangular factors and their uniform bound -/

/-- The coefficient of the first triangular factor `shear₁`. -/
def shearCoefA (q : EuclideanSpace ℝ (Fin 4)) (t : ℝ) : ℝ :=
  ballClamp q 0 * (1 - 2 * t) + ballClamp q 2 * hb t

/-- The coefficient of the second triangular factor `shear₂`. -/
def shearCoefB (q : EuclideanSpace ℝ (Fin 4)) (t : ℝ) : ℝ :=
  ballClamp q 1 * (1 - 2 * t) + ballClamp q 3 * hb t

/-- Every coordinate of the clamped parameter is `< 1/2` in absolute value. -/
lemma abs_ballClamp_coord_lt {n : ℕ} (q : EuclideanSpace ℝ (Fin n)) (i : Fin n) :
    |ballClamp q i| < 1 / 2 := by
  have h := PiLp.norm_apply_le (ballClamp q) i
  rw [Real.norm_eq_abs] at h
  exact lt_of_le_of_lt h (norm_ballClamp_lt q)

/-- **The coefficient bound.**  For `t ∈ [0,1]`, `|a (1 - 2t) + b hb t| < 1` whenever
`|a| < 1/2` and `|b| < 1/2`. -/
lemma abs_coef_lt (a b : ℝ) (ha : |a| < 1 / 2) (hb' : |b| < 1 / 2) {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) 1) : |a * (1 - 2 * t) + b * hb t| < 1 := by
  have h1 : |1 - 2 * t| ≤ 1 := by rw [abs_le]; constructor <;> linarith [ht.1, ht.2]
  have h3 : |hb t| ≤ 1 / 4 := by
    rw [abs_of_nonneg (hb_nonneg ht)]; exact hb_le t
  have hsum : |a * (1 - 2 * t) + b * hb t| ≤ |a| * |1 - 2 * t| + |b| * |hb t| :=
    calc |a * (1 - 2 * t) + b * hb t| ≤ |a * (1 - 2 * t)| + |b * hb t| := abs_add_le _ _
      _ = |a| * |1 - 2 * t| + |b| * |hb t| := by rw [abs_mul, abs_mul]
  have hA : |a| * |1 - 2 * t| ≤ |a| := by
    simpa using mul_le_mul_of_nonneg_left h1 (abs_nonneg a)
  have hB : |b| * |hb t| ≤ |b| * (1 / 4) := mul_le_mul_of_nonneg_left h3 (abs_nonneg b)
  have hB' : |b| * (1 / 4) < 1 / 8 := by linarith
  linarith

lemma abs_shearCoefA_lt (q : EuclideanSpace ℝ (Fin 4)) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    |shearCoefA q t| < 1 :=
  abs_coef_lt _ _ (abs_ballClamp_coord_lt q 0) (abs_ballClamp_coord_lt q 2) ht

lemma abs_shearCoefB_lt (q : EuclideanSpace ℝ (Fin 4)) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    |shearCoefB q t| < 1 :=
  abs_coef_lt _ _ (abs_ballClamp_coord_lt q 1) (abs_ballClamp_coord_lt q 3) ht

/-! ## 3. The coordinate formulas of the shears -/

lemma shear₁_coord_zero (q : EuclideanSpace ℝ (Fin 4)) (y : EuclideanSpace ℝ (Fin 2)) :
    shear₁ q y 0 = y 0 + shearCoefA q (y 1) * hb (y 0) := by
  simp only [shear₁_apply_zero, shearCoefA]

lemma shear₁_coord_one (q : EuclideanSpace ℝ (Fin 4)) (y : EuclideanSpace ℝ (Fin 2)) :
    shear₁ q y 1 = y 1 := shear₁_apply_one q y

lemma shear₂_coord_zero (q : EuclideanSpace ℝ (Fin 4)) (y : EuclideanSpace ℝ (Fin 2)) :
    shear₂ q y 0 = y 0 := shear₂_apply_zero q y

lemma shear₂_coord_one (q : EuclideanSpace ℝ (Fin 4)) (y : EuclideanSpace ℝ (Fin 2)) :
    shear₂ q y 1 = y 1 + shearCoefB q (y 0) * hb (y 1) := by
  simp only [shear₂_apply_one, shearCoefB]

lemma shear_coord_zero (q : EuclideanSpace ℝ (Fin 4)) (y : EuclideanSpace ℝ (Fin 2)) :
    shear q y 0 = y 0 + shearCoefA q (y 1) * hb (y 0) := by
  unfold shear
  simp only [shear₂_apply_zero, shear₁_coord_zero]

lemma shear_coord_one (q : EuclideanSpace ℝ (Fin 4)) (y : EuclideanSpace ℝ (Fin 2)) :
    shear q y 1 = y 1 + shearCoefB q (shear₁ q y 0) * hb (y 1) := by
  unfold shear
  simp only [shear₂_coord_one, shear₁_coord_one]

/-- Membership in the closed unit box, in the two coordinates. -/
lemma mem_unitBox1_iff (y : EuclideanSpace ℝ (Fin 2)) :
    y ∈ Submission.Drive.unitBox 1 ↔ y 0 ∈ Set.Icc (0 : ℝ) 1 ∧ y 1 ∈ Set.Icc (0 : ℝ) 1 := by
  have h : (∀ i : Fin 2, y i ∈ Set.Icc (0 : ℝ) 1) ↔
      y 0 ∈ Set.Icc (0 : ℝ) 1 ∧ y 1 ∈ Set.Icc (0 : ℝ) 1 := Fin.forall_fin_two
  exact h

/-! ## 4. The two triangular factors are box self-bijections -/

lemma shear₁_mapsTo (q : EuclideanSpace ℝ (Fin 4)) :
    MapsTo (shear₁ q) (Submission.Drive.unitBox 1) (Submission.Drive.unitBox 1) := by
  intro y hy
  rw [mem_unitBox1_iff] at hy ⊢
  obtain ⟨hy0, hy1⟩ := hy
  refine ⟨?_, ?_⟩
  · rw [shear₁_coord_zero]
    exact shearBox_oneD_mapsTo (abs_shearCoefA_lt q hy1) hy0
  · rw [shear₁_coord_one]; exact hy1

lemma shear₁_injOn (q : EuclideanSpace ℝ (Fin 4)) :
    InjOn (shear₁ q) (Submission.Drive.unitBox 1) := by
  intro y hy y' hy' heq
  have hy0 : y 0 ∈ Set.Icc (0 : ℝ) 1 := hy 0
  have hy1 : y 1 ∈ Set.Icc (0 : ℝ) 1 := hy 1
  have hy'0 : y' 0 ∈ Set.Icc (0 : ℝ) 1 := hy' 0
  have hy'1 : y' 1 ∈ Set.Icc (0 : ℝ) 1 := hy' 1
  have h1 : y 1 = y' 1 := by
    have h := congrArg (fun z : EuclideanSpace ℝ (Fin 2) => z 1) heq
    simpa only [shear₁_coord_one] using h
  have h0 : y 0 = y' 0 := by
    have h := congrArg (fun z : EuclideanSpace ℝ (Fin 2) => z 0) heq
    simp only [shear₁_coord_zero] at h
    rw [h1] at h
    exact shearBox_oneD_injOn (abs_shearCoefA_lt q hy'1) hy0 hy'0 h
  ext i
  fin_cases i
  · exact h0
  · exact h1

lemma shear₁_surjOn (q : EuclideanSpace ℝ (Fin 4)) :
    SurjOn (shear₁ q) (Submission.Drive.unitBox 1) (Submission.Drive.unitBox 1) := by
  intro w hw
  rw [mem_unitBox1_iff] at hw
  obtain ⟨hw0, hw1⟩ := hw
  obtain ⟨x, hx, hxeq⟩ := shearBox_oneD_surjOn (shearCoefA q (w 1)) hw0
  refine ⟨pt2 x (w 1), ?_, ?_⟩
  · rw [mem_unitBox1_iff]; exact ⟨hx, hw1⟩
  · have h0 : shear₁ q (pt2 x (w 1)) 0 = w 0 := by
      rw [shear₁_coord_zero, pt2_zero, pt2_one]; exact hxeq
    have h1 : shear₁ q (pt2 x (w 1)) 1 = w 1 := by
      rw [shear₁_coord_one, pt2_one]
    ext i
    fin_cases i
    · exact h0
    · exact h1

lemma shear₂_mapsTo (q : EuclideanSpace ℝ (Fin 4)) :
    MapsTo (shear₂ q) (Submission.Drive.unitBox 1) (Submission.Drive.unitBox 1) := by
  intro y hy
  rw [mem_unitBox1_iff] at hy ⊢
  obtain ⟨hy0, hy1⟩ := hy
  refine ⟨?_, ?_⟩
  · rw [shear₂_coord_zero]; exact hy0
  · rw [shear₂_coord_one]
    exact shearBox_oneD_mapsTo (abs_shearCoefB_lt q hy0) hy1

lemma shear₂_injOn (q : EuclideanSpace ℝ (Fin 4)) :
    InjOn (shear₂ q) (Submission.Drive.unitBox 1) := by
  intro y hy y' hy' heq
  have hy0 : y 0 ∈ Set.Icc (0 : ℝ) 1 := hy 0
  have hy1 : y 1 ∈ Set.Icc (0 : ℝ) 1 := hy 1
  have hy'0 : y' 0 ∈ Set.Icc (0 : ℝ) 1 := hy' 0
  have hy'1 : y' 1 ∈ Set.Icc (0 : ℝ) 1 := hy' 1
  have h0 : y 0 = y' 0 := by
    have h := congrArg (fun z : EuclideanSpace ℝ (Fin 2) => z 0) heq
    simpa only [shear₂_coord_zero] using h
  have h1 : y 1 = y' 1 := by
    have h := congrArg (fun z : EuclideanSpace ℝ (Fin 2) => z 1) heq
    simp only [shear₂_coord_one] at h
    rw [h0] at h
    exact shearBox_oneD_injOn (abs_shearCoefB_lt q hy'0) hy1 hy'1 h
  ext i
  fin_cases i
  · exact h0
  · exact h1

lemma shear₂_surjOn (q : EuclideanSpace ℝ (Fin 4)) :
    SurjOn (shear₂ q) (Submission.Drive.unitBox 1) (Submission.Drive.unitBox 1) := by
  intro w hw
  rw [mem_unitBox1_iff] at hw
  obtain ⟨hw0, hw1⟩ := hw
  obtain ⟨x, hx, hxeq⟩ := shearBox_oneD_surjOn (shearCoefB q (w 0)) hw1
  refine ⟨pt2 (w 0) x, ?_, ?_⟩
  · rw [mem_unitBox1_iff]; exact ⟨hw0, hx⟩
  · have h0 : shear₂ q (pt2 (w 0) x) 0 = w 0 := by
      rw [shear₂_coord_zero, pt2_zero]
    have h1 : shear₂ q (pt2 (w 0) x) 1 = w 1 := by
      rw [shear₂_coord_one, pt2_zero, pt2_one]; exact hxeq
    ext i
    fin_cases i
    · exact h0
    · exact h1

lemma shear₁_bijOn (q : EuclideanSpace ℝ (Fin 4)) :
    Set.BijOn (shear₁ q) (Submission.Drive.unitBox 1) (Submission.Drive.unitBox 1) :=
  ⟨shear₁_mapsTo q, shear₁_injOn q, shear₁_surjOn q⟩

lemma shear₂_bijOn (q : EuclideanSpace ℝ (Fin 4)) :
    Set.BijOn (shear₂ q) (Submission.Drive.unitBox 1) (Submission.Drive.unitBox 1) :=
  ⟨shear₂_mapsTo q, shear₂_injOn q, shear₂_surjOn q⟩

theorem shear_box_bijOn (q : EuclideanSpace ℝ (Fin 4)) :
    Set.BijOn (Work.Drive.shear q) (Submission.Drive.unitBox 1) (Submission.Drive.unitBox 1) ∧
    (∀ y : EuclideanSpace ℝ (Fin 2), y ∈ Submission.Drive.unitBox 1 → ∀ i : Fin 2,
      (Work.Drive.shear q y i = 0 ↔ y i = 0) ∧ (Work.Drive.shear q y i = 1 ↔ y i = 1)) := by
  refine ⟨(shear₂_bijOn q).comp (shear₁_bijOn q), ?_⟩
  intro y hy i
  have hy0 : y 0 ∈ Set.Icc (0 : ℝ) 1 := hy 0
  have hy1 : y 1 ∈ Set.Icc (0 : ℝ) 1 := hy 1
  have hz : shear₁ q y 0 ∈ Set.Icc (0 : ℝ) 1 := (shear₁_mapsTo q hy) 0
  have hA := abs_shearCoefA_lt q hy1
  have hB := abs_shearCoefB_lt q hz
  have e00 : shear q y 0 = 0 ↔ y 0 = 0 := by
    rw [shear_coord_zero]; exact shearBox_oneD_eq_zero_iff hA hy0
  have e01 : shear q y 0 = 1 ↔ y 0 = 1 := by
    rw [shear_coord_zero]; exact shearBox_oneD_eq_one_iff hA hy0
  have e10 : shear q y 1 = 0 ↔ y 1 = 0 := by
    rw [shear_coord_one]; exact shearBox_oneD_eq_zero_iff hB hy1
  have e11 : shear q y 1 = 1 ↔ y 1 = 1 := by
    rw [shear_coord_one]; exact shearBox_oneD_eq_one_iff hB hy1
  fin_cases i
  · exact ⟨e00, e01⟩
  · exact ⟨e10, e11⟩

end

end Work.Drive
