import Mathlib

/-!
# The chord geometry of the unit disc: definitions and elementary API

This file is the *geometry half* of the planar Jordan–Schoenflies chapter of the workspace
(`Submission/Work/Smooth/Schoenflies/`).  It has no dependency beyond Mathlib, so that the
elementary plane geometry below can be proved and used independently of the analytic chapters.

For two distinct points `x`, `y` of the unit circle:

* `chordFun x y z` — the (affine) linear functional `z ↦ det (y - x) (z - x)`, whose zero set is
  the line through `x` and `y`;
* `chord x y` — the **chord**: the intersection of the closed unit disc with that line;
* `capPos x y`, `capNeg x y` — the two **caps**: the parts of the open unit disc on the two sides of
  the chord;
* `arcPos x y`, `arcNeg x y` — the two **arcs**: the parts of the unit circle on the two sides.

The choice of describing the sides by the *linear* functional `chordFun` (rather than by angles)
makes both caps *convex* (each is the intersection of the unit ball with an open half-plane) and
both arcs intersections of the circle with an open half-plane, which is what the boundary
correspondence argument of `Work.Smooth.Schoenflies.Injectivity` needs.
-/

open Set Metric
open scoped Topology

namespace Work.Smooth.Schoenflies

noncomputable section

/-! ## The oriented area -/

/-- The **oriented area** `det a b = a.re * b.im - a.im * b.re` of the parallelogram spanned by
`a` and `b`.  (In the sibling chapters this is `detV`; it is repeated here so that this file depends
on Mathlib only.) -/
def det (a b : ℂ) : ℝ := ((starRingEnd ℂ) a * b).im

theorem det_apply (a b : ℂ) : det a b = a.re * b.im - a.im * b.re := by
  rw [det, Complex.mul_im, Complex.conj_re, Complex.conj_im]
  ring

@[simp] theorem det_self (a : ℂ) : det a a = 0 := by
  rw [det_apply]; ring

@[simp] theorem det_zero_left (b : ℂ) : det 0 b = 0 := by
  rw [det_apply]; simp

@[simp] theorem det_zero_right (a : ℂ) : det a 0 = 0 := by
  rw [det_apply]; simp

theorem det_add_right (a b c : ℂ) : det a (b + c) = det a b + det a c := by
  rw [det_apply, det_apply, det_apply]; simp only [Complex.add_re, Complex.add_im]; ring

theorem det_sub_right (a b c : ℂ) : det a (b - c) = det a b - det a c := by
  have h := det_add_right a (b - c) c
  rw [sub_add_cancel] at h
  linarith

theorem det_smul_right (r : ℝ) (a b : ℂ) : det a ((r : ℂ) * b) = r * det a b := by
  rw [det_apply, det_apply]; simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero]; ring

theorem det_neg_right (a b : ℂ) : det a (-b) = -det a b := by
  rw [det_apply, det_apply]; simp only [Complex.neg_re, Complex.neg_im]; ring

theorem det_swap (a b : ℂ) : det b a = -det a b := by
  rw [det_apply, det_apply]; ring

/-- Cauchy–Schwarz for the determinant: it is an area. -/
theorem abs_det_le (a b : ℂ) : |det a b| ≤ ‖a‖ * ‖b‖ := by
  rw [det, ← norm_star a, ← norm_mul]
  exact Complex.abs_im_le_norm _

/-! ## The chord functional -/

/-- The **chord functional** of the pair `(x,y)`: `z ↦ det (y - x) (z - x)`, the oriented area of
the triangle `x z y`.  It is affine in `z` and vanishes exactly on the line through `x` and `y`. -/
def chordFun (x y z : ℂ) : ℝ := det (y - x) (z - x)

theorem chordFun_eq (x y z : ℂ) : chordFun x y z = det (y - x) (z - x) := rfl

@[simp] theorem chordFun_x (x y : ℂ) : chordFun x y x = 0 := by
  simp [chordFun]

@[simp] theorem chordFun_y (x y : ℂ) : chordFun x y y = 0 := by
  simp [chordFun]

/-- The chord functional is affine in its third argument. -/
theorem chordFun_affine (x y : ℂ) (t : ℝ) (z w : ℂ) :
    chordFun x y (((1 - t : ℝ) : ℂ) * z + ((t : ℝ) : ℂ) * w) =
      (1 - t) * chordFun x y z + t * chordFun x y w := by
  have h : ((1 - t : ℝ) : ℂ) * z + ((t : ℝ) : ℂ) * w - x
      = ((1 - t : ℝ) : ℂ) * (z - x) + ((t : ℝ) : ℂ) * (w - x) := by
    push_cast
    ring
  rw [chordFun, chordFun, chordFun, h, det_add_right, det_smul_right, det_smul_right]

theorem continuous_chordFun (x y : ℂ) : Continuous (fun z : ℂ => chordFun x y z) := by
  simp only [chordFun, det_apply]
  fun_prop

/-! ## The segment -/

/-- The point `(1-t) x + t y` of the segment from `x` to `y`. -/
def segPoint (t : ℝ) (x y : ℂ) : ℂ := ((1 - t : ℝ) : ℂ) * x + ((t : ℝ) : ℂ) * y

/-- The closed segment from `x` to `y`. -/
def seg (x y : ℂ) : Set ℂ := (fun t : ℝ => segPoint t x y) '' Set.Icc (0 : ℝ) 1

@[simp] theorem segPoint_zero (x y : ℂ) : segPoint 0 x y = x := by simp [segPoint]

@[simp] theorem segPoint_one (x y : ℂ) : segPoint 1 x y = y := by simp [segPoint]

theorem mem_seg_iff {x y z : ℂ} : z ∈ seg x y ↔ ∃ t ∈ Set.Icc (0 : ℝ) 1, segPoint t x y = z :=
  Iff.rfl

theorem left_mem_seg (x y : ℂ) : x ∈ seg x y := ⟨0, by norm_num, by simp⟩

theorem right_mem_seg (x y : ℂ) : y ∈ seg x y := ⟨1, by norm_num, by simp⟩

theorem continuous_segPoint (x y : ℂ) : Continuous fun t : ℝ => segPoint t x y := by
  simp only [segPoint]
  fun_prop

theorem segPoint_injOn {x y : ℂ} (hxy : x ≠ y) :
    Set.InjOn (fun t : ℝ => segPoint t x y) (Set.Icc (0 : ℝ) 1) := by
  intro s _ t _ hst
  have h2 : ((s - t : ℝ) : ℂ) * (y - x) = 0 := by
    have h' : segPoint s x y - segPoint t x y = 0 := sub_eq_zero.mpr hst
    have key : segPoint s x y - segPoint t x y = ((s - t : ℝ) : ℂ) * (y - x) := by
      rw [segPoint, segPoint]; push_cast; ring
    rw [key] at h'
    exact h'
  rcases mul_eq_zero.mp h2 with h3 | h4
  · have h3' : (s - t : ℝ) = 0 := Complex.ofReal_eq_zero.mp h3
    linarith
  · exact absurd (sub_eq_zero.mp h4).symm hxy

theorem seg_subset_closedBall {x y : ℂ} (hx : ‖x‖ ≤ 1) (hy : ‖y‖ ≤ 1) :
    seg x y ⊆ Metric.closedBall (0 : ℂ) 1 := by
  rintro z ⟨t, ht, rfl⟩
  rw [Metric.mem_closedBall, dist_zero_right]
  calc ‖segPoint t x y‖ ≤ (1 - t) * ‖x‖ + t * ‖y‖ := by
        rw [segPoint]
        refine le_trans (norm_add_le _ _) (add_le_add ?_ ?_)
        · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith [ht.2])]
        · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht.1]
    _ ≤ (1 - t) * 1 + t * 1 :=
        add_le_add (mul_le_mul_of_nonneg_left hx (by linarith [ht.2]))
          (mul_le_mul_of_nonneg_left hy ht.1)
    _ = 1 := by ring

/-! ## The chord, the caps and the arcs -/

/-- The **chord** through `x` and `y`: the intersection of the closed unit disc with the line
through `x` and `y`. -/
def chord (x y : ℂ) : Set ℂ := {z | z ∈ Metric.closedBall (0 : ℂ) 1 ∧ chordFun x y z = 0}

/-- The **positive cap**: the part of the open unit disc on the positive side of the chord. -/
def capPos (x y : ℂ) : Set ℂ := {z | z ∈ Metric.ball (0 : ℂ) 1 ∧ 0 < chordFun x y z}

/-- The **negative cap**. -/
def capNeg (x y : ℂ) : Set ℂ := {z | z ∈ Metric.ball (0 : ℂ) 1 ∧ chordFun x y z < 0}

/-- The **positive arc**: the part of the unit circle on the positive side of the chord. -/
def arcPos (x y : ℂ) : Set ℂ := {z | z ∈ Metric.sphere (0 : ℂ) 1 ∧ 0 < chordFun x y z}

/-- The **negative arc**. -/
def arcNeg (x y : ℂ) : Set ℂ := {z | z ∈ Metric.sphere (0 : ℂ) 1 ∧ chordFun x y z < 0}

theorem capPos_def (x y : ℂ) :
    capPos x y = Metric.ball (0 : ℂ) 1 ∩ {z | 0 < chordFun x y z} := rfl

theorem capNeg_def (x y : ℂ) :
    capNeg x y = Metric.ball (0 : ℂ) 1 ∩ {z | chordFun x y z < 0} := rfl

theorem arcPos_def (x y : ℂ) :
    arcPos x y = Metric.sphere (0 : ℂ) 1 ∩ {z | 0 < chordFun x y z} := rfl

theorem arcNeg_def (x y : ℂ) :
    arcNeg x y = Metric.sphere (0 : ℂ) 1 ∩ {z | chordFun x y z < 0} := rfl

theorem isOpen_capPos (x y : ℂ) : IsOpen (capPos x y) :=
  isOpen_ball.inter (isOpen_lt continuous_const (continuous_chordFun x y))

theorem isOpen_capNeg (x y : ℂ) : IsOpen (capNeg x y) :=
  isOpen_ball.inter (isOpen_lt (continuous_chordFun x y) continuous_const)

/-- The chord functional in linear form: `chordFun x y z = det (y - x) z - det (y - x) x`. -/
theorem chordFun_eq_sub (x y z : ℂ) :
    chordFun x y z = det (y - x) z - det (y - x) x := by
  rw [chordFun_eq, det_sub_right]

/-- The set where the chord functional is positive is an open half-plane, hence convex. -/
theorem convex_chordPos (x y : ℂ) : Convex ℝ {z : ℂ | 0 < chordFun x y z} := by
  have hlin : IsLinearMap ℝ (fun z : ℂ => det (y - x) z) := by
    refine ⟨fun a b => det_add_right _ _ _, fun c a => ?_⟩
    rw [Complex.real_smul, det_smul_right, smul_eq_mul]
  have hset : {z : ℂ | 0 < chordFun x y z} = {z : ℂ | det (y - x) x < det (y - x) z} := by
    ext z
    change 0 < chordFun x y z ↔ det (y - x) x < det (y - x) z
    rw [chordFun_eq_sub]
    constructor <;> intro h <;> linarith
  rw [hset]
  exact convex_halfSpace_gt hlin _

/-- The set where the chord functional is negative is an open half-plane, hence convex. -/
theorem convex_chordNeg (x y : ℂ) : Convex ℝ {z : ℂ | chordFun x y z < 0} := by
  have hlin : IsLinearMap ℝ (fun z : ℂ => det (y - x) z) := by
    refine ⟨fun a b => det_add_right _ _ _, fun c a => ?_⟩
    rw [Complex.real_smul, det_smul_right, smul_eq_mul]
  have hset : {z : ℂ | chordFun x y z < 0} = {z : ℂ | det (y - x) z < det (y - x) x} := by
    ext z
    change chordFun x y z < 0 ↔ det (y - x) z < det (y - x) x
    rw [chordFun_eq_sub]
    constructor <;> intro h <;> linarith
  rw [hset]
  exact convex_halfSpace_lt hlin _

/-- Each cap is the intersection of the unit ball with an open half-plane, hence convex. -/
theorem convex_capPos (x y : ℂ) : Convex ℝ (capPos x y) :=
  (convex_ball (0 : ℂ) 1).inter (convex_chordPos x y)

theorem convex_capNeg (x y : ℂ) : Convex ℝ (capNeg x y) :=
  (convex_ball (0 : ℂ) 1).inter (convex_chordNeg x y)

theorem isPreconnected_capPos (x y : ℂ) : IsPreconnected (capPos x y) :=
  (convex_capPos x y).isPreconnected

theorem isPreconnected_capNeg (x y : ℂ) : IsPreconnected (capNeg x y) :=
  (convex_capNeg x y).isPreconnected

theorem disjoint_capPos_capNeg (x y : ℂ) : Disjoint (capPos x y) (capNeg x y) := by
  rw [Set.disjoint_left]
  intro z hz hz'
  linarith [hz.2, hz'.2]

/-- The open unit disc is the disjoint union of the two caps and the part of the chord inside it. -/
theorem ball_eq_capPos_union_capNeg (x y : ℂ) :
    Metric.ball (0 : ℂ) 1
      = capPos x y ∪ capNeg x y ∪ (chord x y ∩ Metric.ball (0 : ℂ) 1) := by
  ext z
  constructor
  · intro hz
    rcases lt_trichotomy (chordFun x y z) 0 with h | h | h
    · exact Or.inl (Or.inr ⟨hz, h⟩)
    · exact Or.inr ⟨⟨Metric.ball_subset_closedBall hz, h⟩, hz⟩
    · exact Or.inl (Or.inl ⟨hz, h⟩)
  · rintro ((hz | hz) | ⟨⟨_, _⟩, hz⟩)
    · exact hz.1
    · exact hz.1
    · exact hz

end

end Work.Smooth.Schoenflies
