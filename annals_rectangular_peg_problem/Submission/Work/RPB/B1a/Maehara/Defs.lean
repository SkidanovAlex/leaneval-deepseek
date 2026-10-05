import Mathlib
import Submission.Work.RPB1a.Caratheodory.Brouwer.crossing_lemma_rect_complex
import Submission.Work.RPB1a.Caratheodory.Brouwer.exists_jordan_arcs
import Submission.Work.RPB1a.Caratheodory.Brouwer.exists_boundary_path

set_option linter.unusedVariables false

/-!
# The Maehara rectangle in `ℂ`, and elementary path tools

This file collects the vocabulary used by the Maehara proof of the existence of a bounded
component of the complement of a Jordan curve (see
`Work.RPB.B1a.exists_bounded_component_compl`):

* `RectC` is the rectangle `[-1,1] × [-2,2]` (in complex coordinates), `BdC` the union of its
  four supporting lines and `Vseg` the vertical segment `{re = 0} ∩ RectC`;
* `seg u v` is the straight segment from `u` to `v`, parametrised on `[-1,1]`;
* `arc P s t` is the piece of the parametrised curve `P` between the parameters `s` and `t`;
* `glue f g` concatenates two paths parametrised on `[-1,1]`.
-/

namespace Work.RPB.B1a

open Set Metric Complex

/-- The rectangle `[-1,1] × [-2,2]` of the complex plane. -/
def RectC : Set ℂ := {z | -1 ≤ z.re ∧ z.re ≤ 1 ∧ -2 ≤ z.im ∧ z.im ≤ 2}

/-- The union of the four supporting lines of `RectC`. -/
def BdC : Set ℂ := {z | z.re = -1 ∨ z.re = 1 ∨ z.im = -2 ∨ z.im = 2}

/-- The vertical segment through the origin with imaginary part in `[-2,2]`. -/
def Vseg : Set ℂ := {z | z.re = 0 ∧ -2 ≤ z.im ∧ z.im ≤ 2}

@[simp] theorem mem_RectC {z : ℂ} :
    z ∈ RectC ↔ -1 ≤ z.re ∧ z.re ≤ 1 ∧ -2 ≤ z.im ∧ z.im ≤ 2 := Iff.rfl

@[simp] theorem mem_BdC {z : ℂ} :
    z ∈ BdC ↔ z.re = -1 ∨ z.re = 1 ∨ z.im = -2 ∨ z.im = 2 := Iff.rfl

@[simp] theorem mem_Vseg {z : ℂ} :
    z ∈ Vseg ↔ z.re = 0 ∧ -2 ≤ z.im ∧ z.im ≤ 2 := Iff.rfl

theorem isClosed_RectC : IsClosed RectC := by
  rw [show RectC = {z : ℂ | -1 ≤ z.re} ∩ {z : ℂ | z.re ≤ 1} ∩ {z : ℂ | -2 ≤ z.im}
      ∩ {z : ℂ | z.im ≤ 2} from by ext z; simp [RectC, and_assoc]]
  exact (((isClosed_le continuous_const Complex.continuous_re).inter
    (isClosed_le Complex.continuous_re continuous_const)).inter
    (isClosed_le continuous_const Complex.continuous_im)).inter
    (isClosed_le Complex.continuous_im continuous_const)

theorem isClosed_BdC : IsClosed BdC := by
  rw [show BdC = {z : ℂ | z.re = -1} ∪ {z : ℂ | z.re = 1} ∪ {z : ℂ | z.im = -2}
      ∪ {z : ℂ | z.im = 2} from by ext z; simp [BdC, or_assoc]]
  exact (((isClosed_eq Complex.continuous_re continuous_const).union
    (isClosed_eq Complex.continuous_re continuous_const)).union
    (isClosed_eq Complex.continuous_im continuous_const)).union
    (isClosed_eq Complex.continuous_im continuous_const)

theorem isClosed_Vseg : IsClosed Vseg := by
  rw [show Vseg = {z : ℂ | z.re = 0} ∩ {z : ℂ | -2 ≤ z.im} ∩ {z : ℂ | z.im ≤ 2} from by
    ext z; simp [Vseg, and_assoc]]
  exact ((isClosed_eq Complex.continuous_re continuous_const).inter
    (isClosed_le continuous_const Complex.continuous_im)).inter
    (isClosed_le Complex.continuous_im continuous_const)

theorem isBounded_RectC : Bornology.IsBounded RectC := by
  refine (Metric.isBounded_iff_subset_ball (0 : ℂ)).mpr ⟨3, fun z hz => ?_⟩
  obtain ⟨h1, h2, h3, h4⟩ := mem_RectC.mp hz
  rw [Metric.mem_ball, dist_zero_right]
  have h5 : ‖z‖ ^ 2 ≤ 5 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    nlinarith
  nlinarith [norm_nonneg z, h5]

theorem convex_RectC : Convex ℝ RectC := by
  intro x hx y hy a b ha hb hab
  obtain ⟨hx1, hx2, hx3, hx4⟩ := mem_RectC.mp hx
  obtain ⟨hy1, hy2, hy3, hy4⟩ := mem_RectC.mp hy
  rw [mem_RectC]
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    · simp only [Complex.add_re, Complex.add_im, Complex.smul_re, Complex.smul_im, smul_eq_mul]
      nlinarith

/-! ## Straight segments -/

/-- The straight segment from `u` to `v`, parametrised on `[-1,1]` (and extended affinely
outside). -/
noncomputable def seg (u v : ℂ) : ℝ → ℂ := fun t => u + ((t + 1) / 2 : ℝ) • (v - u)

theorem continuous_seg (u v : ℂ) : Continuous (seg u v) := by
  unfold seg; fun_prop

theorem seg_apply (u v : ℂ) (t : ℝ) :
    seg u v t = (1 - (t + 1) / 2 : ℝ) • u + ((t + 1) / 2 : ℝ) • v := by
  simp only [seg]
  module

@[simp] theorem seg_neg_one (u v : ℂ) : seg u v (-1) = u := by
  simp [seg]

@[simp] theorem seg_one (u v : ℂ) : seg u v 1 = v := by
  simp [seg]

theorem seg_mem_of_mem {u v : ℂ} {s : Set ℂ} (hs : Convex ℝ s) (hu : u ∈ s) (hv : v ∈ s)
    {t : ℝ} (ht : t ∈ Set.Icc (-1 : ℝ) 1) : seg u v t ∈ s := by
  have h1 : (0:ℝ) ≤ (t + 1) / 2 := by linarith [ht.1]
  have h2 : (1:ℝ) - (t + 1) / 2 = 1 - (t + 1) / 2 := rfl
  have h4 : (0:ℝ) ≤ 1 - (t + 1) / 2 := by linarith [ht.2]
  have h3 : (1 - (t + 1) / 2) + (t + 1) / 2 = 1 := by ring
  have h := hs hu hv h4 h1 h3
  rw [seg_apply]
  exact h

theorem seg_re (u v : ℂ) (t : ℝ) :
    (seg u v t).re = (1 - (t + 1) / 2) * u.re + ((t + 1) / 2) * v.re := by
  simp only [seg_apply, Complex.add_re, Complex.smul_re, smul_eq_mul, Complex.sub_re]

theorem seg_im (u v : ℂ) (t : ℝ) :
    (seg u v t).im = (1 - (t + 1) / 2) * u.im + ((t + 1) / 2) * v.im := by
  simp only [seg_apply, Complex.add_im, Complex.smul_im, smul_eq_mul, Complex.sub_im]

/-! ## Pieces of a parametrised curve -/

/-- The piece of the parametrised curve `P` between the parameters `s` and `t`, parametrised on
`[-1,1]`. -/
noncomputable def arc (P : ℝ → ℂ) (s t : ℝ) : ℝ → ℂ :=
  fun r => P (s + ((r + 1) / 2 : ℝ) * (t - s))

theorem continuous_arc {P : ℝ → ℂ} (hP : Continuous P) (s t : ℝ) : Continuous (arc P s t) := by
  unfold arc; exact hP.comp (by fun_prop)

@[simp] theorem arc_neg_one (P : ℝ → ℂ) (s t : ℝ) : arc P s t (-1) = P s := by
  simp [arc]

@[simp] theorem arc_one (P : ℝ → ℂ) (s t : ℝ) : arc P s t 1 = P t := by
  simp [arc]

theorem arc_mem_range (P : ℝ → ℂ) (s t r : ℝ) : arc P s t r ∈ Set.range P := ⟨_, rfl⟩

theorem arc_eq (P : ℝ → ℂ) (s t r : ℝ) :
    arc P s t r = P (s + ((r + 1) / 2 : ℝ) * (t - s)) := rfl

theorem arc_arg_mem_Icc {s t r : ℝ} (hr : r ∈ Set.Icc (-1 : ℝ) 1) (hst : s ≤ t) :
    s + ((r + 1) / 2 : ℝ) * (t - s) ∈ Set.Icc s t := by
  constructor
  · nlinarith [hr.1, hr.2]
  · nlinarith [hr.1, hr.2]

/-! ## Concatenation of two parametrised paths -/

/-- Concatenation of two paths `f`, `g : ℝ → ℂ` parametrised on `[-1,1]`: the first half of
`[-1,1]` runs through `f` (from `f (-1)` to `f 1`) and the second half through `g` (from `g (-1)`
to `g 1`). -/
noncomputable def glue (f g : ℝ → ℂ) (h : f 1 = g (-1)) : ℝ → ℂ :=
  fun t => if t ≤ 0 then f (2 * t + 1) else g (2 * t - 1)

theorem frontier_Iic_zero : frontier {x : ℝ | x ≤ 0} = {0} := by
  rw [show {x : ℝ | x ≤ 0} = Set.Iic (0:ℝ) from rfl, frontier_Iic]

theorem continuous_glue {f g : ℝ → ℂ} (hf : Continuous f) (hg : Continuous g) (h : f 1 = g (-1)) :
    Continuous (glue f g h) := by
  have hfront : ∀ a ∈ frontier {x : ℝ | x ≤ 0}, f (2 * a + 1) = g (2 * a - 1) := by
    intro a ha
    have ha0 : a = 0 := by
      rw [frontier_Iic_zero] at ha
      simpa using ha
    subst ha0
    norm_num
    exact h
  refine continuous_if hfront ?_ ?_ <;>
    · refine Continuous.continuousOn ?_ <;> fun_prop

@[simp] theorem glue_neg_one {f g : ℝ → ℂ} (h : f 1 = g (-1)) : glue f g h (-1) = f (-1) := by
  rw [glue, ite_eq_left (by norm_num : (-1:ℝ) ≤ 0)]
  norm_num

@[simp] theorem glue_one {f g : ℝ → ℂ} (h : f 1 = g (-1)) : glue f g h 1 = g 1 := by
  rw [glue, ite_eq_right (by norm_num : ¬ ((1:ℝ) ≤ 0))]
  norm_num

theorem glue_mem {F : Set ℂ} {f g : ℝ → ℂ} (h : f 1 = g (-1))
    (hf : ∀ t ∈ Set.Icc (-1 : ℝ) 1, f t ∈ F) (hg : ∀ t ∈ Set.Icc (-1 : ℝ) 1, g t ∈ F) :
    ∀ t ∈ Set.Icc (-1 : ℝ) 1, glue f g h t ∈ F := by
  intro t ht
  by_cases hc : t ≤ 0
  · rw [glue, ite_eq_left hc]
    apply hf
    constructor <;> linarith [ht.1, ht.2]
  · rw [glue, ite_eq_right hc]
    apply hg
    constructor <;> linarith [ht.1, ht.2]

theorem glue_notMem {B : Set ℂ} {f g : ℝ → ℂ} (h : f 1 = g (-1))
    (hf : ∀ t ∈ Set.Icc (-1 : ℝ) 1, f t ∉ B) (hg : ∀ t ∈ Set.Icc (-1 : ℝ) 1, g t ∉ B) :
    ∀ t ∈ Set.Icc (-1 : ℝ) 1, glue f g h t ∉ B :=
  glue_mem (F := Bᶜ) h hf hg

/-! ## Paths parametrised on `[-1,1]` -/

/-- A `Path` reparametrised on `[-1,1]`, running from its source (at `-1`) to its target (at
`1`). -/
noncomputable def pathOn {a b : ℂ} (p : Path a b) : ℝ → ℂ := fun t => p.extend ((t + 1) / 2)

/-- The reverse of a `Path`, reparametrised on `[-1,1]`. -/
noncomputable def pathOnRev {a b : ℂ} (p : Path a b) : ℝ → ℂ := fun t => p.extend ((1 - t) / 2)

theorem continuous_pathOn {a b : ℂ} (p : Path a b) : Continuous (pathOn p) :=
  p.continuous_extend.comp (by fun_prop)

theorem continuous_pathOnRev {a b : ℂ} (p : Path a b) : Continuous (pathOnRev p) :=
  p.continuous_extend.comp (by fun_prop)

@[simp] theorem pathOn_neg_one {a b : ℂ} (p : Path a b) : pathOn p (-1) = a := by
  simp [pathOn]

@[simp] theorem pathOn_one {a b : ℂ} (p : Path a b) : pathOn p 1 = b := by
  simp [pathOn]

@[simp] theorem pathOnRev_neg_one {a b : ℂ} (p : Path a b) : pathOnRev p (-1) = b := by
  simp [pathOnRev]

@[simp] theorem pathOnRev_one {a b : ℂ} (p : Path a b) : pathOnRev p 1 = a := by
  simp [pathOnRev]

theorem pathOn_mem {a b : ℂ} {S : Set ℂ} (p : Path a b) (h : ∀ t, p t ∈ S) :
    ∀ t ∈ Set.Icc (-1 : ℝ) 1, pathOn p t ∈ S := by
  intro t ht
  have ht' : (t + 1) / 2 ∈ Set.Icc (0:ℝ) 1 := ⟨by linarith [ht.1], by linarith [ht.2]⟩
  rw [pathOn, Path.extend_apply p ht']
  exact h _

theorem pathOnRev_mem {a b : ℂ} {S : Set ℂ} (p : Path a b) (h : ∀ t, p t ∈ S) :
    ∀ t ∈ Set.Icc (-1 : ℝ) 1, pathOnRev p t ∈ S := by
  intro t ht
  have ht' : (1 - t) / 2 ∈ Set.Icc (0:ℝ) 1 := ⟨by linarith [ht.2], by linarith [ht.1]⟩
  rw [pathOnRev, Path.extend_apply p ht']
  exact h _

theorem pathOn_notMem {a b : ℂ} {B : Set ℂ} (p : Path a b) (h : ∀ t, p t ∉ B) :
    ∀ t ∈ Set.Icc (-1 : ℝ) 1, pathOn p t ∉ B :=
  pathOn_mem (S := Bᶜ) p h

theorem pathOnRev_notMem {a b : ℂ} {B : Set ℂ} (p : Path a b) (h : ∀ t, p t ∉ B) :
    ∀ t ∈ Set.Icc (-1 : ℝ) 1, pathOnRev p t ∉ B :=
  pathOnRev_mem (S := Bᶜ) p h

/-! ## The vertical parametrisation of the rectangle -/

/-- The point `(0, 2t)`, parametrising the vertical middle segment of the rectangle. -/
noncomputable def vertPt (t : ℝ) : ℂ := ((2 * t : ℝ) : ℂ) * Complex.I

@[simp] theorem vertPt_re (t : ℝ) : (vertPt t).re = 0 := by simp [vertPt]

@[simp] theorem vertPt_im (t : ℝ) : (vertPt t).im = 2 * t := by simp [vertPt]

theorem continuous_vertPt : Continuous vertPt := by
  unfold vertPt; fun_prop

theorem vertPt_mem_RectC {t : ℝ} (ht : t ∈ Set.Icc (-1 : ℝ) 1) : vertPt t ∈ RectC := by
  rw [mem_RectC, vertPt_re, vertPt_im]
  exact ⟨by norm_num, by norm_num, by linarith [ht.1], by linarith [ht.2]⟩

end Work.RPB.B1a
