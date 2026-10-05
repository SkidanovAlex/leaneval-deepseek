import Mathlib
import Submission.Work.RPCore.GenFun.Basic

/-!
# The complement of the support slab is preconnected

This file proves the "chapter lemma" `Work.RPCore.GenFun.slab_preconnected`: the complement of
the support slab of a compactly supported Hamiltonian,
`{y : PS | R < |y.1.1| + |y.2.1| + |y.2.2|} = (Work.RPCore.slab R)ᶜ`,
is preconnected.  This is what legitimises the normalisation in the generating-function route:
a function whose gradient vanishes on the complement of a compact set is locally constant, hence
constant on a preconnected open piece, so the primitive of a closed vector field can be
normalised to vanish "at infinity" (see `Work.RPCore.GenFun.rayPrimitive`).

The mathematics.  Write `S y = |y.1.1| + |y.2.1| + |y.2.2|`.  The set is the complement of the
`ℓ¹`-ball in the three coordinates `(q₁,p₁,p₂)` (with `q₂` free); such a set is connected as soon
as at least two coordinates are involved (indeed every point has one nonnegative and one
nonpositive coordinate), and the argument here is a two-piece star-shapedness:

* the half `A = {y | 0 ≤ y.1.1 ∧ R < S y}` is star-shaped with respect to `p₊ = ((M,0),(0,0))`,
  where `M = max (R+1) 1 > R`;
* the half `B = {y | y.1.1 ≤ 0 ∧ R < S y}` is star-shaped with respect to `p₋ = ((-M,0),(0,0))`.

A star-shaped set is preconnected (it is the union of the segments joining its centre to its
points; each segment is convex, hence preconnected, and they all contain the centre), and
`A ∩ B ∋ slabMid R = ((0,0),(R+1,0))` is nonempty; hence `A ∪ B = {R < S}`, a union of two
preconnected sets that meet, is preconnected.

The choice `M = max (R+1) 1` removes any case distinction on the sign of `R`: each centre lies in
its own half (`M > R` always, because `M ≥ R + 1 > R`, and `M ≥ 0`), and both halves are
star-shaped whatever the sign of `R`.
-/

set_option autoImplicit false

noncomputable section

namespace Work.RPCore.GenFun

open Work.RPV

/-- The "slab radius" `|q₁| + |p₁| + |p₂| : PS → ℝ`, i.e. the function whose sublevel set is the
support slab `Work.RPCore.slab`. -/
def slabFun (y : PS) : ℝ := |y.1.1| + |y.2.1| + |y.2.2|

/-- The auxiliary radius `max (R+1) 1`, always `> R` and `≥ 0`. -/
def slabAux (R : ℝ) : ℝ := max (R+1) 1

/-- Centre of the star-shapedness of the half `{0 ≤ q₁}`. -/
def slabPos (R : ℝ) : PS := ((slabAux R, 0), (0, 0))

/-- Centre of the star-shapedness of the half `{q₁ ≤ 0}`. -/
def slabNeg (R : ℝ) : PS := ((-(slabAux R), 0), (0, 0))

/-- The common point of the two halves. -/
def slabMid (R : ℝ) : PS := ((0, 0), (R + 1, 0))

theorem slabAux_nonneg (R : ℝ) : 0 ≤ slabAux R := le_trans zero_le_one (le_max_right _ _)

theorem lt_slabAux (R : ℝ) : R < slabAux R := lt_of_lt_of_le (by linarith) (le_max_left _ _)

theorem slabFun_nonneg (y : PS) : 0 ≤ slabFun y := by
  simp only [slabFun]; positivity

/-- **Convex-combination strictness.**  A convex combination of two numbers both `> R` is `> R`. -/
theorem slab_combo_gt (R cy MR a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1)
    (hM : R < MR) (hcy : R < cy) : R < a * MR + b * cy := by
  have hAB : a * R + b * R = R := by rw [← add_mul, hab, one_mul]
  rw [← hAB]
  have h2 : a * R ≤ a * MR := mul_le_mul_of_nonneg_left (le_of_lt hM) ha
  rcases eq_or_lt_of_le hb with hb0 | hbpos
  · subst hb0
    have ha1 : a = 1 := by linarith
    subst ha1
    simpa using hM
  · have h1 : b * R < b * cy := mul_lt_mul_of_pos_left hcy hbpos
    linarith

theorem lt_slabFun_slabMid (R : ℝ) : R < slabFun (slabMid R) := by
  have h : slabFun (slabMid R) = |R + 1| := by simp [slabFun, slabMid]
  rw [h]
  rcases lt_or_ge 0 (R + 1) with h' | h'
  · rw [abs_of_nonneg (le_of_lt h')]; linarith
  · rw [abs_of_nonpos h']; linarith

/-- The exact computation of `slabFun` along a segment from `slabPos R`, for points with
nonnegative first coordinate. -/
theorem slabFun_smul_slabPos (R : ℝ) (y : PS) (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hy1 : 0 ≤ y.1.1) :
    slabFun (a • slabPos R + b • y) = a * slabAux R + b * slabFun y := by
  have hM : 0 ≤ slabAux R := slabAux_nonneg R
  have hnn : 0 ≤ a * slabAux R + b * y.1.1 := by nlinarith [ha, hb, hy1, hM]
  have h1 : slabFun y = y.1.1 + |y.2.1| + |y.2.2| := by rw [slabFun, abs_of_nonneg hy1]
  rw [h1]
  simp only [slabFun]
  have e1 : (a • slabPos R + b • y).1.1 = a * (slabAux R) + b * y.1.1 := by simp [slabPos]
  have e2 : (a • slabPos R + b • y).2.1 = b * y.2.1 := by simp [slabPos]
  have e3 : (a • slabPos R + b • y).2.2 = b * y.2.2 := by simp [slabPos]
  rw [e1, e2, e3, abs_of_nonneg hnn, abs_mul, abs_mul, abs_of_nonneg hb]
  ring

/-- The exact computation of `slabFun` along a segment from `slabNeg R`, for points with
nonpositive first coordinate. -/
theorem slabFun_smul_slabNeg (R : ℝ) (y : PS) (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hy1 : y.1.1 ≤ 0) :
    slabFun (a • slabNeg R + b • y) = a * slabAux R + b * slabFun y := by
  have hM : 0 ≤ slabAux R := slabAux_nonneg R
  have hnn : a * (-(slabAux R)) + b * y.1.1 ≤ 0 := by nlinarith [ha, hb, hy1, hM]
  have h1 : slabFun y = -y.1.1 + |y.2.1| + |y.2.2| := by rw [slabFun, abs_of_nonpos hy1]
  rw [h1]
  simp only [slabFun]
  have e1 : (a • slabNeg R + b • y).1.1 = a * (-(slabAux R)) + b * y.1.1 := by simp [slabNeg]
  have e2 : (a • slabNeg R + b • y).2.1 = b * y.2.1 := by simp [slabNeg]
  have e3 : (a • slabNeg R + b • y).2.2 = b * y.2.2 := by simp [slabNeg]
  rw [e1, e2, e3, abs_of_nonpos hnn, abs_mul, abs_mul, abs_of_nonneg hb]
  ring

/-- The half `{0 ≤ q₁}` of the complement of the slab is star-shaped. -/
theorem starConvex_slab_ge (R : ℝ) :
    StarConvex ℝ (slabPos R) {y : PS | 0 ≤ y.1.1 ∧ R < slabFun y} := by
  intro y hy a b ha hb hab
  obtain ⟨hy1, hyS⟩ := hy
  have hM : 0 ≤ slabAux R := slabAux_nonneg R
  refine ⟨?_, ?_⟩
  · rw [show (a • slabPos R + b • y).1.1 = a * slabAux R + b * y.1.1 from by simp [slabPos]]
    nlinarith [ha, hb, hy1, hM]
  · rw [slabFun_smul_slabPos R y a b ha hb hy1]
    exact slab_combo_gt R (slabFun y) (slabAux R) a b ha hb hab (lt_slabAux R) hyS

/-- The half `{q₁ ≤ 0}` of the complement of the slab is star-shaped. -/
theorem starConvex_slab_le (R : ℝ) :
    StarConvex ℝ (slabNeg R) {y : PS | y.1.1 ≤ 0 ∧ R < slabFun y} := by
  intro y hy a b ha hb hab
  obtain ⟨hy1, hyS⟩ := hy
  have hM : 0 ≤ slabAux R := slabAux_nonneg R
  refine ⟨?_, ?_⟩
  · rw [show (a • slabNeg R + b • y).1.1 = a * (-(slabAux R)) + b * y.1.1 from by simp [slabNeg]]
    nlinarith [ha, hb, hy1, hM]
  · rw [slabFun_smul_slabNeg R y a b ha hb hy1]
    exact slab_combo_gt R (slabFun y) (slabAux R) a b ha hb hab (lt_slabAux R) hyS

/-- A star-shaped set in `PS` is preconnected: it is the union of the segments joining the centre
to its points, which are convex and share the centre. -/
theorem isPreconnected_of_starConvex {s : Set PS} {a : PS} (h : StarConvex ℝ a s) :
    IsPreconnected s :=
  isPreconnected_of_forall a fun y hy =>
    ⟨segment ℝ a y, h.segment_subset hy, left_mem_segment ℝ a y, right_mem_segment ℝ a y,
     (convex_segment (𝕜 := ℝ) a y).isPreconnected⟩

theorem slabMid_mem_ge (R : ℝ) : slabMid R ∈ {y : PS | 0 ≤ y.1.1 ∧ R < slabFun y} :=
  ⟨le_refl 0, lt_slabFun_slabMid R⟩

theorem slabMid_mem_le (R : ℝ) : slabMid R ∈ {y : PS | y.1.1 ≤ 0 ∧ R < slabFun y} :=
  ⟨le_refl 0, lt_slabFun_slabMid R⟩

/-- **The complement of the support slab is preconnected.** -/
theorem slab_preconnected (R : ℝ) :
    IsPreconnected {y : Work.RPV.PS | R < |y.1.1| + |y.2.1| + |y.2.2|} := by
  change IsPreconnected {y : PS | R < slabFun y}
  have hA : IsPreconnected {y : PS | 0 ≤ y.1.1 ∧ R < slabFun y} :=
    isPreconnected_of_starConvex (starConvex_slab_ge R)
  have hB : IsPreconnected {y : PS | y.1.1 ≤ 0 ∧ R < slabFun y} :=
    isPreconnected_of_starConvex (starConvex_slab_le R)
  have hAB : IsPreconnected
      ({y : PS | 0 ≤ y.1.1 ∧ R < slabFun y} ∪ {y : PS | y.1.1 ≤ 0 ∧ R < slabFun y}) :=
    hA.union _ (slabMid_mem_ge R) (slabMid_mem_le R) hB
  have heq : {y : PS | 0 ≤ y.1.1 ∧ R < slabFun y} ∪ {y : PS | y.1.1 ≤ 0 ∧ R < slabFun y}
      = {y : PS | R < slabFun y} := by
    ext y
    constructor
    · rintro (⟨-, h⟩ | ⟨-, h⟩) <;> exact h
    · intro hy
      rcases le_total y.1.1 0 with h | h
      · exact Or.inr ⟨h, hy⟩
      · exact Or.inl ⟨h, hy⟩
  rw [← heq]
  exact hAB

end Work.RPCore.GenFun
