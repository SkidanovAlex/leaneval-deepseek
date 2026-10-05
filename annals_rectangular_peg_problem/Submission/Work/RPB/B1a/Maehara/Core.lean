import Mathlib
import Submission.Work.RPB.B1a.Maehara.Defs
import Submission.Work.RPB.B1a.Maehara.exists_boundary_path_of_unbounded_component
import Submission.Work.RPB1a.Caratheodory.Brouwer.cpx_transport_bounded_component

set_option maxHeartbeats 1000000

/-!
# The rectangular peg problem: a bounded complementary component of a Jordan curve

This file proves `Work.RPB.B1a.exists_bounded_component_compl`: the complement of the image of a
continuous injective map `γ : Circle → ℝ × ℝ` has a bounded connected component.

The proof is Maehara's (via the Brouwer fixed point theorem).  After transporting along the linear
isometry `ℂ ≃ ℝ × ℝ` and normalising by a similarity of the plane (delegated to
`Work.RPB.B1a.Maehara.exists_bounded_component_complex_of_normalized`), one is reduced to a Jordan
curve lying in the rectangle `RectC = [-1,1] × [-2,2]`, meeting `BdC` exactly in `-1` and `1`, with
`-1`, `1` on the curve.  The two arcs `P`, `Q` of the curve between `-1` and `1` are produced by
`Work.RPB1a.Caratheodory.Brouwer.exists_jordan_arcs`.

* `m` is the topmost point of the curve on the vertical line `re = 0`, `Jl` the arc containing it,
  `Jm` the other arc;
* `l` is the bottommost point of `Jl` on that line; `k'` the topmost point of `Jm` on the part of
  the line below `l` (`Work.RPB.B1a.Maehara.maehara_segment_meets` guarantees that this set is
  nonempty);
* `z0` is the midpoint of `l` and `k'`, and is not on the curve.

If the component of `z0` in the complement were unbounded it would reach the boundary of the
rectangle, through a point `w ∉ range γ`
(`Work.RPB.B1a.Maehara.exists_boundary_path_of_unbounded_component`); walking along the boundary
from `w` to the bottom or the top side and then back through the curve produces a bottom-to-top
path in the rectangle which avoids one of the two arcs, contradicting the crossing lemma
`Work.RPB1a.Caratheodory.Brouwer.crossing_lemma_rect_complex`.
-/

namespace Work.RPB.B1a

open Set Metric Complex
open Work.RPB1a.Caratheodory.Brouwer (crossing_lemma_rect_complex exists_boundary_path
  exists_jordan_arcs cpx_transport_bounded_component)
open Work.RPB.B1a.Maehara

/-- The centre `(0,2)` of the top side of the rectangle. -/
def cTop : ℂ := Complex.mk 0 2

/-- The centre `(0,-2)` of the bottom side of the rectangle. -/
def cBot : ℂ := Complex.mk 0 (-2)

@[simp] theorem cTop_re : cTop.re = 0 := rfl

@[simp] theorem cTop_im : cTop.im = 2 := rfl

@[simp] theorem cBot_re : cBot.re = 0 := rfl

@[simp] theorem cBot_im : cBot.im = -2 := rfl

theorem cTop_mem_RectC : cTop ∈ RectC := by
  rw [mem_RectC]
  exact ⟨by norm_num [cTop], by norm_num [cTop], by norm_num [cTop], by norm_num [cTop]⟩

theorem cBot_mem_RectC : cBot ∈ RectC := by
  rw [mem_RectC]
  exact ⟨by norm_num [cBot], by norm_num [cBot], by norm_num [cBot], by norm_num [cBot]⟩

theorem abs_le_of_mem_RectC {z : ℂ} (hz : z ∈ RectC) : |z.re| ≤ 1 ∧ |z.im| ≤ 2 :=
  ⟨abs_le.mpr ⟨hz.1, hz.2.1⟩, abs_le.mpr ⟨hz.2.2.1, hz.2.2.2⟩⟩

theorem mem_RectC_of {z : ℂ} (h1 : -1 ≤ z.re) (h2 : z.re ≤ 1) (h3 : -2 ≤ z.im)
    (h4 : z.im ≤ 2) : z ∈ RectC := ⟨h1, h2, h3, h4⟩

/-- The convex combination `(1-λ)x + λy` of two reals of `(-1,1)` lies in `(-1,1)`. -/
theorem convex_lt_one {c x y : ℝ} (hc0 : 0 ≤ c) (hc1 : c ≤ 1) (hx : -1 < x) (hx' : x < 1)
    (hy : -1 < y) (hy' : y < 1) :
    -1 < (1 - c) * x + c * y ∧ (1 - c) * x + c * y < 1 := by
  have h1 : (0:ℝ) ≤ 1 - c := by linarith
  have h2 : 0 ≤ x + 1 := by linarith
  have h3 : 0 ≤ 1 - x := by linarith
  have h4 : 0 ≤ y + 1 := by linarith
  have h5 : 0 ≤ 1 - y := by linarith
  constructor
  · rcases eq_or_lt_of_le hc0 with h | h
    · rw [← h]; ring_nf; linarith
    · have hb : 0 < c * (y + 1) := mul_pos h (by linarith)
      have ha : 0 ≤ (1 - c) * (x + 1) := mul_nonneg h1 h2
      nlinarith [ha, hb]
  · rcases eq_or_lt_of_le hc1 with h | h
    · rw [h]; ring_nf; linarith
    · have ha : 0 < (1 - c) * (1 - x) := mul_pos (by linarith) (by linarith)
      have hb : 0 ≤ c * (1 - y) := mul_nonneg hc0 h5
      nlinarith [ha, hb]

/-- The affine parametrisation of the interval between two points of `(-1,1)` stays in `(-1,1)`. -/
theorem affine_mem_Ioo {a b : ℝ} (ha : a ∈ Set.Ioo (-1 : ℝ) 1) (hb : b ∈ Set.Ioo (-1 : ℝ) 1) :
    ∀ r ∈ Set.Icc (-1 : ℝ) 1, a + ((r + 1) / 2 : ℝ) * (b - a) ∈ Set.Ioo (-1 : ℝ) 1 := by
  intro r hr
  have h1 : (0:ℝ) ≤ (r + 1) / 2 := by linarith [hr.1]
  have h2 : (r + 1) / 2 ≤ 1 := by linarith [hr.2]
  have hconv : a + ((r + 1) / 2) * (b - a) = (1 - (r + 1) / 2) * a + ((r + 1) / 2) * b := by ring
  rw [hconv]
  exact convex_lt_one h1 h2 ha.1 ha.2 hb.1 hb.2

theorem seg_re_eq_zero {u v : ℂ} (hu : u.re = 0) (hv : v.re = 0) (t : ℝ) :
    (seg u v t).re = 0 := by
  rw [seg_re, hu, hv]; ring

theorem seg_vert_im {u v : ℂ} (t : ℝ) :
    (seg u v t).im = (1 - (t + 1) / 2) * u.im + ((t + 1) / 2) * v.im := seg_im u v t

/-- The vertical segment between two points of the vertical line, between two points of `RectC`,
lies in `RectC`. -/
theorem seg_vert_mem_RectC {u v : ℂ} (hu : u ∈ RectC) (hv : v ∈ RectC) (hure : u.re = 0)
    (hvre : v.re = 0) {t : ℝ} (ht : t ∈ Set.Icc (-1 : ℝ) 1) : seg u v t ∈ RectC := by
  have hre : (seg u v t).re = 0 := seg_re_eq_zero hure hvre t
  have him : (seg u v t).im = (1 - (t + 1) / 2) * u.im + ((t + 1) / 2) * v.im := seg_vert_im t
  have h1 : (0:ℝ) ≤ (t + 1) / 2 := by linarith [ht.1]
  have h2 : (t + 1) / 2 ≤ 1 := by linarith [ht.2]
  rw [mem_RectC, hre, him]
  exact ⟨by norm_num, by norm_num, by nlinarith [hu.2.2.1, hv.2.2.1, h1, h2],
    by nlinarith [hu.2.2.2, hv.2.2.2, h1, h2]⟩

/-- A horizontal segment between two points of `RectC` lies in `RectC`. -/
theorem seg_horiz_mem_RectC {u v : ℂ} (hu : u ∈ RectC) (hv : v ∈ RectC) (hui : u.im = v.im)
    {t : ℝ} (ht : t ∈ Set.Icc (-1 : ℝ) 1) : seg u v t ∈ RectC := by
  have him : (seg u v t).im = u.im := by rw [seg_im, ← hui]; ring
  have hre : (seg u v t).re = (1 - (t + 1) / 2) * u.re + ((t + 1) / 2) * v.re := seg_re u v t
  have h1 : (0:ℝ) ≤ (t + 1) / 2 := by linarith [ht.1]
  have h2 : (t + 1) / 2 ≤ 1 := by linarith [ht.2]
  rw [mem_RectC, hre, him]
  exact ⟨by nlinarith [hu.1, hv.1, h1, h2], by nlinarith [hu.2.1, hv.2.1, h1, h2],
    hu.2.2.1, hu.2.2.2⟩

/-- The imaginary part of a point of the vertical segment between `u` and `v` lies between the
imaginary parts of `u` and `v`. -/
theorem seg_vert_im_bounds {u v : ℂ} (huv : u.im ≤ v.im) {t : ℝ}
    (ht : t ∈ Set.Icc (-1 : ℝ) 1) : u.im ≤ (seg u v t).im ∧ (seg u v t).im ≤ v.im := by
  have h1 : (0:ℝ) ≤ (t + 1) / 2 := by linarith [ht.1]
  have h2 : (t + 1) / 2 ≤ 1 := by linarith [ht.2]
  rw [seg_vert_im]
  exact ⟨by nlinarith, by nlinarith⟩

/-- **Contrapositive of the crossing lemma, in the form used below.**  A path from the centre of
the bottom side to the centre of the top side of `RectC`, staying in `RectC` and avoiding the image
on `[-1,1]` of a left-to-right path, is impossible. -/
theorem no_path_vertical_of_arc (A ρ : ℝ → ℂ) (hA : Continuous A)
    (hAm : ∀ t ∈ Set.Icc (-1 : ℝ) 1, |(A t).re| ≤ 1 ∧ |(A t).im| ≤ 2)
    (hAl : (A (-1)).re = -1) (hAr : (A 1).re = 1)
    (hρ : Continuous ρ)
    (hρm : ∀ t ∈ Set.Icc (-1 : ℝ) 1, |(ρ t).re| ≤ 1 ∧ |(ρ t).im| ≤ 2)
    (hρbot : (ρ (-1)).im = -2) (hρtop : (ρ 1).im = 2)
    (hdisj : ∀ t ∈ Set.Icc (-1 : ℝ) 1, ρ t ∉ A '' Set.Icc (-1 : ℝ) 1) : False := by
  obtain ⟨s, hs, t, ht, heq⟩ := crossing_lemma_rect_complex hA hρ hAm hρm hAl hAr hρbot hρtop
  exact hdisj t ht ⟨s, hs, heq⟩

/-- **The second arc meets the vertical axis below the lowest point of the first arc.**  Otherwise
the broken line `(0,-2) ~ l` (along the axis), `l ~ m` (along the first arc) and `m ~ (0,2)` (along
the axis) would be a bottom-to-top path of the rectangle avoiding the second arc, contradicting the
crossing lemma. -/
theorem axis_meets_other_arc (P Q : ℝ → ℂ) (m l : ℂ)
    (hP : Continuous P) (hQ : Continuous Q)
    (hPm1 : P (-1) = -1) (hP1 : P 1 = 1) (hQm1 : Q (-1) = -1) (hQ1 : Q 1 = 1)
    (hPinj : Set.InjOn P (Set.Icc (-1 : ℝ) 1)) (hQinj : Set.InjOn Q (Set.Icc (-1 : ℝ) 1))
    (hPR : ∀ t ∈ Set.Icc (-1 : ℝ) 1, P t ∈ RectC)
    (hQR : ∀ t ∈ Set.Icc (-1 : ℝ) 1, Q t ∈ RectC)
    (hmeet : P '' Set.Icc (-1 : ℝ) 1 ∩ Q '' Set.Icc (-1 : ℝ) 1 = {(-1 : ℂ), 1})
    (hm : m ∈ P '' Set.Icc (-1 : ℝ) 1) (hmre : m.re = 0)
    (hmmax : ∀ z ∈ P '' Set.Icc (-1 : ℝ) 1 ∪ Q '' Set.Icc (-1 : ℝ) 1, z.re = 0 → z.im ≤ m.im)
    (hl : l ∈ P '' Set.Icc (-1 : ℝ) 1) (hlre : l.re = 0)
    (hlmin : ∀ z ∈ P '' Set.Icc (-1 : ℝ) 1, z.re = 0 → l.im ≤ z.im) :
    ∃ z ∈ Q '' Set.Icc (-1 : ℝ) 1, z.re = 0 ∧ z.im ≤ l.im := by
  by_contra hcon
  have hcon' : ∀ z ∈ Q '' Set.Icc (-1 : ℝ) 1, z.re = 0 → l.im < z.im := by
    intro z hz hzr
    by_contra h
    exact hcon ⟨z, hz, hzr, not_lt.mp h⟩
  have hmP : m ∈ P '' Set.Icc (-1 : ℝ) 1 := hm
  obtain ⟨sl, hslI, hsl⟩ := hl
  obtain ⟨sm, hsmI, hsm⟩ := hm
  have hlR : l ∈ RectC := by rw [← hsl]; exact hPR sl hslI
  have hmR : m ∈ RectC := by rw [← hsm]; exact hPR sm hsmI
  have hsl_ne_m1 : sl ≠ -1 := by
    intro h
    have h1 : l = -1 := by rw [← hsl, h, hPm1]
    rw [h1] at hlre; norm_num at hlre
  have hsl_ne_1 : sl ≠ 1 := by
    intro h
    have h1 : l = 1 := by rw [← hsl, h, hP1]
    rw [h1] at hlre; norm_num at hlre
  have hsm_ne_m1 : sm ≠ -1 := by
    intro h
    have h1 : m = -1 := by rw [← hsm, h, hPm1]
    rw [h1] at hmre; norm_num at hmre
  have hsm_ne_1 : sm ≠ 1 := by
    intro h
    have h1 : m = 1 := by rw [← hsm, h, hP1]
    rw [h1] at hmre; norm_num at hmre
  have hslIoo : sl ∈ Set.Ioo (-1 : ℝ) 1 :=
    ⟨lt_of_le_of_ne hslI.1 (Ne.symm hsl_ne_m1), lt_of_le_of_ne hslI.2 hsl_ne_1⟩
  have hsmIoo : sm ∈ Set.Ioo (-1 : ℝ) 1 :=
    ⟨lt_of_le_of_ne hsmI.1 (Ne.symm hsm_ne_m1), lt_of_le_of_ne hsmI.2 hsm_ne_1⟩
  have hargIoo := affine_mem_Ioo hslIoo hsmIoo
  have hargI : ∀ r ∈ Set.Icc (-1 : ℝ) 1, sl + ((r + 1) / 2 : ℝ) * (sm - sl)
      ∈ Set.Icc (-1 : ℝ) 1 := fun r hr => ⟨(hargIoo r hr).1.le, (hargIoo r hr).2.le⟩
  have hargnotend : ∀ r ∈ Set.Icc (-1 : ℝ) 1, sl + ((r + 1) / 2 : ℝ) * (sm - sl) ≠ -1 ∧
      sl + ((r + 1) / 2 : ℝ) * (sm - sl) ≠ 1 := fun r hr =>
    ⟨ne_of_gt (hargIoo r hr).1, ne_of_lt (hargIoo r hr).2⟩
  have harcQ : ∀ t ∈ Set.Icc (-1 : ℝ) 1, arc P sl sm t ∉ Q '' Set.Icc (-1 : ℝ) 1 := by
    intro t ht hmem
    obtain ⟨s', hs', hs'e⟩ := hmem
    have hmem' : P (sl + ((t + 1) / 2 : ℝ) * (sm - sl))
        ∈ P '' Set.Icc (-1 : ℝ) 1 ∩ Q '' Set.Icc (-1 : ℝ) 1 :=
      ⟨⟨_, hargI t ht, rfl⟩, ⟨s', hs', hs'e⟩⟩
    rw [hmeet] at hmem'
    rcases hmem' with hh | hh
    · rw [← hPm1] at hh
      exact (hargnotend t ht).1 (hPinj (hargI t ht) (by norm_num) hh)
    · rw [← hP1] at hh
      exact (hargnotend t ht).2 (hPinj (hargI t ht) (by norm_num) hh)
  -- the three pieces of the broken line
  have hbuli : cBot.im ≤ l.im := by rw [cBot_im]; exact hlR.2.2.1
  have humc : m.im ≤ cTop.im := by rw [cTop_im]; exact hmR.2.2.2
  have hp1R : ∀ t ∈ Set.Icc (-1 : ℝ) 1, seg cBot l t ∈ RectC := fun t ht =>
    seg_vert_mem_RectC cBot_mem_RectC hlR cBot_re hlre ht
  have hp2R : ∀ t ∈ Set.Icc (-1 : ℝ) 1, arc P sl sm t ∈ RectC := fun t ht => hPR _ (hargI t ht)
  have hp3R : ∀ t ∈ Set.Icc (-1 : ℝ) 1, seg m cTop t ∈ RectC := fun t ht =>
    seg_vert_mem_RectC hmR cTop_mem_RectC hmre cTop_re ht
  have hp1not : ∀ t ∈ Set.Icc (-1 : ℝ) 1, seg cBot l t ∉ Q '' Set.Icc (-1 : ℝ) 1 := by
    intro t ht hmem
    have hre : (seg cBot l t).re = 0 := seg_re_eq_zero cBot_re hlre t
    have hle : (seg cBot l t).im ≤ l.im := (seg_vert_im_bounds hbuli ht).2
    exact absurd (hcon' _ hmem hre) (not_lt.mpr hle)
  have hp3not : ∀ t ∈ Set.Icc (-1 : ℝ) 1, seg m cTop t ∉ Q '' Set.Icc (-1 : ℝ) 1 := by
    intro t ht hmem
    obtain ⟨s', hs', hs'e⟩ := hmem
    have hre : (seg m cTop t).re = 0 := seg_re_eq_zero hmre cTop_re t
    have hge : m.im ≤ (seg m cTop t).im := (seg_vert_im_bounds humc ht).1
    have hle : (seg m cTop t).im ≤ m.im := hmmax _ (Or.inr ⟨s', hs', hs'e⟩) hre
    have heq : seg m cTop t = m := Complex.ext (by rw [hre, hmre]) (le_antisymm hle hge)
    have hmem2 : m ∈ P '' Set.Icc (-1 : ℝ) 1 ∩ Q '' Set.Icc (-1 : ℝ) 1 :=
      ⟨hmP, ⟨s', hs', by rw [hs'e, heq]⟩⟩
    rw [hmeet] at hmem2
    rcases hmem2 with hh | hh
    · rw [hh] at hmre; norm_num at hmre
    · rw [hh] at hmre; norm_num at hmre
  have e23 : arc P sl sm 1 = (seg m cTop) (-1) := by
    rw [arc_one, seg_neg_one]; exact hsm
  have e123 : (seg cBot l) 1 = (glue (arc P sl sm) (seg m cTop) e23) (-1) := by
    rw [seg_one, glue_neg_one, arc_neg_one]; exact hsl.symm
  set ρ : ℝ → ℂ := glue (seg cBot l) (glue (arc P sl sm) (seg m cTop) e23) e123 with hρdef
  have hρR : ∀ t ∈ Set.Icc (-1 : ℝ) 1, |(ρ t).re| ≤ 1 ∧ |(ρ t).im| ≤ 2 := by
    intro t ht
    have hmem := glue_mem e123 hp1R (glue_mem e23 hp2R hp3R) t ht
    exact abs_le_of_mem_RectC hmem
  have hρbot : (ρ (-1)).im = -2 := by
    rw [hρdef, glue_neg_one, seg_neg_one, cBot_im]
  have hρtop : (ρ 1).im = 2 := by
    rw [hρdef, glue_one, glue_one, seg_one, cTop_im]
  have hρnot : ∀ t ∈ Set.Icc (-1 : ℝ) 1, ρ t ∉ Q '' Set.Icc (-1 : ℝ) 1 := by
    intro t ht
    exact glue_notMem e123 hp1not (glue_notMem e23 harcQ hp3not) t ht
  exact no_path_vertical_of_arc Q ρ hQ (fun t ht => abs_le_of_mem_RectC (hQR t ht))
    (by rw [hQm1]; norm_num) (by rw [hQ1]; norm_num) (continuous_glue (continuous_seg _ _)
      (continuous_glue (continuous_arc hP _ _) (continuous_seg _ _) e23) e123)
    hρR hρbot hρtop hρnot

/-- The normalised Maehara step: a Jordan curve in `RectC` through `-1` and `1`, meeting `BdC`
exactly in those two points, has a bounded complementary component. -/
theorem maehara_normalized (γ : Circle → ℂ) (hγ : Continuous γ) (hinj : Function.Injective γ)
    (hm1 : (-1 : ℂ) ∈ Set.range γ) (h1 : (1 : ℂ) ∈ Set.range γ)
    (hsub : Set.range γ ⊆ RectC) (hbd : Set.range γ ∩ BdC = {(-1 : ℂ), (1 : ℂ)}) :
    ∃ x : ℂ, x ∉ Set.range γ ∧ Bornology.IsBounded (connectedComponentIn ((Set.range γ)ᶜ) x) := by
  classical
  have hKc : IsCompact (Set.range γ) := isCompact_range hγ
  have hKcl : IsClosed (Set.range γ) := hKc.isClosed
  -- a point of the curve on the boundary of the rectangle is `-1` or `1`
  have hBdK : ∀ z ∈ Set.range γ, z ∈ BdC → z = -1 ∨ z = 1 := by
    intro z hz hzB
    have hmem : z ∈ Set.range γ ∩ BdC := ⟨hz, hzB⟩
    rw [hbd] at hmem
    simpa using hmem
  -- ## Step 1: the two arcs of the curve
  obtain ⟨P, Q, hPc, hQc, hPm1, hP1, hQm1, hQ1, hPinj, hQinj, hPrange, hQrange, hcover,
    hmeet⟩ := exists_jordan_arcs γ hγ hinj hm1 h1
  have hPR : ∀ t ∈ Set.Icc (-1 : ℝ) 1, P t ∈ RectC := fun t ht => hsub (hPrange t ht)
  have hQR : ∀ t ∈ Set.Icc (-1 : ℝ) 1, Q t ∈ RectC := fun t ht => hsub (hQrange t ht)
  -- ## Step 2: the topmost point `m` of the curve on the vertical line `re = 0`
  have hPvert : ∃ t ∈ Set.Icc (-1 : ℝ) 1, (P t).re = 0 := by
    obtain ⟨s, hs, t, ht, hst⟩ := crossing_lemma_rect_complex (h := P) (v := vertPt) hPc
      continuous_vertPt
      (fun u hu => abs_le_of_mem_RectC (hPR u hu))
      (fun u hu => abs_le_of_mem_RectC (vertPt_mem_RectC hu))
      (by rw [hPm1]; norm_num) (by rw [hP1]; norm_num)
      (by rw [vertPt_im]; norm_num) (by rw [vertPt_im]; norm_num)
    exact ⟨s, hs, by rw [hst, vertPt_re]⟩
  have hns_ne : (Set.range γ ∩ {z : ℂ | z.re = 0}).Nonempty :=
    ⟨P hPvert.choose, hPrange _ hPvert.choose_spec.1, hPvert.choose_spec.2⟩
  have hns_cpt : IsCompact (Set.range γ ∩ {z : ℂ | z.re = 0}) :=
    hKc.inter_right (isClosed_eq Complex.continuous_re continuous_const)
  obtain ⟨m, hm_mem, hm_max⟩ := hns_cpt.exists_isMaxOn hns_ne Complex.continuous_im.continuousOn
  have hmK : m ∈ Set.range γ := hm_mem.1
  have hmre : m.re = 0 := hm_mem.2
  have hmmax : ∀ z ∈ Set.range γ, z.re = 0 → z.im ≤ m.im := fun z hz hzr => hm_max ⟨hz, hzr⟩
  have hmE : m ∈ RectC := hsub hmK
  have hm_ne_m1 : m ≠ -1 := by
    intro h; have := congrArg Complex.re h; simp at this; linarith [hmre]
  have hm_ne_1 : m ≠ 1 := by
    intro h; have := congrArg Complex.re h; simp at this; linarith [hmre]
  -- ## Step 3: `Jl` is the arc through `m`, `Jm` the other one
  set Jl : ℝ → ℂ := if m ∈ P '' Set.Icc (-1 : ℝ) 1 then P else Q with hJldef
  set Jm : ℝ → ℂ := if m ∈ P '' Set.Icc (-1 : ℝ) 1 then Q else P with hJmdef
  have hJlJm : (Jl = P ∧ Jm = Q) ∨ (Jl = Q ∧ Jm = P) := by
    by_cases h : m ∈ P '' Set.Icc (-1 : ℝ) 1
    · left; exact ⟨by simp only [hJldef, h, if_true], by simp only [hJmdef, h, if_true]⟩
    · right; exact ⟨by simp only [hJldef, h, if_false], by simp only [hJmdef, h, if_false]⟩
  have hJldata : Continuous Jl ∧ Jl (-1) = -1 ∧ Jl 1 = 1 ∧
      Set.InjOn Jl (Set.Icc (-1 : ℝ) 1) ∧ (∀ t ∈ Set.Icc (-1 : ℝ) 1, Jl t ∈ Set.range γ) ∧
      (∀ t ∈ Set.Icc (-1 : ℝ) 1, Jl t ∈ RectC) := by
    rcases hJlJm with ⟨e1, e2⟩ | ⟨e1, e2⟩
    · rw [e1]; exact ⟨hPc, hPm1, hP1, hPinj, hPrange, hPR⟩
    · rw [e1]; exact ⟨hQc, hQm1, hQ1, hQinj, hQrange, hQR⟩
  obtain ⟨hJlc, hJlm1, hJl1, hJli, hJlK, hJlR⟩ := hJldata
  have hJmdata : Continuous Jm ∧ Jm (-1) = -1 ∧ Jm 1 = 1 ∧
      Set.InjOn Jm (Set.Icc (-1 : ℝ) 1) ∧ (∀ t ∈ Set.Icc (-1 : ℝ) 1, Jm t ∈ Set.range γ) ∧
      (∀ t ∈ Set.Icc (-1 : ℝ) 1, Jm t ∈ RectC) := by
    rcases hJlJm with ⟨e1, e2⟩ | ⟨e1, e2⟩
    · rw [e2]; exact ⟨hQc, hQm1, hQ1, hQinj, hQrange, hQR⟩
    · rw [e2]; exact ⟨hPc, hPm1, hP1, hPinj, hPrange, hPR⟩
  obtain ⟨hJmc, hJmm1, hJm1, hJmi, hJmK, hJmR⟩ := hJmdata
  have hJlK' : ∀ z ∈ Jl '' Set.Icc (-1 : ℝ) 1, z ∈ Set.range γ := by
    rintro z ⟨w, hw, rfl⟩; exact hJlK w hw
  have hJmK' : ∀ z ∈ Jm '' Set.Icc (-1 : ℝ) 1, z ∈ Set.range γ := by
    rintro z ⟨w, hw, rfl⟩; exact hJmK w hw
  have hcover2 : Set.range γ = Jl '' Set.Icc (-1 : ℝ) 1 ∪ Jm '' Set.Icc (-1 : ℝ) 1 := by
    rcases hJlJm with ⟨e1, e2⟩ | ⟨e1, e2⟩
    · rw [e1, e2, hcover]
    · rw [e1, e2, hcover, Set.union_comm]
  have hmeet2 : Jl '' Set.Icc (-1 : ℝ) 1 ∩ Jm '' Set.Icc (-1 : ℝ) 1 = {(-1 : ℂ), 1} := by
    rcases hJlJm with ⟨e1, e2⟩ | ⟨e1, e2⟩
    · rw [e1, e2]; exact hmeet
    · rw [e1, e2, Set.inter_comm]; exact hmeet
  have hm_or : m ∈ P '' Set.Icc (-1 : ℝ) 1 ∨ m ∈ Q '' Set.Icc (-1 : ℝ) 1 := by
    have := hmK; rw [hcover] at this; exact this
  have hm_Jl : m ∈ Jl '' Set.Icc (-1 : ℝ) 1 := by
    by_cases h : m ∈ P '' Set.Icc (-1 : ℝ) 1
    · have e : Jl = P := by simp only [hJldef, h, if_true]
      rw [e]; exact h
    · have e : Jl = Q := by simp only [hJldef, h, if_false]
      rw [e]; exact hm_or.resolve_left h
  have hm_not_Jm : m ∉ Jm '' Set.Icc (-1 : ℝ) 1 := by
    by_cases h : m ∈ P '' Set.Icc (-1 : ℝ) 1
    · have e : Jm = Q := by simp only [hJmdef, h, if_true]
      rw [e]; intro hQ
      rw [← e] at hQ
      have hmem : m ∈ Jl '' Set.Icc (-1 : ℝ) 1 ∩ Jm '' Set.Icc (-1 : ℝ) 1 := ⟨hm_Jl, hQ⟩
      rw [hmeet2] at hmem
      rcases hmem with hh | hh
      · exact hm_ne_m1 hh
      · exact hm_ne_1 hh
    · have e : Jm = P := by simp only [hJmdef, h, if_false]
      rw [e]; exact h
  -- ## Step 4: the lowest point `l` of `Jl` on the vertical line
  have hJlns_ne : (Jl '' Set.Icc (-1 : ℝ) 1 ∩ {z : ℂ | z.re = 0}).Nonempty := ⟨m, hm_Jl, hmre⟩
  have hJlns_cpt : IsCompact (Jl '' Set.Icc (-1 : ℝ) 1 ∩ {z : ℂ | z.re = 0}) :=
    (isCompact_Icc.image hJlc).inter_right (isClosed_eq Complex.continuous_re continuous_const)
  obtain ⟨l, hl_mem, hl_min⟩ :=
    hJlns_cpt.exists_isMinOn hJlns_ne Complex.continuous_im.continuousOn
  have hl_Jl : l ∈ Jl '' Set.Icc (-1 : ℝ) 1 := hl_mem.1
  have hlre : l.re = 0 := hl_mem.2
  have hlmin : ∀ z ∈ Jl '' Set.Icc (-1 : ℝ) 1, z.re = 0 → l.im ≤ z.im :=
    fun z hz hzr => hl_min ⟨hz, hzr⟩
  have hlK : l ∈ Set.range γ := hJlK' l hl_Jl
  have hlE : l ∈ RectC := hsub hlK
  have hl_ne_m1 : l ≠ -1 := by
    intro h; have := congrArg Complex.re h; simp at this; linarith [hlre]
  have hl_ne_1 : l ≠ 1 := by
    intro h; have := congrArg Complex.re h; simp at this; linarith [hlre]
  -- ## Step 5: the second arc also meets the vertical line below `l`
  have hmmax2 : ∀ z ∈ Jl '' Set.Icc (-1 : ℝ) 1 ∪ Jm '' Set.Icc (-1 : ℝ) 1,
      z.re = 0 → z.im ≤ m.im := by
    intro z hz hzr
    exact hmmax z ((hcover2 ▸ hz : z ∈ Set.range γ)) hzr
  obtain ⟨k, hk_Jm, hkre, hkle⟩ :=
    axis_meets_other_arc Jl Jm m l hJlc hJmc hJlm1 hJl1 hJmm1 hJm1
      hJli hJmi hJlR hJmR hmeet2 hm_Jl hmre hmmax2 hl_Jl hlre hlmin
  -- ## Step 6: the topmost point `k'` of `Jm` on the vertical line below `l`
  have hMS_cl : IsClosed {z : ℂ | z.re = 0 ∧ -2 ≤ z.im ∧ z.im ≤ l.im} := by
    have h : {z : ℂ | z.re = 0 ∧ -2 ≤ z.im ∧ z.im ≤ l.im}
        = {z : ℂ | z.re = 0} ∩ {z : ℂ | -2 ≤ z.im} ∩ {z : ℂ | z.im ≤ l.im} := by
      ext z; simp only [Set.mem_ofPred_eq, Set.mem_inter_iff]; tauto
    rw [h]
    exact ((isClosed_eq Complex.continuous_re continuous_const).inter
      (isClosed_le continuous_const Complex.continuous_im)).inter
      (isClosed_le Complex.continuous_im continuous_const)
  have hJmMS_ne : (Jm '' Set.Icc (-1 : ℝ) 1 ∩
      {z : ℂ | z.re = 0 ∧ -2 ≤ z.im ∧ z.im ≤ l.im}).Nonempty :=
    ⟨k, hk_Jm, hkre, (hsub (hJmK' k hk_Jm)).2.2.1, hkle⟩
  have hJmMS_cpt : IsCompact (Jm '' Set.Icc (-1 : ℝ) 1 ∩
      {z : ℂ | z.re = 0 ∧ -2 ≤ z.im ∧ z.im ≤ l.im}) :=
    (isCompact_Icc.image hJmc).inter_right hMS_cl
  obtain ⟨k', hk'_mem, hk'_max⟩ :=
    hJmMS_cpt.exists_isMaxOn hJmMS_ne Complex.continuous_im.continuousOn
  have hk'_Jm : k' ∈ Jm '' Set.Icc (-1 : ℝ) 1 := hk'_mem.1
  have hk're : k'.re = 0 := hk'_mem.2.1
  have hk'ge : -2 ≤ k'.im := hk'_mem.2.2.1
  have hk'le : k'.im ≤ l.im := hk'_mem.2.2.2
  have hk'max : ∀ z ∈ Jm '' Set.Icc (-1 : ℝ) 1, z.re = 0 → z.im ≤ l.im → z.im ≤ k'.im := by
    intro z hz hzr hzle
    exact hk'_max ⟨hz, hzr, (hsub (hJmK' z hz)).2.2.1, hzle⟩
  have hk'_ne_l : k' ≠ l := by
    intro h
    have hmem : k' ∈ Jl '' Set.Icc (-1 : ℝ) 1 ∩ Jm '' Set.Icc (-1 : ℝ) 1 :=
      ⟨h ▸ hl_Jl, hk'_Jm⟩
    rw [hmeet2] at hmem
    rcases hmem with hh | hh
    · rw [hh] at hk're; simp at hk're
    · rw [hh] at hk're; simp at hk're
  have hk'_lt : k'.im < l.im :=
    lt_of_le_of_ne hk'le (fun h => hk'_ne_l (Complex.ext (by rw [hk're, hlre]) h))
  -- ## Step 7: the midpoint `z0` of `l` and `k'` is outside the curve
  set z0 : ℂ := ((l.im + k'.im) / 2 : ℝ) * Complex.I with hz0def
  have hz0re : z0.re = 0 := by rw [hz0def]; simp
  have hz0im : z0.im = (l.im + k'.im) / 2 := by rw [hz0def]; simp
  have hz0_gt : k'.im < z0.im := by rw [hz0im]; linarith
  have hz0_lt : z0.im < l.im := by rw [hz0im]; linarith
  have hz0K : z0 ∉ Set.range γ := by
    intro hK
    have hor : z0 ∈ Jl '' Set.Icc (-1 : ℝ) 1 ∨ z0 ∈ Jm '' Set.Icc (-1 : ℝ) 1 := by
      have := hK; rw [hcover2] at this; exact this
    rcases hor with hz | hz
    · linarith [hlmin z0 hz hz0re, hz0_lt]
    · linarith [hk'max z0 hz hz0re (le_of_lt hz0_lt), hz0_gt]
  have hz0R : z0 ∈ RectC :=
    mem_RectC_of (by rw [hz0re]; norm_num) (by rw [hz0re]; norm_num)
      (by rw [hz0im]; linarith [hlE.2.2.1, hk'ge]) (by rw [hz0im]; linarith [hlE.2.2.2, hk'le])
  -- parameters of `l` and `m` on the arc `Jl`
  obtain ⟨sl, hslI, hsl⟩ := hl_Jl
  obtain ⟨sm, hsmI, hsm⟩ := hm_Jl
  have hsl_ne_m1 : sl ≠ -1 := by
    intro h; rw [h, hJlm1] at hsl; exact hl_ne_m1 hsl.symm
  have hsl_ne_1 : sl ≠ 1 := by
    intro h; rw [h, hJl1] at hsl; exact hl_ne_1 hsl.symm
  have hsm_ne_m1 : sm ≠ -1 := by
    intro h; rw [h, hJlm1] at hsm; exact hm_ne_m1 hsm.symm
  have hsm_ne_1 : sm ≠ 1 := by
    intro h; rw [h, hJl1] at hsm; exact hm_ne_1 hsm.symm
  -- the piece of `Jl` between `l` and `m` avoids the other arc and the two endpoints
  have hslIoo : sl ∈ Set.Ioo (-1 : ℝ) 1 :=
    ⟨lt_of_le_of_ne hslI.1 (Ne.symm hsl_ne_m1), lt_of_le_of_ne hslI.2 hsl_ne_1⟩
  have hsmIoo : sm ∈ Set.Ioo (-1 : ℝ) 1 :=
    ⟨lt_of_le_of_ne hsmI.1 (Ne.symm hsm_ne_m1), lt_of_le_of_ne hsmI.2 hsm_ne_1⟩
  have hargIoo : ∀ r ∈ Set.Icc (-1 : ℝ) 1,
      sl + ((r + 1) / 2 : ℝ) * (sm - sl) ∈ Set.Ioo (-1 : ℝ) 1 :=
    affine_mem_Ioo hslIoo hsmIoo
  have hargI : ∀ r ∈ Set.Icc (-1 : ℝ) 1, sl + ((r + 1) / 2 : ℝ) * (sm - sl)
      ∈ Set.Icc (-1 : ℝ) 1 := fun r hr => ⟨(hargIoo r hr).1.le, (hargIoo r hr).2.le⟩
  have hargnotend : ∀ r ∈ Set.Icc (-1 : ℝ) 1, sl + ((r + 1) / 2 : ℝ) * (sm - sl) ≠ -1 ∧
      sl + ((r + 1) / 2 : ℝ) * (sm - sl) ≠ 1 := fun r hr =>
    ⟨ne_of_gt (hargIoo r hr).1, ne_of_lt (hargIoo r hr).2⟩
  have harcJm : ∀ t ∈ Set.Icc (-1 : ℝ) 1, arc Jl sl sm t ∉ Jm '' Set.Icc (-1 : ℝ) 1 := by
    intro t ht hmem
    obtain ⟨s', hs', hs'e⟩ := hmem
    have hmem' : Jl (sl + ((t + 1) / 2 : ℝ) * (sm - sl))
        ∈ Jl '' Set.Icc (-1 : ℝ) 1 ∩ Jm '' Set.Icc (-1 : ℝ) 1 :=
      ⟨⟨_, hargI t ht, rfl⟩, ⟨s', hs', hs'e⟩⟩
    rw [hmeet2] at hmem'
    rcases hmem' with hh | hh
    · rw [← hJlm1] at hh
      exact (hargnotend t ht).1 (hJli (hargI t ht) (by norm_num) hh)
    · rw [← hJl1] at hh
      exact (hargnotend t ht).2 (hJli (hargI t ht) (by norm_num) hh)
  -- ## Step 8: `z0` is not connected to the boundary of the rectangle inside `RectC ∖ range γ`
  have key : ¬ Bornology.IsBounded (connectedComponentIn ((Set.range γ)ᶜ) z0) → False := by
    intro hnotbdd
    obtain ⟨w, hwBd, hwK, q, hqc, hq0, hq1, hqR, hqK⟩ :=
      exists_boundary_path_of_unbounded_component (Set.range γ) hKcl z0 hz0K hz0R hnotbdd
    have hwR : w ∈ RectC := by
      have h := hqR 1 (by norm_num : (1:ℝ) ∈ Set.Icc (-1:ℝ) 1)
      rwa [hq1] at h
    have hw_ne_m1 : w ≠ -1 := fun h => hwK (h ▸ hm1)
    have hw_ne_1 : w ≠ 1 := fun h => hwK (h ▸ h1)
    obtain ⟨z2, hz2, β, hβR, hβBd, hβne⟩ := exists_boundary_path w
      ⟨hwR.1, hwR.2.1, hwR.2.2.1, hwR.2.2.2⟩ hwBd hw_ne_m1 hw_ne_1
    have hβK : ∀ t, β t ∉ Set.range γ := fun t hK => by
      rcases hBdK (β t) hK (hβBd t) with h | h
      · exact (hβne t).1 h
      · exact (hβne t).2 h
    have hz2R : z2 ∈ RectC := by
      have h := hβR 1
      rwa [Path.target β] at h
    -- the reversed version of the path `q`, from `w` down to `z0`
    have hqrev0 : (fun t : ℝ => q (1 - max 0 (min 1 t))) (-1) = w := by
      show q (1 - max 0 (min 1 (-1:ℝ))) = w
      have h : 1 - max 0 (min 1 (-1:ℝ)) = 1 := by norm_num
      rw [h, hq1]
    have hqrev1 : (fun t : ℝ => q (1 - max 0 (min 1 t))) 1 = z0 := by
      show q (1 - max 0 (min 1 (1:ℝ))) = z0
      have h : 1 - max 0 (min 1 (1:ℝ)) = 0 := by norm_num
      rw [h, hq0]
    have hqrevc : Continuous fun t : ℝ => q (1 - max 0 (min 1 t)) := by fun_prop
    have hqrevR : ∀ t ∈ Set.Icc (-1 : ℝ) 1, q (1 - max 0 (min 1 t)) ∈ RectC := by
      intro t ht
      have h1 : (0:ℝ) ≤ 1 - max 0 (min 1 t) := by
        have h2 : max 0 (min 1 t) ≤ 1 := max_le (by norm_num) (min_le_left _ _)
        linarith
      have h2 : 1 - max 0 (min 1 t) ≤ 1 := by
        have h3 : (0:ℝ) ≤ max 0 (min 1 t) := le_max_left _ _
        linarith
      exact hqR _ ⟨by linarith, h2⟩
    have hqrevK : ∀ t ∈ Set.Icc (-1 : ℝ) 1, q (1 - max 0 (min 1 t)) ∉ Set.range γ :=
      fun t _ => hqK _
    rcases hz2 with hz2 | hz2
    · -- ## Case A: `z2` lies on the bottom side
      set p1 : ℝ → ℂ := seg cBot z2 with hp1def
      set p2 : ℝ → ℂ := pathOnRev β with hp2def
      set p3 : ℝ → ℂ := fun t : ℝ => q (1 - max 0 (min 1 t)) with hp3def
      set p4 : ℝ → ℂ := seg z0 l with hp4def
      set p5 : ℝ → ℂ := arc Jl sl sm with hp5def
      set p6 : ℝ → ℂ := seg m cTop with hp6def
      have huiA : cBot.im = z2.im := by rw [cBot_im, hz2]
      have huliA : z0.im ≤ l.im := le_of_lt hz0_lt
      have humcA : m.im ≤ cTop.im := by rw [cTop_im]; exact hmE.2.2.2
      have hp1R : ∀ t ∈ Set.Icc (-1 : ℝ) 1, p1 t ∈ RectC := fun t ht =>
        seg_horiz_mem_RectC cBot_mem_RectC hz2R huiA ht
      have hp2R : ∀ t ∈ Set.Icc (-1 : ℝ) 1, p2 t ∈ RectC := fun t ht =>
        pathOnRev_mem β hβR t ht
      have hp3R : ∀ t ∈ Set.Icc (-1 : ℝ) 1, p3 t ∈ RectC := fun t ht => hqrevR t ht
      have hp4R : ∀ t ∈ Set.Icc (-1 : ℝ) 1, p4 t ∈ RectC := fun t ht =>
        seg_vert_mem_RectC hz0R hlE hz0re hlre ht
      have hp5R : ∀ t ∈ Set.Icc (-1 : ℝ) 1, p5 t ∈ RectC := fun t ht => hJlR _ (hargI t ht)
      have hp6R : ∀ t ∈ Set.Icc (-1 : ℝ) 1, p6 t ∈ RectC := fun t ht =>
        seg_vert_mem_RectC hmE cTop_mem_RectC hmre cTop_re ht
      have hp1K : ∀ t ∈ Set.Icc (-1 : ℝ) 1, p1 t ∉ Set.range γ := by
        intro t ht hmem
        have him : (p1 t).im = -2 := by rw [hp1def, seg_im, cBot_im, hz2]; ring
        rcases hBdK _ hmem (by rw [mem_BdC]; exact Or.inr (Or.inr (Or.inl him))) with h | h <;>
          · rw [h] at him; norm_num at him
      have hp1not : ∀ t ∈ Set.Icc (-1 : ℝ) 1, p1 t ∉ Jm '' Set.Icc (-1 : ℝ) 1 :=
        fun t ht hmem => hp1K t ht (hJmK' _ hmem)
      have hp2not : ∀ t ∈ Set.Icc (-1 : ℝ) 1, p2 t ∉ Jm '' Set.Icc (-1 : ℝ) 1 :=
        fun t ht hmem => pathOnRev_notMem β hβK t ht (hJmK' _ hmem)
      have hp3not : ∀ t ∈ Set.Icc (-1 : ℝ) 1, p3 t ∉ Jm '' Set.Icc (-1 : ℝ) 1 :=
        fun t ht hmem => hqrevK t ht (hJmK' _ hmem)
      have hp4not : ∀ t ∈ Set.Icc (-1 : ℝ) 1, p4 t ∉ Jm '' Set.Icc (-1 : ℝ) 1 := by
        intro t ht hmem
        have hre : (p4 t).re = 0 := seg_re_eq_zero hz0re hlre t
        have hge : z0.im ≤ (p4 t).im := (seg_vert_im_bounds huliA ht).1
        have hle : (p4 t).im ≤ l.im := (seg_vert_im_bounds huliA ht).2
        exact absurd (hk'max _ hmem hre hle) (not_le.mpr (lt_of_lt_of_le hz0_gt hge))
      have hp5not : ∀ t ∈ Set.Icc (-1 : ℝ) 1, p5 t ∉ Jm '' Set.Icc (-1 : ℝ) 1 :=
        fun t ht hmem => harcJm t ht hmem
      have hp6not : ∀ t ∈ Set.Icc (-1 : ℝ) 1, p6 t ∉ Jm '' Set.Icc (-1 : ℝ) 1 := by
        intro t ht hmem
        obtain ⟨s', hs', hs'e⟩ := hmem
        have hre : (p6 t).re = 0 := seg_re_eq_zero hmre cTop_re t
        have hge : m.im ≤ (p6 t).im := (seg_vert_im_bounds humcA ht).1
        have hle : (p6 t).im ≤ m.im := hmmax _ (hJmK' _ ⟨s', hs', hs'e⟩) hre
        have heq : p6 t = m := Complex.ext (by rw [hre, hmre]) (le_antisymm hle hge)
        rw [heq] at hs'e
        exact hm_not_Jm ⟨s', hs', hs'e⟩
      have e56 : p5 1 = p6 (-1) := by
        rw [hp5def, hp6def, arc_one, seg_neg_one]; exact hsm
      have e456 : p4 1 = (glue p5 p6 e56) (-1) := by
        rw [glue_neg_one, hp4def, hp5def, seg_one, arc_neg_one]; exact hsl.symm
      have e3456 : p3 1 = (glue p4 (glue p5 p6 e56) e456) (-1) := by
        rw [glue_neg_one, hp3def, hp4def, seg_neg_one]; exact hqrev1
      have e23456 : p2 1 = (glue p3 (glue p4 (glue p5 p6 e56) e456) e3456) (-1) := by
        rw [glue_neg_one, hp2def, hp3def, pathOnRev_one]; exact hqrev0.symm
      have e123456 : p1 1 =
          (glue p2 (glue p3 (glue p4 (glue p5 p6 e56) e456) e3456) e23456) (-1) := by
        rw [glue_neg_one, hp1def, hp2def, seg_one, pathOnRev_neg_one]
      set ρ : ℝ → ℂ := glue p1 (glue p2 (glue p3 (glue p4 (glue p5 p6 e56) e456) e3456)
        e23456) e123456 with hρdef
      have hρc : Continuous ρ := by
        rw [hρdef]
        exact continuous_glue (continuous_seg _ _) (continuous_glue (continuous_pathOnRev β)
          (continuous_glue hqrevc (continuous_glue (continuous_seg _ _)
            (continuous_glue (continuous_arc hJlc _ _) (continuous_seg _ _) e56) e456)
            e3456) e23456) e123456
      have hρR : ∀ t ∈ Set.Icc (-1 : ℝ) 1, |(ρ t).re| ≤ 1 ∧ |(ρ t).im| ≤ 2 := by
        intro t ht
        have hmem := glue_mem e123456 hp1R (glue_mem e23456 hp2R (glue_mem e3456 hp3R
          (glue_mem e456 hp4R (glue_mem e56 hp5R hp6R)))) t ht
        exact abs_le_of_mem_RectC hmem
      have hρbot : (ρ (-1)).im = -2 := by
        rw [hρdef, glue_neg_one, hp1def, seg_neg_one, cBot_im]
      have hρtop : (ρ 1).im = 2 := by
        rw [hρdef, glue_one, glue_one, glue_one, glue_one, glue_one, hp6def, seg_one, cTop_im]
      have hρnot : ∀ t ∈ Set.Icc (-1 : ℝ) 1, ρ t ∉ Jm '' Set.Icc (-1 : ℝ) 1 := by
        intro t ht
        exact glue_notMem e123456 hp1not (glue_notMem e23456 hp2not (glue_notMem e3456 hp3not
          (glue_notMem e456 hp4not (glue_notMem e56 hp5not hp6not)))) t ht
      exact no_path_vertical_of_arc Jm ρ hJmc (fun t ht => abs_le_of_mem_RectC (hJmR t ht))
        (by rw [hJmm1]; norm_num) (by rw [hJm1]; norm_num) hρc hρR hρbot hρtop hρnot
    · -- ## Case B: `z2` lies on the top side
      set p1 : ℝ → ℂ := seg cBot z0 with hp1def
      set p2 : ℝ → ℂ := fun t : ℝ => q ((t + 1) / 2) with hp2def
      set p3 : ℝ → ℂ := pathOn β with hp3def
      set p4 : ℝ → ℂ := seg z2 cTop with hp4def
      have huiB : z2.im = cTop.im := by rw [hz2, cTop_im]
      have hbuliB : cBot.im ≤ z0.im := by rw [cBot_im]; exact hz0R.2.2.1
      have hp1R : ∀ t ∈ Set.Icc (-1 : ℝ) 1, p1 t ∈ RectC := fun t ht =>
        seg_vert_mem_RectC cBot_mem_RectC hz0R cBot_re hz0re ht
      have hp2c : Continuous p2 := by rw [hp2def]; exact hqc.comp (by fun_prop)
      have hp2R : ∀ t ∈ Set.Icc (-1 : ℝ) 1, p2 t ∈ RectC := fun t ht =>
        hqR _ ⟨by linarith [ht.1], by linarith [ht.2]⟩
      have hp3R : ∀ t ∈ Set.Icc (-1 : ℝ) 1, p3 t ∈ RectC := fun t ht => pathOn_mem β hβR t ht
      have hp4R : ∀ t ∈ Set.Icc (-1 : ℝ) 1, p4 t ∈ RectC := fun t ht =>
        seg_horiz_mem_RectC hz2R cTop_mem_RectC huiB ht
      have hp1not : ∀ t ∈ Set.Icc (-1 : ℝ) 1, p1 t ∉ Jl '' Set.Icc (-1 : ℝ) 1 := by
        intro t ht hmem
        have hre : (p1 t).re = 0 := seg_re_eq_zero cBot_re hz0re t
        have hle : (p1 t).im ≤ z0.im := (seg_vert_im_bounds hbuliB ht).2
        linarith [hlmin _ hmem hre, hz0_lt, hle]
      have hp2not : ∀ t ∈ Set.Icc (-1 : ℝ) 1, p2 t ∉ Jl '' Set.Icc (-1 : ℝ) 1 :=
        fun t ht hmem => hqK _ (hJlK' _ hmem)
      have hp3not : ∀ t ∈ Set.Icc (-1 : ℝ) 1, p3 t ∉ Jl '' Set.Icc (-1 : ℝ) 1 :=
        fun t ht hmem => pathOn_notMem β hβK t ht (hJlK' _ hmem)
      have hp4not : ∀ t ∈ Set.Icc (-1 : ℝ) 1, p4 t ∉ Jl '' Set.Icc (-1 : ℝ) 1 := by
        intro t ht hmem
        have him : (p4 t).im = 2 := by rw [hp4def, seg_im, hz2, cTop_im]; ring
        rcases hBdK _ (hJlK' _ hmem) (by rw [mem_BdC]; exact Or.inr (Or.inr (Or.inr him)))
          with h | h <;> · rw [h] at him; norm_num at him
      have e34 : p3 1 = p4 (-1) := by
        rw [hp3def, hp4def, pathOn_one, seg_neg_one]
      have e234 : p2 1 = (glue p3 p4 e34) (-1) := by
        rw [glue_neg_one]
        show q (((1:ℝ) + 1) / 2) = pathOn β (-1)
        rw [show ((1:ℝ) + 1) / 2 = 1 by norm_num, hq1, pathOn_neg_one]
      have e1234 : p1 1 = (glue p2 (glue p3 p4 e34) e234) (-1) := by
        rw [glue_neg_one]
        show seg cBot z0 1 = q (((-1:ℝ) + 1) / 2)
        rw [seg_one, show ((-1:ℝ) + 1) / 2 = 0 by norm_num, hq0]
      set ρ : ℝ → ℂ := glue p1 (glue p2 (glue p3 p4 e34) e234) e1234 with hρdef
      have hρc : Continuous ρ := by
        rw [hρdef]
        exact continuous_glue (continuous_seg _ _) (continuous_glue hp2c
          (continuous_glue (continuous_pathOn β) (continuous_seg _ _) e34) e234) e1234
      have hρR : ∀ t ∈ Set.Icc (-1 : ℝ) 1, |(ρ t).re| ≤ 1 ∧ |(ρ t).im| ≤ 2 := by
        intro t ht
        have hmem := glue_mem e1234 hp1R (glue_mem e234 hp2R (glue_mem e34 hp3R hp4R)) t ht
        exact abs_le_of_mem_RectC hmem
      have hρbot : (ρ (-1)).im = -2 := by
        rw [hρdef, glue_neg_one, hp1def, seg_neg_one, cBot_im]
      have hρtop : (ρ 1).im = 2 := by
        rw [hρdef, glue_one, glue_one, glue_one, hp4def, seg_one, cTop_im]
      have hρnot : ∀ t ∈ Set.Icc (-1 : ℝ) 1, ρ t ∉ Jl '' Set.Icc (-1 : ℝ) 1 := by
        intro t ht
        exact glue_notMem e1234 hp1not (glue_notMem e234 hp2not (glue_notMem e34 hp3not hp4not))
          t ht
      exact no_path_vertical_of_arc Jl ρ hJlc (fun t ht => abs_le_of_mem_RectC (hJlR t ht))
        (by rw [hJlm1]; norm_num) (by rw [hJl1]; norm_num) hρc hρR hρbot hρtop hρnot
  exact ⟨z0, hz0K, by by_contra h; exact key h⟩

end Work.RPB.B1a
