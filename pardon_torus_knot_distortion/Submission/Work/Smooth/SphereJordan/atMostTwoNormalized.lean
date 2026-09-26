import Mathlib
import Submission.Work.Topology.PlaneCurve.jordanRectSetup
import Submission.Work.Topology.PlaneCurve.frontier_component_eq_range
import Submission.Work.Smooth.SphereJordan.memClosureConnectedComponentIn
import Submission.Work.Smooth.JordanSeparation.phragmen_brouwer_of_square

namespace Work.Smooth.SphereJordan

open Set Metric
open Work.Topology.PlaneCurve

set_option maxHeartbeats 1600000

noncomputable section

/-! ### Elementary facts about the box and the vertical segment -/

theorem compl_closedBox_eq :
    (closedBox : Set ℂ)ᶜ = {z : ℂ | 1 < z.re ∨ z.re < -1 ∨ 2 < z.im ∨ z.im < -2} := by
  ext z
  simp only [Set.mem_compl_iff, closedBox, Set.mem_setOf_eq]
  constructor
  · intro h
    rcases le_or_gt z.re 1 with h1 | h1
    · rcases le_or_gt (-1) z.re with h2 | h2
      · rcases le_or_gt z.im 2 with h3 | h3
        · rcases le_or_gt (-2) z.im with h4 | h4
          · exact absurd ⟨abs_le.mpr ⟨h2, h1⟩, abs_le.mpr ⟨h4, h3⟩⟩ h
          · exact Or.inr (Or.inr (Or.inr (by linarith)))
        · exact Or.inr (Or.inr (Or.inl (by linarith)))
      · exact Or.inr (Or.inl (by linarith))
    · exact Or.inl (by linarith)
  · rintro (h | h | h | h) ⟨h1, h2⟩
    · linarith [abs_le.mp h1]
    · linarith [abs_le.mp h1]
    · linarith [abs_le.mp h2]
    · linarith [abs_le.mp h2]

theorem isPreconnected_re_gt (c : ℝ) : IsPreconnected {z : ℂ | c < z.re} := by
  have h := (isPreconnected_Ioi (a := c)).prod (isPreconnected_univ (α := ℝ))
  have h2 := h.image (fun p : ℝ × ℝ => (p.1 : ℂ) + (p.2 : ℂ) * Complex.I) (by fun_prop)
  rw [show {z : ℂ | c < z.re}
      = (fun p : ℝ × ℝ => (p.1 : ℂ) + (p.2 : ℂ) * Complex.I) '' (Ioi c ×ˢ univ) from ?_]
  exact h2
  ext z
  constructor
  · intro hz
    exact ⟨(z.re, z.im), ⟨hz, trivial⟩, by simp⟩
  · rintro ⟨⟨x, y⟩, ⟨hx, -⟩, rfl⟩
    show c < ((x : ℂ) + (y : ℂ) * Complex.I).re
    simpa using hx

theorem isPreconnected_im_gt (c : ℝ) : IsPreconnected {z : ℂ | c < z.im} := by
  have h := (isPreconnected_Ioi (a := c)).prod (isPreconnected_univ (α := ℝ))
  have h2 := h.image (fun p : ℝ × ℝ => (p.2 : ℂ) + (p.1 : ℂ) * Complex.I) (by fun_prop)
  rw [show {z : ℂ | c < z.im}
      = (fun p : ℝ × ℝ => (p.2 : ℂ) + (p.1 : ℂ) * Complex.I) '' (Ioi c ×ˢ univ) from ?_]
  exact h2
  ext z
  constructor
  · intro hz
    exact ⟨(z.im, z.re), ⟨hz, trivial⟩, by simp⟩
  · rintro ⟨⟨x, y⟩, ⟨hx, -⟩, rfl⟩
    show c < ((y : ℂ) + (x : ℂ) * Complex.I).im
    simpa using hx

theorem isPreconnected_re_lt (c : ℝ) : IsPreconnected {z : ℂ | z.re < c} := by
  have h := (isPreconnected_Iio (a := c)).prod (isPreconnected_univ (α := ℝ))
  have h2 := h.image (fun p : ℝ × ℝ => (p.1 : ℂ) + (p.2 : ℂ) * Complex.I) (by fun_prop)
  rw [show {z : ℂ | z.re < c}
      = (fun p : ℝ × ℝ => (p.1 : ℂ) + (p.2 : ℂ) * Complex.I) '' (Iio c ×ˢ univ) from ?_]
  exact h2
  ext z
  constructor
  · intro hz
    exact ⟨(z.re, z.im), ⟨hz, trivial⟩, by simp⟩
  · rintro ⟨⟨x, y⟩, ⟨hx, -⟩, rfl⟩
    show ((x : ℂ) + (y : ℂ) * Complex.I).re < c
    simpa using hx

theorem isPreconnected_im_lt (c : ℝ) : IsPreconnected {z : ℂ | z.im < c} := by
  have h := (isPreconnected_Iio (a := c)).prod (isPreconnected_univ (α := ℝ))
  have h2 := h.image (fun p : ℝ × ℝ => (p.2 : ℂ) + (p.1 : ℂ) * Complex.I) (by fun_prop)
  rw [show {z : ℂ | z.im < c}
      = (fun p : ℝ × ℝ => (p.2 : ℂ) + (p.1 : ℂ) * Complex.I) '' (Iio c ×ˢ univ) from ?_]
  exact h2
  ext z
  constructor
  · intro hz
    exact ⟨(z.im, z.re), ⟨hz, trivial⟩, by simp⟩
  · rintro ⟨⟨x, y⟩, ⟨hx, -⟩, rfl⟩
    show ((y : ℂ) + (x : ℂ) * Complex.I).im < c
    simpa using hx

theorem isPreconnected_compl_closedBox : IsPreconnected ((closedBox : Set ℂ)ᶜ) := by
  have hcs : ((closedBox : Set ℂ)ᶜ)
      = ((({z : ℂ | 1 < z.re} ∪ {z : ℂ | 2 < z.im}) ∪ {z : ℂ | z.re < -1})
        ∪ {z : ℂ | z.im < -2}) := by
    rw [compl_closedBox_eq]
    ext z
    simp only [Set.mem_setOf_eq, Set.mem_union]
    tauto
  rw [hcs]
  have h12 : IsPreconnected ({z : ℂ | 1 < z.re} ∪ {z : ℂ | 2 < z.im}) :=
    IsPreconnected.union (2 + 3 * Complex.I)
      (by norm_num [Complex.add_re, Complex.mul_re])
      (by norm_num [Complex.add_re, Complex.mul_re])
      (isPreconnected_re_gt 1) (isPreconnected_im_gt 2)
  have h123 : IsPreconnected (({z : ℂ | 1 < z.re} ∪ {z : ℂ | 2 < z.im}) ∪ {z : ℂ | z.re < -1}) :=
    IsPreconnected.union (-2 + 3 * Complex.I)
      (by norm_num [Complex.add_re, Complex.mul_re])
      (by norm_num [Complex.add_re, Complex.mul_re])
      h12 (isPreconnected_re_lt (-1))
  exact IsPreconnected.union (2 - 3 * Complex.I)
    (by norm_num [Complex.add_re, Complex.mul_re])
    (by norm_num [Complex.add_re, Complex.mul_re])
    h123 (isPreconnected_im_lt (-2))

theorem vSeg_subset_closedBox : vSeg ⊆ closedBox := by
  intro z hz
  exact ⟨by rw [hz.1]; norm_num, abs_le.mpr ⟨hz.2.1, hz.2.2⟩⟩

theorem isClosed_vSeg : IsClosed vSeg := by
  have h1 : IsClosed {z : ℂ | z.re = 0} := isClosed_eq Complex.continuous_re continuous_const
  have h2 : IsClosed {z : ℂ | -2 ≤ z.im} := isClosed_le continuous_const Complex.continuous_im
  have h3 : IsClosed {z : ℂ | z.im ≤ 2} := isClosed_le Complex.continuous_im continuous_const
  have hset : vSeg = {z : ℂ | z.re = 0} ∩ {z : ℂ | -2 ≤ z.im} ∩ {z : ℂ | z.im ≤ 2} := by
    ext z; simp [vSeg, and_assoc]
  rw [hset]; exact (h1.inter h2).inter h3

/-- A point of `range γ` with `re = 0` lies in `rectR` (so `-2 < im < 2`). -/
theorem mem_rectR_of_mem_range_re_zero {γ : ℝ → ℂ}
    (hsub : ∀ w ∈ Set.range γ, w ∈ rectR ∨ w = -1 ∨ w = 1)
    {z : ℂ} (hz : z ∈ Set.range γ) (hre : z.re = 0) : z ∈ rectR := by
  rcases hsub z hz with h | h | h
  · exact h
  · rw [h] at hre; norm_num at hre
  · rw [h] at hre; norm_num at hre

/-- A complex number with vanishing real part is `im * I`. -/
theorem eq_of_re_zero {z : ℂ} (h : z.re = 0) : z = (z.im : ℂ) * Complex.I := by
  apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im, h]

/-! ### Independent facts about `Path.trans` -/

theorem range_trans_subset {x y z : ℂ} (γ : Path x y) (γ' : Path y z) :
    Set.range (γ.trans γ') ⊆ Set.range γ ∪ Set.range γ' := by
  rintro w ⟨t, ht⟩
  rw [Path.trans_apply] at ht
  split_ifs at ht
  · left; exact ⟨_, ht⟩
  · right; exact ⟨_, ht⟩

theorem trans_mem {x y z : ℂ} (γ : Path x y) (γ' : Path y z) {S : Set ℂ}
    (hγ : ∀ t, γ t ∈ S) (hγ' : ∀ t, γ' t ∈ S) : ∀ t, (γ.trans γ') t ∈ S := by
  intro t
  rw [Path.trans_apply]
  split_ifs with h
  · exact hγ _
  · exact hγ' _

/-- The open window of `vSeg` between `k` and `m` is contained in the component of any of its
points, when it is free of `J`. -/
theorem window_subset_componentIn {J : Set ℂ} {k m : ℂ} (hkSeg : k ∈ vSeg) (hmSeg : m ∈ vSeg)
    (hkm : k.im < m.im)
    (hfree : ∀ z ∈ vSeg, k.im < z.im → z.im < m.im → z ∉ J) :
    {z : ℂ | z.re = 0 ∧ k.im < z.im ∧ z.im < m.im}
      ⊆ connectedComponentIn Jᶜ (⟨0, (k.im + m.im) / 2⟩ : ℂ) := by
  have hpre : IsPreconnected {z : ℂ | z.re = 0 ∧ k.im < z.im ∧ z.im < m.im} := by
    have himg : {z : ℂ | z.re = 0 ∧ k.im < z.im ∧ z.im < m.im}
        = (fun s : ℝ => (s : ℂ) * Complex.I) '' (Set.Ioo k.im m.im) := by
      ext z; constructor
      · rintro ⟨hre, h1, h2⟩
        exact ⟨z.im, ⟨by simpa using h1, by simpa using h2⟩, (eq_of_re_zero hre).symm⟩
      · rintro ⟨s, hs, rfl⟩
        exact ⟨by simp, by simpa using hs.1, by simpa using hs.2⟩
    rw [himg]
    exact (isPreconnected_Ioo).image _ (by fun_prop)
  apply IsPreconnected.subset_connectedComponentIn hpre _ _
  · refine ⟨rfl, ?_, ?_⟩ <;> (rw [show ((⟨0, (k.im + m.im) / 2⟩ : ℂ)).im = (k.im + m.im) / 2 from rfl]; linarith)
  · intro z hz
    refine hfree z ?_ hz.2.1 hz.2.2
    exact ⟨hz.1, by linarith [hkSeg.2.1, hz.2.1], by linarith [hmSeg.2.2, hz.2.2]⟩

/-- The downward ray of `vSeg` from level `t`, together with the complement of the box, is contained
in the unbounded component (when it is free of `J`). -/
theorem ray_lt_subset_Uinf {J : Set ℂ} (hJbox : J ⊆ closedBox) {t : ℝ}
    (hfree : ∀ z ∈ vSeg, z.im < t → z ∉ J) :
    {z : ℂ | z.re = 0 ∧ z.im < t} ∪ (closedBox : Set ℂ)ᶜ
      ⊆ connectedComponentIn Jᶜ (3 * Complex.I) := by
  have h3i_box : (3 * Complex.I : ℂ) ∈ (closedBox : Set ℂ)ᶜ := by
    rw [compl_closedBox_eq]; exact Or.inr (Or.inr (Or.inl (by norm_num)))
  have hpre : IsPreconnected ({z : ℂ | z.re = 0 ∧ z.im < t} ∪ (closedBox : Set ℂ)ᶜ) := by
    have h1 : IsPreconnected {z : ℂ | z.re = 0 ∧ z.im < t} := by
      have himg : {z : ℂ | z.re = 0 ∧ z.im < t}
          = (fun s : ℝ => (s : ℂ) * Complex.I) '' (Set.Iio t) := by
        ext z; constructor
        · rintro ⟨hre, h1⟩
          exact ⟨z.im, by simpa using h1, (eq_of_re_zero hre).symm⟩
        · rintro ⟨s, hs, rfl⟩
          exact ⟨by simp, by simpa using hs⟩
      rw [himg]
      exact (isPreconnected_Iio (a := t)).image _ (by fun_prop)
    have hz0 : (⟨0, min t 0 - 3⟩ : ℂ) ∈ {z : ℂ | z.re = 0 ∧ z.im < t} := by
      refine ⟨rfl, ?_⟩
      have hh : (⟨0, min t 0 - 3⟩ : ℂ).im = min t 0 - 3 := rfl
      rw [hh]; have := min_le_left t 0; linarith
    have hz0' : (⟨0, min t 0 - 3⟩ : ℂ) ∈ (closedBox : Set ℂ)ᶜ := by
      rw [compl_closedBox_eq]; right; right; right
      have hh : (⟨0, min t 0 - 3⟩ : ℂ).im = min t 0 - 3 := rfl
      rw [hh]; have := min_le_right t 0; linarith
    exact IsPreconnected.union _ hz0 hz0' h1 isPreconnected_compl_closedBox
  apply IsPreconnected.subset_connectedComponentIn hpre _ _
  · right; exact h3i_box
  · rintro z (⟨hre, hlt⟩ | hz)
    · by_cases hlt2 : z.im < -2
      · intro hzJ
        have hzcl : z ∈ closedBox := hJbox hzJ
        have : |z.im| ≤ 2 := hzcl.2
        rw [abs_of_neg (by linarith)] at this
        linarith
      · intro hzJ
        refine hfree z ?_ hlt hzJ
        have hzcl : z ∈ closedBox := hJbox hzJ
        have h2 : z.im ≤ 2 := by have hh := hzcl.2; rw [abs_le] at hh; exact hh.2
        exact ⟨hre, by linarith, h2⟩
    · intro hzJ; exact hz (hJbox hzJ)

/-- The upward ray of `vSeg` from level `t`, together with the complement of the box, is contained
in the unbounded component (when it is free of `J`). -/
theorem ray_gt_subset_Uinf {J : Set ℂ} (hJbox : J ⊆ closedBox) {t : ℝ}
    (hfree : ∀ z ∈ vSeg, t < z.im → z ∉ J) :
    {z : ℂ | z.re = 0 ∧ t < z.im} ∪ (closedBox : Set ℂ)ᶜ
      ⊆ connectedComponentIn Jᶜ (3 * Complex.I) := by
  have h3i_box : (3 * Complex.I : ℂ) ∈ (closedBox : Set ℂ)ᶜ := by
    rw [compl_closedBox_eq]; exact Or.inr (Or.inr (Or.inl (by norm_num)))
  have hpre : IsPreconnected ({z : ℂ | z.re = 0 ∧ t < z.im} ∪ (closedBox : Set ℂ)ᶜ) := by
    have h1 : IsPreconnected {z : ℂ | z.re = 0 ∧ t < z.im} := by
      have himg : {z : ℂ | z.re = 0 ∧ t < z.im}
          = (fun s : ℝ => (s : ℂ) * Complex.I) '' (Set.Ioi t) := by
        ext z; constructor
        · rintro ⟨hre, h1⟩
          exact ⟨z.im, by simpa using h1, (eq_of_re_zero hre).symm⟩
        · rintro ⟨s, hs, rfl⟩
          exact ⟨by simp, by simpa using hs⟩
      rw [himg]
      exact (isPreconnected_Ioi (a := t)).image _ (by fun_prop)
    have hz0 : (⟨0, max t 0 + 3⟩ : ℂ) ∈ {z : ℂ | z.re = 0 ∧ t < z.im} := by
      refine ⟨rfl, ?_⟩
      have hh : (⟨0, max t 0 + 3⟩ : ℂ).im = max t 0 + 3 := rfl
      rw [hh]; have := le_max_left t 0; linarith
    have hz0' : (⟨0, max t 0 + 3⟩ : ℂ) ∈ (closedBox : Set ℂ)ᶜ := by
      rw [compl_closedBox_eq]; right; right; left
      have hh : (⟨0, max t 0 + 3⟩ : ℂ).im = max t 0 + 3 := rfl
      rw [hh]; have := le_max_right t 0; linarith
    exact IsPreconnected.union _ hz0 hz0' h1 isPreconnected_compl_closedBox
  apply IsPreconnected.subset_connectedComponentIn hpre _ _
  · right; exact h3i_box
  · rintro z (⟨hre, hlt⟩ | hz)
    · by_cases hlt2 : 2 < z.im
      · intro hzJ
        have hzcl : z ∈ closedBox := hJbox hzJ
        have : |z.im| ≤ 2 := hzcl.2
        rw [abs_of_pos (by linarith)] at this
        linarith
      · intro hzJ
        refine hfree z ?_ hlt hzJ
        have hzcl : z ∈ closedBox := hJbox hzJ
        have h2 : -2 ≤ z.im := by have hh := hzcl.2; rw [abs_le] at hh; exact hh.1
        exact ⟨hre, h2, by linarith⟩
    · intro hzJ; exact hz (hJbox hzJ)

/-! ### Straight-line segments -/

theorem segment_formula (a b : ℂ) (t : unitInterval) :
    (Path.segment a b) t = (1 - (t : ℝ)) * a + (t : ℝ) * b := by
  rw [Path.segment_apply, AffineMap.lineMap_apply_module, Complex.real_smul, Complex.real_smul]
  push_cast; ring

theorem segment_formula' (a b : ℂ) (t : unitInterval) :
    (Path.segment a b) t = (1 - (t : ℝ)) • a + (t : ℝ) • b := by
  rw [Path.segment_apply, AffineMap.lineMap_apply_module]

theorem segment_re (a b : ℂ) (t : unitInterval) :
    ((Path.segment a b) t).re = (1 - (t : ℝ)) * a.re + (t : ℝ) * b.re := by
  rw [Path.segment_apply, AffineMap.lineMap_apply_module]
  simp [Complex.add_re, Complex.mul_re]

theorem segment_im (a b : ℂ) (t : unitInterval) :
    ((Path.segment a b) t).im = (1 - (t : ℝ)) * a.im + (t : ℝ) * b.im := by
  rw [Path.segment_apply, AffineMap.lineMap_apply_module]
  simp [Complex.add_im, Complex.mul_im]

theorem segment_re_zero (a b : ℂ) (ha : a.re = 0) (hb : b.re = 0) (t : unitInterval) :
    ((Path.segment a b) t).re = 0 := by
  rw [segment_re, ha, hb]; ring

theorem segment_ne_pm_one (a b : ℂ) (ha : a.re = 0) (hb : b.re = 0) (t : unitInterval) :
    (Path.segment a b) t ≠ -1 ∧ (Path.segment a b) t ≠ 1 := by
  have hre := segment_re_zero a b ha hb t
  constructor <;> intro h
  · have hh := congrArg Complex.re h
    rw [hre] at hh
    rw [show ((-1 : ℂ)).re = -1 from rfl] at hh
    linarith
  · have hh := congrArg Complex.re h
    rw [hre] at hh
    rw [show ((1 : ℂ)).re = 1 from rfl] at hh
    linarith

theorem segment_mem_vSeg {a b : ℂ} (ha : a ∈ vSeg) (hb : b ∈ vSeg) (t : unitInterval) :
    (Path.segment a b) t ∈ vSeg := by
  rw [segment_formula']
  exact vSeg_convex ha hb (by linarith [t.2.2]) (by linarith [t.2.1]) (by ring)

theorem segment_mem_closedBox {a b : ℂ} (ha : a ∈ closedBox) (hb : b ∈ closedBox)
    (t : unitInterval) : (Path.segment a b) t ∈ closedBox := by
  obtain ⟨ha1, ha2⟩ := ha
  obtain ⟨hb1, hb2⟩ := hb
  have ha1' : -1 ≤ a.re ∧ a.re ≤ 1 := abs_le.mp ha1
  have ha2' : -2 ≤ a.im ∧ a.im ≤ 2 := abs_le.mp ha2
  have hb1' : -1 ≤ b.re ∧ b.re ≤ 1 := abs_le.mp hb1
  have hb2' : -2 ≤ b.im ∧ b.im ≤ 2 := abs_le.mp hb2
  have hre := segment_re a b t
  have him := segment_im a b t
  refine ⟨?_, ?_⟩
  · rw [abs_le, hre]
    constructor <;> nlinarith [t.2.1, t.2.2, ha1'.1, ha1'.2, hb1'.1, hb1'.2]
  · rw [abs_le, him]
    constructor <;> nlinarith [t.2.1, t.2.2, ha2'.1, ha2'.2, hb2'.1, hb2'.2]

theorem segment_im_between {a b : ℂ} (h : a.im ≤ b.im) (t : unitInterval) :
    a.im ≤ ((Path.segment a b) t).im ∧ ((Path.segment a b) t).im ≤ b.im := by
  have hh : ((Path.segment a b) t).im = (1 - (t:ℝ)) * a.im + (t:ℝ) * b.im := segment_im a b t
  constructor
  · rw [hh]; nlinarith [t.2.1, t.2.2, h]
  · rw [hh]; nlinarith [t.2.1, t.2.2, h]

theorem convex_closedBox : Convex ℝ closedBox := by
  intro x hx y hy a b ha hb hab
  obtain ⟨hx1, hx2⟩ := hx
  obtain ⟨hy1, hy2⟩ := hy
  have hx1' : -1 ≤ x.re ∧ x.re ≤ 1 := abs_le.mp hx1
  have hx2' : -2 ≤ x.im ∧ x.im ≤ 2 := abs_le.mp hx2
  have hy1' : -1 ≤ y.re ∧ y.re ≤ 1 := abs_le.mp hy1
  have hy2' : -2 ≤ y.im ∧ y.im ≤ 2 := abs_le.mp hy2
  have hre : (a • x + b • y).re = a * x.re + b * y.re := by
    rw [Complex.real_smul, Complex.real_smul]; simp [Complex.add_re, Complex.mul_re]
  have him : (a • x + b • y).im = a * x.im + b * y.im := by
    rw [Complex.real_smul, Complex.real_smul]; simp [Complex.add_im, Complex.mul_im]
  rw [closedBox]
  refine ⟨?_, ?_⟩
  · rw [abs_le, hre]
    exact ⟨by nlinarith [hx1'.1, hy1'.1], by nlinarith [hx1'.2, hy1'.2]⟩
  · rw [abs_le, him]
    exact ⟨by nlinarith [hx2'.1, hy2'.1], by nlinarith [hx2'.2, hy2'.2]⟩

/-- **At most two complementary components from a free window.** -/
theorem atMostTwo_of_windowConfig {J : Set ℂ} (hJc : IsClosed J)
    (hJbox : J ⊆ closedBox)
    (hcl : ∀ w : ℂ, w ∉ J → (-1 : ℂ) ∈ closure (connectedComponentIn Jᶜ w) ∧
                                 (1 : ℂ) ∈ closure (connectedComponentIn Jᶜ w))
    {l m k j : ℂ} (hlJ : l ∈ J) (hmJ : m ∈ J) (hkJ : k ∈ J) (hjJ : j ∈ J)
    (hlSeg : l ∈ vSeg) (hmSeg : m ∈ vSeg) (hkSeg : k ∈ vSeg) (hjSeg : j ∈ vSeg)
    (hj2 : -2 < j.im) (hl2 : l.im < 2) (hkm : k.im < m.im)
    (hmkfree : ∀ z ∈ vSeg, k.im < z.im → z.im < m.im → z ∉ J)
    (hjfree : ∀ z ∈ vSeg, z.im < j.im → z ∉ J)
    (hlfree : ∀ z ∈ vSeg, l.im < z.im → z ∉ J)
    {δ₁ : Path m l} (hδ₁J : ∀ t, δ₁ t ∈ J) (hδ₁av : ∀ t, δ₁ t ≠ -1 ∧ δ₁ t ≠ 1)
    {δ₂ : Path k j} (hδ₂J : ∀ t, δ₂ t ∈ J) (hδ₂av : ∀ t, δ₂ t ≠ -1 ∧ δ₂ t ≠ 1)
    {x y z : ℂ} (hx : x ∉ J) (hy : y ∉ J) (hz : z ∉ J) :
    connectedComponentIn Jᶜ x = connectedComponentIn Jᶜ y ∨
    connectedComponentIn Jᶜ x = connectedComponentIn Jᶜ z ∨
    connectedComponentIn Jᶜ y = connectedComponentIn Jᶜ z := by
  classical
  set X₀ : ℂ := (⟨0, (k.im + m.im) / 2⟩ : ℂ) with hX₀def
  set U : Set ℂ := connectedComponentIn Jᶜ X₀ with hUdef
  set Uinf : Set ℂ := connectedComponentIn Jᶜ (3 * Complex.I) with hUinfdef
  have hboxUinf : (closedBox : Set ℂ)ᶜ ⊆ Uinf := by
    rw [hUinfdef]
    refine IsPreconnected.subset_connectedComponentIn isPreconnected_compl_closedBox ?_ ?_
    · rw [compl_closedBox_eq]; exact Or.inr (Or.inr (Or.inl (by norm_num)))
    · intro z hz hzJ; exact hz (hJbox hzJ)
  have hwinU : {z : ℂ | z.re = 0 ∧ k.im < z.im ∧ z.im < m.im} ⊆ U := by
    rw [hUdef, hX₀def]; exact window_subset_componentIn hkSeg hmSeg hkm hmkfree
  have hrayBot : {z : ℂ | z.re = 0 ∧ z.im < j.im} ∪ (closedBox : Set ℂ)ᶜ ⊆ Uinf := by
    rw [hUinfdef]; exact ray_lt_subset_Uinf hJbox hjfree
  have hrayTop : {z : ℂ | z.re = 0 ∧ l.im < z.im} ∪ (closedBox : Set ℂ)ᶜ ⊆ Uinf := by
    rw [hUinfdef]; exact ray_gt_subset_Uinf hJbox hlfree
  -- the bottom-to-top path σ
  set σ : Path ptBot ptTop :=
    ((Path.segment ptBot j).trans δ₂.symm).trans
      ((Path.segment k m).trans (δ₁.trans (Path.segment l ptTop))) with hσdef
  have hσmem : ∀ t, σ t ∈ U ∪ Uinf ∪ (J : Set ℂ) := by
    have hA : ∀ t, (Path.segment ptBot j) t ∈ U ∪ Uinf ∪ (J : Set ℂ) := by
      intro t
      have hre : ((Path.segment ptBot j) t).re = 0 := by
        rw [segment_re, ptBot_re, hjSeg.1]; ring
      have him : ((Path.segment ptBot j) t).im = (1 - (t:ℝ)) * (-2) + (t:ℝ) * j.im := by
        rw [segment_im, ptBot_im]
      by_cases ht : (t:ℝ) = 1
      · right
        have hz : (Path.segment ptBot j) t = j := by rw [segment_formula, ht]; simp
        rw [hz]; exact hjJ
      · have ht1 : (t:ℝ) < 1 := lt_of_le_of_ne t.2.2 ht
        left; right
        apply hrayBot; left
        exact ⟨hre, by rw [him]; nlinarith [ht1, hj2]⟩
    have hB : ∀ t, δ₂.symm t ∈ U ∪ Uinf ∪ (J : Set ℂ) := by
      intro t; right; rw [Path.symm_apply]; exact hδ₂J _
    have hC : ∀ t, (Path.segment k m) t ∈ U ∪ Uinf ∪ (J : Set ℂ) := by
      intro t
      have hre : ((Path.segment k m) t).re = 0 := by
        rw [segment_re, hkSeg.1, hmSeg.1]; ring
      have him : ((Path.segment k m) t).im = (1 - (t:ℝ)) * k.im + (t:ℝ) * m.im :=
        segment_im k m t
      by_cases ht0 : (t:ℝ) = 0
      · right
        have hz : (Path.segment k m) t = k := by rw [segment_formula, ht0]; simp
        rw [hz]; exact hkJ
      · by_cases ht1 : (t:ℝ) = 1
        · right
          have hz : (Path.segment k m) t = m := by rw [segment_formula, ht1]; simp
          rw [hz]; exact hmJ
        · have h0 : 0 < (t:ℝ) := lt_of_le_of_ne t.2.1 (Ne.symm ht0)
          have h1 : (t:ℝ) < 1 := lt_of_le_of_ne t.2.2 ht1
          left; left
          apply hwinU
          refine ⟨hre, ?_, ?_⟩
          · rw [him]; nlinarith [hkm, h0, h1]
          · rw [him]; nlinarith [hkm, h0, h1]
    have hD : ∀ t, δ₁ t ∈ U ∪ Uinf ∪ (J : Set ℂ) := by
      intro t; right; exact hδ₁J t
    have hE : ∀ t, (Path.segment l ptTop) t ∈ U ∪ Uinf ∪ (J : Set ℂ) := by
      intro t
      have hre : ((Path.segment l ptTop) t).re = 0 := by
        rw [segment_re, hlSeg.1, ptTop_re]; ring
      have him : ((Path.segment l ptTop) t).im = (1 - (t:ℝ)) * l.im + (t:ℝ) * 2 := by
        rw [segment_im, ptTop_im]
      by_cases ht0 : (t:ℝ) = 0
      · right
        have hz : (Path.segment l ptTop) t = l := by rw [segment_formula, ht0]; simp
        rw [hz]; exact hlJ
      · have h0 : 0 < (t:ℝ) := lt_of_le_of_ne t.2.1 (Ne.symm ht0)
        left; right
        apply hrayTop; left
        exact ⟨hre, by rw [him]; nlinarith [h0, hl2]⟩
    have h1 : ∀ t, ((Path.segment ptBot j).trans δ₂.symm) t ∈ U ∪ Uinf ∪ (J : Set ℂ) :=
      trans_mem _ _ hA hB
    have h2 : ∀ t, ((Path.segment k m).trans (δ₁.trans (Path.segment l ptTop))) t
        ∈ U ∪ Uinf ∪ (J : Set ℂ) := trans_mem _ _ hC (trans_mem _ _ hD hE)
    intro t; rw [hσdef]; exact trans_mem _ _ h1 h2 t
  have hσsub : Set.range (σ : unitInterval → ℂ) ⊆ U ∪ Uinf ∪ (J : Set ℂ) :=
    fun z ⟨t, ht⟩ => ht ▸ hσmem t
  have hσav : ∀ t, σ t ≠ -1 ∧ σ t ≠ 1 := by
    have hA : ∀ t, (Path.segment ptBot j) t ∈ {z : ℂ | z ≠ -1 ∧ z ≠ 1} :=
      fun t => segment_ne_pm_one _ _ ptBot_re hjSeg.1 t
    have hB : ∀ t, δ₂.symm t ∈ {z : ℂ | z ≠ -1 ∧ z ≠ 1} := by
      intro t; rw [Path.symm_apply]; exact hδ₂av _
    have hC : ∀ t, (Path.segment k m) t ∈ {z : ℂ | z ≠ -1 ∧ z ≠ 1} :=
      fun t => segment_ne_pm_one _ _ hkSeg.1 hmSeg.1 t
    have hD : ∀ t, δ₁ t ∈ {z : ℂ | z ≠ -1 ∧ z ≠ 1} := hδ₁av
    have hE : ∀ t, (Path.segment l ptTop) t ∈ {z : ℂ | z ≠ -1 ∧ z ≠ 1} :=
      fun t => segment_ne_pm_one _ _ hlSeg.1 ptTop_re t
    have h1 : ∀ t, ((Path.segment ptBot j).trans δ₂.symm) t ∈ {z : ℂ | z ≠ -1 ∧ z ≠ 1} :=
      trans_mem _ _ hA hB
    have h2 : ∀ t, ((Path.segment k m).trans (δ₁.trans (Path.segment l ptTop))) t
        ∈ {z : ℂ | z ≠ -1 ∧ z ≠ 1} := trans_mem _ _ hC (trans_mem _ _ hD hE)
    intro t; rw [hσdef]; exact trans_mem _ _ h1 h2 t
  have hσbox : ∀ t, σ t ∈ closedBox := by
    have hA : ∀ t, (Path.segment ptBot j) t ∈ closedBox :=
      fun t => vSeg_subset_closedBox (segment_mem_vSeg ptBot_mem_vSeg hjSeg t)
    have hB : ∀ t, δ₂.symm t ∈ closedBox := by
      intro t; rw [Path.symm_apply]; exact hJbox (hδ₂J _)
    have hC : ∀ t, (Path.segment k m) t ∈ closedBox :=
      fun t => vSeg_subset_closedBox (segment_mem_vSeg hkSeg hmSeg t)
    have hD : ∀ t, δ₁ t ∈ closedBox := fun t => hJbox (hδ₁J t)
    have hE : ∀ t, (Path.segment l ptTop) t ∈ closedBox :=
      fun t => vSeg_subset_closedBox (segment_mem_vSeg hlSeg ptTop_mem_vSeg t)
    have h1 : ∀ t, ((Path.segment ptBot j).trans δ₂.symm) t ∈ closedBox := trans_mem _ _ hA hB
    have h2 : ∀ t, ((Path.segment k m).trans (δ₁.trans (Path.segment l ptTop))) t ∈ closedBox :=
      trans_mem _ _ hC (trans_mem _ _ hD hE)
    intro t; rw [hσdef]; exact trans_mem _ _ h1 h2 t
  -- every component is `U` or `Uinf`
  have hkey : ∀ w : ℂ, w ∉ J → connectedComponentIn Jᶜ w = U ∨ connectedComponentIn Jᶜ w = Uinf := by
    intro w hw
    by_contra hcon
    rw [not_or] at hcon
    obtain ⟨hneU, hneUinf⟩ := hcon
    set G : Set ℂ := connectedComponentIn Jᶜ w with hGdef
    have hGsub : G ⊆ Jᶜ := by rw [hGdef]; exact connectedComponentIn_subset _ _
    have hGbox : G ⊆ closedBox := by
      intro z hzG
      by_contra hzbox
      have hzUinf : z ∈ Uinf := hboxUinf hzbox
      have h1 : connectedComponentIn Jᶜ w = connectedComponentIn Jᶜ z :=
        connectedComponentIn_eq hzG
      have h2 : connectedComponentIn Jᶜ (3 * Complex.I) = connectedComponentIn Jᶜ z := by
        rw [← hUinfdef]; exact connectedComponentIn_eq (by rwa [hUinfdef] at hzUinf)
      exact hneUinf (by rw [hGdef, hUinfdef]; exact h1.trans h2.symm)
    have hclw := hcl w hw
    have hσcpt : IsCompact (Set.range (σ : unitInterval → ℂ)) := isCompact_range σ.continuous
    have hσcl : IsClosed (Set.range (σ : unitInterval → ℂ)) := hσcpt.isClosed
    have h1not : (1:ℂ) ∉ Set.range (σ : unitInterval → ℂ) := fun ⟨t, ht⟩ => (hσav t).2 ht
    have hm1not : (-1:ℂ) ∉ Set.range (σ : unitInterval → ℂ) := fun ⟨t, ht⟩ => (hσav t).1 ht
    obtain ⟨ε, hε, hεsub⟩ := Metric.isOpen_iff.mp hσcl.isOpen_compl (-1) hm1not
    obtain ⟨δ, hδ, hδsub⟩ := Metric.isOpen_iff.mp hσcl.isOpen_compl 1 h1not
    set ρ : ℝ := min ε δ with hρdef
    have hρ : 0 < ρ := by rw [hρdef]; exact lt_min hε hδ
    have hball1 : Metric.ball (-1) ρ ⊆ (Set.range (σ : unitInterval → ℂ))ᶜ :=
      fun z hz => hεsub (Metric.ball_subset_ball (by rw [hρdef]; exact min_le_left _ _) hz)
    have hball2 : Metric.ball (1:ℂ) ρ ⊆ (Set.range (σ : unitInterval → ℂ))ᶜ :=
      fun z hz => hδsub (Metric.ball_subset_ball (by rw [hρdef]; exact min_le_right _ _) hz)
    obtain ⟨a₁, ha₁G, ha₁b⟩ := Metric.mem_closure_iff.mp hclw.1 ρ hρ
    obtain ⟨b₁, hb₁G, hb₁b⟩ := Metric.mem_closure_iff.mp hclw.2 ρ hρ
    have ha₁box : a₁ ∈ closedBox := hGbox ha₁G
    have hb₁box : b₁ ∈ closedBox := hGbox hb₁G
    have ha₁ball : a₁ ∈ Metric.ball (-1) ρ := by rw [Metric.mem_ball, dist_comm]; exact ha₁b
    have hb₁ball : b₁ ∈ Metric.ball (1:ℂ) ρ := by rw [Metric.mem_ball, dist_comm]; exact hb₁b
    have ha₁Jc : a₁ ∈ Jᶜ := hGsub ha₁G
    have hb₁comp : b₁ ∈ connectedComponentIn Jᶜ a₁ := by
      have h : connectedComponentIn Jᶜ w = connectedComponentIn Jᶜ a₁ :=
        connectedComponentIn_eq (by rw [← hGdef]; exact ha₁G)
      rw [← h]; exact hb₁G
    obtain ⟨β, hβ⟩ : JoinedIn Jᶜ a₁ b₁ :=
      Work.Smooth.JordanSeparation.joinedIn_of_mem_connectedComponentIn hJc.isOpen_compl ha₁Jc hb₁comp
    have hβG : ∀ t, β t ∈ G := by
      have hpre : IsPreconnected (Set.range (β : unitInterval → ℂ)) := by
        rw [← Set.image_univ]
        exact isPreconnected_univ.image _ β.continuous.continuousOn
      have h0 : β 0 ∈ Set.range (β : unitInterval → ℂ) := ⟨0, rfl⟩
      have hsub := IsPreconnected.subset_connectedComponentIn hpre h0
        (fun x hx => by obtain ⟨s, rfl⟩ := hx; exact hβ s)
      have hGeq : G = connectedComponentIn Jᶜ a₁ := by
        rw [hGdef]; exact connectedComponentIn_eq (by rw [← hGdef]; exact ha₁G)
      intro t
      have := hsub ⟨t, rfl⟩
      rw [show β 0 = a₁ from β.source] at this
      rw [hGeq]; exact this
    set lamPt : Path (-1) 1 := (Path.segment (-1) a₁).trans (β.trans (Path.segment b₁ 1)) with hlamPtdef
    have hlamPtav : ∀ t, lamPt t ∉ Set.range (σ : unitInterval → ℂ) := by
      have hP1 : ∀ t, (Path.segment (-1) a₁) t ∈ (Set.range (σ : unitInterval → ℂ))ᶜ := by
        intro t
        apply hball1
        rw [segment_formula']
        exact convex_ball (-1) ρ (by rw [Metric.mem_ball]; simpa using hρ) ha₁ball
          (by linarith [t.2.2]) (by linarith [t.2.1]) (by ring)
      have hPg : ∀ t, β t ∈ (Set.range (σ : unitInterval → ℂ))ᶜ := by
        intro t htσ
        have hzsub := hσsub htσ
        rcases hzsub with (hU | hUi) | hJ
        · have h1 : connectedComponentIn Jᶜ w = connectedComponentIn Jᶜ (β t) :=
            connectedComponentIn_eq (by rw [← hGdef]; exact hβG t)
          have h2 : connectedComponentIn Jᶜ X₀ = connectedComponentIn Jᶜ (β t) := by
            rw [hUdef] at hU; exact connectedComponentIn_eq hU
          exact hneU (by rw [hGdef, hUdef]; exact h1.trans h2.symm)
        · have h1 : connectedComponentIn Jᶜ w = connectedComponentIn Jᶜ (β t) :=
            connectedComponentIn_eq (by rw [← hGdef]; exact hβG t)
          have h2 : connectedComponentIn Jᶜ (3 * Complex.I) = connectedComponentIn Jᶜ (β t) := by
            rw [← hUinfdef]; exact connectedComponentIn_eq (by rwa [hUinfdef] at hUi)
          exact hneUinf (by rw [hGdef, hUinfdef]; exact h1.trans h2.symm)
        · exact hGsub (hβG t) hJ
      have hP2 : ∀ t, (Path.segment b₁ 1) t ∈ (Set.range (σ : unitInterval → ℂ))ᶜ := by
        intro t
        apply hball2
        rw [segment_formula']
        exact convex_ball (1:ℂ) ρ hb₁ball (by rw [Metric.mem_ball]; simpa using hρ)
          (by linarith [t.2.2]) (by linarith [t.2.1]) (by ring)
      intro t
      rw [hlamPtdef]
      exact trans_mem _ _ hP1 (trans_mem _ _ hPg hP2) t
    have hlamPtbox : ∀ t, lamPt t ∈ closedBox := by
      have hP1 : ∀ t, (Path.segment (-1) a₁) t ∈ closedBox :=
        fun t => segment_mem_closedBox neg1_mem_closedBox ha₁box t
      have hPg : ∀ t, β t ∈ closedBox := fun t => hGbox (hβG t)
      have hP2 : ∀ t, (Path.segment b₁ 1) t ∈ closedBox :=
        fun t => segment_mem_closedBox hb₁box one_mem_closedBox t
      intro t; rw [hlamPtdef]; exact trans_mem _ _ hP1 (trans_mem _ _ hPg hP2) t
    -- reparametrise to [-1,1] and cross
    set hL : ℝ → ℂ := fun s => lamPt.extend ((s + 1) / 2) with hhL
    set vL : ℝ → ℂ := fun s => σ.extend ((s + 1) / 2) with hvL
    have hhcont : Continuous hL := by rw [hhL]; fun_prop
    have hvcont : Continuous vL := by rw [hvL]; fun_prop
    have hhbox : ∀ s ∈ Set.Icc (-1:ℝ) 1, |(hL s).re| ≤ 1 ∧ |(hL s).im| ≤ 2 := by
      intro s hs; rw [hhL]; exact hlamPtbox _
    have hvbox : ∀ s ∈ Set.Icc (-1:ℝ) 1, |(vL s).re| ≤ 1 ∧ |(vL s).im| ≤ 2 := by
      intro s hs; rw [hvL]; exact hσbox _
    have hh_left : (hL (-1)).re = -1 := by
      rw [hhL]; dsimp only
      rw [show ((-1:ℝ) + 1) / 2 = 0 from by norm_num, Path.extend_zero]
      norm_num
    have hh_right : (hL 1).re = 1 := by
      rw [hhL]; dsimp only
      rw [show ((1:ℝ) + 1) / 2 = 1 from by norm_num, Path.extend_one]
      norm_num
    have hv_bot : (vL (-1)).im = -2 := by
      rw [hvL]; dsimp only
      rw [show ((-1:ℝ) + 1) / 2 = 0 from by norm_num, Path.extend_zero]
      exact ptBot_im
    have hv_top : (vL 1).im = 2 := by
      rw [hvL]; dsimp only
      rw [show ((1:ℝ) + 1) / 2 = 1 from by norm_num, Path.extend_one]
      exact ptTop_im
    obtain ⟨s, hs, t, ht, heq⟩ :=
      crossing_rect hhcont hvcont hhbox hvbox hh_left hh_right hv_bot hv_top
    have hmem : hL s ∈ Set.range (σ : unitInterval → ℂ) := by
      rw [hvL] at heq
      exact ⟨_, heq.symm⟩
    rw [hhL] at hmem
    dsimp only at hmem
    exact hlamPtav _ hmem
  rcases hkey x hx with hxU | hxU <;> rcases hkey y hy with hyU | hyU <;>
    rcases hkey z hz with hzU | hzU
  · exact Or.inl (by rw [hxU, hyU])
  · exact Or.inl (by rw [hxU, hyU])
  · exact Or.inr (Or.inl (by rw [hxU, hzU]))
  · exact Or.inr (Or.inr (by rw [hyU, hzU]))
  · exact Or.inr (Or.inr (by rw [hyU, hzU]))
  · exact Or.inr (Or.inl (by rw [hxU, hzU]))
  · exact Or.inl (by rw [hxU, hyU])
  · exact Or.inl (by rw [hxU, hyU])

/-- **The Maehara free window (existence).** -/
theorem exists_windowConfig {γ : ℝ → ℂ} (hcont : Continuous γ)
    (hper : Function.Periodic γ (2 * Real.pi)) (hinj : Set.InjOn γ (Set.Ico 0 (2 * Real.pi)))
    (hsub : ∀ w ∈ Set.range γ, w ∈ rectR ∨ w = -1 ∨ w = 1)
    (hzero : γ 0 = -1) (hpos : 1 ∈ Set.range γ) :
    ∃ l m k j : ℂ, ∃ δ₁ : Path m l, ∃ δ₂ : Path k j,
      l ∈ Set.range γ ∧ m ∈ Set.range γ ∧ k ∈ Set.range γ ∧ j ∈ Set.range γ ∧
      l ∈ vSeg ∧ m ∈ vSeg ∧ k ∈ vSeg ∧ j ∈ vSeg ∧
      -2 < j.im ∧ j.im ≤ k.im ∧ k.im < m.im ∧ m.im ≤ l.im ∧ l.im < 2 ∧
      (∀ z ∈ vSeg, k.im < z.im → z.im < m.im → z ∉ Set.range γ) ∧
      (∀ z ∈ vSeg, z.im < j.im → z ∉ Set.range γ) ∧
      (∀ z ∈ vSeg, l.im < z.im → z ∉ Set.range γ) ∧
      (∀ t, δ₁ t ∈ Set.range γ) ∧ (∀ t, δ₁ t ≠ -1 ∧ δ₁ t ≠ 1) ∧
      (∀ t, δ₂ t ∈ Set.range γ) ∧ (∀ t, δ₂ t ≠ -1 ∧ δ₂ t ≠ 1) := by
  classical
  have hπ : (0 : ℝ) < 2 * Real.pi := by positivity
  -- the point `1` on the curve, with parameter `θ ∈ (0, 2π)`
  obtain ⟨t₁, ht₁⟩ := hpos
  obtain ⟨n₀, hn₀⟩ := exists_int_mul_add_mem_Ico hπ 0 t₁
  set θ : ℝ := t₁ + (n₀ : ℝ) * (2 * Real.pi) with hθdef
  have hγθ : γ θ = 1 := by
    rw [hθdef]; exact ((hper.int_mul n₀) t₁).trans ht₁
  have hθIco : θ ∈ Set.Ico 0 (2 * Real.pi) := ⟨hn₀.1, by linarith [hn₀.2]⟩
  have hθpos : 0 < θ := by
    rcases lt_or_eq_of_le hθIco.1 with h | h
    · exact h
    · exfalso
      have h1 : γ θ = -1 := by rw [← h]; exact hzero
      rw [hγθ] at h1; norm_num at h1
  have hθlt : θ < 2 * Real.pi := hθIco.2
  have hγ2π : γ (2 * Real.pi) = -1 := by
    have h := hper 0; simp only [zero_add] at h; rw [h, hzero]
  set A : Set ℂ := γ '' Set.Icc 0 θ with hA
  set B : Set ℂ := γ '' Set.Icc θ (2 * Real.pi) with hB
  have hIcc_union : Set.Icc (0 : ℝ) θ ∪ Set.Icc θ (2 * Real.pi) = Set.Icc 0 (2 * Real.pi) := by
    ext t; constructor
    · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
      · exact ⟨h1, le_trans h2 hθlt.le⟩
      · exact ⟨le_trans hθpos.le h1, h2⟩
    · rintro ⟨h1, h2⟩
      rcases le_or_gt t θ with h | h
      · exact Or.inl ⟨h1, h⟩
      · exact Or.inr ⟨le_of_lt h, h2⟩
  have hAB : A ∪ B = Set.range γ := by
    have h1 : A ∪ B = γ '' (Set.Icc 0 θ ∪ Set.Icc θ (2 * Real.pi)) := by
      rw [hA, hB, Set.image_union]
    rw [h1, hIcc_union, range_eq_image_Icc hper]
  have hinjA : Set.InjOn γ (Set.Icc 0 θ) := injOn_Icc_of_injOn_Ico hper hinj (by linarith [hθlt])
  have hinjB : Set.InjOn γ (Set.Icc θ (2 * Real.pi)) :=
    injOn_Icc_of_injOn_Ico hper hinj (by linarith [hθpos])
  have hAB_inter : A ∩ B ⊆ ({-1, 1} : Set ℂ) := by
    rintro w ⟨⟨u, hu, huw⟩, ⟨v, hv, hvw⟩⟩
    have huv : γ u = γ v := by rw [huw, hvw]
    obtain ⟨kk, hkk⟩ := exists_int_sub_eq_of_periodic_injOn hper hinj huv
    have hk_le : kk ≤ 0 := by
      by_contra hc
      have hc1 : (1 : ℤ) ≤ kk := by omega
      have hc' : (1 : ℝ) ≤ (kk : ℝ) := by exact_mod_cast hc1
      have h1 : 2 * Real.pi ≤ (kk : ℝ) * (2 * Real.pi) := by nlinarith [hc', hπ]
      have h2 : (kk : ℝ) * (2 * Real.pi) ≤ 0 := by linarith [hu.2, hv.1, hkk]
      linarith [hπ]
    have hk_ge : -1 ≤ kk := by
      by_contra hc
      have hc2 : kk ≤ -2 := by omega
      have hc' : (kk : ℝ) ≤ -2 := by exact_mod_cast hc2
      have h1 : (kk : ℝ) * (2 * Real.pi) ≤ (-2) * (2 * Real.pi) := by nlinarith [hc', hπ]
      have h2 : -(2 * Real.pi) ≤ (kk : ℝ) * (2 * Real.pi) := by linarith [hu.1, hv.2, hkk]
      linarith [hπ]
    have hk_cases : kk = 0 ∨ kk = -1 := by omega
    rcases hk_cases with hk | hk
    · right
      have hsub : u - v = 0 := by rw [hk] at hkk; push_cast at hkk; linarith
      have huv' : u = v := sub_eq_zero.mp hsub
      have huθ : u = θ := le_antisymm hu.2 (by rw [huv']; exact hv.1)
      rw [← huw, huθ, hγθ]
      simp
    · left
      have hsub : u - v = -(2 * Real.pi) := by rw [hk] at hkk; push_cast at hkk; linarith
      have hv2 : v = 2 * Real.pi := le_antisymm hv.2 (by linarith [hu.1, hsub])
      have hu0 : u = 0 := by linarith [hsub, hv2]
      rw [← huw, hu0, hzero]
  -- the topmost point `l` of the trace on `vSeg`
  have hJcompact : IsCompact (Set.range γ) := isCompact_range_of_periodic hcont hper
  have hKne : (Set.range γ ∩ vSeg).Nonempty := vSeg_meet hcont hsub ⟨0, hzero⟩ ⟨t₁, ht₁⟩
  have hKcompact : IsCompact (Set.range γ ∩ vSeg) := hJcompact.inter_right isClosed_vSeg
  obtain ⟨l, hlK, hlmax⟩ := hKcompact.exists_isMaxOn hKne Complex.continuous_im.continuousOn
  have hlJ : l ∈ Set.range γ := hlK.1
  have hlSeg : l ∈ vSeg := hlK.2
  have hlAB : l ∈ A ∪ B := by rw [hAB]; exact hlJ
  -- the two arcs `J₁` (through `l`) and `J₂`
  set c₁ : ℝ := if l ∈ A then 0 else θ with hc₁
  set d₁ : ℝ := if l ∈ A then θ else 2 * Real.pi with hd₁
  set c₂ : ℝ := if l ∈ A then θ else 0 with hc₂
  set d₂ : ℝ := if l ∈ A then 2 * Real.pi else θ with hd₂
  have hc₁d₁ : (c₁ = 0 ∧ d₁ = θ) ∨ (c₁ = θ ∧ d₁ = 2 * Real.pi) := by
    by_cases h : l ∈ A
    · left; exact ⟨by rw [hc₁, if_pos h], by rw [hd₁, if_pos h]⟩
    · right; exact ⟨by rw [hc₁, if_neg h], by rw [hd₁, if_neg h]⟩
  have hc₂d₂ : (c₂ = θ ∧ d₂ = 2 * Real.pi) ∨ (c₂ = 0 ∧ d₂ = θ) := by
    by_cases h : l ∈ A
    · left; exact ⟨by rw [hc₂, if_pos h], by rw [hd₂, if_pos h]⟩
    · right; exact ⟨by rw [hc₂, if_neg h], by rw [hd₂, if_neg h]⟩
  have hc₁_le_d₁ : c₁ ≤ d₁ := by
    rcases hc₁d₁ with ⟨e1, e2⟩ | ⟨e1, e2⟩ <;> rw [e1, e2] <;> linarith [hθpos, hθlt]
  have hc₂_le_d₂ : c₂ ≤ d₂ := by
    rcases hc₂d₂ with ⟨e1, e2⟩ | ⟨e1, e2⟩ <;> rw [e1, e2] <;> linarith [hθpos, hθlt]
  have hinj₁ : Set.InjOn γ (Set.Icc c₁ d₁) := by
    apply injOn_Icc_of_injOn_Ico hper hinj
    rcases hc₁d₁ with ⟨e1, e2⟩ | ⟨e1, e2⟩ <;> rw [e1, e2] <;> linarith [hθpos, hθlt]
  have hinj₂ : Set.InjOn γ (Set.Icc c₂ d₂) := by
    apply injOn_Icc_of_injOn_Ico hper hinj
    rcases hc₂d₂ with ⟨e1, e2⟩ | ⟨e1, e2⟩ <;> rw [e1, e2] <;> linarith [hθpos, hθlt]
  set J₁ : Set ℂ := γ '' Set.Icc c₁ d₁ with hJ₁
  set J₂ : Set ℂ := γ '' Set.Icc c₂ d₂ with hJ₂
  have hIcc12 : Set.Icc c₁ d₁ ∪ Set.Icc c₂ d₂ = Set.Icc 0 (2 * Real.pi) := by
    rw [hc₁, hd₁, hc₂, hd₂]
    by_cases h : l ∈ A
    · rw [if_pos h, if_pos h, if_pos h, if_pos h]; exact hIcc_union
    · rw [if_neg h, if_neg h, if_neg h, if_neg h, Set.union_comm]; exact hIcc_union
  have hJ₁J₂ : J₁ ∪ J₂ = Set.range γ := by
    rw [hJ₁, hJ₂, ← Set.image_union, hIcc12, range_eq_image_Icc hper]
  have hJ₁_sub : J₁ ⊆ Set.range γ := by rw [← hJ₁J₂]; exact Set.subset_union_left
  have hJ₂_sub : J₂ ⊆ Set.range γ := by rw [← hJ₁J₂]; exact Set.subset_union_right
  have hlJ₁ : l ∈ J₁ := by
    rw [hJ₁]
    by_cases h : l ∈ A
    · rw [hc₁, hd₁, if_pos h, if_pos h]; exact h
    · rw [hc₁, hd₁, if_neg h, if_neg h]
      rcases hlAB with h' | h'
      · exact absurd h' h
      · exact h'
  have hJ₁J₂_inter : J₁ ∩ J₂ ⊆ ({-1, 1} : Set ℂ) := by
    rw [hJ₁, hJ₂, hc₁, hd₁, hc₂, hd₂]
    by_cases h : l ∈ A
    · rw [if_pos h, if_pos h, if_pos h, if_pos h]; exact hAB_inter
    · rw [if_neg h, if_neg h, if_neg h, if_neg h, Set.inter_comm]; exact hAB_inter
  have hγc₁ : γ c₁ = -1 ∨ γ c₁ = 1 := by
    rcases hc₁d₁ with ⟨e1, _⟩ | ⟨e1, _⟩
    · rw [e1]; left; exact hzero
    · rw [e1]; right; exact hγθ
  have hγd₁ : γ d₁ = -1 ∨ γ d₁ = 1 := by
    rcases hc₁d₁ with ⟨_, e2⟩ | ⟨_, e2⟩
    · rw [e2]; right; exact hγθ
    · rw [e2]; left; exact hγ2π
  have hγc₂ : γ c₂ = -1 ∨ γ c₂ = 1 := by
    rcases hc₂d₂ with ⟨e1, _⟩ | ⟨e1, _⟩
    · rw [e1]; right; exact hγθ
    · rw [e1]; left; exact hzero
  have hγd₂ : γ d₂ = -1 ∨ γ d₂ = 1 := by
    rcases hc₂d₂ with ⟨_, e2⟩ | ⟨_, e2⟩
    · rw [e2]; left; exact hγ2π
    · rw [e2]; right; exact hγθ
  have hc₁d₁_lt : c₁ < d₁ := lt_of_le_of_ne hc₁_le_d₁ (by
    rcases hc₁d₁ with ⟨e1, e2⟩ | ⟨e1, e2⟩ <;> rw [e1, e2] <;> linarith [hθpos, hθlt])
  have hγcne : γ c₁ ≠ γ d₁ := fun h =>
    absurd (hinj₁ ⟨le_rfl, hc₁_le_d₁⟩ ⟨hc₁_le_d₁, le_rfl⟩ h) (ne_of_lt hc₁d₁_lt)
  have hγc₁d₁ : ({-1, 1} : Set ℂ) = ({γ c₁, γ d₁} : Set ℂ) := by
    rcases hγc₁ with h1 | h1 <;> rcases hγd₁ with h2 | h2
    · exact absurd (h1.trans h2.symm) hγcne
    · rw [h1, h2]
    · rw [h1, h2]; ext w; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto
    · exact absurd (h1.trans h2.symm) hγcne
  have hl_ne : l ≠ -1 ∧ l ≠ 1 := by
    constructor <;> intro h
    · have hh := congrArg Complex.re h; rw [hlSeg.1] at hh; norm_num at hh
    · have hh := congrArg Complex.re h; rw [hlSeg.1] at hh; norm_num at hh
  have havoid₁ : ∀ u ∈ Set.Ioo c₁ d₁, γ u ≠ -1 ∧ γ u ≠ 1 := by
    intro u hu
    have huIcc : u ∈ Set.Icc c₁ d₁ := ⟨hu.1.le, hu.2.le⟩
    have hne_c : γ u ≠ γ c₁ := fun h =>
      absurd (hinj₁ huIcc ⟨le_rfl, hc₁_le_d₁⟩ h) (ne_of_gt hu.1)
    have hne_d : γ u ≠ γ d₁ := fun h =>
      absurd (hinj₁ huIcc ⟨hc₁_le_d₁, le_rfl⟩ h) (ne_of_lt hu.2)
    constructor <;> intro hcon
    · have hmem : γ u ∈ ({-1, 1} : Set ℂ) := by rw [hcon]; left; rfl
      rw [hγc₁d₁] at hmem
      rcases hmem with h | h
      · exact hne_c h
      · exact hne_d h
    · have hmem : γ u ∈ ({-1, 1} : Set ℂ) := by rw [hcon]; right; rfl
      rw [hγc₁d₁] at hmem
      rcases hmem with h | h
      · exact hne_c h
      · exact hne_d h
  -- the lowest point `m` of `J₁` on `vSeg`
  have hK₁ne : (J₁ ∩ vSeg).Nonempty := ⟨l, hlJ₁, hlSeg⟩
  have hJ₁compact : IsCompact J₁ := by rw [hJ₁]; exact isCompact_Icc.image hcont
  have hK₁compact : IsCompact (J₁ ∩ vSeg) := hJ₁compact.inter_right isClosed_vSeg
  obtain ⟨m, hmK₁, hmmin⟩ := hK₁compact.exists_isMinOn hK₁ne Complex.continuous_im.continuousOn
  have hmJ₁ : m ∈ J₁ := hmK₁.1
  have hmSeg : m ∈ vSeg := hmK₁.2
  have hmJ : m ∈ Set.range γ := hJ₁_sub hmJ₁
  have hm_ne : m ≠ -1 ∧ m ≠ 1 := by
    constructor <;> intro h
    · have hh := congrArg Complex.re h; rw [hmSeg.1] at hh; norm_num at hh
    · have hh := congrArg Complex.re h; rw [hmSeg.1] at hh; norm_num at hh
  have hlJ₁' := hlJ₁
  obtain ⟨u_l, hu_l, hγu_l⟩ : ∃ u ∈ Set.Icc c₁ d₁, γ u = l := hlJ₁'
  have hmJ₁' := hmJ₁
  obtain ⟨u_m, hu_m, hγu_m⟩ : ∃ u ∈ Set.Icc c₁ d₁, γ u = m := hmJ₁'
  have hu_l_int : u_l ∈ Set.Ioo c₁ d₁ := by
    refine ⟨lt_of_le_of_ne hu_l.1 ?_, lt_of_le_of_ne hu_l.2 ?_⟩
    · intro h; rw [← h] at hγu_l
      rcases hγc₁ with hc | hc
      · exact hl_ne.1 (hγu_l.symm.trans hc)
      · exact hl_ne.2 (hγu_l.symm.trans hc)
    · intro h; rw [h] at hγu_l
      rcases hγd₁ with hc | hc
      · exact hl_ne.1 (hγu_l.symm.trans hc)
      · exact hl_ne.2 (hγu_l.symm.trans hc)
  have hu_m_int : u_m ∈ Set.Ioo c₁ d₁ := by
    refine ⟨lt_of_le_of_ne hu_m.1 ?_, lt_of_le_of_ne hu_m.2 ?_⟩
    · intro h; rw [← h] at hγu_m
      rcases hγc₁ with hc | hc
      · exact hm_ne.1 (hγu_m.symm.trans hc)
      · exact hm_ne.2 (hγu_m.symm.trans hc)
    · intro h; rw [h] at hγu_m
      rcases hγd₁ with hc | hc
      · exact hm_ne.1 (hγu_m.symm.trans hc)
      · exact hm_ne.2 (hγu_m.symm.trans hc)
  -- the arc `m → l` inside `J₁`
  let arc₁ : Path m l :=
    ⟨⟨fun t => γ (u_m + (t : ℝ) * (u_l - u_m)), hcont.comp (by fun_prop)⟩,
      by show γ (u_m + (↑(0 : unitInterval)) * (u_l - u_m)) = m
         rw [show ((0 : unitInterval) : ℝ) = 0 from rfl, zero_mul, add_zero]; exact hγu_m,
      by show γ (u_m + (↑(1 : unitInterval)) * (u_l - u_m)) = l
         rw [show ((1 : unitInterval) : ℝ) = 1 from rfl, one_mul,
           show u_m + (u_l - u_m) = u_l from by ring]; exact hγu_l⟩
  have harc₁_int : ∀ t : unitInterval, u_m + (t : ℝ) * (u_l - u_m) ∈ Set.Ioo c₁ d₁ := by
    intro t
    rcases le_or_gt u_m u_l with h | h
    · refine ⟨?_, ?_⟩ <;> nlinarith [hu_m_int.1, hu_l_int.1, hu_m_int.2, hu_l_int.2, h, t.2.1, t.2.2]
    · refine ⟨?_, ?_⟩ <;> nlinarith [hu_m_int.1, hu_l_int.1, hu_m_int.2, hu_l_int.2, h, t.2.1, t.2.2]
  have harc₁_sub : ∀ t, arc₁ t ∈ J₁ := by
    intro t
    rw [hJ₁]
    exact ⟨_, ⟨(harc₁_int t).1.le, (harc₁_int t).2.le⟩, rfl⟩
  have harc₁_ne : ∀ t, arc₁ t ≠ -1 ∧ arc₁ t ≠ 1 := fun t => havoid₁ _ (harc₁_int t)
  -- the crossing path `P` (bottom to top)
  set P : Path ptBot ptTop :=
    ((Path.segment ptBot m).trans arc₁).trans (Path.segment l ptTop) with hP
  have hPbox : ∀ t, P t ∈ closedBox := by
    have hA' : ∀ t, (Path.segment ptBot m) t ∈ closedBox :=
      fun t => vSeg_subset_closedBox (segment_mem_vSeg ptBot_mem_vSeg hmSeg t)
    have hB' : ∀ t, arc₁ t ∈ closedBox := fun t => range_subset_closedBox hsub (hJ₁_sub (harc₁_sub t))
    have hC' : ∀ t, (Path.segment l ptTop) t ∈ closedBox :=
      fun t => vSeg_subset_closedBox (segment_mem_vSeg hlSeg ptTop_mem_vSeg t)
    have h1 : ∀ t, ((Path.segment ptBot m).trans arc₁) t ∈ closedBox := trans_mem _ _ hA' hB'
    intro t; rw [hP]; exact trans_mem _ _ h1 hC' t
  -- the left-right path `Q` along `J₂`
  set s₂ : ℝ := if l ∈ A then 2 * Real.pi else 0 with hs₂
  have hs₂_cases : (s₂ = 2 * Real.pi ∧ c₂ = θ ∧ d₂ = 2 * Real.pi) ∨
      (s₂ = 0 ∧ c₂ = 0 ∧ d₂ = θ) := by
    by_cases h : l ∈ A
    · left; exact ⟨by rw [hs₂, if_pos h], by rw [hc₂, if_pos h], by rw [hd₂, if_pos h]⟩
    · right; exact ⟨by rw [hs₂, if_neg h], by rw [hc₂, if_neg h], by rw [hd₂, if_neg h]⟩
  have hγs₂ : γ s₂ = -1 := by
    rcases hs₂_cases with ⟨e, _, _⟩ | ⟨e, _, _⟩
    · rw [e]; exact hγ2π
    · rw [e]; exact hzero
  let Q : Path (-1 : ℂ) (1 : ℂ) :=
    ⟨⟨fun t => γ (s₂ + (t : ℝ) * (θ - s₂)), hcont.comp (by fun_prop)⟩,
      by show γ (s₂ + (↑(0 : unitInterval)) * (θ - s₂)) = -1
         rw [show ((0 : unitInterval) : ℝ) = 0 from rfl, zero_mul, add_zero]; exact hγs₂,
      by show γ (s₂ + (↑(1 : unitInterval)) * (θ - s₂)) = 1
         rw [show ((1 : unitInterval) : ℝ) = 1 from rfl, one_mul,
           show s₂ + (θ - s₂) = θ from by ring]; exact hγθ⟩
  have hQJ₂ : ∀ t, Q t ∈ J₂ := by
    intro t
    rw [hJ₂]
    refine ⟨s₂ + (t : ℝ) * (θ - s₂), ?_, rfl⟩
    rcases hs₂_cases with ⟨e1, e2, e3⟩ | ⟨e1, e2, e3⟩
    · rw [e1, e2, e3]
      constructor <;> nlinarith [t.2.1, t.2.2, hθpos, hθlt]
    · rw [e1, e2, e3]
      constructor <;> nlinarith [t.2.1, t.2.2, hθpos, hθlt]
  have hQbox : ∀ t, Q t ∈ closedBox := fun t => range_subset_closedBox hsub (hJ₂_sub (hQJ₂ t))
  -- reparametrise and cross
  set hP' : ℝ → ℂ := fun s => P.extend ((s + 1) / 2) with hP'def
  set hQ' : ℝ → ℂ := fun s => Q.extend ((s + 1) / 2) with hQ'def
  have hP'cont : Continuous hP' := by rw [hP'def]; fun_prop
  have hQ'cont : Continuous hQ' := by rw [hQ'def]; fun_prop
  have hP'box : ∀ s ∈ Set.Icc (-1 : ℝ) 1, |(hP' s).re| ≤ 1 ∧ |(hP' s).im| ≤ 2 := by
    intro s hs
    have hs' : (s + 1) / 2 ∈ Set.Icc (0 : ℝ) 1 := ⟨by linarith [hs.1], by linarith [hs.2]⟩
    have he : hP' s = P ⟨(s + 1) / 2, hs'⟩ := by
      rw [hP'def]; dsimp only; exact Path.extend_apply P hs'
    rw [he]; exact hPbox _
  have hQ'box : ∀ s ∈ Set.Icc (-1 : ℝ) 1, |(hQ' s).re| ≤ 1 ∧ |(hQ' s).im| ≤ 2 := by
    intro s hs
    have hs' : (s + 1) / 2 ∈ Set.Icc (0 : ℝ) 1 := ⟨by linarith [hs.1], by linarith [hs.2]⟩
    have he : hQ' s = Q ⟨(s + 1) / 2, hs'⟩ := by
      rw [hQ'def]; dsimp only; exact Path.extend_apply Q hs'
    rw [he]; exact hQbox _
  have hQ'_left : (hQ' (-1)).re = -1 := by
    have h0 : ((-1 : ℝ) + 1) / 2 = 0 := by norm_num
    have he : hQ' (-1) = Q.extend 0 := by rw [hQ'def]; dsimp only; rw [h0]
    rw [he, Path.extend_zero]; norm_num
  have hQ'_right : (hQ' 1).re = 1 := by
    have h1 : ((1 : ℝ) + 1) / 2 = 1 := by norm_num
    have he : hQ' 1 = Q.extend 1 := by rw [hQ'def]; dsimp only; rw [h1]
    rw [he, Path.extend_one]; norm_num
  have hP'_bot : (hP' (-1)).im = -2 := by
    have h0 : ((-1 : ℝ) + 1) / 2 = 0 := by norm_num
    have he : hP' (-1) = P.extend 0 := by rw [hP'def]; dsimp only; rw [h0]
    rw [he, Path.extend_zero]; exact ptBot_im
  have hP'_top : (hP' 1).im = 2 := by
    have h1 : ((1 : ℝ) + 1) / 2 = 1 := by norm_num
    have he : hP' 1 = P.extend 1 := by rw [hP'def]; dsimp only; rw [h1]
    rw [he, Path.extend_one]; exact ptTop_im
  obtain ⟨s, hs, t, ht, heq⟩ := crossing_rect hQ'cont hP'cont hQ'box hP'box
    hQ'_left hQ'_right hP'_bot hP'_top
  -- the crossing point
  have hs' : (s + 1) / 2 ∈ Set.Icc (0 : ℝ) 1 := ⟨by linarith [hs.1], by linarith [hs.2]⟩
  have ht' : (t + 1) / 2 ∈ Set.Icc (0 : ℝ) 1 := ⟨by linarith [ht.1], by linarith [ht.2]⟩
  set k₀ : ℂ := Q ⟨(s + 1) / 2, hs'⟩ with hk₀
  have hk₀_J₂ : k₀ ∈ J₂ := hQJ₂ _
  have heqP : k₀ = P ⟨(t + 1) / 2, ht'⟩ := by
    have h1 : hQ' s = Q ⟨(s + 1) / 2, hs'⟩ := by
      rw [hQ'def]; dsimp only; exact Path.extend_apply Q hs'
    have h2 : hP' t = P ⟨(t + 1) / 2, ht'⟩ := by
      rw [hP'def]; dsimp only; exact Path.extend_apply P ht'
    rw [hk₀, ← h1, heq, h2]
  have hk₀_rangeP : k₀ ∈ Set.range (P : unitInterval → ℂ) := ⟨_, heqP.symm⟩
  have hP_range : Set.range (P : unitInterval → ℂ) ⊆
      Set.range (Path.segment ptBot m : unitInterval → ℂ) ∪
        (Set.range (arc₁ : unitInterval → ℂ) ∪ Set.range (Path.segment l ptTop : unitInterval → ℂ)) := by
    intro z hz
    rw [hP] at hz
    rcases range_trans_subset _ _ hz with h | h
    · rcases range_trans_subset _ _ h with h' | h'
      · exact Or.inl h'
      · exact Or.inr (Or.inl h')
    · exact Or.inr (Or.inr h)
  have hk₀_not_arc : k₀ ∉ Set.range (arc₁ : unitInterval → ℂ) := by
    rintro ⟨u, hu⟩
    have h1 : k₀ ∈ J₁ := by rw [← hu]; exact harc₁_sub u
    have h2 : k₀ ∈ ({-1,1} : Set ℂ) := hJ₁J₂_inter ⟨h1, hk₀_J₂⟩
    have h3 := harc₁_ne u
    rw [← hu] at h2
    rcases h2 with h | h
    · exact h3.1 h
    · exact h3.2 h
  have hk₀_not_top : k₀ ∉ Set.range (Path.segment l ptTop : unitInterval → ℂ) := by
    rintro ⟨u, hu⟩
    have hre : k₀.re = 0 := by
      rw [← hu]; exact segment_re_zero l ptTop hlSeg.1 ptTop_re u
    have him : k₀.im ≤ 2 := by
      rw [← hu]
      have := (segment_im_between (a := l) (b := ptTop) (by rw [ptTop_im]; exact hlSeg.2.2) u).2
      simpa [ptTop_im] using this
    have hge : l.im ≤ k₀.im := by
      rw [← hu]
      have := (segment_im_between (a := l) (b := ptTop) (by rw [ptTop_im]; exact hlSeg.2.2) u).1
      simpa using this
    have hk₀_J : k₀ ∈ Set.range γ := hJ₂_sub hk₀_J₂
    have hk₀_seg : k₀ ∈ vSeg := ⟨hre, by linarith [hlSeg.2.1], him⟩
    have hle : k₀.im ≤ l.im := hlmax ⟨hk₀_J, hk₀_seg⟩
    have him_eq : k₀.im = l.im := le_antisymm hle hge
    have hlk : k₀ = l := Complex.ext (by rw [hre, hlSeg.1]) him_eq
    have : l ∈ J₂ := by rw [← hlk]; exact hk₀_J₂
    have h2 : l ∈ ({-1,1} : Set ℂ) := hJ₁J₂_inter ⟨hlJ₁, this⟩
    rcases h2 with h | h
    · exact hl_ne.1 h
    · exact hl_ne.2 h
  have hk₀_below : k₀.im ≤ m.im := by
    have hmem := hP_range hk₀_rangeP
    rcases hmem with h | h
    · -- k₀ is on the bottom segment
      rw [Set.mem_range] at h
      obtain ⟨u, hu⟩ := h
      have := (segment_im_between (a := ptBot) (b := m) (by rw [ptBot_im]; exact hmSeg.2.1) u).2
      rw [hu] at this; exact this
    · rcases h with h | h
      · exact absurd h hk₀_not_arc
      · exact absurd h hk₀_not_top
  -- the set `K' = J₂ ∩ vSeg ∩ {im ≤ m.im}`
  have hk₀_seg : k₀ ∈ vSeg := by
    have hmem := hP_range hk₀_rangeP
    rcases hmem with h | h
    · rw [Set.mem_range] at h; obtain ⟨u, hu⟩ := h
      rw [← hu]; exact segment_mem_vSeg ptBot_mem_vSeg hmSeg u
    · rcases h with h | h
      · exact absurd h hk₀_not_arc
      · rw [Set.mem_range] at h; obtain ⟨u, hu⟩ := h
        rw [← hu]; exact segment_mem_vSeg hlSeg ptTop_mem_vSeg u
  have hJ₂compact : IsCompact J₂ := by rw [hJ₂]; exact isCompact_Icc.image hcont
  have hK₂compact : IsCompact (J₂ ∩ vSeg) := hJ₂compact.inter_right isClosed_vSeg
  set K : Set ℂ := (J₂ ∩ vSeg) ∩ {z : ℂ | z.im ≤ m.im} with hK
  have hKne : K.Nonempty := ⟨k₀, ⟨⟨hk₀_J₂, hk₀_seg⟩, hk₀_below⟩⟩
  have hKcompact : IsCompact K := hK₂compact.inter_right
    (isClosed_le Complex.continuous_im continuous_const)
  obtain ⟨k, hkK, hkmax⟩ := hKcompact.exists_isMaxOn hKne Complex.continuous_im.continuousOn
  obtain ⟨j, hjK, hjmin⟩ := hKcompact.exists_isMinOn hKne Complex.continuous_im.continuousOn
  have hkJ₂ : k ∈ J₂ := hkK.1.1
  have hkSeg : k ∈ vSeg := hkK.1.2
  have hkim : k.im ≤ m.im := hkK.2
  have hjJ₂ : j ∈ J₂ := hjK.1.1
  have hjSeg : j ∈ vSeg := hjK.1.2
  have hjm : j.im ≤ m.im := hjK.2
  have hkJ : k ∈ Set.range γ := hJ₂_sub hkJ₂
  have hjJ : j ∈ Set.range γ := hJ₂_sub hjJ₂
  have hk_ne : k ≠ -1 ∧ k ≠ 1 := by
    constructor <;> intro h
    · have hh := congrArg Complex.re h; rw [hkSeg.1] at hh; norm_num at hh
    · have hh := congrArg Complex.re h; rw [hkSeg.1] at hh; norm_num at hh
  have hkm : k.im < m.im := by
    rcases lt_or_eq_of_le hkim with h | h
    · exact h
    · exfalso
      have hkl : k = m := Complex.ext (by rw [hkSeg.1, hmSeg.1]) h
      have : m ∈ ({-1,1} : Set ℂ) := hJ₁J₂_inter ⟨hmJ₁, hkl ▸ hkJ₂⟩
      rcases this with h' | h'
      · exact hm_ne.1 h'
      · exact hm_ne.2 h'
  have hj2 : -2 < j.im := by
    have := mem_rectR_of_mem_range_re_zero hsub hjJ hjSeg.1
    exact this.2.2.1
  have hl2 : l.im < 2 := by
    have := mem_rectR_of_mem_range_re_zero hsub hlJ hlSeg.1
    exact this.2.2.2
  have hml : m.im ≤ l.im := hlmax ⟨hmJ, hmSeg⟩
  have hjk : j.im ≤ k.im := hkmax hjK
  -- freeness
  have hmkfree : ∀ z ∈ vSeg, k.im < z.im → z.im < m.im → z ∉ Set.range γ := by
    intro z hz h1 h2 hzJ
    have hz12 : z ∈ J₁ ∨ z ∈ J₂ := by
      rw [← Set.mem_union, hJ₁J₂]; exact hzJ
    rcases hz12 with hz1 | hz2
    · have hle : m.im ≤ z.im := by simpa using hmmin ⟨hz1, hz⟩
      linarith
    · have hle : z.im ≤ k.im := by simpa using hkmax ⟨⟨hz2, hz⟩, h2.le⟩
      linarith
  have hjfree : ∀ z ∈ vSeg, z.im < j.im → z ∉ Set.range γ := by
    intro z hz h1 hzJ
    have hz12 : z ∈ J₁ ∨ z ∈ J₂ := by
      rw [← Set.mem_union, hJ₁J₂]; exact hzJ
    rcases hz12 with hz1 | hz2
    · have hle : m.im ≤ z.im := by simpa using hmmin ⟨hz1, hz⟩
      linarith
    · have hle : j.im ≤ z.im := by simpa using hjmin ⟨⟨hz2, hz⟩, show z.im ≤ m.im from le_trans h1.le hjm⟩
      linarith
  have hlfree : ∀ z ∈ vSeg, l.im < z.im → z ∉ Set.range γ := by
    intro z hz h1 hzJ
    have hle : z.im ≤ l.im := by simpa using hlmax ⟨hzJ, hz⟩
    linarith
  -- the two paths of the window
  have hkJ₂' := hkJ₂
  obtain ⟨u_k, hu_k, hγu_k⟩ : ∃ u ∈ Set.Icc c₂ d₂, γ u = k := hkJ₂'
  have hjJ₂' := hjJ₂
  obtain ⟨u_j, hu_j, hγu_j⟩ : ∃ u ∈ Set.Icc c₂ d₂, γ u = j := hjJ₂'
  have hc₂d₂_lt : c₂ < d₂ := lt_of_le_of_ne hc₂_le_d₂ (by
    rcases hc₂d₂ with ⟨e1, e2⟩ | ⟨e1, e2⟩ <;> rw [e1, e2] <;> linarith [hθpos, hθlt])
  have hγc₂ne : γ c₂ ≠ γ d₂ := fun h =>
    absurd (hinj₂ ⟨le_rfl, hc₂_le_d₂⟩ ⟨hc₂_le_d₂, le_rfl⟩ h) (ne_of_lt hc₂d₂_lt)
  have hγc₂d₂ : ({-1, 1} : Set ℂ) = ({γ c₂, γ d₂} : Set ℂ) := by
    rcases hγc₂ with h1 | h1 <;> rcases hγd₂ with h2 | h2
    · exact absurd (h1.trans h2.symm) hγc₂ne
    · rw [h1, h2]
    · rw [h1, h2]; ext w; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto
    · exact absurd (h1.trans h2.symm) hγc₂ne
  have havoid₂ : ∀ u ∈ Set.Ioo c₂ d₂, γ u ≠ -1 ∧ γ u ≠ 1 := by
    intro u hu
    have huIcc : u ∈ Set.Icc c₂ d₂ := ⟨hu.1.le, hu.2.le⟩
    have hne_c : γ u ≠ γ c₂ := fun h =>
      absurd (hinj₂ huIcc ⟨le_rfl, hc₂_le_d₂⟩ h) (ne_of_gt hu.1)
    have hne_d : γ u ≠ γ d₂ := fun h =>
      absurd (hinj₂ huIcc ⟨hc₂_le_d₂, le_rfl⟩ h) (ne_of_lt hu.2)
    constructor <;> intro hcon
    · have hmem : γ u ∈ ({-1, 1} : Set ℂ) := by rw [hcon]; left; rfl
      rw [hγc₂d₂] at hmem
      rcases hmem with h | h
      · exact hne_c h
      · exact hne_d h
    · have hmem : γ u ∈ ({-1, 1} : Set ℂ) := by rw [hcon]; right; rfl
      rw [hγc₂d₂] at hmem
      rcases hmem with h | h
      · exact hne_c h
      · exact hne_d h
  have hu_k_int : u_k ∈ Set.Ioo c₂ d₂ := by
    refine ⟨lt_of_le_of_ne hu_k.1 ?_, lt_of_le_of_ne hu_k.2 ?_⟩
    · intro h; rw [← h] at hγu_k
      rcases hγc₂ with hc | hc
      · exact hk_ne.1 (hγu_k.symm.trans hc)
      · exact hk_ne.2 (hγu_k.symm.trans hc)
    · intro h; rw [h] at hγu_k
      rcases hγd₂ with hc | hc
      · exact hk_ne.1 (hγu_k.symm.trans hc)
      · exact hk_ne.2 (hγu_k.symm.trans hc)
  have hu_j_int : u_j ∈ Set.Ioo c₂ d₂ := by
    refine ⟨lt_of_le_of_ne hu_j.1 ?_, lt_of_le_of_ne hu_j.2 ?_⟩
    · intro h; rw [← h] at hγu_j
      have hj_ne : j ≠ -1 ∧ j ≠ 1 := by
        constructor <;> intro hh
        · have hhh := congrArg Complex.re hh; rw [hjSeg.1] at hhh; norm_num at hhh
        · have hhh := congrArg Complex.re hh; rw [hjSeg.1] at hhh; norm_num at hhh
      rcases hγc₂ with hc | hc
      · exact hj_ne.1 (hγu_j.symm.trans hc)
      · exact hj_ne.2 (hγu_j.symm.trans hc)
    · intro h; rw [h] at hγu_j
      have hj_ne : j ≠ -1 ∧ j ≠ 1 := by
        constructor <;> intro hh
        · have hhh := congrArg Complex.re hh; rw [hjSeg.1] at hhh; norm_num at hhh
        · have hhh := congrArg Complex.re hh; rw [hjSeg.1] at hhh; norm_num at hhh
      rcases hγd₂ with hc | hc
      · exact hj_ne.1 (hγu_j.symm.trans hc)
      · exact hj_ne.2 (hγu_j.symm.trans hc)
  let δ₂ : Path k j :=
    ⟨⟨fun t => γ (u_k + (t : ℝ) * (u_j - u_k)), hcont.comp (by fun_prop)⟩,
      by show γ (u_k + (↑(0 : unitInterval)) * (u_j - u_k)) = k
         rw [show ((0 : unitInterval) : ℝ) = 0 from rfl, zero_mul, add_zero]; exact hγu_k,
      by show γ (u_k + (↑(1 : unitInterval)) * (u_j - u_k)) = j
         rw [show ((1 : unitInterval) : ℝ) = 1 from rfl, one_mul,
           show u_k + (u_j - u_k) = u_j from by ring]; exact hγu_j⟩
  have hδ₂_int : ∀ t : unitInterval, u_k + (t : ℝ) * (u_j - u_k) ∈ Set.Ioo c₂ d₂ := by
    intro t
    rcases le_or_gt u_k u_j with h | h
    · refine ⟨?_, ?_⟩ <;> nlinarith [hu_k_int.1, hu_j_int.1, hu_k_int.2, hu_j_int.2, h, t.2.1, t.2.2]
    · refine ⟨?_, ?_⟩ <;> nlinarith [hu_k_int.1, hu_j_int.1, hu_k_int.2, hu_j_int.2, h, t.2.1, t.2.2]
  have hδ₂J : ∀ t, δ₂ t ∈ Set.range γ := by
    intro t
    rw [hJ₂] at hkJ₂
    exact hJ₂_sub (by rw [hJ₂]; exact ⟨_, ⟨(hδ₂_int t).1.le, (hδ₂_int t).2.le⟩, rfl⟩)
  have hδ₂av : ∀ t, δ₂ t ≠ -1 ∧ δ₂ t ≠ 1 := fun t => havoid₂ _ (hδ₂_int t)
  have hδ₁J : ∀ t, arc₁ t ∈ Set.range γ := fun t => hJ₁_sub (harc₁_sub t)
  exact ⟨l, m, k, j, arc₁, δ₂, hlJ, hmJ, hkJ, hjJ, hlSeg, hmSeg, hkSeg, hjSeg,
    hj2, hjk, hkm, hml, hl2, hmkfree, hjfree, hlfree, hδ₁J, harc₁_ne, hδ₂J, hδ₂av⟩

/-- **The normalised "at most two components" statement (Maehara's argument).** -/
theorem atMostTwoNormalized {γ : ℝ → ℂ} (hcont : Continuous γ)
    (hper : Function.Periodic γ (2 * Real.pi)) (hinj : Set.InjOn γ (Set.Ico 0 (2 * Real.pi)))
    (hzero : γ 0 = -1) (hpos : 1 ∈ Set.range γ)
    (hsub : ∀ w ∈ Set.range γ, w ∈ Work.Topology.PlaneCurve.rectR ∨ w = -1 ∨ w = 1) :
    ∀ x y z : ℂ, x ∉ Set.range γ → y ∉ Set.range γ → z ∉ Set.range γ →
      connectedComponentIn (Set.range γ)ᶜ x = connectedComponentIn (Set.range γ)ᶜ y ∨
      connectedComponentIn (Set.range γ)ᶜ x = connectedComponentIn (Set.range γ)ᶜ z ∨
      connectedComponentIn (Set.range γ)ᶜ y = connectedComponentIn (Set.range γ)ᶜ z := by
  intro x y z hx hy hz
  have hJc : IsClosed (Set.range γ) := (isCompact_range_of_periodic hcont hper).isClosed
  have hJbox : Set.range γ ⊆ closedBox := range_subset_closedBox hsub
  have hcl : ∀ w : ℂ, w ∉ Set.range γ →
      (-1 : ℂ) ∈ closure (connectedComponentIn (Set.range γ)ᶜ w) ∧
      (1 : ℂ) ∈ closure (connectedComponentIn (Set.range γ)ᶜ w) := by
    intro w hw
    exact ⟨memClosureConnectedComponentIn hcont hper hinj hw ⟨0, hzero⟩,
           memClosureConnectedComponentIn hcont hper hinj hw hpos⟩
  obtain ⟨l, m, k, j, δ₁, δ₂, hrest⟩ := exists_windowConfig hcont hper hinj hsub hzero hpos
  obtain ⟨hlJ, hmJ, hkJ, hjJ, hlSeg, hmSeg, hkSeg, hjSeg, hj2, hjk, hkm, hml, hl2,
    hmkfree, hjfree, hlfree, hδ₁J, hδ₁av, hδ₂J, hδ₂av⟩ := hrest
  exact atMostTwo_of_windowConfig hJc hJbox hcl hlJ hmJ hkJ hjJ hlSeg hmSeg hkSeg hjSeg
    hj2 hl2 hkm hmkfree hjfree hlfree hδ₁J hδ₁av hδ₂J hδ₂av hx hy hz

end

end Work.Smooth.SphereJordan
