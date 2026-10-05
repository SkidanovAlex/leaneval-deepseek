import Mathlib
import Submission.Work.RPB1a.Caratheodory.Brouwer.MaeharaDefs

set_option autoImplicit false

/-!
# Setup for the Maehara broken line

Basic vocabulary for the proof of `Work.RPB.B1a.maehara_broken_line`:

* `V` is the vertical segment `{0} × [-2, 2]` (the segment from `(0,2)` to `(0,-2)`);
* `segPath u v` is the straight path from `u` to `v`, parametrised on `[-1,1]`;
* `subarcPath J s t` is the piece of a parametrised curve `J` between the parameters `s` and `t`,
  parametrised on `[-1,1]`;
* `glueP f g` concatenates two paths parametrised on `[-1,1]`;
* `revPath f` reverses a path;
* the `not_isBounded_*` lemmas show that a complementary component meeting a ray of the form
  `{0} × [c, ∞)` is unbounded.
-/

namespace Work.RPB.B1a.Maehara

open Set
open Work.RPB1a.Caratheodory.Brouwer

/-- The vertical segment `{0} × [-2,2]` of the plane (the segment joining `(0,2)` and `(0,-2)`). -/
def V : Set (ℝ × ℝ) := {p | p.1 = 0 ∧ -2 ≤ p.2 ∧ p.2 ≤ 2}

@[simp] theorem mem_V {p : ℝ × ℝ} : p ∈ V ↔ p.1 = 0 ∧ -2 ≤ p.2 ∧ p.2 ≤ 2 := Iff.rfl

/-- The four distinguished points of the construction. -/
abbrev ptA : ℝ × ℝ := ((-1 : ℝ), (0 : ℝ))
abbrev ptB : ℝ × ℝ := ((1 : ℝ), (0 : ℝ))
abbrev ptN : ℝ × ℝ := ((0 : ℝ), (2 : ℝ))
abbrev ptS : ℝ × ℝ := ((0 : ℝ), (-2 : ℝ))

@[simp] theorem ptA_fst : ptA.1 = -1 := rfl
@[simp] theorem ptA_snd : ptA.2 = 0 := rfl
@[simp] theorem ptB_fst : ptB.1 = 1 := rfl
@[simp] theorem ptB_snd : ptB.2 = 0 := rfl
@[simp] theorem ptN_fst : ptN.1 = 0 := rfl
@[simp] theorem ptN_snd : ptN.2 = 2 := rfl
@[simp] theorem ptS_fst : ptS.1 = 0 := rfl
@[simp] theorem ptS_snd : ptS.2 = -2 := rfl

theorem ptA_mem_rect : ptA ∈ rect := by rw [mem_rect]; norm_num
theorem ptB_mem_rect : ptB ∈ rect := by rw [mem_rect]; norm_num
theorem ptN_mem_rect : ptN ∈ rect := by rw [mem_rect]; norm_num
theorem ptS_mem_rect : ptS ∈ rect := by rw [mem_rect]; norm_num

theorem ptA_ne_ptB : ptA ≠ ptB := by intro h; have := congrArg Prod.fst h; norm_num at this

theorem V_subset_rect : V ⊆ rect := by
  intro p hp
  rw [mem_V] at hp
  rw [mem_rect]
  exact ⟨by rw [hp.1]; norm_num, by rw [hp.1]; norm_num, hp.2.1, hp.2.2⟩

theorem convex_V : Convex ℝ V := by
  rw [show V = {0} ×ˢ Set.Icc (-2:ℝ) 2 from by ext p; simp [V]]
  exact (convex_singleton (0:ℝ)).prod (convex_Icc (-2:ℝ) 2)

theorem isClosed_V : IsClosed V := by
  rw [show V = {0} ×ˢ Set.Icc (-2:ℝ) 2 from by ext p; simp [V]]
  exact isClosed_singleton.prod isClosed_Icc

/-- The straight path from `u` to `v`, parametrised on `[-1,1]` (and extended affinely outside). -/
noncomputable def segPath (u v : ℝ × ℝ) : ℝ → ℝ × ℝ :=
  fun t => (1 - (t + 1) / 2) • u + ((t + 1) / 2) • v

theorem continuous_segPath (u v : ℝ × ℝ) : Continuous (segPath u v) := by
  unfold segPath; fun_prop

@[simp] theorem segPath_neg_one (u v : ℝ × ℝ) : segPath u v (-1) = u := by
  simp [segPath]

@[simp] theorem segPath_one (u v : ℝ × ℝ) : segPath u v 1 = v := by
  simp [segPath]

theorem segPath_image (u v : ℝ × ℝ) :
    segPath u v '' Set.Icc (-1 : ℝ) 1 = segment ℝ u v := by
  rw [segment_eq_image]
  ext p
  constructor
  · rintro ⟨t, ht, rfl⟩
    refine ⟨(t + 1) / 2, ⟨by linarith [ht.1], by linarith [ht.2]⟩, ?_⟩
    simp only [segPath]
  · rintro ⟨θ, hθ, rfl⟩
    refine ⟨2 * θ - 1, ⟨by linarith [hθ.1], by linarith [hθ.2]⟩, ?_⟩
    have h2 : (2 * θ - 1 + 1) / 2 = θ := by ring
    simp only [segPath, h2]

theorem segPath_mem_rect {u v : ℝ × ℝ} (hu : u ∈ rect) (hv : v ∈ rect) (t : ℝ)
    (ht : t ∈ Set.Icc (-1 : ℝ) 1) : segPath u v t ∈ rect := by
  have h : segPath u v t ∈ segment ℝ u v := by
    rw [← segPath_image]; exact ⟨t, ht, rfl⟩
  exact rect_convex.segment_subset hu hv h

theorem fst_eq_zero_of_mem_segment {u v z : ℝ × ℝ} (hu : u.1 = 0) (hv : v.1 = 0)
    (hz : z ∈ segment ℝ u v) : z.1 = 0 := by
  rw [segment_eq_image] at hz
  obtain ⟨θ, _, rfl⟩ := hz
  simp only [Prod.fst_add, Prod.smul_fst, smul_eq_mul, hu, hv, mul_zero, add_zero]

theorem snd_mem_Icc_of_mem_segment {u v z : ℝ × ℝ} (hz : z ∈ segment ℝ u v) :
    z.2 ∈ Set.Icc (min u.2 v.2) (max u.2 v.2) := by
  rw [segment_eq_image] at hz
  obtain ⟨θ, hθ, rfl⟩ := hz
  simp only [Prod.snd_add, Prod.smul_snd, smul_eq_mul]
  rcases le_total u.2 v.2 with h | h
  · rw [min_eq_left h, max_eq_right h]; constructor <;> nlinarith [hθ.1, hθ.2]
  · rw [min_eq_right h, max_eq_left h]; constructor <;> nlinarith [hθ.1, hθ.2]

/-! ## Pieces of a parametrised curve -/

/-- The piece of the parametrised curve `J` between the parameters `s` and `t`, parametrised on
`[-1,1]`. -/
noncomputable def subarcPath (J : ℝ → ℝ × ℝ) (s t : ℝ) : ℝ → ℝ × ℝ :=
  fun u => J (s + (u + 1) / 2 * (t - s))

theorem continuous_subarcPath {J : ℝ → ℝ × ℝ} (hJ : Continuous J) (s t : ℝ) :
    Continuous (subarcPath J s t) := by
  unfold subarcPath; exact hJ.comp (by fun_prop)

@[simp] theorem subarcPath_neg_one (J : ℝ → ℝ × ℝ) (s t : ℝ) : subarcPath J s t (-1) = J s := by
  simp [subarcPath]

@[simp] theorem subarcPath_one (J : ℝ → ℝ × ℝ) (s t : ℝ) : subarcPath J s t 1 = J t := by
  simp [subarcPath]

theorem subarcPath_arg_mem_Icc {s t u : ℝ} (hs : s ∈ Set.Icc (-1:ℝ) 1)
    (ht : t ∈ Set.Icc (-1:ℝ) 1) (hu : u ∈ Set.Icc (-1:ℝ) 1) :
    s + (u + 1) / 2 * (t - s) ∈ Set.Icc (-1:ℝ) 1 := by
  have h1 : (0:ℝ) ≤ (u + 1) / 2 := by linarith [hu.1]
  have h2 : (u + 1) / 2 ≤ 1 := by linarith [hu.2]
  have h3 : s + (u + 1) / 2 * (t - s)
      = (1 - (u + 1) / 2) * s + ((u + 1) / 2) * t := by ring
  rw [h3]
  exact ⟨by nlinarith [hs.1, ht.1, h1, h2], by nlinarith [hs.2, ht.2, h1, h2]⟩

theorem subarcPath_image_subset (J : ℝ → ℝ × ℝ) {s t : ℝ}
    (hs : s ∈ Set.Icc (-1:ℝ) 1) (ht : t ∈ Set.Icc (-1:ℝ) 1) :
    subarcPath J s t '' Set.Icc (-1 : ℝ) 1 ⊆ J '' Set.Icc (-1 : ℝ) 1 := by
  rintro p ⟨u, hu, rfl⟩
  exact ⟨_, subarcPath_arg_mem_Icc hs ht hu, rfl⟩

/-! ## Concatenation of two paths -/

/-- Concatenation of two paths `f`, `g : ℝ → ℝ × ℝ` parametrised on `[-1,1]`. -/
noncomputable def glueP (f g : ℝ → ℝ × ℝ) (h : f 1 = g (-1)) : ℝ → ℝ × ℝ :=
  fun t => if t ≤ 0 then f (2 * t + 1) else g (2 * t - 1)

theorem continuous_glueP {f g : ℝ → ℝ × ℝ} (hf : Continuous f) (hg : Continuous g)
    (h : f 1 = g (-1)) : Continuous (glueP f g h) := by
  have hfront : ∀ a ∈ frontier {x : ℝ | x ≤ 0}, f (2 * a + 1) = g (2 * a - 1) := by
    intro a ha
    have ha0 : a = 0 := by
      have : frontier {x : ℝ | x ≤ 0} = {0} := by
        rw [show {x : ℝ | x ≤ 0} = Set.Iic (0:ℝ) from rfl, frontier_Iic]
      rw [this] at ha; simpa using ha
    subst ha0
    norm_num
    exact h
  refine continuous_if hfront ?_ ?_ <;>
    · refine Continuous.continuousOn ?_ <;> fun_prop

@[simp] theorem glueP_neg_one {f g : ℝ → ℝ × ℝ} (h : f 1 = g (-1)) :
    glueP f g h (-1) = f (-1) := by
  rw [glueP, if_pos (by norm_num : (-1:ℝ) ≤ 0)]; norm_num

@[simp] theorem glueP_one {f g : ℝ → ℝ × ℝ} (h : f 1 = g (-1)) : glueP f g h 1 = g 1 := by
  rw [glueP, if_neg (by norm_num : ¬ ((1:ℝ) ≤ 0))]; norm_num

theorem image_glueP {f g : ℝ → ℝ × ℝ} (h : f 1 = g (-1)) :
    glueP f g h '' Set.Icc (-1 : ℝ) 1
      = f '' Set.Icc (-1 : ℝ) 1 ∪ g '' Set.Icc (-1 : ℝ) 1 := by
  ext p
  constructor
  · rintro ⟨t, ht, rfl⟩
    by_cases hc : t ≤ 0
    · left
      refine ⟨2 * t + 1, ⟨by linarith [ht.1], by linarith [ht.2]⟩, ?_⟩
      rw [glueP, if_pos hc]
    · right
      refine ⟨2 * t - 1, ⟨by linarith [ht.1], by linarith [ht.2]⟩, ?_⟩
      rw [glueP, if_neg hc]
  · rintro (⟨s, hs, rfl⟩ | ⟨s, hs, rfl⟩)
    · refine ⟨(s - 1) / 2, ⟨by linarith [hs.1], by linarith [hs.2]⟩, ?_⟩
      rw [glueP, if_pos (by linarith [hs.2] : (s - 1) / 2 ≤ 0)]
      ring_nf
    · refine ⟨(s + 1) / 2, ⟨by linarith [hs.1], by linarith [hs.2]⟩, ?_⟩
      by_cases hc : (s + 1) / 2 ≤ 0
      · have hs1 : s = -1 := by linarith [hs.1]
        rw [glueP, if_pos hc, hs1]
        norm_num
        exact h
      · rw [glueP, if_neg hc]
        ring_nf

/-- Reversal of a path parametrised on `[-1,1]`. -/
noncomputable def revPath (f : ℝ → ℝ × ℝ) : ℝ → ℝ × ℝ := fun t => f (-t)

theorem glueP_mem {F : Set (ℝ × ℝ)} {f g : ℝ → ℝ × ℝ} (h : f 1 = g (-1))
    (hf : ∀ t, f t ∈ F) (hg : ∀ t, g t ∈ F) : ∀ t, glueP f g h t ∈ F := by
  intro t
  by_cases hc : t ≤ 0
  · rw [glueP, if_pos hc]; exact hf _
  · rw [glueP, if_neg hc]; exact hg _

theorem continuous_revPath {f : ℝ → ℝ × ℝ} (hf : Continuous f) : Continuous (revPath f) := by
  unfold revPath; fun_prop

@[simp] theorem revPath_neg_one (f : ℝ → ℝ × ℝ) : revPath f (-1) = f 1 := by simp [revPath]

@[simp] theorem revPath_one (f : ℝ → ℝ × ℝ) : revPath f 1 = f (-1) := by simp [revPath]

theorem image_revPath (f : ℝ → ℝ × ℝ) :
    revPath f '' Set.Icc (-1 : ℝ) 1 = f '' Set.Icc (-1 : ℝ) 1 := by
  ext p; constructor
  · rintro ⟨t, ht, htp⟩
    exact ⟨-t, ⟨by linarith [ht.2], by linarith [ht.1]⟩, by simpa [revPath] using htp⟩
  · rintro ⟨t, ht, htp⟩
    exact ⟨-t, ⟨by linarith [ht.2], by linarith [ht.1]⟩, by simpa [revPath] using htp⟩

/-- Clamping a path to its values at `-1` and `1`: the resulting path agrees with `f` on `[-1,1]`
and is constant (equal to `f (-1)` resp. `f 1`) outside.  This is used so that the range of the
clamped path is exactly `f '' [-1,1]`, which is what the crossing lemma needs. -/
noncomputable def clampPath (f : ℝ → ℝ × ℝ) : ℝ → ℝ × ℝ := fun t => f (max (-1) (min 1 t))

theorem continuous_clampPath {f : ℝ → ℝ × ℝ} (hf : Continuous f) : Continuous (clampPath f) := by
  change Continuous (fun t : ℝ => f (max (-1) (min 1 t)))
  exact hf.comp (by fun_prop)

@[simp] theorem clampPath_neg_one (f : ℝ → ℝ × ℝ) : clampPath f (-1) = f (-1) := by
  simp [clampPath]

@[simp] theorem clampPath_one (f : ℝ → ℝ × ℝ) : clampPath f 1 = f 1 := by
  simp [clampPath]

theorem clampPath_of_mem {f : ℝ → ℝ × ℝ} {t : ℝ} (ht : t ∈ Set.Icc (-1:ℝ) 1) :
    clampPath f t = f t := by
  show f (max (-1) (min 1 t)) = f t
  rw [min_eq_right ht.2, max_eq_right ht.1]

theorem clampPath_image (f : ℝ → ℝ × ℝ) :
    clampPath f '' Set.Icc (-1 : ℝ) 1 = f '' Set.Icc (-1 : ℝ) 1 := by
  ext p; constructor
  · rintro ⟨t, ht, htp⟩
    exact ⟨t, ht, (clampPath_of_mem ht).symm.trans htp⟩
  · rintro ⟨t, ht, htp⟩
    exact ⟨t, ht, (clampPath_of_mem ht).trans htp⟩

theorem clampPath_mem_rect {f : ℝ → ℝ × ℝ} (h : ∀ t ∈ Set.Icc (-1:ℝ) 1, f t ∈ rect) :
    ∀ t, clampPath f t ∈ rect := by
  intro t
  exact h _ ⟨le_max_left (-1) (min 1 t), max_le (by norm_num) (min_le_left 1 t)⟩

theorem clampPath_mem_image (f : ℝ → ℝ × ℝ) (t : ℝ) :
    clampPath f t ∈ f '' Set.Icc (-1 : ℝ) 1 :=
  ⟨_, ⟨le_max_left (-1) (min 1 t), max_le (by norm_num) (min_le_left 1 t)⟩, rfl⟩

/-! ## Unboundedness of complementary components meeting a vertical ray -/

/-- If all points of `S` on the vertical line `{re = 0}` lie strictly below `p`, and `p ∉ S` lies
on that line, then the component of `p` in `Sᶜ` is unbounded (it contains the ray above `p`). -/
theorem not_isBounded_component_of_below {S : Set (ℝ × ℝ)} {p : ℝ × ℝ}
    (hp : p ∉ S) (hp1 : p.1 = 0) (hS : ∀ y ∈ S, y.1 = 0 → y.2 < p.2) :
    ¬ Bornology.IsBounded (connectedComponentIn Sᶜ p) := by
  intro hb
  rw [Metric.isBounded_iff] at hb
  obtain ⟨C, hC⟩ := hb
  have hpcomp : p ∈ connectedComponentIn Sᶜ p := mem_connectedComponentIn (by simpa using hp)
  have hC0 : 0 ≤ C := by have := hC hpcomp hpcomp; simpa using this
  set q : ℝ × ℝ := (0, p.2 + (C + 1)) with hq
  have hseg : segment ℝ p q ⊆ Sᶜ := by
    intro y hy
    rw [Set.mem_compl_iff]
    intro hyS
    rw [segment_eq_image] at hy
    obtain ⟨θ, hθ, rfl⟩ := hy
    have hy1 : ((1 - θ) • p + θ • q).1 = 0 := by simp [hq, hp1]
    have hy2 : p.2 ≤ ((1 - θ) • p + θ • q).2 := by
      have : ((1 - θ) • p + θ • q).2 = (1 - θ) * p.2 + θ * (p.2 + (C + 1)) := by simp [hq]
      rw [this]; nlinarith [hθ.1, hθ.2]
    have := hS _ hyS hy1
    linarith
  have hpre : IsPreconnected (segment ℝ p q) := convex_segment p q |>.isPreconnected
  have hpseg : p ∈ segment ℝ p q := left_mem_segment ℝ p q
  have hcomp : segment ℝ p q ⊆ connectedComponentIn Sᶜ p :=
    hpre.subset_connectedComponentIn (by simpa using hpseg) hseg
  have hqmem : q ∈ connectedComponentIn Sᶜ p := hcomp (right_mem_segment ℝ p q)
  have hd := hC hpcomp hqmem
  rw [dist_eq_norm] at hd
  have hnorm : ‖p - q‖ = C + 1 := by
    have hpq : p - q = (0, -(C + 1)) := by ext <;> simp [hq, hp1]
    rw [hpq, Prod.norm_mk, norm_zero, norm_neg, Real.norm_eq_abs,
      max_eq_right (abs_nonneg _), abs_of_nonneg (by linarith)]
  rw [hnorm] at hd
  linarith

/-- If all points of `S` on the vertical line `{re = 0}` lie strictly above `p` and `p ∉ S` lies on
that line, then the component of `p` in `Sᶜ` is unbounded (it contains the ray below `p`). -/
theorem not_isBounded_component_of_above {S : Set (ℝ × ℝ)} {p : ℝ × ℝ}
    (hp : p ∉ S) (hp1 : p.1 = 0) (hS : ∀ y ∈ S, y.1 = 0 → p.2 < y.2) :
    ¬ Bornology.IsBounded (connectedComponentIn Sᶜ p) := by
  intro hb
  rw [Metric.isBounded_iff] at hb
  obtain ⟨C, hC⟩ := hb
  have hpcomp : p ∈ connectedComponentIn Sᶜ p := mem_connectedComponentIn (by simpa using hp)
  have hC0 : 0 ≤ C := by have := hC hpcomp hpcomp; simpa using this
  set q : ℝ × ℝ := (0, p.2 - (C + 1)) with hq
  have hseg : segment ℝ p q ⊆ Sᶜ := by
    intro y hy
    rw [Set.mem_compl_iff]
    intro hyS
    rw [segment_eq_image] at hy
    obtain ⟨θ, hθ, rfl⟩ := hy
    have hy1 : ((1 - θ) • p + θ • q).1 = 0 := by simp [hq, hp1]
    have hy2 : ((1 - θ) • p + θ • q).2 ≤ p.2 := by
      have : ((1 - θ) • p + θ • q).2 = (1 - θ) * p.2 + θ * (p.2 - (C + 1)) := by simp [hq]
      rw [this]; nlinarith [hθ.1, hθ.2]
    have := hS _ hyS hy1
    linarith
  have hpre : IsPreconnected (segment ℝ p q) := convex_segment p q |>.isPreconnected
  have hpseg : p ∈ segment ℝ p q := left_mem_segment ℝ p q
  have hcomp : segment ℝ p q ⊆ connectedComponentIn Sᶜ p :=
    hpre.subset_connectedComponentIn (by simpa using hpseg) hseg
  have hqmem : q ∈ connectedComponentIn Sᶜ p := hcomp (right_mem_segment ℝ p q)
  have hd := hC hpcomp hqmem
  rw [dist_eq_norm] at hd
  have hnorm : ‖p - q‖ = C + 1 := by
    have hpq : p - q = (0, C + 1) := by ext <;> simp [hq, hp1]
    rw [hpq, Prod.norm_mk, norm_zero, Real.norm_eq_abs, max_eq_right (abs_nonneg _),
      abs_of_nonneg (by linarith)]
  rw [hnorm] at hd
  linarith

end Work.RPB.B1a.Maehara
