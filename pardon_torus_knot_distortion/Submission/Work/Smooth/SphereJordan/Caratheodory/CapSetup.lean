import Mathlib
import Submission.Work.Smooth.SphereJordan.crosscutComponents
import Submission.Work.Smooth.SphereJordan.Caratheodory.CapEndpoints

/-!
# The crosscut of `𝔻` at the boundary point `1` and its two sides

For `0 < s < 2` the circular arc `{|z - 1| = s} ∩ 𝔻`, parametrised by `τ ↦ capPt s τ`
(`τ ∈ (-α, α)`, `α = arccos (s/2)`), is a **crosscut** of the unit disc: its endpoints lie on the
unit circle and its interior lies in `𝔻`.  The two sides are

* the *lens* `lens s = 𝔻 ∩ ball 1 s` (a convex set containing points close to `1`), and
* the *outside* `𝔻 ∖ (lens s ∪ arc)`.

This is the geometric input of the Garnett–Marshall uniform-continuity argument: the image of the
lens under the Riemann map is enclosed by the image of the crosscut together with a short arc of
the boundary.
-/

noncomputable section
open Set Metric Filter
open scoped Topology

namespace Work.Smooth.SphereJordan.Caratheodory

/-- The crosscut of `𝔻` consisting of the arc `{|z - 1| = s} ∩ 𝔻`, parametrised monotonically. -/
def capArcPath (s : ℝ) : C(Set.Icc (0 : ℝ) 1, ℂ) :=
  ⟨fun t => capPt s (-(capAlpha s) + (t : ℝ) * (2 * capAlpha s)),
    (continuous_capPt s).comp (by fun_prop)⟩

theorem capArcPath_apply (s : ℝ) (t : Set.Icc (0 : ℝ) 1) :
    capArcPath s t = capPt s (-(capAlpha s) + (t : ℝ) * (2 * capAlpha s)) := rfl

theorem capArcPath_zero (s : ℝ) : capArcPath s ⟨0, by norm_num⟩ = capPt s (-(capAlpha s)) := by
  simp [capArcPath]

theorem capArcPath_one (s : ℝ) : capArcPath s ⟨1, by norm_num⟩ = capPt s (capAlpha s) := by
  simp only [capArcPath, ContinuousMap.coe_mk]
  congr 1
  ring

/-- The parametrisation is monotone, hence injective. -/
theorem capArcPath_injective {s : ℝ} (hs : 0 < s) (hs2 : s < 2) :
    Function.Injective (capArcPath s) := by
  intro a b hab
  have hα : 0 < capAlpha s := capAlpha_pos hs2
  have hπ : capAlpha s < Real.pi := capAlpha_lt_pi hs
  have ha : -(capAlpha s) + (a : ℝ) * (2 * capAlpha s) ∈ Set.Ioo (-Real.pi) Real.pi := by
    rw [Set.mem_Ioo]
    constructor <;> nlinarith [a.2.1, a.2.2, hα, hπ]
  have hb : -(capAlpha s) + (b : ℝ) * (2 * capAlpha s) ∈ Set.Ioo (-Real.pi) Real.pi := by
    rw [Set.mem_Ioo]
    constructor <;> nlinarith [b.2.1, b.2.2, hα, hπ]
  have h := capPt_injOn hs ha hb (by simpa only [capArcPath, ContinuousMap.coe_mk] using hab)
  have hmul : (a : ℝ) * (2 * capAlpha s) = (b : ℝ) * (2 * capAlpha s) := by linarith
  have hne : (2 * capAlpha s) ≠ 0 := by linarith
  exact Subtype.ext (mul_right_cancel₀ hne hmul)

/-- The arc evaluated at an interior parameter is a point of `𝔻`. -/
theorem capArcPath_mem_ball {s : ℝ} (hs : 0 < s) (hs2 : s < 2) (t : Set.Icc (0 : ℝ) 1)
    (ht : (t : ℝ) ∈ Set.Ioo 0 1) : capArcPath s t ∈ Metric.ball (0 : ℂ) 1 := by
  rw [capArcPath_apply]
  refine capPt_mem_ball_of_mem_Ioo hs hs2 ?_
  rw [Set.mem_Ioo] at ht ⊢
  have hα : 0 < capAlpha s := capAlpha_pos hs2
  constructor <;> nlinarith [ht.1, ht.2]

/-- The two endpoints of the arc lie on the unit circle. -/
theorem capArcPath_mem_sphere {s : ℝ} (hs : 0 < s) (hs2 : s < 2)
    (t : Set.Icc (0 : ℝ) 1) (ht : (t : ℝ) = 0 ∨ (t : ℝ) = 1) :
    capArcPath s t ∈ Metric.sphere (0 : ℂ) 1 := by
  have hcos : Real.cos (-(capAlpha s) + (t : ℝ) * (2 * capAlpha s)) = s / 2 := by
    rcases ht with ht | ht
    · rw [ht, zero_mul, add_zero, Real.cos_neg, cos_capAlpha hs hs2]
    · rw [ht, one_mul, show -(capAlpha s) + 2 * capAlpha s = capAlpha s by ring,
        cos_capAlpha hs hs2]
  rw [Metric.mem_sphere]
  show dist (capPt s (-(capAlpha s) + (t : ℝ) * (2 * capAlpha s))) (0 : ℂ) = 1
  rw [dist_eq_norm, sub_zero]
  have hsq := sq_norm_capPt s (-(capAlpha s) + (t : ℝ) * (2 * capAlpha s))
  rw [hcos] at hsq
  have h2 : ‖capPt s (-(capAlpha s) + (t : ℝ) * (2 * capAlpha s))‖ ^ 2 = 1 := by
    rw [hsq]; ring
  nlinarith [norm_nonneg (capPt s (-(capAlpha s) + (t : ℝ) * (2 * capAlpha s)))]

/-- The **lens** cut off by the crosscut: `𝔻 ∩ ball 1 s`. -/
def lens (s : ℝ) : Set ℂ := Metric.ball (0 : ℂ) 1 ∩ Metric.ball (1 : ℂ) s

theorem mem_lens_iff {s : ℝ} {z : ℂ} : z ∈ lens s ↔ ‖z‖ < 1 ∧ ‖z - 1‖ < s := by
  rw [lens, Set.mem_inter_iff, Metric.mem_ball, Metric.mem_ball, dist_zero_right, dist_eq_norm]

theorem lens_isOpen (s : ℝ) : IsOpen (lens s) :=
  Metric.isOpen_ball.inter Metric.isOpen_ball

theorem lens_convex (s : ℝ) : Convex ℝ (lens s) :=
  (convex_ball (0 : ℂ) 1).inter (convex_ball (1 : ℂ) s)

theorem lens_subset_ball (s : ℝ) : lens s ⊆ Metric.ball (0 : ℂ) 1 := fun z hz => hz.1

theorem zero_notMem_lens {s : ℝ} (hs : s < 1) : (0 : ℂ) ∉ lens s := by
  rw [mem_lens_iff]
  rintro ⟨h1, h2⟩
  rw [zero_sub, norm_neg, norm_one] at h2
  linarith

/-- The arc stays in the closed unit disc. -/
theorem norm_capArcPath_le {s : ℝ} (hs : 0 < s) (hs2 : s < 2) (t : Set.Icc (0 : ℝ) 1) :
    ‖capArcPath s t‖ ≤ 1 := by
  rcases eq_or_lt_of_le t.2.1 with h0 | h0
  · have ht : (t : ℝ) = 0 := h0.symm
    have h := capArcPath_mem_sphere hs hs2 t (Or.inl ht)
    rw [Metric.mem_sphere, dist_eq_norm, sub_zero] at h
    exact h.le
  · rcases eq_or_lt_of_le t.2.2 with h1 | h1
    · have ht : (t : ℝ) = 1 := h1
      have h := capArcPath_mem_sphere hs hs2 t (Or.inr ht)
      rw [Metric.mem_sphere, dist_eq_norm, sub_zero] at h
      exact h.le
    · have h := capArcPath_mem_ball hs hs2 t ⟨h0, h1⟩
      rw [Metric.mem_ball, dist_zero_right] at h
      exact h.le

theorem capArcPath_subset_closedBall {s : ℝ} (hs : 0 < s) (hs2 : s < 2) :
    Set.range (capArcPath s) ⊆ Metric.closedBall (0 : ℂ) 1 := fun z hz => by
  obtain ⟨t, rfl⟩ := hz
  rw [Metric.mem_closedBall, dist_zero_right]
  exact norm_capArcPath_le hs hs2 t

/-- No point of the arc lies in the lens. -/
theorem lens_disjoint_arc {s : ℝ} (hs : 0 < s) :
    Disjoint (lens s) (Set.range (capArcPath s)) := by
  rw [Set.disjoint_left]
  intro z hz hzarc
  rw [mem_lens_iff] at hz
  obtain ⟨t, rfl⟩ := hzarc
  rw [capArcPath_apply, norm_capPt_sub_one, abs_of_pos hs] at hz
  exact absurd hz.2 (lt_irrefl s)

theorem lens_subset_compl_arc {s : ℝ} (hs : 0 < s) :
    lens s ⊆ Metric.ball (0 : ℂ) 1 \ Set.range (capArcPath s) := by
  intro z hz
  exact ⟨lens_subset_ball s hz, fun hcon => (Set.disjoint_left.mp (lens_disjoint_arc hs)) hz hcon⟩


/-- **The circle of radius `s` about `1` meets the open unit disc exactly in the cap arc.** -/
theorem sphere_inter_ball {s : ℝ} (hs : 0 < s) (hs2 : s < 2) :
    {z : ℂ | ‖z - 1‖ = s} ∩ Metric.ball (0 : ℂ) 1 =
      capPt s '' Set.Ioo (-(capAlpha s)) (capAlpha s) := by
  have hα : 0 < capAlpha s := capAlpha_pos hs2
  have hαπ : capAlpha s < Real.pi := capAlpha_lt_pi hs
  have hcos : Real.cos (capAlpha s) = s / 2 := cos_capAlpha hs hs2
  have hsne : (s : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hs
  ext z
  constructor
  · intro hz
    have hz1 : ‖z - 1‖ = s := hz.1
    have hz2 : z ∈ Metric.ball (0 : ℂ) 1 := hz.2
    set u : ℂ := (1 - z) / (s : ℂ) with hu
    have hunorm : ‖u‖ = 1 := by
      rw [hu, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hs, norm_sub_rev, hz1,
        div_self (ne_of_gt hs)]
    have huarg : u = Complex.exp ((Complex.arg u : ℂ) * Complex.I) := by
      have h := Complex.norm_mul_exp_arg_mul_I u
      rw [hunorm] at h
      simpa using h.symm
    have hz_eq : capPt s (Complex.arg u) = z := by
      have h1 : (s : ℂ) * u = 1 - z := by rw [hu]; field_simp
      rw [capPt, ← huarg, h1]
      ring
    have hcosarg : s / 2 < Real.cos (Complex.arg u) := by
      have h := capPt_mem_ball_iff hs hs2 (Complex.arg u)
      rw [hz_eq] at h
      exact h.mp hz2
    have hargpi : Complex.arg u < Real.pi := by
      rcases lt_or_eq_of_le (Complex.arg_le_pi u) with h | h
      · exact h
      · exfalso
        have hc : Real.cos (Complex.arg u) = -1 := by rw [h]; exact Real.cos_pi
        rw [hc] at hcosarg
        linarith
    have hcu : Real.cos (capAlpha s) < Real.cos |Complex.arg u| := by
      rw [hcos]
      rcases lt_or_ge (Complex.arg u) 0 with h0 | h0
      · rw [abs_of_neg h0, Real.cos_neg]; exact hcosarg
      · rw [abs_of_nonneg h0]; exact hcosarg
    have habs_le : |Complex.arg u| ≤ Real.pi := by
      rw [abs_le]
      exact ⟨le_of_lt (Complex.neg_pi_lt_arg u), le_of_lt hargpi⟩
    have harglt : |Complex.arg u| < capAlpha s := by
      by_contra hcon
      rw [not_lt] at hcon
      have hlt : capAlpha s < |Complex.arg u| := lt_of_le_of_ne hcon (fun heq => by
        rw [heq] at hcu
        exact absurd hcu (lt_irrefl _))
      exact absurd (Real.cos_lt_cos_of_nonneg_of_le_pi hα.le habs_le hlt)
        (not_lt.mpr hcu.le)
    refine ⟨Complex.arg u, ?_, hz_eq⟩
    exact Set.mem_Ioo.mpr (abs_lt.mp harglt)
  · rintro ⟨θ, hθ, rfl⟩
    refine ⟨?_, capPt_mem_ball_of_mem_Ioo hs hs2 hθ⟩
    show ‖capPt s θ - 1‖ = s
    rw [norm_capPt_sub_one, abs_of_pos hs]

/-- The part of `𝔻` outside the lens. -/
def outerLens (s : ℝ) : Set ℂ := Metric.ball (0 : ℂ) 1 ∩ {z : ℂ | s < ‖z - 1‖}

theorem outerLens_isOpen (s : ℝ) : IsOpen (outerLens s) :=
  Metric.isOpen_ball.inter (isOpen_lt continuous_const (by fun_prop))

/-- Points of the arc are exactly the points of `𝔻` at distance `s` from `1`, so they are never in
the lens nor in `outerLens`. -/
theorem capPt_image_subset_range {s : ℝ} (hs2 : s < 2) :
    capPt s '' Set.Ioo (-(capAlpha s)) (capAlpha s) ⊆ Set.range (capArcPath s) := by
  rintro z ⟨θ, hθ, rfl⟩
  have hα : 0 < capAlpha s := capAlpha_pos hs2
  refine ⟨⟨(θ + capAlpha s) / (2 * capAlpha s), ?_⟩, ?_⟩
  · rw [Set.mem_Icc]
    constructor
    · apply div_nonneg <;> linarith [hθ.1]
    · rw [div_le_one (by linarith)]
      linarith [hθ.2]
  · rw [capArcPath_apply]
    congr 1
    field_simp
    ring

theorem lens_union_outerLens {s : ℝ} (hs : 0 < s) (hs2 : s < 2) :
    lens s ∪ outerLens s = Metric.ball (0 : ℂ) 1 \ Set.range (capArcPath s) := by
  refine Set.Subset.antisymm ?_ ?_
  · rintro z (hz | hz)
    · exact lens_subset_compl_arc hs hz
    · refine ⟨hz.1, fun hcon => ?_⟩
      obtain ⟨t, rfl⟩ := hcon
      have h2 : s < ‖(capArcPath s) t - 1‖ := hz.2
      rw [capArcPath_apply, norm_capPt_sub_one, abs_of_pos hs] at h2
      exact absurd h2 (lt_irrefl s)
  · intro z hz
    have hz1 : z ∈ Metric.ball (0 : ℂ) 1 := hz.1
    have hzn : z ∉ Set.range (capArcPath s) := hz.2
    rcases lt_trichotomy ‖z - 1‖ s with h | h | h
    · refine Or.inl ((mem_lens_iff).mpr ⟨?_, h⟩)
      rwa [Metric.mem_ball, dist_zero_right] at hz1
    · exfalso
      have hmem : z ∈ {w : ℂ | ‖w - 1‖ = s} ∩ Metric.ball (0 : ℂ) 1 := ⟨h, hz1⟩
      rw [sphere_inter_ball hs hs2] at hmem
      exact hzn (capPt_image_subset_range (s := s) hs2 hmem)
    · exact Or.inr ⟨hz1, h⟩

theorem disjoint_lens_outerLens {s : ℝ} : Disjoint (lens s) (outerLens s) := by
  rw [Set.disjoint_left]
  intro z hz hz'
  rw [mem_lens_iff] at hz
  exact absurd hz.2 (not_lt.mpr hz'.2.le)

theorem lens_nonempty {s : ℝ} (hs : 0 < s) (hs2 : s < 2) : (lens s).Nonempty := by
  refine ⟨((1 - s / 2 : ℝ) : ℂ), ?_⟩
  rw [mem_lens_iff]
  have hsub : ((1 - s / 2 : ℝ) : ℂ) - 1 = ((-(s / 2) : ℝ) : ℂ) := by push_cast; ring
  constructor
  · rw [Complex.norm_real, Real.norm_eq_abs]
    rw [abs_lt]
    constructor <;> linarith
  · rw [hsub, Complex.norm_real, Real.norm_eq_abs, abs_of_neg (by linarith : -(s / 2) < 0),
      neg_neg]
    linarith

theorem outerLens_nonempty {s : ℝ} (hs : 0 < s) (hs2 : s < 2) : (outerLens s).Nonempty := by
  refine ⟨(-(s / 2) : ℝ), ?_, ?_⟩
  · rw [Metric.mem_ball, dist_zero_right, Complex.norm_real, Real.norm_eq_abs,
      abs_of_neg (by linarith : -(s / 2) < 0)]
    linarith
  · show s < ‖((-(s / 2) : ℝ) : ℂ) - 1‖
    have hsub : ((-(s / 2) : ℝ) : ℂ) - 1 = ((-(1 + s / 2) : ℝ) : ℂ) := by push_cast; ring
    rw [hsub, Complex.norm_real, Real.norm_eq_abs,
      abs_of_neg (by linarith : -(1 + s / 2) < 0)]
    linarith

/-- **The lens is one of the two components cut out by the crosscut.** -/
theorem lens_eq_component {s : ℝ} (hs : 0 < s) (hs2 : s < 2) :
    ∃ P Q : Set ℂ, P.Nonempty ∧ Q.Nonempty ∧ IsOpen P ∧ IsOpen Q ∧
      IsPreconnected P ∧ IsPreconnected Q ∧
      Metric.ball (0 : ℂ) 1 \ Set.range (capArcPath s) = P ∪ Q ∧ Disjoint P Q ∧
      (lens s = P ∨ lens s = Q) := by
  obtain ⟨P, Q, hPne, hQne, hPopen, hQopen, hPpre, hQpre, hunion, hdisj⟩ :=
    crosscutComponents (c := (0 : ℂ)) (ρ := 1) one_pos
      (capArcPath_injective hs hs2) (capArcPath_subset_closedBall hs hs2)
      (capArcPath_mem_sphere hs hs2 ⟨0, by norm_num⟩ (Or.inl rfl))
      (capArcPath_mem_sphere hs hs2 ⟨1, by norm_num⟩ (Or.inr rfl))
      (fun hcon => by
        have h := capArcPath_injective hs hs2 hcon
        exact absurd (Subtype.ext_iff.mp h) (by norm_num))
      (fun t ht => capArcPath_mem_ball hs hs2 t ht)
  have hcompl := lens_union_outerLens hs hs2
  have hmem_iff : ∀ {z : ℂ}, z ∈ Metric.ball (0 : ℂ) 1 \ Set.range (capArcPath s) ↔
      z ∈ P ∪ Q := fun {z} => by rw [hunion]
  have hP : P ⊆ lens s ∨ P ⊆ outerLens s :=
    hPpre.subset_or_subset (lens_isOpen s) (outerLens_isOpen s) disjoint_lens_outerLens
      (fun z hz => by rw [hcompl, hunion]; exact Or.inl hz)
  have hQ : Q ⊆ lens s ∨ Q ⊆ outerLens s :=
    hQpre.subset_or_subset (lens_isOpen s) (outerLens_isOpen s) disjoint_lens_outerLens
      (fun z hz => by rw [hcompl, hunion]; exact Or.inr hz)
  have hneL : (lens s).Nonempty := lens_nonempty hs hs2
  have hneO : (outerLens s).Nonempty := outerLens_nonempty hs hs2
  -- a point of `lens` (resp. `outerLens`) is in `P ∪ Q`, hence avoids the other piece
  have key : ∀ {Y : Set ℂ} {z : ℂ}, z ∈ lens s → Y ⊆ outerLens s → z ∈ P ∪ Q → z ∉ Y := by
    intro Y z hz hY _
    exact fun hcond => Set.disjoint_left.mp disjoint_lens_outerLens hz (hY hcond)
  have key' : ∀ {Y : Set ℂ} {z : ℂ}, z ∈ outerLens s → Y ⊆ lens s → z ∈ P ∪ Q → z ∉ Y := by
    intro Y z hz hY _
    exact fun hcond => Set.disjoint_left.mp disjoint_lens_outerLens (hY hcond) hz
  have hof : ∀ {z : ℂ}, z ∈ lens s ∨ z ∈ outerLens s → z ∈ P ∪ Q := by
    intro z hz
    have h1 : z ∈ Metric.ball (0 : ℂ) 1 \ Set.range (capArcPath s) := by
      rw [← hcompl]; exact hz
    rw [← hunion]; exact h1
  have hcases : (P ⊆ lens s ∧ Q ⊆ outerLens s) ∨ (P ⊆ outerLens s ∧ Q ⊆ lens s) := by
    rcases hP with h1 | h1 <;> rcases hQ with h2 | h2
    · -- both pieces inside the lens: `outerLens` would be inside `P ∪ Q ⊆ lens`
      exfalso
      obtain ⟨z, hz⟩ := hneO
      rcases hof (Or.inr hz) with h | h
      · exact (Set.disjoint_left.mp disjoint_lens_outerLens) (h1 h) hz
      · exact (Set.disjoint_left.mp disjoint_lens_outerLens) (h2 h) hz
    · exact Or.inl ⟨h1, h2⟩
    · exact Or.inr ⟨h1, h2⟩
    · -- both pieces inside `outerLens`: the lens would be inside `P ∪ Q ⊆ outerLens`
      exfalso
      obtain ⟨z, hz⟩ := hneL
      rcases hof (Or.inl hz) with h | h
      · exact (Set.disjoint_left.mp disjoint_lens_outerLens) hz (h1 h)
      · exact (Set.disjoint_left.mp disjoint_lens_outerLens) hz (h2 h)
  refine ⟨P, Q, hPne, hQne, hPopen, hQopen, hPpre, hQpre, hunion, hdisj, ?_⟩
  rcases hcases with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · left
    refine Set.Subset.antisymm ?_ h1
    intro z hz
    rcases hof (Or.inl hz) with h | h
    · exact h
    · exact absurd (h2 h) (fun hcon => Set.disjoint_left.mp disjoint_lens_outerLens hz hcon)
  · right
    refine Set.Subset.antisymm ?_ h2
    intro z hz
    rcases hof (Or.inl hz) with h | h
    · exact absurd (h1 h) (fun hcon => Set.disjoint_left.mp disjoint_lens_outerLens hz hcon)
    · exact h

end Work.Smooth.SphereJordan.Caratheodory
