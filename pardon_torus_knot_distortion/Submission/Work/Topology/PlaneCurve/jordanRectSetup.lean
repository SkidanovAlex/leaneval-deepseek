import Mathlib
import Submission.Work.Smooth.SphereJordan.brouwer_disc
import Submission.Work.Topology.PlaneCurve.plane_crossing_lemma
import Submission.Work.Smooth.SphereJordan.range_eq_of_subset_of_periodic
import Submission.Work.Smooth.JordanSeparation.exists_continuum_separating

/-!
# The rectangle setup for Maehara's proof of the Jordan curve theorem

Definitions and elementary lemmas used by `Work.Topology.PlaneCurve.compl_jordan_atMostTwo`:

* the open rectangle `rectR = (-1,1) × (-2,2)`, the vertical segment `vSeg`, the points
  `ptTop = 2I`, `ptBot = -2I`, the closed box `closedBox = [-1,1] × [-2,2]`;
* `crossing_rect`, the crossing lemma (`Work.Topology.PlaneCurve.plane_crossing_lemma`) rescaled to
  the rectangle `(-1,1) × (-2,2)`: a path from the left side to the right side meets every path
  from the bottom side to the top side;
* `vSeg_meet`: the trace of the curve meets the vertical segment `vSeg`;
* `exists_gap_of_decomp`: the gap lemma, two disjoint nonempty compact subsets of `ℝ` have two
  points of their union with nothing of the union in between.
-/

namespace Work.Topology.PlaneCurve

open Set

noncomputable section

/-- The open rectangle `(-1,1) × (-2,2) ⊆ ℂ`. -/
def rectR : Set ℂ := {z : ℂ | -1 < z.re ∧ z.re < 1 ∧ -2 < z.im ∧ z.im < 2}

/-- The closed vertical segment `{0} × [-2,2] ⊆ ℂ`. -/
def vSeg : Set ℂ := {z : ℂ | z.re = 0 ∧ -2 ≤ z.im ∧ z.im ≤ 2}

/-- The top middle point `(0,2)`. -/
def ptTop : ℂ := 2 * Complex.I

/-- The bottom middle point `(0,-2)`. -/
def ptBot : ℂ := -2 * Complex.I

@[simp] theorem ptTop_re : ptTop.re = 0 := by simp [ptTop]
@[simp] theorem ptTop_im : ptTop.im = 2 := by simp [ptTop]
@[simp] theorem ptBot_re : ptBot.re = 0 := by simp [ptBot]
@[simp] theorem ptBot_im : ptBot.im = -2 := by simp [ptBot]

theorem ptTop_mem_vSeg : ptTop ∈ vSeg := by
  refine ⟨by simp, by simp, by simp⟩

theorem ptBot_mem_vSeg : ptBot ∈ vSeg := by
  refine ⟨by simp, by simp, by simp⟩

theorem vSeg_convex : Convex ℝ vSeg := by
  intro x hx y hy a b _ _ _
  obtain ⟨hx1, hx2, hx3⟩ := hx
  obtain ⟨hy1, hy2, hy3⟩ := hy
  refine ⟨?_, ?_, ?_⟩
  · simp [hx1, hy1]
  · have : (a • x + b • y).im = a * x.im + b * y.im := by simp
    rw [this]; nlinarith
  · have : (a • x + b • y).im = a * x.im + b * y.im := by simp
    rw [this]; nlinarith

/-- The crossing lemma, in the form of the rectangle `(-1,1) × (-2,2)`: a continuous path joining
the left side to the right side meets every continuous path joining the bottom side to the top
side. -/
theorem crossing_rect {h v : ℝ → ℂ} (hh : Continuous h) (hv : Continuous v)
    (hhbox : ∀ t ∈ Icc (-1:ℝ) 1, |(h t).re| ≤ 1 ∧ |(h t).im| ≤ 2)
    (hvbox : ∀ t ∈ Icc (-1:ℝ) 1, |(v t).re| ≤ 1 ∧ |(v t).im| ≤ 2)
    (hh_left : (h (-1)).re = -1) (hh_right : (h 1).re = 1)
    (hv_bot : (v (-1)).im = -2) (hv_top : (v 1).im = 2) :
    ∃ s ∈ Icc (-1:ℝ) 1, ∃ t ∈ Icc (-1:ℝ) 1, h s = v t := by
  set H : ℝ → ℂ := fun t => (h t).re + ((h t).im / 2) * Complex.I with hH
  set V : ℝ → ℂ := fun t => (v t).re + ((v t).im / 2) * Complex.I with hV
  have hHc : Continuous H := by rw [hH]; fun_prop
  have hVc : Continuous V := by rw [hV]; fun_prop
  have hHbox : ∀ t ∈ Icc (-1:ℝ) 1, |(H t).re| ≤ 1 ∧ |(H t).im| ≤ 1 := by
    intro t ht
    obtain ⟨h1, h2⟩ := hhbox t ht
    have hre : (H t).re = (h t).re := by rw [hH]; simp
    have him : (H t).im = (h t).im / 2 := by rw [hH]; simp
    rw [hre, him]
    refine ⟨h1, ?_⟩
    have : |(h t).im / 2| ≤ 1 := by rw [abs_div]; norm_num; linarith
    exact this
  have hVbox : ∀ t ∈ Icc (-1:ℝ) 1, |(V t).re| ≤ 1 ∧ |(V t).im| ≤ 1 := by
    intro t ht
    obtain ⟨h1, h2⟩ := hvbox t ht
    have hre : (V t).re = (v t).re := by rw [hV]; simp
    have him : (V t).im = (v t).im / 2 := by rw [hV]; simp
    rw [hre, him]
    refine ⟨h1, ?_⟩
    have : |(v t).im / 2| ≤ 1 := by rw [abs_div]; norm_num; linarith
    exact this
  have hHleft : (H (-1)).re = -1 := by rw [hH]; simpa using hh_left
  have hHright : (H 1).re = 1 := by rw [hH]; simpa using hh_right
  have hVbot : (V (-1)).im = -1 := by
    have him : (V (-1)).im = (v (-1)).im / 2 := by rw [hV]; simp
    rw [him, hv_bot]; norm_num
  have hVtop : (V 1).im = 1 := by
    have him : (V 1).im = (v 1).im / 2 := by rw [hV]; simp
    rw [him, hv_top]; norm_num
  obtain ⟨s, hs, t, ht, heq⟩ := plane_crossing_lemma hHc hVc hHbox hVbox hHleft hHright hVbot hVtop
  refine ⟨s, hs, t, ht, ?_⟩
  have h1 : (h s).re = (v t).re := by
    have := congrArg Complex.re heq
    rw [hH, hV] at this
    simpa using this
  have h2 : (h s).im = (v t).im := by
    have hs' : (H s).im = (h s).im / 2 := by rw [hH]; simp
    have ht' : (V t).im = (v t).im / 2 := by rw [hV]; simp
    have := congrArg Complex.im heq
    rw [hs', ht'] at this
    linarith
  exact Complex.ext h1 h2

theorem rectR_subset_box {z : ℂ} (hz : z ∈ rectR) : |z.re| ≤ 1 ∧ |z.im| ≤ 2 := by
  obtain ⟨h1, h2, h3, h4⟩ := hz
  refine ⟨?_, ?_⟩ <;> rw [abs_le] <;> constructor <;> linarith

theorem neg1_mem_box : |(-1 : ℂ).re| ≤ 1 ∧ |(-1 : ℂ).im| ≤ 2 := by
  constructor <;> norm_num

theorem one_mem_box : |(1 : ℂ).re| ≤ 1 ∧ |(1 : ℂ).im| ≤ 2 := by
  constructor <;> norm_num

/-- The vertical segment `vSeg` meets the trace of `γ`, by the crossing lemma. -/
theorem vSeg_meet {γ : ℝ → ℂ} (hcont : Continuous γ)
    (hsub : ∀ w ∈ Set.range γ, w ∈ rectR ∨ w = -1 ∨ w = 1)
    (hm1 : -1 ∈ Set.range γ) (h1 : 1 ∈ Set.range γ) :
    (Set.range γ ∩ vSeg).Nonempty := by
  obtain ⟨sm, hsm⟩ := hm1
  obtain ⟨sp, hsp⟩ := h1
  set H : ℝ → ℂ := fun t => γ (sm + (t + 1) / 2 * (sp - sm)) with hHdef
  set V : ℝ → ℂ := fun t => (2 * t : ℝ) * Complex.I with hVdef
  have hHc : Continuous H := by rw [hHdef]; exact hcont.comp (by fun_prop)
  have hVc : Continuous V := by rw [hVdef]; fun_prop
  have hHbox : ∀ t ∈ Icc (-1:ℝ) 1, |(H t).re| ≤ 1 ∧ |(H t).im| ≤ 2 := by
    intro t ht
    have hmem : H t ∈ Set.range γ := ⟨_, rfl⟩
    rcases hsub (H t) hmem with h | h | h
    · exact rectR_subset_box h
    · rw [h]; exact neg1_mem_box
    · rw [h]; exact one_mem_box
  have hVbox : ∀ t ∈ Icc (-1:ℝ) 1, |(V t).re| ≤ 1 ∧ |(V t).im| ≤ 2 := by
    intro t ht
    have him : (V t).im = 2 * t := by rw [hVdef]; simp
    have hre : (V t).re = 0 := by rw [hVdef]; simp
    refine ⟨?_, ?_⟩
    · rw [hre]; norm_num
    · rw [him]
      have : |2 * t| ≤ 2 := by rw [abs_mul]; norm_num; rw [abs_le]; exact ht
      exact this
  have hHleft : (H (-1)).re = -1 := by
    have h1' : H (-1) = -1 := by
      rw [hHdef]
      simp only
      rw [show sm + ((-1:ℝ) + 1) / 2 * (sp - sm) = sm by ring]
      exact hsm
    rw [h1']; norm_num
  have hHright : (H 1).re = 1 := by
    have h1' : H 1 = 1 := by
      rw [hHdef]
      simp only
      rw [show sm + ((1:ℝ) + 1) / 2 * (sp - sm) = sp by ring]
      exact hsp
    rw [h1']; norm_num
  have hVbot : (V (-1)).im = -2 := by rw [hVdef]; norm_num
  have hVtop : (V 1).im = 2 := by rw [hVdef]; norm_num
  obtain ⟨s, _, t, ht, heq⟩ := crossing_rect hHc hVc hHbox hVbox hHleft hHright hVbot hVtop
  refine ⟨H s, ⟨_, rfl⟩, ?_⟩
  rw [heq]
  refine ⟨?_, ?_, ?_⟩
  · rw [hVdef]; simp
  · rw [hVdef]
    have hh : ((↑(2 * t) : ℂ) * Complex.I).im = 2 * t := by simp
    rw [hh]; linarith [ht.1]
  · rw [hVdef]
    have hh : ((↑(2 * t) : ℂ) * Complex.I).im = 2 * t := by simp
    rw [hh]; linarith [ht.2]

/-- The closed box `[-1,1] × [-2,2]`. -/
def closedBox : Set ℂ := {z : ℂ | |z.re| ≤ 1 ∧ |z.im| ≤ 2}

theorem rectR_subset_closedBox {z : ℂ} (hz : z ∈ rectR) : z ∈ closedBox :=
  rectR_subset_box hz

theorem neg1_mem_closedBox : (-1 : ℂ) ∈ closedBox := neg1_mem_box

theorem one_mem_closedBox : (1 : ℂ) ∈ closedBox := one_mem_box

theorem ptTop_mem_closedBox : ptTop ∈ closedBox := by
  refine ⟨?_, ?_⟩ <;> simp

theorem ptBot_mem_closedBox : ptBot ∈ closedBox := by
  refine ⟨?_, ?_⟩ <;> simp

theorem range_subset_closedBox {γ : ℝ → ℂ}
    (hsub : ∀ w ∈ Set.range γ, w ∈ rectR ∨ w = -1 ∨ w = 1) :
    Set.range γ ⊆ closedBox := by
  intro w hw
  rcases hsub w hw with h | h | h
  · exact rectR_subset_closedBox h
  · rw [h]; exact neg1_mem_closedBox
  · rw [h]; exact one_mem_closedBox

/-- **The gap lemma.** If `X` and `Y` are disjoint nonempty compact subsets of `ℝ`, there are two
points of `X ∪ Y` with no point of `X ∪ Y` strictly between them.  (Applied to the two arcs onto
which a pair of points of a Jordan curve divides it, this produces the "free window" on a crosscut
which Maehara's argument uses.) -/
theorem exists_gap_of_decomp {X Y : Set ℝ} (hX : IsCompact X) (hY : IsCompact Y)
    (hneX : X.Nonempty) (hneY : Y.Nonempty) (hdisj : Disjoint X Y) :
    ∃ a ∈ X ∪ Y, ∃ b ∈ X ∪ Y, a < b ∧ ∀ c ∈ X ∪ Y, ¬ (a < c ∧ c < b) := by
  have hcomp : IsCompact (X ×ˢ Y : Set (ℝ × ℝ)) := hX.prod hY
  have hne : (X ×ˢ Y : Set (ℝ × ℝ)).Nonempty := hneX.prod hneY
  obtain ⟨p, hp, hpmin⟩ := hcomp.exists_isMinOn hne
    ((continuous_fst.sub continuous_snd).abs.continuousOn)
  obtain ⟨hpx, hpy⟩ := hp
  have hne' : p.1 ≠ p.2 := fun h => Set.disjoint_left.mp hdisj hpx (h ▸ hpy)
  rcases lt_or_gt_of_ne hne' with h | h
  · refine ⟨p.1, Or.inl hpx, p.2, Or.inr hpy, h, ?_⟩
    rintro c (hcX | hcY) ⟨h1, h2⟩
    · have hlt : |c - p.2| < |p.1 - p.2| := by
        rw [abs_of_neg (by linarith), abs_of_neg (by linarith)]; linarith
      have hkey : |p.1 - p.2| ≤ |c - p.2| := hpmin (show (c, p.2) ∈ X ×ˢ Y from ⟨hcX, hpy⟩)
      linarith
    · have hlt : |p.1 - c| < |p.1 - p.2| := by
        rw [abs_of_neg (by linarith), abs_of_neg (by linarith)]; linarith
      have hkey : |p.1 - p.2| ≤ |p.1 - c| := hpmin (show (p.1, c) ∈ X ×ˢ Y from ⟨hpx, hcY⟩)
      linarith
  · refine ⟨p.2, Or.inr hpy, p.1, Or.inl hpx, h, ?_⟩
    rintro c (hcX | hcY) ⟨h1, h2⟩
    · have hlt : |c - p.2| < |p.1 - p.2| := by
        rw [abs_of_pos (by linarith), abs_of_pos (by linarith)]; linarith
      have hkey : |p.1 - p.2| ≤ |c - p.2| := hpmin (show (c, p.2) ∈ X ×ˢ Y from ⟨hcX, hpy⟩)
      linarith
    · have hlt : |p.1 - c| < |p.1 - p.2| := by
        rw [abs_of_pos (by linarith), abs_of_pos (by linarith)]; linarith
      have hkey : |p.1 - p.2| ≤ |p.1 - c| := hpmin (show (p.1, c) ∈ X ×ˢ Y from ⟨hpx, hcY⟩)
      linarith


end

end Work.Topology.PlaneCurve
