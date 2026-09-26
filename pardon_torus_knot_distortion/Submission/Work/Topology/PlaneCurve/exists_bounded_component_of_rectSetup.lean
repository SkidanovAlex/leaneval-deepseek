import Mathlib
import Submission.Work.Topology.PlaneCurve.jordanRectSetup
import Submission.Work.Topology.PlaneCurve.arcMembership
import Submission.Work.Topology.PlaneCurve.compl_jordan_atMostTwo
import Submission.Work.Topology.PlaneCurve.frontier_component_eq_range
import Submission.Work.Smooth.SphereJordan.atMostTwoNormalized

/-!
# A point of the imaginary axis with bounded complementary component (rectangle setup)

For a continuous `2π`-periodic curve `γ : ℝ → ℂ` injective on one period, whose trace lies in the
open rectangle `rectR = (-1,1) × (-2,2)` apart from the two points `±1`, with `γ 0 = -1` and
`1 ∈ range γ`, there is a point `z` of the imaginary axis, off the trace, whose component in the
complement of the trace is bounded.

This is the "boundedness" half of Maehara's proof of the Jordan curve theorem in the form needed
by Pardon's argument: the free window of `Work.Smooth.SphereJordan.exists_windowConfig` supplies a
point of the imaginary axis off the trace, and one shows that its component cannot leave the closed
box `closedBox = [-1,1] × [-2,2]`: any path from it to the outside of the box, truncated at its
first exit, would produce (together with the pieces of the window configuration) a bottom-to-top
path of the box avoiding one of the two arcs into which `±1` cut the trace, contradicting the
crossing lemma `Work.Topology.PlaneCurve.crossing_rect`.
-/

namespace Work.Topology.PlaneCurve

open Set

noncomputable section

/-! ## The box: interior, frontier and the two half-boundaries -/

theorem isOpen_rectR : IsOpen rectR := by
  rw [rectR]
  exact IsOpen.inter (isOpen_lt continuous_const Complex.continuous_re)
    (IsOpen.inter (isOpen_lt Complex.continuous_re continuous_const)
      (IsOpen.inter (isOpen_lt continuous_const Complex.continuous_im)
        (isOpen_lt Complex.continuous_im continuous_const)))

theorem rectR_subset_closedBox' : rectR ⊆ closedBox := fun z hz => rectR_subset_closedBox hz

theorem rectR_subset_interior_closedBox : rectR ⊆ interior closedBox :=
  interior_maximal rectR_subset_closedBox' isOpen_rectR

theorem isClosed_closedBox : IsClosed closedBox := by
  have h : closedBox = {z : ℂ | |z.re| ≤ 1} ∩ {z : ℂ | |z.im| ≤ 2} := by
    ext z; simp [closedBox]
  rw [h]
  exact IsClosed.inter (isClosed_le (continuous_abs.comp Complex.continuous_re) continuous_const)
    (isClosed_le (continuous_abs.comp Complex.continuous_im) continuous_const)

theorem frontier_closedBox_subset_closedBox {w : ℂ} (hw : w ∈ frontier closedBox) :
    |w.re| ≤ 1 ∧ |w.im| ≤ 2 := by
  have h1 : w ∈ closure closedBox := frontier_subset_closure hw
  rw [isClosed_closedBox.closure_eq] at h1
  simpa [closedBox] using h1

theorem not_mem_interior_closedBox_of_mem_frontier {w : ℂ} (hw : w ∈ frontier closedBox) :
    w ∉ interior closedBox := by
  have h2 : w ∈ closure (closedBox : Set ℂ)ᶜ := by
    rw [frontier_eq_closure_inter_closure] at hw; exact hw.2
  rwa [closure_compl] at h2

theorem interior_closedBox_subset_strict :
    interior closedBox ⊆ {z : ℂ | |z.re| < 1 ∧ |z.im| < 2} := by
  intro z hz
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp isOpen_interior z hz
  have hmem : ∀ y : ℂ, dist y z < ε → |y.re| ≤ 1 ∧ |y.im| ≤ 2 := by
    intro y hy
    have hy' : y ∈ Metric.ball z ε := by rw [Metric.mem_ball]; exact hy
    have h := interior_subset (hball hy')
    simpa [closedBox] using h
  set c : ℂ := (((ε/2 : ℝ)) : ℂ) with hc
  have hcval : ‖c‖ < ε := by
    rw [hc, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith : (0:ℝ) < ε/2)]
    linarith
  have hd1 : dist (z + c) z < ε := by rw [dist_eq_norm, add_sub_cancel_left]; exact hcval
  have hd2 : dist (z - c) z < ε := by
    rw [dist_eq_norm, show (z - c) - z = -c by ring, norm_neg]; exact hcval
  have hd3 : dist (z + c * Complex.I) z < ε := by
    rw [dist_eq_norm, show (z + c * Complex.I) - z = c * Complex.I by ring,
      norm_mul, Complex.norm_I, mul_one]; exact hcval
  have hd4 : dist (z - c * Complex.I) z < ε := by
    rw [dist_eq_norm, show (z - c * Complex.I) - z = -(c * Complex.I) by ring,
      norm_neg, norm_mul, Complex.norm_I, mul_one]; exact hcval
  have hre1 : (z + c).re = z.re + ε/2 := by simp [hc]
  have hre2 : (z - c).re = z.re - ε/2 := by simp [hc]
  have him1 : (z + c * Complex.I).im = z.im + ε/2 := by simp [hc]
  have him2 : (z - c * Complex.I).im = z.im - ε/2 := by simp [hc]
  constructor
  · rw [abs_lt]; constructor
    · by_contra hcc; push_neg at hcc
      have h1 : |(z - c).re| ≤ 1 := (hmem _ hd2).1
      rw [hre2, abs_of_neg (by linarith : z.re - ε/2 < 0)] at h1; linarith
    · by_contra hcc; push_neg at hcc
      have h1 : |(z + c).re| ≤ 1 := (hmem _ hd1).1
      rw [hre1, abs_of_pos (by linarith : (0:ℝ) < z.re + ε/2)] at h1; linarith
  · rw [abs_lt]; constructor
    · by_contra hcc; push_neg at hcc
      have h1 : |(z - c * Complex.I).im| ≤ 2 := (hmem _ hd4).2
      rw [him2, abs_of_neg (by linarith : z.im - ε/2 < 0)] at h1; linarith
    · by_contra hcc; push_neg at hcc
      have h1 : |(z + c * Complex.I).im| ≤ 2 := (hmem _ hd3).2
      rw [him1, abs_of_pos (by linarith : (0:ℝ) < z.im + ε/2)] at h1; linarith

theorem mem_frontier_closedBox_iff (z : ℂ) :
    z ∈ frontier closedBox ↔ |z.re| ≤ 1 ∧ |z.im| ≤ 2 ∧ (|z.re| = 1 ∨ |z.im| = 2) := by
  constructor
  · intro hz
    have hbox := frontier_closedBox_subset_closedBox hz
    refine ⟨hbox.1, hbox.2, ?_⟩
    by_contra hcon
    push_neg at hcon
    obtain ⟨hre, him⟩ := hcon
    have hlt1 : |z.re| < 1 := lt_of_le_of_ne hbox.1 hre
    have hlt2 : |z.im| < 2 := lt_of_le_of_ne hbox.2 him
    have hzr : z ∈ rectR := by
      rw [rectR]
      rw [abs_lt] at hlt1 hlt2
      exact ⟨hlt1.1, hlt1.2, hlt2.1, hlt2.2⟩
    exact not_mem_interior_closedBox_of_mem_frontier hz (rectR_subset_interior_closedBox hzr)
  · rintro ⟨h1, h2, h3⟩
    rw [frontier_eq_closure_inter_closure]
    constructor
    · rw [isClosed_closedBox.closure_eq]; simpa [closedBox] using ⟨h1, h2⟩
    · rw [closure_compl]
      intro hcon
      have hstrict := interior_closedBox_subset_strict hcon
      rcases h3 with h3 | h3
      · exact absurd h3 (ne_of_lt hstrict.1)
      · exact absurd h3 (ne_of_lt hstrict.2)

theorem range_inter_frontier_closedBox_subset {γ : ℝ → ℂ}
    (hsub : ∀ w ∈ Set.range γ, w ∈ rectR ∨ w = -1 ∨ w = 1) :
    Set.range γ ∩ frontier closedBox ⊆ ({-1, 1} : Set ℂ) := by
  rintro w ⟨hwγ, hwf⟩
  rcases hsub w hwγ with h | h | h
  · exact absurd (rectR_subset_interior_closedBox h)
      (not_mem_interior_closedBox_of_mem_frontier hwf)
  · rw [h]; exact Set.mem_insert _ _
  · rw [h]; exact Set.mem_insert_of_mem _ rfl

/-- A convex combination of two strictly negative numbers is strictly negative. -/
theorem comboNeg {a b s : ℝ} (ha : a < 0) (hb : b < 0) (hs1 : 0 ≤ s) (hs2 : s ≤ 1) :
    (1 - s) * a + s * b < 0 := by
  rcases lt_or_eq_of_le hs2 with h | h
  · have h1 : (1 - s) * a < 0 := mul_neg_of_pos_of_neg (by linarith) ha
    have h2 : s * b ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hs1 hb.le
    linarith
  · subst h; ring_nf; exact hb

/-- **Bottom half of the boundary.**  A point of the frontier of the closed box below the real
axis is joined to `ptBot = -2I` inside the frontier. -/
theorem exists_path_frontier_closedBox_bot {w : ℂ} (hw : w ∈ frontier closedBox)
    (hwim : w.im < 0) :
    ∃ σ : Path w ptBot, Set.range σ ⊆ frontier closedBox ∧
      (∀ t, (σ t).im < 0) ∧ (∀ t, σ t ≠ -1 ∧ σ t ≠ 1) := by
  obtain ⟨hre, him, hdisj⟩ := (mem_frontier_closedBox_iff w).mp hw
  obtain ⟨hi1, hi2⟩ := abs_le.mp him
  have hwi : (0:ℝ) ≤ w.im + 2 := by linarith
  set mid : ℂ := ⟨w.re, -2⟩ with hmid
  have hmidre : mid.re = w.re := rfl
  have hmidim : mid.im = -2 := rfl
  have hw2 : w.im = -2 ∨ |w.re| = 1 := by
    rcases hdisj with h | h
    · right; exact h
    · left
      rw [abs_of_neg hwim] at h
      linarith
  have hseg1_im : ∀ t : unitInterval,
      ((Path.segment w mid) t).im = (1 - (t:ℝ)) * w.im + (t:ℝ) * (-2) := by
    intro t
    rw [Work.Smooth.SphereJordan.segment_im, hmidim]
  have hseg2_im : ∀ t : unitInterval, ((Path.segment mid ptBot) t).im = -2 := by
    intro t
    rw [Work.Smooth.SphereJordan.segment_im, hmidim, ptBot_im]; ring
  have hseg1f : ∀ t : unitInterval, (Path.segment w mid) t ∈ frontier closedBox := by
    intro t
    rw [mem_frontier_closedBox_iff]
    have hre' : ((Path.segment w mid) t).re = w.re := by
      rw [Work.Smooth.SphereJordan.segment_re, hmidre]; ring
    have ht1 : (0:ℝ) ≤ (t:ℝ) := t.2.1
    have hle : (1 - (t:ℝ)) * w.im + (t:ℝ) * (-2) ≤ w.im := by
      have := mul_nonneg ht1 hwi
      nlinarith [this]
    have hge : -2 ≤ (1 - (t:ℝ)) * w.im + (t:ℝ) * (-2) := by
      have hnn : (0:ℝ) ≤ 1 - (t:ℝ) := by linarith [t.2.2]
      have := mul_nonneg hnn hwi
      nlinarith [this]
    refine ⟨by rw [hre']; exact hre, ?_, ?_⟩
    · rw [hseg1_im t, abs_le]; exact ⟨hge, by linarith⟩
    · rcases hw2 with h | h
      · right
        rw [hseg1_im t, h]
        have : (1 - (t:ℝ)) * (-2) + (t:ℝ) * (-2) = -2 := by ring
        rw [this]; norm_num
      · left; rw [hre']; exact h
  have hseg2f : ∀ t : unitInterval, (Path.segment mid ptBot) t ∈ frontier closedBox := by
    intro t
    rw [mem_frontier_closedBox_iff]
    have hre' : ((Path.segment mid ptBot) t).re = (1 - (t:ℝ)) * w.re := by
      rw [Work.Smooth.SphereJordan.segment_re, hmidre, ptBot_re]; ring
    have hnn : (0:ℝ) ≤ 1 - (t:ℝ) := by linarith [t.2.2]
    have hle : (1 - (t:ℝ)) * |w.re| ≤ 1 := by
      have h1 : (1 - (t:ℝ)) * |w.re| ≤ (1 - (t:ℝ)) * 1 := mul_le_mul_of_nonneg_left hre hnn
      rw [mul_one] at h1; linarith [t.2.1]
    refine ⟨?_, ?_, ?_⟩
    · rw [hre', abs_mul, abs_of_nonneg hnn]; exact hle
    · rw [hseg2_im t]; norm_num
    · right; rw [hseg2_im t]; norm_num
  have hseg1neg : ∀ t : unitInterval, ((Path.segment w mid) t).im < 0 := by
    intro t
    rw [hseg1_im t]
    exact comboNeg hwim (by norm_num) t.2.1 (by linarith [t.2.2])
  have hseg2neg : ∀ t : unitInterval, ((Path.segment mid ptBot) t).im < 0 := by
    intro t; rw [hseg2_im t]; norm_num
  have hneg : ∀ t : unitInterval, ((Path.segment w mid).trans (Path.segment mid ptBot) t).im < 0 :=
    Work.Smooth.SphereJordan.trans_mem (S := {z : ℂ | z.im < 0}) _ _ hseg1neg hseg2neg
  refine ⟨(Path.segment w mid).trans (Path.segment mid ptBot), ?_, hneg, ?_⟩
  · rintro z ⟨t, rfl⟩
    exact Work.Smooth.SphereJordan.trans_mem _ _ hseg1f hseg2f t
  · intro t
    constructor <;> intro hcon
    · have h := hneg t
      rw [hcon] at h
      norm_num at h
    · have h := hneg t
      rw [hcon] at h
      norm_num at h

/-- **Top half of the boundary.**  A point of the frontier of the closed box above the real
axis is joined to `ptTop = 2I` inside the frontier. -/
theorem exists_path_frontier_closedBox_top {w : ℂ} (hw : w ∈ frontier closedBox)
    (hwim : 0 < w.im) :
    ∃ σ : Path w ptTop, Set.range σ ⊆ frontier closedBox ∧
      (∀ t, 0 < (σ t).im) ∧ (∀ t, σ t ≠ -1 ∧ σ t ≠ 1) := by
  obtain ⟨hre, him, hdisj⟩ := (mem_frontier_closedBox_iff w).mp hw
  obtain ⟨hi1, hi2⟩ := abs_le.mp him
  have hwi : (0:ℝ) ≤ 2 - w.im := by linarith
  set mid : ℂ := ⟨w.re, 2⟩ with hmid
  have hmidre : mid.re = w.re := rfl
  have hmidim : mid.im = 2 := rfl
  have hw2 : w.im = 2 ∨ |w.re| = 1 := by
    rcases hdisj with h | h
    · right; exact h
    · left
      rw [abs_of_pos hwim] at h
      linarith
  have hseg1_im : ∀ t : unitInterval,
      ((Path.segment w mid) t).im = (1 - (t:ℝ)) * w.im + (t:ℝ) * 2 := by
    intro t
    rw [Work.Smooth.SphereJordan.segment_im, hmidim]
  have hseg2_im : ∀ t : unitInterval, ((Path.segment mid ptTop) t).im = 2 := by
    intro t
    rw [Work.Smooth.SphereJordan.segment_im, hmidim, ptTop_im]; ring
  have hseg1f : ∀ t : unitInterval, (Path.segment w mid) t ∈ frontier closedBox := by
    intro t
    rw [mem_frontier_closedBox_iff]
    have hre' : ((Path.segment w mid) t).re = w.re := by
      rw [Work.Smooth.SphereJordan.segment_re, hmidre]; ring
    have ht1 : (0:ℝ) ≤ (t:ℝ) := t.2.1
    have hge : w.im ≤ (1 - (t:ℝ)) * w.im + (t:ℝ) * 2 := by
      have := mul_nonneg ht1 hwi
      nlinarith [this]
    have hle : (1 - (t:ℝ)) * w.im + (t:ℝ) * 2 ≤ 2 := by
      have hnn : (0:ℝ) ≤ 1 - (t:ℝ) := by linarith [t.2.2]
      have := mul_nonneg hnn hwi
      nlinarith [this]
    refine ⟨by rw [hre']; exact hre, ?_, ?_⟩
    · rw [hseg1_im t, abs_le]; exact ⟨by linarith, hle⟩
    · rcases hw2 with h | h
      · right
        rw [hseg1_im t, h]
        have : (1 - (t:ℝ)) * 2 + (t:ℝ) * 2 = 2 := by ring
        rw [this]; norm_num
      · left; rw [hre']; exact h
  have hseg2f : ∀ t : unitInterval, (Path.segment mid ptTop) t ∈ frontier closedBox := by
    intro t
    rw [mem_frontier_closedBox_iff]
    have hre' : ((Path.segment mid ptTop) t).re = (1 - (t:ℝ)) * w.re := by
      rw [Work.Smooth.SphereJordan.segment_re, hmidre, ptTop_re]; ring
    have hnn : (0:ℝ) ≤ 1 - (t:ℝ) := by linarith [t.2.2]
    have hle : (1 - (t:ℝ)) * |w.re| ≤ 1 := by
      have h1 : (1 - (t:ℝ)) * |w.re| ≤ (1 - (t:ℝ)) * 1 := mul_le_mul_of_nonneg_left hre hnn
      rw [mul_one] at h1; linarith [t.2.1]
    refine ⟨?_, ?_, ?_⟩
    · rw [hre', abs_mul, abs_of_nonneg hnn]; exact hle
    · rw [hseg2_im t]; norm_num
    · right; rw [hseg2_im t]; norm_num
  have hseg1pos : ∀ t : unitInterval, 0 < ((Path.segment w mid) t).im := by
    intro t
    rw [hseg1_im t]
    have := comboNeg (show -w.im < 0 by linarith) (by norm_num : (-2:ℝ) < 0) t.2.1
      (by linarith [t.2.2])
    linarith
  have hseg2pos : ∀ t : unitInterval, 0 < ((Path.segment mid ptTop) t).im := by
    intro t; rw [hseg2_im t]; norm_num
  have hpos : ∀ t : unitInterval, 0 < ((Path.segment w mid).trans (Path.segment mid ptTop) t).im :=
    Work.Smooth.SphereJordan.trans_mem (S := {z : ℂ | 0 < z.im}) _ _ hseg1pos hseg2pos
  refine ⟨(Path.segment w mid).trans (Path.segment mid ptTop), ?_, hpos, ?_⟩
  · rintro z ⟨t, rfl⟩
    exact Work.Smooth.SphereJordan.trans_mem _ _ hseg1f hseg2f t
  · intro t
    constructor <;> intro hcon
    · have h := hpos t
      rw [hcon] at h
      norm_num at h
    · have h := hpos t
      rw [hcon] at h
      norm_num at h

/-! ## First exit of a path from the box -/

/-- **First exit from the box.**  A path from a point of the rectangle `rectR` to a point outside
the closed box has a first time at which it leaves the rectangle; the restriction to that time
still lies in the closed box and ends on its boundary. -/
theorem exists_first_exit {z y : ℂ} {σ : Path z y} (hz : z ∈ rectR) (hy : y ∉ closedBox) :
    ∃ (w : ℂ) (σ₁ : Path z w), w ∈ frontier closedBox ∧ Set.range σ₁ ⊆ closedBox ∧
      Set.range σ₁ ⊆ Set.range σ := by
  have hI : CompactSpace unitInterval := isCompact_iff_compactSpace.mp isCompact_Icc
  have hzint : z ∈ interior closedBox := rectR_subset_interior_closedBox hz
  set S : Set unitInterval := {t | σ t ∉ interior closedBox} with hSdef
  have hSclosed : IsClosed S := by
    have h1 : IsOpen (σ ⁻¹' (interior closedBox)) := isOpen_interior.preimage σ.continuous
    have h2 : S = (σ ⁻¹' (interior closedBox))ᶜ := by ext t; simp [hSdef]
    rw [h2]; exact h1.isClosed_compl
  have h0S : (0 : unitInterval) ∉ S := by
    intro hcon
    have h : σ (0 : unitInterval) ∉ interior closedBox := hcon
    exact h (by rw [Path.source]; exact hzint)
  have hSne : S.Nonempty := ⟨(1 : unitInterval), by
    show σ (1 : unitInterval) ∉ interior closedBox
    rw [Path.target]; exact fun h => hy (interior_subset h)⟩
  obtain ⟨t₀, ht₀S, ht₀min⟩ := hSclosed.isCompact.exists_isMinOn hSne continuous_id.continuousOn
  have ht₀nn : (0:ℝ) ≤ (t₀:ℝ) := t₀.2.1
  have ht₀le : (t₀:ℝ) ≤ 1 := t₀.2.2
  have ht₀pos : 0 < (t₀:ℝ) := by
    rcases lt_or_eq_of_le ht₀nn with h | h
    · exact h
    · exfalso
      apply h0S
      have he : (0 : unitInterval) = t₀ := Subtype.ext h
      rw [he]; exact ht₀S
  have hL : ∀ s : unitInterval, (s:ℝ) < (t₀:ℝ) → σ s ∈ interior closedBox := by
    intro s hs
    by_contra hcon
    have h1 : (t₀:ℝ) ≤ (s:ℝ) := ht₀min hcon
    linarith
  have hwbox : σ t₀ ∈ closedBox := by
    by_contra hcon
    have hopen : IsOpen {s : unitInterval | σ s ∉ closedBox} :=
      (isClosed_closedBox.preimage σ.continuous).isOpen_compl
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hopen t₀ hcon
    set δ : ℝ := min ε (t₀:ℝ) / 2 with hδdef
    have hδpos : 0 < δ := by
      have h0 : 0 < min ε (t₀:ℝ) := lt_min hε ht₀pos
      rw [hδdef]; linarith
    have hδlt : δ < ε := by
      have := min_le_left ε (t₀:ℝ)
      rw [hδdef]; linarith
    have hδt : δ < (t₀:ℝ) := by
      have := min_le_right ε (t₀:ℝ)
      rw [hδdef]; linarith
    set s₀ : unitInterval := ⟨(t₀:ℝ) - δ,
      Set.mem_Icc.mpr ⟨by linarith, by linarith [ht₀le]⟩⟩ with hs₀def
    have hs₀val : (s₀:ℝ) = (t₀:ℝ) - δ := rfl
    have hs₀lt : (s₀:ℝ) < (t₀:ℝ) := by rw [hs₀val]; linarith
    have hballmem : s₀ ∈ Metric.ball t₀ ε := by
      rw [Metric.mem_ball, Subtype.dist_eq, Real.dist_eq, hs₀val]
      rw [show (t₀:ℝ) - δ - (t₀:ℝ) = -δ by ring, abs_neg, abs_of_pos hδpos]
      exact hδlt
    exact (hball hballmem) (interior_subset (hL s₀ hs₀lt))
  have hp : ∀ t : unitInterval, (t₀:ℝ) * (t:ℝ) ∈ unitInterval := fun t =>
    Set.mem_Icc.mpr ⟨mul_nonneg ht₀nn t.2.1, by nlinarith [ht₀nn, ht₀le, t.2.1, t.2.2]⟩
  have hf : Continuous (fun t : unitInterval => (⟨(t₀:ℝ) * (t:ℝ), hp t⟩ : unitInterval)) :=
    Continuous.subtype_mk (continuous_const.mul continuous_subtype_val) hp
  refine ⟨σ t₀, ⟨⟨fun t : unitInterval => σ ⟨(t₀:ℝ) * (t:ℝ), hp t⟩, σ.continuous.comp hf⟩, ?_, ?_⟩,
    ?_, ?_, ?_⟩
  · have h0 : (⟨(t₀:ℝ) * ((0 : unitInterval):ℝ), hp (0 : unitInterval)⟩ : unitInterval) =
        (0 : unitInterval) := Subtype.ext (by simp)
    exact (congrArg σ h0).trans (Path.source σ)
  · have h1 : (⟨(t₀:ℝ) * ((1 : unitInterval):ℝ), hp (1 : unitInterval)⟩ : unitInterval) = t₀ :=
      Subtype.ext (by simp)
    exact congrArg σ h1
  · rw [frontier_eq_closure_inter_closure]
    refine ⟨?_, ?_⟩
    · rwa [isClosed_closedBox.closure_eq]
    · rw [closure_compl]; exact ht₀S
  · rintro z ⟨t, rfl⟩
    show σ ⟨(t₀:ℝ) * (t:ℝ), hp t⟩ ∈ closedBox
    by_cases ht : (t:ℝ) = 1
    · have he : (⟨(t₀:ℝ) * (t:ℝ), hp t⟩ : unitInterval) = t₀ := by
        apply Subtype.ext
        simp [ht]
      rw [show σ ⟨(t₀:ℝ) * (t:ℝ), hp t⟩ = σ t₀ from congrArg σ he]
      exact hwbox
    · have ht1 : (t:ℝ) < 1 := lt_of_le_of_ne t.2.2 ht
      have hlt : (t₀:ℝ) * (t:ℝ) < (t₀:ℝ) := by
        have := mul_lt_mul_of_pos_left ht1 ht₀pos
        rwa [mul_one] at this
      exact interior_subset (hL _ hlt)
  · rintro z ⟨t, rfl⟩
    exact ⟨⟨(t₀:ℝ) * (t:ℝ), hp t⟩, rfl⟩
/-! ## Parameterising the two arcs cut out by `-1` and `1` -/

/-- The parametrisation of the arc `γ '' Icc c d` as a path on `[-1,1]`, from `γ c` to `γ d`. -/
def arcParam (γ : ℝ → ℂ) (c d : ℝ) : ℝ → ℂ := fun t => γ (c + (d - c) * (t + 1) / 2)

theorem arcParam_cont {γ : ℝ → ℂ} (hγ : Continuous γ) (c d : ℝ) :
    Continuous (arcParam γ c d) := by
  unfold arcParam; exact hγ.comp (by fun_prop)

theorem arcParam_neg {γ : ℝ → ℂ} {c d : ℝ} (hc : γ c = -1) : arcParam γ c d (-1) = -1 := by
  unfold arcParam; norm_num; exact hc

theorem arcParam_pos {γ : ℝ → ℂ} {c d : ℝ} (hd : γ d = 1) : arcParam γ c d 1 = 1 := by
  unfold arcParam; norm_num; exact hd

theorem arcParam_arg_mem {c d s : ℝ} (hcd : c ≤ d) (hs : s ∈ Set.Icc (-1:ℝ) 1) :
    c + (d - c) * (s + 1) / 2 ∈ Set.Icc c d := by
  obtain ⟨hs1, hs2⟩ := hs
  have h4 : (d - c) * ((s + 1) / 2) ≤ d - c := by
    have := mul_le_mul_of_nonneg_left (by linarith : (s+1)/2 ≤ 1) (by linarith : (0:ℝ) ≤ d - c)
    rwa [mul_one] at this
  have he : c + (d - c) * (s + 1) / 2 = c + (d - c) * ((s + 1) / 2) := by ring
  rw [he]
  exact ⟨by linarith [mul_nonneg (by linarith : (0:ℝ) ≤ d - c) (by linarith : (0:ℝ) ≤ (s+1)/2)],
    by linarith⟩

theorem arcParam_mem {γ : ℝ → ℂ} {c d : ℝ} (hcd : c ≤ d) (s : ℝ)
    (hs : s ∈ Set.Icc (-1:ℝ) 1) : arcParam γ c d s ∈ γ '' Set.Icc c d :=
  ⟨_, arcParam_arg_mem hcd hs, rfl⟩

theorem arcParam_arg_mem_minmax (c d : ℝ) (s : ℝ) (hs : s ∈ Set.Icc (-1:ℝ) 1) :
    c + (d - c) * (s + 1) / 2 ∈ Set.Icc (min c d) (max c d) := by
  rcases le_total c d with hcd | hcd
  · rw [min_eq_left hcd, max_eq_right hcd]; exact arcParam_arg_mem hcd hs
  · rw [min_eq_right hcd, max_eq_left hcd]
    have hs1 : (0:ℝ) ≤ (s + 1) / 2 := by linarith [hs.1]
    have hs2 : (s + 1) / 2 ≤ 1 := by linarith [hs.2]
    have he : c + (d - c) * (s + 1) / 2 = c - (c - d) * ((s + 1) / 2) := by ring
    rw [he]
    have h1 : (c - d) * ((s + 1) / 2) ≤ c - d := by
      have hh := mul_le_mul_of_nonneg_left hs2 (by linarith : (0:ℝ) ≤ c - d)
      rwa [mul_one] at hh
    have h2 : 0 ≤ (c - d) * ((s + 1) / 2) := mul_nonneg (by linarith) hs1
    exact ⟨by linarith, by linarith⟩

theorem arcParam_mem_minmax {γ : ℝ → ℂ} (c d : ℝ) (s : ℝ) (hs : s ∈ Set.Icc (-1:ℝ) 1) :
    arcParam γ c d s ∈ γ '' Set.Icc (min c d) (max c d) :=
  ⟨_, arcParam_arg_mem_minmax c d s hs, rfl⟩

/-- A left-to-right path of the box cannot avoid an arc of the trace joining `-1` to `1`. -/
theorem false_of_path_avoiding_arc {γ : ℝ → ℂ} (_hγ : Continuous γ)
    (hsub : ∀ w ∈ Set.range γ, w ∈ rectR ∨ w = -1 ∨ w = 1)
    {B : Set ℂ} (hBsub : B ⊆ Set.range γ)
    {hfun : ℝ → ℂ} (hfh : Continuous hfun)
    (hhneg : hfun (-1) = -1) (hhpos : hfun 1 = 1)
    (hhmem : ∀ s ∈ Set.Icc (-1:ℝ) 1, hfun s ∈ B)
    (ρ : Path ptBot ptTop) (hρbox : Set.range ρ ⊆ closedBox) (hρav : ∀ t, ρ t ∉ B) : False := by
  set vfun : ℝ → ℂ := fun s => ρ.extend ((s + 1) / 2) with hvfundef
  have hfv : Continuous vfun := by rw [hvfundef]; fun_prop
  have hfbox : ∀ s ∈ Set.Icc (-1:ℝ) 1, |(hfun s).re| ≤ 1 ∧ |(hfun s).im| ≤ 2 := by
    intro s hs
    have hmem : hfun s ∈ B := hhmem s hs
    have h := range_subset_closedBox hsub (hBsub hmem)
    rwa [closedBox] at h
  have hvbox : ∀ s ∈ Set.Icc (-1:ℝ) 1, |(vfun s).re| ≤ 1 ∧ |(vfun s).im| ≤ 2 := by
    intro s hs
    have hs' : (s + 1) / 2 ∈ Set.Icc (0:ℝ) 1 := ⟨by linarith [hs.1], by linarith [hs.2]⟩
    have hmem : vfun s ∈ Set.range ρ := by
      rw [hvfundef]
      exact ⟨⟨(s+1)/2, hs'⟩, (Path.extend_apply ρ hs').symm⟩
    have h := hρbox hmem
    rwa [closedBox] at h
  have hfleft : (hfun (-1)).re = -1 := by rw [hhneg]; norm_num
  have hfright : (hfun 1).re = 1 := by rw [hhpos]; norm_num
  have hvbot : (vfun (-1)).im = -2 := by
    have h1 : (((-1:ℝ) + 1) / 2) = 0 := by norm_num
    have h : vfun (-1) = ptBot := by
      show ρ.extend (((-1:ℝ) + 1) / 2) = ptBot
      rw [h1, Path.extend_zero]
    rw [h]; norm_num
  have hvtop : (vfun 1).im = 2 := by
    have h1 : (((1:ℝ) + 1) / 2) = 1 := by norm_num
    have h : vfun 1 = ptTop := by
      show ρ.extend (((1:ℝ) + 1) / 2) = ptTop
      rw [h1, Path.extend_one]
    rw [h]; norm_num
  obtain ⟨s, hs, t, ht, heq⟩ := crossing_rect hfh hfv hfbox hvbox hfleft hfright hvbot hvtop
  have hmemB : hfun s ∈ B := hhmem s hs
  rw [heq] at hmemB
  have ht' : (t + 1) / 2 ∈ Set.Icc (0:ℝ) 1 := ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have hv : vfun t = ρ ⟨(t+1)/2, ht'⟩ := by rw [hvfundef]; exact Path.extend_apply ρ ht'
  rw [hv] at hmemB
  exact hρav _ hmemB

/-- The two arcs into which `-1` and `1` divide the trace, and their elementary properties. -/
theorem exists_arc_decomposition {γ : ℝ → ℂ} (hper : Function.Periodic γ (2 * Real.pi))
    (hinj : Set.InjOn γ (Set.Ico 0 (2 * Real.pi))) (hzero : γ 0 = -1) (hpos : 1 ∈ Set.range γ) :
    ∃ θ : ℝ, 0 < θ ∧ θ < 2 * Real.pi ∧ γ θ = 1 ∧ γ (2 * Real.pi) = -1 ∧
      γ '' Set.Icc 0 θ ∪ γ '' Set.Icc θ (2 * Real.pi) = Set.range γ ∧
      γ '' Set.Icc 0 θ ∩ γ '' Set.Icc θ (2 * Real.pi) = ({-1, 1} : Set ℂ) := by
  have hπ : (0 : ℝ) < 2 * Real.pi := by positivity
  obtain ⟨t₁, ht₁⟩ := hpos
  obtain ⟨n₀, hn₀⟩ := exists_int_mul_add_mem_Ico hπ 0 t₁
  set θ : ℝ := t₁ + (n₀ : ℝ) * (2 * Real.pi) with hθdef
  have hγθ : γ θ = 1 := by rw [hθdef]; exact ((hper.int_mul n₀) t₁).trans ht₁
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
  refine ⟨θ, hθpos, hθlt, hγθ, hγ2π, ?_, ?_⟩
  · have hIcc_union : Set.Icc (0:ℝ) θ ∪ Set.Icc θ (2 * Real.pi) = Set.Icc 0 (2 * Real.pi) := by
      ext t; constructor
      · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
        · exact ⟨h1, le_trans h2 hθlt.le⟩
        · exact ⟨le_trans hθpos.le h1, h2⟩
      · rintro ⟨h1, h2⟩
        rcases le_or_gt t θ with h | h
        · exact Or.inl ⟨h1, h⟩
        · exact Or.inr ⟨le_of_lt h, h2⟩
    rw [← Set.image_union, hIcc_union, range_eq_image_Icc hper]
  · refine Subset.antisymm ?_ ?_
    · have hsub := image_Icc_inter_image_Icc_subset hper hinj hθpos hθlt
      simpa [hzero, hγθ] using hsub
    · intro w hw
      rcases hw with rfl | rfl
      · exact ⟨⟨0, ⟨le_refl 0, hθpos.le⟩, hzero⟩,
          ⟨2 * Real.pi, ⟨hθlt.le, le_refl _⟩, hγ2π⟩⟩
      · exact ⟨⟨θ, ⟨hθpos.le, le_refl _⟩, hγθ⟩, ⟨θ, ⟨le_refl _, hθlt.le⟩, hγθ⟩⟩

/-- Two interior points of an arc of the trace are joined by a path inside the arc avoiding the
two endpoints. -/
theorem path_in_arc {γ : ℝ → ℂ} (hγ : Continuous γ) {c d : ℝ} (hcd : c ≤ d)
    (hinj : Set.InjOn γ (Set.Icc c d)) {p q : ℂ}
    (hp : p ∈ γ '' Set.Icc c d) (hq : q ∈ γ '' Set.Icc c d)
    (hp1 : p ≠ γ c) (hp2 : p ≠ γ d) (hq1 : q ≠ γ c) (hq2 : q ≠ γ d) :
    ∃ ρ : Path p q, Set.range ρ ⊆ γ '' Set.Icc c d ∧ ∀ t, ρ t ≠ γ c ∧ ρ t ≠ γ d := by
  obtain ⟨up, hup, hupq⟩ := hp
  obtain ⟨uq, huq, huqq⟩ := hq
  have hupne1 : up ≠ c := fun h => hp1 (by rw [← hupq, h])
  have hupne2 : up ≠ d := fun h => hp2 (by rw [← hupq, h])
  have huqne1 : uq ≠ c := fun h => hq1 (by rw [← huqq, h])
  have huqne2 : uq ≠ d := fun h => hq2 (by rw [← huqq, h])
  have hupIoo : up ∈ Set.Ioo c d := ⟨lt_of_le_of_ne hup.1 (Ne.symm hupne1),
    lt_of_le_of_ne hup.2 hupne2⟩
  have huqIoo : uq ∈ Set.Ioo c d := ⟨lt_of_le_of_ne huq.1 (Ne.symm huqne1),
    lt_of_le_of_ne huq.2 huqne2⟩
  have hparam : ∀ t : unitInterval, up + (t:ℝ) * (uq - up) ∈ Set.Ioo c d := by
    intro t
    have h1 : (0:ℝ) ≤ (t:ℝ) := t.2.1
    have h2 : (t:ℝ) ≤ 1 := t.2.2
    refine ⟨?_, ?_⟩
    · rcases le_or_gt up uq with h | h
      · have := mul_nonneg h1 (by linarith : (0:ℝ) ≤ uq - up); nlinarith [hupIoo.1]
      · have := mul_le_mul_of_nonneg_right h2 (by linarith : (0:ℝ) ≤ up - uq)
        nlinarith [huqIoo.1]
    · rcases le_or_gt up uq with h | h
      · have := mul_le_mul_of_nonneg_left h2 (by linarith : (0:ℝ) ≤ uq - up)
        nlinarith [huqIoo.2]
      · have := mul_nonpos_of_nonneg_of_nonpos h1 (by linarith : uq - up ≤ 0)
        nlinarith [hupIoo.2]
  refine ⟨⟨⟨fun t : unitInterval => γ (up + (t:ℝ) * (uq - up)), hγ.comp (by fun_prop)⟩, ?_, ?_⟩,
    ?_, ?_⟩
  · show γ (up + ((0:unitInterval):ℝ) * (uq - up)) = p
    rw [show ((0:unitInterval):ℝ) = 0 from rfl, zero_mul, add_zero]; exact hupq
  · show γ (up + ((1:unitInterval):ℝ) * (uq - up)) = q
    rw [show ((1:unitInterval):ℝ) = 1 from rfl, one_mul]
    rw [show up + (uq - up) = uq by ring]; exact huqq
  · rintro y ⟨t, rfl⟩
    exact ⟨_, ⟨(hparam t).1.le, (hparam t).2.le⟩, rfl⟩
  · intro t
    constructor
    · intro hcon
      have hmem : up + (t:ℝ) * (uq - up) ∈ Set.Icc c d := ⟨(hparam t).1.le, (hparam t).2.le⟩
      exact absurd (hinj hmem ⟨le_refl c, hcd⟩ hcon) (ne_of_gt (hparam t).1)
    · intro hcon
      have hmem : up + (t:ℝ) * (uq - up) ∈ Set.Icc c d := ⟨(hparam t).1.le, (hparam t).2.le⟩
      exact absurd (hinj hmem ⟨hcd, le_refl d⟩ hcon) (ne_of_lt (hparam t).2)

/-- If `j` is a point of the free ray below and `l` the topmost point of the trace on the vertical
segment, then `j` does not lie on the arc of the trace through `l`. -/
theorem not_mem_arc_of_windowConfig {γ : ℝ → ℂ} (hγ : Continuous γ)
    (hper : Function.Periodic γ (2 * Real.pi)) (hinj : Set.InjOn γ (Set.Ico 0 (2 * Real.pi)))
    (hsub : ∀ w ∈ Set.range γ, w ∈ rectR ∨ w = -1 ∨ w = 1)
    {A B : Set ℂ} (hAB : A ∪ B = Set.range γ) (hABi : A ∩ B = ({-1, 1} : Set ℂ))
    {l j : ℂ} (hlA : l ∈ A) (hlSeg : l ∈ vSeg) (hl2 : l.im < 2) (hjSeg : j ∈ vSeg)
    (hj2 : -2 < j.im)
    (hjfree : ∀ z ∈ vSeg, z.im < j.im → z ∉ Set.range γ)
    (hlfree : ∀ z ∈ vSeg, l.im < z.im → z ∉ Set.range γ)
    {c d : ℝ} (hcd : c ≤ d) (hcdlt : d - c < 2 * Real.pi)
    (hAeq : A = γ '' Set.Icc c d)
    (hend : (γ c = -1 ∧ γ d = 1) ∨ (γ c = 1 ∧ γ d = -1))
    {c' d' : ℝ} (hBeq : B = γ '' Set.Icc (min c' d') (max c' d'))
    (hγc' : γ c' = -1) (hγd' : γ d' = 1) :
    j ∉ A := by
  intro hjA
  have hBsub : B ⊆ Set.range γ := by rw [← hAB]; exact Set.subset_union_right
  have hAsub : A ⊆ Set.range γ := by rw [← hAB]; exact Set.subset_union_left
  have hinjcd : Set.InjOn γ (Set.Icc c d) := injOn_Icc_of_injOn_Ico hper hinj hcdlt
  have hjne1 : j ≠ γ c := fun h => by
    have hh : j.re = 0 := hjSeg.1
    rcases hend with ⟨h1, _⟩ | ⟨h1, _⟩ <;> rw [h, h1] at hh <;> norm_num at hh
  have hjne2 : j ≠ γ d := fun h => by
    have hh : j.re = 0 := hjSeg.1
    rcases hend with ⟨_, h2⟩ | ⟨_, h2⟩ <;> rw [h, h2] at hh <;> norm_num at hh
  have hlne1 : l ≠ γ c := fun h => by
    have hh : l.re = 0 := hlSeg.1
    rcases hend with ⟨h1, _⟩ | ⟨h1, _⟩ <;> rw [h, h1] at hh <;> norm_num at hh
  have hlne2 : l ≠ γ d := fun h => by
    have hh : l.re = 0 := hlSeg.1
    rcases hend with ⟨_, h2⟩ | ⟨_, h2⟩ <;> rw [h, h2] at hh <;> norm_num at hh
  have hjB : j ∉ B := fun hcon => by
    have hmem : j ∈ ({-1, 1} : Set ℂ) := hABi ▸ (show j ∈ A ∩ B from ⟨hjA, hcon⟩)
    rcases hmem with h | h
    · rw [h] at hjSeg; exact absurd hjSeg.1 (by norm_num)
    · rw [h] at hjSeg; exact absurd hjSeg.1 (by norm_num)
  have hlB : l ∉ B := fun hcon => by
    have hmem : l ∈ ({-1, 1} : Set ℂ) := hABi ▸ (show l ∈ A ∩ B from ⟨hlA, hcon⟩)
    rcases hmem with h | h
    · rw [h] at hlSeg; exact absurd hlSeg.1 (by norm_num)
    · rw [h] at hlSeg; exact absurd hlSeg.1 (by norm_num)
  obtain ⟨ρ₁, hρ₁range, hρ₁av⟩ := path_in_arc hγ hcd hinjcd
    (hAeq ▸ hjA) (hAeq ▸ hlA) hjne1 hjne2 hlne1 hlne2
  have hsegB_im : ∀ t : unitInterval,
      ((Path.segment ptBot j) t).im = (1 - (t:ℝ)) * (-2) + (t:ℝ) * j.im := by
    intro t; rw [Work.Smooth.SphereJordan.segment_im, ptBot_im]
  have hsegB_re : ∀ t : unitInterval, ((Path.segment ptBot j) t).re = 0 := by
    intro t; rw [Work.Smooth.SphereJordan.segment_re, ptBot_re, hjSeg.1]; ring
  have hsegB_av : ∀ t : unitInterval, (Path.segment ptBot j) t ∉ B := by
    intro t htB
    by_cases ht : (t:ℝ) = 1
    · have he : (Path.segment ptBot j) t = j := by
        rw [Work.Smooth.SphereJordan.segment_formula, ht]; simp
      exact hjB (he ▸ htB)
    · have ht1 : (t:ℝ) < 1 := lt_of_le_of_ne t.2.2 ht
      have h1 : (0:ℝ) < 1 - (t:ℝ) := by linarith
      have him : ((Path.segment ptBot j) t).im < j.im := by
        rw [hsegB_im t]
        nlinarith [mul_neg_of_pos_of_neg h1 (by linarith [hj2] : -2 - j.im < 0)]
      have hmem : (Path.segment ptBot j) t ∈ vSeg := by
        refine ⟨hsegB_re t, ?_, ?_⟩
        · rw [hsegB_im t]
          nlinarith [mul_nonneg t.2.1 (by linarith [hj2] : (0:ℝ) ≤ j.im + 2)]
        · rw [hsegB_im t]
          have h3 := mul_le_mul_of_nonneg_right (t.2.2 : (t:ℝ) ≤ 1)
            (by linarith [hj2] : (0:ℝ) ≤ j.im + 2)
          nlinarith [hjSeg.2.2]
      exact hjfree _ hmem him (hBsub htB)
  have hsegT_im : ∀ t : unitInterval,
      ((Path.segment l ptTop) t).im = (1 - (t:ℝ)) * l.im + (t:ℝ) * 2 := by
    intro t; rw [Work.Smooth.SphereJordan.segment_im, ptTop_im]
  have hsegT_re : ∀ t : unitInterval, ((Path.segment l ptTop) t).re = 0 := by
    intro t; rw [Work.Smooth.SphereJordan.segment_re, hlSeg.1, ptTop_re]; ring
  have hsegT_av : ∀ t : unitInterval, (Path.segment l ptTop) t ∉ B := by
    intro t htB
    by_cases ht : (t:ℝ) = 0
    · have he : (Path.segment l ptTop) t = l := by
        rw [Work.Smooth.SphereJordan.segment_formula, ht]; simp
      exact hlB (he ▸ htB)
    · have ht0 : 0 < (t:ℝ) := lt_of_le_of_ne t.2.1 (Ne.symm ht)
      have hpos : (0:ℝ) < 2 - l.im := by linarith [hl2]
      have him : l.im < ((Path.segment l ptTop) t).im := by
        rw [hsegT_im t]
        nlinarith [mul_pos ht0 hpos]
      have hmem : (Path.segment l ptTop) t ∈ vSeg := by
        refine ⟨hsegT_re t, ?_, ?_⟩
        · rw [hsegT_im t]
          nlinarith [mul_nonneg (by linarith [t.2.2] : (0:ℝ) ≤ 1 - (t:ℝ))
            (by linarith [hlSeg.2.1] : (0:ℝ) ≤ l.im + 2)]
        · rw [hsegT_im t]
          have h3 := mul_le_mul_of_nonneg_right (t.2.2 : (t:ℝ) ≤ 1) (le_of_lt hpos)
          nlinarith [hl2]
      exact hlfree _ hmem him (hBsub htB)
  have hρ₁avB : ∀ t : unitInterval, ρ₁ t ∉ B := by
    intro t htB
    have hmem : ρ₁ t ∈ ({-1, 1} : Set ℂ) := hABi ▸ ⟨hAeq ▸ hρ₁range ⟨t, rfl⟩, htB⟩
    rcases hend with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rcases hmem with h | h
      · exact (hρ₁av t).1 (h.trans h1.symm)
      · exact (hρ₁av t).2 (h.trans h2.symm)
    · rcases hmem with h | h
      · exact (hρ₁av t).2 (h.trans h2.symm)
      · exact (hρ₁av t).1 (h.trans h1.symm)
  set ρ : Path ptBot ptTop :=
    (Path.segment ptBot j).trans (ρ₁.trans (Path.segment l ptTop)) with hρdef
  have hρav : ∀ t : unitInterval, ρ t ∉ B := by
    intro t
    rw [hρdef]
    refine Work.Smooth.SphereJordan.trans_mem (S := (B : Set ℂ)ᶜ) _ _ hsegB_av ?_ t
    exact Work.Smooth.SphereJordan.trans_mem (S := (B : Set ℂ)ᶜ) _ _ hρ₁avB hsegT_av
  have hρbox : Set.range ρ ⊆ closedBox := by
    intro y hy
    obtain ⟨t, rfl⟩ := hy
    rw [hρdef]
    refine Work.Smooth.SphereJordan.trans_mem (S := closedBox) _ _ ?_ ?_ t
    · intro s
      exact Work.Smooth.SphereJordan.vSeg_subset_closedBox
        (Work.Smooth.SphereJordan.segment_mem_vSeg ptBot_mem_vSeg hjSeg s)
    · refine Work.Smooth.SphereJordan.trans_mem (S := closedBox) _ _ ?_ ?_
      · intro s; exact range_subset_closedBox hsub (hAsub (hAeq ▸ hρ₁range ⟨s, rfl⟩))
      · intro s
        exact Work.Smooth.SphereJordan.vSeg_subset_closedBox
          (Work.Smooth.SphereJordan.segment_mem_vSeg hlSeg ptTop_mem_vSeg s)
  exact false_of_path_avoiding_arc hγ hsub hBsub (arcParam_cont hγ c' d')
    (arcParam_neg hγc') (arcParam_pos hγd')
    (fun s hs => hBeq.symm ▸ arcParam_mem_minmax c' d' s hs) ρ hρbox hρav

/-! ## The main theorem -/

theorem range_path_symm {x y : ℂ} (ρ : Path x y) : Set.range ρ.symm = Set.range ρ := by
  ext z; constructor
  · rintro ⟨t, ht⟩
    refine ⟨unitInterval.symm t, ?_⟩
    rw [← ht, Path.symm_apply]
    simp
  · rintro ⟨t, ht⟩
    refine ⟨unitInterval.symm t, ?_⟩
    rw [Path.symm_apply]
    simp only [Function.comp_apply, unitInterval.symm_symm]
    exact ht

theorem exists_bounded_component_of_rectSetup {γ : ℝ → ℂ} (hγ : Continuous γ)
    (hper : Function.Periodic γ (2 * Real.pi))
    (hinj : Set.InjOn γ (Set.Ico 0 (2 * Real.pi)))
    (hsub : ∀ w ∈ Set.range γ, w ∈ Work.Topology.PlaneCurve.rectR ∨ w = -1 ∨ w = 1)
    (hzero : γ 0 = -1) (hpos : 1 ∈ Set.range γ) :
    ∃ z : ℂ, z.re = 0 ∧ z ∉ Set.range γ ∧
      Bornology.IsBounded (connectedComponentIn (Set.range γ)ᶜ z) := by
  classical
  obtain ⟨l, m, k, j, δ₁, δ₂, hlJ, hmJ, hkJ, hjJ, hlSeg, hmSeg, hkSeg, hjSeg,
    hj2, hjk, hkm, hml, hl2, hwin, hjfree, hlfree, hδ₁J, hδ₁av, hδ₂J, hδ₂av⟩ :=
    Work.Smooth.SphereJordan.exists_windowConfig hγ hper hinj hsub hzero hpos
  obtain ⟨θ, hθ0, hθ2, hγθ, hγ2π, hAB, hABi⟩ := exists_arc_decomposition hper hinj hzero hpos
  have hJclosed : IsClosed (Set.range γ) := (isCompact_range_of_periodic hγ hper).isClosed
  have hUopen : IsOpen (Set.range γ)ᶜ := hJclosed.isOpen_compl
  set J₁ : Set ℂ := if l ∈ γ '' Set.Icc 0 θ then γ '' Set.Icc 0 θ
    else γ '' Set.Icc θ (2 * Real.pi) with hJ₁def
  set J₂ : Set ℂ := if l ∈ γ '' Set.Icc 0 θ then γ '' Set.Icc θ (2 * Real.pi)
    else γ '' Set.Icc 0 θ with hJ₂def
  have hlJ₁ : l ∈ J₁ := by
    rw [hJ₁def]; split_ifs with h
    · exact h
    · rcases (show l ∈ γ '' Set.Icc 0 θ ∪ γ '' Set.Icc θ (2 * Real.pi) from by
        rw [hAB]; exact hlJ) with h' | h'
      · exact absurd h' h
      · exact h'
  have hJ₁J₂ : J₁ ∪ J₂ = Set.range γ := by
    by_cases h : l ∈ γ '' Set.Icc 0 θ
    · rw [hJ₁def, hJ₂def, if_pos h, if_pos h]; exact hAB
    · rw [hJ₁def, hJ₂def, if_neg h, if_neg h, Set.union_comm]; exact hAB
  have hJ₁inter : J₁ ∩ J₂ = ({-1, 1} : Set ℂ) := by
    by_cases h : l ∈ γ '' Set.Icc 0 θ
    · rw [hJ₁def, hJ₂def, if_pos h, if_pos h]; exact hABi
    · rw [hJ₁def, hJ₂def, if_neg h, if_neg h, Set.inter_comm]; exact hABi
  have hJ₁sub : J₁ ⊆ Set.range γ := by rw [← hJ₁J₂]; exact Set.subset_union_left
  have hJ₂sub : J₂ ⊆ Set.range γ := by rw [← hJ₁J₂]; exact Set.subset_union_right
  have hlne1 : l ≠ -1 := fun h => by
    have hh := hlSeg.1; rw [h] at hh; norm_num at hh
  have hlne2 : l ≠ 1 := fun h => by
    have hh := hlSeg.1; rw [h] at hh; norm_num at hh
  have hlJ₂ : l ∉ J₂ := fun hcon => by
    have hmem : l ∈ ({-1, 1} : Set ℂ) := hJ₁inter ▸ (show l ∈ J₁ ∩ J₂ from ⟨hlJ₁, hcon⟩)
    rcases hmem with h | h
    · exact hlne1 h
    · exact hlne2 h
  have hδ₁J₁ : ∀ t : unitInterval, δ₁ t ∈ J₁ := by
    have hconn : IsConnected (Set.range δ₁) := isConnected_range δ₁.continuous
    have hrange : Set.range δ₁ ⊆ Set.range γ := fun y hy => by
      obtain ⟨t, rfl⟩ := hy; exact hδ₁J t
    have h0 : γ 0 ∉ Set.range δ₁ := fun ⟨t, ht⟩ => (hδ₁av t).1 (by rw [ht, hzero])
    have hθ : γ θ ∉ Set.range δ₁ := fun ⟨t, ht⟩ => (hδ₁av t).2 (by rw [ht, hγθ])
    rcases isConnected_subset_arc_of_avoid hγ hper hinj hθ0 hθ2 hconn hrange h0 hθ with hAc | hBc
    · have hlAr : l ∈ γ '' Set.Icc 0 θ := hAc ⟨1, Path.target δ₁⟩
      intro t
      rw [hJ₁def, if_pos hlAr]
      exact hAc ⟨t, rfl⟩
    · have hlBr : l ∈ γ '' Set.Icc θ (2 * Real.pi) := hBc ⟨1, Path.target δ₁⟩
      have hnotA : ¬ (l ∈ γ '' Set.Icc 0 θ) := fun hcon => by
        have hmem : l ∈ ({-1, 1} : Set ℂ) :=
          hABi ▸ (show l ∈ γ '' Set.Icc 0 θ ∩ γ '' Set.Icc θ (2 * Real.pi) from ⟨hcon, hlBr⟩)
        rcases hmem with h | h
        · exact hlne1 h
        · exact hlne2 h
      intro t
      rw [hJ₁def, if_neg hnotA]
      exact hBc ⟨t, rfl⟩
  have hmJ₁ : m ∈ J₁ := by
    have h := hδ₁J₁ (0 : unitInterval)
    rwa [Path.source δ₁] at h
  have hmJ₂ : m ∉ J₂ := fun hcon => by
    have hmem : m ∈ ({-1, 1} : Set ℂ) := hJ₁inter ▸ (show m ∈ J₁ ∩ J₂ from ⟨hmJ₁, hcon⟩)
    rcases hmem with h | h
    · rw [h] at hmSeg; exact absurd hmSeg.1 (by norm_num)
    · rw [h] at hmSeg; exact absurd hmSeg.1 (by norm_num)
  have hJ₁arc : ∃ c d : ℝ, max c d - min c d < 2 * Real.pi ∧
      J₁ = γ '' Set.Icc (min c d) (max c d) ∧ γ c = -1 ∧ γ d = 1 := by
    by_cases h : l ∈ γ '' Set.Icc 0 θ
    · exact ⟨0, θ, by simp only [min_eq_left hθ0.le, max_eq_right hθ0.le]; linarith,
        by rw [hJ₁def, if_pos h]; simp only [min_eq_left hθ0.le, max_eq_right hθ0.le],
        hzero, hγθ⟩
    · exact ⟨2 * Real.pi, θ, by rw [min_eq_right hθ2.le, max_eq_left hθ2.le]; linarith,
        by rw [hJ₁def, if_neg h]; rw [min_eq_right hθ2.le, max_eq_left hθ2.le],
        hγ2π, hγθ⟩
  have hJ₂arc : ∃ c d : ℝ, max c d - min c d < 2 * Real.pi ∧
      J₂ = γ '' Set.Icc (min c d) (max c d) ∧ γ c = -1 ∧ γ d = 1 := by
    by_cases h : l ∈ γ '' Set.Icc 0 θ
    · refine ⟨2 * Real.pi, θ, ?_, ?_, hγ2π, hγθ⟩
      · rw [min_eq_right hθ2.le, max_eq_left hθ2.le]; linarith
      · rw [hJ₂def, if_pos h, min_eq_right hθ2.le, max_eq_left hθ2.le]
    · refine ⟨0, θ, ?_, ?_, hzero, hγθ⟩
      · rw [min_eq_left hθ0.le, max_eq_right hθ0.le]; linarith
      · rw [hJ₂def, if_neg h, min_eq_left hθ0.le, max_eq_right hθ0.le]
  have hj_not_J₁ : j ∉ J₁ := by
    obtain ⟨c, d, hcdlt, hJ₁eq, hγc, hγd⟩ := hJ₁arc
    have hend : (γ (min c d) = -1 ∧ γ (max c d) = 1) ∨
        (γ (min c d) = 1 ∧ γ (max c d) = -1) := by
      rcases le_total c d with h | h
      · left; rw [min_eq_left h, max_eq_right h]; exact ⟨hγc, hγd⟩
      · right; rw [min_eq_right h, max_eq_left h]; exact ⟨hγd, hγc⟩
    obtain ⟨c', d', _, hJ₂eq, hγc', hγd'⟩ := hJ₂arc
    exact not_mem_arc_of_windowConfig hγ hper hinj hsub (A := J₁) (B := J₂) hJ₁J₂ hJ₁inter
      hlJ₁ hlSeg hl2 hjSeg hj2 hjfree hlfree min_le_max hcdlt hJ₁eq hend hJ₂eq hγc' hγd'
  have hδ₂J₂ : ∀ t : unitInterval, δ₂ t ∈ J₂ := by
    have hconn : IsConnected (Set.range δ₂) := isConnected_range δ₂.continuous
    have hrange : Set.range δ₂ ⊆ Set.range γ := fun y hy => by
      obtain ⟨t, rfl⟩ := hy; exact hδ₂J t
    have h0 : γ 0 ∉ Set.range δ₂ := fun ⟨t, ht⟩ => (hδ₂av t).1 (by rw [ht, hzero])
    have hθ : γ θ ∉ Set.range δ₂ := fun ⟨t, ht⟩ => (hδ₂av t).2 (by rw [ht, hγθ])
    rcases isConnected_subset_arc_of_avoid hγ hper hinj hθ0 hθ2 hconn hrange h0 hθ with hAc | hBc
    · have hjAr : j ∈ γ '' Set.Icc 0 θ := hAc ⟨1, Path.target δ₂⟩
      have hnotA : ¬ (l ∈ γ '' Set.Icc 0 θ) := fun hcon => by
        have hJ₁eqA : J₁ = γ '' Set.Icc 0 θ := by rw [hJ₁def, if_pos hcon]
        exact hj_not_J₁ (hJ₁eqA ▸ hjAr)
      intro t
      rw [hJ₂def, if_neg hnotA]
      exact hAc ⟨t, rfl⟩
    · have hjBr : j ∈ γ '' Set.Icc θ (2 * Real.pi) := hBc ⟨1, Path.target δ₂⟩
      have hlAr : l ∈ γ '' Set.Icc 0 θ := by
        by_contra hcon
        have hJ₁eqB : J₁ = γ '' Set.Icc θ (2 * Real.pi) := by rw [hJ₁def, if_neg hcon]
        exact hj_not_J₁ (hJ₁eqB ▸ hjBr)
      intro t
      rw [hJ₂def, if_pos hlAr]
      exact hBc ⟨t, rfl⟩
  have hkJ₂ : k ∈ J₂ := by
    have h := hδ₂J₂ (0 : unitInterval)
    rwa [Path.source δ₂] at h
  have hkJ₁ : k ∉ J₁ := fun hcon => by
    have hmem : k ∈ ({-1, 1} : Set ℂ) := hJ₁inter ▸ (show k ∈ J₁ ∩ J₂ from ⟨hcon, hkJ₂⟩)
    rcases hmem with h | h
    · rw [h] at hkSeg; exact absurd hkSeg.1 (by norm_num)
    · rw [h] at hkSeg; exact absurd hkSeg.1 (by norm_num)
  have hjJ₂ : j ∈ J₂ := by
    have h := hδ₂J₂ (1 : unitInterval)
    rwa [Path.target δ₂] at h
  -- the witness point
  set z : ℂ := ⟨0, (k.im + m.im) / 2⟩ with hzdef
  have hzre : z.re = 0 := rfl
  have hzim : z.im = (k.im + m.im) / 2 := rfl
  have hzk : k.im < z.im := by rw [hzim]; linarith
  have hzm : z.im < m.im := by rw [hzim]; linarith
  have hzmem : z ∈ vSeg := ⟨hzre, by rw [hzim]; linarith [hjk, hj2],
    by rw [hzim]; linarith [hml, hl2]⟩
  have hznot : z ∉ Set.range γ := fun hcon => hwin z hzmem hzk hzm hcon
  have hzrect : z ∈ rectR := by
    rw [rectR]
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [hzre]; norm_num
    · rw [hzre]; norm_num
    · rw [hzim]; linarith [hjk, hj2]
    · rw [hzim]; linarith [hml, hl2]
  refine ⟨z, hzre, hznot, ?_⟩
  have hboxball : closedBox ⊆ Metric.closedBall z 10 := by
    intro y hy
    rw [Metric.mem_closedBall, dist_eq_norm]
    have hy1 : |y.re| ≤ 1 := hy.1
    have hy2 : |y.im| ≤ 2 := hy.2
    have hz2 : |z.im| ≤ 2 := by
      rw [hzim, abs_le]; constructor <;> linarith [hjk, hml, hj2, hl2]
    have h1 : |(y - z).re| ≤ 1 := by rw [Complex.sub_re, hzre]; simpa using hy1
    have h2 : |(y - z).im| ≤ 4 := by
      rw [Complex.sub_im, hzim, abs_le]
      obtain ⟨hlo, hhi⟩ := abs_le.mp hy2
      obtain ⟨hlo', hhi'⟩ := abs_le.mp hz2
      constructor <;> linarith
    calc ‖y - z‖ ≤ |(y - z).re| + |(y - z).im| := Complex.norm_le_abs_re_add_abs_im _
      _ ≤ 1 + 4 := by linarith
      _ ≤ 10 := by norm_num
  refine (Metric.isBounded_closedBall (x := z) (r := 10)).subset ?_
  intro x hx
  by_contra hxout
  rw [Metric.mem_closedBall] at hxout
  push_neg at hxout
  have hxnotbox : x ∉ closedBox := fun hcon => absurd (hboxball hcon) (not_le.mpr hxout)
  obtain ⟨σ, hσ⟩ := Work.Smooth.JordanSeparation.joinedIn_of_mem_connectedComponentIn
    (U := (Set.range γ)ᶜ) hUopen hznot hx
  obtain ⟨w, σ₁, hwfront, hσ₁box, hσ₁range⟩ := exists_first_exit hzrect hxnotbox
  have hσcompl : Set.range σ ⊆ (Set.range γ)ᶜ := fun y hy => by
    obtain ⟨t, rfl⟩ := hy; exact hσ t
  have hσ₁compl : Set.range σ₁ ⊆ (Set.range γ)ᶜ := hσ₁range.trans hσcompl
  have hwnot : w ∉ Set.range γ := hσ₁compl ⟨1, Path.target σ₁⟩
  have hwfr := (mem_frontier_closedBox_iff w).mp hwfront
  have hwne1 : w ≠ -1 := fun h => hwnot (by rw [h]; exact ⟨0, hzero⟩)
  have hwne2 : w ≠ 1 := fun h => hwnot (by rw [h]; exact hpos)
  rcases le_or_gt (w.im) 0 with hwle | hwgt
  · -- Case A: w on the lower half of the boundary
    have hwlt : w.im < 0 := by
      rcases lt_or_eq_of_le hwle with h | h
      · exact h
      · exfalso
        have hwre : w.re = 1 ∨ w.re = -1 := by
          rcases hwfr.2.2 with h' | h'
          · have hle : |w.re| ≤ 1 := le_of_eq h'
            obtain ⟨hlo, hhi⟩ := abs_le.mp hle
            rcases eq_or_lt_of_le hhi with hh | hh
            · exact Or.inl hh
            · refine Or.inr ?_
              by_contra hne
              have h1 : -1 < w.re := lt_of_le_of_ne hlo (Ne.symm hne)
              have : |w.re| < 1 := abs_lt.mpr ⟨h1, hh⟩
              linarith
          · rw [h] at h'; norm_num at h'
        rcases hwre with hh | hh
        · exact hwne2 (Complex.ext (by rw [hh]; norm_num) (by rw [h]; norm_num))
        · exact hwne1 (Complex.ext (by rw [hh]; norm_num) (by rw [h]; norm_num))
    obtain ⟨exitBot, hexitFront, hexitneg, hexitne⟩ :=
      exists_path_frontier_closedBox_bot hwfront hwlt
    have hexitBot_c : ∀ t : unitInterval, exitBot t ∈ closedBox := by
      intro t
      have h := frontier_subset_closure (hexitFront ⟨t, rfl⟩)
      rwa [isClosed_closedBox.closure_eq] at h
    set ρ : Path ptTop ptBot :=
      (Path.segment ptTop l).trans (δ₁.symm.trans ((Path.segment m z).trans (σ₁.trans exitBot)))
      with hρdef
    have hρbox : Set.range ρ ⊆ closedBox := by
      intro y hy
      obtain ⟨t, rfl⟩ := hy
      rw [hρdef]
      refine Work.Smooth.SphereJordan.trans_mem (S := closedBox) _ _ ?_ ?_ t
      · intro s
        exact Work.Smooth.SphereJordan.vSeg_subset_closedBox
          (Work.Smooth.SphereJordan.segment_mem_vSeg ptTop_mem_vSeg hlSeg s)
      · refine Work.Smooth.SphereJordan.trans_mem (S := closedBox) _ _ ?_ ?_
        · intro s
          exact range_subset_closedBox hsub (hJ₁sub (hδ₁J₁ (unitInterval.symm s)))
        · refine Work.Smooth.SphereJordan.trans_mem (S := closedBox) _ _ ?_ ?_
          · intro s
            exact Work.Smooth.SphereJordan.vSeg_subset_closedBox
              (Work.Smooth.SphereJordan.segment_mem_vSeg hmSeg hzmem s)
          · refine Work.Smooth.SphereJordan.trans_mem (S := closedBox) _ _ ?_ ?_
            · intro s; exact hσ₁box ⟨s, rfl⟩
            · intro s; exact hexitBot_c s
    have hsegTop_av : ∀ t : unitInterval, (Path.segment ptTop l) t ∉ J₂ := by
      intro t htJ₂
      have hre : ((Path.segment ptTop l) t).re = 0 := by
        rw [Work.Smooth.SphereJordan.segment_re, ptTop_re, hlSeg.1]; ring
      have him : ((Path.segment ptTop l) t).im = (1 - (t:ℝ)) * 2 + (t:ℝ) * l.im := by
        rw [Work.Smooth.SphereJordan.segment_im, ptTop_im]
      by_cases ht : (t:ℝ) = 1
      · have he : (Path.segment ptTop l) t = l := by
          rw [Work.Smooth.SphereJordan.segment_formula, ht]; simp
        exact hlJ₂ (he ▸ htJ₂)
      · have ht1 : (t:ℝ) < 1 := lt_of_le_of_ne t.2.2 ht
        have h1 : (0:ℝ) < 1 - (t:ℝ) := by linarith
        have h2 : (0:ℝ) < 2 - l.im := by linarith [hl2]
        have hgt : l.im < ((Path.segment ptTop l) t).im := by
          rw [him]; nlinarith [mul_pos h1 h2]
        have hmem : (Path.segment ptTop l) t ∈ vSeg := by
          refine ⟨hre, ?_, ?_⟩
          · rw [him]
            nlinarith [mul_nonneg t.2.1 (by linarith [hlSeg.2.1] : (0:ℝ) ≤ l.im + 2)]
          · rw [him]
            have h3 : (t:ℝ) * (2 - l.im) ≤ 2 - l.im := by
              have hh := mul_le_mul_of_nonneg_right (t.2.2 : (t:ℝ) ≤ 1) (le_of_lt h2)
              rwa [one_mul] at hh
            have h4 : 0 ≤ (t:ℝ) * (2 - l.im) := mul_nonneg t.2.1 (le_of_lt h2)
            nlinarith [h3, h4]
        exact hlfree _ hmem hgt (hJ₂sub htJ₂)
    have hδ₁symm_av : ∀ t : unitInterval, δ₁.symm t ∉ J₂ := by
      intro t htJ₂
      have h1 : δ₁.symm t ∈ J₁ := hδ₁J₁ (unitInterval.symm t)
      have h2 : δ₁.symm t ∈ ({-1, 1} : Set ℂ) := hJ₁inter ▸ ⟨h1, htJ₂⟩
      rcases h2 with h | h
      · exact (hδ₁av (unitInterval.symm t)).1 (by rw [Path.symm_apply] at h; exact h)
      · exact (hδ₁av (unitInterval.symm t)).2 (by rw [Path.symm_apply] at h; exact h)
    have hsegBot_av : ∀ t : unitInterval, (Path.segment m z) t ∉ J₂ := by
      intro t htJ₂
      have hre : ((Path.segment m z) t).re = 0 := by
        rw [Work.Smooth.SphereJordan.segment_re, hmSeg.1, hzre]; ring
      have him : ((Path.segment m z) t).im = (1 - (t:ℝ)) * m.im + (t:ℝ) * z.im := by
        rw [Work.Smooth.SphereJordan.segment_im]
      by_cases ht : (t:ℝ) = 0
      · have he : (Path.segment m z) t = m := by
          rw [Work.Smooth.SphereJordan.segment_formula, ht]; simp
        exact hmJ₂ (he ▸ htJ₂)
      · have ht0 : 0 < (t:ℝ) := lt_of_le_of_ne t.2.1 (Ne.symm ht)
        have hlt : ((Path.segment m z) t).im < m.im := by
          rw [him]; nlinarith [mul_neg_of_pos_of_neg ht0 (by linarith [hzm] : z.im - m.im < 0)]
        have hgt : k.im < ((Path.segment m z) t).im := by
          rw [him]
          have h3 := mul_le_mul_of_nonneg_right (t.2.2 : (t:ℝ) ≤ 1)
            (by linarith [hzm] : (0:ℝ) ≤ m.im - z.im)
          nlinarith [hzk]
        have hmem : (Path.segment m z) t ∈ vSeg := by
          refine ⟨hre, ?_, ?_⟩
          · rw [him]; linarith [hj2, hjk, hzk]
          · rw [him]; linarith [hl2, hml, hzm]
        exact hwin _ hmem hgt hlt (hJ₂sub htJ₂)
    have hσ₁_av : ∀ t : unitInterval, σ₁ t ∉ J₂ := fun t hcon =>
      hσ₁compl ⟨t, rfl⟩ (hJ₂sub hcon)
    have hexitBot_av : ∀ t : unitInterval, exitBot t ∉ J₂ := by
      intro t htJ₂
      have hrange : exitBot t ∈ Set.range γ := hJ₂sub htJ₂
      have hmem := range_inter_frontier_closedBox_subset hsub
        ⟨hrange, hexitFront ⟨t, rfl⟩⟩
      have hneg := hexitneg t
      rcases hmem with h | h
      · rw [h] at hneg; norm_num at hneg
      · rw [h] at hneg; norm_num at hneg
    have htail : ∀ t : unitInterval,
        (δ₁.symm.trans ((Path.segment m z).trans (σ₁.trans exitBot))) t ∈ (J₂ : Set ℂ)ᶜ := by
      intro t
      refine Work.Smooth.SphereJordan.trans_mem (S := (J₂ : Set ℂ)ᶜ) _ _ hδ₁symm_av ?_ t
      exact Work.Smooth.SphereJordan.trans_mem (S := (J₂ : Set ℂ)ᶜ) _ _ hsegBot_av
        (Work.Smooth.SphereJordan.trans_mem (S := (J₂ : Set ℂ)ᶜ) _ _ hσ₁_av hexitBot_av)
    have hρav : ∀ t : unitInterval, ρ.symm t ∉ J₂ := by
      intro t
      rw [Path.symm_apply, hρdef]
      exact Work.Smooth.SphereJordan.trans_mem (S := (J₂ : Set ℂ)ᶜ) _ _ hsegTop_av htail
        (unitInterval.symm t)
    have hρbox' : Set.range ρ.symm ⊆ closedBox := by
      rw [range_path_symm]; exact hρbox
    obtain ⟨c', d', _, hJ₂eq, hγc', hγd'⟩ := hJ₂arc
    exact false_of_path_avoiding_arc hγ hsub hJ₂sub (arcParam_cont hγ c' d')
      (arcParam_neg hγc') (arcParam_pos hγd')
      (fun s hs => hJ₂eq.symm ▸ arcParam_mem_minmax c' d' s hs) ρ.symm hρbox' hρav
  · -- Case B: w on the upper half of the boundary
    obtain ⟨exitTop, hexitFront, hexitpos, hexitne⟩ :=
      exists_path_frontier_closedBox_top hwfront hwgt
    have hexitTop_c : ∀ t : unitInterval, exitTop t ∈ closedBox := by
      intro t
      have h := frontier_subset_closure (hexitFront ⟨t, rfl⟩)
      rwa [isClosed_closedBox.closure_eq] at h
    set ρ : Path ptBot ptTop :=
      (Path.segment ptBot j).trans (δ₂.symm.trans ((Path.segment k z).trans (σ₁.trans exitTop)))
      with hρdef
    have hρbox : Set.range ρ ⊆ closedBox := by
      intro y hy
      obtain ⟨t, rfl⟩ := hy
      rw [hρdef]
      refine Work.Smooth.SphereJordan.trans_mem (S := closedBox) _ _ ?_ ?_ t
      · intro s
        exact Work.Smooth.SphereJordan.vSeg_subset_closedBox
          (Work.Smooth.SphereJordan.segment_mem_vSeg ptBot_mem_vSeg hjSeg s)
      · refine Work.Smooth.SphereJordan.trans_mem (S := closedBox) _ _ ?_ ?_
        · intro s
          exact range_subset_closedBox hsub (hJ₂sub (hδ₂J₂ (unitInterval.symm s)))
        · refine Work.Smooth.SphereJordan.trans_mem (S := closedBox) _ _ ?_ ?_
          · intro s
            exact Work.Smooth.SphereJordan.vSeg_subset_closedBox
              (Work.Smooth.SphereJordan.segment_mem_vSeg hkSeg hzmem s)
          · refine Work.Smooth.SphereJordan.trans_mem (S := closedBox) _ _ ?_ ?_
            · intro s; exact hσ₁box ⟨s, rfl⟩
            · intro s; exact hexitTop_c s
    have hsegBot_av : ∀ t : unitInterval, (Path.segment ptBot j) t ∉ J₁ := by
      intro t htJ₁
      have hre : ((Path.segment ptBot j) t).re = 0 := by
        rw [Work.Smooth.SphereJordan.segment_re, ptBot_re, hjSeg.1]; ring
      have him : ((Path.segment ptBot j) t).im = (1 - (t:ℝ)) * (-2) + (t:ℝ) * j.im := by
        rw [Work.Smooth.SphereJordan.segment_im, ptBot_im]
      by_cases ht : (t:ℝ) = 1
      · have he : (Path.segment ptBot j) t = j := by
          rw [Work.Smooth.SphereJordan.segment_formula, ht]; simp
        exact hj_not_J₁ (he ▸ htJ₁)
      · have ht1 : (t:ℝ) < 1 := lt_of_le_of_ne t.2.2 ht
        have h1 : (0:ℝ) < 1 - (t:ℝ) := by linarith
        have hlt : ((Path.segment ptBot j) t).im < j.im := by
          rw [him]
          nlinarith [mul_neg_of_pos_of_neg h1 (by linarith [hj2] : -2 - j.im < 0)]
        have hmem : (Path.segment ptBot j) t ∈ vSeg := by
          refine ⟨hre, ?_, ?_⟩
          · rw [him]
            nlinarith [mul_nonneg t.2.1 (by linarith [hj2] : (0:ℝ) ≤ j.im + 2)]
          · rw [him]
            have h3 := mul_le_mul_of_nonneg_right (t.2.2 : (t:ℝ) ≤ 1)
              (by linarith [hj2] : (0:ℝ) ≤ j.im + 2)
            nlinarith [hjSeg.2.2]
        exact hjfree _ hmem hlt (hJ₁sub htJ₁)
    have hδ₂symm_av : ∀ t : unitInterval, δ₂.symm t ∉ J₁ := by
      intro t htJ₁
      have h1 : δ₂.symm t ∈ J₂ := hδ₂J₂ (unitInterval.symm t)
      have h2 : δ₂.symm t ∈ ({-1, 1} : Set ℂ) := hJ₁inter ▸ ⟨htJ₁, h1⟩
      rcases h2 with h | h
      · exact (hδ₂av (unitInterval.symm t)).1 (by rw [Path.symm_apply] at h; exact h)
      · exact (hδ₂av (unitInterval.symm t)).2 (by rw [Path.symm_apply] at h; exact h)
    have hsegKZ_av : ∀ t : unitInterval, (Path.segment k z) t ∉ J₁ := by
      intro t htJ₁
      have hre : ((Path.segment k z) t).re = 0 := by
        rw [Work.Smooth.SphereJordan.segment_re, hkSeg.1, hzre]; ring
      have him : ((Path.segment k z) t).im = (1 - (t:ℝ)) * k.im + (t:ℝ) * z.im := by
        rw [Work.Smooth.SphereJordan.segment_im]
      by_cases ht : (t:ℝ) = 0
      · have he : (Path.segment k z) t = k := by
          rw [Work.Smooth.SphereJordan.segment_formula, ht]; simp
        exact hkJ₁ (he ▸ htJ₁)
      · have ht0 : 0 < (t:ℝ) := lt_of_le_of_ne t.2.1 (Ne.symm ht)
        have hgt : k.im < ((Path.segment k z) t).im := by
          rw [him]; nlinarith [mul_pos ht0 (by linarith [hzk] : (0:ℝ) < z.im - k.im)]
        have hlt : ((Path.segment k z) t).im < m.im := by
          rw [him]
          have h3 := mul_le_mul_of_nonneg_right (t.2.2 : (t:ℝ) ≤ 1)
            (by linarith [hzk] : (0:ℝ) ≤ z.im - k.im)
          nlinarith [hzm]
        have hmem : (Path.segment k z) t ∈ vSeg := by
          refine ⟨hre, ?_, ?_⟩
          · rw [him]; linarith [hj2, hjk, hzk]
          · rw [him]; linarith [hl2, hml, hzm]
        exact hwin _ hmem hgt hlt (hJ₁sub htJ₁)
    have hσ₁_av : ∀ t : unitInterval, σ₁ t ∉ J₁ := fun t hcon =>
      hσ₁compl ⟨t, rfl⟩ (hJ₁sub hcon)
    have hexitTop_av : ∀ t : unitInterval, exitTop t ∉ J₁ := by
      intro t htJ₁
      have hrange : exitTop t ∈ Set.range γ := hJ₁sub htJ₁
      have hmem := range_inter_frontier_closedBox_subset hsub
        ⟨hrange, hexitFront ⟨t, rfl⟩⟩
      have hpos := hexitpos t
      rcases hmem with h | h
      · rw [h] at hpos; norm_num at hpos
      · rw [h] at hpos; norm_num at hpos
    have htail : ∀ t : unitInterval,
        (δ₂.symm.trans ((Path.segment k z).trans (σ₁.trans exitTop))) t ∈ (J₁ : Set ℂ)ᶜ := by
      intro t
      refine Work.Smooth.SphereJordan.trans_mem (S := (J₁ : Set ℂ)ᶜ) _ _ hδ₂symm_av ?_ t
      exact Work.Smooth.SphereJordan.trans_mem (S := (J₁ : Set ℂ)ᶜ) _ _ hsegKZ_av
        (Work.Smooth.SphereJordan.trans_mem (S := (J₁ : Set ℂ)ᶜ) _ _ hσ₁_av hexitTop_av)
    have hρav : ∀ t : unitInterval, ρ t ∉ J₁ := by
      intro t
      rw [hρdef]
      exact Work.Smooth.SphereJordan.trans_mem (S := (J₁ : Set ℂ)ᶜ) _ _ hsegBot_av htail t
    obtain ⟨c, d, _, hJ₁eq, hγc, hγd⟩ := hJ₁arc
    exact false_of_path_avoiding_arc hγ hsub hJ₁sub (arcParam_cont hγ c d)
      (arcParam_neg hγc) (arcParam_pos hγd)
      (fun s hs => hJ₁eq.symm ▸ arcParam_mem_minmax c d s hs) ρ hρbox hρav

end
end Work.Topology.PlaneCurve
