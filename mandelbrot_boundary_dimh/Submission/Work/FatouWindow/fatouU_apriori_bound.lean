import Mathlib
import Submission.Work.FatouWindow.fatouDerivSetup
import Submission.Work.FatouWindow.fatouU_compact_bound
import Submission.Work.FatouWindow.fatouU_deep_bound
import Submission.Work.FatouCH.fatouDerivEstimate

namespace Work.FatouWindow

open Work.FatouL1

open MandelDim Set Metric

noncomputable section

variable {b₁ b₂ : Option ℂ} {F : ℂ → ℂ} {x₀ : ℝ}

/-- Margin of the left vertex `a` at `z`: up to a factor `√2` the distance to the cone excluded
by the constraint attached to `a`. -/
def vmLeft (a z : ℂ) : ℝ := (z.re - a.re) + |z.im - a.im|

/-- Margin of the right vertex `b` at `z`. -/
def vmRight (b z : ℂ) : ℝ := (b.re - z.re) + |z.im - b.im|

lemma vmLeft_sub_le (a z w : ℂ) : vmLeft a z - vmLeft a w ≤ 2 * ‖z - w‖ := by
  have h1 : z.re - w.re ≤ ‖z - w‖ := by
    have := Complex.abs_re_le_norm (z - w)
    rw [Complex.sub_re] at this
    exact le_trans (le_abs_self _) this
  have h2 : |z.im - a.im| - |w.im - a.im| ≤ ‖z - w‖ := by
    have h := abs_sub_abs_le_abs_sub (z.im - a.im) (w.im - a.im)
    have h3 : (z.im - a.im) - (w.im - a.im) = (z - w).im := by simp
    rw [h3] at h
    have h4 : |(z - w).im| ≤ ‖z - w‖ := Complex.abs_im_le_norm (z - w)
    linarith [h, h4, abs_nonneg ((z - w).im)]
  simp only [vmLeft]
  linarith

lemma vmRight_sub_le (b z w : ℂ) : vmRight b z - vmRight b w ≤ 2 * ‖z - w‖ := by
  have h1 : w.re - z.re ≤ ‖z - w‖ := by
    have := Complex.abs_re_le_norm (w - z)
    rw [Complex.sub_re] at this
    have hz : ‖w - z‖ = ‖z - w‖ := norm_sub_rev w z
    rw [hz] at this
    exact le_trans (le_abs_self _) this
  have h2 : |z.im - b.im| - |w.im - b.im| ≤ ‖z - w‖ := by
    have h := abs_sub_abs_le_abs_sub (z.im - b.im) (w.im - b.im)
    have h3 : (z.im - b.im) - (w.im - b.im) = (z - w).im := by simp
    rw [h3] at h
    have h4 : |(z - w).im| ≤ ‖z - w‖ := Complex.abs_im_le_norm (z - w)
    linarith [h, h4, abs_nonneg ((z - w).im)]
  simp only [vmRight]
  linarith

lemma vmLeft_pos_of_ball {a z : ℂ} {R : ℝ} (h : 2 * R < vmLeft a z) {w : ℂ}
    (hw : ‖w - z‖ < R) : 0 < vmLeft a w := by
  have hh := vmLeft_sub_le a z w
  have h2 : ‖z - w‖ = ‖w - z‖ := norm_sub_rev z w
  rw [h2] at hh
  linarith

lemma vmRight_pos_of_ball {b z : ℂ} {R : ℝ} (h : 2 * R < vmRight b z) {w : ℂ}
    (hw : ‖w - z‖ < R) : 0 < vmRight b w := by
  have hh := vmRight_sub_le b z w
  have h2 : ‖z - w‖ = ‖w - z‖ := norm_sub_rev z w
  rw [h2] at hh
  linarith

lemma mem_Qreg_some_some (a b z : ℂ) :
    z ∈ MandelDim.Qreg (some a) (some b) ↔ 0 < vmLeft a z ∧ 0 < vmRight b z := by
  constructor
  · intro h
    constructor
    · have h1 := h.1 a (by simp)
      have hre : (z - a).re = z.re - a.re := by simp
      have him : (z - a).im = z.im - a.im := by simp
      simp only [vmLeft]
      rw [hre, him] at h1
      linarith
    · have h2 := h.2 b (by simp)
      have hre : (z - b).re = z.re - b.re := by simp
      have him : (z - b).im = z.im - b.im := by simp
      simp only [vmRight]
      rw [hre, him] at h2
      linarith
  · intro h
    constructor
    · intro c hc
      simp only [Option.mem_some_iff] at hc
      subst hc
      have hre : (z - a).re = z.re - a.re := by simp
      have him : (z - a).im = z.im - a.im := by simp
      rw [hre, him]
      have := h.1
      simp only [vmLeft] at this
      linarith
    · intro c hc
      simp only [Option.mem_some_iff] at hc
      subst hc
      have hre : (z - b).re = z.re - b.re := by simp
      have him : (z - b).im = z.im - b.im := by simp
      rw [hre, him]
      have := h.2
      simp only [vmRight] at this
      linarith

lemma ball_subset_Qreg_some_some {a b z : ℂ} {R : ℝ}
    (h : 2 * R < min (vmLeft a z) (vmRight b z)) :
    Metric.ball z R ⊆ MandelDim.Qreg (some a) (some b) := by
  intro w hw
  rw [Metric.mem_ball, dist_eq_norm] at hw
  rw [mem_Qreg_some_some]
  exact ⟨vmLeft_pos_of_ball (lt_of_lt_of_le h (min_le_left _ _)) hw,
         vmRight_pos_of_ball (lt_of_lt_of_le h (min_le_right _ _)) hw⟩

lemma deep_ball {a b z : ℂ} {R δ : ℝ} (h : 2 * (R + δ) < min (vmLeft a z) (vmRight b z))
    {w : ℂ} (hw : ‖w - z‖ < δ) : 2 * R < min (vmLeft a w) (vmRight b w) := by
  have h1 := vmLeft_sub_le a z w
  have h2 := vmRight_sub_le b z w
  have h3 : ‖z - w‖ = ‖w - z‖ := norm_sub_rev z w
  rw [h3] at h1 h2
  refine lt_min ?_ ?_
  · linarith [h, min_le_left (vmLeft a z) (vmRight b z)]
  · linarith [h, min_le_right (vmLeft a z) (vmRight b z)]

lemma vm_im_bound {a b z : ℂ} {T : ℝ} (ha : a.re < z.re) (hb : z.re < b.re)
    (h : min (vmLeft a z) (vmRight b z) ≤ T) :
    |z.im| ≤ T + max |a.im| |b.im| := by
  rcases min_le_iff.mp h with h1 | h1
  · have hT : |z.im - a.im| ≤ T := by
      have hv : vmLeft a z = (z.re - a.re) + |z.im - a.im| := rfl
      rw [hv] at h1
      linarith
    have h2 : |z.im| ≤ |a.im| + |z.im - a.im| := by
      calc |z.im| = |z.im - a.im + a.im| := by ring_nf
        _ ≤ |z.im - a.im| + |a.im| := abs_add_le _ _
        _ = |a.im| + |z.im - a.im| := by ring
    have h4 : |a.im| ≤ max |a.im| |b.im| := le_max_left _ _
    linarith
  · have hT : |z.im - b.im| ≤ T := by
      have hv : vmRight b z = (b.re - z.re) + |z.im - b.im| := rfl
      rw [hv] at h1
      linarith
    have h2 : |z.im| ≤ |b.im| + |z.im - b.im| := by
      calc |z.im| = |z.im - b.im + b.im| := by ring_nf
        _ ≤ |z.im - b.im| + |b.im| := abs_add_le _ _
        _ = |b.im| + |z.im - b.im| := by ring
    have h4 : |b.im| ≤ max |a.im| |b.im| := le_max_right _ _
    linarith

/-- The rectangle `{x₀ - 1/2 ≤ Re z ≤ x₀ + 2, |Im z| ≤ τ}` is compact. -/
lemma isCompact_rect (x₀ τ : ℝ) :
    IsCompact {z : ℂ | x₀ - 1 / 2 ≤ z.re ∧ z.re ≤ x₀ + 2 ∧ |z.im| ≤ τ} := by
  have hcont : Continuous (fun p : ℝ × ℝ => ((p.1 : ℂ) + (p.2 : ℂ) * Complex.I)) := by
    continuity
  have himg : {z : ℂ | x₀ - 1 / 2 ≤ z.re ∧ z.re ≤ x₀ + 2 ∧ |z.im| ≤ τ} =
      (fun p : ℝ × ℝ => ((p.1 : ℂ) + (p.2 : ℂ) * Complex.I)) ''
        (Set.Icc (x₀ - 1 / 2) (x₀ + 2) ×ˢ Set.Icc (-τ) τ) := by
    ext z
    constructor
    · rintro ⟨h1, h2, h3⟩
      refine ⟨(z.re, z.im), ⟨⟨h1, h2⟩, ?_⟩, ?_⟩
      · rw [abs_le] at h3; exact h3
      · simp [Complex.re_add_im]
    · rintro ⟨p, ⟨hp1, hp2⟩, rfl⟩
      rw [Set.mem_Icc] at hp1 hp2
      refine ⟨?_, ?_, ?_⟩
      · simpa using hp1.1
      · simpa using hp1.2
      · have h : ((fun p : ℝ × ℝ => ((p.1 : ℂ) + (p.2 : ℂ) * Complex.I)) p).im = p.2 := by simp
        rw [h, abs_le]
        exact ⟨hp2.1, hp2.2⟩
  rw [himg]
  exact (isCompact_Icc.prod isCompact_Icc).image hcont

theorem fatouU_apriori_bound {b₁ b₂ : Option ℂ} {F : ℂ → ℂ} {x₀ : ℝ}
    (hadm : MandelDim.QAdm b₁ b₂) (hF : MandelDim.NearTranslationL1 F (MandelDim.Qreg b₁ b₂))
    (h₁ : ∀ a ∈ b₁, a.re + 1 < x₀) (h₂ : ∀ b ∈ b₂, x₀ + 3 < b.re) :
    ∃ B : ℝ, ∀ z : ℂ, x₀ - 1 / 2 < z.re → z.re < x₀ + 2 →
      ‖Work.FatouWindow.fatouU hadm hF z‖ ≤ B ∧
      ‖iteratedDeriv 2 (Work.FatouWindow.fatouCoord hadm hF) z‖ ≤ B := by
  obtain ⟨R₁, C₁, C₂, hR₁pos, _hC₁pos, hC₂pos, hEst⟩ := Work.FatouCH.fatouDerivEstimate
  set δ : ℝ := min (1 / 8) (R₁ / 2) with hδdef
  have hδpos : 0 < δ := by
    rw [hδdef]; exact lt_min (by norm_num) (by linarith)
  have hδlt : δ < R₁ := by
    rw [hδdef]
    have := min_le_right (1 / 8 : ℝ) (R₁ / 2)
    linarith
  set T : ℝ := 2 * (R₁ + δ) with hTdef
  have hTpos : 0 < T := by rw [hTdef]; linarith
  have core : ∀ (a b : ℂ), a.re + 1 < x₀ → x₀ + 3 < b.re →
      MandelDim.Qreg (some a) (some b) ⊆ MandelDim.Qreg b₁ b₂ →
      ∃ B : ℝ, ∀ z : ℂ, x₀ - 1 / 2 < z.re → z.re < x₀ + 2 →
        ‖Work.FatouWindow.fatouU hadm hF z‖ ≤ B ∧
        ‖iteratedDeriv 2 (Work.FatouWindow.fatouCoord hadm hF) z‖ ≤ B := by
    intro a b ha hb hsub
    set τ : ℝ := T + max |a.im| |b.im| with hτdef
    set K : Set ℂ := {z : ℂ | x₀ - 1 / 2 ≤ z.re ∧ z.re ≤ x₀ + 2 ∧ |z.im| ≤ τ} with hKdef
    have hKc : IsCompact K := by
      rw [hKdef]
      exact isCompact_rect x₀ τ
    have hKQ : K ⊆ MandelDim.Qreg b₁ b₂ := by
      intro z hz
      rw [hKdef] at hz
      obtain ⟨h1, h2, h3⟩ := hz
      refine hsub ?_
      rw [mem_Qreg_some_some]
      refine ⟨?_, ?_⟩
      · simp only [vmLeft]
        linarith [h1, ha, abs_nonneg (z.im - a.im)]
      · simp only [vmRight]
        linarith [h2, hb, abs_nonneg (z.im - b.im)]
    obtain ⟨BK, _hBK0, hBK⟩ := fatouU_compact_bound hadm hF hKc hKQ
    have hdeep : ∀ z : ℂ, T < min (vmLeft a z) (vmRight b z) →
        ‖Work.FatouWindow.fatouU hadm hF z‖ ≤ C₂ / R₁ + 1 / 31 ∧
        ‖iteratedDeriv 2 (Work.FatouWindow.fatouCoord hadm hF) z‖ ≤ (C₂ / R₁ + 1 / 31) / δ := by
      intro z hz
      have hz2 : 2 * (R₁ + δ) < min (vmLeft a z) (vmRight b z) := by
        rw [hTdef] at hz
        exact hz
      refine fatouU_deep_bound (z := z) hadm hF hR₁pos hC₂pos hδpos (le_of_lt hδlt) ?_ ?_ ?_
      · intro Φ v z₀ R hR hΦ hinj hv hv1 hAbel
        exact (hEst Φ v z₀ R hR hΦ hinj hv hv1 hAbel).2
      · intro w hw
        refine hsub (ball_subset_Qreg_some_some ?_ hw)
        have hw' : ‖w - z‖ < 2 * δ := by
          rw [Metric.mem_ball, dist_eq_norm] at hw
          exact hw
        have : 4 * δ < 2 * (R₁ + δ) := by linarith
        linarith
      · intro w hw
        exact fun y hy => hsub (ball_subset_Qreg_some_some (deep_ball (R := R₁) (δ := δ) hz2 hw) hy)
    refine ⟨max BK (max (C₂ / R₁ + 1 / 31) ((C₂ / R₁ + 1 / 31) / δ)), ?_⟩
    intro z hz1 hz2
    by_cases hzK : z ∈ K
    · exact ⟨le_trans (hBK z hzK).1 (le_max_left _ _),
             le_trans (hBK z hzK).2 (le_max_left _ _)⟩
    · have hzK' : ¬ (x₀ - 1 / 2 ≤ z.re ∧ z.re ≤ x₀ + 2 ∧ |z.im| ≤ τ) := by
        intro h
        exact hzK (by rw [hKdef]; exact h)
      have him : τ < |z.im| := by
        by_contra hcon
        exact hzK' ⟨by linarith, by linarith, not_lt.mp hcon⟩
      have hTmin : T < min (vmLeft a z) (vmRight b z) := by
        by_contra hcon
        have himb := vm_im_bound (a := a) (b := b) (z := z) (T := T)
          (by linarith) (by linarith) (not_lt.mp hcon)
        rw [hτdef] at him
        linarith
      have hd := hdeep z hTmin
      exact ⟨le_trans (le_trans hd.1 (le_max_left _ _)) (le_max_right _ _),
             le_trans (le_trans hd.2 (le_max_right _ _)) (le_max_right _ _)⟩
  rcases b₁ with _ | a₀
  · rcases b₂ with _ | b₀
    · obtain ⟨B, hB⟩ := core ((x₀ - T - 10 : ℝ) : ℂ) ((x₀ + T + 10 : ℝ) : ℂ)
        (by simp; linarith [hTpos]) (by simp; linarith [hTpos])
        (by intro z hz; simp [MandelDim.Qreg])
      exact ⟨B, hB⟩
    · obtain ⟨B, hB⟩ := core ((x₀ - T - 10 : ℝ) : ℂ) b₀
        (by simp; linarith [hTpos]) (by simpa using h₂ b₀ (by simp))
        (by intro z hz; exact ⟨by intro c hc; simp at hc, hz.2⟩)
      exact ⟨B, hB⟩
  · rcases b₂ with _ | b₀
    · obtain ⟨B, hB⟩ := core a₀ ((x₀ + T + 10 : ℝ) : ℂ)
        (by simpa using h₁ a₀ (by simp)) (by simp; linarith [hTpos])
        (by intro z hz; exact ⟨hz.1, by intro c hc; simp at hc⟩)
      exact ⟨B, hB⟩
    · obtain ⟨B, hB⟩ := core a₀ b₀ (by simpa using h₁ a₀ (by simp)) (by simpa using h₂ b₀ (by simp))
        (by intro z hz; exact hz)
      exact ⟨B, hB⟩

end

end Work.FatouWindow

-- the target rests only on the permitted axioms
#print axioms Work.FatouWindow.fatouU_apriori_bound
