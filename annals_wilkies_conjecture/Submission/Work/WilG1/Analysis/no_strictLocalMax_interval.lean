import Mathlib
import Submission.Work.WilG1.Basic

namespace Work.WilG1.Analysis

/-- Given `a < b`, every point of `[a,b]` has distinct points of `[a,b]` arbitrarily close to it. -/
private lemma exists_ne_near_Icc {a b n : ℝ} (hab : a < b) (hn : n ∈ Set.Icc a b) {δ : ℝ}
    (hδ : 0 < δ) : ∃ y ∈ Set.Icc a b, y ≠ n ∧ |y - n| < δ := by
  have hna : a ≤ n := hn.1
  have hnb : n ≤ b := hn.2
  rcases lt_or_eq_of_le hnb with hlt | heq
  · refine ⟨n + min δ (b - n) / 2, ⟨?_, ?_⟩, ?_, ?_⟩
    · have hpos : (0 : ℝ) < min δ (b - n) := lt_min hδ (by linarith)
      linarith
    · have hle : min δ (b - n) ≤ b - n := min_le_right _ _
      have hpos : (0 : ℝ) < min δ (b - n) := lt_min hδ (by linarith)
      nlinarith [hle]
    · have hpos : (0 : ℝ) < min δ (b - n) := lt_min hδ (by linarith)
      intro hc; linarith
    · have hle : min δ (b - n) ≤ δ := min_le_left _ _
      have hpos : (0 : ℝ) < min δ (b - n) := lt_min hδ (by linarith)
      rw [abs_lt]
      constructor <;> nlinarith [hle, hpos]
  · refine ⟨n - min δ (b - a) / 2, ⟨?_, ?_⟩, ?_, ?_⟩
    · have hle : min δ (b - a) ≤ b - a := min_le_right _ _
      have hpos : (0 : ℝ) < min δ (b - a) := lt_min hδ (by linarith)
      nlinarith [hle, heq]
    · have hpos : (0 : ℝ) < min δ (b - a) := lt_min hδ (by linarith)
      linarith
    · have hpos : (0 : ℝ) < min δ (b - a) := lt_min hδ (by linarith)
      intro hc; linarith
    · have hle : min δ (b - a) ≤ δ := min_le_left _ _
      have hpos : (0 : ℝ) < min δ (b - a) := lt_min hδ (by linarith)
      rw [abs_lt]
      constructor <;> nlinarith [hle, hpos]

theorem no_strictLocalMax_interval {f : ℝ → ℝ} {I : Set ℝ} (hI : I.OrdConnected)
    (hcont : ∀ x ∈ I, ContinuousAt f x)
    (hmax : ∀ x ∈ I, ∃ δ > 0, ∀ y, y ≠ x → |y - x| < δ → f y < f x) :
    I.Subsingleton := by
  intro x hx y hy
  rcases le_total x y with hxy | hyx
  · rcases lt_or_eq_of_le hxy with hlt | heq
    · exfalso
      have hsub : Set.Icc x y ⊆ I := hI.out hx hy
      have hcont' : ContinuousOn f (Set.Icc x y) :=
        fun z hz => (hcont z (hsub hz)).continuousWithinAt
      obtain ⟨n, hn, hmin⟩ :=
        isCompact_Icc.exists_isMinOn ⟨x, Set.left_mem_Icc.mpr hxy⟩ hcont'
      have hnI : n ∈ I := hsub hn
      obtain ⟨δ, hδ, hδmax⟩ := hmax n hnI
      obtain ⟨z, hz, hzne, hzn⟩ := exists_ne_near_Icc hlt hn hδ
      have h1 : f z < f n := hδmax z hzne hzn
      have h2 : f n ≤ f z := hmin hz
      linarith
    · exact heq
  · rcases lt_or_eq_of_le hyx with hlt | heq
    · exfalso
      have hsub : Set.Icc y x ⊆ I := hI.out hy hx
      have hcont' : ContinuousOn f (Set.Icc y x) :=
        fun z hz => (hcont z (hsub hz)).continuousWithinAt
      obtain ⟨n, hn, hmin⟩ :=
        isCompact_Icc.exists_isMinOn ⟨y, Set.left_mem_Icc.mpr hyx⟩ hcont'
      have hnI : n ∈ I := hsub hn
      obtain ⟨δ, hδ, hδmax⟩ := hmax n hnI
      obtain ⟨z, hz, hzne, hzn⟩ := exists_ne_near_Icc hlt hn hδ
      have h1 : f z < f n := hδmax z hzne hzn
      have h2 : f n ≤ f z := hmin hz
      linarith
    · exact heq.symm

end Work.WilG1.Analysis
