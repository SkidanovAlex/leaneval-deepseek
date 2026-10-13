import Mathlib
import Submission.Work.WilG4c.StepCleanDefs

namespace Work.WilG4c

open WilkiesDesign WilkiesDesign.CG

/-- If `lo` is a lower bound of `F` and no larger number is one, then it is the greatest lower
bound. -/
lemma isGLB_of_sharp {F : Set ℝ} {lo : ℝ} (h1 : ∀ x ∈ F, lo ≤ x)
    (h2 : ∀ u : ℝ, lo < u → ∃ x ∈ F, x < u) : IsGLB F lo := by
  refine ⟨h1, ?_⟩
  intro b hb
  by_contra h
  rw [not_le] at h
  obtain ⟨x, hxF, hx⟩ := h2 b h
  exact absurd (hb hxF) (not_le.mpr hx)

/-- If `hi` is an upper bound of `F` and no smaller number is one, then it is the least upper
bound. -/
lemma isLUB_of_sharp {F : Set ℝ} {hi : ℝ} (h1 : ∀ x ∈ F, x ≤ hi)
    (h2 : ∀ u : ℝ, u < hi → ∃ x ∈ F, u < x) : IsLUB F hi := by
  refine ⟨h1, ?_⟩
  intro b hb
  by_contra h
  rw [not_le] at h
  obtain ⟨x, hxF, hx⟩ := h2 b h
  exact absurd (hb hxF) (not_le.mpr hx)

/-- A slice `F ⊆ (0,1)` which is an interval with `EReal` endpoints or a singleton is in fact an
open interval with *real* endpoints or a singleton.  The hypotheses `F ⊆ (0,1)` and `F ≠ ∅`
exclude the half-line cases `a = ⊥` and `b = ⊤`. -/
lemma slice_shape {F : Set ℝ} (hne : F.Nonempty) (h01 : ∀ x ∈ F, 0 < x ∧ x < 1)
    (hslice : (∃ a b : EReal, F = {x : ℝ | a < (x : EReal) ∧ (x : EReal) < b}) ∨
      (∃ c : ℝ, F = {c})) :
    (∃ A B : ℝ, A < B ∧ F = Set.Ioo A B) ∨ (∃ c : ℝ, F = {c}) := by
  rcases hslice with ⟨a, b, hF⟩ | h
  · left
    obtain ⟨x0, hx0F⟩ := hne
    have hx0G : x0 ∈ {x : ℝ | a < (x : EReal) ∧ (x : EReal) < b} := by
      rw [← hF]; exact hx0F
    obtain ⟨ha_lt, hlt_b⟩ := hx0G
    have hx0_01 := h01 x0 hx0F
    have ha_ne_top : a ≠ ⊤ := by
      intro h; rw [h] at ha_lt; exact absurd ha_lt not_top_lt
    have hb_ne_bot : b ≠ ⊥ := by
      intro h; rw [h] at hlt_b; exact absurd hlt_b not_lt_bot
    have ha_ne_bot : a ≠ ⊥ := by
      intro h
      have hy0 : (x0 - 1 : ℝ) < x0 := by linarith
      have hcast : ((x0 - 1 : ℝ) : EReal) < (x0 : EReal) := EReal.coe_lt_coe_iff.mpr hy0
      have hmem : (x0 - 1 : ℝ) ∈ {x : ℝ | a < (x : EReal) ∧ (x : EReal) < b} := by
        refine ⟨?_, lt_trans hcast hlt_b⟩
        rw [h]; exact EReal.bot_lt_coe _
      have h01' := h01 _ (by rw [hF]; exact hmem)
      linarith [h01'.1, hx0_01.2]
    have hb_ne_top : b ≠ ⊤ := by
      intro h
      have hy0 : x0 < (x0 + 1 : ℝ) := by linarith
      have hcast : (x0 : EReal) < ((x0 + 1 : ℝ) : EReal) := EReal.coe_lt_coe_iff.mpr hy0
      have hmem : (x0 + 1 : ℝ) ∈ {x : ℝ | a < (x : EReal) ∧ (x : EReal) < b} := by
        refine ⟨lt_trans ha_lt hcast, ?_⟩
        rw [h]; exact EReal.coe_lt_top _
      have h01' := h01 _ (by rw [hF]; exact hmem)
      linarith [h01'.2, hx0_01.1]
    have ha_eq : a = (a.toReal : EReal) := (EReal.coe_toReal ha_ne_top ha_ne_bot).symm
    have hb_eq : b = (b.toReal : EReal) := (EReal.coe_toReal hb_ne_top hb_ne_bot).symm
    refine ⟨a.toReal, b.toReal, ?_, ?_⟩
    · have h1 : (a.toReal : EReal) < (x0 : EReal) := by rw [← ha_eq]; exact ha_lt
      have h2 : (x0 : EReal) < (b.toReal : EReal) := by rw [← hb_eq]; exact hlt_b
      have h1' : a.toReal < x0 := EReal.coe_lt_coe_iff.mp h1
      have h2' : x0 < b.toReal := EReal.coe_lt_coe_iff.mp h2
      linarith
    · rw [hF]
      ext x
      simp only [Set.mem_ofPred_eq, Set.mem_Ioo]
      constructor
      · rintro ⟨h1, h2⟩
        rw [ha_eq] at h1
        rw [hb_eq] at h2
        exact ⟨EReal.coe_lt_coe_iff.mp h1, EReal.coe_lt_coe_iff.mp h2⟩
      · rintro ⟨h1, h2⟩
        exact ⟨by rw [ha_eq]; exact EReal.coe_lt_coe_iff.mpr h1,
               by rw [hb_eq]; exact EReal.coe_lt_coe_iff.mpr h2⟩
  · right; exact h

/-- **Fibre interpolation (BNZ §2.3).**  Let `F ⊆ ℝ` be a nonempty subset of `(0,1)` which is
either an interval with `EReal` endpoints or a single point.  Let `lo, hi` be sharp bounds of
`F`: `lo ≤ x ≤ hi` for all `x ∈ F`, and no number above `lo` (resp. below `hi`) bounds `F`.
Then the interpolation `s ↦ lo + (hi - lo) * s` maps `(0,1)` exactly onto `F`. -/
theorem FibreInterp {F : Set ℝ} {lo hi : ℝ} (hne : F.Nonempty)
    (h01 : ∀ x ∈ F, 0 < x ∧ x < 1)
    (hslice : (∃ a b : EReal, F = {x : ℝ | a < (x : EReal) ∧ (x : EReal) < b}) ∨
      (∃ c : ℝ, F = {c}))
    (hlo : ∀ x ∈ F, lo ≤ x ∧ x ≤ hi)
    (hsharp_lo : ∀ u : ℝ, lo < u → ∃ x ∈ F, x < u)
    (hsharp_hi : ∀ u : ℝ, u < hi → ∃ x ∈ F, u < x) :
    (∀ s ∈ Set.Ioo (0 : ℝ) 1, lo + (hi - lo) * s ∈ F) ∧
      (∀ y ∈ F, ∃ s ∈ Set.Ioo (0 : ℝ) 1, lo + (hi - lo) * s = y) := by
  have hGLB : IsGLB F lo := isGLB_of_sharp (fun x hx => (hlo x hx).1) hsharp_lo
  have hLUB : IsLUB F hi := isLUB_of_sharp (fun x hx => (hlo x hx).2) hsharp_hi
  rcases slice_shape hne h01 hslice with ⟨A, B, hAB, hF⟩ | ⟨c, hF⟩
  · have hlo_eq : lo = A := ((hF ▸ hGLB) : IsGLB (Set.Ioo A B) lo).unique (isGLB_Ioo hAB)
    have hhi_eq : hi = B := ((hF ▸ hLUB) : IsLUB (Set.Ioo A B) hi).unique (isLUB_Ioo hAB)
    refine ⟨?_, ?_⟩
    · intro s hs
      rw [hlo_eq, hhi_eq, hF]
      rw [Set.mem_Ioo] at hs ⊢
      exact ⟨by nlinarith [hs.1, hAB], by nlinarith [hs.1, hs.2, hAB]⟩
    · intro y hy
      rw [hF] at hy
      rw [Set.mem_Ioo] at hy
      refine ⟨(y - A) / (B - A), ?_, ?_⟩
      · rw [Set.mem_Ioo]
        exact ⟨div_pos (by linarith [hy.1]) (by linarith),
               (div_lt_one (by linarith)).mpr (by linarith [hy.2])⟩
      · rw [hlo_eq, hhi_eq, mul_div_cancel₀ (y - A) (by linarith : B - A ≠ 0)]
        ring
  · have hlo_eq : lo = c := ((hF ▸ hGLB) : IsGLB {c} lo).unique isGLB_singleton
    have hhi_eq : hi = c := ((hF ▸ hLUB) : IsLUB {c} hi).unique isLUB_singleton
    refine ⟨?_, ?_⟩
    · intro s hs
      rw [hlo_eq, hhi_eq, hF]
      simp
    · intro y hy
      rw [hF] at hy
      rw [Set.mem_singleton_iff] at hy
      refine ⟨1 / 2, by rw [Set.mem_Ioo]; norm_num, ?_⟩
      rw [hlo_eq, hhi_eq, hy]
      ring

end Work.WilG4c
