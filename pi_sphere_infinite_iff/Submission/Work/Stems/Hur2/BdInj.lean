import Submission.Work.Stems.Hur2.ConeRad

/-!
# `bd` is injective off the wrap-around

`bd : I → ∂I²` traverses the boundary counterclockwise; it is injective except that
`bd 0 = bd 1 = (0,0)`.  Concretely: `bd t = bd t'` forces `t = t'` or `{t,t'} = {0,1}`.
This is the fibre statement used to descend a null-homotopy along `coneMap`.
-/

open scoped unitInterval Topology

namespace Work.Stems.Hur2

open Work.Stems.Cubical

noncomputable section

/-! ## The converse characterisations of the four edge values -/

theorem bd1_eq_zero_imp (t : unitInterval) (h : (bd1 t : ℝ) = 0) :
    (t : ℝ) ≤ 1 / 4 ∨ (t : ℝ) = 1 := by
  have ht1 : (t : ℝ) ≤ 1 := t.2.2
  rcases le_total (t : ℝ) (1 / 4) with h1 | h1
  · exact Or.inl h1
  rcases le_total (t : ℝ) (1 / 2) with h2 | h2
  · have hlin : (bd1 t : ℝ) = 4 * (t : ℝ) - 1 := bd1_eq_of_quarter_le t h1 h2
    rw [hlin] at h
    exact Or.inl (by linarith)
  rcases le_total (t : ℝ) (3 / 4) with h3 | h3
  · have hlin : (bd1 t : ℝ) = 1 := bd1_eq_one_of_half_le t h2 h3
    rw [hlin] at h
    norm_num at h
  · have hlin : (bd1 t : ℝ) = 4 - 4 * (t : ℝ) := bd1_eq_of_three_quarter_le t h3
    rw [hlin] at h
    exact Or.inr (by linarith)

theorem bd0_eq_one_imp (t : unitInterval) (h : (bd0 t : ℝ) = 1) :
    1 / 4 ≤ (t : ℝ) ∧ (t : ℝ) ≤ 1 / 2 := by
  rcases le_total (t : ℝ) (1 / 4) with h1 | h1
  · have hlin : (bd0 t : ℝ) = 4 * (t : ℝ) := bd0_eq_of_le_quarter t h1
    rw [hlin] at h
    constructor <;> linarith
  rcases le_total (t : ℝ) (1 / 2) with h2 | h2
  · exact ⟨h1, h2⟩
  rcases le_total (t : ℝ) (3 / 4) with h3 | h3
  · have hlin : (bd0 t : ℝ) = 3 - 4 * (t : ℝ) := bd0_eq_of_half_le t h2 h3
    rw [hlin] at h
    constructor <;> linarith
  · have hlin : (bd0 t : ℝ) = 0 := bd0_eq_zero_of_three_quarter_le t h3
    rw [hlin] at h
    norm_num at h

theorem bd1_eq_one_imp (t : unitInterval) (h : (bd1 t : ℝ) = 1) :
    1 / 2 ≤ (t : ℝ) ∧ (t : ℝ) ≤ 3 / 4 := by
  have ht0 : (0 : ℝ) ≤ (t : ℝ) := t.2.1
  rcases le_total (t : ℝ) (1 / 4) with h1 | h1
  · have hlin : (bd1 t : ℝ) = 0 := bd1_eq_zero_of_le_quarter t h1
    rw [hlin] at h
    norm_num at h
  rcases le_total (t : ℝ) (1 / 2) with h2 | h2
  · have hlin : (bd1 t : ℝ) = 4 * (t : ℝ) - 1 := bd1_eq_of_quarter_le t h1 h2
    rw [hlin] at h
    constructor <;> linarith
  rcases le_total (t : ℝ) (3 / 4) with h3 | h3
  · exact ⟨h2, h3⟩
  · have hlin : (bd1 t : ℝ) = 4 - 4 * (t : ℝ) := bd1_eq_of_three_quarter_le t h3
    rw [hlin] at h
    constructor <;> linarith

theorem bd0_eq_zero_imp (t : unitInterval) (h : (bd0 t : ℝ) = 0) :
    (t : ℝ) = 0 ∨ 3 / 4 ≤ (t : ℝ) := by
  rcases le_total (t : ℝ) (1 / 4) with h1 | h1
  · have hlin : (bd0 t : ℝ) = 4 * (t : ℝ) := bd0_eq_of_le_quarter t h1
    rw [hlin] at h
    exact Or.inl (by linarith)
  rcases le_total (t : ℝ) (1 / 2) with h2 | h2
  · have hlin : (bd0 t : ℝ) = 1 := bd0_eq_one_of_quarter_le t h1 h2
    rw [hlin] at h
    norm_num at h
  rcases le_total (t : ℝ) (3 / 4) with h3 | h3
  · have hlin : (bd0 t : ℝ) = 3 - 4 * (t : ℝ) := bd0_eq_of_half_le t h2 h3
    rw [hlin] at h
    exact Or.inr (by linarith)
  · exact Or.inr h3

/-! ## The fibre statement -/

theorem bd_inj_weak (t t' : unitInterval) (h : bd t = bd t') :
    t = t' ∨ (t = 0 ∧ t' = 1) ∨ (t = 1 ∧ t' = 0) := by
  have h0 : (bd0 t : ℝ) = (bd0 t' : ℝ) := by
    have := congrArg (fun q : IC 2 => (q 0 : ℝ)) h
    simpa [bd_apply_zero] using this
  have h1 : (bd1 t : ℝ) = (bd1 t' : ℝ) := by
    have := congrArg (fun q : IC 2 => (q 1 : ℝ)) h
    simpa [bd_apply_one] using this
  rcases le_total (t : ℝ) (1 / 4) with hA | hA
  · have hz : (bd1 t : ℝ) = 0 := bd1_eq_zero_of_le_quarter t hA
    rw [hz] at h1
    have hz' : (bd1 t' : ℝ) = 0 := h1.symm
    rcases bd1_eq_zero_imp t' hz' with hB | hB
    · left
      have hlin : (bd0 t : ℝ) = 4 * (t : ℝ) := bd0_eq_of_le_quarter t hA
      have hlin' : (bd0 t' : ℝ) = 4 * (t' : ℝ) := bd0_eq_of_le_quarter t' hB
      apply Subtype.ext
      linarith
    · right; left
      refine ⟨?_, ?_⟩
      · apply Subtype.ext
        have hlin : (bd0 t : ℝ) = 4 * (t : ℝ) := bd0_eq_of_le_quarter t hA
        have hz0 : (bd0 t' : ℝ) = 0 := by
          have ht' : t' = 1 := Subtype.ext hB
          rw [ht']
          exact bd0_eq_zero_of_three_quarter_le 1 (by norm_num)
        show (t : ℝ) = 0
        linarith
      · exact Subtype.ext hB
  rcases le_total (t : ℝ) (1 / 2) with hB | hB
  · have ho : (bd0 t : ℝ) = 1 := bd0_eq_one_of_quarter_le t hA hB
    rw [ho] at h0
    have ho' : (bd0 t' : ℝ) = 1 := h0.symm
    obtain ⟨hc, hd⟩ := bd0_eq_one_imp t' ho'
    left
    have hlin : (bd1 t : ℝ) = 4 * (t : ℝ) - 1 := bd1_eq_of_quarter_le t hA hB
    have hlin' : (bd1 t' : ℝ) = 4 * (t' : ℝ) - 1 := bd1_eq_of_quarter_le t' hc hd
    apply Subtype.ext
    linarith
  rcases le_total (t : ℝ) (3 / 4) with hC | hC
  · have ho : (bd1 t : ℝ) = 1 := bd1_eq_one_of_half_le t hB hC
    rw [ho] at h1
    have ho' : (bd1 t' : ℝ) = 1 := h1.symm
    obtain ⟨hc, hd⟩ := bd1_eq_one_imp t' ho'
    left
    have hlin : (bd0 t : ℝ) = 3 - 4 * (t : ℝ) := bd0_eq_of_half_le t hB hC
    have hlin' : (bd0 t' : ℝ) = 3 - 4 * (t' : ℝ) := bd0_eq_of_half_le t' hc hd
    apply Subtype.ext
    linarith
  · have hz : (bd0 t : ℝ) = 0 := bd0_eq_zero_of_three_quarter_le t hC
    rw [hz] at h0
    have hz' : (bd0 t' : ℝ) = 0 := h0.symm
    rcases bd0_eq_zero_imp t' hz' with hD | hD
    · right; right
      refine ⟨?_, ?_⟩
      · apply Subtype.ext
        have hlin : (bd1 t : ℝ) = 4 - 4 * (t : ℝ) := bd1_eq_of_three_quarter_le t hC
        have hz1 : (bd1 t' : ℝ) = 0 := by
          have ht' : t' = 0 := Subtype.ext hD
          rw [ht']
          exact bd1_eq_zero_of_le_quarter 0 (by norm_num)
        rw [hlin] at h1
        rw [hz1] at h1
        show (t : ℝ) = 1
        linarith
      · exact Subtype.ext hD
    · left
      have hlin : (bd1 t : ℝ) = 4 - 4 * (t : ℝ) := bd1_eq_of_three_quarter_le t hC
      have hlin' : (bd1 t' : ℝ) = 4 - 4 * (t' : ℝ) := bd1_eq_of_three_quarter_le t' hD
      apply Subtype.ext
      rw [hlin] at h1
      rw [hlin'] at h1
      linarith

end

end Work.Stems.Hur2
