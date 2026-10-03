import Mathlib

namespace Work.Pert

/-- A complex function that is `1`-periodic in the real direction and continuous on the closed
half-plane `{w | y ≤ w.im}` and strictly bounded by `δ` on the line `{w | w.im = y}` is bounded
above by some `M < δ` on that line.  The proof restricts to the compact arc
`{w | w.im = y, 0 ≤ w.re ≤ 1}`, on which `‖D ·‖` attains its maximum, and transports the bound
to the whole line using the periodicity. -/
lemma exists_line_bound_lt (D : ℂ → ℂ) {y δ : ℝ}
    (hper : ∀ w : ℂ, D (w + 1) = D w)
    (hcont : ContinuousOn D {w : ℂ | y ≤ w.im})
    (hline : ∀ w : ℂ, w.im = y → ‖D w‖ < δ) :
    ∃ M : ℝ, M < δ ∧ ∀ w : ℂ, w.im = y → ‖D w‖ ≤ M := by
  -- periodicity transported to integer translations
  have hperZ : ∀ (z : ℂ) (n : ℤ), D (z + n) = D z := by
    intro z n
    have h : Function.Periodic D (1 : ℂ) := hper
    have := h.int_mul n
    have hz := this z
    simpa using hz
  -- the compact arc as the image of `[0,1]`
  have hSimg : {w : ℂ | w.im = y ∧ 0 ≤ w.re ∧ w.re ≤ 1}
      = (fun t : ℝ => (t : ℂ) + y * Complex.I) '' (Set.Icc 0 1) := by
    ext w
    constructor
    · rintro ⟨him, h0, h1⟩
      refine ⟨w.re, ⟨h0, h1⟩, ?_⟩
      apply Complex.ext
      · simp
      · simp [him]
    · rintro ⟨t, ht, rfl⟩
      refine ⟨?_, ?_, ?_⟩
      · simp
      · simp [ht.1]
      · simp [ht.2]
  have hcontf : Continuous (fun t : ℝ => (t : ℂ) + y * Complex.I) := by continuity
  have hScomp : IsCompact {w : ℂ | w.im = y ∧ 0 ≤ w.re ∧ w.re ≤ 1} := by
    rw [hSimg]; exact isCompact_Icc.image hcontf
  have hSsub : {w : ℂ | w.im = y ∧ 0 ≤ w.re ∧ w.re ≤ 1} ⊆ {w : ℂ | y ≤ w.im} := by
    intro w hw; exact le_of_eq hw.1.symm
  have hf : ContinuousOn (fun w : ℂ => ‖D w‖) {w : ℂ | w.im = y ∧ 0 ≤ w.re ∧ w.re ≤ 1} :=
    (hcont.mono hSsub).norm
  have hSne : ({w : ℂ | w.im = y ∧ 0 ≤ w.re ∧ w.re ≤ 1} : Set ℂ).Nonempty :=
    ⟨⟨0, y⟩, by simp⟩
  obtain ⟨w₀, hw₀S, hw₀max⟩ := hScomp.exists_isMaxOn hSne hf
  refine ⟨‖D w₀‖, hline w₀ hw₀S.1, ?_⟩
  intro w hw
  have hzS : w - (⌊w.re⌋ : ℂ) ∈ {w : ℂ | w.im = y ∧ 0 ≤ w.re ∧ w.re ≤ 1} := by
    have h1 : ((⌊w.re⌋ : ℤ) : ℝ) ≤ w.re := Int.floor_le w.re
    have h2 : w.re < ((⌊w.re⌋ : ℤ) : ℝ) + 1 := Int.lt_floor_add_one w.re
    refine ⟨?_, ?_, ?_⟩
    · simp [hw]
    · simp only [Complex.sub_re, Complex.intCast_re]; linarith
    · simp only [Complex.sub_re, Complex.intCast_re]; linarith
  have hDw : D w = D (w - (⌊w.re⌋ : ℂ)) := by
    have := hperZ (w - (⌊w.re⌋ : ℂ)) ⌊w.re⌋
    simpa using this
  rw [hDw]
  exact hw₀max hzS

end Work.Pert
