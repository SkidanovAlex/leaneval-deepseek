import Mathlib
import Submission.Work.Fatou.Surface.orbitDefs

namespace Work.Fatou.Surface

noncomputable section

variable {b₁ b₂ : Option ℂ} {F : ℂ → ℂ} {x₀ : ℝ}

/-- An orbit piece of length `1` is just membership of the point and its image in `𝒬`. -/
theorem piece_one_of_mem {z : ℂ} (hz : z ∈ MandelDim.Qreg b₁ b₂)
    (hz' : F z ∈ MandelDim.Qreg b₁ b₂) : Piece b₁ b₂ F z 1 := by
  intro j hj
  interval_cases j
  · simpa using hz
  · simpa using hz'

/-- **One step of `F` increases the level by one.** If `(s, k)` is a candidate orbit coordinate for `z` and `F z` stays in `𝒬`, then `(s, k+1)` is a candidate orbit coordinate for `F z`. -/
theorem specSucc {b₁ b₂ : Option ℂ} {F : ℂ → ℂ} {x₀ : ℝ} {z : ℂ} {p : ℂ × ℤ}
    (h : Work.Fatou.Surface.Spec b₁ b₂ F x₀ z p) (hz : F z ∈ MandelDim.Qreg b₁ b₂) :
    Work.Fatou.Surface.Spec b₁ b₂ F x₀ (F z) (p.1, p.2 + 1) := by
  obtain ⟨hs, a, b, ⟨hmeet1, hp1, hp2⟩, hab, hlev⟩ := h
  have hzQ : z ∈ MandelDim.Qreg b₁ b₂ := hp2 0 (Nat.zero_le b)
  rcases hab with ha | hb
  · -- `a = 0`, i.e. `p.1 = F^[b] z`, so `z` sits `b` steps *behind* the representative
    subst ha
    simp only [Function.iterate_zero_apply] at hmeet1 hlev
    rcases Nat.eq_zero_or_pos b with hb0 | hbpos
    · -- `b = 0` as well: `p.1 = z`, level `0`; step forward one level with `a' = 1, b' = 0`
      subst hb0
      simp only [Nat.cast_zero] at hmeet1 hlev
      exact ⟨hs, 1, 0, ⟨by rw [hmeet1]; simp,
        piece_one_of_mem (by rw [hmeet1]; exact hzQ) (by rw [hmeet1]; exact hz),
        piece_zero hz⟩, Or.inr rfl, by rw [hlev]; norm_num⟩
    · -- `b ≥ 1`: `p.1 = F^[b] z` and `F^[b-1] (F z) = p.1`, so `a' = 0, b' = b - 1`
      have hstep : F^[b - 1] (F z) = p.1 := by
        rw [hmeet1, show F z = F^[1] z by simp, ← Function.iterate_add_apply]
        congr 1
        omega
      refine ⟨hs, 0, b - 1, ⟨?_, piece_zero (fund_mem hs), ?_⟩, Or.inl rfl, ?_⟩
      · simpa only [Function.iterate_zero_apply] using hstep.symm
      · -- `Piece F (F z) (b-1)` from `Piece F z b`
        have hpi := piece_of_iterate (b₁ := b₁) (b₂ := b₂) (z := z) (a := 1) (n := b - 1)
          (by rw [Nat.add_sub_cancel' hbpos]; exact hp2)
        simpa only [Function.iterate_one] using hpi
      · rw [hlev]
        have hb1 : ((b - 1 : ℕ) : ℤ) = (b : ℤ) - 1 := by omega
        omega
  · -- `b = 0`, i.e. `F^[a] p.1 = z`, level `a`; step forward one level with `a' = a+1, b' = 0`
    subst hb
    simp only [Function.iterate_zero_apply] at hmeet1 hlev
    refine ⟨hs, a + 1, 0, ⟨?_, ?_, piece_zero hz⟩, Or.inr rfl, ?_⟩
    · -- `F^[a+1] p.1 = F^[0] (F z)`
      rw [Function.iterate_succ_apply', hmeet1]
      simp
    · -- `Piece F p.1 (a+1)`
      exact piece_trans (b₁ := b₁) (b₂ := b₂) (z := p.1) (a := a) (n := 1) hp1
        (by rw [hmeet1]; exact piece_one_of_mem hzQ hz)
    · rw [hlev]
      push_cast
      ring

end

end Work.Fatou.Surface
