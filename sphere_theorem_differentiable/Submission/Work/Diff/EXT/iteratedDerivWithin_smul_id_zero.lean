import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.EXT

/-- If `t ↦ t • ψ t` is (right-)flat to infinite order at `0` on `Ico 0 T`, then so is `ψ`.
This is the Leibniz identity `(t • ψ t)^{(k+1)}(0) = (k+1) • ψ^{(k)}(0)`
(`iteratedDerivWithin_smul` applied to `id • ψ`). -/
theorem iteratedDerivWithin_smul_id_zero
    {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    {T : ℝ} (hT : 0 < T) (ψ : ℝ → Z)
    (hψ : ContDiffOn ℝ (⊤ : ℕ∞) ψ (Set.Ico 0 T))
    (h0 : ∀ k : ℕ, iteratedDerivWithin (k + 1) (fun t : ℝ => t • ψ t) (Set.Ico 0 T) 0 = 0) :
    ∀ j : ℕ, iteratedDerivWithin j ψ (Set.Ico 0 T) 0 = 0 := by
  intro j
  have hs : UniqueDiffOn ℝ (Set.Ico 0 T) := uniqueDiffOn_Ico 0 T
  have hx : (0 : ℝ) ∈ Set.Ico 0 T := ⟨le_refl 0, hT⟩
  -- The Leibniz identity at the boundary point `0`.
  have key : ∀ k : ℕ, iteratedDerivWithin (k + 1) (fun t : ℝ => t • ψ t) (Set.Ico 0 T) 0
      = ((k + 1 : ℕ) : ℝ) • iteratedDerivWithin k ψ (Set.Ico 0 T) 0 := by
    intro k
    have hψ' : ContDiffWithinAt ℝ (((k + 1 : ℕ) : ℕ∞)) ψ (Set.Ico 0 T) 0 :=
      (hψ.contDiffWithinAt hx).of_le (by simp)
    have hid : ContDiffWithinAt ℝ (((k + 1 : ℕ) : ℕ∞)) (id : ℝ → ℝ) (Set.Ico 0 T) 0 :=
      contDiffWithinAt_id
    have hsmul := iteratedDerivWithin_smul (𝔸 := ℝ) hx hs hid hψ'
    change iteratedDerivWithin (k + 1) ((id : ℝ → ℝ) • ψ) (Set.Ico 0 T) 0 = _
    rw [hsmul, Finset.sum_eq_single 1]
    · rw [iteratedDerivWithin_id hx hs]
      simp [Nat.choose_one_right]
      rw [show (↑k + 1 : ℝ) = ((k + 1 : ℕ) : ℝ) by push_cast; ring]
      rw [Nat.cast_smul_eq_nsmul]
    · intro i _ hne
      rw [iteratedDerivWithin_id hx hs]
      have hiz : (if i = 0 then (0 : ℝ) else if i = 1 then 1 else 0) = 0 := by
        rcases eq_or_ne i 0 with h | h
        · simp [h]
        · simp [h, hne]
      rw [hiz]
      simp
    · intro hnot
      exact absurd (Finset.mem_range.mpr (by omega : 1 < (k + 1) + 1)) hnot
  have hk := h0 j
  rw [key j] at hk
  have hne : ((j + 1 : ℕ) : ℝ) ≠ 0 := by positivity
  exact (smul_eq_zero.mp hk).resolve_left hne

end Work.Diff.EXT
