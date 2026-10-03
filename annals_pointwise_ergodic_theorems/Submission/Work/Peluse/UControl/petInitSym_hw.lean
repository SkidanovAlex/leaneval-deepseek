import Mathlib
import Submission.Work.Peluse.UControl.petInitDefs

namespace Work.Peluse.UControl

noncomputable section

/-- The weight `k ↦ petChainLevel γ k ^ 2 / (20000 * (2 ^ k * D + 1))` appearing in the window
condition of the analytic PET chain is nonincreasing in the step count `k`.

Indeed `petChainLevel γ (k+1) = petChainLevel γ k ^ 2 / 2000`, so passing from `k` to `k+1` squares
the (already `≤ 1`) level and multiplies the denominator by (more than) `2`, whence a gain of at
least `2000 ^ 2`. -/
lemma petChainWindowLevel_antitone (γ : ℝ) (D : ℕ) (hγ0 : 0 < γ) (hγ1 : γ ≤ 1) :
    Antitone fun k : ℕ =>
      petChainLevel γ k ^ 2 / (20000 * (((2 ^ k * D : ℕ) : ℝ) + 1)) := by
  refine antitone_nat_of_succ_le fun k => ?_
  rw [petChainLevel_succ]
  set L := petChainLevel γ k with hL
  have hx0 : 0 < L := petChainLevel_pos γ hγ0 k
  have hx1 : L ≤ 1 := petChainLevel_le_one γ hγ0 hγ1 k
  have hAB : (((2 ^ k * D : ℕ) : ℝ) + 1) ≤ (((2 ^ (k + 1) * D : ℕ) : ℝ) + 1) := by
    have h2 : (2 : ℕ) ^ k ≤ 2 ^ (k + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    have h3 : (2 ^ k * D : ℕ) + 1 ≤ 2 ^ (k + 1) * D + 1 :=
      Nat.add_le_add_right (Nat.mul_le_mul_right D h2) 1
    exact_mod_cast h3
  have h1 : (L ^ 2 / 2000) ^ 2 ≤ L ^ 2 := by
    have hL2 : L ^ 2 ≤ 1 := by nlinarith
    have h2000 : L ^ 2 / 2000 ≤ 1 := by
      rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 2000)]; linarith
    have hnn : 0 ≤ L ^ 2 / 2000 := by positivity
    nlinarith [hnn, h2000, sq_nonneg (L ^ 2)]
  have h2 : (20000 : ℝ) * (((2 ^ k * D : ℕ) : ℝ) + 1)
      ≤ 20000 * (((2 ^ (k + 1) * D : ℕ) : ℝ) + 1) := by linarith
  exact div_le_div₀ (sq_nonneg L) h1 (by positivity) h2

/-- The window radius `petWindow γ D (chainLen X)` of the initial symbolic PET state satisfies the
window condition of `PetInv` at every step of the chain: the condition is *decreasing* in the step
count, so it is enough to check it at the last step, which is exactly how `petWindow` is defined. -/
theorem petInitSym_hw (P : Polynomial ℤ) (γ : ℝ) (D : ℕ) (hγ0 : 0 < γ) (hγ1 : γ ≤ 1)
    (hD : 1 ≤ D) :
    ∀ k : ℕ, k < chainLen (petInitSym P) →
      petWindow γ D (chainLen (petInitSym P)) ≤
        petChainLevel γ k ^ 2 / (20000 * (((2 ^ k * D : ℕ) : ℝ) + 1)) := by
  intro k hk
  have hk' : k ≤ chainLen (petInitSym P) - 1 := Nat.le_sub_one_of_lt hk
  have hmono := petChainWindowLevel_antitone γ D hγ0 hγ1 hk'
  calc petWindow γ D (chainLen (petInitSym P))
      = min 1 (petChainLevel γ (chainLen (petInitSym P) - 1) ^ 2
          / (20000 * (((2 ^ (chainLen (petInitSym P) - 1) * D : ℕ) : ℝ) + 1))) := rfl
    _ ≤ petChainLevel γ (chainLen (petInitSym P) - 1) ^ 2
          / (20000 * (((2 ^ (chainLen (petInitSym P) - 1) * D : ℕ) : ℝ) + 1)) :=
        min_le_right _ _
    _ ≤ petChainLevel γ k ^ 2 / (20000 * (((2 ^ k * D : ℕ) : ℝ) + 1)) := hmono

end

end Work.Peluse.UControl
