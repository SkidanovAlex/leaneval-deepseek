import Mathlib.Data.ZMod.Basic

set_option autoImplicit false
set_option linter.style.haveILetI false

namespace Commons.Data.Nat

/-- If `R` is coprime to the positive modulus `Q`, then every residue class
`c` modulo `Q` contains a representative `a0` of the form `a0 * R`, with
`a0` drawn from the canonical interval `[1, Q]`. -/
theorem exists_canonical_congruence_solution (Q R c : ℕ) (hQ : 1 ≤ Q)
    (hcop : Nat.Coprime R Q) :
    ∃ a0 : ℕ, 1 ≤ a0 ∧ a0 ≤ Q ∧ a0 * R ≡ c [MOD Q] := by
  have hQne : Q ≠ 0 := by omega
  letI : NeZero Q := ⟨hQne⟩
  let u : (ZMod Q)ˣ := ZMod.unitOfCoprime R hcop
  let z : ZMod Q := (c : ZMod Q) * ((u⁻¹ : (ZMod Q)ˣ) : ZMod Q)
  let a0 : ℕ := if z.val = 0 then Q else z.val
  have hzlt : z.val < Q := z.val_lt
  have hcast_u : (u : ZMod Q) = (R : ZMod Q) := by
    change ((ZMod.unitOfCoprime R hcop : (ZMod Q)ˣ) : ZMod Q) = (R : ZMod Q)
    exact ZMod.coe_unitOfCoprime R hcop
  have hmain : z * (R : ZMod Q) = (c : ZMod Q) := by
    dsimp [z]
    rw [← hcast_u]
    rw [mul_assoc]
    rw [Units.inv_mul u]
    simp
  have ha0cast : (a0 : ZMod Q) = z := by
    dsimp [a0]
    by_cases hz : z.val = 0
    · have hz0 : (0 : ZMod Q) = z := by
        rw [← ZMod.natCast_zmod_val z]
        simp [hz]
      simpa [hz] using hz0
    · simp [hz]
  refine ⟨a0, ?_, ?_, ?_⟩
  · dsimp [a0]
    by_cases hz : z.val = 0
    · simp [hz, hQ]
    · simp [hz]
      omega
  · dsimp [a0]
    by_cases hz : z.val = 0
    · simp [hz]
    · simp [hz]
      exact le_of_lt hzlt
  · rw [← ZMod.natCast_eq_natCast_iff]
    calc
      ((a0 * R : ℕ) : ZMod Q) = (a0 : ZMod Q) * (R : ZMod Q) := by simp
      _ = z * (R : ZMod Q) := by rw [ha0cast]
      _ = (c : ZMod Q) := hmain

end Commons.Data.Nat