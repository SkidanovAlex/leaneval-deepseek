import Mathlib

-- v4.35 port: restore the v4.34 instance-unification behaviour (respectTransparency) in this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.KMTPlan.A6Aux

/-- One full block of length `Q` enumerates `ZMod Q`: summing `f` along
`j ↦ (t + j : ZMod Q)` for `j = 0, …, Q-1` is the same as summing over all residues. -/
lemma residueBlockSum_block {Q : ℕ} [NeZero Q] (t : ℕ) (f : ZMod Q → ℂ) :
    ∑ j ∈ Finset.range Q, f (((t + j : ℕ)) : ZMod Q) = ∑ y : ZMod Q, f y := by
  refine Finset.sum_bij (fun j _ => (((t + j : ℕ)) : ZMod Q)) ?_ ?_ ?_ ?_
  · intro j _
    exact Finset.mem_univ _
  · intro i hi j hj hij
    have h : ((i : ZMod Q)) = ((j : ZMod Q)) := by
      rw [Nat.cast_add, Nat.cast_add] at hij
      exact add_left_cancel hij
    rw [ZMod.natCast_eq_natCast_iff'] at h
    rw [Nat.mod_eq_of_lt (Finset.mem_range.mp hi),
      Nat.mod_eq_of_lt (Finset.mem_range.mp hj)] at h
    exact h
  · intro y _
    refine ⟨(y - (t : ZMod Q)).val, Finset.mem_range.mpr (ZMod.val_lt _), ?_⟩
    rw [Nat.cast_add, ZMod.natCast_zmod_val]
    ring
  · intro j _
    rfl

/-- `k` consecutive blocks of length `Q` give `k` times the sum over one block. -/
lemma residueBlockSum_mul {Q : ℕ} [NeZero Q] (k t : ℕ) (f : ZMod Q → ℂ) :
    ∑ j ∈ Finset.range (k * Q), f (((t + j : ℕ)) : ZMod Q)
      = (k : ℂ) * ∑ j ∈ Finset.range Q, f (((t + j : ℕ)) : ZMod Q) := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [Nat.succ_mul, Finset.sum_range_add, ih]
      have h : ∑ j ∈ Finset.range Q, f (((t + (k * Q + j) : ℕ)) : ZMod Q)
             = ∑ j ∈ Finset.range Q, f (((t + j : ℕ)) : ZMod Q) := by
        apply Finset.sum_congr rfl
        intro j _
        congr 1
        have hk : ((k * Q : ℕ) : ZMod Q) = 0 := by
          rw [Nat.cast_mul, ZMod.natCast_self, mul_zero]
        rw [show (t + (k * Q + j) : ℕ) = (t + j) + k * Q by omega]
        rw [Nat.cast_add, hk, add_zero]
      rw [h]
      push_cast
      ring

theorem ResidueBlockSum {Q : ℕ} [NeZero Q] (k t : ℕ) (f : ZMod Q → ℂ) :
    ∑ j ∈ Finset.range (k * Q), f (((t + j : ℕ)) : ZMod Q) = (k : ℂ) * ∑ y : ZMod Q, f y := by
  rw [residueBlockSum_mul k t f, residueBlockSum_block t f]

end Work.KMTPlan.A6Aux
