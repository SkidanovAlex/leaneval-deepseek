import Mathlib
import Submission.Work.Resample.buQWdefs

namespace Work.Resample

open HvdH

/-- The halving `z ↦ (z₁ / 2, z₂ / 2)` of a fixed-point pair in the disc of radius `2 ^ p` stays
in the disc of radius `2 ^ (p - 1) + 2`.  The essential point is that the disc hypothesis is used
through `|a| ^ 2 + |b| ^ 2 ≤ 4 ^ p` (a per-coordinate bound would only give the false
`2 * 4 ^ (p - 1) ≤ (2 ^ (p - 1) + 2) ^ 2`). -/
theorem buHalve_buIn (p : ℕ) (z : ℤ × ℤ) (h : buIn (2 ^ p) z) :
    buIn (2 ^ (p - 1) + 2) (buHalve z) := by
  obtain ⟨a, b⟩ := z
  simp only [buIn, buHalve] at h ⊢
  have hnat : a.natAbs ^ 2 + b.natAbs ^ 2 ≤ (2 ^ p) ^ 2 := by
    have hh : ((a.natAbs : ℕ) : ℤ) ^ 2 + ((b.natAbs : ℕ) : ℤ) ^ 2
        ≤ (((2 ^ p : ℕ) : ℤ)) ^ 2 := by
      rw [Int.natAbs_sq, Int.natAbs_sq]
      exact h
    exact_mod_cast hh
  -- truncation loses at most a factor `2` in each coordinate
  have h4 : 4 * ((a.natAbs / 2) ^ 2 + (b.natAbs / 2) ^ 2) ≤ a.natAbs ^ 2 + b.natAbs ^ 2 := by
    have h1 : 2 * (a.natAbs / 2) ≤ a.natAbs := by
      calc 2 * (a.natAbs / 2) = a.natAbs / 2 * 2 := by ring
        _ ≤ a.natAbs := Nat.div_mul_le_self _ _
    have h2 : 2 * (b.natAbs / 2) ≤ b.natAbs := by
      calc 2 * (b.natAbs / 2) = b.natAbs / 2 * 2 := by ring
        _ ≤ b.natAbs := Nat.div_mul_le_self _ _
    have e1 : (2 * (a.natAbs / 2)) ^ 2 = 4 * (a.natAbs / 2) ^ 2 := by ring
    have e2 : (2 * (b.natAbs / 2)) ^ 2 = 4 * (b.natAbs / 2) ^ 2 := by ring
    have p1 := Nat.pow_le_pow_left h1 2
    have p2 := Nat.pow_le_pow_left h2 2
    rw [e1] at p1
    rw [e2] at p2
    linarith
  have hp4 : (2 ^ p) ^ 2 = 4 ^ p := by
    rw [← Nat.pow_mul, show p * 2 = 2 * p by ring, Nat.pow_mul]
  have h4p : (2 ^ p) ^ 2 ≤ 4 * 4 ^ (p - 1) := by
    rw [hp4]
    by_cases hp : p = 0
    · subst hp; norm_num
    · have hpp : p - 1 + 1 = p := Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hp)
      have hstep : 4 ^ p = 4 * 4 ^ (p - 1) := by
        conv_lhs => rw [← hpp]
        rw [pow_succ]
        ring
      exact le_of_eq hstep
  have hAB : (a.natAbs / 2) ^ 2 + (b.natAbs / 2) ^ 2 ≤ 4 ^ (p - 1) := by
    have hchain : 4 * ((a.natAbs / 2) ^ 2 + (b.natAbs / 2) ^ 2) ≤ 4 * 4 ^ (p - 1) :=
      le_trans (le_trans h4 hnat) h4p
    exact Nat.le_of_mul_le_mul_left hchain (by norm_num)
  have hfin : 4 ^ (p - 1) ≤ (2 ^ (p - 1) + 2) ^ 2 := by
    have he : 4 ^ (p - 1) = (2 ^ (p - 1)) ^ 2 := by
      calc (4:ℕ) ^ (p - 1) = (2^2) ^ (p - 1) := by norm_num
        _ = 2 ^ (2 * (p - 1)) := (Nat.pow_mul 2 2 (p - 1)).symm
        _ = 2 ^ ((p - 1) * 2) := by rw [mul_comm]
        _ = (2 ^ (p - 1)) ^ 2 := Nat.pow_mul 2 (p - 1) 2
    rw [he]
    exact Nat.pow_le_pow_left (Nat.le_add_right _ 2) 2
  have hkey : (a.natAbs / 2) ^ 2 + (b.natAbs / 2) ^ 2 ≤ (2 ^ (p - 1) + 2) ^ 2 :=
    le_trans hAB hfin
  have hz1 : (a.tdiv 2) ^ 2 = (((a.natAbs / 2 : ℕ)) : ℤ) ^ 2 := by
    rw [← Int.natAbs_sq, Int.natAbs_tdiv]
    rfl
  have hz2 : (b.tdiv 2) ^ 2 = (((b.natAbs / 2 : ℕ)) : ℤ) ^ 2 := by
    rw [← Int.natAbs_sq, Int.natAbs_tdiv]
    rfl
  rw [hz1, hz2]
  exact_mod_cast hkey

/-- **Selection preserves the disc.**  Reading the input vector `u` (every entry in the disc of
radius `2 ^ p`) at the indices `egNu s t ℓ` and halving keeps every coordinate in the disc of
radius `2 ^ (p - 1) + 2`.  This is the size invariant needed by the selection stage `buQWsel` of
the one-dimensional `B̃` word. -/
theorem buSelLInV (p s t : ℕ) (u : List (ℤ × ℤ)) (hu : u.length = t)
    (h : Work.Resample.buInV (2 ^ p) u) :
    Work.Resample.buInV (2 ^ (p - 1) + 2) (Work.Resample.buSelL s t u) := by
  intro z hz
  rw [buSelL, List.mem_ofFn] at hz
  obtain ⟨ℓ, rfl⟩ := hz
  apply buHalve_buIn
  by_cases hlt : egNu s t (ℓ : ℕ) < u.length
  · rw [List.getD_eq_getElem _ _ hlt]
    exact h _ (List.getElem_mem hlt)
  · rw [List.getD_eq_default _ _ (Nat.le_of_not_lt hlt)]
    simp [buIn]

end Work.Resample
