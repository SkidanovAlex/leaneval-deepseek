/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gorenstein–Walter formalisation team (area FUS, `Work.FUS`)

# The reflection sign on a dihedral group, and small arithmetic helpers

`Work.FUS.reflSign n : DihedralGroup n →* Multiplicative (ZMod 2)` is the character which is
`1` on the rotation subgroup `Work.Dihedral.rot n` and `-1` on the reflections. Its kernel is
`rot n` (`Work.FUS.ker_reflSign`). This is the `σ` used by Thompson's transfer lemma
(`Work.FUS.thompson_transfer`) in the proof of `Work.GW2.InvolutionFusionProp`.
-/
import Mathlib
import Submission.Work.Dihedral.Defs

namespace Work.FUS

open DihedralGroup

/-! ## The reflection sign -/

/-- The "reflection sign": `1` on `r i`, `-1` on `sr i`. It is a group homomorphism onto the
two-element group, with kernel `Work.Dihedral.rot n`. -/
def reflSign (n : ℕ) : DihedralGroup n →* Multiplicative (ZMod 2) where
  toFun x := match x with
    | .r _ => 1
    | .sr _ => Multiplicative.ofAdd (1 : ZMod 2)
  map_one' := rfl
  map_mul' := by
    intro a b
    match a, b with
    | .r i, .r j => simp [DihedralGroup.r_mul_r]
    | .r i, .sr j => simp [DihedralGroup.r_mul_sr]
    | .sr i, .r j => simp [DihedralGroup.sr_mul_r]
    | .sr i, .sr j =>
        simp only [DihedralGroup.sr_mul_sr]
        decide

@[simp] lemma reflSign_r (n : ℕ) (i : ZMod n) :
    reflSign n (DihedralGroup.r i) = 1 := rfl

@[simp] lemma reflSign_sr (n : ℕ) (i : ZMod n) :
    reflSign n (DihedralGroup.sr i) = Multiplicative.ofAdd (1 : ZMod 2) := rfl

/-- The kernel of the reflection sign is the rotation subgroup. -/
lemma ker_reflSign (n : ℕ) : (reflSign n).ker = Work.Dihedral.rot n := by
  ext x
  constructor
  · intro hx
    rcases Work.Dihedral.eq_r_or_sr x with ⟨i, rfl⟩ | ⟨i, rfl⟩
    · exact Work.Dihedral.r_mem_rot i
    · exfalso
      have h := hx
      simp only [MonoidHom.mem_ker, reflSign_sr] at h
      exact absurd h (by decide)
  · intro hx
    rcases Work.Dihedral.mem_rot.mp hx with ⟨i, rfl⟩
    simp

/-- In the two-element group `Multiplicative (ZMod 2)` every element is `1` or the generator. -/
lemma mulTwo_eq_one_or (x : Multiplicative (ZMod 2)) :
    x = 1 ∨ x = Multiplicative.ofAdd (1 : ZMod 2) := by
  induction x using Multiplicative.rec with
  | ofAdd a =>
      fin_cases a
      · exact Or.inl rfl
      · exact Or.inr rfl

/-! ## Arithmetic -/

/-- If `2 * n = 2 ^ k` and `n ≥ 2`, then `n` is even. -/
lemma even_of_two_mul_eq_two_pow {n k : ℕ} (hn : 2 ≤ n) (h : 2 * n = 2 ^ k) : Even n := by
  have hk : 1 ≤ k := by
    rcases Nat.eq_zero_or_pos k with hk | hk
    · subst hk; simp at h
    · exact hk
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  have hn' : n = 2 ^ m := by
    rw [pow_succ'] at h
    exact Nat.mul_left_cancel (by norm_num : 0 < (2 : ℕ)) h
  subst hn'
  rcases Nat.eq_zero_or_pos m with hm | hm
  · subst hm; simp at hn
  · refine ⟨2 ^ (m - 1), ?_⟩
    have hmul : 2 ^ m = 2 * 2 ^ (m - 1) := by
      rw [← pow_succ']
      congr 1
      omega
    omega

end Work.FUS
