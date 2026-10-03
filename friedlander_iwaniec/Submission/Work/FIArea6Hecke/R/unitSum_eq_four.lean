import Mathlib
import Submission.Work.FIArea5.S16Hecke.ThetaDefs
import Submission.Work.FIArea5.S16Hecke.Defs

open Finset
open scoped BigOperators

namespace Work.FIArea6Hecke.R

open Work.FIArea5.S16Hecke

/-- **The unit sum at `m = 0` is the sum of `χ` over the four units**: for `m = 0` the factor
`u^m = 1` drops out and `μ₄ = {1, -1, i, -i}`. -/
lemma unitSum_zero_expand {chi : GaussianInt → ℂ} :
    unitSum chi 0 = chi 1 + chi (-1) + chi (⟨0,1⟩ : GaussianInt) + chi (⟨0,-1⟩ : GaussianInt) := by
  rw [unitSum]
  simp only [pow_zero, mul_one]
  rw [units4, Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_singleton]
  ring

/-- **`unitSum χ 0 ∈ {0, 4}`**.  Writing `a = χ(i)`, multiplicativity of `χ` gives
`χ(-1) = a²`, `χ(-i) = a³` and `a⁴ = χ(i⁴) = χ(1) = 1`; hence
`unitSum χ 0 = 1 + a² + a + a³` satisfies `(a-1)·unitSum χ 0 = a⁴ - 1 = 0`.
So `unitSum χ 0 = 0` unless `a = 1`, and in the latter case all four summands are `1`
and the sum is `4`. -/
theorem unitSum_eq_four {d : ℕ} {chi : GaussianInt → ℂ}
    (hchi : Work.FIArea5.S16Hecke.IsCharMod4dStrict d chi)
    (hU : Work.FIArea5.S16Hecke.unitSum chi 0 ≠ 0) :
    Work.FIArea5.S16Hecke.unitSum chi 0 = 4 := by
  have hmod : Work.FITop3.IsCharMod4d d chi := hchi.1
  have hone : chi 1 = 1 := hmod.1
  have hmul : ∀ z w : GaussianInt, chi (z * w) = chi z * chi w := hmod.2.1
  have hpow : ∀ (z : GaussianInt) (k : ℕ), chi (z ^ k) = chi z ^ k := by
    intro z k
    induction k with
    | zero => simp [hone]
    | succ k ih => rw [pow_succ', hmul, ih, pow_succ']
  set a : ℂ := chi ⟨0,1⟩ with ha_def
  have hneg1 : chi (-1 : GaussianInt) = a ^ 2 := by
    have h : (-1 : GaussianInt) = (⟨0,1⟩ : GaussianInt) ^ 2 := by decide
    rw [h, hpow]
  have hnegi : chi (⟨0,-1⟩ : GaussianInt) = a ^ 3 := by
    have h : (⟨0,-1⟩ : GaussianInt) = (⟨0,1⟩ : GaussianInt) ^ 3 := by decide
    rw [h, hpow]
  have ha4 : a ^ 4 = 1 := by
    rw [ha_def, ← hpow]
    have h4 : (⟨0,1⟩ : GaussianInt) ^ 4 = 1 := by decide
    rw [h4, hone]
  have hS : unitSum chi 0 = 1 + a ^ 2 + a + a ^ 3 := by
    rw [unitSum_zero_expand, hone, hneg1, hnegi]
  have hkey : (a - 1) * (unitSum chi 0) = 0 := by
    rw [hS]
    have : (a - 1) * (1 + a ^ 2 + a + a ^ 3) = a ^ 4 - 1 := by ring
    rw [this, ha4]; ring
  have ha1 : a = 1 := by
    rcases mul_eq_zero.mp hkey with h | h
    · linear_combination h
    · exact absurd h hU
  rw [hS, ha1]; norm_num

end Work.FIArea6Hecke.R
