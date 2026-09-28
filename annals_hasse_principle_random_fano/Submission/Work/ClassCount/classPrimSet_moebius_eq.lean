import Mathlib
import Submission.Work.HP.PFCountDefs
import Submission.Work.HP.DNC.moebius_prim_ncard
import Submission.Work.HP.eNorm_veronese_bounds
import Submission.Work.HP.Psi

namespace Work.ClassCount

open Finset

/-- Möbius identity for `classPrimSet`: the exact identity

`#classPrimSet d n a b W α R = Σ_{k ∈ Icc 1 ⌊R⌋₊} μ(k) · mobiusCount d n a b W k α R` (in `ℝ`),
obtained from `Work.HP.DNC.moebius_prim_ncard` with `ι := Fin (n+1)`,
`K := {t : Fin (n+1) → ℝ | toR a ∈ Cgam (veronese d n t) α}`,
`P v := ∀ i, (W : ℤ) ∣ v i - b i`, `A := R`.

Route: `hK` is `Cgam_veronese_const_mul` (plus `(s • t) = fun i => s * t i`); the LHS set is
`classPrimSet` after rewriting with `Work.HP.toR_veronese`; each `k`-th summand set is
`mobiusCount` after rewriting `((k : ℤ) • z) i = (k : ℤ) * z i` and again `toR_veronese`. -/
theorem classPrimSet_moebius_eq (d n : ℕ) (a : Work.HP.Mon d n → ℤ) (b : Fin (n + 1) → ℤ)
    (W : ℕ) (α R : ℝ) (hR : 0 ≤ R) :
    ((Work.HP.classPrimSet d n a b W α R).ncard : ℝ)
      = ∑ k ∈ Finset.Icc 1 ⌊R⌋₊,
          (ArithmeticFunction.moebius k : ℝ) * ((Work.HP.mobiusCount d n a b W k α R : ℕ) : ℝ) := by
  classical
  -- The cone condition is invariant under positive scalings of the real variable.
  have hK : ∀ (s : ℝ) (t : Fin (n + 1) → ℝ), 0 < s →
      (Work.HP.toR a ∈ Work.HP.Cgam (Work.HP.veronese d n t) α ↔
       Work.HP.toR a ∈ Work.HP.Cgam (Work.HP.veronese d n (s • t)) α) := by
    intro s t hs
    rw [show (s • t : Fin (n + 1) → ℝ) = fun i => s * t i from by
      funext i; simp [Pi.smul_apply, smul_eq_mul]]
    exact (Work.HP.Cgam_veronese_const_mul a hs t).symm
  have hmain := Work.HP.DNC.moebius_prim_ncard (ι := Fin (n + 1))
    {t : Fin (n + 1) → ℝ | Work.HP.toR a ∈ Work.HP.Cgam (Work.HP.veronese d n t) α} hK
    (fun v : Fin (n + 1) → ℤ => ∀ i, (W : ℤ) ∣ v i - b i) R hR
  -- The left-hand set of `moebius_prim_ncard` is exactly `classPrimSet`.
  have hL : Work.HP.classPrimSet d n a b W α R =
      {v : Fin (n + 1) → ℤ | Work.HP.IsPrim v ∧ Work.HP.eNorm v ≤ R ∧
        Work.HP.toR v ∈
          {t : Fin (n + 1) → ℝ | Work.HP.toR a ∈ Work.HP.Cgam (Work.HP.veronese d n t) α} ∧
        (∀ i, (W : ℤ) ∣ v i - b i)} := by
    ext v
    simp only [Work.HP.classPrimSet, Set.mem_ofPred_eq, Work.HP.toR_veronese]
    tauto
  rw [hL, hmain]
  -- Each Möbius summand set is exactly the set whose cardinality is `mobiusCount`.
  apply Finset.sum_congr rfl
  intro k _
  congr 1
  have hS : {z : Fin (n + 1) → ℤ | z ≠ 0 ∧ Work.HP.eNorm z ≤ R / (k : ℝ) ∧
        Work.HP.toR z ∈
          {t : Fin (n + 1) → ℝ | Work.HP.toR a ∈ Work.HP.Cgam (Work.HP.veronese d n t) α} ∧
        (∀ i, (W : ℤ) ∣ ((k : ℤ) • z) i - b i)}
      = {z : Fin (n + 1) → ℤ | z ≠ 0 ∧ (∀ i, (W : ℤ) ∣ (k : ℤ) * z i - b i) ∧
        Work.HP.eNorm z ≤ R / (k : ℝ) ∧
        Work.HP.toR a ∈ Work.HP.Cgam (Work.HP.toR (Work.HP.veronese d n z)) α} := by
    ext z
    simp only [Set.mem_ofPred_eq, Work.HP.toR_veronese, Pi.smul_apply, smul_eq_mul]
    tauto
  rw [hS]
  rfl

end Work.ClassCount
