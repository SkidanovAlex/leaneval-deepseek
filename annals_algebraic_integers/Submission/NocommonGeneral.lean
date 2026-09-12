import Mathlib
import Submission.Nocommon
import Submission.NocommonCore

/-!
# `lem:squarefree_nocommon` with an arbitrary lead index

`Submission.NocommonCore.nocommon_core` has the lead at index 0.  Its consumers
(`lem:second_squeeze`, `thm:squarefree`) have families whose maximum-degree
element sits at an arbitrary index `i₀`.  This wrapper permutes the family
(`Equiv.swap 0 i₀`) so the max-degree element becomes `T 0`, applies
`nocommon_core`, and maps the resulting combination back.

## Proof route
Given `hlead : ∃ i₀, (S i₀).natDegree = m`, choose such `i₀`.  Let
`σ : Equiv.Perm (Fin (K+1)) := Equiv.swap 0 i₀` and `T j := S (σ j)`.
- `T 0 = S i₀`, so `(T 0).natDegree = m`; each `(T j).natDegree ≤ m`; `T j ≠ 0`
  (from `hnz`); and no common complex root of the `T j` (since σ is a
  bijection, `hnc` transfers).
- Apply `Submission.NocommonCore.nocommon_core (S := T)` to obtain
  `bc : Fin K → ℕ` with `bc i ≤ 2m` and
  `A := T 0 + Σ_{i : Fin K} C((bc i : ℤ))·T (Fin.succ i)` satisfying
  `DistinctRootData A m`.
- Map back: `A = S i₀ + Σ_i (bc i)·S (σ (Fin.succ i))`, and as `i` ranges over
  `Fin K`, `σ (Fin.succ i)` ranges over all indices `j ≠ i₀`.  Define
  `b : Fin (K+1) → ℕ` by `b j := if j = i₀ then 1 else bc (the index i with
  σ (Fin.succ i) = j)`.  Concretely, for `j ≠ i₀`, `σ⁻¹ j ≠ 0` (because
  `σ⁻¹ i₀ = 0`), so `σ⁻¹ j = Fin.succ i` for the unique `i : Fin K` with
  `i.val + 1 = (σ⁻¹ j).val` (use `Fin.pred` on `⟨(σ⁻¹ j).val - 1, ...⟩` or
  the arithmetic of your choice).  Then `b i₀ = 1`, `∀ j, b j ≤ 2m + 1`
  (non-lead values are `bc i ≤ 2m`), and
  `Σ_j C((b j : ℤ))·S j = A`.
- Conclude with that `i₀, b`.  (You may additionally record
  `(S i₀).natDegree = m` in the output, which is just the choice of `i₀`.)

Deliver exactly the theorem below, no placeholders, axioms ⊆ {propext, Quot.sound,
Classical.choice}.  This file may import `Submission.Nocommon` (for
`DistinctRootData` and `CombPoly`) and `Submission.NocommonCore`.
-/

noncomputable section

open Polynomial
open scoped BigOperators

namespace Submission.NocommonGeneral

open Submission.Nocommon

/-- `lem:squarefree_nocommon` with an arbitrary lead index: some `b` with
`b i₀ = 1` (coefficient 1 on the maximum-degree element) and all weights
`≤ 2m+1` makes the combination squarefree of degree `m`. -/
theorem nocommon_general {m K : ℕ} (hK : 1 ≤ K) (S : Fin (K + 1) → Polynomial ℤ)
    (hnz : ∀ i, S i ≠ 0) (hdeg : ∀ i, (S i).natDegree ≤ m)
    (hlead : ∃ i₀ : Fin (K + 1), (S i₀).natDegree = m)
    (hnc : ∀ z : ℂ, ¬ (∀ i : Fin (K + 1), Polynomial.aeval z (S i) = 0)) :
    ∃ (i₀ : Fin (K + 1)) (b : Fin (K + 1) → ℕ),
      (S i₀).natDegree = m ∧ b i₀ = 1 ∧ (∀ i, b i ≤ 2 * m + 1) ∧
        DistinctRootData (∑ i : Fin (K + 1), Polynomial.C (((b i : ℕ) : ℤ)) * S i) m := by
  rcases hlead with ⟨i₀, hi₀deg⟩
  let σ : Equiv.Perm (Fin (K + 1)) := Equiv.swap 0 i₀
  let T : Fin (K + 1) → Polynomial ℤ := fun j => S (σ j)
  have hσ0 : σ 0 = i₀ := by
    simp [σ]
  have hT0 : T 0 ≠ 0 := by
    dsimp [T]
    rw [hσ0]
    exact hnz i₀
  have hTdeg : ∀ i, (T i).natDegree ≤ m := by
    intro i
    simpa [T] using hdeg (σ i)
  have hTlead : (T 0).natDegree = m := by
    dsimp [T]
    rw [hσ0]
    exact hi₀deg
  have hTnc : ∀ z : ℂ, ¬ (∀ i : Fin (K + 1), Polynomial.aeval z (T i) = 0) := by
    intro z hz
    exact hnc z (fun j => by
      have hz' := hz (σ.symm j)
      simpa [T, Equiv.apply_symm_apply] using hz')
  rcases Submission.NocommonCore.nocommon_core hK T hT0 hTdeg hTlead hTnc with ⟨bc, hbc, hA⟩
  let b : Fin (K + 1) → ℕ := fun j =>
    if h : σ.symm j = (0 : Fin (K + 1)) then 1 else bc ((σ.symm j).pred h)
  have hbσ0 : b (σ 0) = 1 := by
    dsimp [b]
    simp [Equiv.symm_apply_apply]
  have hbσsucc : ∀ i : Fin K, b (σ i.succ) = bc i := by
    intro i
    dsimp [b]
    rw [Equiv.symm_apply_apply]
    by_cases h : i.succ = 0
    · exfalso
      exact Fin.succ_ne_zero i h
    · simp [h]
  have hb1 : b i₀ = 1 := by
    rw [← hσ0]
    exact hbσ0
  have hbound : ∀ i, b i ≤ 2 * m + 1 := by
    intro j
    dsimp [b]
    by_cases hj : σ.symm j = 0
    · simp [hj]
    · simp [hj]
      exact le_trans (hbc ((σ.symm j).pred hj)) (by omega)
  have hsum :
      (∑ j : Fin (K + 1), Polynomial.C (((b j : ℕ) : ℤ)) * S j)
        = T 0 + ∑ i : Fin K, Polynomial.C (((bc i : ℕ) : ℤ)) * T i.succ := by
    calc
      (∑ j : Fin (K + 1), Polynomial.C (((b j : ℕ) : ℤ)) * S j)
          = ∑ x : Fin (K + 1), Polynomial.C (((b (σ x) : ℕ) : ℤ)) * S (σ x) := by
            rw [Equiv.sum_comp σ (fun j : Fin (K + 1) => Polynomial.C (((b j : ℕ) : ℤ)) * S j)]
      _ = ∑ x : Fin (K + 1), Polynomial.C (((b (σ x) : ℕ) : ℤ)) * T x := by
            apply Finset.sum_congr rfl
            intro x hx
            simp [T]
      _ = Polynomial.C (((b (σ 0) : ℕ) : ℤ)) * T 0 +
            ∑ i : Fin K, Polynomial.C (((b (σ i.succ) : ℕ) : ℤ)) * T i.succ := by
            rw [Fin.sum_univ_succ]
      _ = T 0 + ∑ i : Fin K, Polynomial.C (((bc i : ℕ) : ℤ)) * T i.succ := by
            rw [hbσ0]
            simp
            apply Finset.sum_congr rfl
            intro i hi
            rw [hbσsucc i]
  refine ⟨i₀, b, hi₀deg, hb1, hbound, ?_⟩
  rw [hsum]
  exact hA

end Submission.NocommonGeneral
