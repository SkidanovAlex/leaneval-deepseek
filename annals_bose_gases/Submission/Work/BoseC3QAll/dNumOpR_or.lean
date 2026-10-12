import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Module.LinearMap.Defs
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Submission.Work.BoseC3QAll.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseC3QAll.dNumOpR_or` — the additivity of the diagonal reserve

`F.dNumOpR E R = ∑_{i ∈ excited, R i} E.D i • b_i†b_i` is a sum over a *filtered*
mode set, so it is **additive over disjoint regions**:

  `dNumOpR (R ∨ S) + dNumOpR (R ∧ S) = dNumOpR R + dNumOpR S`,

whence for disjoint `R`, `S` (the case used by the C3Q assembly, where the
reserve lives on `RHi ∖ P_H^q` and the diagonal of the targeted word on `RHi`):

  `dNumOpR (R ∨ S) = dNumOpR R + dNumOpR S`.

This is what lets the `§10` bookkeeping split the coefficient budget on `RHi`
into the pieces `P_H^q` and `RHi ∖ P_H^q`; without it only the monotonicity
`dNumOpR_mono` is available, and the coefficients `(1−𝓁²)` on `P_H`, `𝓁²` on
`P_H^q` and `½` on `RHi ∖ P_H^q` would sum to `3/2` instead of `1`.
-/

noncomputable section

open scoped BigOperators


namespace Work.BoseC3QAll

open Work.BoseB7

/-- **Additivity of the diagonal reserve over regions.** -/
theorem dNumOpR_or {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
    (F : FockData Mode) (E : Q3Env Mode) (R S : Mode → Prop) [DecidablePred R]
    [DecidablePred S] :
    F.dNumOpR E (fun i => R i ∨ S i) + F.dNumOpR E (fun i => R i ∧ S i)
      = F.dNumOpR E R + F.dNumOpR E S := by
  simp only [FockData.dNumOpR, FockData.regionSum, Finset.sum_filter]
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases hp : R i <;> by_cases hq : S i <;> simp [hp, hq]

/-- **Additivity of the diagonal reserve over disjoint regions.** -/
theorem dNumOpR_disj {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
    (F : FockData Mode) (E : Q3Env Mode) (R S : Mode → Prop) [DecidablePred R]
    [DecidablePred S] (h : ∀ i, ¬ (R i ∧ S i)) :
    F.dNumOpR E (fun i => R i ∨ S i) = F.dNumOpR E R + F.dNumOpR E S := by
  have hemp : F.dNumOpR E (fun i => R i ∧ S i) = 0 := by
    simp only [FockData.dNumOpR, FockData.regionSum]
    rw [Finset.filter_false_of_mem]
    · simp
    · intro i _ hi
      exact h i hi
  have h1 := dNumOpR_or F E R S
  rw [hemp, add_zero] at h1
  exact h1

/-- The reserve region `RHi = P_H^q ∪ (RHi ∖ P_H^q)` is the disjoint union of its
`P_H^q` part and its complement. -/
theorem dNumOpR_RHi {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
    (F : FockData Mode) (E : Q3Env Mode)
    (hPHq : ∀ i : Mode, F.PHq E.KH E.aScat i → RHi F E i) :
    F.dNumOpR E (fun k => RHi F E k ∧ ¬ F.PHq E.KH E.aScat k) + F.dNumOpR E (F.PHq E.KH E.aScat)
      = F.dNumOpR E (RHi F E) := by
  have h := dNumOpR_disj F E (R := F.PHq E.KH E.aScat)
    (S := fun k => RHi F E k ∧ ¬ F.PHq E.KH E.aScat k) (fun i hi => hi.2.2 hi.1)
  have hEq : F.dNumOpR E (fun i => F.PHq E.KH E.aScat i ∨ (RHi F E i ∧ ¬ F.PHq E.KH E.aScat i))
      = F.dNumOpR E (RHi F E) := by
    congr 1
    ext k
    by_cases hq : F.PHq E.KH E.aScat k
    · refine iff_of_true ?_ (hPHq k hq)
      exact Or.inl hq
    · simp only [hq, false_or, not_false_eq_true, and_true]
  rw [← hEq]
  exact (add_comm _ _).trans h.symm

end Work.BoseC3QAll
