import Mathlib
import Submission.Work.Diff.STE.B3.SymCalcStep8.CSqZ
import Submission.Work.Diff.STE.B3.SymCalcStep8.perTransfer_csq_le_of_support
import Submission.Work.Diff.STE.B3.SymCalcStep8.perTransfer_CSqZ_neg_le
import Submission.Work.Diff.STE.B3.SymCalcStep8.periodization_compact_contDiff

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.STE.B3.SymCalcStep8

/-- The local chart transfer is bounded on **every** Sobolev level `H^t`, `t : ℤ`.

This is the all-integer-exponent amalgamation of the two existing estimates: the positive range
`t ≥ 0` is `perTransfer_csq_le_of_support` (which is stated with `CSq`, translated here into `CSqZ`
by `CSqZ_natCast`), and the negative range `t < 0` is `perTransfer_CSqZ_neg_le` (stated directly in
terms of `CSqZ`).  The smoothness and `1`-periodicity of `perTransfer c T W` are supplied in both
cases by `perTransfer_contDiff_periodic_of` (they do not depend on the value of `t`). -/
theorem perTransfer_CSqZ_le_all {ι : Type*} [Fintype ι] [DecidableEq ι]
    (c : (ι → ℝ) → ℂ) (hc : ContDiff ℝ (⊤ : ℕ∞) c) (hcs : HasCompactSupport c)
    (T : (ι → ℝ) → (ι → ℝ)) (hT : ContDiff ℝ (⊤ : ℕ∞) T)
    (hinj : Set.InjOn T (tsupport c))
    (hdet : ∀ z ∈ tsupport c, (fderiv ℝ T z).det ≠ 0) (t : ℤ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ W : (ι → ℝ) → ℂ, ContDiff ℝ (⊤ : ℕ∞) W → Work.Diff.STE.Periodic1 W →
      ContDiff ℝ (⊤ : ℕ∞) (Work.Diff.STE.B3.perTransfer c T W) ∧
      Work.Diff.STE.Periodic1 (Work.Diff.STE.B3.perTransfer c T W) ∧
      Work.Diff.STE.B3.SymCalcStep8.CSqZ t
          (Work.Diff.STE.fourierCoeff (Work.Diff.STE.B3.perTransfer c T W))
        ≤ C * Work.Diff.STE.B3.SymCalcStep8.CSqZ t (Work.Diff.STE.fourierCoeff W) := by
  classical
  rcases le_total (0 : ℤ) t with ht | ht
  · -- ## Non-negative exponents: reduce to the `H^t` bound `perTransfer_csq_le_of_support`
    obtain ⟨C, hC, hCb⟩ :=
      Work.Diff.STE.B3.SymCalcStep8.perTransfer_csq_le_of_support c hc hcs T hT hinj hdet t.toNat
    refine ⟨C, hC, fun W hW hWp => ⟨?_, ?_, ?_⟩⟩
    · exact (Work.Diff.STE.B3.SymCalcStep8.perTransfer_contDiff_periodic_of
        c hc hcs T hT W hW hWp).1
    · exact (Work.Diff.STE.B3.SymCalcStep8.perTransfer_contDiff_periodic_of
        c hc hcs T hT W hW hWp).2
    · have ht' : ((t.toNat : ℕ) : ℤ) = t := Int.toNat_of_nonneg ht
      rw [← ht', Work.Diff.STE.B3.SymCalcStep8.CSqZ_natCast,
        Work.Diff.STE.B3.SymCalcStep8.CSqZ_natCast]
      exact hCb W hW hWp
  · -- ## Negative exponents: reduce to the duality bound `perTransfer_CSqZ_neg_le`
    obtain ⟨C, hC, hCb⟩ :=
      Work.Diff.STE.B3.SymCalcStep8.perTransfer_CSqZ_neg_le c hc hcs T hT hinj hdet (-t).toNat
    have ht' : -((((-t).toNat : ℕ) : ℤ)) = t := by
      have h : (((-t).toNat : ℕ) : ℤ) = -t := Int.toNat_of_nonneg (by omega)
      omega
    refine ⟨C, hC, fun W hW hWp => ⟨?_, ?_, ?_⟩⟩
    · exact (Work.Diff.STE.B3.SymCalcStep8.perTransfer_contDiff_periodic_of
        c hc hcs T hT W hW hWp).1
    · exact (Work.Diff.STE.B3.SymCalcStep8.perTransfer_contDiff_periodic_of
        c hc hcs T hT W hW hWp).2
    · rw [← ht']
      exact hCb W hW hWp

end Work.Diff.STE.B3.SymCalcStep8
