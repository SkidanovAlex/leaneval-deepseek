/-
  WilG4c / `CritFixAux.contSetMem` — `Ω`-definability of the value (continuity) factor `contSet`
  of the (corrected) punctured-limit criterion, with format/degree bounds that are *uniform in
  the order bound* `k` (the set does not depend on `k`, so the degree polynomial may be taken
  constant in `k`).

  `contSet p n f = projLast (LimeqP p n (famGraph f) ∩ famGraph f)` (`AlSliceBase`), so this is
  `fibreLimitEqMem_pi` applied to the hypothesis `famGraph f ∈ S.Ω F0 D _`, intersected with
  `famGraph f` itself and then projected.  The two-variable degree polynomial encoding the
  result is `bL.eval₂ C (X 0) + X 0`, whose evaluation at `![D,k]` is `bL.eval D + D`.

  This is the first of the three factors of `UVFix` (`CritFixDefs`); the other two (the uniform
  per-index limit condition and the cardinality bookkeeping of the finset intersection) are
  `CritFixAux.limcond_fix_mem` and `CritFixAux.finset_inter_mem`.
-/
import Mathlib
import Submission.Work.Wilkies.Defs
import Submission.Work.WilG4c.AlSliceBase
import Submission.Work.WilG4c.CritMem
import Submission.Work.WilG4c.fibreLimitEqMem_pi
import Submission.Work.WilG1.Basic

set_option autoImplicit false
noncomputable section
open Classical

namespace Work.WilkG4c.CritFixAux

open WilkiesDesign WilkiesDesign.CG

/-- The value factor `contSet` of the criterion is `Ω`-definable, uniformly: one fixed format
and one fixed two-variable degree polynomial work for all `D`, `k` and `f` (given the graph of
`f` at format `F0`, degree `D`). -/
theorem contSetMem (S : WilkiesDesign.SOMin) (p n F0 : ℕ) :
    ∃ (a : ℕ) (b : MvPolynomial (Fin 2) ℕ), ∀ (D k : ℕ)
      (f : (Fin p → ℝ) → (Fin (n + 1) → ℝ) → ℝ),
      WilkiesDesign.CG.famGraph f ∈ S.Ω F0 D (p + (n + 1) + 1) →
      Work.WilkG4c.contSet p n f ∈ S.Ω a (MvPolynomial.eval ![D, k] b) (p + (n + 1)) := by
  obtain ⟨aL, bL, hL⟩ := Work.WilG4c.fibreLimitEqMem_pi (S := S) (p := p) (n := n)
  refine ⟨F0 + aL + 2,
    bL.eval₂ MvPolynomial.C (MvPolynomial.X (0 : Fin 2)) + MvPolynomial.X (0 : Fin 2), ?_⟩
  intro D k f hf
  -- `LimeqP p n (famGraph f)` is `Ω`-definable with the bound `bL.eval D`
  have h1 : Work.WilG4c.LimeqP p n (WilkiesDesign.CG.famGraph f) ∈
      S.Ω (F0 + aL) (bL.eval D) (p + (n + 1) + 1) := by
    simpa only [Work.WilG4c.LimeqP] using hL (WilkiesDesign.CG.famGraph f) hf
  -- intersect with the graph itself and project the value coordinate away
  have h2 : (WilkiesDesign.CG.famGraph f) ∈
      S.Ω F0 (Polynomial.eval D Polynomial.X) (p + (n + 1) + 1) := by
    simpa only [Polynomial.eval_X] using hf
  have h3 : (Work.WilG4c.LimeqP p n (WilkiesDesign.CG.famGraph f) ∩
      WilkiesDesign.CG.famGraph f) ∈
      S.Ω (max (F0 + aL) F0 + 1) ((bL + Polynomial.X).eval D) (p + (n + 1) + 1) :=
    Work.WilG1.Omega.inter₂ h1 h2
  have h4 := S.proj h3
  -- bookkeeping: the format and the degree agree with the declared `a` and `b`
  have hmax : max (F0 + aL) F0 + 1 + 1 ≤ F0 + aL + 2 := by omega
  have hdeg : MvPolynomial.eval ![D, k]
        (bL.eval₂ MvPolynomial.C (MvPolynomial.X (0 : Fin 2)) + MvPolynomial.X (0 : Fin 2))
      = (bL + Polynomial.X).eval D := by
    simp only [MvPolynomial.eval_add, Work.WilkG4c.eval_eval₂, MvPolynomial.eval_X,
      Polynomial.eval_add, Polynomial.eval_X, Matrix.cons_val_zero]
  rw [hdeg]
  exact Work.WilG1.Omega.mono h4 hmax le_rfl

end Work.WilkG4c.CritFixAux
