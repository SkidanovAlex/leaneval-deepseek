/-
  WilG4cR / `UvfixGlue` — a **clean** copy of `Work.WilkG4c.CritFixAux.uvfixGlue`
  (`Submission/Work/WilG4c/CritFixAux/uvfixGlue.lean`), which is `sorry`-free but imports the
  currently non-building `CritFixAux/limcond_fix_mem.lean`; the copy below uses the repaired
  `Work.WilG4cR.limcond_fix_mem` instead.

  `UVFix p n f k` is the value-free corrected criterion: the *value* (continuity) factor
  `contSet p n f` intersected with the limit conditions `LimCond p n f (m+1) c` over the whole
  index set `critIdxFix n k` (counts vectors with entries `≤ m`).  The three factors are
  `Ω`-definable with format/degree uniform in the index (`contSetMem`, `limcond_fix_mem`), and
  the `Finset`-indexed intersection is `Work.WilG4cR.finset_inter_mem`; the cardinality
  `#(critIdxFix n k) ≤ (k+2)^{n+2}` (`card_critIdxFix_le`) is absorbed into the degree
  polynomial `(X₁+2)^{n+2} · bL`.
-/
import Mathlib
import Submission.Work.Wilkies.Defs
import Submission.Work.WilG4c.AlSliceBase
import Submission.Work.WilG4c.CritFixDefs
import Submission.Work.WilG4c.CritMem
import Submission.Work.WilG4c.fibreLimitEqMem_pi
import Submission.Work.WilG4c.CritFixAux.critIdxFixCard
import Submission.Work.WilG4c.CritFixAux.contSetMem
import Submission.Work.WilG4cR.finset_inter_mem
import Submission.Work.WilG4cR.LimcondFixMem
import Submission.Work.WilG1.Basic

set_option autoImplicit false
noncomputable section
open Classical

namespace Work.WilG4cR

open WilkiesDesign WilkiesDesign.CG

/-- The evaluation of `(X₁ + 2)^{n+2}` at `![D,k]` is `(k+2)^{n+2}`. -/
theorem eval_X1_add_two_pow (n D k : ℕ) :
    MvPolynomial.eval ![D, k]
        ((MvPolynomial.X (1 : Fin 2) + MvPolynomial.C 2) ^ (n + 2))
      = (k + 2) ^ (n + 2) := by
  simp [MvPolynomial.eval_pow, MvPolynomial.eval_add, MvPolynomial.eval_X, MvPolynomial.eval_C,
    Matrix.cons_val_one]

/-- **`UVFix` is `Ω`-definable.** -/
theorem uvfixGlue (S : WilkiesDesign.SOMin) (hder : WilkiesDesign.SOMin.SharpDeriv S)
    (p n F0 : ℕ) :
    ∃ (a : ℕ) (b : MvPolynomial (Fin 2) ℕ), ∀ (D k : ℕ)
      (f : (Fin p → ℝ) → (Fin (n + 1) → ℝ) → ℝ),
      WilkiesDesign.CG.famGraph f ∈ S.Ω F0 D (p + (n + 1) + 1) →
      Work.WilkG4c.UVFix p n f k ∈ S.Ω a (MvPolynomial.eval ![D, k] b) (p + (n + 1)) := by
  obtain ⟨aC, bC, hC⟩ := Work.WilkG4c.CritFixAux.contSetMem S p n F0
  obtain ⟨aL, bL, hL⟩ := Work.WilG4cR.limcond_fix_mem S hder p n F0
  refine ⟨max aC (aL + 1) + 1,
    bC + (MvPolynomial.X (1 : Fin 2) + MvPolynomial.C 2) ^ (n + 2) * bL, ?_⟩
  intro D k f hf
  have hcon := hC D k f hf
  -- the intersection of all limit conditions of the index set
  have hLim : (⋂ i ∈ Work.WilkG4c.critIdxFix n k,
      Work.WilkG4c.LimCond p n f (i.1.val + 1) (fun j => (i.2 j).val)) ∈
      S.Ω (aL + 1) (MvPolynomial.eval ![D, k]
        (MvPolynomial.C (Work.WilkG4c.critIdxFix n k).card * bL)) (p + (n + 1)) :=
    Work.WilG4cR.finset_inter_mem _ _ (fun i _ => hL D k f i hf)
  -- the cardinality step: `#(critIdxFix n k) · bL ≤ (k+2)^{n+2} · bL`
  have hcard : MvPolynomial.eval ![D, k]
        (MvPolynomial.C (Work.WilkG4c.critIdxFix n k).card * bL)
      ≤ MvPolynomial.eval ![D, k]
        ((MvPolynomial.X (1 : Fin 2) + MvPolynomial.C 2) ^ (n + 2) * bL) := by
    rw [MvPolynomial.eval_mul, MvPolynomial.eval_mul, MvPolynomial.eval_C,
      eval_X1_add_two_pow]
    exact Nat.mul_le_mul_right _ (Work.WilkG4c.CritFixAux.card_critIdxFix_le n k)
  have hLim' := Work.WilG1.Omega.mono hLim le_rfl hcard
  have hboth := Work.WilkG4c.inter_mv hcon hLim'
  rw [Work.WilkG4c.UVFix]
  exact hboth

end Work.WilG4cR
