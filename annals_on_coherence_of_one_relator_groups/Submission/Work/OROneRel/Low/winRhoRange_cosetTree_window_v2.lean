/-
Copyright: subproject `OROneRel` -- one-relator combinatorics (node N2).

# The free-group (`F α`) half of the window splitting, carrying the case hypotheses of the residual

This module states `Work.OROneRel.Low.winRhoRange_cosetTree_window_v2` -- the **free-group half**
(`P-A`) of the `Z`-domain splitting of the residual of `Work.OROneRel.magnus_step_root`:

  for window data `(c, Wt, lo, hi, u, l)` of the band of the walk of `u`, with `hA` (the window
  Freiheitssatz) and the *case hypotheses* of the residual (`hu`, `hcyc`, `hn`, `hbad`, `hnd`,
  `hnlo`, `hocc`, `hnfk`, `hnc`), and for **every** deck element `τ` of weight one whose decorated
  walk lies in the window, the coset graph `Coset ((winRho Wt c lo hi).range) τ` of the pair
  (window vertex of the free group, `τ`) is a **tree**.

Equivalently: `F α` is the HNN extension of its subgroup `(winRho Wt c lo hi).range` along `τ`
(the graph-of-spaces / line-of-pieces step of Linton's *One-relator hierarchies*, arXiv 2202.11324,
Prop. 2.2.19 and 4.3).

## Why this (duplicated) statement exists

The same statement is stated in `Submission/Work/OROneRel/winRhoRange_cosetTree_window_v2.lean`,
but that file imports `Submission.Work.OROneRel.magnus_step_root` -- only because the case
predicates `FreeKernelCase`/`NielsenCountCase` occurred in its hypotheses.  With those predicates
moved to the *lower* module `Submission.Work.OROneRel.magnusCaseDefs`, the statement is available
*below* `magnus_step_root`, which is exactly what its residual needs: combined with the generation
half `Work.OROneRel.Low.winVertex_generation_exists_windowWalk_v2` (in
`Submission/Work/OROneRel/winVertexGenerationLow.lean`) and the assembly
`Work.OROneRel.Low.magnus_residual_winTreeSplitting_of_freeTree`
(`Submission/Work/OROneRel/winTreeSplittingLow.lean`, proved) plus
`Work.OROneRel.exists_split_of_cosetTree` (`Submission/Work/OROneRel/split_of_cosetTree.lean`,
proved), it yields the pair form of the window splitting consumed by `magnus_step_root`.

The mathematical content is unchanged, and the intended proof is the same as the one of the original
statement; the helper lemmas that were used in that file (`tau_mul_Wt_one_inv_mem_range`,
`isTree_tau_iff_Wt_one`, `adjC_doubleCoset`, ...) are deliberately *not* duplicated here: the
assembly below `magnus_step_root` does not need them, because this statement quantifies over all
admissible `τ` (so the generation half may pick the `τ`).
-/
import Mathlib
import Submission.Work.OROneRel.winBasisDefs
import Submission.Work.OROneRel.winAssembly
import Submission.Work.OROneRel.graded_hnn_coset
import Submission.Work.OROneRel.magnusCaseDefs
import Submission.Work.OROneRel.twoLetter_F2_generation
import Submission.Work.OROneRel.decor_invRev
import Submission.Work.OROneRel.coedgeBase
import Submission.Work.OROneRel.coverCoedgeDev
import Submission.Work.ORBassSerre.Tree.Basic

namespace Work.OROneRel

namespace Low

universe u

set_option autoImplicit false

theorem winRhoRange_cosetTree_window_v2 {α : Type u} [Fintype α] [DecidableEq α]
    (u : FreeGroup α) (l : ℕ) (hl : 1 ≤ l)
    (hu : ¬ Work.OROneRel.IsProperPower u)
    (hcyc : Work.OROneRel.IsCyclicallyReducedRelator u)
    (hn : 2 ≤ Work.OROneRel.relatorNorm u)
    (hbad : ∀ x : α, x ∈ Work.OROneRel.relatorLetters u → Work.OROneRel.eps x u ≠ 0)
    (hnd : ∀ (t : α) (c : α → ℤ), t ∈ Work.OROneRel.relatorLetters u → c t = 1 →
      Work.OROneRel.cohom c u ≠ 1)
    (hnlo : ∀ (x : α) (b : Bool), (FreeGroup.toWord u).count (x, b) = 1 →
      (FreeGroup.toWord u).count (x, Bool.not b) ≠ 0)
    (hocc : ∀ x : α, x ∈ Work.OROneRel.relatorLetters u)
    (hnfk : ¬ Work.OROneRel.FreeKernelCase u l)
    (hnc : ¬ Work.OROneRel.NielsenCountCase u)
    {c : α → ℤ} (hcu : Work.OROneRel.cohom c u = 1)
    {Wt : ℤ → FreeGroup α} {lo hi : ℤ} (hW0 : Wt 0 = 1)
    (hcoh : ∀ i : ℤ, Work.OROneRel.cohom c (Wt i) = Multiplicative.ofAdd i)
    (hwin : ∀ p ∈ Work.OROneRel.decor c 0 (Work.OROneRel.wordOf u),
      Work.OROneRel.coverEdge p ∈ Work.OROneRel.winE c lo hi)
    (hone : ∀ k : ℤ, k ≠ 0 →
      ¬ (∀ p ∈ Work.OROneRel.decor c 0 (Work.OROneRel.wordOf u),
          lo ≤ p.1.2 + k ∧ lo ≤ p.1.2 + c p.1.1 + k ∧
            p.1.2 + k ≤ hi ∧ p.1.2 + c p.1.1 + k ≤ hi))
    (htree : ∀ i : ℤ, lo ≤ i → i ≤ hi →
      ∀ q ∈ Work.OROneRel.decor c 0 (Work.OROneRel.wordOf (Wt i)),
        Work.OROneRel.coverEdge q ∈ Work.OROneRel.winTree Wt c lo hi)
    (hcov : ∀ x : α, ∃ i : ℤ, (x, i) ∈ Work.OROneRel.winE c lo hi)
    (hlast : ∃ p ∈ Work.OROneRel.decor c 0 (Work.OROneRel.wordOf u),
      Work.OROneRel.coverEdge p ∈ Work.OROneRel.winTree Wt c lo hi)
    (hlo1 : lo ≤ 1) (hhi1 : 1 ≤ hi)
    (hA : ∀ x : FreeGroup (Work.OROneRel.winBeta Wt c lo hi),
      Work.OROneRel.winRho Wt c lo hi x ∈
          Subgroup.normalClosure ({u ^ l} : Set (FreeGroup α)) →
        x ∈ Subgroup.normalClosure
          ({Work.OROneRel.winRoot Wt c lo hi u ^ l} :
            Set (FreeGroup (Work.OROneRel.winBeta Wt c lo hi))))
    {τ : FreeGroup α} (hτ : Work.OROneRel.cohom c τ = Multiplicative.ofAdd 1)
    (hτwalk : ∀ p ∈ Work.OROneRel.decor c 0 (Work.OROneRel.wordOf τ),
      Work.OROneRel.coverEdge p ∈ Work.OROneRel.winE c lo hi) :
    Work.ORBassSerre.IsTree
      (Work.OROneRel.GradedHNN.Coset (Work.OROneRel.winRho Wt c lo hi).range τ) := by sorry

end Low

end Work.OROneRel
