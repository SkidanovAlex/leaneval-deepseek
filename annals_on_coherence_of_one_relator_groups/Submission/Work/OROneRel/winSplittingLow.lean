/-
Copyright: subproject `OROneRel` -- one-relator combinatorics (node N2).

# The window splitting of the residual of `magnus_step_root`, below `magnus_step_root`

This module assembles, **below** `Submission.Work.OROneRel.magnus_step_root` in the module order, the
pair form of the window splitting that the residual of `magnus_step_root` consumes.

Recall the two halves of the `Z`-domain splitting for window data `(c, Wt, lo, hi, u, l)` of the band
of the walk of `u` (with the case hypotheses of the residual and the window Freiheitssatz `hA`):

* **(P-A)** `Work.OROneRel.Low.winRhoRange_cosetTree_window_v2`
  (`Submission/Work/OROneRel/winRhoRange_cosetTreeLow.lean`): for **every** deck element `τ` of
  weight one with walk in the window, the coset graph `Coset ((winRho Wt c lo hi).range) τ` of the
  *free group* is a tree -- the graph-of-spaces / line-of-pieces step (Linton, *One-relator
  hierarchies*, Prop. 2.2.19 & 4.3);
* **(P-B)** `Work.OROneRel.Low.winVertex_generation_exists_windowWalk_v2`
  (`Submission/Work/OROneRel/winVertexGenerationLow.lean`): some such `τ` generates the one-relator
  group `G = ⟨α | u ^ l⟩` together with the window vertex `winVertex Wt c lo hi u l`.

Given the two, the assembled statement is:

* `Low.magnus_residual_winTreeSplitting_of_freeTree`
  (`Submission/Work/OROneRel/winTreeSplittingLow.lean`, **proved**; a copy below the Magnus step of
  `Submission/Work/OROneRel/magnus_residual_winTreeSplitting.lean`) transports (P-A) to the same tree
  statement for the *one-relator group* `G`, using that `u = winRho (winRoot)` is elliptic;
* `Work.OROneRel.exists_split_of_cosetTree`
  (`Submission/Work/OROneRel/split_of_cosetTree.lean`, **proved**) turns a tree on the coset graph of
  the pair into generation plus injectivity of the canonical comparison map `hnnConjMap`.

The conclusion `Low.windowSplitting_v2` below is *exactly* the pair form consumed by
`magnus_step_root_no_eps_zero_residual` in `Submission/Work/OROneRel/magnus_step_root.lean`, with the
case hypotheses of that residual carried explicitly -- so that the residual closes by a single
application, and the statement is available below the Magnus step.
-/
import Mathlib
import Submission.Work.OROneRel.winBasisDefs
import Submission.Work.OROneRel.winAssembly
import Submission.Work.OROneRel.magnusCaseDefs
import Submission.Work.OROneRel.Low.winRhoRange_cosetTree_window_v2
import Submission.Work.OROneRel.Low.winVertex_generation_exists_windowWalk_v2
import Submission.Work.OROneRel.winTreeSplittingLow
import Submission.Work.OROneRel.split_of_cosetTree
import Submission.Work.OROneRel.winRhoRange_tree

namespace Work.OROneRel

namespace Low

universe u

set_option autoImplicit false

/-- **The weight map of the presented group on a representative**: `presentedCohom c u l hc` sends
the class of `w : F α` to `cohom c w`.  (Local copy of
`Work.OROneRel.presentedCohom_mk_apply`, so as not to depend on
`Submission/Work/OROneRel/isFreeGroup_ker_presentedCohom_of_freeEdge.lean`, whose module is currently
broken in the workspace.) -/
theorem presentedCohom_mk_eq_cohom {α : Type u} (c : α → ℤ) (u : FreeGroup α) (l : ℕ)
    (hc : Work.OROneRel.cohom c u = 1) (w : FreeGroup α) :
    Work.OROneRel.presentedCohom c u l hc
      (PresentedGroup.mk ({u ^ l} : Set (FreeGroup α)) w) = Work.OROneRel.cohom c w := by
  have h : (Work.OROneRel.presentedCohom c u l hc).comp
      (PresentedGroup.mk ({u ^ l} : Set (FreeGroup α))) = Work.OROneRel.cohom c := by
    refine FreeGroup.ext_hom _ _ fun x => ?_
    show Work.OROneRel.presentedCohom c u l hc (PresentedGroup.of x) =
      Work.OROneRel.cohom c (FreeGroup.of x)
    rw [Work.OROneRel.presentedCohom_of, Work.OROneRel.cohom_of]
  exact congrArg (fun f : FreeGroup α →* Multiplicative ℤ => f w) h

/-- **The pair form of the window splitting, with the case hypotheses of the residual.**

Under the hypotheses of the residual of `magnus_step_root` (a cyclically reduced root `u` that is
neither a proper power nor a letter, all of whose exponent sums are non-zero, which is not divisible,
not a free-kernel instance and not a Nielsen-count instance), and for the window data
`(c, Wt, lo, hi)` of the band of the walk of `u` together with the window Freiheitssatz `hA`, there
is a deck element `τ` of weight one whose decorated walk lies in the window, such that

* `winVertex Wt c lo hi u l` together with the class of `τ` generates `G = ⟨α | u ^ l⟩`, and
* the canonical comparison map `hnnConjMap (winVertex …) (mk τ)` is injective.

This is Linton's `Z`-domain splitting of the one-relator group over the window vertex
(*One-relator hierarchies*, arXiv 2202.11324, Prop. 4.3), in exactly the shape in which the
`Z`-domain datum of the Magnus step consumes it. -/
theorem windowSplitting_v2 {α : Type u} [Fintype α] [DecidableEq α]
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
            Set (FreeGroup (Work.OROneRel.winBeta Wt c lo hi)))) :
    ∃ τ : FreeGroup α, Work.OROneRel.cohom c τ = Multiplicative.ofAdd 1 ∧
      (∀ p ∈ Work.OROneRel.decor c 0 (Work.OROneRel.wordOf τ),
        Work.OROneRel.coverEdge p ∈ Work.OROneRel.winE c lo hi) ∧
      winVertex Wt c lo hi u l ⊔
          Subgroup.zpowers (PresentedGroup.mk ({u ^ l} : Set (FreeGroup α)) τ) = ⊤ ∧
      Function.Injective (hnnConjMap (winVertex Wt c lo hi u l)
        (PresentedGroup.mk ({u ^ l} : Set (FreeGroup α)) τ)) := by
  classical
  -- **(P-B)**: a weight-one deck element whose walk lies in the window, generating `G` with the
  -- vertex.
  obtain ⟨τ, hτ, hwalk, hgen⟩ :=
    Low.winVertex_generation_exists_windowWalk_v2 u l hl hu hcyc hn hbad hnd hnlo hocc hnfk hnc
      hcu hW0 hcoh hwin hone htree hcov hlast hlo1 hhi1 hA
  -- **(P-A)** for that very `τ` (the statement quantifies over all admissible `τ`): the coset graph
  -- of the pair `((winRho …).range, τ)` inside the free group is a tree.
  have hT₀ : Work.ORBassSerre.IsTree
      (Work.OROneRel.GradedHNN.Coset (Work.OROneRel.winRho Wt c lo hi).range τ) :=
    Low.winRhoRange_cosetTree_window_v2 u l hl hu hcyc hn hbad hnd hnlo hocc hnfk hnc
      hcu hW0 hcoh hwin hone htree hcov hlast hlo1 hhi1 hA hτ hwalk
  -- **the transport to the one-relator group**: the normal closure of `u ^ l` is generated by
  -- elliptic elements of the free-group tree, so the quotient coset graph is again a tree.
  have hT : Work.ORBassSerre.IsTree
      (Work.OROneRel.GradedHNN.Coset (winVertex Wt c lo hi u l)
        (PresentedGroup.mk ({u ^ l} : Set (FreeGroup α)) τ)) :=
    Low.magnus_residual_winTreeSplitting_of_freeTree u l hcu hW0 hcoh hwin hτ hT₀ hgen
  -- **the weight map on `G`** kills the vertex and sends the class of `τ` to `ofAdd 1`; this is the
  -- coherence datum needed by `exists_split_of_cosetTree`.
  have hφ : ∀ h : ↥(winVertex Wt c lo hi u l),
      presentedCohom c u l hcu (h : PresentedGroup ({u ^ l} : Set (FreeGroup α))) = 1 := by
    intro h
    obtain ⟨g, hg, hgh⟩ := h.2
    rw [← hgh, presentedCohom_mk_eq_cohom]
    exact cohom_eq_one_of_mem_winRho_range Wt c lo hi hcoh hg
  have hφτ : presentedCohom c u l hcu
      (PresentedGroup.mk ({u ^ l} : Set (FreeGroup α)) τ) = Multiplicative.ofAdd 1 := by
    rw [presentedCohom_mk_eq_cohom, hτ]
  -- **the tree gives the splitting**: generation and injectivity of the comparison map.
  obtain ⟨hgen', hinj⟩ :=
    exists_split_of_cosetTree (winVertex Wt c lo hi u l)
      (PresentedGroup.mk ({u ^ l} : Set (FreeGroup α)) τ) (presentedCohom c u l hcu) hφ hφτ hT
  exact ⟨τ, hτ, hwalk, hgen', hinj⟩

end Low

end Work.OROneRel
