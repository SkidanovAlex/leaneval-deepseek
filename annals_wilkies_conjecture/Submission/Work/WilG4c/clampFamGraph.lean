/-
  WilG4c / clampFamGraph — the graph of a clamped family is still `Ω`-bounded.

  The statement (BNZ §5.2's "clamp the values into `(0,1)`" device, in the form the reduction
  `StepYbdd` needs): there are constants `a`, `c` depending only on `p` and `m` such that
  clamping the values of every member of a family into `(0,1)` costs `a` in the *format* and
  `c` in the *degree* of the graphs.

  The naive set-theoretic decomposition

    graph (clamp ∘ f)  =  (graph f ∩ {value ∈ (0,1)}) ∪ ({t = 1/2} ∩ {value ∉ (0,1)})

  mentions `graph f` **twice**, and since `Ω`-degrees add under unions and intersections, it
  would cost `2 * D` and not `D + c` (the second occurrence is hidden in
  `{value ∉ (0,1)} = projLast (graph f ∩ {value ∈ (0,1)})ᶜ`).  The way out is that the value
  of `f` at `(l,u)` can be *read off* from `graph f`:  put the value into an extra coordinate
  `s`, i.e. pull `graph f` back along the substitution `σ` that keeps the parameters and the
  new coordinate `s` but forgets the old `t`-slot (cost: `D + 2`), intersect with the *fixed*
  relation `t = clamp01 s` (degree `O(1)`, proved in `clampRel_mem`), and project `s` away
  again.  The graph of `f` is used exactly once, so the degree only grows by a constant.

  The two ingredients are the delegated lemmas `clampRel_mem` (the fixed relation is `Ω`) and
  `projLast_inter_dropSecondLast` (the projection computes the clamped graph); the rest is
  `subst_mem` plus the `Ω`-bookkeeping.
-/
import Mathlib
import Submission.Work.Wilkies.CG.Spec
import Submission.Work.WilG4c.ClampDefs
import Submission.Work.WilG4c.GraphOfComp
import Submission.Work.WilG0.API
import Submission.Work.WilG1.Basic
import Submission.Work.WilG4c.clampRel_mem
import Submission.Work.WilG4c.projLast_inter_dropSecondLast

set_option autoImplicit false
noncomputable section
open Classical

namespace Work.WilG4c

open WilkiesDesign WilkiesDesign.CG
open Work.WilG0 Work.WilG1

/-- Core of `clampFamGraph`: one family member, with the explicit format/degree increments
`a = 4 * (p + m) + 100` and `c = 40`.  (The stated bounds are generous; the useful content is
that both are bounded independently of the family, of `F0`, of `D` and of the member.) -/
theorem clampFamGraph_mem (S : SOMin) (p m : ℕ) :
    ∃ (a c : ℕ), ∀ (F0 D : ℕ) (f : (Fin p → ℝ) → (Fin m → ℝ) → ℝ),
      famGraph f ∈ S.Ω F0 D (p + m + 1) →
      famGraph (fun l u => if f l u ∈ Set.Ioo (0 : ℝ) 1 then f l u else (1 / 2 : ℝ)) ∈
        S.Ω (F0 + a) (D + c) (p + m + 1) := by
  -- the two ingredients (delegated): the fixed clamp relation is `Ω`, and the projection
  -- of the pulled-back graph intersected with it is the clamped graph
  have hrel : clampRel (p + m) ∈ S.Ω (p + m + 20) 30 ((p + m) + 2) := clampRel_mem S (p + m)
  refine ⟨4 * (p + m) + 100, 40, ?_⟩
  intro F0 D f hf
  -- pull the graph back along the substitution that forgets the `t`-slot
  have hsub : {z : Fin ((p + m) + 2) → ℝ |
      z ∘ dropSecondLast (p + m) ∈ famGraph f} ∈
      S.Ω (F0 + 2 * (((p + m) + 2) + ((p + m) + 1)) + 1) (D + 2) ((p + m) + 2) :=
    GraphComp.subst_mem S (dropSecondLast (p + m)) hf
  -- intersect with the fixed clamp relation, at a common format
  have hA : {z : Fin ((p + m) + 2) → ℝ |
      z ∘ dropSecondLast (p + m) ∈ famGraph f} ∈
      S.Ω (max (F0 + 2 * (((p + m) + 2) + ((p + m) + 1)) + 1) (p + m + 20)) (D + 2)
        ((p + m) + 2) :=
    Omega_mono_F (le_max_left _ _) hsub
  have hB : clampRel (p + m) ∈
      S.Ω (max (F0 + 2 * (((p + m) + 2) + ((p + m) + 1)) + 1) (p + m + 20)) 30
        ((p + m) + 2) :=
    Omega_mono_F (le_max_right _ _) hrel
  have hI := Omega_inter2 hA hB
  -- project the value coordinate away: the clamped graph
  have hP := S.proj hI
  rw [projLast_inter_dropSecondLast (f := f)] at hP
  exact Omega.mono hP (by omega) (by omega)

/-- **Wilkie's conjecture for Pfaffian structures, BNZ §5.2, the clamping device.**
For any `p m` there are `a c` such that replacing every member `F i` of a family by its
clamp into `(0,1)` costs `a` in the format and `c` in the degree of the graphs. -/
theorem clampFamGraph (S : WilkiesDesign.SOMin) (p m : ℕ) :
    ∃ (a c : ℕ),
      ∀ {k : ℕ} (F0 D : ℕ) (F : Fin k → (Fin p → ℝ) → (Fin m → ℝ) → ℝ),
        (∀ i, WilkiesDesign.CG.famGraph (F i) ∈ S.Ω F0 D (p + m + 1)) →
        ∀ i, WilkiesDesign.CG.famGraph
              (fun l u => if F i l u ∈ Set.Ioo (0 : ℝ) 1 then F i l u else (1 / 2 : ℝ)) ∈
            S.Ω (F0 + a) (D + c) (p + m + 1) := by
  obtain ⟨a, c, h⟩ := clampFamGraph_mem S p m
  exact ⟨a, c, fun F0 D F hF i => h F0 D (F i) (hF i)⟩

end Work.WilG4c
