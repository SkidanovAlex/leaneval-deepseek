/-
Copyright: work module for the Elgindi finite-time singularity project.

# `FTS_EllLimOK.BoxDataH.contDiffOn_two_of_fderivWithin_data`

The assembly step of the closed-box regularity argument (see the docstring of
`FTS_EllLimOK.BoxReg_of_uniform`): given, on the box `cbox a b = [a,b] × [0,π/2]`,

* *within*-Fréchet derivatives of `G` with slopes `A`, `B`,
* *within*-Fréchet derivatives of `A` with slopes `A₁`, `A₂`,
* *within*-Fréchet derivatives of `B` with slopes `B₁`, `B₂`,

and continuity on the box of the six slope functions, the function `G` is jointly `C²` on the
box.  No staircase / sequence is involved: the two-level `HasFDerivWithinAt` data and the
continuity of the first-order slopes already say that the derivative family
`p ↦ ellCop (A p) (B p)` is `C¹` within the box, and two applications of
`contDiffWithinAt_succ_iff_hasFDerivWithinAt'` give the conclusion.

Everything here is `sorry`-free.
-/
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Order.CompletePartialOrder
import Submission.Work.FTS_EllLimOK.BoxDataH.WithinVec
import Submission.Work.FTS_EllLimOK.BoxRegAux.hasFDerivWithinAt_of_uniform_slice_partials
import Submission.Work.FTS_EllLimOK.BoxRegAux.Defs
import Submission.Work.FTS_EllLimOK.BoxReg_of_uniform

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology ContDiff
open MeasureTheory Set Filter

namespace Work.FTS_EllLimOK.BoxDataH

set_option autoImplicit false

theorem contDiffOn_two_of_fderivWithin_data {G A B A₁ A₂ B₁ B₂ : ℝ → ℝ → ℝ} {a b : ℝ}
    (hab : a < b)
    (hcontA : ContinuousOn (fun p : ℝ × ℝ => A p.1 p.2) (Work.FTS_EllLimOK.cbox a b))
    (hcontB : ContinuousOn (fun p : ℝ × ℝ => B p.1 p.2) (Work.FTS_EllLimOK.cbox a b))
    (hcontA₁ : ContinuousOn (fun p : ℝ × ℝ => A₁ p.1 p.2) (Work.FTS_EllLimOK.cbox a b))
    (hcontA₂ : ContinuousOn (fun p : ℝ × ℝ => A₂ p.1 p.2) (Work.FTS_EllLimOK.cbox a b))
    (hcontB₁ : ContinuousOn (fun p : ℝ × ℝ => B₁ p.1 p.2) (Work.FTS_EllLimOK.cbox a b))
    (hcontB₂ : ContinuousOn (fun p : ℝ × ℝ => B₂ p.1 p.2) (Work.FTS_EllLimOK.cbox a b))
    (hS0 : ∀ p ∈ Work.FTS_EllLimOK.cbox a b, HasFDerivWithinAt (Function.uncurry G)
      (Work.FTS_EllLimOK.ellCop (A p.1 p.2) (B p.1 p.2)) (Work.FTS_EllLimOK.cbox a b) p)
    (hS1 : ∀ p ∈ Work.FTS_EllLimOK.cbox a b, HasFDerivWithinAt (Function.uncurry A)
      (Work.FTS_EllLimOK.ellCop (A₁ p.1 p.2) (A₂ p.1 p.2)) (Work.FTS_EllLimOK.cbox a b) p)
    (hS2 : ∀ p ∈ Work.FTS_EllLimOK.cbox a b, HasFDerivWithinAt (Function.uncurry B)
      (Work.FTS_EllLimOK.ellCop (B₁ p.1 p.2) (B₂ p.1 p.2)) (Work.FTS_EllLimOK.cbox a b) p) :
    ContDiffOn ℝ 2 (Function.uncurry G) (Work.FTS_EllLimOK.cbox a b) := by
  -- `A` is `C¹` within the box (with derivative `ellCop A₁ A₂`)
  have hA_c1 : ∀ q ∈ Work.FTS_EllLimOK.cbox a b,
      ContDiffWithinAt ℝ 1 (fun y : ℝ × ℝ => A y.1 y.2) (Work.FTS_EllLimOK.cbox a b) q := by
    intro q hq
    have haux : ContDiffWithinAt ℝ ((0 : ℕ∞ω) + 1) (fun y : ℝ × ℝ => A y.1 y.2)
        (Work.FTS_EllLimOK.cbox a b) q := by
      refine (contDiffWithinAt_succ_iff_hasFDerivWithinAt' (n := 0) (by simp)).mpr ?_
      refine ⟨insert q (Work.FTS_EllLimOK.cbox a b), self_mem_nhdsWithin, subset_rfl,
        fun h => absurd h (by simp),
        (fun y : ℝ × ℝ => Work.FTS_EllLimOK.ellCop (A₁ y.1 y.2) (A₂ y.1 y.2)), ?_, ?_⟩
      · intro y hy
        have hy' : y ∈ Work.FTS_EllLimOK.cbox a b := by
          rcases Set.mem_insert_iff.mp hy with h | h
          · rw [h]; exact hq
          · exact h
        exact hS1 y hy'
      · refine (contDiffWithinAt_zero hq).2 ⟨Work.FTS_EllLimOK.cbox a b, self_mem_nhdsWithin, ?_⟩
        intro y hy
        exact Work.FTS_EllLimOK.continuousWithinAt_ellCop
          ((hcontA₁.continuousWithinAt hy.1).mono Set.inter_subset_left)
          ((hcontA₂.continuousWithinAt hy.1).mono Set.inter_subset_left)
    simpa using haux
  -- `B` is `C¹` within the box (with derivative `ellCop B₁ B₂`)
  have hB_c1 : ∀ q ∈ Work.FTS_EllLimOK.cbox a b,
      ContDiffWithinAt ℝ 1 (fun y : ℝ × ℝ => B y.1 y.2) (Work.FTS_EllLimOK.cbox a b) q := by
    intro q hq
    have haux : ContDiffWithinAt ℝ ((0 : ℕ∞ω) + 1) (fun y : ℝ × ℝ => B y.1 y.2)
        (Work.FTS_EllLimOK.cbox a b) q := by
      refine (contDiffWithinAt_succ_iff_hasFDerivWithinAt' (n := 0) (by simp)).mpr ?_
      refine ⟨insert q (Work.FTS_EllLimOK.cbox a b), self_mem_nhdsWithin, subset_rfl,
        fun h => absurd h (by simp),
        (fun y : ℝ × ℝ => Work.FTS_EllLimOK.ellCop (B₁ y.1 y.2) (B₂ y.1 y.2)), ?_, ?_⟩
      · intro y hy
        have hy' : y ∈ Work.FTS_EllLimOK.cbox a b := by
          rcases Set.mem_insert_iff.mp hy with h | h
          · rw [h]; exact hq
          · exact h
        exact hS2 y hy'
      · refine (contDiffWithinAt_zero hq).2 ⟨Work.FTS_EllLimOK.cbox a b, self_mem_nhdsWithin, ?_⟩
        intro y hy
        exact Work.FTS_EllLimOK.continuousWithinAt_ellCop
          ((hcontB₁.continuousWithinAt hy.1).mono Set.inter_subset_left)
          ((hcontB₂.continuousWithinAt hy.1).mono Set.inter_subset_left)
    simpa using haux
  -- the derivative family `y ↦ ellCop (A y) (B y)` is `C¹` within the box
  have hf'_c1 : ∀ q ∈ Work.FTS_EllLimOK.cbox a b,
      ContDiffWithinAt ℝ 1
        (fun u : ℝ × ℝ => Work.FTS_EllLimOK.ellCop (A u.1 u.2) (B u.1 u.2))
        (Work.FTS_EllLimOK.cbox a b) q := by
    intro q hq
    have hpair : ContDiffWithinAt ℝ 1 (fun y : ℝ × ℝ => (A y.1 y.2, B y.1 y.2))
        (Work.FTS_EllLimOK.cbox a b) q := (hA_c1 q hq).prodMk (hB_c1 q hq)
    have hg : ContDiffWithinAt ℝ 1 (fun w : ℝ × ℝ => Work.FTS_EllLimOK.copBilin w)
        (Set.univ : Set (ℝ × ℝ)) (A q.1 q.2, B q.1 q.2) :=
      (ContinuousLinearMap.contDiff Work.FTS_EllLimOK.copBilin).contDiffWithinAt
    have h2 : ContDiffWithinAt ℝ 1
        (fun y : ℝ × ℝ => Work.FTS_EllLimOK.copBilin (A y.1 y.2, B y.1 y.2))
        (Work.FTS_EllLimOK.cbox a b) q :=
      hg.comp q hpair (fun y _ => Set.mem_univ _)
    refine h2.congr (fun y _ => (Work.FTS_EllLimOK.copBilin_apply (A y.1 y.2) (B y.1 y.2)).symm)
      (Work.FTS_EllLimOK.copBilin_apply (A q.1 q.2) (B q.1 q.2)).symm
  -- the second-order conclusion, in the `n + 1` form
  have hmain : ∀ q ∈ Work.FTS_EllLimOK.cbox a b, ContDiffWithinAt ℝ ((1 : ℕ∞ω) + 1)
      (Function.uncurry G) (Work.FTS_EllLimOK.cbox a b) q := by
    intro q hq
    refine (contDiffWithinAt_succ_iff_hasFDerivWithinAt' (n := 1) (by simp)).mpr ?_
    refine ⟨insert q (Work.FTS_EllLimOK.cbox a b), self_mem_nhdsWithin, subset_rfl,
      fun h => absurd h (by simp),
      (fun u : ℝ × ℝ => Work.FTS_EllLimOK.ellCop (A u.1 u.2) (B u.1 u.2)), ?_, hf'_c1 q hq⟩
    intro y hy
    have hy' : y ∈ Work.FTS_EllLimOK.cbox a b := by
      rcases Set.mem_insert_iff.mp hy with h | h
      · rw [h]; exact hq
      · exact h
    exact hS0 y hy'
  intro p hp
  simpa [show ((1 : ℕ∞ω) + 1 : ℕ∞ω) = 2 from by norm_num] using hmain p hp

end Work.FTS_EllLimOK.BoxDataH
