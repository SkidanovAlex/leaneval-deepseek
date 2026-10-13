/-
Copyright: work module for the Elgindi finite-time singularity project.

# `FTS_EllLimOK.ProducerH.BoxAux.contDiffOn_two_of_sliceData`

Closed-box `C²`-regularity from **within-slice** data.  This is the "pointwise" version of the
assembly `FTS_EllLimOK.BoxDataH.contDiffOn_two_of_fderivWithin_data`: instead of within-Fréchet
derivatives of the three functions `Ψ`, `A`, `B` on the box, one only assumes the two
*one-variable* within-derivatives of each (the `z`-slice and the `θ`-slice), together with
continuity of all the involved slope functions on the box.

The proof has two steps:

* `hasFDerivWithinAt_uncurry_of_sliceData` — the staircase argument: two one-variable
  within-derivatives of a function of two variables, with continuous slopes, give the
  within-Fréchet derivative `ellCop (A z θ) (B z θ)`.  This is the constant-sequence instance of
  `BoxRegAux.hasFDerivWithinAt_of_uniform_slice_partials`;
* `contDiffOn_two_of_fderivWithin_data_le` — the assembly with
  `contDiffWithinAt_succ_iff_hasFDerivWithinAt'` twice, which is the statement of
  `BoxDataH.contDiffOn_two_of_fderivWithin_data` but with the hypothesis `a ≤ b` instead of
  `a < b` (the proof of the latter never uses `a < b`; it is reproduced here so that the
  degenerate box `a = b` is covered too).

Everything here is `sorry`-free.
-/
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Order.CompletePartialOrder
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS_EllLimOK.BoxRegAux.hasFDerivWithinAt_of_uniform_slice_partials
import Submission.Work.FTS_EllLimOK.BoxDataH.contDiffOn_two_of_fderivWithin_data
import Submission.Work.FTS_EllLimOK.BoxReg

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology ContDiff
open MeasureTheory Set Filter

namespace Work.FTS_EllLimOK.ProducerH.BoxAux

set_option autoImplicit false

/-! ## Step 1: the two within-slice derivatives give the within-Fréchet derivative -/

/-- **Staircase from within-slice data.**  If a function `F` of two variables has, on the box
`[a,b] × [0,π/2]`, `z`-slice within-derivative `A` and `θ`-slice within-derivative `B`, with
`F`, `A`, `B` continuous on the box, then `F` is within-Fréchet differentiable on the box with
derivative `ellCop (A p) (B p)`. -/
theorem hasFDerivWithinAt_uncurry_of_sliceData
    {F A B : ℝ → ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hcontF : ContinuousOn (Function.uncurry F) (Work.FTS_EllLimOK.cbox a b))
    (hcontA : ContinuousOn (Function.uncurry A) (Work.FTS_EllLimOK.cbox a b))
    (hcontB : ContinuousOn (Function.uncurry B) (Work.FTS_EllLimOK.cbox a b))
    (hsz : ∀ z ∈ Set.Icc a b, ∀ θ ∈ Set.Icc 0 (Real.pi / 2),
      HasDerivWithinAt (fun z' => F z' θ) (A z θ) (Set.Icc a b) z)
    (hth : ∀ z ∈ Set.Icc a b, ∀ θ ∈ Set.Icc 0 (Real.pi / 2),
      HasDerivWithinAt (fun θ' => F z θ') (B z θ) (Set.Icc 0 (Real.pi / 2)) θ) :
    ∀ p ∈ Work.FTS_EllLimOK.cbox a b,
      HasFDerivWithinAt (Function.uncurry F)
        (Work.FTS_EllLimOK.ellCop (A p.1 p.2) (B p.1 p.2))
        (Work.FTS_EllLimOK.cbox a b) p := by
  have hcd : (0 : ℝ) ≤ Real.pi / 2 := by linarith [Real.pi_pos]
  -- the constant sequence converges uniformly to itself
  have hunif : ∀ P : ℝ → ℝ → ℝ,
      TendstoUniformlyOn (fun (_ : ℕ) (p : ℝ × ℝ) => P p.1 p.2)
        (fun p : ℝ × ℝ => P p.1 p.2) Filter.atTop
        (Set.Icc a b ×ˢ Set.Icc 0 (Real.pi / 2)) := by
    intro P
    rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    exact Filter.Eventually.of_forall fun n p hp => by simpa using hε
  have hmain := Work.FTS_EllLimOK.BoxRegAux.hasFDerivWithinAt_of_uniform_slice_partials
    (a := a) (b := b) (c := 0) (d := Real.pi / 2) hab hcd
    (H := fun _ : ℕ => F) (H₀ := F) (P := fun _ : ℕ => A) (P₀ := A)
    (Q := fun _ : ℕ => B) (Q₀ := B)
    (fun _ => by simpa only [Work.FTS_EllLimOK.cbox, Function.uncurry] using hcontF)
    (fun _ z hz θ hθ => hsz z hz θ hθ)
    (fun _ z hz θ hθ => hth z hz θ hθ)
    (fun _ => by simpa only [Work.FTS_EllLimOK.cbox, Function.uncurry] using hcontA)
    (fun _ => by simpa only [Work.FTS_EllLimOK.cbox, Function.uncurry] using hcontB)
    (fun z hz θ hθ => tendsto_const_nhds)
    (hunif A) (hunif B)
    (by simpa only [Work.FTS_EllLimOK.cbox, Function.uncurry] using hcontA)
    (by simpa only [Work.FTS_EllLimOK.cbox, Function.uncurry] using hcontB)
  intro p hp
  obtain ⟨z, θ⟩ := p
  rw [Work.FTS_EllLimOK.mem_cbox] at hp
  exact hmain z hp.1 θ hp.2

/-! ## Step 2: the assembly (with `a ≤ b`, so that the degenerate box is covered) -/

/-- **The closed-box `C²` assembly from within-Fréchet data.**  This is
`BoxDataH.contDiffOn_two_of_fderivWithin_data` with `a ≤ b` in place of `a < b`; the proof is
that of the cited theorem, which does not use its `a < b` hypothesis. -/
theorem contDiffOn_two_of_fderivWithin_data_le {G A B A₁ A₂ B₁ B₂ : ℝ → ℝ → ℝ} {a b : ℝ}
    (hab : a ≤ b)
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

/-! ## Step 3: the requested theorem -/

theorem contDiffOn_two_of_sliceData
    {Ψ A B A₁ A₂ B₁ B₂ : ℝ → ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hcontΨ : ContinuousOn (Function.uncurry Ψ) (Work.FTS_EllLimOK.cbox a b))
    (hcontA : ContinuousOn (Function.uncurry A) (Work.FTS_EllLimOK.cbox a b))
    (hcontB : ContinuousOn (Function.uncurry B) (Work.FTS_EllLimOK.cbox a b))
    (hcontA₁ : ContinuousOn (Function.uncurry A₁) (Work.FTS_EllLimOK.cbox a b))
    (hcontA₂ : ContinuousOn (Function.uncurry A₂) (Work.FTS_EllLimOK.cbox a b))
    (hcontB₁ : ContinuousOn (Function.uncurry B₁) (Work.FTS_EllLimOK.cbox a b))
    (hcontB₂ : ContinuousOn (Function.uncurry B₂) (Work.FTS_EllLimOK.cbox a b))
    (hszΨ : ∀ z ∈ Set.Icc a b, ∀ θ ∈ Set.Icc 0 (Real.pi / 2),
      HasDerivWithinAt (fun z' => Ψ z' θ) (A z θ) (Set.Icc a b) z)
    (hthΨ : ∀ z ∈ Set.Icc a b, ∀ θ ∈ Set.Icc 0 (Real.pi / 2),
      HasDerivWithinAt (fun θ' => Ψ z θ') (B z θ) (Set.Icc 0 (Real.pi / 2)) θ)
    (hszA : ∀ z ∈ Set.Icc a b, ∀ θ ∈ Set.Icc 0 (Real.pi / 2),
      HasDerivWithinAt (fun z' => A z' θ) (A₁ z θ) (Set.Icc a b) z)
    (hthA : ∀ z ∈ Set.Icc a b, ∀ θ ∈ Set.Icc 0 (Real.pi / 2),
      HasDerivWithinAt (fun θ' => A z θ') (A₂ z θ) (Set.Icc 0 (Real.pi / 2)) θ)
    (hszB : ∀ z ∈ Set.Icc a b, ∀ θ ∈ Set.Icc 0 (Real.pi / 2),
      HasDerivWithinAt (fun z' => B z' θ) (B₁ z θ) (Set.Icc a b) z)
    (hthB : ∀ z ∈ Set.Icc a b, ∀ θ ∈ Set.Icc 0 (Real.pi / 2),
      HasDerivWithinAt (fun θ' => B z θ') (B₂ z θ) (Set.Icc 0 (Real.pi / 2)) θ) :
    ContDiffOn ℝ 2 (Function.uncurry Ψ) (Work.FTS_EllLimOK.cbox a b) := by
  have hG : ∀ p ∈ Work.FTS_EllLimOK.cbox a b,
      HasFDerivWithinAt (Function.uncurry Ψ)
        (Work.FTS_EllLimOK.ellCop (A p.1 p.2) (B p.1 p.2))
        (Work.FTS_EllLimOK.cbox a b) p :=
    hasFDerivWithinAt_uncurry_of_sliceData hab hcontΨ hcontA hcontB hszΨ hthΨ
  have hA : ∀ p ∈ Work.FTS_EllLimOK.cbox a b,
      HasFDerivWithinAt (Function.uncurry A)
        (Work.FTS_EllLimOK.ellCop (A₁ p.1 p.2) (A₂ p.1 p.2))
        (Work.FTS_EllLimOK.cbox a b) p :=
    hasFDerivWithinAt_uncurry_of_sliceData hab hcontA hcontA₁ hcontA₂ hszA hthA
  have hB : ∀ p ∈ Work.FTS_EllLimOK.cbox a b,
      HasFDerivWithinAt (Function.uncurry B)
        (Work.FTS_EllLimOK.ellCop (B₁ p.1 p.2) (B₂ p.1 p.2))
        (Work.FTS_EllLimOK.cbox a b) p :=
    hasFDerivWithinAt_uncurry_of_sliceData hab hcontB hcontB₁ hcontB₂ hszB hthB
  exact contDiffOn_two_of_fderivWithin_data_le hab hcontA hcontB hcontA₁ hcontA₂ hcontB₁ hcontB₂
    hG hA hB

end Work.FTS_EllLimOK.ProducerH.BoxAux
