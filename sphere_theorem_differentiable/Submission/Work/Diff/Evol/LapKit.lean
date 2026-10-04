import Mathlib
import Submission.Diff.Evol
import Submission.Work.Diff.Evol.Vocab
import Submission.Work.Diff.Evol.Curv4Coef
import Submission.Work.Diff.GE.dRmPhi
import Submission.Work.Diff.GE.dRmPhi_slotA
import Submission.Work.Diff.GE.curvbasic
import Submission.Work.Diff.GE.onFrame_orthogonal_change
import Submission.Work.Diff.GE.NablaRm
import Submission.Work.Diff.GE.contMDiff_rmP_fields
import Submission.Work.Diff.GE.cov2RmExt_prelim
import Submission.Work.Diff.GE.mvfderiv_covRm_fields
import Submission.Work.Diff.GE.laplAt_eq_sum_hessAt
import Submission.Work.Diff.GE.hessAt_comm
import Submission.Work.Diff.GE.lapRmAt_trace
import Submission.Work.Diff.GE.frameMotion_cancel_cov2Rm
import Submission.Work.Diff.GE.sum_trace_bilinear_orthogonal

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Toolkit for the proof of `LapRmFrameParallel` (area Evol / LapRmFrameParallel)

Vocabulary and elementary lemmas used by `Submission.Work.Diff.Evol.lap_parallel`.

The proof of `LapRmFrameParallel` has two layers:

* **geometry** (`Work.Diff.Evol.frame_exists`): a global smooth frame field `Ef` which at `x` is the
  given orthonormal frame `e`, which is orthonormal near `x`, and which is *parallel at `x` to second
  order*: `∇_v Ef i = 0` and `∇_W ∇_W Ef i = 0` at `x` for every direction `v` and every smooth `W`
  (realised by parallel transport along the straight chart lines through `x`; the chart-line
  construction makes the dependence on the direction an ordinary ODE-with-parameters problem);

* **tensor calculus** (this file): from those two conditions, the Laplacian at `x` of any linear
  functional `ℓ` of the curvature components of `Ef` is `ℓ` applied to the trace of `∇²Rm`.  The
  computation splits into
  - `mvfderiv_ell_rmFrame'`: the first derivative of `ℓ ∘ rmFrame ∘ Ef` at `x` is `ℓ(∇Rm)` on the
    values (the frame-rotation corrections vanish by `∇Ef i(x) = 0`);
  - `second_deriv_ell_rmFrame` / `hessAt_ell_rmFrame`: the second derivative of `ℓ ∘ rmFrame ∘ Ef`
    in a parallel direction is `ℓ(∇²Rm) + ℓ(∇_{∇W}W Rm)`, and the two `∇_{∇W}W` terms of `hessAt`
    cancel;
  - `lapRmFrame_trace_indep`: the trace over an orthonormal frame is frame-independent (the
    `(0,6)`-tensoriality of `∇²Rm`);
  - `laplAt_ell_rmFrame_eq`: the assembly.
-/

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option maxHeartbeats 4000000

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology BigOperators
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter

namespace Work.Diff.Evol

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M] [IsManifold I ∞ M] [I.Boundaryless]

/-- `rmFrame` in terms of `rmP`. -/
theorem rmFrame_eq_rmP (g : SMet I M) (y : M) (e : Fin (Module.finrank ℝ E) → TangentSpace I y) :
    rmFrame g y e = fun i j k l => rmP g y (e i) (e j) (e k) (e l) := rfl

/-- `Work.Diff.GE.cov2RmExt` composed with the chosen extensions is the frozen `Submission.Diff.cov2Rm`. -/
theorem cov2RmExt_smoothExt_eq_cov2Rm (g : SMet I M) (x : M)
    (v w a b c d : TangentSpace I x) :
    Work.Diff.GE.cov2RmExt g x v (smoothExt x w) (smoothExt x a) (smoothExt x b)
        (smoothExt x c) (smoothExt x d) = cov2Rm g x v w a b c d := by
  simp only [Work.Diff.GE.cov2RmExt, Submission.Diff.cov2Rm, Work.Diff.GE.smoothExt_apply]

/-- `rmP` vanishes when its first argument is zero. -/
theorem rmP_zero_fst (hLC : LCSmooth I M) (g : SMet I M) (x : M)
    (b c d : TangentSpace I x) : rmP g x 0 b c d = 0 := by
  simpa using Work.Diff.GE.rmP_smul_fst (I := I) (M := M) g hLC x 0 (0 : TangentSpace I x) b c d

/-- `rmP` vanishes when its second argument is zero. -/
theorem rmP_zero_snd (hLC : LCSmooth I M) (g : SMet I M) (x : M)
    (a c d : TangentSpace I x) : rmP g x a 0 c d = 0 := by
  simpa using Work.Diff.GE.rmP_smul_snd (I := I) (M := M) g hLC x 0 a (0 : TangentSpace I x) c d

/-- `rmP` vanishes when its third argument is zero. -/
theorem rmP_zero_thd (hLC : LCSmooth I M) (g : SMet I M) (x : M)
    (a b d : TangentSpace I x) : rmP g x a b (0 : TangentSpace I x) d = 0 := by
  simpa using Work.Diff.GE.rmP_smul_thd (I := I) (M := M) g hLC x 0 a b (0 : TangentSpace I x) d

/-- `rmP` vanishes when its fourth argument is zero. -/
theorem rmP_zero_fth (hLC : LCSmooth I M) (g : SMet I M) (x : M)
    (a b c : TangentSpace I x) : rmP g x a b c (0 : TangentSpace I x) = 0 := by
  simpa using Work.Diff.GE.rmP_smul_fth (I := I) (M := M) g hLC x 0 a b c (0 : TangentSpace I x)

/-- `covRm` vanishes in its second slot. -/
theorem covRm_zero_snd (hLC : LCSmooth I M) (g : SMet I M) (x : M)
    (v b c d : TangentSpace I x) : covRm g x v (0 : TangentSpace I x) b c d = 0 := by
  simpa using Work.Diff.GE.covRm_linear_snd (I := I) (M := M) hLC g x v 0 0
    (0 : TangentSpace I x) (0 : TangentSpace I x) b c d

/-- `covRm` vanishes in its third slot. -/
theorem covRm_zero_thd (hLC : LCSmooth I M) (g : SMet I M) (x : M)
    (v a c d : TangentSpace I x) : covRm g x v a (0 : TangentSpace I x) c d = 0 := by
  simpa using Work.Diff.GE.covRm_linear_thd (I := I) (M := M) hLC g x v a 0 0
    (0 : TangentSpace I x) (0 : TangentSpace I x) c d

/-- `covRm` vanishes in its fourth slot. -/
theorem covRm_zero_fth (hLC : LCSmooth I M) (g : SMet I M) (x : M)
    (v a b d : TangentSpace I x) : covRm g x v a b (0 : TangentSpace I x) d = 0 := by
  simpa using Work.Diff.GE.covRm_linear_fth (I := I) (M := M) hLC g x v a b 0 0
    (0 : TangentSpace I x) (0 : TangentSpace I x) d

/-- `covRm` vanishes in its fifth slot. -/
theorem covRm_zero_fif (hLC : LCSmooth I M) (g : SMet I M) (x : M)
    (v a b c : TangentSpace I x) : covRm g x v a b c (0 : TangentSpace I x) = 0 := by
  simpa using Work.Diff.GE.covRm_linear_fif (I := I) (M := M) hLC g x v a b c 0 0
    (0 : TangentSpace I x) (0 : TangentSpace I x)

variable {x : M}

/-! ## The curvature components of a frame field -/

/-- The curvature components of a frame field: `Rm_{ijkl}(y) = Rm(Ef i, Ef j, Ef k, Ef l)(y)`. -/
noncomputable def frameComp (g : SMet I M)
    (Ef : Fin (Module.finrank ℝ E) → Π y : M, TangentSpace I y)
    (i j k l : Fin (Module.finrank ℝ E)) (y : M) : ℝ :=
  rmP g y (Ef i y) (Ef j y) (Ef k y) (Ef l y)

/-- The curvature component of the frame field indexed by the product type
`((Fin n × Fin n) × Fin n) × Fin n`. -/
noncomputable def frameCompF (g : SMet I M)
    (Ef : Fin (Module.finrank ℝ E) → Π y : M, TangentSpace I y) :
    (((Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E)) × Fin (Module.finrank ℝ E)) ×
      Fin (Module.finrank ℝ E)) → M → ℝ :=
  fun p => frameComp g Ef p.1.1.1 p.1.1.2 p.1.2 p.2

/-- Coordinates of `ℓ` on the flattened index type. -/
noncomputable def coefF {n : ℕ} (ℓ : Curv4 n →L[ℝ] ℝ) :
    (((Fin n × Fin n) × Fin n) × Fin n) → ℝ :=
  fun p => coef ℓ p.1.1.1 p.1.1.2 p.1.2 p.2

/-- **The value of the first derivative of a curvature component.**  The derivative of
`y ↦ Rm(Ef i, Ef j, Ef k, Ef l)(y)` in the direction of a smooth field `W` is `covRm` on the values
plus the four frame-rotation corrections; this is that value, packaged so that the large expressions
below stay compact. -/
noncomputable def rmFirstTerm (g : SMet I M)
    (Ef : Fin (Module.finrank ℝ E) → Π y : M, TangentSpace I y)
    (W : Π y : M, TangentSpace I y)
    (i j k l : Fin (Module.finrank ℝ E)) (y : M) : ℝ :=
  covRm g y (W y) (Ef i y) (Ef j y) (Ef k y) (Ef l y)
    + rmP g y (lcOf g (Ef i) y (W y)) (Ef j y) (Ef k y) (Ef l y)
    + rmP g y (Ef i y) (lcOf g (Ef j) y (W y)) (Ef k y) (Ef l y)
    + rmP g y (Ef i y) (Ef j y) (lcOf g (Ef k) y (W y)) (Ef l y)
    + rmP g y (Ef i y) (Ef j y) (Ef k y) (lcOf g (Ef l) y (W y))

/-- **The Leibniz rule for the curvature along fields.**  The derivative of
`y ↦ Rm(A y, B y, C y, D y)` is the covariant derivative `∇Rm` on the values plus the four
corrections coming from the connection acting on the four fields. -/
theorem rmP_mvfderiv (hLC : LCSmooth I M) (g : SMet I M)
    {A B C D : Π y : M, TangentSpace I y}
    (hA : SmoothField I M A) (hB : SmoothField I M B) (hC : SmoothField I M C)
    (hD : SmoothField I M D) (z : M) (v : TangentSpace I z) :
    mvfderiv I (fun y : M => rmP g y (A y) (B y) (C y) (D y)) z v
      = covRm g z v (A z) (B z) (C z) (D z)
        + rmP g z (lcOf g A z v) (B z) (C z) (D z)
        + rmP g z (A z) (lcOf g B z v) (C z) (D z)
        + rmP g z (A z) (B z) (lcOf g C z v) (D z)
        + rmP g z (A z) (B z) (C z) (lcOf g D z v) := by
  have hV : SmoothField I M (smoothExt z v) := Work.Diff.GE.smoothExt_cmdiff z v
  have hfield := Work.Diff.GE.covRm_fields_eq_dRmPhi (I := I) (M := M) (g := g) hLC
    (V := smoothExt z v) (A := A) (B := B) (C := C) (D := D) hV hA hB hC hD z
  rw [show smoothExt z v z = v from Work.Diff.GE.smoothExt_apply z v] at hfield
  rw [hfield]
  simp only [Work.Diff.GE.dRmPhi]
  ring

/-- **The first derivative of a curvature component in a frame field.** -/
theorem mvfderiv_frameCompF_rm (hLC : LCSmooth I M) (g : SMet I M)
    (Ef : Fin (Module.finrank ℝ E) → Π y : M, TangentSpace I y)
    (hEf : ∀ i, SmoothField I M (Ef i))
    (W : Π y : M, TangentSpace I y)
    (p : ((Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E)) ×
      Fin (Module.finrank ℝ E)) × Fin (Module.finrank ℝ E)) (y : M) :
    mvfderiv I (frameCompF g Ef p) y (W y)
      = rmFirstTerm g Ef W p.1.1.1 p.1.1.2 p.1.2 p.2 y :=
  rmP_mvfderiv hLC g (hEf p.1.1.1) (hEf p.1.1.2) (hEf p.1.2) (hEf p.2) y (W y)

/-- The curvature components of a frame field are smooth. -/
theorem frameComp_smooth (hLC : LCSmooth I M) (g : SMet I M)
    (Ef : Fin (Module.finrank ℝ E) → Π y : M, TangentSpace I y)
    (hEf : ∀ i, SmoothField I M (Ef i)) (i j k l : Fin (Module.finrank ℝ E)) :
    CMDiff ∞ (frameComp g Ef i j k l) :=
  Work.Diff.GE.rmP_fields_smooth (I := I) (M := M) hLC g (hEf i) (hEf j) (hEf k) (hEf l)

/-- The flattened curvature components of a frame field are smooth. -/
theorem frameCompF_smooth (hLC : LCSmooth I M) (g : SMet I M)
    (Ef : Fin (Module.finrank ℝ E) → Π y : M, TangentSpace I y)
    (hEf : ∀ i, SmoothField I M (Ef i))
    (p : ((Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E)) ×
      Fin (Module.finrank ℝ E)) × Fin (Module.finrank ℝ E)) :
    CMDiff ∞ (frameCompF g Ef p) :=
  frameComp_smooth hLC g Ef hEf p.1.1.1 p.1.1.2 p.1.2 p.2

/-- Smoothness of the covariant derivative of one field in the direction of another. -/
theorem lcOf_field_smooth (hLC : LCSmooth I M) (g : SMet I M)
    {A W : Π y : M, TangentSpace I y} (hA : SmoothField I M A) (hW : SmoothField I M W) :
    SmoothField I M (fun y : M => lcOf g A y (W y)) :=
  Commons.Geometry.Manifold.VectorBundle.CovariantDerivative.contMDiff_cov_apply
    (lcOf g) (hLC g).1.some hA hW

/-- Smoothness at `z` of `rmFirstTerm` for smooth data. -/
theorem contMDiffAt_rmFirstTerm (hLC : LCSmooth I M) (g : SMet I M)
    (Ef : Fin (Module.finrank ℝ E) → Π y : M, TangentSpace I y)
    (hEf : ∀ i, SmoothField I M (Ef i))
    (W : Π y : M, TangentSpace I y) (hW : SmoothField I M W) (z : M)
    (i j k l : Fin (Module.finrank ℝ E)) :
    ContMDiffAt I 𝓘(ℝ, ℝ) ∞ (rmFirstTerm g Ef W i j k l) z := by
  have h2 := (Work.Diff.GE.rmP_fields_smooth (I := I) (M := M) hLC g
    (lcOf_field_smooth hLC g (hEf i) hW) (hEf j) (hEf k) (hEf l)).contMDiffAt (x := z)
  have h3 := (Work.Diff.GE.rmP_fields_smooth (I := I) (M := M) hLC g
    (hEf i) (lcOf_field_smooth hLC g (hEf j) hW) (hEf k) (hEf l)).contMDiffAt (x := z)
  have h4 := (Work.Diff.GE.rmP_fields_smooth (I := I) (M := M) hLC g
    (hEf i) (hEf j) (lcOf_field_smooth hLC g (hEf k) hW) (hEf l)).contMDiffAt (x := z)
  have h5 := (Work.Diff.GE.rmP_fields_smooth (I := I) (M := M) hLC g
    (hEf i) (hEf j) (hEf k) (lcOf_field_smooth hLC g (hEf l) hW)).contMDiffAt (x := z)
  have h6 := (Work.Diff.GE.covRm_fields_smooth (I := I) (M := M) (g := g) hLC hW (hEf i)
    (hEf j) (hEf k) (hEf l)).contMDiffAt (x := z)
  have h := ((h6.add h2).add h3 |>.add h4).add h5
  have hfun : rmFirstTerm g Ef W i j k l
      = fun y : M => covRm g y (W y) (Ef i y) (Ef j y) (Ef k y) (Ef l y)
        + rmP g y (lcOf g (Ef i) y (W y)) (Ef j y) (Ef k y) (Ef l y)
        + rmP g y (Ef i y) (lcOf g (Ef j) y (W y)) (Ef k y) (Ef l y)
        + rmP g y (Ef i y) (Ef j y) (lcOf g (Ef k) y (W y)) (Ef l y)
        + rmP g y (Ef i y) (Ef j y) (Ef k y) (lcOf g (Ef l) y (W y)) := rfl
  rw [hfun]
  exact h

/-- Smoothness at `z` of the curvature array of a frame field. -/
theorem contMDiffAt_rmFrame (hLC : LCSmooth I M) (g : SMet I M)
    (Ef : Fin (Module.finrank ℝ E) → Π y : M, TangentSpace I y)
    (hEf : ∀ i, SmoothField I M (Ef i)) (z : M) :
    ContMDiffAt I 𝓘(ℝ, Curv4 (Module.finrank ℝ E)) ∞
      (fun y : M => rmFrame g y (fun i => Ef i y)) z := by
  rw [contMDiffAt_pi_space]
  intro i
  rw [contMDiffAt_pi_space]
  intro j
  rw [contMDiffAt_pi_space]
  intro k
  rw [contMDiffAt_pi_space]
  intro l
  exact (Work.Diff.GE.rmP_fields_smooth (I := I) (M := M) hLC g
    (hEf i) (hEf j) (hEf k) (hEf l)).contMDiffAt (x := z)

/-! ## Linear combinations: the `ℓ`-coordinate calculus -/

/-- A finite sum of differentiable functions is differentiable. -/
theorem mdiffAt_finset_sum {ι : Type*} (s : Finset ι) (F : ι → M → ℝ)
    (hF : ∀ i ∈ s, MDiffAt (F i) x) :
    MDiffAt (fun y : M => ∑ i ∈ s, F i y) x := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using mdifferentiableAt_const (c := (0 : ℝ))
  | insert a s ha ih =>
      have ha' : MDiffAt (F a) x := hF a (Finset.mem_insert_self a s)
      have hs' : ∀ i ∈ s, MDiffAt (F i) x := fun i hi => hF i (Finset.mem_insert_of_mem hi)
      have hs := ih hs'
      have hfun : (fun y : M => ∑ i ∈ insert a s, F i y) = F a + fun y : M => ∑ i ∈ s, F i y := by
        funext y; rw [Finset.sum_insert ha]; rfl
      rw [hfun]
      exact ha'.add hs

/-- `mvfderiv` of a finite sum of real functions, in applied form. -/
theorem mvfderiv_finset_sum {ι : Type*} (s : Finset ι) (F : ι → M → ℝ)
    (hF : ∀ i ∈ s, MDiffAt (F i) x) (v : TangentSpace I x) :
    mvfderiv I (fun y : M => ∑ i ∈ s, F i y) x v = ∑ i ∈ s, mvfderiv I (F i) x v := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      have h0 : (fun y : M => ∑ i ∈ ∅, F i y) = fun _ : M => (0 : ℝ) := by
        funext y; simp
      rw [h0]
      simp [mvfderiv_const]
  | insert a s ha ih =>
      have ha' : MDiffAt (F a) x := hF a (Finset.mem_insert_self a s)
      have hs' : ∀ i ∈ s, MDiffAt (F i) x := fun i hi => hF i (Finset.mem_insert_of_mem hi)
      have hs := mdiffAt_finset_sum s F hs'
      have hfun : (fun y : M => ∑ i ∈ insert a s, F i y) = F a + fun y : M => ∑ i ∈ s, F i y := by
        funext y; rw [Finset.sum_insert ha]; rfl
      rw [hfun, congrArg (fun L : TangentSpace I x →L[ℝ] ℝ => L v) (mvfderiv_add ha' hs),
        add_apply, ih hs', Finset.sum_insert ha]

/-- `mvfderiv` of a constant multiple, in applied form. -/
theorem mvfderiv_const_mul (c : ℝ) {F : M → ℝ} (hF : MDiffAt F x) (v : TangentSpace I x) :
    mvfderiv I (fun y : M => c * F y) x v = c * mvfderiv I F x v := by
  have hfun : (fun y : M => c * F y) = (fun _ : M => c) • F := by
    funext y; simp [smul_eq_mul]
  have hc : mvfderiv I (fun _ : M => c) x = 0 := mvfderiv_const (c := c)
  rw [hfun, congrArg (fun L : TangentSpace I x →L[ℝ] ℝ => L v)
      (mvfderiv_smul (mdifferentiableAt_const (c := c)) hF), add_apply, smul_apply, hc]
  simp [smul_eq_mul]

/-- **Flattened expansion of `ℓ` applied to the curvature array of a frame field.** -/
theorem ell_rmFrame_eq_sum (hLC : LCSmooth I M) (g : SMet I M)
    (ℓ : Curv4 (Module.finrank ℝ E) →L[ℝ] ℝ)
    (Ef : Fin (Module.finrank ℝ E) → Π y : M, TangentSpace I y) (y : M) :
    ℓ (rmFrame g y (fun i => Ef i y))
      = ∑ p, coefF ℓ p * frameCompF g Ef p y := by
  rw [show rmFrame g y (fun i => Ef i y)
      = fun i j k l => frameComp g Ef i j k l y from rfl]
  rw [ell_eq_sum_coef]
  rw [← Fintype.sum_prod_type
      (f := fun p : Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E) =>
        ∑ k, ∑ l, coef ℓ p.1 p.2 k l * frameComp g Ef p.1 p.2 k l y),
    ← Fintype.sum_prod_type
      (f := fun p : (Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E)) ×
          Fin (Module.finrank ℝ E) =>
        ∑ l, coef ℓ p.1.1 p.1.2 p.2 l * frameComp g Ef p.1.1 p.1.2 p.2 l y),
    ← Fintype.sum_prod_type
      (f := fun p : ((Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E)) ×
          Fin (Module.finrank ℝ E)) × Fin (Module.finrank ℝ E) =>
        coef ℓ p.1.1.1 p.1.1.2 p.1.2 p.2 * frameComp g Ef p.1.1.1 p.1.1.2 p.1.2 p.2 y)]
  rfl

/-- Reverse flattened expansion: a sum against the coordinates of `ℓ` is `ℓ` applied to the array. -/
theorem sum_coefF_eq {n : ℕ} (ℓ : Curv4 n →L[ℝ] ℝ) (X : Curv4 n) :
    (∑ p, coefF ℓ p * X p.1.1.1 p.1.1.2 p.1.2 p.2) = ℓ X := by
  have h : ℓ X = ∑ p, coefF ℓ p * X p.1.1.1 p.1.1.2 p.1.2 p.2 := by
    rw [ell_eq_sum_coef ℓ X]
    rw [← Fintype.sum_prod_type (f := fun p : Fin n × Fin n =>
        ∑ k, ∑ l, coef ℓ p.1 p.2 k l * X p.1 p.2 k l),
      ← Fintype.sum_prod_type (f := fun p : (Fin n × Fin n) × Fin n =>
        ∑ l, coef ℓ p.1.1 p.1.2 p.2 l * X p.1.1 p.1.2 p.2 l),
      ← Fintype.sum_prod_type (f := fun p : ((Fin n × Fin n) × Fin n) × Fin n =>
        coef ℓ p.1.1.1 p.1.1.2 p.1.2 p.2 * X p.1.1.1 p.1.1.2 p.1.2 p.2)]
    rfl
  exact h.symm

/-! ## The first derivative of `ℓ ∘ Rm` in a frame field -/

/-- **The first derivative of `ℓ ∘ Rm` in a frame field.** -/
theorem mvfderiv_ell_rmFrame_rm (hLC : LCSmooth I M) (g : SMet I M)
    (ℓ : Curv4 (Module.finrank ℝ E) →L[ℝ] ℝ)
    (Ef : Fin (Module.finrank ℝ E) → Π y : M, TangentSpace I y)
    (hEf : ∀ i, SmoothField I M (Ef i))
    (W : Π y : M, TangentSpace I y) (z : M) :
    mvfderiv I (fun y : M => ℓ (rmFrame g y (fun i => Ef i y))) z (W z)
      = ℓ (fun i j k l => rmFirstTerm g Ef W i j k l z) := by
  have hfun : (fun y : M => ℓ (rmFrame g y (fun i => Ef i y)))
      = fun y : M => ∑ p, coefF ℓ p * frameCompF g Ef p y := by
    funext y; exact ell_rmFrame_eq_sum hLC g ℓ Ef y
  rw [hfun]
  have hd : ∀ p, MDiffAt (frameCompF g Ef p) z := fun p =>
    ((frameCompF_smooth hLC g Ef hEf p).contMDiffAt (x := z)).mdifferentiableAt (by simp)
  rw [mvfderiv_finset_sum Finset.univ
    (fun p => fun y : M => coefF ℓ p * frameCompF g Ef p y)
    (fun p _ => (mdifferentiableAt_const (c := coefF ℓ p)).mul (hd p)) (W z)]
  rw [show (∑ p, mvfderiv I (fun y : M => coefF ℓ p * frameCompF g Ef p y) z (W z))
      = ∑ p, coefF ℓ p * mvfderiv I (frameCompF g Ef p) z (W z) from
    Finset.sum_congr rfl
      (fun p _ => mvfderiv_const_mul (coefF ℓ p) (F := frameCompF g Ef p) (hd p) (W z))]
  rw [show (∑ p, coefF ℓ p * mvfderiv I (frameCompF g Ef p) z (W z))
      = ∑ p, coefF ℓ p * rmFirstTerm g Ef W p.1.1.1 p.1.1.2 p.1.2 p.2 z from
    Finset.sum_congr rfl
      (fun p _ => by rw [mvfderiv_frameCompF_rm hLC g Ef hEf W p z])]
  exact sum_coefF_eq ℓ (fun i j k l => rmFirstTerm g Ef W i j k l z)

/-- **The first derivative of `ℓ ∘ Rm` with the first-order condition.** -/
theorem mvfderiv_ell_rmFrame' (hLC : LCSmooth I M) (g : SMet I M)
    (ℓ : Curv4 (Module.finrank ℝ E) →L[ℝ] ℝ)
    (Ef : Fin (Module.finrank ℝ E) → Π y : M, TangentSpace I y)
    (hEf : ∀ i, SmoothField I M (Ef i)) (z : M) (v : TangentSpace I z)
    (hfirst : ∀ (i : Fin (Module.finrank ℝ E)) (u : TangentSpace I z), lcOf g (Ef i) z u = 0) :
    mvfderiv I (fun y : M => ℓ (rmFrame g y (fun i => Ef i y))) z v
      = ℓ (fun i j k l => covRm g z v (Ef i z) (Ef j z) (Ef k z) (Ef l z)) := by
  have hWs : (smoothExt z v) z = v := Work.Diff.GE.smoothExt_apply z v
  have h := mvfderiv_ell_rmFrame_rm hLC g ℓ Ef hEf (smoothExt z v) z
  rw [hWs] at h
  rw [h]
  congr 1
  funext i j k l
  simp only [rmFirstTerm, hWs]
  rw [hfirst i v, hfirst j v, hfirst k v, hfirst l v]
  simp only [rmP_zero_fst hLC g z, rmP_zero_snd hLC g z, rmP_zero_thd hLC g z,
    rmP_zero_fth hLC g z, add_zero]

/-! ## The second derivative of `ℓ ∘ Rm` in a parallel frame -/

/-- The value of the second derivative of a curvature component in a parallel frame: `∇²Rm` on the
values plus the term produced by the acceleration of the test field `W`. -/
noncomputable def rmSecondTerm (g : SMet I M) (z : M)
    (Ef : Fin (Module.finrank ℝ E) → Π y : M, TangentSpace I y)
    (W : Π y : M, TangentSpace I y)
    (i j k l : Fin (Module.finrank ℝ E)) : ℝ :=
  cov2Rm g z (W z) (W z) (Ef i z) (Ef j z) (Ef k z) (Ef l z)
    + covRm g z (lcOf g W z (W z)) (Ef i z) (Ef j z) (Ef k z) (Ef l z)

/-- Additivity of `mvfderiv` over five summands, in applied form. -/
theorem mvfderiv_add5 {f₁ f₂ f₃ f₄ f₅ : M → ℝ} (h₁ : MDiffAt f₁ x) (h₂ : MDiffAt f₂ x)
    (h₃ : MDiffAt f₃ x) (h₄ : MDiffAt f₄ x) (h₅ : MDiffAt f₅ x) (v : TangentSpace I x) :
    mvfderiv I (f₁ + f₂ + f₃ + f₄ + f₅) x v
      = mvfderiv I f₁ x v + mvfderiv I f₂ x v + mvfderiv I f₃ x v + mvfderiv I f₄ x v
        + mvfderiv I f₅ x v := by
  have h1234 : MDiffAt (f₁ + f₂ + f₃ + f₄) x := ((h₁.add h₂).add h₃).add h₄
  have h123 : MDiffAt (f₁ + f₂ + f₃) x := (h₁.add h₂).add h₃
  have h12 : MDiffAt (f₁ + f₂) x := h₁.add h₂
  rw [show (f₁ + f₂ + f₃ + f₄ + f₅ : M → ℝ) = (f₁ + f₂ + f₃ + f₄) + f₅ from rfl,
    congrArg (fun L : TangentSpace I x →L[ℝ] ℝ => L v) (mvfderiv_add h1234 h₅), add_apply,
    show (f₁ + f₂ + f₃ + f₄ : M → ℝ) = (f₁ + f₂ + f₃) + f₄ from rfl,
    congrArg (fun L : TangentSpace I x →L[ℝ] ℝ => L v) (mvfderiv_add h123 h₄), add_apply,
    show (f₁ + f₂ + f₃ : M → ℝ) = (f₁ + f₂) + f₃ from rfl,
    congrArg (fun L : TangentSpace I x →L[ℝ] ℝ => L v) (mvfderiv_add h12 h₃), add_apply,
    congrArg (fun L : TangentSpace I x →L[ℝ] ℝ => L v) (mvfderiv_add h₁ h₂), add_apply]

/-- A smooth field whose first slot vanishes at `z` (and which is first-order parallel at `z`) has
vanishing `rmP`-derivative in the direction `W z`. -/
theorem mvfderiv_rmP_primed_fst (hLC : LCSmooth I M) (g : SMet I M) (z : M)
    {A B C D : Π y : M, TangentSpace I y}
    (hA : SmoothField I M A) (hB : SmoothField I M B) (hC : SmoothField I M C)
    (hD : SmoothField I M D) (W : Π y : M, TangentSpace I y) (hW : SmoothField I M W)
    (hA0 : A z = 0) (hA1 : lcOf g A z (W z) = 0) :
    mvfderiv I (fun y : M => rmP g y (A y) (B y) (C y) (D y)) z (W z) = 0 := by
  rw [rmP_mvfderiv hLC g hA hB hC hD z (W z), hA0, hA1]
  simp only [covRm_zero_snd hLC g z, rmP_zero_fst hLC g z, add_zero]

/-- A smooth field whose second slot vanishes at `z`, with `A` first-order parallel at `z` and `B`
first-order parallel at `z`, has vanishing `rmP`-derivative in the direction `W z`. -/
theorem mvfderiv_rmP_primed_snd (hLC : LCSmooth I M) (g : SMet I M) (z : M)
    {A B C D : Π y : M, TangentSpace I y}
    (hA : SmoothField I M A) (hB : SmoothField I M B) (hC : SmoothField I M C)
    (hD : SmoothField I M D) (W : Π y : M, TangentSpace I y) (hW : SmoothField I M W)
    (hB0 : B z = 0) (hA1 : lcOf g A z (W z) = 0) (hB1 : lcOf g B z (W z) = 0) :
    mvfderiv I (fun y : M => rmP g y (A y) (B y) (C y) (D y)) z (W z) = 0 := by
  rw [rmP_mvfderiv hLC g hA hB hC hD z (W z), hB0, hA1, hB1]
  simp only [covRm_zero_thd hLC g z, rmP_zero_snd hLC g z, rmP_zero_fst hLC g z, add_zero]

/-- A smooth field whose third slot vanishes at `z` (and which is first-order parallel at `z`) has
vanishing `rmP`-derivative in the direction `W z`. -/
theorem mvfderiv_rmP_primed_thd (hLC : LCSmooth I M) (g : SMet I M) (z : M)
    {A B C D : Π y : M, TangentSpace I y}
    (hA : SmoothField I M A) (hB : SmoothField I M B) (hC : SmoothField I M C)
    (hD : SmoothField I M D) (W : Π y : M, TangentSpace I y) (hW : SmoothField I M W)
    (hC0 : C z = 0) (hC1 : lcOf g C z (W z) = 0) :
    mvfderiv I (fun y : M => rmP g y (A y) (B y) (C y) (D y)) z (W z) = 0 := by
  rw [rmP_mvfderiv hLC g hA hB hC hD z (W z), hC0, hC1]
  simp only [covRm_zero_fth hLC g z, rmP_zero_thd hLC g z, rmP_zero_fst hLC g z,
    rmP_zero_snd hLC g z, add_zero]

/-- A smooth field whose fourth slot vanishes at `z` (and which is first-order parallel at `z`) has
vanishing `rmP`-derivative in the direction `W z`. -/
theorem mvfderiv_rmP_primed_fth (hLC : LCSmooth I M) (g : SMet I M) (z : M)
    {A B C D : Π y : M, TangentSpace I y}
    (hA : SmoothField I M A) (hB : SmoothField I M B) (hC : SmoothField I M C)
    (hD : SmoothField I M D) (W : Π y : M, TangentSpace I y) (hW : SmoothField I M W)
    (hD0 : D z = 0) (hD1 : lcOf g D z (W z) = 0) :
    mvfderiv I (fun y : M => rmP g y (A y) (B y) (C y) (D y)) z (W z) = 0 := by
  rw [rmP_mvfderiv hLC g hA hB hC hD z (W z), hD0, hD1]
  simp only [covRm_zero_fif hLC g z, rmP_zero_fth hLC g z, rmP_zero_fst hLC g z,
    rmP_zero_snd hLC g z, rmP_zero_thd hLC g z, add_zero]

/-- **The second derivative of a curvature component in a parallel frame.** -/
theorem mvfderiv_rmFirstTerm (hLC : LCSmooth I M) (g : SMet I M) (z : M)
    (Ef : Fin (Module.finrank ℝ E) → Π y : M, TangentSpace I y)
    (hEf : ∀ i, SmoothField I M (Ef i))
    (hfirst : ∀ (i : Fin (Module.finrank ℝ E)) (v : TangentSpace I z), lcOf g (Ef i) z v = 0)
    (hsecond : ∀ (i : Fin (Module.finrank ℝ E)) (W : Π y : M, TangentSpace I y),
      SmoothField I M W → lcOf g (fun y : M => lcOf g (Ef i) y (W y)) z (W z) = 0)
    (W : Π y : M, TangentSpace I y) (hW : SmoothField I M W)
    (i j k l : Fin (Module.finrank ℝ E)) :
    mvfderiv I (fun y : M => rmFirstTerm g Ef W i j k l y) z (W z)
      = rmSecondTerm g z Ef W i j k l := by
  set X1 : M → ℝ := fun y => covRm g y (W y) (Ef i y) (Ef j y) (Ef k y) (Ef l y) with hX1def
  set X2 : M → ℝ := fun y => rmP g y (lcOf g (Ef i) y (W y)) (Ef j y) (Ef k y) (Ef l y)
    with hX2def
  set X3 : M → ℝ := fun y => rmP g y (Ef i y) (lcOf g (Ef j) y (W y)) (Ef k y) (Ef l y)
    with hX3def
  set X4 : M → ℝ := fun y => rmP g y (Ef i y) (Ef j y) (lcOf g (Ef k) y (W y)) (Ef l y)
    with hX4def
  set X5 : M → ℝ := fun y => rmP g y (Ef i y) (Ef j y) (Ef k y) (lcOf g (Ef l) y (W y))
    with hX5def
  have hfun : (fun y : M => rmFirstTerm g Ef W i j k l y) = X1 + X2 + X3 + X4 + X5 := by
    funext y
    simp only [rmFirstTerm, hX1def, hX2def, hX3def, hX4def, hX5def, Pi.add_apply]
  have hX1d : MDiffAt X1 z := hX1def.symm ▸
    ((Work.Diff.GE.covRm_fields_smooth (I := I) (M := M) (g := g) hLC hW (hEf i) (hEf j)
      (hEf k) (hEf l)).contMDiffAt (x := z)).mdifferentiableAt (by simp)
  have hX2d : MDiffAt X2 z := hX2def.symm ▸
    (((Work.Diff.GE.rmP_fields_smooth (I := I) (M := M) hLC g
      (lcOf_field_smooth hLC g (hEf i) hW) (hEf j) (hEf k) (hEf l)).contMDiffAt
      (x := z)).mdifferentiableAt (by simp))
  have hX3d : MDiffAt X3 z := hX3def.symm ▸
    (((Work.Diff.GE.rmP_fields_smooth (I := I) (M := M) hLC g
      (hEf i) (lcOf_field_smooth hLC g (hEf j) hW) (hEf k) (hEf l)).contMDiffAt
      (x := z)).mdifferentiableAt (by simp))
  have hX4d : MDiffAt X4 z := hX4def.symm ▸
    (((Work.Diff.GE.rmP_fields_smooth (I := I) (M := M) hLC g
      (hEf i) (hEf j) (lcOf_field_smooth hLC g (hEf k) hW) (hEf l)).contMDiffAt
      (x := z)).mdifferentiableAt (by simp))
  have hX5d : MDiffAt X5 z := hX5def.symm ▸
    (((Work.Diff.GE.rmP_fields_smooth (I := I) (M := M) hLC g
      (hEf i) (hEf j) (hEf k) (lcOf_field_smooth hLC g (hEf l) hW)).contMDiffAt
      (x := z)).mdifferentiableAt (by simp))
  have e1 : mvfderiv I X1 z (W z) = rmSecondTerm g z Ef W i j k l := by
    have h := Work.Diff.GE.mvfderiv_covRm_fields (I := I) (M := M) hLC g
      (hV := hW) (hA := hEf i) (hB := hEf j) (hC := hEf k) (hD := hEf l) z (W z)
    rw [hX1def, h, hfirst i (W z), hfirst j (W z), hfirst k (W z), hfirst l (W z)]
    simp only [covRm_zero_thd hLC g z, covRm_zero_fth hLC g z, covRm_zero_fif hLC g z,
      covRm_zero_snd hLC g z, add_zero, rmSecondTerm]
  have e2 : mvfderiv I X2 z (W z) = 0 := by
    rw [hX2def]
    exact mvfderiv_rmP_primed_fst hLC g z (lcOf_field_smooth hLC g (hEf i) hW) (hEf j) (hEf k)
      (hEf l) W hW (hfirst i (W z)) (hsecond i W hW)
  have e3 : mvfderiv I X3 z (W z) = 0 := by
    rw [hX3def]
    exact mvfderiv_rmP_primed_snd hLC g z (hEf i) (lcOf_field_smooth hLC g (hEf j) hW) (hEf k)
      (hEf l) W hW (hfirst j (W z)) (hfirst i (W z)) (hsecond j W hW)
  have e4 : mvfderiv I X4 z (W z) = 0 := by
    rw [hX4def]
    exact mvfderiv_rmP_primed_thd hLC g z (hEf i) (hEf j) (lcOf_field_smooth hLC g (hEf k) hW)
      (hEf l) W hW (hfirst k (W z)) (hsecond k W hW)
  have e5 : mvfderiv I X5 z (W z) = 0 := by
    rw [hX5def]
    exact mvfderiv_rmP_primed_fth hLC g z (hEf i) (hEf j) (hEf k)
      (lcOf_field_smooth hLC g (hEf l) hW) W hW (hfirst l (W z)) (hsecond l W hW)
  rw [hfun, mvfderiv_add5 hX1d hX2d hX3d hX4d hX5d (W z), e1, e2, e3, e4, e5]
  ring

/-- **The derivative of the flattened first term.** -/
theorem mvfderiv_rmFirstTerm_flat (hLC : LCSmooth I M) (g : SMet I M) (z : M)
    (Ef : Fin (Module.finrank ℝ E) → Π y : M, TangentSpace I y)
    (hEf : ∀ i, SmoothField I M (Ef i))
    (hfirst : ∀ (i : Fin (Module.finrank ℝ E)) (v : TangentSpace I z), lcOf g (Ef i) z v = 0)
    (hsecond : ∀ (i : Fin (Module.finrank ℝ E)) (W : Π y : M, TangentSpace I y),
      SmoothField I M W → lcOf g (fun y : M => lcOf g (Ef i) y (W y)) z (W z) = 0)
    (W : Π y : M, TangentSpace I y) (hW : SmoothField I M W)
    (p : ((Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E)) ×
      Fin (Module.finrank ℝ E)) × Fin (Module.finrank ℝ E)) :
    mvfderiv I (fun y : M => rmFirstTerm g Ef W p.1.1.1 p.1.1.2 p.1.2 p.2 y) z (W z)
      = rmSecondTerm g z Ef W p.1.1.1 p.1.1.2 p.1.2 p.2 :=
  mvfderiv_rmFirstTerm hLC g z Ef hEf hfirst hsecond W hW p.1.1.1 p.1.1.2 p.1.2 p.2

/-- **The second derivative of `ℓ ∘ Rm` in a parallel frame.** -/
theorem second_deriv_ell_rmFrame (hLC : LCSmooth I M) (g : SMet I M) (z : M)
    (ℓ : Curv4 (Module.finrank ℝ E) →L[ℝ] ℝ)
    (Ef : Fin (Module.finrank ℝ E) → Π y : M, TangentSpace I y)
    (hEf : ∀ i, SmoothField I M (Ef i))
    (hfirst : ∀ (i : Fin (Module.finrank ℝ E)) (v : TangentSpace I z), lcOf g (Ef i) z v = 0)
    (hsecond : ∀ (i : Fin (Module.finrank ℝ E)) (W : Π y : M, TangentSpace I y),
      SmoothField I M W → lcOf g (fun y : M => lcOf g (Ef i) y (W y)) z (W z) = 0)
    (W : Π y : M, TangentSpace I y) (hW : SmoothField I M W) :
    mvfderiv I (fun y : M =>
        mvfderiv I (fun z : M => ℓ (rmFrame g z (fun i => Ef i z))) y (W y)) z (W z)
      = ℓ (fun i j k l => rmSecondTerm g z Ef W i j k l) := by
  have hfun : (fun y : M => mvfderiv I (fun z : M => ℓ (rmFrame g z (fun i => Ef i z))) y (W y))
      = fun y : M => ∑ p, coefF ℓ p * rmFirstTerm g Ef W p.1.1.1 p.1.1.2 p.1.2 p.2 y := by
    funext y
    rw [mvfderiv_ell_rmFrame_rm hLC g ℓ Ef hEf W y,
      sum_coefF_eq ℓ (fun i j k l => rmFirstTerm g Ef W i j k l y)]
  have hdiff : ∀ p ∈ (Finset.univ : Finset (((Fin (Module.finrank ℝ E) ×
        Fin (Module.finrank ℝ E)) × Fin (Module.finrank ℝ E)) × Fin (Module.finrank ℝ E))),
      MDiffAt (fun y : M => rmFirstTerm g Ef W p.1.1.1 p.1.1.2 p.1.2 p.2 y) z :=
    fun p _ => (contMDiffAt_rmFirstTerm hLC g Ef hEf W hW z p.1.1.1 p.1.1.2 p.1.2
      p.2).mdifferentiableAt (by simp)
  rw [hfun, mvfderiv_finset_sum Finset.univ
    (fun p => fun y : M => coefF ℓ p * rmFirstTerm g Ef W p.1.1.1 p.1.1.2 p.1.2 p.2 y)
    (fun p hp => (mdifferentiableAt_const (c := coefF ℓ p)).mul (hdiff p hp)) (W z)]
  rw [show (∑ p, mvfderiv I (fun y : M =>
        coefF ℓ p * rmFirstTerm g Ef W p.1.1.1 p.1.1.2 p.1.2 p.2 y) z (W z))
      = ∑ p, coefF ℓ p * mvfderiv I (fun y : M =>
          rmFirstTerm g Ef W p.1.1.1 p.1.1.2 p.1.2 p.2 y) z (W z) from
    Finset.sum_congr rfl (fun p _ => mvfderiv_const_mul (coefF ℓ p)
      (F := fun y : M => rmFirstTerm g Ef W p.1.1.1 p.1.1.2 p.1.2 p.2 y)
      (hdiff p (Finset.mem_univ p)) (W z))]
  rw [show (∑ p, coefF ℓ p * mvfderiv I (fun y : M =>
        rmFirstTerm g Ef W p.1.1.1 p.1.1.2 p.1.2 p.2 y) z (W z))
      = ∑ p, coefF ℓ p * rmSecondTerm g z Ef W p.1.1.1 p.1.1.2 p.1.2 p.2 from
    Finset.sum_congr rfl (fun p _ => by
      rw [mvfderiv_rmFirstTerm_flat hLC g z Ef hEf hfirst hsecond W hW p])]
  exact sum_coefF_eq ℓ (fun i j k l => rmSecondTerm g z Ef W i j k l)

/-! ## The Hessian of `ℓ ∘ Rm` and the assembly -/

/-- **The Hessian of `ℓ ∘ Rm` in a parallel frame.**  Both `∇_{∇_W W}` terms of `hessAt` cancel. -/
theorem hessAt_ell_rmFrame (hLC : LCSmooth I M) (g : SMet I M) (z : M)
    (ℓ : Curv4 (Module.finrank ℝ E) →L[ℝ] ℝ)
    (Ef : Fin (Module.finrank ℝ E) → Π y : M, TangentSpace I y)
    (hEf : ∀ i, SmoothField I M (Ef i))
    (hfirst : ∀ (i : Fin (Module.finrank ℝ E)) (v : TangentSpace I z), lcOf g (Ef i) z v = 0)
    (hsecond : ∀ (i : Fin (Module.finrank ℝ E)) (W : Π y : M, TangentSpace I y),
      SmoothField I M W → lcOf g (fun y : M => lcOf g (Ef i) y (W y)) z (W z) = 0)
    (v : TangentSpace I z) :
    hessAt g (fun y : M => ℓ (rmFrame g y (fun i => Ef i y))) z v v
      = ℓ (fun i j k l => cov2Rm g z v v (Ef i z) (Ef j z) (Ef k z) (Ef l z)) := by
  have hWs : (smoothExt z v) z = v := Work.Diff.GE.smoothExt_apply z v
  have hW : SmoothField I M (smoothExt z v) := Work.Diff.GE.smoothExt_cmdiff z v
  have h2 := second_deriv_ell_rmFrame hLC g z ℓ Ef hEf hfirst hsecond (smoothExt z v) hW
  rw [hWs] at h2
  have h1 := mvfderiv_ell_rmFrame' hLC g ℓ Ef hEf z (lcOf g (smoothExt z v) z v) hfirst
  rw [hessAt, h2, h1, ← map_sub]
  congr 1
  funext i j k l
  simp only [rmSecondTerm, hWs, Pi.sub_apply]
  ring

/-- The frozen `Submission.Diff.cov2Rm` agrees with the `Work.Diff.GE` version on values. -/
theorem cov2Rm_eq_GE (g : SMet I M) (z : M) (v w a b c d : TangentSpace I z) :
    cov2Rm g z v w a b c d = Work.Diff.GE.cov2Rm g z v w a b c d :=
  (cov2RmExt_smoothExt_eq_cov2Rm g z v w a b c d).symm

/-- **Frame independence of the trace of `∇²Rm`**: the trace may be computed in any
`g`-orthonormal frame. -/
theorem cov2Rm_trace_indep (hLC : LCSmooth I M) (g : SMet I M) (z : M)
    (e e' : Fin (Module.finrank ℝ E) → TangentSpace I z)
    (he : IsONFrame g z e) (he' : IsONFrame g z e') (a b c d : TangentSpace I z) :
    (∑ m, cov2Rm g z (e m) (e m) a b c d) = ∑ m, cov2Rm g z (e' m) (e' m) a b c d := by
  rw [show (∑ m, cov2Rm g z (e m) (e m) a b c d)
      = ∑ m, Work.Diff.GE.cov2Rm g z (e m) (e m) a b c d from
    Finset.sum_congr rfl (fun m _ => cov2Rm_eq_GE g z (e m) (e m) a b c d)]
  rw [show (∑ m, cov2Rm g z (e' m) (e' m) a b c d)
      = ∑ m, Work.Diff.GE.cov2Rm g z (e' m) (e' m) a b c d from
    Finset.sum_congr rfl (fun m _ => cov2Rm_eq_GE g z (e' m) (e' m) a b c d)]
  rw [← Work.Diff.GE.lapRmAt_trace (I := I) (M := M) hLC g z e he a b c d,
    ← Work.Diff.GE.lapRmAt_trace (I := I) (M := M) hLC g z e' he' a b c d]

/-- **Frame independence of the trace of `∇²Rm`**, in the form used by the assembly: the trace part
of `lapRmFrame` may be computed in any `g`-orthonormal frame (the four free slots are held fixed). -/
theorem cov2Rm_trace_indep_slots (hLC : LCSmooth I M) (g : SMet I M) (z : M)
    (e e' : Fin (Module.finrank ℝ E) → TangentSpace I z)
    (he : IsONFrame g z e) (he' : IsONFrame g z e') (a b c d : TangentSpace I z) :
    (∑ m, cov2Rm g z (e m) (e m) a b c d) = ∑ m, cov2Rm g z (e' m) (e' m) a b c d :=
  cov2Rm_trace_indep hLC g z e e' he he' a b c d

/-- **The assembly of `LapRmFrameParallel`** from a frame field which is parallel at `z` to first
and second order. -/
theorem laplAt_ell_rmFrame_eq (hLC : LCSmooth I M) (g : SMet I M) (z : M)
    (e : Fin (Module.finrank ℝ E) → TangentSpace I z) (he : IsONFrame g z e)
    (Ef : Fin (Module.finrank ℝ E) → Π y : M, TangentSpace I y)
    (hval : ∀ i, Ef i z = e i) (hEf : ∀ i, SmoothField I M (Ef i))
    (hfirst : ∀ (i : Fin (Module.finrank ℝ E)) (v : TangentSpace I z), lcOf g (Ef i) z v = 0)
    (hsecond : ∀ (i : Fin (Module.finrank ℝ E)) (W : Π y : M, TangentSpace I y),
      SmoothField I M W → lcOf g (fun y : M => lcOf g (Ef i) y (W y)) z (W z) = 0)
    (ℓ : Curv4 (Module.finrank ℝ E) →L[ℝ] ℝ) :
    laplAt g (fun y : M => ℓ (rmFrame g y (fun i => Ef i y))) z = ℓ (lapRmFrame g z e) := by
  classical
  let u : M → ℝ := fun y => ℓ (rmFrame g y (fun i => Ef i y))
  have hu : ContMDiffAt I 𝓘(ℝ, ℝ) ∞ u z :=
    ℓ.contMDiff.contMDiffAt.comp z (contMDiffAt_rmFrame hLC g Ef hEf z)
  have h2 : ContMDiffAt I (modelWithCornersSelf ℝ ℝ) 2 u z := hu.of_le (by simp)
  have hsym : ∀ v w : TangentSpace I z, hessAt g u z v w = hessAt g u z w v :=
    fun v w => Work.Diff.GE.hessAt_comm (I := I) (M := M) hLC g u z h2 v w
  rw [Work.Diff.GE.laplAt_eq_sum_hessAt (I := I) (M := M) g u z (onFrame g z)
    (Work.Diff.GE.isONFrame_onFrame g z) hsym]
  have hsum : (∑ m, hessAt g u z (onFrame g z m) (onFrame g z m))
      = ∑ m, ℓ (fun i j k l => cov2Rm g z (onFrame g z m) (onFrame g z m) (e i) (e j)
          (e k) (e l)) := by
    refine Finset.sum_congr rfl (fun m _ => ?_)
    have h := hessAt_ell_rmFrame hLC g z ℓ Ef hEf hfirst hsecond (onFrame g z m)
    rw [h]
    congr 1
    funext i j k l
    rw [hval i, hval j, hval k, hval l]
  rw [hsum, ← map_sum]
  congr 1
  funext i j k l
  simp only [Finset.sum_apply, lapRmFrame]
  exact cov2Rm_trace_indep (I := I) (M := M) hLC g z (onFrame g z) e
    (Work.Diff.GE.isONFrame_onFrame g z) he (e i) (e j) (e k) (e l)

end Work.Diff.Evol
