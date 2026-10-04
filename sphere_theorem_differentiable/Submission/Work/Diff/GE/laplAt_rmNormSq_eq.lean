import Mathlib
import Submission.Work.Diff.GE.Frame
import Submission.Work.Diff.GE.curvbasic
import Submission.Work.Diff.PP.evolution
import Submission.Work.Diff.GE.NablaRm
import Submission.Work.Diff.GE.dRmPhi
import Submission.Work.Diff.GE.dRmPhi_slotA
import Submission.Work.Diff.GE.covRm_linear_fth
import Submission.Work.Diff.GE.rmFrame_eq_rot
import Submission.Work.Diff.GE.onFrame_orthogonal_change
import Submission.Work.Diff.GE.rot_frobsq
import Submission.Work.Diff.GE.Gest.Base
import Submission.Work.Diff.GE.Gest.hess_mul_field
import Submission.Work.Diff.GE.Gest.lapl_mul
import Submission.Work.Diff.GE.Gest.lapl_sq
import Submission.Work.Diff.GE.kato_lapl_sum
import Submission.Work.Diff.GE.gradSq_rmoNormSq
import Submission.Work.Diff.GE.kato_cov2RmExt_field
import Submission.Work.Diff.GE.Kato3.CovRmKit
import Submission.Work.Diff.GE.cov2RmExt_prelim
import Submission.Work.Diff.GE.FrameIndep
import Submission.Work.Diff.GE.kato_frame_second_antisymm
import Submission.Work.Diff.GE.mvfderivWithin_apply_mlieBracketWithin_two
import Submission.Work.Diff.GE.kato_leftover_sum
import Submission.Work.Diff.GE.kato_second_deriv_defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.GE

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology BigOperators
open Bundle ContDiff Set VectorField CovariantDerivative Metric
open Commons.Geometry.Manifold.VectorField

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1000000

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]

/-! ## Locality of `laplAt` -/

/-- `laplAt g · x` only depends on the germ of the function at `x`. -/
theorem laplAt_congr_eventuallyEq (g : SMet I M) {u v : M → ℝ} (x : M)
    (h : u =ᶠ[𝓝 x] v) : laplAt g u x = laplAt g v x := by
  have hmem : {z : M | u z = v z} ∈ 𝓝 x := h
  have hx : x ∈ interior {z : M | u z = v z} := mem_interior_iff_mem_nhds.mpr hmem
  have hinner : ∀ w : TangentSpace I x,
      (fun y : M ↦ mvfderiv I u y (smoothExt x w y))
        =ᶠ[𝓝 x] (fun y : M ↦ mvfderiv I v y (smoothExt x w y)) := by
    intro w
    filter_upwards [isOpen_interior.mem_nhds hx] with y hy
    rw [mvfderiv_congr_eventuallyEq (I := I)
      (Filter.mem_of_superset (isOpen_interior.mem_nhds hy) interior_subset)]
  simp only [laplAt, hessAt]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [mvfderiv_congr_eventuallyEq (I := I) (hinner (onFrame g x i)),
    mvfderiv_congr_eventuallyEq (I := I) h]

/-! ## The Hessian in a smooth field -/

/-- **`hessAt` depends on its second argument only through the value.**  For a function `u` smooth at
`x`, the frozen `hessAt g u x v w` (defined with the `Classical.epsilon`-chosen extension
`smoothExt x w`) equals the field-based expression with any smooth field `Z` with `Z x = w`. -/
theorem hessAt_field_eq (hLC : LCSmooth I M) (g : SMet I M) (x : M) {u : M → ℝ}
    (hu : ContMDiffAt I 𝓘(ℝ, ℝ) ∞ u x)
    (Y Z : Π y : M, TangentSpace I y) (hY : CMDiff ∞ (T% Y)) (hZ : CMDiff ∞ (T% Z)) :
    hessAt g u x (Y x) (Z x)
      = mvfderiv I (fun y : M ↦ mvfderiv I u y (Z y)) x (Y x)
        - mvfderiv I u x (lcOf g Z x (Y x)) := by
  classical
  haveI : IsManifold I (2 : ℕ∞ω) M :=
    IsManifold.of_le (I := I) (M := M) (m := (2 : ℕ∞ω)) (n := ∞) (by simp)
  obtain ⟨U, hUopen, hxU, hUsm⟩ :=
    hu.contMDiffOn' (m := (2 : ℕ∞ω)) (n := ∞) (by simp) (by intro h; exact absurd h (by decide))
  have hUsm' : CMDiff[U] (2 : ℕ∞ω) u := by simpa using hUsm
  have hUmems : U ∈ 𝓝 x := hUopen.mem_nhds hxU
  have hw : ∀ (F : M → ℝ), mvfderivWithin I F U x = mvfderiv I F x :=
    fun F => by simp only [mvfderivWithin, mvfderiv, mfderivWithin_of_mem_nhds hUmems]
  have hconv : ∀ (B' : Π z : M, TangentSpace I z),
      mvfderivWithin I (fun z => mvfderivWithin I u U z (B' z)) U x
        = mvfderiv I (fun z => mvfderiv I u z (B' z)) x := by
    intro B'
    have hev : (fun z => mvfderiv I u z (B' z)) =ᶠ[𝓝[U] x]
        (fun z => mvfderivWithin I u U z (B' z)) := by
      filter_upwards [self_mem_nhdsWithin] with z hz
      simp only [mvfderivWithin, mvfderiv, mfderivWithin_of_isOpen hUopen hz]
    have hx' : (fun z => mvfderiv I u z (B' z)) x
        = (fun z => mvfderivWithin I u U z (B' z)) x := by
      simp only [mvfderivWithin, mvfderiv, mfderivWithin_of_isOpen hUopen hxU]
    have hcongr := Commons.Geometry.Manifold.VectorField.mvfderivWithin_congr_eventually
      (I := I) (s := U) (x := x) hev hx'
    rw [← hcongr, hw (fun z => mvfderiv I u z (B' z))]
  have key : ∀ (A B : Π y : M, TangentSpace I y), CMDiff ∞ (T% A) → CMDiff ∞ (T% B) →
      mvfderiv I (fun y => mvfderiv I u y (B y)) x (A x)
        = mvfderiv I (fun y => mvfderiv I u y (A y)) x (B x)
          + mvfderiv I u x (mlieBracket I A B x) := by
    intro A B hA hB
    have hAs : CMDiff[U] ∞ (T% A) := (contMDiffOn_univ.mpr hA).mono (subset_univ U)
    have hBs : CMDiff[U] ∞ (T% B) := (contMDiffOn_univ.mpr hB).mono (subset_univ U)
    have hxs' : x ∈ closure (interior U) := by
      rw [hUopen.interior_eq]; exact subset_closure hxU
    have hmain := Work.Diff.GE.mvfderivWithin_apply_mlieBracketWithin_two (s := U) (f := u)
      (X := A) (Y := B) (x := x)
      hUopen.uniqueMDiffOn hxU hxs' hUsm' hAs hBs
    have hbr : mvfderivWithin I u U x (mlieBracketWithin I A B U x)
        = mvfderiv I u x (mlieBracket I A B x) := by
      rw [hw u]
      congr 1
      rw [← mlieBracketWithin_univ, ← univ_inter U,
        mlieBracketWithin_inter (s := univ) (t := U) hUmems]
    rw [hconv B, hconv A, hbr] at hmain
    exact hmain
  have hW : CMDiff ∞ (T% (smoothExt x (Z x))) := smoothExt_cmdiff x (Z x)
  have hWx : smoothExt x (Z x) x = Z x := smoothExt_apply x (Z x)
  have hYm : MDiffAt (T% Y) x := hY.contMDiffAt.mdifferentiableAt (by simp)
  have hWm : MDiffAt (T% (smoothExt x (Z x))) x := hW.contMDiffAt.mdifferentiableAt (by simp)
  have hZm : MDiffAt (T% Z) x := hZ.contMDiffAt.mdifferentiableAt (by simp)
  have htors : ∀ {A B : Π y : M, TangentSpace I y},
      MDiffAt (T% A) x → MDiffAt (T% B) x →
      ((lcOf g) B x) (A x) - ((lcOf g) A x) (B x) = mlieBracket I A B x :=
    fun hA hB => (CovariantDerivative.torsion_eq_zero_iff (lcOf g)).1 (hLC g).2.1 hA hB
  have htor1 : mlieBracket I Y (smoothExt x (Z x)) x
      = ((lcOf g) (smoothExt x (Z x)) x) (Y x) - ((lcOf g) Y x) (smoothExt x (Z x) x) :=
    (htors hYm hWm).symm
  have htor2 : mlieBracket I Y Z x = ((lcOf g) Z x) (Y x) - ((lcOf g) Y x) (Z x) :=
    (htors hYm hZm).symm
  have hkey1 := key Y (smoothExt x (Z x)) hY hW
  have hkey2 := key Y Z hY hZ
  rw [hessAt, hkey1, hkey2, htor1, htor2, hWx, map_sub, map_sub]
  abel

/-! ## `laplAt` in a geodesic frame -/

/-- **`laplAt` in a frame that is geodesic at `x`.** -/
theorem laplAt_eq_sum_frame (hLC : LCSmooth I M) (g : SMet I M) (x : M)
    (W : Fin (Module.finrank ℝ E) → (Π y : M, TangentSpace I y))
    (hWs : ∀ i, CMDiff ∞ (T% (W i))) (hWx : ∀ i, W i x = onFrame g x i)
    (hgeo : ∀ m j, lcOf g (W j) x (W m x) = 0)
    {u : M → ℝ} (hu : ContMDiffAt I 𝓘(ℝ,ℝ) ∞ u x) :
    laplAt g u x = ∑ i, mvfderiv I (fun y : M => mvfderiv I u y (W i y)) x (W i x) := by
  simp only [laplAt]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  have h1 := hessAt_field_eq (I := I) (M := M) hLC g x hu (W i) (W i) (hWs i) (hWs i)
  rw [← hWx i, h1, hgeo i i, map_zero, sub_zero]


/-! ## `rmP` vanishes on a zero argument, and derivatives of `rmP` on a field that vanishes -/

theorem rmP_zero_slot1 (hLC : LCSmooth I M) (g : SMet I M) (x : M)
    (b c d : TangentSpace I x) : rmP g x 0 b c d = 0 := by
  simpa using rmP_smul_fst (I := I) (M := M) g hLC x (0 : ℝ) (0 : TangentSpace I x) b c d

theorem rmP_zero_slot2 (hLC : LCSmooth I M) (g : SMet I M) (x : M)
    (a c d : TangentSpace I x) : rmP g x a 0 c d = 0 := by
  simpa using rmP_smul_snd (I := I) (M := M) g hLC x (0 : ℝ) a (0 : TangentSpace I x) c d

theorem rmP_zero_slot3 (hLC : LCSmooth I M) (g : SMet I M) (x : M)
    (a b d : TangentSpace I x) : rmP g x a b 0 d = 0 := by
  simpa using rmP_smul_thd (I := I) (M := M) g hLC x (0 : ℝ) a b (0 : TangentSpace I x) d

theorem rmP_zero_slot4 (hLC : LCSmooth I M) (g : SMet I M) (x : M)
    (a b c : TangentSpace I x) : rmP g x a b c 0 = 0 := by
  simpa using rmP_smul_fth (I := I) (M := M) g hLC x (0 : ℝ) a b c (0 : TangentSpace I x)

/-- The fourth field slot of `dRmPhi` vanishes on a field vanishing at the base point. -/
theorem dRmPhi_zero_fif (hLC : LCSmooth I M) {g : SMet I M} {x : M} {v : TangentSpace I x}
    {A B C D : Π y : M, TangentSpace I y}
    (hA : CMDiff ∞ (T% A)) (hB : CMDiff ∞ (T% B)) (hC : CMDiff ∞ (T% C)) (hD : CMDiff ∞ (T% D))
    (hDx : D x = 0) : dRmPhi g x v A B C D = 0 := by
  have h1 := dRmPhi_skew_thd_fth (g := g) (x := x) (v := v) hLC hA hB hC hD
  have h2 := fth_dRmPhi_zero (g := g) (x := x) (v := v) hLC hA hB hD hC hDx
  rw [h1, h2, neg_zero]

/-- Derivative at `x` along `U x` of a component of `rmP` whose first slot field vanishes at `x`. -/
theorem deriv_rmP_zero_slot1 (hLC : LCSmooth I M) (g : SMet I M) (x : M)
    (X A B C : Π y : M, TangentSpace I y)
    (hX : CMDiff ∞ (T% X)) (hA : CMDiff ∞ (T% A)) (hB : CMDiff ∞ (T% B)) (hC : CMDiff ∞ (T% C))
    (U : Π y : M, TangentSpace I y) (hU : CMDiff ∞ (T% U)) (hXx : X x = 0) :
    mvfderiv I (fun y : M ↦ rmP g y (X y) (A y) (B y) (C y)) x (U x)
      = rmP g x (lcOf g X x (U x)) (A x) (B x) (C x) := by
  have h1 : mvfderiv I (fun y : M ↦ rmP g y (X y) (A y) (B y) (C y)) x (U x)
      = dRmPhi g x (U x) X A B C
        + rmP g x (lcOf g X x (U x)) (A x) (B x) (C x)
        + rmP g x (X x) (lcOf g A x (U x)) (B x) (C x)
        + rmP g x (X x) (A x) (lcOf g B x (U x)) (C x)
        + rmP g x (X x) (A x) (B x) (lcOf g C x (U x)) := by
    simp only [dRmPhi]
    ring
  rw [h1, dRmPhi_zero_fst (g := g) (x := x) (v := U x) hLC hX hA hB hC hXx]
  rw [hXx, rmP_zero_slot1 (I := I) (M := M) hLC g x, rmP_zero_slot1 (I := I) (M := M) hLC g x,
    rmP_zero_slot1 (I := I) (M := M) hLC g x]
  ring

/-- Derivative at `x` along `U x` of a component of `rmP` whose second slot field vanishes at `x`. -/
theorem deriv_rmP_zero_slot2 (hLC : LCSmooth I M) (g : SMet I M) (x : M)
    (A X B C : Π y : M, TangentSpace I y)
    (hA : CMDiff ∞ (T% A)) (hX : CMDiff ∞ (T% X)) (hB : CMDiff ∞ (T% B)) (hC : CMDiff ∞ (T% C))
    (U : Π y : M, TangentSpace I y) (hU : CMDiff ∞ (T% U)) (hXx : X x = 0) :
    mvfderiv I (fun y : M ↦ rmP g y (A y) (X y) (B y) (C y)) x (U x)
      = rmP g x (A x) (lcOf g X x (U x)) (B x) (C x) := by
  have h1 : mvfderiv I (fun y : M ↦ rmP g y (A y) (X y) (B y) (C y)) x (U x)
      = dRmPhi g x (U x) A X B C
        + rmP g x (lcOf g A x (U x)) (X x) (B x) (C x)
        + rmP g x (A x) (lcOf g X x (U x)) (B x) (C x)
        + rmP g x (A x) (X x) (lcOf g B x (U x)) (C x)
        + rmP g x (A x) (X x) (B x) (lcOf g C x (U x)) := by
    simp only [dRmPhi]
    ring
  rw [h1, dRmPhi_zero_slotB (g := g) (x := x) (v := U x) hLC hA hX hB hC hXx]
  rw [hXx, rmP_zero_slot2 (I := I) (M := M) hLC g x, rmP_zero_slot2 (I := I) (M := M) hLC g x,
    rmP_zero_slot2 (I := I) (M := M) hLC g x]
  ring

/-- Derivative at `x` along `U x` of a component of `rmP` whose third slot field vanishes at `x`. -/
theorem deriv_rmP_zero_slot3 (hLC : LCSmooth I M) (g : SMet I M) (x : M)
    (A B X C : Π y : M, TangentSpace I y)
    (hA : CMDiff ∞ (T% A)) (hB : CMDiff ∞ (T% B)) (hX : CMDiff ∞ (T% X)) (hC : CMDiff ∞ (T% C))
    (U : Π y : M, TangentSpace I y) (hU : CMDiff ∞ (T% U)) (hXx : X x = 0) :
    mvfderiv I (fun y : M ↦ rmP g y (A y) (B y) (X y) (C y)) x (U x)
      = rmP g x (A x) (B x) (lcOf g X x (U x)) (C x) := by
  have h1 : mvfderiv I (fun y : M ↦ rmP g y (A y) (B y) (X y) (C y)) x (U x)
      = dRmPhi g x (U x) A B X C
        + rmP g x (lcOf g A x (U x)) (B x) (X x) (C x)
        + rmP g x (A x) (lcOf g B x (U x)) (X x) (C x)
        + rmP g x (A x) (B x) (lcOf g X x (U x)) (C x)
        + rmP g x (A x) (B x) (X x) (lcOf g C x (U x)) := by
    simp only [dRmPhi]
    ring
  rw [h1, fth_dRmPhi_zero (g := g) (x := x) (v := U x) hLC hA hB hX hC hXx]
  rw [hXx, rmP_zero_slot3 (I := I) (M := M) hLC g x, rmP_zero_slot3 (I := I) (M := M) hLC g x,
    rmP_zero_slot3 (I := I) (M := M) hLC g x]
  ring

/-- Derivative at `x` along `U x` of a component of `rmP` whose fourth slot field vanishes at `x`. -/
theorem deriv_rmP_zero_slot4 (hLC : LCSmooth I M) (g : SMet I M) (x : M)
    (A B C X : Π y : M, TangentSpace I y)
    (hA : CMDiff ∞ (T% A)) (hB : CMDiff ∞ (T% B)) (hC : CMDiff ∞ (T% C)) (hX : CMDiff ∞ (T% X))
    (U : Π y : M, TangentSpace I y) (hU : CMDiff ∞ (T% U)) (hXx : X x = 0) :
    mvfderiv I (fun y : M ↦ rmP g y (A y) (B y) (C y) (X y)) x (U x)
      = rmP g x (A x) (B x) (C x) (lcOf g X x (U x)) := by
  have h1 : mvfderiv I (fun y : M ↦ rmP g y (A y) (B y) (C y) (X y)) x (U x)
      = dRmPhi g x (U x) A B C X
        + rmP g x (lcOf g A x (U x)) (B x) (C x) (X x)
        + rmP g x (A x) (lcOf g B x (U x)) (C x) (X x)
        + rmP g x (A x) (B x) (lcOf g C x (U x)) (X x)
        + rmP g x (A x) (B x) (C x) (lcOf g X x (U x)) := by
    simp only [dRmPhi]
    ring
  rw [h1, dRmPhi_zero_fif (g := g) (x := x) (v := U x) hLC hA hB hC hX hXx]
  rw [hXx, rmP_zero_slot4 (I := I) (M := M) hLC g x, rmP_zero_slot4 (I := I) (M := M) hLC g x,
    rmP_zero_slot4 (I := I) (M := M) hLC g x]
  ring


/-! ## The frame components of the curvature and their first two derivatives -/

/-- The `(0,4)`-tensor `Rm` evaluated on four vectors of the frame. -/
noncomputable def P4 (g : SMet I M) (x : M) (v : Fin 4 → TangentSpace I x) : ℝ :=
  rmP g x (v 0) (v 1) (v 2) (v 3)

/-- The vector `∇_{W i x}(∇_{W i} W γ)`: the second-order frame correction. -/
noncomputable def Avec4 (g : SMet I M)
    (W : Fin (Module.finrank ℝ E) → (Π y : M, TangentSpace I y)) (x : M)
    (i γ : Fin (Module.finrank ℝ E)) : TangentSpace I x :=
  lcOf g (fun p : M ↦ lcOf g (W γ) p (W i p)) x (W i x)

/-- The derivative of a component of `∇Rm` along the frame field is the corresponding component of
`∇²Rm`, when the frame is geodesic at `x`. -/
theorem mvfderiv_covRm_geodesic (hLC : LCSmooth I M) (g : SMet I M) (x : M)
    (W : Fin (Module.finrank ℝ E) → (Π y : M, TangentSpace I y))
    (hWs : ∀ i, CMDiff ∞ (T% (W i))) (hgeo : ∀ m j, lcOf g (W j) x (W m x) = 0)
    (i : Fin (Module.finrank ℝ E)) (α : Fin 4 → Fin (Module.finrank ℝ E)) :
    mvfderiv I (fun y : M ↦ covRm g y (W i y) (W (α 0) y) (W (α 1) y) (W (α 2) y)
        (W (α 3) y)) x (W i x)
      = cov2Rm g x (W i x) (W i x) (W (α 0) x) (W (α 1) x) (W (α 2) x) (W (α 3) x) := by
  have h1 : mvfderiv I (fun y : M ↦ covRm g y (W i y) (W (α 0) y) (W (α 1) y) (W (α 2) y)
        (W (α 3) y)) x (W i x)
      = cov2RmExt g x (W i x) (W i) (W (α 0)) (W (α 1)) (W (α 2)) (W (α 3))
        + (covRm g x (lcOf g (W i) x (W i x)) (W (α 0) x) (W (α 1) x) (W (α 2) x) (W (α 3) x)
          + covRm g x (W i x) (lcOf g (W (α 0)) x (W i x)) (W (α 1) x) (W (α 2) x) (W (α 3) x)
          + covRm g x (W i x) (W (α 0) x) (lcOf g (W (α 1)) x (W i x)) (W (α 2) x) (W (α 3) x)
          + covRm g x (W i x) (W (α 0) x) (W (α 1) x) (lcOf g (W (α 2)) x (W i x)) (W (α 3) x)
          + covRm g x (W i x) (W (α 0) x) (W (α 1) x) (W (α 2) x)
              (lcOf g (W (α 3)) x (W i x))) := by
    simp only [cov2RmExt]
    ring
  have htens := kato_cov2RmExt_field (I := I) (M := M) hLC g x
    (W i) (W (α 0)) (W (α 1)) (W (α 2)) (W (α 3))
    (smoothExt x (W i x)) (smoothExt x (W (α 0) x)) (smoothExt x (W (α 1) x))
    (smoothExt x (W (α 2) x)) (smoothExt x (W (α 3) x))
    (hWs i) (hWs (α 0)) (hWs (α 1)) (hWs (α 2)) (hWs (α 3))
    (smoothExt_cmdiff x (W i x)) (smoothExt_cmdiff x (W (α 0) x))
    (smoothExt_cmdiff x (W (α 1) x)) (smoothExt_cmdiff x (W (α 2) x))
    (smoothExt_cmdiff x (W (α 3) x))
    (smoothExt_apply x (W i x)).symm (smoothExt_apply x (W (α 0) x)).symm
    (smoothExt_apply x (W (α 1) x)).symm (smoothExt_apply x (W (α 2) x)).symm
    (smoothExt_apply x (W (α 3) x)).symm
  have hcov := htens.1 (W i x)
  rw [h1, hcov, hgeo i i, hgeo i (α 0), hgeo i (α 1), hgeo i (α 2), hgeo i (α 3)]
  simp only [covRm_zero_fst hLC g x, covRm_zero_snd hLC g x, covRm_zero_thd hLC g x,
    covRm_zero_fth hLC g x, covRm_zero_fif hLC g x, add_zero]
  rfl

/-- **First derivative of a component of `Rm` in a geodesic frame.** -/
theorem mvfderiv_curvComp (hLC : LCSmooth I M) (g : SMet I M) (x : M)
    (W : Fin (Module.finrank ℝ E) → (Π y : M, TangentSpace I y))
    (hWs : ∀ i, CMDiff ∞ (T% (W i))) (hgeo : ∀ m j, lcOf g (W j) x (W m x) = 0)
    (α : Fin 4 → Fin (Module.finrank ℝ E)) (i : Fin (Module.finrank ℝ E)) :
    mvfderiv I (fun y : M ↦ rmP g y (W (α 0) y) (W (α 1) y) (W (α 2) y) (W (α 3) y))
        x (W i x)
      = covRm g x (W i x) (W (α 0) x) (W (α 1) x) (W (α 2) x) (W (α 3) x) := by
  have h1 : mvfderiv I (fun y : M ↦ rmP g y (W (α 0) y) (W (α 1) y) (W (α 2) y) (W (α 3) y))
        x (W i x)
      = dRmPhi g x (W i x) (W (α 0)) (W (α 1)) (W (α 2)) (W (α 3))
        + (rmP g x (lcOf g (W (α 0)) x (W i x)) (W (α 1) x) (W (α 2) x) (W (α 3) x)
          + rmP g x (W (α 0) x) (lcOf g (W (α 1)) x (W i x)) (W (α 2) x) (W (α 3) x)
          + rmP g x (W (α 0) x) (W (α 1) x) (lcOf g (W (α 2)) x (W i x)) (W (α 3) x)
          + rmP g x (W (α 0) x) (W (α 1) x) (W (α 2) x) (lcOf g (W (α 3)) x (W i x))) := by
    simp only [dRmPhi]
    ring
  rw [h1, hgeo i (α 0), hgeo i (α 1), hgeo i (α 2), hgeo i (α 3)]
  simp only [rmP_zero_slot1 hLC g x, rmP_zero_slot2 hLC g x, rmP_zero_slot3 hLC g x,
    rmP_zero_slot4 hLC g x, add_zero]
  rw [← Kato3.covRm_field_form (I := I) (M := M) hLC g x (W i x)
    (hWs (α 0)) (hWs (α 1)) (hWs (α 2)) (hWs (α 3))]


/-- The four slot-corrections of the first derivative of a component of `Rm`, as functions of `y`. -/
noncomputable def corr0 (g : SMet I M)
    (W : Fin (Module.finrank ℝ E) → (Π y : M, TangentSpace I y))
    (α : Fin 4 → Fin (Module.finrank ℝ E)) (i : Fin (Module.finrank ℝ E)) : M → ℝ :=
  fun y => rmP g y (lcOf g (W (α 0)) y (W i y)) (W (α 1) y) (W (α 2) y) (W (α 3) y)

noncomputable def corr1 (g : SMet I M)
    (W : Fin (Module.finrank ℝ E) → (Π y : M, TangentSpace I y))
    (α : Fin 4 → Fin (Module.finrank ℝ E)) (i : Fin (Module.finrank ℝ E)) : M → ℝ :=
  fun y => rmP g y (W (α 0) y) (lcOf g (W (α 1)) y (W i y)) (W (α 2) y) (W (α 3) y)

noncomputable def corr2 (g : SMet I M)
    (W : Fin (Module.finrank ℝ E) → (Π y : M, TangentSpace I y))
    (α : Fin 4 → Fin (Module.finrank ℝ E)) (i : Fin (Module.finrank ℝ E)) : M → ℝ :=
  fun y => rmP g y (W (α 0) y) (W (α 1) y) (lcOf g (W (α 2)) y (W i y)) (W (α 3) y)

noncomputable def corr3 (g : SMet I M)
    (W : Fin (Module.finrank ℝ E) → (Π y : M, TangentSpace I y))
    (α : Fin 4 → Fin (Module.finrank ℝ E)) (i : Fin (Module.finrank ℝ E)) : M → ℝ :=
  fun y => rmP g y (W (α 0) y) (W (α 1) y) (W (α 2) y) (lcOf g (W (α 3)) y (W i y))

section CorrSmooth

variable {W : Fin (Module.finrank ℝ E) → (Π y : M, TangentSpace I y)}
  {α : Fin 4 → Fin (Module.finrank ℝ E)} {i : Fin (Module.finrank ℝ E)}

theorem corr0_smooth (hLC : LCSmooth I M) (g : SMet I M) (hWs : ∀ i, CMDiff ∞ (T% (W i))) :
    CMDiff ∞ (corr0 g W α i) := by
  have hcov := (hLC g).1
  exact rmP_fields_smooth hLC g
    (Commons.Geometry.Manifold.VectorBundle.CovariantDerivative.contMDiff_cov_apply
      (lcOf g) hcov.some (hWs (α 0)) (hWs i)) (hWs (α 1)) (hWs (α 2)) (hWs (α 3))

theorem corr1_smooth (hLC : LCSmooth I M) (g : SMet I M) (hWs : ∀ i, CMDiff ∞ (T% (W i))) :
    CMDiff ∞ (corr1 g W α i) := by
  have hcov := (hLC g).1
  exact rmP_fields_smooth hLC g (hWs (α 0))
    (Commons.Geometry.Manifold.VectorBundle.CovariantDerivative.contMDiff_cov_apply
      (lcOf g) hcov.some (hWs (α 1)) (hWs i)) (hWs (α 2)) (hWs (α 3))

theorem corr2_smooth (hLC : LCSmooth I M) (g : SMet I M) (hWs : ∀ i, CMDiff ∞ (T% (W i))) :
    CMDiff ∞ (corr2 g W α i) := by
  have hcov := (hLC g).1
  exact rmP_fields_smooth hLC g (hWs (α 0)) (hWs (α 1))
    (Commons.Geometry.Manifold.VectorBundle.CovariantDerivative.contMDiff_cov_apply
      (lcOf g) hcov.some (hWs (α 2)) (hWs i)) (hWs (α 3))

theorem corr3_smooth (hLC : LCSmooth I M) (g : SMet I M) (hWs : ∀ i, CMDiff ∞ (T% (W i))) :
    CMDiff ∞ (corr3 g W α i) := by
  have hcov := (hLC g).1
  exact rmP_fields_smooth hLC g (hWs (α 0)) (hWs (α 1)) (hWs (α 2))
    (Commons.Geometry.Manifold.VectorBundle.CovariantDerivative.contMDiff_cov_apply
      (lcOf g) hcov.some (hWs (α 3)) (hWs i))

end CorrSmooth

/-- The covRm-part of the first derivative of a component of `Rm` is smooth. -/
theorem covRmPart_smooth (hLC : LCSmooth I M) (g : SMet I M)
    (W : Fin (Module.finrank ℝ E) → (Π y : M, TangentSpace I y))
    (hWs : ∀ i, CMDiff ∞ (T% (W i))) (α : Fin 4 → Fin (Module.finrank ℝ E))
    (i : Fin (Module.finrank ℝ E)) :
    CMDiff ∞ (fun y : M ↦ covRm g y (W i y) (W (α 0) y) (W (α 1) y) (W (α 2) y)
      (W (α 3) y)) :=
  covRm_fields_smooth (g := g) hLC (hWs i) (hWs (α 0)) (hWs (α 1)) (hWs (α 2)) (hWs (α 3))

/-- **Second derivative of a component of `Rm` in a geodesic frame**, with the second-order
correction coming from the variation of the frame. -/
theorem mvfderiv2_curvComp (hLC : LCSmooth I M) (g : SMet I M) (x : M)
    (W : Fin (Module.finrank ℝ E) → (Π y : M, TangentSpace I y))
    (hWs : ∀ i, CMDiff ∞ (T% (W i))) (hgeo : ∀ m j, lcOf g (W j) x (W m x) = 0)
    (α : Fin 4 → Fin (Module.finrank ℝ E)) (i : Fin (Module.finrank ℝ E)) :
    mvfderiv I (fun y : M ↦ mvfderiv I (fun z : M ↦ rmP g z (W (α 0) z) (W (α 1) z)
        (W (α 2) z) (W (α 3) z)) y (W i y)) x (W i x)
      = cov2Rm g x (W i x) (W i x) (W (α 0) x) (W (α 1) x) (W (α 2) x) (W (α 3) x)
        + (rmP g x (Avec4 g W x i (α 0)) (W (α 1) x) (W (α 2) x) (W (α 3) x)
          + (rmP g x (W (α 0) x) (Avec4 g W x i (α 1)) (W (α 2) x) (W (α 3) x)
            + (rmP g x (W (α 0) x) (W (α 1) x) (Avec4 g W x i (α 2)) (W (α 3) x)
              + rmP g x (W (α 0) x) (W (α 1) x) (W (α 2) x) (Avec4 g W x i (α 3))))) := by
  have hcov := (hLC g).1
  have hX0 : CMDiff ∞ (T% (fun z : M ↦ lcOf g (W (α 0)) z (W i z))) :=
    Commons.Geometry.Manifold.VectorBundle.CovariantDerivative.contMDiff_cov_apply
      (lcOf g) hcov.some (hWs (α 0)) (hWs i)
  have hX1 : CMDiff ∞ (T% (fun z : M ↦ lcOf g (W (α 1)) z (W i z))) :=
    Commons.Geometry.Manifold.VectorBundle.CovariantDerivative.contMDiff_cov_apply
      (lcOf g) hcov.some (hWs (α 1)) (hWs i)
  have hX2 : CMDiff ∞ (T% (fun z : M ↦ lcOf g (W (α 2)) z (W i z))) :=
    Commons.Geometry.Manifold.VectorBundle.CovariantDerivative.contMDiff_cov_apply
      (lcOf g) hcov.some (hWs (α 2)) (hWs i)
  have hX3 : CMDiff ∞ (T% (fun z : M ↦ lcOf g (W (α 3)) z (W i z))) :=
    Commons.Geometry.Manifold.VectorBundle.CovariantDerivative.contMDiff_cov_apply
      (lcOf g) hcov.some (hWs (α 3)) (hWs i)
  -- (a) the pointwise decomposition of the inner derivative into five functions
  have hdec : (fun y : M ↦ mvfderiv I (fun z : M ↦ rmP g z (W (α 0) z) (W (α 1) z)
        (W (α 2) z) (W (α 3) z)) y (W i y))
      = (fun y : M ↦ covRm g y (W i y) (W (α 0) y) (W (α 1) y) (W (α 2) y) (W (α 3) y))
        + (corr0 g W α i + (corr1 g W α i + (corr2 g W α i + corr3 g W α i))) := by
    funext y
    rw [show mvfderiv I (fun z : M ↦ rmP g z (W (α 0) z) (W (α 1) z) (W (α 2) z)
          (W (α 3) z)) y (W i y)
        = dRmPhi g y (W i y) (W (α 0)) (W (α 1)) (W (α 2)) (W (α 3))
          + (rmP g y (lcOf g (W (α 0)) y (W i y)) (W (α 1) y) (W (α 2) y) (W (α 3) y)
            + (rmP g y (W (α 0) y) (lcOf g (W (α 1)) y (W i y)) (W (α 2) y) (W (α 3) y)
              + (rmP g y (W (α 0) y) (W (α 1) y) (lcOf g (W (α 2)) y (W i y)) (W (α 3) y)
                + rmP g y (W (α 0) y) (W (α 1) y) (W (α 2) y)
                    (lcOf g (W (α 3)) y (W i y))))) from by
      simp only [dRmPhi]
      ring]
    rw [← Kato3.covRm_field_form (I := I) (M := M) hLC g y (W i y) (hWs (α 0)) (hWs (α 1))
      (hWs (α 2)) (hWs (α 3))]
    simp only [Pi.add_apply, corr0, corr1, corr2, corr3]
  rw [hdec]
  -- (b) the sum rule
  have h0 : MDifferentiableAt I 𝓘(ℝ,ℝ)
      (fun y : M ↦ covRm g y (W i y) (W (α 0) y) (W (α 1) y) (W (α 2) y) (W (α 3) y)) x :=
    (covRmPart_smooth hLC g W hWs α i).contMDiffAt.mdifferentiableAt (by simp)
  have hs0 : MDifferentiableAt I 𝓘(ℝ,ℝ) (corr0 g W α i) x :=
    (corr0_smooth (W := W) (α := α) (i := i) hLC g hWs).contMDiffAt.mdifferentiableAt
      (by simp)
  have hs1 : MDifferentiableAt I 𝓘(ℝ,ℝ) (corr1 g W α i) x :=
    (corr1_smooth (W := W) (α := α) (i := i) hLC g hWs).contMDiffAt.mdifferentiableAt
      (by simp)
  have hs2 : MDifferentiableAt I 𝓘(ℝ,ℝ) (corr2 g W α i) x :=
    (corr2_smooth (W := W) (α := α) (i := i) hLC g hWs).contMDiffAt.mdifferentiableAt
      (by simp)
  have hs3 : MDifferentiableAt I 𝓘(ℝ,ℝ) (corr3 g W α i) x :=
    (corr3_smooth (W := W) (α := α) (i := i) hLC g hWs).contMDiffAt.mdifferentiableAt
      (by simp)
  rw [mvfderiv_add h0 (hs0.add (hs1.add (hs2.add hs3))),
    mvfderiv_add hs0 (hs1.add (hs2.add hs3)),
    mvfderiv_add hs1 (hs2.add hs3), mvfderiv_add hs2 hs3]
  simp only [ContinuousLinearMap.add_apply]
  -- (c) the five derivatives
  rw [mvfderiv_covRm_geodesic (I := I) (M := M) hLC g x W hWs hgeo i α]
  unfold corr0 corr1 corr2 corr3
  rw [deriv_rmP_zero_slot1 (I := I) (M := M) hLC g x (fun z : M ↦ lcOf g (W (α 0)) z (W i z))
      (W (α 1)) (W (α 2)) (W (α 3)) hX0 (hWs (α 1)) (hWs (α 2)) (hWs (α 3)) (W i) (hWs i)
      (hgeo i (α 0)),
    deriv_rmP_zero_slot2 (I := I) (M := M) hLC g x (W (α 0))
      (fun z : M ↦ lcOf g (W (α 1)) z (W i z)) (W (α 2)) (W (α 3)) (hWs (α 0)) hX1
      (hWs (α 2)) (hWs (α 3)) (W i) (hWs i) (hgeo i (α 1)),
    deriv_rmP_zero_slot3 (I := I) (M := M) hLC g x (W (α 0)) (W (α 1))
      (fun z : M ↦ lcOf g (W (α 2)) z (W i z)) (W (α 3)) (hWs (α 0)) (hWs (α 1)) hX2
      (hWs (α 3)) (W i) (hWs i) (hgeo i (α 2)),
    deriv_rmP_zero_slot4 (I := I) (M := M) hLC g x (W (α 0)) (W (α 1)) (W (α 2))
      (fun z : M ↦ lcOf g (W (α 3)) z (W i z)) (hWs (α 0)) (hWs (α 1)) (hWs (α 2)) hX3
      (W i) (hWs i) (hgeo i (α 3))]
  simp only [Avec4]


/-! ## The frame-leftover sum vanishes (four indices) -/

/-- A sum over `Fin 4` as four explicit terms. -/
theorem sum_fin_four {R : Type*} [AddCommMonoid R] (f : Fin 4 → R) :
    (∑ s : Fin 4, f s) = f 0 + f 1 + f 2 + f 3 :=
  Fin.sum_univ_four f

/-- **The frame-leftover sum vanishes.**  For any array `P : (Fin m → Fin n) → ℝ` and any
antisymmetric matrix `A`, the sum `∑ α, P α * ∑ j, ∑ β, A (α j) β * P (Function.update α j β)`
vanishes (the finite-sum cancellation making the second-order frame correction disappear). -/
theorem leftover_sum_fin {n m : ℕ} (P : (Fin m → Fin n) → ℝ) (A : Fin n → Fin n → ℝ)
    (hA : ∀ i j, A i j = - A j i) :
    ∑ α : Fin m → Fin n, P α * (∑ j : Fin m, ∑ β : Fin n,
      A (α j) β * P (Function.update α j β)) = 0 := by
  classical
  have hdiag : ∀ i : Fin n, A i i = 0 := by
    intro i
    have h := hA i i
    linarith
  have hsingle : ∀ j : Fin m,
      (∑ α : Fin m → Fin n, ∑ β : Fin n,
        P α * A (α j) β * P (Function.update α j β)) = 0 := by
    intro j
    rw [← Fintype.sum_prod_type (fun x : (Fin m → Fin n) × Fin n =>
      P x.1 * A (x.1 j) x.2 * P (Function.update x.1 j x.2))]
    refine Finset.sum_ninvolution (s := Finset.univ)
      (f := fun x : (Fin m → Fin n) × Fin n =>
        P x.1 * A (x.1 j) x.2 * P (Function.update x.1 j x.2))
      (fun x => (Function.update x.1 j x.2, x.1 j)) ?_ ?_ ?_ ?_
    · intro a
      have h1 : Function.update a.1 j a.2 j = a.2 := by simp
      have h2 : Function.update (Function.update a.1 j a.2) j (a.1 j) = a.1 := by
        simp [Function.update_idem, Function.update_eq_self]
      simp only [h1, h2, hA a.2 (a.1 j)]
      ring
    · intro a hg hga
      apply hg
      have h1 : a.1 j = a.2 := by
        simpa using congrArg (fun p : (Fin m → Fin n) × Fin n => p.2) hga
      rw [← h1]
      simp [hdiag]
    · intro a
      exact Finset.mem_univ _
    · intro a
      simp [Function.update_idem, Function.update_eq_self]
  have hconv :
      (∑ α : Fin m → Fin n, P α * (∑ j : Fin m, ∑ β : Fin n,
          A (α j) β * P (Function.update α j β)))
        = ∑ j : Fin m, ∑ α : Fin m → Fin n, ∑ β : Fin n,
            P α * A (α j) β * P (Function.update α j β) := by
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    refine Finset.sum_congr rfl (fun α _ => ?_)
    refine Finset.sum_congr rfl (fun β _ => ?_)
    ring
  rw [hconv]
  simp [hsingle]

/-! ## Expansion of the second-order frame correction in the orthonormal frame -/

/-- The vector `Avec4 g W x i γ` expands in the orthonormal frame `W · x`. -/
theorem avec4_eq_sum (g : SMet I M)
    (W : Fin (Module.finrank ℝ E) → (Π y : M, TangentSpace I y)) (x : M)
    (hn : 0 < Module.finrank ℝ E) (hONx : IsONFrame g x (fun j => W j x))
    (i γ : Fin (Module.finrank ℝ E)) :
    Avec4 g W x i γ
      = ∑ β : Fin (Module.finrank ℝ E), g.inner x (Avec4 g W x i γ) (W β x) • W β x :=
  (sum_smul_inner_eq_self g x hn (fun β => W β x) hONx (Avec4 g W x i γ)).symm

/-- The first slot of the second-order frame correction, expanded in the orthonormal frame. -/
theorem leftover_slot0_expand (hLC : LCSmooth I M) (g : SMet I M) (x : M)
    (W : Fin (Module.finrank ℝ E) → (Π y : M, TangentSpace I y))
    (hn : 0 < Module.finrank ℝ E) (hONx : IsONFrame g x (fun j => W j x))
    (α : Fin 4 → Fin (Module.finrank ℝ E)) (i : Fin (Module.finrank ℝ E)) :
    rmP g x (Avec4 g W x i (α 0)) (W (α 1) x) (W (α 2) x) (W (α 3) x)
      = ∑ β : Fin (Module.finrank ℝ E), g.inner x (Avec4 g W x i (α 0)) (W β x)
          * rmP g x (W β x) (W (α 1) x) (W (α 2) x) (W (α 3) x) := by
  have h := rmP_sum_fst (I := I) (M := M) hLC g x Finset.univ
    (fun β => g.inner x (Avec4 g W x i (α 0)) (W β x)) (fun β => W β x)
    (W (α 1) x) (W (α 2) x) (W (α 3) x)
  rw [← h]
  exact congrArg (fun v => rmP g x v (W (α 1) x) (W (α 2) x) (W (α 3) x))
    (avec4_eq_sum g W x hn hONx i (α 0))

theorem leftover_slot1_expand (hLC : LCSmooth I M) (g : SMet I M) (x : M)
    (W : Fin (Module.finrank ℝ E) → (Π y : M, TangentSpace I y))
    (hn : 0 < Module.finrank ℝ E) (hONx : IsONFrame g x (fun j => W j x))
    (α : Fin 4 → Fin (Module.finrank ℝ E)) (i : Fin (Module.finrank ℝ E)) :
    rmP g x (W (α 0) x) (Avec4 g W x i (α 1)) (W (α 2) x) (W (α 3) x)
      = ∑ β : Fin (Module.finrank ℝ E), g.inner x (Avec4 g W x i (α 1)) (W β x)
          * rmP g x (W (α 0) x) (W β x) (W (α 2) x) (W (α 3) x) := by
  have h := rmP_sum_snd (I := I) (M := M) hLC g x Finset.univ
    (fun β => g.inner x (Avec4 g W x i (α 1)) (W β x)) (fun β => W β x)
    (W (α 0) x) (W (α 2) x) (W (α 3) x)
  rw [← h]
  exact congrArg (fun v => rmP g x (W (α 0) x) v (W (α 2) x) (W (α 3) x))
    (avec4_eq_sum g W x hn hONx i (α 1))

theorem leftover_slot2_expand (hLC : LCSmooth I M) (g : SMet I M) (x : M)
    (W : Fin (Module.finrank ℝ E) → (Π y : M, TangentSpace I y))
    (hn : 0 < Module.finrank ℝ E) (hONx : IsONFrame g x (fun j => W j x))
    (α : Fin 4 → Fin (Module.finrank ℝ E)) (i : Fin (Module.finrank ℝ E)) :
    rmP g x (W (α 0) x) (W (α 1) x) (Avec4 g W x i (α 2)) (W (α 3) x)
      = ∑ β : Fin (Module.finrank ℝ E), g.inner x (Avec4 g W x i (α 2)) (W β x)
          * rmP g x (W (α 0) x) (W (α 1) x) (W β x) (W (α 3) x) := by
  have h := rmP_sum_thd (I := I) (M := M) hLC g x Finset.univ
    (fun β => g.inner x (Avec4 g W x i (α 2)) (W β x)) (fun β => W β x)
    (W (α 0) x) (W (α 1) x) (W (α 3) x)
  rw [← h]
  exact congrArg (fun v => rmP g x (W (α 0) x) (W (α 1) x) v (W (α 3) x))
    (avec4_eq_sum g W x hn hONx i (α 2))

theorem leftover_slot3_expand (hLC : LCSmooth I M) (g : SMet I M) (x : M)
    (W : Fin (Module.finrank ℝ E) → (Π y : M, TangentSpace I y))
    (hn : 0 < Module.finrank ℝ E) (hONx : IsONFrame g x (fun j => W j x))
    (α : Fin 4 → Fin (Module.finrank ℝ E)) (i : Fin (Module.finrank ℝ E)) :
    rmP g x (W (α 0) x) (W (α 1) x) (W (α 2) x) (Avec4 g W x i (α 3))
      = ∑ β : Fin (Module.finrank ℝ E), g.inner x (Avec4 g W x i (α 3)) (W β x)
          * rmP g x (W (α 0) x) (W (α 1) x) (W (α 2) x) (W β x) := by
  have h := rmP_sum_fth (I := I) (M := M) hLC g x Finset.univ
    (fun β => g.inner x (Avec4 g W x i (α 3)) (W β x)) (fun β => W β x)
    (W (α 0) x) (W (α 1) x) (W (α 2) x)
  rw [← h]
  exact congrArg (fun v => rmP g x (W (α 0) x) (W (α 1) x) (W (α 2) x) v)
    (avec4_eq_sum g W x hn hONx i (α 3))


/-! ## The components of `Rm` in the geodesic frame: notation and basic identities -/

/-- The component `Rm(e_{α 0}, e_{α 1}, e_{α 2}, e_{α 3})` of the curvature in the frame `W`. -/
noncomputable def curvComp (g : SMet I M)
    (W : Fin (Module.finrank ℝ E) → (Π y : M, TangentSpace I y))
    (α : Fin 4 → Fin (Module.finrank ℝ E)) : M → ℝ :=
  fun y => rmP g y (W (α 0) y) (W (α 1) y) (W (α 2) y) (W (α 3) y)

/-- `|Rm|²` computed in the frame `W`. -/
noncomputable def curvNormSq (g : SMet I M)
    (W : Fin (Module.finrank ℝ E) → (Π y : M, TangentSpace I y)) : M → ℝ :=
  fun y => ∑ α : Fin 4 → Fin (Module.finrank ℝ E), (curvComp g W α y) ^ 2

/-- The frame vectors `(W (α 0) x, …, W (α 3) x)` at `x` as a function `Fin 4 → TₓM`. -/
noncomputable def Vfun (g : SMet I M)
    (W : Fin (Module.finrank ℝ E) → (Π y : M, TangentSpace I y)) (x : M)
    (α : Fin 4 → Fin (Module.finrank ℝ E)) : Fin 4 → TangentSpace I x :=
  fun t => W (α t) x

/-- The component of `Rm` at `x` on the frame vectors indexed by `α`. -/
noncomputable def Pfun (g : SMet I M)
    (W : Fin (Module.finrank ℝ E) → (Π y : M, TangentSpace I y)) (x : M)
    (α : Fin 4 → Fin (Module.finrank ℝ E)) : ℝ :=
  P4 g x (Vfun g W x α)

theorem Pfun_eq (g : SMet I M)
    (W : Fin (Module.finrank ℝ E) → (Π y : M, TangentSpace I y)) (x : M)
    (α : Fin 4 → Fin (Module.finrank ℝ E)) :
    Pfun g W x α = rmP g x (W (α 0) x) (W (α 1) x) (W (α 2) x) (W (α 3) x) := rfl

theorem Vfun_update (g : SMet I M)
    (W : Fin (Module.finrank ℝ E) → (Π y : M, TangentSpace I y)) (x : M)
    (α : Fin 4 → Fin (Module.finrank ℝ E)) (s : Fin 4) (β : Fin (Module.finrank ℝ E)) :
    Vfun g W x (Function.update α s β)
      = Function.update (Vfun g W x α) s (W β x) := by
  funext t
  by_cases ht : t = s
  · subst ht
    simp only [Vfun, Function.update_self]
  · simp only [Vfun, Function.update_of_ne ht]

theorem Pfun_update (g : SMet I M)
    (W : Fin (Module.finrank ℝ E) → (Π y : M, TangentSpace I y)) (x : M)
    (α : Fin 4 → Fin (Module.finrank ℝ E)) (s : Fin 4) (β : Fin (Module.finrank ℝ E)) :
    Pfun g W x (Function.update α s β)
      = P4 g x (Function.update (Vfun g W x α) s (W β x)) := by
  rw [Pfun, Vfun_update]

theorem P4_update_0 (g : SMet I M) (x : M) (v : Fin 4 → TangentSpace I x)
    (c : TangentSpace I x) :
    P4 g x (Function.update v 0 c) = rmP g x c (v 1) (v 2) (v 3) := by
  simp only [P4, Function.update_apply]
  rw [if_pos trivial, if_neg (by decide : ¬ ((1 : Fin 4) = 0)),
    if_neg (by decide : ¬ ((2 : Fin 4) = 0)), if_neg (by decide : ¬ ((3 : Fin 4) = 0))]

theorem P4_update_1 (g : SMet I M) (x : M) (v : Fin 4 → TangentSpace I x)
    (c : TangentSpace I x) :
    P4 g x (Function.update v 1 c) = rmP g x (v 0) c (v 2) (v 3) := by
  simp only [P4, Function.update_apply]
  rw [if_neg (by decide : ¬ ((0 : Fin 4) = 1)), if_pos trivial,
    if_neg (by decide : ¬ ((2 : Fin 4) = 1)), if_neg (by decide : ¬ ((3 : Fin 4) = 1))]

theorem P4_update_2 (g : SMet I M) (x : M) (v : Fin 4 → TangentSpace I x)
    (c : TangentSpace I x) :
    P4 g x (Function.update v 2 c) = rmP g x (v 0) (v 1) c (v 3) := by
  simp only [P4, Function.update_apply]
  rw [if_neg (by decide : ¬ ((0 : Fin 4) = 2)), if_neg (by decide : ¬ ((1 : Fin 4) = 2)),
    if_pos trivial, if_neg (by decide : ¬ ((3 : Fin 4) = 2))]

theorem P4_update_3 (g : SMet I M) (x : M) (v : Fin 4 → TangentSpace I x)
    (c : TangentSpace I x) :
    P4 g x (Function.update v 3 c) = rmP g x (v 0) (v 1) (v 2) c := by
  simp only [P4, Function.update_apply]
  rw [if_neg (by decide : ¬ ((0 : Fin 4) = 3)), if_neg (by decide : ¬ ((1 : Fin 4) = 3)),
    if_neg (by decide : ¬ ((2 : Fin 4) = 3)), if_pos trivial]

theorem Pfun_update_0 (g : SMet I M)
    (W : Fin (Module.finrank ℝ E) → (Π y : M, TangentSpace I y)) (x : M)
    (α : Fin 4 → Fin (Module.finrank ℝ E)) (β : Fin (Module.finrank ℝ E)) :
    Pfun g W x (Function.update α 0 β)
      = rmP g x (W β x) (W (α 1) x) (W (α 2) x) (W (α 3) x) := by
  rw [Pfun_update, P4_update_0]
  rfl

theorem Pfun_update_1 (g : SMet I M)
    (W : Fin (Module.finrank ℝ E) → (Π y : M, TangentSpace I y)) (x : M)
    (α : Fin 4 → Fin (Module.finrank ℝ E)) (β : Fin (Module.finrank ℝ E)) :
    Pfun g W x (Function.update α 1 β)
      = rmP g x (W (α 0) x) (W β x) (W (α 2) x) (W (α 3) x) := by
  rw [Pfun_update, P4_update_1]
  rfl

theorem Pfun_update_2 (g : SMet I M)
    (W : Fin (Module.finrank ℝ E) → (Π y : M, TangentSpace I y)) (x : M)
    (α : Fin 4 → Fin (Module.finrank ℝ E)) (β : Fin (Module.finrank ℝ E)) :
    Pfun g W x (Function.update α 2 β)
      = rmP g x (W (α 0) x) (W (α 1) x) (W β x) (W (α 3) x) := by
  rw [Pfun_update, P4_update_2]
  rfl

theorem Pfun_update_3 (g : SMet I M)
    (W : Fin (Module.finrank ℝ E) → (Π y : M, TangentSpace I y)) (x : M)
    (α : Fin 4 → Fin (Module.finrank ℝ E)) (β : Fin (Module.finrank ℝ E)) :
    Pfun g W x (Function.update α 3 β)
      = rmP g x (W (α 0) x) (W (α 1) x) (W (α 2) x) (W β x) := by
  rw [Pfun_update, P4_update_3]
  rfl

/-- The component `Rm(e_{α 0}, …, e_{α 3})` is smooth in `y`. -/
theorem curvComp_smooth (hLC : LCSmooth I M) (g : SMet I M)
    (W : Fin (Module.finrank ℝ E) → (Π y : M, TangentSpace I y))
    (hWs : ∀ i, CMDiff ∞ (T% (W i))) (α : Fin 4 → Fin (Module.finrank ℝ E)) :
    CMDiff ∞ (curvComp g W α) :=
  rmP_fields_smooth hLC g (hWs (α 0)) (hWs (α 1)) (hWs (α 2)) (hWs (α 3))

/-- `|Rm|²` in the frame `W` is smooth. -/
theorem curvNormSq_smooth (hLC : LCSmooth I M) (g : SMet I M)
    (W : Fin (Module.finrank ℝ E) → (Π y : M, TangentSpace I y))
    (hWs : ∀ i, CMDiff ∞ (T% (W i))) :
    CMDiff ∞ (curvNormSq g W) := by
  refine ContMDiff.sum (fun α _ => ?_)
  exact (curvComp_smooth hLC g W hWs α).pow 2

/-- The second-order frame correction of the component `α` in the direction `i`. -/
noncomputable def Left4 (g : SMet I M)
    (W : Fin (Module.finrank ℝ E) → (Π y : M, TangentSpace I y)) (x : M)
    (α : Fin 4 → Fin (Module.finrank ℝ E)) (i : Fin (Module.finrank ℝ E)) : ℝ :=
  rmP g x (Avec4 g W x i (α 0)) (W (α 1) x) (W (α 2) x) (W (α 3) x)
    + (rmP g x (W (α 0) x) (Avec4 g W x i (α 1)) (W (α 2) x) (W (α 3) x)
      + (rmP g x (W (α 0) x) (W (α 1) x) (Avec4 g W x i (α 2)) (W (α 3) x)
        + rmP g x (W (α 0) x) (W (α 1) x) (W (α 2) x) (Avec4 g W x i (α 3))))

/-- The cancellation of one slot of the frame correction against the antisymmetric second derivative
of the frame. -/
theorem leftover_slice_fin {n m : ℕ} (j : Fin m) (P : (Fin m → Fin n) → ℝ) (A : Fin n → Fin n → ℝ)
    (hA : ∀ i j, A i j = - A j i) :
    (∑ α : Fin m → Fin n, P α * (∑ β : Fin n, A (α j) β * P (Function.update α j β))) = 0 := by
  classical
  have hdiag : ∀ i : Fin n, A i i = 0 := by
    intro i
    have h := hA i i
    linarith
  simp only [Finset.mul_sum]
  rw [← Fintype.sum_prod_type (fun x : (Fin m → Fin n) × Fin n =>
    P x.1 * (A (x.1 j) x.2 * P (Function.update x.1 j x.2)))]
  refine Finset.sum_ninvolution (s := Finset.univ)
    (f := fun x : (Fin m → Fin n) × Fin n =>
      P x.1 * (A (x.1 j) x.2 * P (Function.update x.1 j x.2)))
    (fun x => (Function.update x.1 j x.2, x.1 j)) ?_ ?_ ?_ ?_
  · intro a
    have h1 : Function.update a.1 j a.2 j = a.2 := by simp
    have h2 : Function.update (Function.update a.1 j a.2) j (a.1 j) = a.1 := by
      simp [Function.update_idem, Function.update_eq_self]
    simp only [h1, h2, hA a.2 (a.1 j)]
    ring
  · intro a hg hga
    apply hg
    have h1 : a.1 j = a.2 := by
      simpa using congrArg (fun p : (Fin m → Fin n) × Fin n => p.2) hga
    rw [← h1]
    simp [hdiag]
  · intro a
    exact Finset.mem_univ _
  · intro a
    simp [Function.update_idem, Function.update_eq_self]

/-- **The total second-order frame correction vanishes** when contracted with the curvature
components: the only nonvanishing part is the antisymmetric pairing of the second derivative of the
geodesic frame with the frame, and it cancels against the symmetric sum. -/
theorem leftover_vanishes (hLC : LCSmooth I M) (g : SMet I M) (x : M)
    (W : Fin (Module.finrank ℝ E) → (Π y : M, TangentSpace I y))
    (hWs : ∀ i, CMDiff ∞ (T% (W i))) (hn : 0 < Module.finrank ℝ E)
    (hWON : ∀ᶠ y in 𝓝 x, IsONFrame g y (fun j => W j y))
    (hWx : ∀ j, W j x = onFrame g x j)
    (hgeo : ∀ m j, lcOf g (W j) x (W m x) = 0) (i : Fin (Module.finrank ℝ E)) :
    (∑ α : Fin 4 → Fin (Module.finrank ℝ E), Pfun g W x α * Left4 g W x α i) = 0 := by
  classical
  have hONx : IsONFrame g x (fun j => W j x) := by
    intro a b
    show g.inner x (W a x) (W b x) = if a = b then 1 else 0
    rw [hWx a, hWx b]
    exact isONFrame_onFrame g x a b
  have hanti : ∀ γ β : Fin (Module.finrank ℝ E),
      g.inner x (Avec4 g W x i γ) (W β x) = - g.inner x (Avec4 g W x i β) (W γ x) :=
    fun γ β => kato_frame_second_antisymm (I := I) (M := M) hLC g W x hWs hWON hgeo i γ β
  have hexp : ∀ α : Fin 4 → Fin (Module.finrank ℝ E), Left4 g W x α i
      = (∑ β : Fin (Module.finrank ℝ E),
            g.inner x (Avec4 g W x i (α 0)) (W β x) * Pfun g W x (Function.update α 0 β))
        + ((∑ β : Fin (Module.finrank ℝ E),
              g.inner x (Avec4 g W x i (α 1)) (W β x) * Pfun g W x (Function.update α 1 β))
          + ((∑ β : Fin (Module.finrank ℝ E),
                g.inner x (Avec4 g W x i (α 2)) (W β x) * Pfun g W x (Function.update α 2 β))
            + (∑ β : Fin (Module.finrank ℝ E),
                g.inner x (Avec4 g W x i (α 3)) (W β x) * Pfun g W x (Function.update α 3 β)))) := by
    intro α
    rw [Left4]
    rw [leftover_slot0_expand hLC g x W hn hONx α i,
      leftover_slot1_expand hLC g x W hn hONx α i,
      leftover_slot2_expand hLC g x W hn hONx α i,
      leftover_slot3_expand hLC g x W hn hONx α i]
    simp only [← Pfun_update_0, ← Pfun_update_1, ← Pfun_update_2, ← Pfun_update_3]
  have hsum : ∀ α : Fin 4 → Fin (Module.finrank ℝ E), Pfun g W x α * Left4 g W x α i
      = Pfun g W x α * (∑ β : Fin (Module.finrank ℝ E),
            g.inner x (Avec4 g W x i (α 0)) (W β x) * Pfun g W x (Function.update α 0 β))
        + (Pfun g W x α * (∑ β : Fin (Module.finrank ℝ E),
              g.inner x (Avec4 g W x i (α 1)) (W β x) * Pfun g W x (Function.update α 1 β))
          + (Pfun g W x α * (∑ β : Fin (Module.finrank ℝ E),
                g.inner x (Avec4 g W x i (α 2)) (W β x) * Pfun g W x (Function.update α 2 β))
            + Pfun g W x α * (∑ β : Fin (Module.finrank ℝ E),
                g.inner x (Avec4 g W x i (α 3)) (W β x) * Pfun g W x (Function.update α 3 β)))) := by
    intro α
    rw [hexp α]
    ring
  simp only [hsum]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib]
  rw [leftover_slice_fin (j := 0) (P := Pfun g W x)
      (A := fun γ β => g.inner x (Avec4 g W x i γ) (W β x)) (fun γ β => hanti γ β),
    leftover_slice_fin (j := 1) (P := Pfun g W x)
      (A := fun γ β => g.inner x (Avec4 g W x i γ) (W β x)) (fun γ β => hanti γ β),
    leftover_slice_fin (j := 2) (P := Pfun g W x)
      (A := fun γ β => g.inner x (Avec4 g W x i γ) (W β x)) (fun γ β => hanti γ β),
    leftover_slice_fin (j := 3) (P := Pfun g W x)
      (A := fun γ β => g.inner x (Avec4 g W x i γ) (W β x)) (fun γ β => hanti γ β)]
  ring

/-! ## The first and second derivative of `|Rm|²` in the geodesic frame -/

theorem mvfderiv_curvNormSq (hLC : LCSmooth I M) (g : SMet I M)
    (W : Fin (Module.finrank ℝ E) → (Π y : M, TangentSpace I y))
    (hWs : ∀ i, CMDiff ∞ (T% (W i)))
    (U : Π y : M, TangentSpace I y) (hU : CMDiff ∞ (T% U)) (y : M) :
    mvfderiv I (curvNormSq g W) y (U y)
      = ∑ α : Fin 4 → Fin (Module.finrank ℝ E),
          2 * curvComp g W α y * mvfderiv I (curvComp g W α) y (U y) := by
  have hsm : ∀ α, CMDiff ∞ (curvComp g W α) := fun α => curvComp_smooth hLC g W hWs α
  unfold curvNormSq
  rw [Work.Diff.GE.Kato3.mvfderiv_sum Finset.univ (fun α y => (curvComp g W α y) ^ 2)
    (fun α => (hsm α).pow 2) y (U y)]
  refine Finset.sum_congr rfl (fun α _ => ?_)
  rw [show (fun z : M => curvComp g W α z ^ 2)
      = fun z : M => curvComp g W α z * curvComp g W α z from by funext z; ring]
  rw [Work.Diff.GE.Gest.mvfderiv_mul_apply (curvComp g W α) (curvComp g W α) (hsm α) (hsm α)
    y (U y)]
  ring

theorem mvfderiv_const_mul (c : ℝ) {h : M → ℝ} (hh : CMDiff ∞ h) (y : M)
    (u : TangentSpace I y) :
    mvfderiv I (fun z : M => c * h z) y u = c * mvfderiv I h y u := by
  have h1 := mvfderiv_mul (I := I) (M := M) (x := y) (f := fun _ : M => c) (g := h)
    (mdifferentiableAt_const (c := c)) (hh.contMDiffAt.mdifferentiableAt (by simp))
  have h2 := congrArg (fun L : TangentSpace I y →L[ℝ] ℝ => L u) h1
  rw [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, ContinuousLinearMap.smul_apply,
    mvfderiv_const, ContinuousLinearMap.zero_apply, smul_zero, add_zero, smul_eq_mul] at h2
  exact h2

theorem mvfderiv2_curvNormSq (hLC : LCSmooth I M) (g : SMet I M) (x : M)
    (W : Fin (Module.finrank ℝ E) → (Π y : M, TangentSpace I y))
    (hWs : ∀ i, CMDiff ∞ (T% (W i))) (i : Fin (Module.finrank ℝ E)) :
    mvfderiv I (fun y : M =>
        mvfderiv I (curvNormSq g W) y (W i y)) x (W i x)
      = ∑ α : Fin 4 → Fin (Module.finrank ℝ E),
          (2 * (mvfderiv I (curvComp g W α) x (W i x)) ^ 2
            + 2 * curvComp g W α x
                * mvfderiv I (fun y : M => mvfderiv I (curvComp g W α) y (W i y))
                    x (W i x)) := by
  have hsm : ∀ α, CMDiff ∞ (curvComp g W α) := fun α => curvComp_smooth hLC g W hWs α
  have hsmD : ∀ α, CMDiff ∞ (fun y : M => mvfderiv I (curvComp g W α) y (W i y)) :=
    fun α => Commons.Geometry.Manifold.VectorField.mvfderiv_apply_contMDiff (hsm α) (hWs i)
  have hpt : (fun y : M => mvfderiv I (curvNormSq g W) y (W i y))
      = fun y : M => ∑ α : Fin 4 → Fin (Module.finrank ℝ E),
          2 * curvComp g W α y * mvfderiv I (curvComp g W α) y (W i y) := by
    funext y
    exact mvfderiv_curvNormSq hLC g W hWs (W i) (hWs i) y
  rw [hpt]
  rw [Work.Diff.GE.Kato3.mvfderiv_sum Finset.univ
    (fun α y => 2 * curvComp g W α y * mvfderiv I (curvComp g W α) y (W i y))
    (fun α => ((contMDiff_const (c := (2 : ℝ))).mul (hsm α)).mul (hsmD α)) x (W i x)]
  refine Finset.sum_congr rfl (fun α _ => ?_)
  have hu : CMDiff ∞ (fun y : M => 2 * curvComp g W α y) :=
    (contMDiff_const (c := (2 : ℝ))).mul (hsm α)
  have hv : CMDiff ∞ (fun y : M => mvfderiv I (curvComp g W α) y (W i y)) := hsmD α
  have hpr := Work.Diff.GE.Gest.mvfderiv_mul_apply (fun y : M => 2 * curvComp g W α y)
    (fun y : M => mvfderiv I (curvComp g W α) y (W i y)) hu hv x (W i x)
  rw [hpr, mvfderiv_const_mul (2 : ℝ) (hsm α) x (W i x)]
  ring


/-! ## Reindexing lemmas -/

/-- Swapping the outermost sum past four sums over the same finite type. -/
theorem sum_comm_swap5 {n : ℕ} {R : Type*} [AddCommMonoid R]
    (F : Fin n → Fin n → Fin n → Fin n → Fin n → R) :
    (∑ i, ∑ a, ∑ b, ∑ c, ∑ d, F i a b c d)
      = ∑ a, ∑ b, ∑ c, ∑ d, ∑ i, F i a b c d := by
  rw [Finset.sum_comm]
  congr 1 with a
  rw [Finset.sum_comm]
  congr 1 with b
  rw [Finset.sum_comm]
  congr 1 with c
  rw [Finset.sum_comm]

/-- A sum over the tuple type `Fin 4 → Fin n` is the four-fold nested sum. -/
theorem sum_four_arrow {n : ℕ} {R : Type*} [AddCommMonoid R]
    (F : Fin n → Fin n → Fin n → Fin n → R) :
    (∑ α : Fin 4 → Fin n, F (α 0) (α 1) (α 2) (α 3)) = ∑ i, ∑ j, ∑ k, ∑ l, F i j k l := by
  classical
  let e : (Fin 4 → Fin n) ≃ ((Fin n × Fin n) × Fin n) × Fin n :=
    { toFun := fun α => (((α 0, α 1), α 2), α 3)
      invFun := fun p => ![p.1.1.1, p.1.1.2, p.1.2, p.2]
      left_inv := by
        intro α
        funext i
        fin_cases i <;> rfl
      right_inv := by
        rintro ⟨⟨⟨i, j⟩, k⟩, l⟩
        rfl }
  rw [Fintype.sum_equiv e (fun α : Fin 4 → Fin n => F (α 0) (α 1) (α 2) (α 3))
    (fun p : ((Fin n × Fin n) × Fin n) × Fin n => F p.1.1.1 p.1.1.2 p.1.2 p.2)
    (by intro α; rfl)]
  rw [Fintype.sum_prod_type, Fintype.sum_prod_type, Fintype.sum_prod_type]

/-- The two versions of the second covariant derivative of the curvature agree. -/
theorem cov2Rm_eq_PP (g : SMet I M) (x : M) (u v a b c d : TangentSpace I x) :
    cov2Rm g x u v a b c d = Work.Diff.PP.cov2Rm g x u v a b c d := by
  simp only [Work.Diff.GE.cov2Rm, Work.Diff.GE.cov2RmExt, Work.Diff.PP.cov2Rm,
    smoothExt_apply]

theorem laplAt_rmNormSq_eq
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ((⊤ : ENat) : WithTop ENat) M] [T2Space M]
    (hLC : Submission.Diff.LCSmooth I M) (g : Submission.Diff.SMet I M) (x : M) :
    Submission.Diff.laplAt g (Submission.Diff.rmNormSq g) x
      = 2 * (∑ i, ∑ j, ∑ k, ∑ l, Submission.Diff.rmC g x i j k l *
            Work.Diff.PP.roughLap g x (Submission.Diff.onFrame g x) i j k l)
        + 2 * Submission.Diff.dRmNormSq g x := by
  classical
  by_cases hn : 0 < Module.finrank ℝ E
  · obtain ⟨W, hWs, hWON, hWx, hgeo⟩ := geodesicFrame (I := I) (M := M) g x
    -- (i) `|Rm|²` computed in the geodesic frame equals the frozen `rmNormSq`
    have hev : curvNormSq g W =ᶠ[𝓝 x] rmNormSq g := by
      filter_upwards [hWON] with y hy
      rw [rmNormSq_eq_frobSq_rmFrame (I := I) (M := M) hLC g y (fun i => W i y) hy]
      show (∑ α : Fin 4 → Fin (Module.finrank ℝ E),
          (rmP g y (W (α 0) y) (W (α 1) y) (W (α 2) y) (W (α 3) y)) ^ 2)
        = ∑ i, ∑ j, ∑ k, ∑ l, (rmP g y (W i y) (W j y) (W k y) (W l y)) ^ 2
      exact sum_four_arrow (fun a b c d => (rmP g y (W a y) (W b y) (W c y) (W d y)) ^ 2)
    -- (ii) `laplAt` in the geodesic frame
    have hstep2 : laplAt g (curvNormSq g W) x
        = ∑ i : Fin (Module.finrank ℝ E),
            mvfderiv I (fun y : M ↦ mvfderiv I (curvNormSq g W) y (W i y)) x (W i x) :=
      laplAt_eq_sum_frame (I := I) (M := M) hLC g x W hWs hWx hgeo
        ((curvNormSq_smooth hLC g W hWs).contMDiffAt)
    -- (iii) the second derivatives, with the component derivatives evaluated
    have hstep3 : ∀ i : Fin (Module.finrank ℝ E),
        mvfderiv I (fun y : M ↦ mvfderiv I (curvNormSq g W) y (W i y)) x (W i x)
          = ∑ α : Fin 4 → Fin (Module.finrank ℝ E),
              (2 * (covRm g x (W i x) (W (α 0) x) (W (α 1) x) (W (α 2) x) (W (α 3) x)) ^ 2
                + 2 * curvComp g W α x
                    * (cov2Rm g x (W i x) (W i x) (W (α 0) x) (W (α 1) x) (W (α 2) x)
                        (W (α 3) x)
                      + Left4 g W x α i)) := by
      intro i
      rw [mvfderiv2_curvNormSq (I := I) (M := M) hLC g x W hWs i]
      unfold curvComp
      refine Finset.sum_congr rfl (fun α _ => ?_)
      rw [mvfderiv_curvComp (I := I) (M := M) hLC g x W hWs hgeo α i,
        mvfderiv2_curvComp (I := I) (M := M) hLC g x W hWs hgeo α i]
      simp only [Left4]
    -- (iv) the total second-order frame correction vanishes
    have hleft : (∑ i : Fin (Module.finrank ℝ E),
        ∑ α : Fin 4 → Fin (Module.finrank ℝ E), curvComp g W α x * Left4 g W x α i) = 0 := by
      refine Finset.sum_eq_zero (fun i _ => ?_)
      have h := leftover_vanishes (I := I) (M := M) hLC g x W hWs hn hWON hWx hgeo i
      have hP : (∑ α : Fin 4 → Fin (Module.finrank ℝ E),
          Pfun g W x α * Left4 g W x α i)
          = ∑ α : Fin 4 → Fin (Module.finrank ℝ E),
              curvComp g W α x * Left4 g W x α i :=
        Finset.sum_congr rfl (fun α _ => by simp only [Pfun_eq, curvComp])
      rw [← hP]
      exact h
    -- (v) `|∇Rm|²`
    have hA : (∑ i : Fin (Module.finrank ℝ E), ∑ α : Fin 4 → Fin (Module.finrank ℝ E),
        (covRm g x (W i x) (W (α 0) x) (W (α 1) x) (W (α 2) x) (W (α 3) x)) ^ 2)
        = dRmNormSq g x := by
      have h1 : ∀ i : Fin (Module.finrank ℝ E),
          (∑ α : Fin 4 → Fin (Module.finrank ℝ E),
            (covRm g x (W i x) (W (α 0) x) (W (α 1) x) (W (α 2) x) (W (α 3) x)) ^ 2)
            = ∑ a, ∑ b, ∑ c, ∑ d,
                (covRm g x (W i x) (W a x) (W b x) (W c x) (W d x)) ^ 2 :=
        fun i => sum_four_arrow
          (fun a b c d => (covRm g x (W i x) (W a x) (W b x) (W c x) (W d x)) ^ 2)
      have h2 : ∀ i : Fin (Module.finrank ℝ E),
          (∑ a, ∑ b, ∑ c, ∑ d,
              (covRm g x (W i x) (W a x) (W b x) (W c x) (W d x)) ^ 2)
            = ∑ a, ∑ b, ∑ c, ∑ d,
                (covRm g x (onFrame g x i) (onFrame g x a) (onFrame g x b) (onFrame g x c)
                  (onFrame g x d)) ^ 2 := by
        intro i
        simp only [hWx]
      rw [Finset.sum_congr rfl (fun i _ => h1 i), Finset.sum_congr rfl (fun i _ => h2 i)]
      rfl
    have hB : (∑ i : Fin (Module.finrank ℝ E), ∑ α : Fin 4 → Fin (Module.finrank ℝ E),
        curvComp g W α x * cov2Rm g x (W i x) (W i x) (W (α 0) x) (W (α 1) x) (W (α 2) x)
            (W (α 3) x))
        = ∑ i, ∑ j, ∑ k, ∑ l, rmC g x i j k l *
            Work.Diff.PP.roughLap g x (onFrame g x) i j k l := by
      have h1 : ∀ i : Fin (Module.finrank ℝ E),
          (∑ α : Fin 4 → Fin (Module.finrank ℝ E),
            curvComp g W α x * cov2Rm g x (W i x) (W i x) (W (α 0) x) (W (α 1) x) (W (α 2) x)
                (W (α 3) x))
            = ∑ a, ∑ b, ∑ c, ∑ d, (rmP g x (W a x) (W b x) (W c x) (W d x)
                * cov2Rm g x (W i x) (W i x) (W a x) (W b x) (W c x) (W d x)) := by
        intro i
        have hcongr : (∑ α : Fin 4 → Fin (Module.finrank ℝ E),
            curvComp g W α x * cov2Rm g x (W i x) (W i x) (W (α 0) x) (W (α 1) x)
                (W (α 2) x) (W (α 3) x))
            = ∑ α : Fin 4 → Fin (Module.finrank ℝ E),
                (rmP g x (W (α 0) x) (W (α 1) x) (W (α 2) x) (W (α 3) x)
                  * cov2Rm g x (W i x) (W i x) (W (α 0) x) (W (α 1) x) (W (α 2) x)
                      (W (α 3) x)) := by
          simp only [curvComp]
        rw [hcongr]
        exact sum_four_arrow (fun a b c d => rmP g x (W a x) (W b x) (W c x) (W d x)
          * cov2Rm g x (W i x) (W i x) (W a x) (W b x) (W c x) (W d x))
      have h3 : (∑ a, ∑ b, ∑ c, ∑ d, ∑ i : Fin (Module.finrank ℝ E),
              (rmP g x (W a x) (W b x) (W c x) (W d x)
                * cov2Rm g x (W i x) (W i x) (W a x) (W b x) (W c x) (W d x)))
            = ∑ a, ∑ b, ∑ c, ∑ d, (rmC g x a b c d * ∑ m : Fin (Module.finrank ℝ E),
                Work.Diff.PP.cov2Rm g x (onFrame g x m) (onFrame g x m) (onFrame g x a)
                  (onFrame g x b) (onFrame g x c) (onFrame g x d)) := by
        refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ =>
          Finset.sum_congr rfl (fun c _ => Finset.sum_congr rfl (fun d _ => ?_))))
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun i _ => ?_)
        rw [hWx a, hWx b, hWx c, hWx d, hWx i, cov2Rm_eq_PP]
        rfl
      rw [Finset.sum_congr rfl (fun i _ => h1 i)]
      rw [sum_comm_swap5 (fun i a b c d => (rmP g x (W a x) (W b x) (W c x) (W d x)
        * cov2Rm g x (W i x) (W i x) (W a x) (W b x) (W c x) (W d x)))]
      exact h3
    -- (vii) assemble
    have hsplit : ∀ i : Fin (Module.finrank ℝ E),
        (∑ α : Fin 4 → Fin (Module.finrank ℝ E),
          (2 * (covRm g x (W i x) (W (α 0) x) (W (α 1) x) (W (α 2) x) (W (α 3) x)) ^ 2
            + 2 * curvComp g W α x
                * (cov2Rm g x (W i x) (W i x) (W (α 0) x) (W (α 1) x) (W (α 2) x)
                    (W (α 3) x) + Left4 g W x α i)))
          = 2 * (∑ α : Fin 4 → Fin (Module.finrank ℝ E),
                (covRm g x (W i x) (W (α 0) x) (W (α 1) x) (W (α 2) x) (W (α 3) x)) ^ 2)
            + 2 * (∑ α : Fin 4 → Fin (Module.finrank ℝ E),
                curvComp g W α x * cov2Rm g x (W i x) (W i x) (W (α 0) x) (W (α 1) x)
                  (W (α 2) x) (W (α 3) x))
            + 2 * (∑ α : Fin 4 → Fin (Module.finrank ℝ E),
                curvComp g W α x * Left4 g W x α i) := by
      intro i
      rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib,
        ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl (fun α _ => ?_)
      ring
    rw [← laplAt_congr_eventuallyEq (I := I) (M := M) g x hev, hstep2]
    simp only [hstep3, hsplit]
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
    simp only [← Finset.mul_sum]
    rw [hleft, hA, hB]
    ring
  · -- the zero-dimensional case is trivial
    have hzero : ∀ (u : M → ℝ) (y : M), laplAt g u y = 0 := by
      intro u y
      simp only [laplAt]
      exact Finset.sum_eq_zero (fun i _ => absurd i.isLt (by omega))
    have hzero2 : dRmNormSq g x = 0 := by
      simp only [dRmNormSq]
      exact Finset.sum_eq_zero (fun m _ => absurd m.isLt (by omega))
    have hsum0 : (∑ i : Fin (Module.finrank ℝ E), ∑ j, ∑ k, ∑ l,
        rmC g x i j k l * Work.Diff.PP.roughLap g x (onFrame g x) i j k l) = 0 :=
      Finset.sum_eq_zero (fun i _ => absurd i.isLt (by omega))
    rw [hzero (rmNormSq g) x, hzero2, hsum0]
    ring

end Work.Diff.GE
