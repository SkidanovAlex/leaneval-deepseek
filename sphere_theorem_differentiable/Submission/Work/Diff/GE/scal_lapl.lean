import Mathlib
import Submission.Diff.Evol
import Submission.Work.Diff.GE.scal_lapl_defs
import Submission.Work.Diff.GE.scal_lapl_basic
import Submission.Work.Diff.GE.curvbasic
import Submission.Work.Diff.GE.Frame
import Submission.Work.Diff.GE.NablaRm
import Submission.Work.Diff.GE.Kato3.CovRmKit
import Submission.Work.Diff.GE.kato_mvfderiv_inner_lc
import Submission.Work.Diff.GE.laplAt_eq_sum_hessAt
import Submission.Work.Diff.GE.hessAt_comm
import Submission.Work.Diff.GE.cov2RmExt_prelim
import Submission.Work.Diff.Evol.CBDefs
import Submission.Work.Diff.Evol.covRm_pair
import Submission.Work.Diff.Evol.covRm_skew12
import Submission.Work.EXT.rmP_pair_symm
import Submission.Work.Diff.GE.curvForm_pair_sum_zero
import Submission.Work.Diff.GE.exists_ON_frame_field_eq
import Submission.Work.Diff.GE.mvfderiv_covRm_fields

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The scalar Laplacian identity `Δ scal = scalAlg (lapRmFrame)`

`Submission.Diff.LapRmFrameParallel` (the `Evol` contract) asks for a smooth
`g`-orthonormal frame field `Ef` through a prescribed orthonormal frame `e` of `TₓM` which is
*parallel at `x`*, and then identifies `laplAt g (ℓ ∘ rmFrame ∘ Ef) x` with `ℓ (lapRmFrame g x e)`
for every continuous linear `ℓ`.

For the *scalar* equation (`EvolScal`, area GE/EV3) only `ℓ = scalAlg` is needed, and then
parallelism at `x` is not needed at all: in the contraction `∑ᵢⱼ Rᵢⱼᵢⱼ` the frame-velocity
corrections cancel automatically, because the velocity matrix `ωᵢₚ = ⟨∇_v Ef i, Ef p⟩` is *skew*
(metric compatibility) while the contracted coefficient array `∑ⱼ Rm(e_p,e_j,e_i,e_j)` is
*symmetric* (antisymmetries + pair exchange of `Rm`).  This file proves the resulting

`laplAt g (scalAt g) x = scalAlg (lapRmFrame g x e)`

for *any* `g`-orthonormal frame `e` of `TₓM`, with no exponential map, no parallel transport and no
radial-parallel frame: only a smooth orthonormal frame field near `x` is needed
(`Work.Diff.GE.exists_ON_frame_field_eq`).

The two computational steps are

* `mvfderiv (scalAlg ∘ rmFrame ∘ Ef) x v = scalAlg (∇_v Rm)`;
* `hessAt (scalAlg ∘ rmFrame ∘ Ef) x v w = scalAlg (∇²_{v,w} Rm)`,

each obtained from the field-level Leibniz rule for `Rm` (`rmP_mvfderiv'`,
`Work.Diff.GE.mvfderiv_covRm_fields`) together with the cancellation
`Work.Diff.GE.curvForm_pair_sum_zero`.
-/

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option maxHeartbeats 800000

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology BigOperators
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter

namespace Work.Diff.GE

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [I.Boundaryless] [T2Space M] [CompactSpace M]

/-! ## 0. Toolbox -/

/-- `rmFrame` in terms of `rmP`. -/
theorem rmFrame_eq_rmP' (g : SMet I M) (y : M)
    (e : Fin (Module.finrank ℝ E) → TangentSpace I y) :
    rmFrame g y e = fun i j k l ↦ rmP g y (e i) (e j) (e k) (e l) := rfl

/-- **Leibniz rule for `Rm` along fields.**  The derivative of the curvature component
`y ↦ Rm(A(y),B(y),C(y),D(y))` is the covariant derivative `∇_v Rm` evaluated on the values plus the
four frame-rotation corrections (the definition of `covRm` on the chosen extensions). -/
theorem rmP_mvfderiv' (hLC : LCSmooth I M) (g : SMet I M)
    {A B C D : Π y : M, TangentSpace I y}
    (hA : SmoothSect (I := I) (M := M) A) (hB : SmoothSect (I := I) (M := M) B)
    (hC : SmoothSect (I := I) (M := M) C) (hD : SmoothSect (I := I) (M := M) D)
    (x : M) (v : TangentSpace I x) :
    mvfderiv I (fun y : M ↦ rmP g y (A y) (B y) (C y) (D y)) x v
      = covRm g x v (A x) (B x) (C x) (D x)
        + rmP g x (lcOf g A x v) (B x) (C x) (D x)
        + rmP g x (A x) (lcOf g B x v) (C x) (D x)
        + rmP g x (A x) (B x) (lcOf g C x v) (D x)
        + rmP g x (A x) (B x) (C x) (lcOf g D x v) := by
  have hV : SmoothSect (I := I) (M := M) (smoothExt x v) := smoothExt_cmdiff x v
  have hfield := Work.Diff.GE.covRm_fields_eq_dRmPhi (I := I) (M := M) (g := g) hLC
    (V := smoothExt x v) (A := A) (B := B) (C := C) (D := D) hV hA hB hC hD x
  rw [show smoothExt x v x = v from smoothExt_apply x v] at hfield
  rw [hfield]
  simp only [Work.Diff.GE.dRmPhi]
  ring

/-! ## 1. The frame-velocity matrix is skew -/

/-- **Metric compatibility in the frame.**  For a smooth frame field `Ef` which is `g`-orthonormal
near `x`, the "velocity matrix" `ωᵢₚ = g(∇_v Ef i, Ef p)` is skew at `x`. -/
theorem frameVel_skew (hLC : LCSmooth I M) (g : SMet I M)
    (Ef : Fin (Module.finrank ℝ E) → Π y : M, TangentSpace I y)
    (hEf : ∀ i, SmoothSect (I := I) (M := M) (Ef i))
    {x : M} (hON : ∀ᶠ y in 𝓝 x, IsONFrame g y (fun i ↦ Ef i y))
    (v : TangentSpace I x) (i p : Fin (Module.finrank ℝ E)) :
    g.inner x (lcOf g (Ef i) x v) (Ef p x)
      + g.inner x (lcOf g (Ef p) x v) (Ef i x) = 0 := by
  have hder := kato_mvfderiv_inner_lc (I := I) (M := M) g x v (hEf i) (hEf p)
  have hconst : (fun y : M ↦ g.inner y (Ef i y) (Ef p y))
      =ᶠ[𝓝 x] (fun _ : M ↦ (if i = p then 1 else 0)) := by
    filter_upwards [hON] with y hy
    exact hy i p
  have hzero : mvfderiv I (fun y : M ↦ g.inner y (Ef i y) (Ef p y)) x v = 0 := by
    rw [mvfderiv_congr_of_eventuallyEq_real hconst]
    simp [mvfderiv_const]
  rw [hzero] at hder
  have hsym : g.inner x (Ef i x) (lcOf g (Ef p) x v)
      = g.inner x (lcOf g (Ef p) x v) (Ef i x) := g.symm x _ _
  linarith [hder, hsym]

/-! ## 2. First derivative of `scalAlg ∘ rmFrame` in a smooth orthonormal frame field -/

/-- **The derivative of the scalar curvature in a frame field is the contraction of `∇Rm`.** -/
theorem mvfderiv_scalAlg_rmFrame_frame (hLC : LCSmooth I M) (g : SMet I M)
    (Ef : Fin (Module.finrank ℝ E) → Π y : M, TangentSpace I y)
    (hEf : ∀ i, SmoothSect (I := I) (M := M) (Ef i))
    {x : M} (hON : ∀ᶠ y in 𝓝 x, IsONFrame g y (fun i ↦ Ef i y))
    (hn : 0 < Module.finrank ℝ E) (v : TangentSpace I x) :
    mvfderiv I (fun y : M ↦ scalAlg (rmFrame g y (fun i ↦ Ef i y))) x v
      = scalAlg (fun i j k l ↦ covRm g x v (Ef i x) (Ef j x) (Ef k x) (Ef l x)) := by
  have hONx : IsONFrame g x (fun i ↦ Ef i x) := hON.self_of_nhds
  -- the velocity expansion of `∇_v Ef i` in the orthonormal frame at `x`
  have hX : ∀ i, lcOf g (Ef i) x v
      = ∑ p, g.inner x (lcOf g (Ef i) x v) (Ef p x) • Ef p x := by
    intro i
    exact (sum_smul_inner_eq_self (I := I) (M := M) g x hn (fun p ↦ Ef p x) hONx
      (lcOf g (Ef i) x v)).symm
  have hanti : ∀ i p, g.inner x (lcOf g (Ef i) x v) (Ef p x)
      + g.inner x (lcOf g (Ef p) x v) (Ef i x) = 0 :=
    fun i p ↦ frameVel_skew (I := I) (M := M) hLC g Ef hEf hON v i p
  -- the four frame-rotation corrections cancel in the contraction
  have hcorr : (∑ i, ∑ j, (rmP g x (lcOf g (Ef i) x v) (Ef j x) (Ef i x) (Ef j x)
        + rmP g x (Ef i x) (lcOf g (Ef j) x v) (Ef i x) (Ef j x)
        + rmP g x (Ef i x) (Ef j x) (lcOf g (Ef i) x v) (Ef j x)
        + rmP g x (Ef i x) (Ef j x) (Ef i x) (lcOf g (Ef j) x v))) = 0 :=
    curvForm_pair_sum_zero (V := TangentSpace I x) (n := Module.finrank ℝ E)
      (T := fun a b c d ↦ rmP g x a b c d)
      (fun r s a₁ a₂ b c d ↦ by
        rw [rmP_add_fst g hLC x (r • a₁) (s • a₂) b c d, rmP_smul_fst g hLC x r a₁ b c d,
          rmP_smul_fst g hLC x s a₂ b c d])
      (fun r s a b₁ b₂ c d ↦ by
        rw [rmP_add_snd g hLC x a (r • b₁) (s • b₂) c d, rmP_smul_snd g hLC x r a b₁ c d,
          rmP_smul_snd g hLC x s a b₂ c d])
      (fun r s a b c₁ c₂ d ↦ by
        rw [rmP_add_thd g hLC x a b (r • c₁) (s • c₂) d, rmP_smul_thd g hLC x r a b c₁ d,
          rmP_smul_thd g hLC x s a b c₂ d])
      (fun r s a b c d₁ d₂ ↦ by
        rw [rmP_add_fth g hLC x a b c (r • d₁) (s • d₂), rmP_smul_fth g hLC x r a b c d₁,
          rmP_smul_fth g hLC x s a b c d₂])
      (fun a b c d ↦ by rw [rmP_antisymm hLC g x a b c d]; ring)
      (fun a b c d ↦ by rw [rmP_skew hLC g x a b c d]; ring)
      (fun a b c d ↦ Work.EXT.rmP_pair_symm hLC g x a b c d)
      (fun i ↦ Ef i x) (fun i ↦ lcOf g (Ef i) x v)
      (fun i p ↦ g.inner x (lcOf g (Ef i) x v) (Ef p x)) hX hanti
  -- rewrite `scalAlg ∘ rmFrame` as a double sum of `rmP` and differentiate term by term
  have hfun : (fun y : M ↦ scalAlg (rmFrame g y (fun i ↦ Ef i y)))
      = fun y : M ↦ ∑ i, ∑ j, rmP g y (Ef i y) (Ef j y) (Ef i y) (Ef j y) := by
    funext y
    rw [rmFrame_eq_rmP']
    simp only [scalAlg]
  rw [hfun]
  have hinner : ∀ i, SmoothScal (I := I) (M := M)
      (fun y : M ↦ ∑ j, rmP g y (Ef i y) (Ef j y) (Ef i y) (Ef j y)) := by
    intro i
    refine ContMDiff.sum fun j _ ↦ ?_
    exact Work.Diff.Evol.rmP_fields_smooth (I := I) (M := M) hLC g
      (hEf i) (hEf j) (hEf i) (hEf j)
  rw [Work.Diff.GE.Kato3.mvfderiv_sum Finset.univ
    (fun i y ↦ ∑ j, rmP g y (Ef i y) (Ef j y) (Ef i y) (Ef j y)) hinner x v]
  have hstep : ∀ i, mvfderiv I
        (fun y : M ↦ ∑ j, rmP g y (Ef i y) (Ef j y) (Ef i y) (Ef j y)) x v
      = ∑ j, mvfderiv I (fun y : M ↦ rmP g y (Ef i y) (Ef j y) (Ef i y) (Ef j y)) x v := by
    intro i
    rw [Work.Diff.GE.Kato3.mvfderiv_sum Finset.univ
      (fun j y ↦ rmP g y (Ef i y) (Ef j y) (Ef i y) (Ef j y))
      (fun j ↦ Work.Diff.Evol.rmP_fields_smooth (I := I) (M := M) hLC g
        (hEf i) (hEf j) (hEf i) (hEf j)) x v]
  rw [Finset.sum_congr rfl (fun i _ ↦ hstep i)]
  have hfive : ∀ i j, mvfderiv I
        (fun y : M ↦ rmP g y (Ef i y) (Ef j y) (Ef i y) (Ef j y)) x v
      = covRm g x v (Ef i x) (Ef j x) (Ef i x) (Ef j x)
        + rmP g x (lcOf g (Ef i) x v) (Ef j x) (Ef i x) (Ef j x)
        + rmP g x (Ef i x) (lcOf g (Ef j) x v) (Ef i x) (Ef j x)
        + rmP g x (Ef i x) (Ef j x) (lcOf g (Ef i) x v) (Ef j x)
        + rmP g x (Ef i x) (Ef j x) (Ef i x) (lcOf g (Ef j) x v) :=
    fun i j ↦ rmP_mvfderiv' (I := I) (M := M) hLC g (hEf i) (hEf j) (hEf i) (hEf j) x v
  rw [Finset.sum_congr rfl (fun i _ ↦ Finset.sum_congr rfl (fun j _ ↦ hfive i j))]
  -- split off the `∇Rm` part and the four corrections
  have hsplit : (∑ i, ∑ j, (covRm g x v (Ef i x) (Ef j x) (Ef i x) (Ef j x)
        + rmP g x (lcOf g (Ef i) x v) (Ef j x) (Ef i x) (Ef j x)
        + rmP g x (Ef i x) (lcOf g (Ef j) x v) (Ef i x) (Ef j x)
        + rmP g x (Ef i x) (Ef j x) (lcOf g (Ef i) x v) (Ef j x)
        + rmP g x (Ef i x) (Ef j x) (Ef i x) (lcOf g (Ef j) x v)))
      = scalAlg (fun i j k l ↦ covRm g x v (Ef i x) (Ef j x) (Ef k x) (Ef l x))
        + (∑ i, ∑ j, (rmP g x (lcOf g (Ef i) x v) (Ef j x) (Ef i x) (Ef j x)
          + rmP g x (Ef i x) (lcOf g (Ef j) x v) (Ef i x) (Ef j x)
          + rmP g x (Ef i x) (Ef j x) (lcOf g (Ef i) x v) (Ef j x)
          + rmP g x (Ef i x) (Ef j x) (Ef i x) (lcOf g (Ef j) x v))) := by
    simp only [scalAlg, Finset.sum_add_distrib]
    ring
  rw [hsplit, hcorr, add_zero]

/-! ## 3. The second derivative of `scalAlg ∘ rmFrame` in a smooth orthonormal frame field -/

/-- **The second derivative of the scalar curvature in a frame field is the contraction of
`∇²Rm`.**  (`hessAt g u x v w` is the second covariant derivative `∇²_{v,w} u`.) -/
theorem hessAt_scalAlg_rmFrame_frame (hLC : LCSmooth I M) (g : SMet I M)
    (Ef : Fin (Module.finrank ℝ E) → Π y : M, TangentSpace I y)
    (hEf : ∀ i, SmoothSect (I := I) (M := M) (Ef i))
    {x : M} (hON : ∀ᶠ y in 𝓝 x, IsONFrame g y (fun i ↦ Ef i y))
    (hn : 0 < Module.finrank ℝ E) (v w : TangentSpace I x) :
    hessAt g (fun y : M ↦ scalAlg (rmFrame g y (fun i ↦ Ef i y))) x v w
      = scalAlg (fun i j k l ↦ Submission.Diff.cov2Rm g x v w (Ef i x) (Ef j x) (Ef k x) (Ef l x)) := by
  -- the frame is orthonormal on a neighbourhood of each of its points
  have hON' : ∀ᶠ y in 𝓝 x, ∀ᶠ z in 𝓝 y, IsONFrame g z (fun i ↦ Ef i z) := by
    have hmem : {z : M | IsONFrame g z (fun i ↦ Ef i z)} ∈ 𝓝 x := hON
    refine Filter.mem_of_superset
      (isOpen_interior.mem_nhds (mem_interior_iff_mem_nhds.mpr hmem)) ?_
    intro y hy
    exact Filter.mem_of_superset (isOpen_interior.mem_nhds hy)
      (fun z hz ↦ interior_subset hz)
  -- the pointwise first-derivative identity
  have hpt : (fun y : M ↦ mvfderiv I (fun z : M ↦ scalAlg (rmFrame g z (fun i ↦ Ef i z)))
        y (smoothExt x w y))
      =ᶠ[𝓝 x] fun y : M ↦ ∑ i, ∑ j,
        covRm g y (smoothExt x w y) (Ef i y) (Ef j y) (Ef i y) (Ef j y) := by
    filter_upwards [hON'] with y hy
    rw [mvfderiv_scalAlg_rmFrame_frame (I := I) (M := M) hLC g Ef hEf hy hn (smoothExt x w y)]
    simp only [scalAlg]
  have hstep1 : mvfderiv I (fun y : M ↦ mvfderiv I
        (fun z : M ↦ scalAlg (rmFrame g z (fun i ↦ Ef i z))) y (smoothExt x w y)) x v
      = mvfderiv I (fun y : M ↦ ∑ i, ∑ j,
          covRm g y (smoothExt x w y) (Ef i y) (Ef j y) (Ef i y) (Ef j y)) x v := by
    rw [mvfderiv_congr_of_eventuallyEq_real hpt]
  -- differentiate the double sum term by term
  have hinner : ∀ i, SmoothScal (I := I) (M := M)
      (fun y : M ↦ ∑ j, covRm g y (smoothExt x w y) (Ef i y) (Ef j y) (Ef i y) (Ef j y)) := by
    intro i
    refine ContMDiff.sum fun j _ ↦ ?_
    exact Work.Diff.GE.covRm_fields_smooth (I := I) (M := M) hLC
      (V := smoothExt x w) (A := Ef i) (B := Ef j) (C := Ef i) (D := Ef j)
      (smoothExt_cmdiff x w) (hEf i) (hEf j) (hEf i) (hEf j)
  have hstep2 : mvfderiv I (fun y : M ↦ ∑ i, ∑ j,
        covRm g y (smoothExt x w y) (Ef i y) (Ef j y) (Ef i y) (Ef j y)) x v
      = ∑ i, ∑ j, mvfderiv I (fun y : M ↦
          covRm g y (smoothExt x w y) (Ef i y) (Ef j y) (Ef i y) (Ef j y)) x v := by
    rw [Work.Diff.GE.Kato3.mvfderiv_sum Finset.univ
      (fun i y ↦ ∑ j, covRm g y (smoothExt x w y) (Ef i y) (Ef j y) (Ef i y) (Ef j y)) hinner x v]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [Work.Diff.GE.Kato3.mvfderiv_sum Finset.univ
      (fun j y ↦ covRm g y (smoothExt x w y) (Ef i y) (Ef j y) (Ef i y) (Ef j y))
      (fun j ↦ Work.Diff.GE.covRm_fields_smooth (I := I) (M := M) hLC
        (V := smoothExt x w) (A := Ef i) (B := Ef j) (C := Ef i) (D := Ef j)
        (smoothExt_cmdiff x w) (hEf i) (hEf j) (hEf i) (hEf j)) x v]
  -- the five-slot Leibniz rule for `∇Rm`
  have hfive : ∀ i j, mvfderiv I (fun y : M ↦
        covRm g y (smoothExt x w y) (Ef i y) (Ef j y) (Ef i y) (Ef j y)) x v
      = Submission.Diff.cov2Rm g x v (smoothExt x w x) (Ef i x) (Ef j x) (Ef i x) (Ef j x)
        + covRm g x (lcOf g (smoothExt x w) x v) (Ef i x) (Ef j x) (Ef i x) (Ef j x)
        + covRm g x (smoothExt x w x) (lcOf g (Ef i) x v) (Ef j x) (Ef i x) (Ef j x)
        + covRm g x (smoothExt x w x) (Ef i x) (lcOf g (Ef j) x v) (Ef i x) (Ef j x)
        + covRm g x (smoothExt x w x) (Ef i x) (Ef j x) (lcOf g (Ef i) x v) (Ef j x)
        + covRm g x (smoothExt x w x) (Ef i x) (Ef j x) (Ef i x) (lcOf g (Ef j) x v) := by
    intro i j
    exact mvfderiv_covRm_fields (I := I) (M := M) hLC g
      (V := smoothExt x w) (A := Ef i) (B := Ef j) (C := Ef i) (D := Ef j)
      (smoothExt_cmdiff x w) (hEf i) (hEf j) (hEf i) (hEf j) x v
  -- the four frame-rotation corrections cancel
  have hONx : IsONFrame g x (fun i ↦ Ef i x) := hON.self_of_nhds
  have hX : ∀ i, lcOf g (Ef i) x v
      = ∑ p, g.inner x (lcOf g (Ef i) x v) (Ef p x) • Ef p x := by
    intro i
    exact (sum_smul_inner_eq_self (I := I) (M := M) g x hn (fun p ↦ Ef p x) hONx
      (lcOf g (Ef i) x v)).symm
  have hanti : ∀ i p, g.inner x (lcOf g (Ef i) x v) (Ef p x)
      + g.inner x (lcOf g (Ef p) x v) (Ef i x) = 0 :=
    fun i p ↦ frameVel_skew (I := I) (M := M) hLC g Ef hEf hON v i p
  have hcorr : (∑ i, ∑ j,
        (covRm g x (smoothExt x w x) (lcOf g (Ef i) x v) (Ef j x) (Ef i x) (Ef j x)
        + covRm g x (smoothExt x w x) (Ef i x) (lcOf g (Ef j) x v) (Ef i x) (Ef j x)
        + covRm g x (smoothExt x w x) (Ef i x) (Ef j x) (lcOf g (Ef i) x v) (Ef j x)
        + covRm g x (smoothExt x w x) (Ef i x) (Ef j x) (Ef i x) (lcOf g (Ef j) x v))) = 0 :=
    curvForm_pair_sum_zero (V := TangentSpace I x) (n := Module.finrank ℝ E)
      (T := fun a b c d ↦ covRm g x (smoothExt x w x) a b c d)
      (fun r s a₁ a₂ b c d ↦
        Work.Diff.GE.covRm_linear_snd hLC g x (smoothExt x w x) r s a₁ a₂ b c d)
      (fun r s a b₁ b₂ c d ↦
        Work.Diff.GE.covRm_linear_thd hLC g x (smoothExt x w x) a r s b₁ b₂ c d)
      (fun r s a b c₁ c₂ d ↦
        Work.Diff.GE.covRm_linear_fth hLC g x (smoothExt x w x) a b r s c₁ c₂ d)
      (fun r s a b c d₁ d₂ ↦
        Work.Diff.GE.covRm_linear_fif hLC g x (smoothExt x w x) a b c r s d₁ d₂)
      (fun a b c d ↦ by
        have h := Work.Diff.Evol.covRm_skew12 (I := I) (M := M) hLC g x (smoothExt x w x) a b c d
        linarith [h])
      (fun a b c d ↦ by
        have h := Work.Diff.GE.Kato3.covRm_skew_last (I := I) (M := M) hLC g x
          (smoothExt x w x) a b c d
        linarith [h])
      (fun a b c d ↦
        Work.Diff.Evol.covRm_pair (I := I) (M := M) hLC g x (smoothExt x w x) a b c d)
      (fun i ↦ Ef i x) (fun i ↦ lcOf g (Ef i) x v)
      (fun i p ↦ g.inner x (lcOf g (Ef i) x v) (Ef p x)) hX hanti
  -- the first-order identity at `x`, applied to the connection direction
  have hV : mvfderiv I (fun z : M ↦ scalAlg (rmFrame g z (fun i ↦ Ef i z))) x
        (lcOf g (smoothExt x w) x v)
      = ∑ i, ∑ j, covRm g x (lcOf g (smoothExt x w) x v)
          (Ef i x) (Ef j x) (Ef i x) (Ef j x) := by
    rw [mvfderiv_scalAlg_rmFrame_frame (I := I) (M := M) hLC g Ef hEf hON hn
      (lcOf g (smoothExt x w) x v)]
    simp only [scalAlg]
  -- assemble
  have hmain : mvfderiv I (fun y : M ↦ mvfderiv I
        (fun z : M ↦ scalAlg (rmFrame g z (fun i ↦ Ef i z))) y (smoothExt x w y)) x v
      = scalAlg (fun i j k l ↦ Submission.Diff.cov2Rm g x v (smoothExt x w x)
            (Ef i x) (Ef j x) (Ef k x) (Ef l x))
        + mvfderiv I (fun z : M ↦ scalAlg (rmFrame g z (fun i ↦ Ef i z))) x
            (lcOf g (smoothExt x w) x v) := by
    rw [hstep1, hstep2,
      Finset.sum_congr rfl (fun i _ ↦ Finset.sum_congr rfl (fun j _ ↦ hfive i j))]
    have hsplit : (∑ i, ∑ j, (Submission.Diff.cov2Rm g x v (smoothExt x w x)
            (Ef i x) (Ef j x) (Ef i x) (Ef j x)
          + covRm g x (lcOf g (smoothExt x w) x v) (Ef i x) (Ef j x) (Ef i x) (Ef j x)
          + covRm g x (smoothExt x w x) (lcOf g (Ef i) x v) (Ef j x) (Ef i x) (Ef j x)
          + covRm g x (smoothExt x w x) (Ef i x) (lcOf g (Ef j) x v) (Ef i x) (Ef j x)
          + covRm g x (smoothExt x w x) (Ef i x) (Ef j x) (lcOf g (Ef i) x v) (Ef j x)
          + covRm g x (smoothExt x w x) (Ef i x) (Ef j x) (Ef i x) (lcOf g (Ef j) x v)))
        = scalAlg (fun i j k l ↦ Submission.Diff.cov2Rm g x v (smoothExt x w x)
              (Ef i x) (Ef j x) (Ef k x) (Ef l x))
          + (∑ i, ∑ j, covRm g x (lcOf g (smoothExt x w) x v)
              (Ef i x) (Ef j x) (Ef i x) (Ef j x))
          + (∑ i, ∑ j,
            (covRm g x (smoothExt x w x) (lcOf g (Ef i) x v) (Ef j x) (Ef i x) (Ef j x)
            + covRm g x (smoothExt x w x) (Ef i x) (lcOf g (Ef j) x v) (Ef i x) (Ef j x)
            + covRm g x (smoothExt x w x) (Ef i x) (Ef j x) (lcOf g (Ef i) x v) (Ef j x)
            + covRm g x (smoothExt x w x) (Ef i x) (Ef j x) (Ef i x) (lcOf g (Ef j) x v))) := by
      simp only [scalAlg, Finset.sum_add_distrib]
      ring
    rw [hsplit, hcorr, add_zero, ← hV]
  -- `hessAt` is this expression minus the connection term
  rw [hessAt, hmain, smoothExt_apply]
  ring

/-! ## 4. The Laplacian of the scalar curvature -/

/-- **`Δ (scalAt g) x` is the contraction of the rough Laplacian of the curvature** in any
`g`-orthonormal frame of `TₓM`.  This is the scalar case of `LapRmFrameParallel`; it needs no
parallel frame at `x`. -/
theorem laplAt_scalAt_eq_scalAlg_lapRmFrame (hLC : LCSmooth I M) (g : SMet I M) (x : M)
    (e : Fin (Module.finrank ℝ E) → TangentSpace I x) (he : IsONFrame g x e) :
    laplAt g (scalAt g) x = scalAlg (lapRmFrame g x e) := by
  by_cases hn : 0 < Module.finrank ℝ E
  · obtain ⟨Ef, hEx, hEfsm, hON⟩ :=
      exists_ON_frame_field_eq (I := I) (M := M) g x e he
    set F : M → ℝ := fun y ↦ scalAlg (rmFrame g y (fun i ↦ Ef i y)) with hFdef
    have hFsm : SmoothScal (I := I) (M := M) F := by
      rw [hFdef]
      have hfun : (fun y : M ↦ scalAlg (rmFrame g y (fun i ↦ Ef i y)))
          = fun y : M ↦ ∑ i, ∑ j, rmP g y (Ef i y) (Ef j y) (Ef i y) (Ef j y) := by
        funext y
        rw [rmFrame_eq_rmP']
        simp only [scalAlg]
      rw [hfun]
      exact ContMDiff.sum fun i _ ↦ ContMDiff.sum fun j _ ↦
        Work.Diff.Evol.rmP_fields_smooth (I := I) (M := M) hLC g
          (hEfsm i) (hEfsm j) (hEfsm i) (hEfsm j)
    -- `F` agrees with `scalAt g` near `x`
    have hloc : laplAt g (scalAt g) x = laplAt g F x := by
      refine laplAt_congr_of_eventuallyEq (I := I) (M := M) g x ?_
      filter_upwards [hON] with y hy
      rw [hFdef]
      exact scalAt_eq_scalAlg_rmFrame_of_isONFrame (I := I) (M := M) g hLC y
        (fun i ↦ Ef i y) hy
    rw [hloc]
    -- `F` is smooth, so the Laplacian is the trace of its Hessian in the frame `e`
    have h2 : ContMDiffAt I (modelWithCornersSelf ℝ ℝ) 2 F x :=
      (hFsm.contMDiffAt).of_le (by simp)
    have hsym : ∀ v w : TangentSpace I x, hessAt g F x v w = hessAt g F x w v :=
      fun v w ↦ hessAt_comm (I := I) (M := M) hLC g F x h2 v w
    rw [laplAt_eq_sum_hessAt (I := I) (M := M) g F x e he hsym]
    calc ∑ i, hessAt g F x (e i) (e i)
        = ∑ i, scalAlg (fun j k l m ↦
            Submission.Diff.cov2Rm g x (e i) (e i) (Ef j x) (Ef k x) (Ef l x) (Ef m x)) := by
          refine Finset.sum_congr rfl fun i _ ↦ ?_
          rw [hFdef, hessAt_scalAlg_rmFrame_frame (I := I) (M := M) hLC g Ef hEfsm hON hn
            (e i) (e i)]
      _ = scalAlg (lapRmFrame g x e) := by
          simp only [scalAlg, lapRmFrame, hEx]
          calc ∑ i, ∑ x_1, ∑ x_2, Submission.Diff.cov2Rm g x (e i) (e i) (e x_1) (e x_2) (e x_1) (e x_2)
              = ∑ x_1, ∑ i, ∑ x_2, Submission.Diff.cov2Rm g x (e i) (e i) (e x_1) (e x_2) (e x_1) (e x_2) :=
                Finset.sum_comm
            _ = ∑ x_1, ∑ x_2, ∑ i, Submission.Diff.cov2Rm g x (e i) (e i) (e x_1) (e x_2) (e x_1) (e x_2) := by
                refine Finset.sum_congr rfl fun y _ ↦ Finset.sum_comm
            _ = ∑ i, ∑ j, ∑ m, Submission.Diff.cov2Rm g x (e m) (e m) (e i) (e j) (e i) (e j) := rfl
  · have hn0 : Module.finrank ℝ E = 0 := Nat.eq_zero_of_not_pos hn
    have h1 : laplAt g (scalAt g) x = 0 := by
      simp only [laplAt]
      exact Finset.sum_eq_zero fun i _ ↦ Fin.elim0 (hn0 ▸ i)
    have h2 : scalAlg (lapRmFrame g x e) = 0 := by
      simp only [scalAlg]
      exact Finset.sum_eq_zero fun i _ ↦ Fin.elim0 (hn0 ▸ i)
    rw [h1, h2]

end Work.Diff.GE
