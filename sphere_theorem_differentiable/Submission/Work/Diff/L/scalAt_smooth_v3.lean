import Mathlib
import Submission.Work.Diff.L.Defs
import Submission.Work.Diff.L.Stmt
import Submission.Work.Diff.L.ConnDefs
import Submission.Work.Diff.GE.scal_lapl
import Submission.Work.Diff.GE.exists_ON_frame_field_eq
import Submission.Work.Diff.GE.flowContAtZeroScal_of_isRicciFlow
import Submission.Work.Diff.EXT.rmP_field_contMDiffAt

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Smoothness of the scalar curvature, and `|∇ scal|² ≤ n² |∇Rm|²`

This module proves `Work.Diff.L.scalAt_smooth_v3`: for a smooth Riemannian metric `g` on a smooth
manifold `M` (no boundary hypothesis, no compactness),

* `x ↦ scalAt g x` is a smooth function on `M`;
* `gradSq g (scalAt g) x ≤ C * dRmNormSq g x` for a positive constant `C` — in fact for
  `C = (finrank ℝ E)²` (or `C = 1` in the degenerate case `finrank ℝ E = 0`).

The mathematical content is the classical identity `∇ scal = tr ∇Rm`: in a (smooth, locally
existing) `g`-orthonormal frame field `Ef` through a prescribed orthonormal frame,

`mvfderiv (fun y ↦ scalAlg (rmFrame g y (Ef y))) x v = scalAlg (fun i j k l ↦ covRm g x v (Ef i x) (Ef j x) (Ef k x) (Ef l x))`.

Indeed, writing `scalAlg ∘ rmFrame` as `∑ᵢ∑ⱼ Rm(eᵢ,eⱼ,eᵢ,eⱼ)` and differentiating with the Leibniz
rule for `Rm`, the four frame-rotation corrections cancel: the "velocity" matrix
`ω_{ip} = ⟪∇_v Ef i, Ef p⟫` is skew (metric compatibility) while the contracted coefficient array is
symmetric (antisymmetries plus pair exchange of `Rm`) — `Work.Diff.GE.curvForm_pair_sum_zero`.

Then `gradSq g (scalAt g) x` is the sum of squares of the `n²`-fold contractions of `∇Rm`, and
Cauchy–Schwarz gives `gradSq ≤ n² dRmNormSq`.

## Why the lemmas are restated here

The counterparts of these lemmas in `Submission.Work.Diff.GE.scal_lapl` and
`Submission.Work.Diff.GE.exists_ON_frame_field_eq` are stated inside a section carrying the
*vacuous* section variables `[I.Boundaryless]` and `[CompactSpace M]` (the files use
`set_option linter.unusedSectionVars false`, and the proofs never mention those instances).  The
statement proved here has neither hypothesis, so the lemmas are re-proved boundary-free.  All
genuinely analytic ingredients are taken from the workspace: the Leibniz rule for `Rm`
(`Work.Diff.GE.covRm_fields_eq_dRmPhi`), the boundary-free smoothness of `rmP`
(`Work.Diff.EXT.rmP_fields_smooth_ext`), the algebraic cancellation
(`Work.Diff.GE.curvForm_pair_sum_zero`), the Gram–Schmidt frame construction
(`Work.Diff.GE.gsNorm`, `Work.Diff.GE.exists_smooth_section_eq_nhds`) and the chart-coordinate joint
smoothness of `scalAt` (`Work.Diff.GE.ScalK.scalAt_jointSmoothAt`, which is already boundary-free).
-/

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1000000

namespace Work.Diff.L

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology BigOperators
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I (((⊤ : ℕ∞) : WithTop ℕ∞)) M] [T2Space M]

/-! ## 1. Locality in the germ -/

/-- `mvfderiv` of `ℝ`-valued functions respects eventual equality (boundary-free form of
`Work.Diff.GE.mvfderiv_congr_of_eventuallyEq_real`). -/
theorem mvfderiv_congr_of_eventuallyEq_real_v3 {f h : M → ℝ} {x : M} (hf : f =ᶠ[𝓝 x] h) :
    mvfderiv I f x = mvfderiv I h x := by
  rw [mvfderiv, mvfderiv, hf.eq_of_nhds, Filter.EventuallyEq.mfderiv_eq hf]
  all_goals first | rfl | (ext v; rfl)

/-! ## 2. Frame independence of the scalar curvature -/

/-- The scalar curvature traced in an arbitrary `g`-orthonormal frame is `scalAt g x`
(boundary-free form of `Work.Diff.GE.scalAt_eq_scalAlg_rmFrame_of_isONFrame`). -/
theorem scalAt_eq_scalAlg_rmFrame_of_isONFrame_v3 (g : SMet I M) (hLC : LCSmooth I M) (x : M)
    (e : Fin (Module.finrank ℝ E) → TangentSpace I x) (he : IsONFrame g x e) :
    scalAt g x = scalAlg (rmFrame g x e) := by
  obtain ⟨A, hA, hAe⟩ :=
    Work.Diff.GE.onFrame_orthogonal_change g x (onFrame g x) e
      (Work.Diff.GE.isONFrame_onFrame g x) he
  show scalAlg (rmFrame g x (onFrame g x)) = scalAlg (rmFrame g x e)
  rw [Work.Diff.GE.rmFrame_eq_rot hLC g x (onFrame g x) e A hAe]
  exact (Work.Diff.GE.rot_invariance A hA (rmFrame g x (onFrame g x))).1.symm

/-! ## 3. Leibniz rule for the curvature form `rmP` -/

/-- The derivative of the curvature component `y ↦ Rm(A(y),B(y),C(y),D(y))` along globally smooth
fields is `∇_v Rm` on the values plus the four frame-rotation corrections
(boundary-free copy of `Work.Diff.GE.rmP_mvfderiv'`). -/
theorem rmP_mvfderiv_v3 (hLC : LCSmooth I M) (g : SMet I M)
    {A B C D : Π y : M, TangentSpace I y}
    (hA : Work.Diff.GE.SmoothSect (I := I) (M := M) A)
    (hB : Work.Diff.GE.SmoothSect (I := I) (M := M) B)
    (hC : Work.Diff.GE.SmoothSect (I := I) (M := M) C)
    (hD : Work.Diff.GE.SmoothSect (I := I) (M := M) D)
    (x : M) (v : TangentSpace I x) :
    mvfderiv I (fun y : M ↦ rmP g y (A y) (B y) (C y) (D y)) x v
      = covRm g x v (A x) (B x) (C x) (D x)
        + rmP g x (lcOf g A x v) (B x) (C x) (D x)
        + rmP g x (A x) (lcOf g B x v) (C x) (D x)
        + rmP g x (A x) (B x) (lcOf g C x v) (D x)
        + rmP g x (A x) (B x) (C x) (lcOf g D x v) := by
  have hV : Work.Diff.GE.SmoothSect (I := I) (M := M) (smoothExt x v) :=
    Work.Diff.GE.smoothExt_cmdiff x v
  have hfield := Work.Diff.GE.covRm_fields_eq_dRmPhi (I := I) (M := M) (g := g) hLC
    (V := smoothExt x v) (A := A) (B := B) (C := C) (D := D) hV hA hB hC hD x
  rw [show smoothExt x v x = v from Work.Diff.GE.smoothExt_apply x v] at hfield
  rw [hfield]
  simp only [Work.Diff.GE.dRmPhi]
  ring

/-! ## 4. The frame-velocity matrix is skew -/

/-- Metric compatibility in an orthonormal frame field: the velocity matrix is skew
(boundary-free copy of `Work.Diff.GE.frameVel_skew`). -/
theorem frameVel_skew_v3 (hLC : LCSmooth I M) (g : SMet I M)
    (Ef : Fin (Module.finrank ℝ E) → Π y : M, TangentSpace I y)
    (hEf : ∀ i, Work.Diff.GE.SmoothSect (I := I) (M := M) (Ef i))
    {x : M} (hON : ∀ᶠ y in 𝓝 x, IsONFrame g y (fun i ↦ Ef i y))
    (v : TangentSpace I x) (i p : Fin (Module.finrank ℝ E)) :
    g.inner x (lcOf g (Ef i) x v) (Ef p x)
      + g.inner x (lcOf g (Ef p) x v) (Ef i x) = 0 := by
  have hder := Work.Diff.GE.kato_mvfderiv_inner_lc (I := I) (M := M) g x v (hEf i) (hEf p)
  have hconst : (fun y : M ↦ g.inner y (Ef i y) (Ef p y))
      =ᶠ[𝓝 x] (fun _ : M ↦ (if i = p then 1 else 0)) := by
    filter_upwards [hON] with y hy
    exact hy i p
  have hzero : mvfderiv I (fun y : M ↦ g.inner y (Ef i y) (Ef p y)) x v = 0 := by
    rw [mvfderiv_congr_of_eventuallyEq_real_v3 hconst]
    simp [mvfderiv_const]
  rw [hzero] at hder
  have hsym : g.inner x (Ef i x) (lcOf g (Ef p) x v)
      = g.inner x (lcOf g (Ef p) x v) (Ef i x) := g.symm x _ _
  linarith [hder, hsym]

/-! ## 5. The derivative of `scalAlg ∘ rmFrame` in a smooth orthonormal frame field -/

/-- **`∇ scal` is the contraction of `∇Rm`** (boundary-free copy of
`Work.Diff.GE.mvfderiv_scalAlg_rmFrame_frame`). -/
theorem mvfderiv_scalAlg_rmFrame_frame_v3 (hLC : LCSmooth I M) (g : SMet I M)
    (Ef : Fin (Module.finrank ℝ E) → Π y : M, TangentSpace I y)
    (hEf : ∀ i, Work.Diff.GE.SmoothSect (I := I) (M := M) (Ef i))
    {x : M} (hON : ∀ᶠ y in 𝓝 x, IsONFrame g y (fun i ↦ Ef i y))
    (hn : 0 < Module.finrank ℝ E) (v : TangentSpace I x) :
    mvfderiv I (fun y : M ↦ scalAlg (rmFrame g y (fun i ↦ Ef i y))) x v
      = scalAlg (fun i j k l ↦ covRm g x v (Ef i x) (Ef j x) (Ef k x) (Ef l x)) := by
  have hONx : IsONFrame g x (fun i ↦ Ef i x) := hON.self_of_nhds
  -- the velocity expansion of `∇_v Ef i` in the orthonormal frame at `x`
  have hX : ∀ i, lcOf g (Ef i) x v
      = ∑ p, g.inner x (lcOf g (Ef i) x v) (Ef p x) • Ef p x := by
    intro i
    exact (Work.Diff.GE.sum_smul_inner_eq_self (I := I) (M := M) g x hn (fun p ↦ Ef p x) hONx
      (lcOf g (Ef i) x v)).symm
  have hanti : ∀ i p, g.inner x (lcOf g (Ef i) x v) (Ef p x)
      + g.inner x (lcOf g (Ef p) x v) (Ef i x) = 0 :=
    fun i p ↦ frameVel_skew_v3 (I := I) (M := M) hLC g Ef hEf hON v i p
  -- the four frame-rotation corrections cancel in the contraction
  have hcorr : (∑ i, ∑ j, (rmP g x (lcOf g (Ef i) x v) (Ef j x) (Ef i x) (Ef j x)
        + rmP g x (Ef i x) (lcOf g (Ef j) x v) (Ef i x) (Ef j x)
        + rmP g x (Ef i x) (Ef j x) (lcOf g (Ef i) x v) (Ef j x)
        + rmP g x (Ef i x) (Ef j x) (Ef i x) (lcOf g (Ef j) x v))) = 0 :=
    Work.Diff.GE.curvForm_pair_sum_zero (V := TangentSpace I x) (n := Module.finrank ℝ E)
      (T := fun a b c d ↦ rmP g x a b c d)
      (fun r s a₁ a₂ b c d ↦ by
        rw [Work.Diff.GE.rmP_add_fst g hLC x (r • a₁) (s • a₂) b c d,
          Work.Diff.GE.rmP_smul_fst g hLC x r a₁ b c d,
          Work.Diff.GE.rmP_smul_fst g hLC x s a₂ b c d])
      (fun r s a b₁ b₂ c d ↦ by
        rw [Work.Diff.GE.rmP_add_snd g hLC x a (r • b₁) (s • b₂) c d,
          Work.Diff.GE.rmP_smul_snd g hLC x r a b₁ c d,
          Work.Diff.GE.rmP_smul_snd g hLC x s a b₂ c d])
      (fun r s a b c₁ c₂ d ↦ by
        rw [Work.Diff.GE.rmP_add_thd g hLC x a b (r • c₁) (s • c₂) d,
          Work.Diff.GE.rmP_smul_thd g hLC x r a b c₁ d,
          Work.Diff.GE.rmP_smul_thd g hLC x s a b c₂ d])
      (fun r s a b c d₁ d₂ ↦ by
        rw [Work.Diff.GE.rmP_add_fth g hLC x a b c (r • d₁) (s • d₂),
          Work.Diff.GE.rmP_smul_fth g hLC x r a b c d₁,
          Work.Diff.GE.rmP_smul_fth g hLC x s a b c d₂])
      (fun a b c d ↦ by rw [Work.Diff.GE.rmP_antisymm hLC g x a b c d]; ring)
      (fun a b c d ↦ by rw [Work.Diff.GE.rmP_skew hLC g x a b c d]; ring)
      (fun a b c d ↦ Work.EXT.rmP_pair_symm hLC g x a b c d)
      (fun i ↦ Ef i x) (fun i ↦ lcOf g (Ef i) x v)
      (fun i p ↦ g.inner x (lcOf g (Ef i) x v) (Ef p x)) hX hanti
  -- rewrite `scalAlg ∘ rmFrame` as a double sum of `rmP` and differentiate term by term
  have hfun : (fun y : M ↦ scalAlg (rmFrame g y (fun i ↦ Ef i y)))
      = fun y : M ↦ ∑ i, ∑ j, rmP g y (Ef i y) (Ef j y) (Ef i y) (Ef j y) := by
    funext y
    simp only [scalAlg]
    rfl
  rw [hfun]
  have hinner : ∀ i, Work.Diff.GE.SmoothScal (I := I) (M := M)
      (fun y : M ↦ ∑ j, rmP g y (Ef i y) (Ef j y) (Ef i y) (Ef j y)) := by
    intro i
    refine ContMDiff.sum fun j _ ↦ ?_
    exact Work.Diff.EXT.rmP_fields_smooth_ext (I := I) (M := M) hLC g
      (hEf i) (hEf j) (hEf i) (hEf j)
  rw [Work.Diff.GE.Kato3.mvfderiv_sum Finset.univ
    (fun i y ↦ ∑ j, rmP g y (Ef i y) (Ef j y) (Ef i y) (Ef j y)) hinner x v]
  have hstep : ∀ i, mvfderiv I
        (fun y : M ↦ ∑ j, rmP g y (Ef i y) (Ef j y) (Ef i y) (Ef j y)) x v
      = ∑ j, mvfderiv I (fun y : M ↦ rmP g y (Ef i y) (Ef j y) (Ef i y) (Ef j y)) x v := by
    intro i
    rw [Work.Diff.GE.Kato3.mvfderiv_sum Finset.univ
      (fun j y ↦ rmP g y (Ef i y) (Ef j y) (Ef i y) (Ef j y))
      (fun j ↦ Work.Diff.EXT.rmP_fields_smooth_ext (I := I) (M := M) hLC g
        (hEf i) (hEf j) (hEf i) (hEf j)) x v]
  rw [Finset.sum_congr rfl (fun i _ ↦ hstep i)]
  have hfive : ∀ i j, mvfderiv I
        (fun y : M ↦ rmP g y (Ef i y) (Ef j y) (Ef i y) (Ef j y)) x v
      = covRm g x v (Ef i x) (Ef j x) (Ef i x) (Ef j x)
        + rmP g x (lcOf g (Ef i) x v) (Ef j x) (Ef i x) (Ef j x)
        + rmP g x (Ef i x) (lcOf g (Ef j) x v) (Ef i x) (Ef j x)
        + rmP g x (Ef i x) (Ef j x) (lcOf g (Ef i) x v) (Ef j x)
        + rmP g x (Ef i x) (Ef j x) (Ef i x) (lcOf g (Ef j) x v) :=
    fun i j ↦ rmP_mvfderiv_v3 (I := I) (M := M) hLC g (hEf i) (hEf j) (hEf i) (hEf j) x v
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

/-! ## 6. A globally smooth field of orthonormal frames through a prescribed frame -/

/-- **A globally smooth field of orthonormal frames with prescribed value at `x`**, on a merely
smooth manifold (no `[I.Boundaryless]`).  Boundary-free copy of
`Work.Diff.GE.exists_ON_frame_field_eq`. -/
theorem frame_field_eq_v3 (g : SMet I M) (x : M)
    (e : Fin (Module.finrank ℝ E) → TangentSpace I x) (he : IsONFrame g x e) :
    ∃ Ef : Fin (Module.finrank ℝ E) → Π y : M, TangentSpace I y,
      (∀ i, Ef i x = e i) ∧ (∀ i, Work.Diff.GE.SmoothSect (I := I) (M := M) (Ef i)) ∧
        (∀ᶠ y in 𝓝 x, IsONFrame g y (fun i ↦ Ef i y)) := by
  classical
  -- globally smooth extensions of the prescribed frame `e`
  let F : Fin (Module.finrank ℝ E) → Π y : M, TangentSpace I y :=
    fun i => smoothExt x (e i)
  have hF : ∀ i, Work.Diff.GE.SmoothSect (I := I) (M := M) (F i) :=
    fun i => Work.Diff.GE.smoothExt_cmdiff x (e i)
  have hFx : ∀ i, F i x = e i := fun i => Work.Diff.GE.smoothExt_apply x (e i)
  have hONx : IsONFrame g x (fun i => F i x) := by
    intro i j
    show g.inner x (F i x) (F j x) = if i = j then 1 else 0
    rw [hFx i, hFx j]
    exact he i j
  -- the family stays pointwise linearly independent near `x`
  have hli : ∀ᶠ y in 𝓝 x, LinearIndependent ℝ (fun i : Fin (Module.finrank ℝ E) => F i y) :=
    Work.Diff.GE.eventually_linearIndependent F (fun i => (hF i).contMDiffAt)
      (Work.Diff.GE.linearIndependent_of_isONFrame g x (fun i => F i x) hONx)
  -- its Gram-Schmidt normalisation is smooth and orthonormal near `x`
  have hsm : ∀ i, ∀ᶠ y in 𝓝 x, CMDiffAt ∞ (T% (Work.Diff.GE.gsNorm g F i)) y := fun i =>
    hli.mono (fun y hy => Work.Diff.GE.gsNorm_contMDiffAt_of_linearIndependent g F hF i y hy)
  have hONnear : ∀ᶠ y in 𝓝 x,
      IsONFrame g y (fun i => Work.Diff.GE.gsNorm g F i y) :=
    hli.mono (fun y hy => Work.Diff.GE.isONFrame_gsNorm (g := g) hy)
  -- globalise, one field at a time
  choose Ef hEfsm hEfx hEfeq using fun i =>
    Work.Diff.GE.exists_smooth_section_eq_nhds (Work.Diff.GE.gsNorm g F i) (hsm i)
  refine ⟨Ef, ?_, ?_, ?_⟩
  · intro i
    rw [hEfx i, Work.Diff.GE.gsNorm_apply_of_isONFrame g x hONx i, hFx i]
  · intro i
    exact hEfsm i
  · filter_upwards [hONnear, Filter.eventually_all.mpr hEfeq] with y h1 h2
    have hfun : (fun i => Ef i y) = fun i => Work.Diff.GE.gsNorm g F i y :=
      funext fun i => h2 i
    rw [hfun]
    exact h1

/-! ## 7. The derivative of the scalar curvature as the contraction of `∇Rm` -/

/-- `∇ scal` is the contraction of `∇Rm` in the `Classical.epsilon`-chosen frame `onFrame g x`. -/
theorem mvfderiv_scalAt_eq_sum_v3 (hLC : LCSmooth I M) (g : SMet I M) (x : M)
    (hn : 0 < Module.finrank ℝ E) (v : TangentSpace I x) :
    mvfderiv I (scalAt g) x v
      = ∑ i, ∑ j, covRm g x v (onFrame g x i) (onFrame g x j) (onFrame g x i)
          (onFrame g x j) := by
  obtain ⟨Ef, hEfx, hEfsm, hON⟩ :=
    frame_field_eq_v3 (I := I) (M := M) g x (onFrame g x) (Work.Diff.GE.isONFrame_onFrame g x)
  have hgerm : scalAt g =ᶠ[𝓝 x] (fun y : M ↦ scalAlg (rmFrame g y (fun i ↦ Ef i y))) := by
    filter_upwards [hON] with y hy
    exact scalAt_eq_scalAlg_rmFrame_of_isONFrame_v3 g hLC y (fun i ↦ Ef i y) hy
  rw [mvfderiv_congr_of_eventuallyEq_real_v3 hgerm,
    mvfderiv_scalAlg_rmFrame_frame_v3 (I := I) (M := M) hLC g Ef hEfsm hON hn v]
  simp only [scalAlg, hEfx]

/-- `|∇ scal|²` is the sum of the squares of the contractions of `∇Rm`. -/
theorem gradSq_scalAt_eq_sum_v3 (hLC : LCSmooth I M) (g : SMet I M) (x : M)
    (hn : 0 < Module.finrank ℝ E) :
    gradSq g (scalAt g) x
      = ∑ m, (∑ i, ∑ j, covRm g x (onFrame g x m) (onFrame g x i) (onFrame g x j)
          (onFrame g x i) (onFrame g x j)) ^ 2 := by
  simp only [gradSq]
  refine Finset.sum_congr rfl (fun m _ => ?_)
  rw [mvfderiv_scalAt_eq_sum_v3 (I := I) (M := M) hLC g x hn]

/-! ## 8. The elementary contraction bound -/

/-- Cauchy–Schwarz for a finite sum, packaged for the estimate below. -/
private theorem sq_sum_le_card_mul_sum_sq_real_v3 {ι : Type*} [Fintype ι] (f : ι → ℝ) :
    (∑ i, f i) ^ 2 ≤ (Fintype.card ι : ℝ) * ∑ i, f i ^ 2 := by
  simpa using sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := f)

/-- Pulling a constant out of a double sum. -/
private theorem mul_sum_sum_v3 {ι κ : Type*} [Fintype ι] [Fintype κ] (c : ℝ) (f : ι → κ → ℝ) :
    c * ∑ i, ∑ j, f i j = ∑ i, c * ∑ j, f i j := by
  rw [Finset.mul_sum]

/-- **The trace of a curvature array is controlled by its total square.**  For an array
`T : Fin N → … → Fin N → ℝ` the `N` traces `∑ᵢⱼ T m i j i j` of the slices satisfy
`∑ₘ (trace m)² ≤ N² ∑ₘ ∑ᵢⱼₖₗ (T m i j k l)²`. -/
theorem trace_sq_le_sum_sq_v3 {N : ℕ} (hN : 1 ≤ N)
    (T : Fin N → Fin N → Fin N → Fin N → Fin N → ℝ) :
    ∑ m, (∑ i, ∑ j, T m i j i j) ^ 2
      ≤ (N : ℝ) ^ 2 * ∑ m, ∑ i, ∑ j, ∑ k, ∑ l, (T m i j k l) ^ 2 := by
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have key : ∀ f : Fin N → ℝ, (∑ i, f i) ^ 2 ≤ (N : ℝ) * ∑ i, f i ^ 2 := by
    intro f
    simpa using sq_sum_le_card_mul_sum_sq_real_v3 f
  have hpair : ∀ m i j, (T m i j i j) ^ 2 ≤ ∑ k, ∑ l, (T m i j k l) ^ 2 := by
    intro m i j
    have h1 : (T m i j i j) ^ 2 ≤ ∑ l, (T m i j i l) ^ 2 :=
      Finset.single_le_sum (f := fun l => (T m i j i l) ^ 2)
        (fun l _ => sq_nonneg _) (Finset.mem_univ j)
    have h2 : (∑ l, (T m i j i l) ^ 2) ≤ ∑ k, ∑ l, (T m i j k l) ^ 2 :=
      Finset.single_le_sum (f := fun k => ∑ l, (T m i j k l) ^ 2)
        (fun k _ => Finset.sum_nonneg (fun l _ => sq_nonneg _)) (Finset.mem_univ i)
    linarith
  have hstep : ∀ m, (∑ i, ∑ j, T m i j i j) ^ 2
      ≤ (N : ℝ) ^ 2 * ∑ i, ∑ j, ∑ k, ∑ l, (T m i j k l) ^ 2 := by
    intro m
    have hinner : ∀ i, (∑ j, T m i j i j) ^ 2 ≤ (N : ℝ) * ∑ j, (T m i j i j) ^ 2 :=
      fun i => key (fun j => T m i j i j)
    have houter : (∑ i, (∑ j, T m i j i j)) ^ 2
        ≤ (N : ℝ) * ∑ i, (∑ j, T m i j i j) ^ 2 := key (fun i => ∑ j, T m i j i j)
    have hsum : (∑ i, ∑ j, (T m i j i j) ^ 2) ≤ ∑ i, ∑ j, ∑ k, ∑ l, (T m i j k l) ^ 2 :=
      Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ => hpair m i j))
    calc (∑ i, ∑ j, T m i j i j) ^ 2
        ≤ (N : ℝ) * ∑ i, (∑ j, T m i j i j) ^ 2 := houter
      _ ≤ (N : ℝ) * ∑ i, ((N : ℝ) * ∑ j, (T m i j i j) ^ 2) :=
            mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun i _ => hinner i)) (le_of_lt hNpos)
      _ = (N : ℝ) ^ 2 * ∑ i, ∑ j, (T m i j i j) ^ 2 := by
            rw [mul_sum_sum_v3]
            rw [Finset.mul_sum]
            exact Finset.sum_congr rfl (fun i _ => by ring)
      _ ≤ (N : ℝ) ^ 2 * ∑ i, ∑ j, ∑ k, ∑ l, (T m i j k l) ^ 2 :=
            mul_le_mul_of_nonneg_left hsum (by positivity)
  calc ∑ m, (∑ i, ∑ j, T m i j i j) ^ 2
      ≤ ∑ m, (N : ℝ) ^ 2 * (∑ i, ∑ j, ∑ k, ∑ l, (T m i j k l) ^ 2) :=
        Finset.sum_le_sum (fun m _ => hstep m)
    _ = (N : ℝ) ^ 2 * ∑ m, ∑ i, ∑ j, ∑ k, ∑ l, (T m i j k l) ^ 2 := by
        rw [Finset.mul_sum]

/-! ## 9. The uniform bound `|∇ scal|² ≤ n² |∇Rm|²` -/

/-- **`|∇ scal|² ≤ n² |∇Rm|²`** for every smooth metric `g`, with `n = finrank ℝ E ≥ 1`. -/
theorem gradSq_scalAt_le_dRmNormSq_v3 (hLC : LCSmooth I M) (g : SMet I M) (x : M)
    (hdim : 1 ≤ Module.finrank ℝ E) :
    gradSq g (scalAt g) x ≤ (Module.finrank ℝ E : ℝ) ^ 2 * dRmNormSq g x := by
  have hn : 0 < Module.finrank ℝ E := hdim
  rw [gradSq_scalAt_eq_sum_v3 (I := I) (M := M) hLC g x hn]
  have hD : dRmNormSq g x
      = ∑ m, ∑ i, ∑ j, ∑ k, ∑ l, (covRm g x (onFrame g x m) (onFrame g x i)
          (onFrame g x j) (onFrame g x k) (onFrame g x l)) ^ 2 := rfl
  rw [hD]
  exact trace_sq_le_sum_sq_v3 hdim
    (fun m i j k l => covRm g x (onFrame g x m) (onFrame g x i) (onFrame g x j)
      (onFrame g x k) (onFrame g x l))

/-! ## 10. Smoothness of the scalar curvature -/

/-- **`scalAt g` is a smooth function.**  The global statement follows from the chart-coordinate
joint smoothness `Work.Diff.GE.ScalK.scalAt_jointSmoothAt` applied to the constant family `G ≡ g`,
restricted to the time slice `t = 0`. -/
theorem scalAt_contMDiffAt_v3 (hLC : LCSmooth I M) (g : SMet I M) (x : M) :
    ContMDiffAt I (modelWithCornersSelf ℝ ℝ) (((⊤ : ℕ∞) : WithTop ℕ∞)) (fun y : M ↦ scalAt g y)
      x := by
  have hJS : JointSmooth (fun _ : ℝ ↦ g) Set.univ := by
    rw [JointSmooth, Set.univ_prod_univ, contMDiffOn_univ]
    exact g.contMDiff.comp contMDiff_snd
  have hjoint : ContMDiffAt (𝓘(ℝ,ℝ).prod I) 𝓘(ℝ,ℝ) ∞
      (fun p : ℝ × M ↦ scalAt g p.2) (0, x) :=
    Work.Diff.GE.ScalK.scalAt_jointSmoothAt (I := I) (M := M) hLC (G := fun _ : ℝ ↦ g)
      (J := Set.univ) isOpen_univ hJS (t₀ := 0) trivial x
  have h0 : ContMDiffAt I 𝓘(ℝ,ℝ) ∞ (fun _ : M ↦ (0 : ℝ)) x := contMDiffAt_const
  have hid : ContMDiffAt I I ∞ (fun y : M ↦ y) x := contMDiffAt_id
  have hpair : ContMDiffAt I (𝓘(ℝ,ℝ).prod I) ∞ (fun y : M ↦ ((0 : ℝ), y)) x := h0.prodMk hid
  have hcomp := ContMDiffAt.comp x hjoint hpair
  exact hcomp

/-! ## 11. The target -/

theorem scalAt_smooth_v3
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I (((⊤ : ℕ∞) : WithTop ℕ∞)) M] [T2Space M]
    (hLC : Submission.Diff.LCSmooth I M) (g : Submission.Diff.SMet I M) :
    (∃ S : M → ℝ, ContMDiff I (modelWithCornersSelf ℝ ℝ) (((⊤ : ℕ∞) : WithTop ℕ∞)) S ∧
      ∀ x, S x = Submission.Diff.scalAt g x) ∧
    (∃ C : ℝ, 0 < C ∧ ∀ x : M,
      Submission.Diff.gradSq g (Submission.Diff.scalAt g) x ≤ C * Submission.Diff.dRmNormSq g x) := by
  constructor
  · refine ⟨Submission.Diff.scalAt g, ?_, fun x => rfl⟩
    exact fun x => scalAt_contMDiffAt_v3 (I := I) (M := M) hLC g x
  · by_cases hn : Module.finrank ℝ E = 0
    · haveI : IsEmpty (Fin (Module.finrank ℝ E)) := by rw [hn]; infer_instance
      refine ⟨1, one_pos, fun x => ?_⟩
      have h1 : Submission.Diff.gradSq g (Submission.Diff.scalAt g) x = 0 := by
        simp only [Submission.Diff.gradSq, Finset.univ_eq_empty, Finset.sum_empty]
      have h2 : Submission.Diff.dRmNormSq g x = 0 := by
        simp only [Submission.Diff.dRmNormSq, Finset.univ_eq_empty, Finset.sum_empty]
      rw [h1, h2]
      norm_num
    · have hdim : 1 ≤ Module.finrank ℝ E := Nat.one_le_iff_ne_zero.mpr hn
      refine ⟨(Module.finrank ℝ E : ℝ) ^ 2, ?_,
        fun x => gradSq_scalAt_le_dRmNormSq_v3 (I := I) (M := M) hLC g x hdim⟩
      have h2 : (0 : ℝ) < (Module.finrank ℝ E : ℝ) := by
        exact_mod_cast Nat.pos_of_ne_zero hn
      positivity

end Work.Diff.L
