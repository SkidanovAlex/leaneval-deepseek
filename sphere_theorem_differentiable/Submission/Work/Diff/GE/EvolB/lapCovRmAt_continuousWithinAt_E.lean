import Mathlib
import Submission.Work.Diff.GE.NablaRm
import Submission.Work.Diff.GE.BoundaryPlans
import Submission.Work.Diff.GE.lapCovRmAt_trace
import Submission.Work.Diff.GE.continuous_flow_quantities
import Submission.Work.Diff.EXT.covK_familySmooth
import Submission.Work.Diff.EXT.lapCovKRm_one_eq_lapCovRmAt

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Continuity at the initial time of `Δ(∇Rm)` along a Ricci flow (smooth level)

`Work.Diff.GE.lapCovRmAt_continuousWithinAt_E`: for a smooth Ricci flow `G` on `[0,T)`, a point `x`
and tangent vectors `v a b c d`, the function `s ↦ lapCovRmAt (G s) x v a b c d` is continuous at `0`
within `[0,T)`.

This is a verbatim copy of `Submission/Work/Diff/GE/lapCovRmAt_zero_continuous.lean` (whose public
statement is stated at the *analytic* manifold level `IsManifold I (⊤ : WithTop ℕ∞) M` and which
derives the smooth level inside the proof), re-stated at the *smooth* level
`IsManifold I ((⊤ : ENat) : WithTop ENat) M` as needed by the `EvolB` development.  All the helpers
below are taken over unchanged.

Route (the one planned in `Submission/Work/Diff/GE/BoundaryPlans.lean`):

1. **Reparametrise time** by `t = τ²`.  `τ ↦ G (τ²)` is jointly smooth on an *open* interval around
   `0` (`Work.Diff.GE.cfq_jointSmooth_sqFlow`), and continuity at `0` of the reparametrised family
   transfers back to `ContinuousWithinAt … (Ico 0 T) 0` along `s ↦ √s`
   (`Work.Diff.GE.cfq_continuousWithinAt_of_continuousAt_comp_sq`).  This is the only place where the
   half-openness of `[0,T)` is used.
2. **Compute `Δ(∇Rm)` in the chart frame.**  `lapCovRmAt` is the trace of the `(0,7)`-tensor `∇³Rm`
   in its two differentiation slots over the `Classical.epsilon`-chosen orthonormal frame, hence it
   may be evaluated in *any* frame; taking the chart frame `cFrame x · x` and contracting with the
   inverse Gram matrix (`Work.Diff.GE.lapcrc_lapCovRmAt_eq_sum_gramInv`, below) gives
   `lapCovRmAt (G t) x v a b c d = ∑ i j (GramInv G x t x) i j · cov3Rm (G t) x (cFrame x i x)
   (cFrame x j x) v a b c d`.
3. **Continuity of the two factors.**  The inverse Gram matrix of a jointly smooth metric family is
   continuous in the time variable (`Work.Diff.GE.gramInv_jointSmooth`), and the chart-frame
   components of `∇³Rm` are continuous in time through the dictionary `covKRm 3 = cov3Rm`
   (`Work.Diff.EXT.covKRm_three_eq_cov3Rm`) and the joint smoothness of the iterated covariant
   derivative tower along a metric family (`Work.Diff.EXT.covK_familySmooth`).

Nothing here uses compactness of `M` (`CompactSpace M` is part of the frozen statement but is not
needed); all the `_jointSmooth` inputs are local in `x`.
-/

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1000000

namespace Work.Diff.GE

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology Matrix InnerProductSpace
open Bundle ContDiff Set VectorField CovariantDerivative Metric

section Helpers

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [I.Boundaryless] [T2Space M]

/-! ## 1. `ℝ`-linearity of `cov3Rm` in its first two slots

`cov3RmExt` is linear in its direction argument (the direction of the `mvfderiv`, and the argument of
the six Leibniz corrections, which is fed through the continuous linear maps `lcOf g · x ·` into the
six arguments of `cov2Rm`).  This gives the `ℝ`-linearity of `cov3Rm` in its first two arguments (the
second one being the first *field* slot of `cov3RmExt`, where only the value at `x` matters). -/

private theorem lapcrc_cov3RmExt_linear_dir (hLC : LCSmooth I M) (g : SMet I M) (x : M)
    (r s : ℝ) (w₁ w₂ : TangentSpace I x) (U V A B C D : Π y : M, TangentSpace I y) :
    cov3RmExt g x (r • w₁ + s • w₂) U V A B C D
      = r * cov3RmExt g x w₁ U V A B C D + s * cov3RmExt g x w₂ U V A B C D := by
  have hd : mvfderiv I (fun y : M => cov2Rm g y (U y) (V y) (A y) (B y) (C y) (D y)) x
        (r • w₁ + s • w₂)
      = r * mvfderiv I (fun y : M => cov2Rm g y (U y) (V y) (A y) (B y) (C y) (D y)) x w₁
        + s * mvfderiv I (fun y : M => cov2Rm g y (U y) (V y) (A y) (B y) (C y) (D y)) x w₂ := by
    rw [map_add, map_smul, map_smul]
    simp only [smul_eq_mul]
  have c1 : cov2Rm g x ((lcOf g) U x (r • w₁ + s • w₂)) (V x) (A x) (B x) (C x) (D x)
      = r * cov2Rm g x ((lcOf g) U x w₁) (V x) (A x) (B x) (C x) (D x)
        + s * cov2Rm g x ((lcOf g) U x w₂) (V x) (A x) (B x) (C x) (D x) := by
    rw [map_add, map_smul, map_smul]
    rw [Kato3.cov2Rm_lin_first hLC g x r s ((lcOf g) U x w₁) ((lcOf g) U x w₂) (V x) (A x)
      (B x) (C x) (D x)]
  have c2 : cov2Rm g x (U x) ((lcOf g) V x (r • w₁ + s • w₂)) (A x) (B x) (C x) (D x)
      = r * cov2Rm g x (U x) ((lcOf g) V x w₁) (A x) (B x) (C x) (D x)
        + s * cov2Rm g x (U x) ((lcOf g) V x w₂) (A x) (B x) (C x) (D x) := by
    rw [map_add, map_smul, map_smul]
    rw [Kato3.cov2Rm_lin_snd hLC g x r s (U x) ((lcOf g) V x w₁) ((lcOf g) V x w₂) (A x)
      (B x) (C x) (D x)]
  have c3 : cov2Rm g x (U x) (V x) ((lcOf g) A x (r • w₁ + s • w₂)) (B x) (C x) (D x)
      = r * cov2Rm g x (U x) (V x) ((lcOf g) A x w₁) (B x) (C x) (D x)
        + s * cov2Rm g x (U x) (V x) ((lcOf g) A x w₂) (B x) (C x) (D x) := by
    rw [map_add, map_smul, map_smul]
    rw [Kato3.cov2Rm_lin_thd hLC g x r s (U x) (V x) ((lcOf g) A x w₁) ((lcOf g) A x w₂)
      (B x) (C x) (D x)]
  have c4 : cov2Rm g x (U x) (V x) (A x) ((lcOf g) B x (r • w₁ + s • w₂)) (C x) (D x)
      = r * cov2Rm g x (U x) (V x) (A x) ((lcOf g) B x w₁) (C x) (D x)
        + s * cov2Rm g x (U x) (V x) (A x) ((lcOf g) B x w₂) (C x) (D x) := by
    rw [map_add, map_smul, map_smul]
    rw [Kato3.cov2Rm_lin_fth hLC g x r s (U x) (V x) (A x) ((lcOf g) B x w₁)
      ((lcOf g) B x w₂) (C x) (D x)]
  have c5 : cov2Rm g x (U x) (V x) (A x) (B x) ((lcOf g) C x (r • w₁ + s • w₂)) (D x)
      = r * cov2Rm g x (U x) (V x) (A x) (B x) ((lcOf g) C x w₁) (D x)
        + s * cov2Rm g x (U x) (V x) (A x) (B x) ((lcOf g) C x w₂) (D x) := by
    rw [map_add, map_smul, map_smul]
    rw [Kato3.cov2Rm_lin_fif hLC g x r s (U x) (V x) (A x) (B x) ((lcOf g) C x w₁)
      ((lcOf g) C x w₂) (D x)]
  have c6 : cov2Rm g x (U x) (V x) (A x) (B x) (C x) ((lcOf g) D x (r • w₁ + s • w₂))
      = r * cov2Rm g x (U x) (V x) (A x) (B x) (C x) ((lcOf g) D x w₁)
        + s * cov2Rm g x (U x) (V x) (A x) (B x) (C x) ((lcOf g) D x w₂) := by
    rw [map_add, map_smul, map_smul]
    rw [Kato3.cov2Rm_lin_sixth hLC g x r s (U x) (V x) (A x) (B x) (C x) ((lcOf g) D x w₁)
      ((lcOf g) D x w₂)]
  simp only [cov3RmExt]
  rw [hd, c1, c2, c3, c4, c5, c6]
  ring

private theorem lapcrc_cov3Rm_linear_fst (hLC : LCSmooth I M) (g : SMet I M) (x : M) :
    ∀ (r s : ℝ) (w₁ w₂ u v a b c d : TangentSpace I x),
      cov3Rm g x (r • w₁ + s • w₂) u v a b c d
        = r * cov3Rm g x w₁ u v a b c d + s * cov3Rm g x w₂ u v a b c d := by
  intro r s w₁ w₂ u v a b c d
  simp only [cov3Rm]
  rw [lapcrc_cov3RmExt_linear_dir hLC g x r s w₁ w₂ (smoothExt x u) (smoothExt x v)
    (smoothExt x a) (smoothExt x b) (smoothExt x c) (smoothExt x d)]

private theorem lapcrc_cov3Rm_linear_snd (hLC : LCSmooth I M) (g : SMet I M) (x : M) :
    ∀ (r s : ℝ) (w u₁ u₂ v a b c d : TangentSpace I x),
      cov3Rm g x w (r • u₁ + s • u₂) v a b c d
        = r * cov3Rm g x w u₁ v a b c d + s * cov3Rm g x w u₂ v a b c d := by
  intro r s w u₁ u₂ v a b c d
  have hU : CMDiff ∞ (T% (smoothExt x (r • u₁ + s • u₂))) :=
    smoothExt_cmdiff x (r • u₁ + s • u₂)
  have hU' : CMDiff ∞ (T% ((fun _ : M => r) • smoothExt x u₁ + (fun _ : M => s) • smoothExt x u₂)) :=
    ((contMDiff_const (c := r)).smul_section (smoothExt_cmdiff x u₁)).add_section
      ((contMDiff_const (c := s)).smul_section (smoothExt_cmdiff x u₂))
  have hval : smoothExt x (r • u₁ + s • u₂) x
      = ((fun _ : M => r) • smoothExt x u₁ + (fun _ : M => s) • smoothExt x u₂) x := by
    rw [show ((fun _ : M => r) • smoothExt x u₁ + (fun _ : M => s) • smoothExt x u₂) x
        = r • smoothExt x u₁ x + s • smoothExt x u₂ x from rfl,
      smoothExt_apply x (r • u₁ + s • u₂), smoothExt_apply x u₁, smoothExt_apply x u₂]
  have hbind := Kato3.cov3RmExt_bind_fst hLC g x w hU hU' (smoothExt_cmdiff x v)
    (smoothExt_cmdiff x a) (smoothExt_cmdiff x b) (smoothExt_cmdiff x c) (smoothExt_cmdiff x d) hval
  have hlin := Kato3.cov3RmExt_linear_fst hLC g x w (smoothExt_cmdiff x u₁)
    (smoothExt_cmdiff x u₂) (smoothExt_cmdiff x v) (smoothExt_cmdiff x a) (smoothExt_cmdiff x b)
    (smoothExt_cmdiff x c) (smoothExt_cmdiff x d) (contMDiff_const (c := r))
    (contMDiff_const (c := s))
  simp only [cov3Rm]
  rw [hbind, hlin]

/-- The Gram matrix of the chart frame `cFrame x · x` with respect to the metric `G t`, written in
terms of the metric pairing so that no `RiemannianBundle` instance is needed to state it.  (A local
`let`/`set` binding of this matrix cannot be unfolded by `rfl`, so it is a global definition.) -/
private noncomputable def lapcrcChartGram (G : ℝ → SMet I M) (x : M) (t : ℝ) :
    Matrix (Fin (Module.finrank ℝ E)) (Fin (Module.finrank ℝ E)) ℝ :=
  fun i j => (G t).inner x (cFrame x i x) (cFrame x j x)

/-! ## 2. `Δ(∇Rm)` computed in the chart frame

`lapCovRmAt g x v a b c d = ∑ m, ∇³Rm(e_m,e_m,v,a,b,c,d)` is the trace of the `(0,7)`-tensor `∇³Rm`
in the two differentiation slots with respect to `g`; it is therefore frame independent and can be
computed in the chart frame `cFrame x · x` of the chart at `x`, by contracting with the inverse Gram
matrix of that frame.  Only the diagonal part of `∇³Rm` (in the two differentiation slots) is used,
so no symmetry of `∇³Rm` in those slots is needed: the trace formula is applied to the symmetric part
`(u,w) ↦ A u w + A w u` of the bilinear form `A(u,w) = cov3Rm g x u w v a b c d`, which has the same
trace. -/

private theorem lapcrc_lapCovRmAt_eq_sum_gramInv (hLC : LCSmooth I M) (G : ℝ → SMet I M)
    (t : ℝ) (x : M) (v a b c d : TangentSpace I x) :
    lapCovRmAt (G t) x v a b c d
      = ∑ i, ∑ j, GramInv G x t x i j
          * cov3Rm (G t) x (cFrame x i x) (cFrame x j x) v a b c d := by
  classical
  letI : RiemannianBundle (fun z : M ↦ TangentSpace I z) := ⟨(G t).toRiemannianMetric⟩
  haveI : IsContMDiffRiemannianBundle I (⊤ : ℕ∞) E (fun z : M ↦ TangentSpace I z) := inferInstance
  haveI : FiniteDimensional ℝ (TangentSpace I x) := inferInstanceAs (FiniteDimensional ℝ E)
  -- the pairing of the instance inner product is the metric pairing
  have hinner : ∀ v w : TangentSpace I x, (G t).inner x v w = Inner.inner ℝ v w := fun v w => rfl
  -- the bilinear form whose trace is `lapCovRmAt`
  set A : TangentSpace I x → TangentSpace I x → ℝ :=
    fun u w => cov3Rm (G t) x u w v a b c d with hA
  have hA1 : ∀ u₁ u₂ w : TangentSpace I x, A (u₁ + u₂) w = A u₁ w + A u₂ w := by
    intro u₁ u₂ w
    rw [hA]
    show cov3Rm (G t) x (u₁ + u₂) w v a b c d = _
    rw [show u₁ + u₂ = (1 : ℝ) • u₁ + (1 : ℝ) • u₂ from by simp]
    rw [lapcrc_cov3Rm_linear_fst hLC (G t) x 1 1 u₁ u₂ w v a b c d]
    ring
  have hA1' : ∀ (r : ℝ) (u w : TangentSpace I x), A (r • u) w = r * A u w := by
    intro r u w
    rw [hA]
    show cov3Rm (G t) x (r • u) w v a b c d = _
    rw [show r • u = r • u + (0 : ℝ) • w from by simp]
    rw [lapcrc_cov3Rm_linear_fst hLC (G t) x r 0 u w w v a b c d]
    ring
  have hA2 : ∀ u w₁ w₂ : TangentSpace I x, A u (w₁ + w₂) = A u w₁ + A u w₂ := by
    intro u w₁ w₂
    rw [hA]
    show cov3Rm (G t) x u (w₁ + w₂) v a b c d = _
    rw [show w₁ + w₂ = (1 : ℝ) • w₁ + (1 : ℝ) • w₂ from by simp]
    rw [lapcrc_cov3Rm_linear_snd hLC (G t) x 1 1 u w₁ w₂ v a b c d]
    ring
  have hA2' : ∀ (r : ℝ) (u w : TangentSpace I x), A u (r • w) = r * A u w := by
    intro r u w
    rw [hA]
    show cov3Rm (G t) x u (r • w) v a b c d = _
    rw [show r • w = r • w + (0 : ℝ) • w from by simp]
    rw [lapcrc_cov3Rm_linear_snd hLC (G t) x r 0 u w w v a b c d]
    ring
  -- the symmetric part of `A`
  set As : TangentSpace I x → TangentSpace I x → ℝ := fun u w => A u w + A w u with hAs
  have hAsadd : ∀ u₁ u₂ w : TangentSpace I x, As (u₁ + u₂) w = As u₁ w + As u₂ w := by
    intro u₁ u₂ w
    show A (u₁ + u₂) w + A w (u₁ + u₂) = (A u₁ w + A w u₁) + (A u₂ w + A w u₂)
    rw [hA1 u₁ u₂ w, hA2 w u₁ u₂]
    ring
  have hAssmul : ∀ (r : ℝ) (u w : TangentSpace I x), As (r • u) w = r * As u w := by
    intro r u w
    show A (r • u) w + A w (r • u) = r * (A u w + A w u)
    rw [hA1' r u w, hA2' r w u]
    ring
  have hAssym : ∀ u w : TangentSpace I x, As u w = As w u := by
    intro u w
    show A u w + A w u = A w u + A u w
    ring
  -- the Gram matrix of the chart frame, and its identification with `GramInv`
  have hGramInv : GramInv G x t x = (lapcrcChartGram (E := E) (I := I) (M := M) G x t)⁻¹ := rfl
  rw [hGramInv]
  have hΓ : ∀ i j, lapcrcChartGram (E := E) (I := I) (M := M) G x t i j
      = Inner.inner ℝ (cFrame x i x) (cFrame x j x) := fun i j => hinner _ _
  have hΓsym : (lapcrcChartGram (E := E) (I := I) (M := M) G x t).IsSymm := by
    rw [Matrix.IsSymm.ext_iff]
    intro i j
    rw [hΓ j i, hΓ i j]
    exact real_inner_comm _ _
  have hΓinvsym : ∀ i j, (lapcrcChartGram (E := E) (I := I) (M := M) G x t)⁻¹ i j
      = (lapcrcChartGram (E := E) (I := I) (M := M) G x t)⁻¹ j i :=
    fun i j => (Matrix.IsSymm.ext_iff.mp hΓsym.inv i j).symm
  -- the chart frame spans `TₓM` and `onFrame` is orthonormal
  have hspan : Submodule.span ℝ (Set.range (fun i => cFrame x i x)) = ⊤ :=
    cfq_cFrame_span (I := I) (M := M) x (mem_chart_source H x)
  have hON : Orthonormal ℝ (onFrame (G t) x) := by
    rw [orthonormal_iff_ite]
    intro i j
    rw [← hinner (onFrame (G t) x i) (onFrame (G t) x j)]
    exact isONFrame_onFrame (G t) x i j
  -- the trace formula for the symmetric bilinear form `As`
  have hGL : (∑ i : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
        (lapcrcChartGram (E := E) (I := I) (M := M) G x t)⁻¹ i j
          * As (cFrame x i x) (cFrame x j x))
      = ∑ i : Fin (Module.finrank ℝ E), As (onFrame (G t) x i) (onFrame (G t) x i) :=
    sum_invGram_mul_eq_sum_orthonormal (V := TangentSpace I x) As
      hAsadd hAssmul hAssym (fun i : Fin (Module.finrank ℝ E) => cFrame x i x)
      (onFrame (G t) x) hspan hON
      (lapcrcChartGram (E := E) (I := I) (M := M) G x t) hΓ
  have hLHS : (∑ i, ∑ j, (lapcrcChartGram (E := E) (I := I) (M := M) G x t)⁻¹ i j * As (cFrame x i x) (cFrame x j x))
      = 2 * (∑ i, ∑ j, (lapcrcChartGram (E := E) (I := I) (M := M) G x t)⁻¹ i j * A (cFrame x i x) (cFrame x j x)) := by
    have hswap : (∑ i, ∑ j, (lapcrcChartGram (E := E) (I := I) (M := M) G x t)⁻¹ i j * A (cFrame x j x) (cFrame x i x))
        = ∑ i, ∑ j, (lapcrcChartGram (E := E) (I := I) (M := M) G x t)⁻¹ i j * A (cFrame x i x) (cFrame x j x) := by
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
      rw [hΓinvsym i j]
    have hstep : ∀ i j : Fin (Module.finrank ℝ E),
        (lapcrcChartGram (E := E) (I := I) (M := M) G x t)⁻¹ i j * As (cFrame x i x) (cFrame x j x)
          = (lapcrcChartGram (E := E) (I := I) (M := M) G x t)⁻¹ i j * A (cFrame x i x) (cFrame x j x)
            + (lapcrcChartGram (E := E) (I := I) (M := M) G x t)⁻¹ i j * A (cFrame x j x) (cFrame x i x) := by
      intro i j
      rw [hAs]
      ring
    calc (∑ i, ∑ j, (lapcrcChartGram (E := E) (I := I) (M := M) G x t)⁻¹ i j * As (cFrame x i x) (cFrame x j x))
        = ∑ i, ∑ j, ((lapcrcChartGram (E := E) (I := I) (M := M) G x t)⁻¹ i j * A (cFrame x i x) (cFrame x j x)
            + (lapcrcChartGram (E := E) (I := I) (M := M) G x t)⁻¹ i j * A (cFrame x j x) (cFrame x i x)) :=
          Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => hstep i j))
      _ = (∑ i, ∑ j, (lapcrcChartGram (E := E) (I := I) (M := M) G x t)⁻¹ i j * A (cFrame x i x) (cFrame x j x))
            + ∑ i, ∑ j, (lapcrcChartGram (E := E) (I := I) (M := M) G x t)⁻¹ i j * A (cFrame x j x) (cFrame x i x) := by
          simp only [Finset.sum_add_distrib]
      _ = 2 * (∑ i, ∑ j, (lapcrcChartGram (E := E) (I := I) (M := M) G x t)⁻¹ i j * A (cFrame x i x) (cFrame x j x)) := by
          rw [hswap]; ring
  have hRHS : (∑ i, As (onFrame (G t) x i) (onFrame (G t) x i))
      = 2 * lapCovRmAt (G t) x v a b c d := by
    have hstep : ∀ i : Fin (Module.finrank ℝ E),
        As (onFrame (G t) x i) (onFrame (G t) x i)
          = 2 * A (onFrame (G t) x i) (onFrame (G t) x i) := by
      intro i
      rw [hAs]; ring
    rw [Finset.sum_congr rfl (fun i _ => hstep i), ← Finset.mul_sum]
    congr 1
  have key : (∑ i, ∑ j, (lapcrcChartGram (E := E) (I := I) (M := M) G x t)⁻¹ i j * A (cFrame x i x) (cFrame x j x))
      = lapCovRmAt (G t) x v a b c d := by
    have h := hGL
    rw [hLHS, hRHS] at h
    linarith
  calc lapCovRmAt (G t) x v a b c d
      = ∑ i, ∑ j, (lapcrcChartGram (E := E) (I := I) (M := M) G x t)⁻¹ i j * A (cFrame x i x) (cFrame x j x) := key.symm
    _ = ∑ i, ∑ j, (lapcrcChartGram (E := E) (I := I) (M := M) G x t)⁻¹ i j
          * cov3Rm (G t) x (cFrame x i x) (cFrame x j x) v a b c d := by
        refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
        rw [hA]

/-! ## 3. Continuity of the chart-frame components of `∇³Rm`

`covKRm (G t) x 3 = cov3Rm (G t) x` on fixed vectors (`Work.Diff.EXT.covKRm_three_eq_cov3Rm`),
and the tower `(t,y) ↦ covKRmExt (G t) k (Vf t) A B C D y` is jointly smooth along a metric family
`G` jointly smooth on an open time set (`Work.Diff.EXT.covK_familySmooth`). -/

private theorem lapcrc_cov3Rm_continuousAt (hLC : LCSmooth I M) {G : ℝ → SMet I M} {J : Set ℝ}
    (hJ : IsOpen J) (hG : JointSmooth G J) {t₀ : ℝ} (ht₀ : t₀ ∈ J) (x : M)
    (w₁ w₂ w₃ a b c d : TangentSpace I x) :
    ContinuousAt (fun t : ℝ ↦ cov3Rm (G t) x w₁ w₂ w₃ a b c d) t₀ := by
  classical
  have hV : IsOpen (J ×ˢ (univ : Set M)) := hJ.prod isOpen_univ
  have hGm : Work.Diff.EXT.JointMet G (J ×ˢ (univ : Set M)) := hG
  let w : Fin 3 → TangentSpace I x := ![w₁, w₂, w₃]
  have hWf : ∀ i : Fin 3, Work.Diff.EXT.JointField
      (fun _ : ℝ => fun y : M => smoothExt x (w i) y) (J ×ˢ (univ : Set M)) := fun i =>
    (Work.Diff.EXT.jointField_const (I := I) (M := M) (smoothExt_cmdiff x (w i))).mono
      (Set.subset_univ _)
  have hA : Work.Diff.EXT.JointField (fun _ : ℝ => fun y : M => smoothExt x a y)
      (J ×ˢ (univ : Set M)) :=
    (Work.Diff.EXT.jointField_const (I := I) (M := M) (smoothExt_cmdiff x a)).mono
      (Set.subset_univ _)
  have hB : Work.Diff.EXT.JointField (fun _ : ℝ => fun y : M => smoothExt x b y)
      (J ×ˢ (univ : Set M)) :=
    (Work.Diff.EXT.jointField_const (I := I) (M := M) (smoothExt_cmdiff x b)).mono
      (Set.subset_univ _)
  have hC : Work.Diff.EXT.JointField (fun _ : ℝ => fun y : M => smoothExt x c y)
      (J ×ˢ (univ : Set M)) :=
    (Work.Diff.EXT.jointField_const (I := I) (M := M) (smoothExt_cmdiff x c)).mono
      (Set.subset_univ _)
  have hD : Work.Diff.EXT.JointField (fun _ : ℝ => fun y : M => smoothExt x d y)
      (J ×ˢ (univ : Set M)) :=
    (Work.Diff.EXT.jointField_const (I := I) (M := M) (smoothExt_cmdiff x d)).mono
      (Set.subset_univ _)
  have hjoint := Work.Diff.EXT.covK_familySmooth (I := I) (M := M) hLC hV hGm 3 hWf hA hB hC hD
  have hAt : Work.Diff.EXT.JointSmoothAt I M
      (fun p : ℝ × M => Work.Diff.EXT.covKRmExt (G p.1) 3 (fun i : Fin 3 => smoothExt x (w i))
        (smoothExt x a) (smoothExt x b) (smoothExt x c) (smoothExt x d) p.2) t₀ x :=
    hjoint.contMDiffAt (hV.mem_nhds ⟨ht₀, mem_univ x⟩)
  refine (cfq_continuousAt_of_jointSmoothAt (I := I) (M := M) hAt).congr_of_eventuallyEq
    (Filter.Eventually.of_forall fun t => ?_)
  exact (Work.Diff.EXT.covKRm_three_eq_cov3Rm hLC (G t) x w a b c d).symm

/-! ## 4. Continuity of the inverse Gram matrix -/

private theorem lapcrc_gramInv_continuousAt (hLC : LCSmooth I M) {G : ℝ → SMet I M} {J : Set ℝ}
    (hJ : IsOpen J) (hG : JointSmooth G J) {t₀ : ℝ} (ht₀ : t₀ ∈ J) (x : M)
    (i j : Fin (Module.finrank ℝ E)) :
    ContinuousAt (fun t : ℝ ↦ GramInv G x t x i j) t₀ := by
  letI : RiemannianBundle (fun z : M ↦ TangentSpace I z) := ⟨(G t₀).toRiemannianMetric⟩
  haveI : IsContMDiffRiemannianBundle I (⊤ : ℕ∞) E (fun z : M ↦ TangentSpace I z) := inferInstance
  exact cfq_continuousAt_of_jointSmoothAt (I := I) (M := M)
    (gramInv_jointSmooth (I := I) (M := M) hJ hG ht₀ x i j)

end Helpers

/-- **Continuity of `Δ(∇Rm)` at the initial time of a Ricci flow** (smooth level). -/
theorem lapCovRmAt_continuousWithinAt_E
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [I.Boundaryless] [T2Space M] [CompactSpace M]
    (hLC : Submission.Diff.LCSmooth I M) :
    ∀ (G : ℝ → Submission.Diff.SMet I M) (T : ℝ), Submission.Diff.IsRicciFlow G T →
      ∀ x : M, ∀ v a b c d : TangentSpace I x,
        ContinuousWithinAt (fun s : ℝ ↦ Work.Diff.GE.lapCovRmAt (G s) x v a b c d)
          (Set.Ico 0 T) 0 := by
  intro G T hflow x v a b c d
  by_cases hT : T ≤ 0
  · rw [Set.Ico_eq_empty_iff.mpr (not_lt.mpr hT)]
    simp [ContinuousWithinAt, nhdsWithin_empty]
  · have hTpos : 0 < T := not_le.mp hT
    set ρ : ℝ := Real.sqrt T / 2 with hρdef
    have hρ : 0 < ρ := by positivity
    have hρT : ρ ^ 2 < T := by
      rw [hρdef, div_pow, Real.sq_sqrt (le_of_lt hTpos)]
      nlinarith
    have hsq : Submission.Diff.JointSmooth (cfq_sqFlow G) (Set.Ioo (-ρ) ρ) :=
      cfq_jointSmooth_sqFlow (I := I) (M := M) G hTpos hρ hρT hflow.1
    have h0 : (0 : ℝ) ∈ Set.Ioo (-ρ) ρ := ⟨by linarith, hρ⟩
    -- the reparametrised quantity is a finite sum of continuous functions at `τ = 0`
    have hsum : ContinuousAt (fun τ : ℝ ↦ ∑ i, ∑ j,
        GramInv (cfq_sqFlow G) x τ x i j
          * Work.Diff.GE.cov3Rm (cfq_sqFlow G τ) x (cFrame x i x) (cFrame x j x)
              v a b c d) 0 := by
      refine cfq_continuousAt_finsetSum Finset.univ (fun i _ => ?_)
      refine cfq_continuousAt_finsetSum Finset.univ (fun j _ => ?_)
      exact (lapcrc_gramInv_continuousAt (I := I) (M := M) hLC isOpen_Ioo hsq h0 x i j).mul
        (lapcrc_cov3Rm_continuousAt (I := I) (M := M) hLC isOpen_Ioo hsq h0 x
          (cFrame x i x) (cFrame x j x) v a b c d)
    have hcont : ContinuousAt (fun τ : ℝ ↦ lapCovRmAt (cfq_sqFlow G τ) x v a b c d) 0 :=
      hsum.congr_of_eventuallyEq (Filter.Eventually.of_forall fun τ =>
        (lapcrc_lapCovRmAt_eq_sum_gramInv (I := I) (M := M) hLC (cfq_sqFlow G) τ x v a b c d))
    refine cfq_continuousWithinAt_of_continuousAt_comp_sq hTpos hcont ?_
    intro s hs
    show lapCovRmAt (G s) x v a b c d = lapCovRmAt (cfq_sqFlow G (Real.sqrt s)) x v a b c d
    rw [show cfq_sqFlow G (Real.sqrt s) = G s from by
      rw [cfq_sqFlow, Real.sq_sqrt hs.1]]

end Work.Diff.GE
