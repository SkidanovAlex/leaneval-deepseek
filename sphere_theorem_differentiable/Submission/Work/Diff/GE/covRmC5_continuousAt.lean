/-
# Continuity in the flow parameter of the chart components of `∇Rm`

`Work.Diff.GE.covRmC5 G x t x m i j k l` is the component `(∇_{σ_m}Rm)(σ_i,σ_j,σ_k,σ_l)` of the
covariant derivative of the curvature of the metric `G t`, computed in the coordinate frame of the
chart at `x`.  This file proves that for a family of metrics `G` jointly smooth on an open time set
`J ∋ t₀`, these components are continuous in `t` at `t₀`.

The proof expands `covRm` through the field form `Work.Diff.GE.Kato3.covRm_field_form` into the
five terms of `Work.Diff.GE.dRmPhi`:

* the spatial derivative term `mvfderiv (fun y ↦ rmP (G t) y …) x v`, continuous in `t` by
  `Work.Diff.EXT.continuousAt_mvfderiv_family` once `(t,y) ↦ rmP (G t) y …` is jointly smooth
  (`rmP_jointSmoothNoCompact`);
* the four connection correction terms `rmP (G t) x (∇_v A) …`, where the *moving* vector `∇_v A`
  is expanded in the time-independent chart frame `fr x j` with coefficients
  `Work.Diff.EXT.reconCoef` (continuous in `t` by `reconCoef_continuousAt`), the three fixed slots
  are expanded in the same frame with *constant* coefficients (`c5_eq_sum_fixCoef`), and the resulting
  fourfold sum of products of continuous functions of `t` times `rmC4 (G t) x t x …` (continuous in
  `t` by `rmC4_jointSmooth`) is continuous.
-/

import Mathlib
import Submission.Work.Diff.GE.norms_defs
import Submission.Work.Diff.EXT.ricCore
import Submission.Work.Diff.GE.rmP_jointSmooth
import Submission.Work.Diff.GE.gramInv_jointSmooth
import Submission.Work.Diff.GE.dRmNormSq_eq_N5_of_basis
import Submission.Work.Diff.EXT.continuousAt_mvfderiv_family
import Submission.Work.Diff.EXT.contMDiffAt_mvfderiv_along_field
import Submission.Work.Diff.T.lcOf_apply_inner_koszul
import Submission.Work.Diff.GE.react.dbKit
import Submission.Work.Diff.Evol.diffBianchiA
import Submission.Work.Diff.GE.Kato3.CovRmKit
import Submission.Work.Diff.EXT.reconDefs
import Submission.Work.Diff.EXT.kosDefs
import Submission.Work.Diff.EXT.contMDiffAt_metric_pairing
import Submission.Work.Diff.EXT.contMDiffAt_matrix_inv
import Submission.Work.Diff.GE.NablaRm
import Submission.Work.Diff.GE.dRmPhi
import Submission.Work.Diff.GE.rmP_jointSmoothNoCompact
import Submission.Work.Diff.GE.reconCoef_continuousAt

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1600000

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology
open Bundle ContDiff Set VectorField CovariantDerivative Metric

namespace Work.Diff.GE

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [I.Boundaryless]
  [T2Space M]

/-! ## Toolbox -/

/-- The chosen smooth extension `smoothExt x u` is a `C^∞` field at `x`. -/
lemma c5_smoothFieldAt_smoothExt (x : M) (u : TangentSpace I x) :
    Work.Diff.EXT.SmoothFieldAt I M (smoothExt x u) x := by
  simpa [Work.Diff.EXT.SmoothFieldAt] using
    (Work.Diff.GE.react.db.smoothExt_spec x u).1.contMDiffAt (x := x)

/-- Metric pairings of two fixed tangent vectors are continuous in the family parameter. -/
lemma c5_inner_fixed_continuousAt {G : ℝ → SMet I M} {J : Set ℝ} (hJ : IsOpen J)
    (hG : JointSmooth G J) {t₀ : ℝ} (ht₀ : t₀ ∈ J) (x : M) (u v : TangentSpace I x) :
    ContinuousAt (fun t : ℝ ↦ (G t).inner x u v) t₀ := by
  have hp := Work.Diff.EXT.contMDiffAt_metric_pairing (I := I) (M := M) (G := G) (J := J)
    hJ hG ht₀ (Y := smoothExt x u) (Z := smoothExt x v)
    (c5_smoothFieldAt_smoothExt x u) (c5_smoothFieldAt_smoothExt x v)
  have h2 : ContMDiffAt 𝓘(ℝ,ℝ) (𝓘(ℝ,ℝ).prod I) ∞ (fun t : ℝ ↦ (t, x)) t₀ :=
    contMDiffAt_id.prodMk contMDiffAt_const
  have h3 := hp.comp t₀ h2
  refine h3.continuousAt.congr_of_eventuallyEq ?_
  filter_upwards with t
  simp [Work.Diff.GE.react.db.smoothExt_apply]

/-! ## Continuity of the frozen curvature components -/

/-- The chart curvature components at the chart centre are continuous in the family parameter. -/
lemma c5_rmC4_continuousAt {G : ℝ → SMet I M} {J : Set ℝ} (hLC : LCSmooth I M) (hJ : IsOpen J)
    (hG : JointSmooth G J) {t₀ : ℝ} (ht₀ : t₀ ∈ J) (x : M)
    (i j k l : Fin (Module.finrank ℝ E)) :
    ContinuousAt (fun t : ℝ ↦ rmC4 (I := I) G x t x i j k l) t₀ := by
  letI : RiemannianBundle (fun y : M ↦ TangentSpace I y) := ⟨(G t₀).toRiemannianMetric⟩
  haveI : IsContMDiffRiemannianBundle I ∞ E (fun y : M ↦ TangentSpace I y) := inferInstance
  have h := rmC4_jointSmooth (I := I) (M := M) hLC hJ hG ht₀ x i j k l
  have h2 : ContMDiffAt 𝓘(ℝ,ℝ) (𝓘(ℝ,ℝ).prod I) ∞ (fun t : ℝ ↦ (t, x)) t₀ :=
    contMDiffAt_id.prodMk contMDiffAt_const
  exact (h.comp t₀ h2).continuousAt

/-! ## Expansions in the time-independent chart frame -/

/-- A `t`-independent coefficient of a fixed tangent vector in the chart frame of the chart at
`x`, computed with the metric `G t₀`. -/
noncomputable def c5_fixCoef (G : ℝ → SMet I M) (x : M) (t₀ : ℝ) (w : TangentSpace I x)
    (k : Fin (Module.finrank ℝ E)) : ℝ :=
  (Matrix.mulVec (Work.Diff.EXT.gramM (I := I) (G t₀) x x)⁻¹
    (fun i ↦ (G t₀).inner x w (Work.Diff.EXT.fr (I := I) x i x))) k

/-- Every fixed tangent vector is the sum of `c5_fixCoef` times the chart frame vectors (an
identity with coefficients that do not depend on the family parameter). -/
lemma c5_eq_sum_fixCoef (G : ℝ → SMet I M) (x : M) (t₀ : ℝ) (w : TangentSpace I x) :
    w = ∑ k, c5_fixCoef (I := I) G x t₀ w k • Work.Diff.EXT.fr (I := I) x k x := by
  have h := Work.Diff.EXT.eq_sum_frameVector_of_pairing (I := I) (g := G t₀) (x₀ := x) (p := x)
    (mem_chart_source H x) w
  simpa only [c5_fixCoef, Work.Diff.EXT.gramM, Work.Diff.EXT.fr] using h

/-- The covariant derivative `∇_v A` expanded in the chart frame, with the explicit (continuous in
`t`) coefficients `Work.Diff.EXT.reconCoef`. -/
lemma c5_lcOf_eq_sum_reconCoef {G : ℝ → SMet I M} (x : M) (v : TangentSpace I x)
    {A : Π y : M, TangentSpace I y} (hA : Work.Diff.EXT.SmoothFieldAt I M A x) (t : ℝ) :
    lcOf (G t) A x v
      = ∑ j, Work.Diff.EXT.reconCoef (I := I) G x (smoothExt x v) A j t x
          • Work.Diff.EXT.fr (I := I) x j x := by
  have h := Work.Diff.EXT.lcOf_eq_sum_reconCoef (I := I) G x (smoothExt x v) A t (y := x)
    (mem_chart_source H x) (c5_smoothFieldAt_smoothExt x v) hA
  simpa only [Work.Diff.GE.react.db.smoothExt_apply] using h

/-! ## Continuity of `rmP` on expanded slots -/

/-- **Continuity of `rmP` with all four slots expanded in the chart frame.**  If every slot is a sum
of the time-independent frame vectors with coefficients continuous in `t`, then the whole expression
is continuous in `t`. -/
lemma c5_rmP_sum4_continuousAt {G : ℝ → SMet I M} {J : Set ℝ} (hLC : LCSmooth I M)
    (hJ : IsOpen J) (hG : JointSmooth G J) {t₀ : ℝ} (ht₀ : t₀ ∈ J) (x : M)
    (c₁ c₂ c₃ c₄ : Fin (Module.finrank ℝ E) → ℝ → ℝ)
    (hc₁ : ∀ j, ContinuousAt (c₁ j) t₀) (hc₂ : ∀ j, ContinuousAt (c₂ j) t₀)
    (hc₃ : ∀ j, ContinuousAt (c₃ j) t₀) (hc₄ : ∀ j, ContinuousAt (c₄ j) t₀) :
    ContinuousAt (fun t : ℝ ↦ rmP (G t) x
        (∑ j, c₁ j t • Work.Diff.EXT.fr (I := I) x j x)
        (∑ j, c₂ j t • Work.Diff.EXT.fr (I := I) x j x)
        (∑ j, c₃ j t • Work.Diff.EXT.fr (I := I) x j x)
        (∑ j, c₄ j t • Work.Diff.EXT.fr (I := I) x j x)) t₀ := by
  have hbase : ∀ j k l m : Fin (Module.finrank ℝ E),
      ContinuousAt (fun t : ℝ ↦ rmP (G t) x (Work.Diff.EXT.fr (I := I) x j x)
        (Work.Diff.EXT.fr (I := I) x k x) (Work.Diff.EXT.fr (I := I) x l x)
        (Work.Diff.EXT.fr (I := I) x m x)) t₀ :=
    fun j k l m => c5_rmC4_continuousAt (I := I) (M := M) hLC hJ hG ht₀ x j k l m
  have hexp : ∀ t : ℝ,
      rmP (G t) x (∑ j, c₁ j t • Work.Diff.EXT.fr (I := I) x j x)
        (∑ j, c₂ j t • Work.Diff.EXT.fr (I := I) x j x)
        (∑ j, c₃ j t • Work.Diff.EXT.fr (I := I) x j x)
        (∑ j, c₄ j t • Work.Diff.EXT.fr (I := I) x j x)
      = ∑ j, c₁ j t * (∑ k, c₂ k t * (∑ l, c₃ l t * (∑ m, c₄ m t *
          rmP (G t) x (Work.Diff.EXT.fr (I := I) x j x) (Work.Diff.EXT.fr (I := I) x k x)
            (Work.Diff.EXT.fr (I := I) x l x) (Work.Diff.EXT.fr (I := I) x m x)))) := by
    intro t
    simp only [rmP_sum_fst hLC (G t) x Finset.univ, rmP_sum_snd hLC (G t) x Finset.univ,
      rmP_sum_thd hLC (G t) x Finset.univ, rmP_sum_fth hLC (G t) x Finset.univ]
  rw [funext hexp]
  refine tendsto_finsetSum Finset.univ (fun j _ => ?_)
  refine (hc₁ j).mul ?_
  refine tendsto_finsetSum Finset.univ (fun k _ => ?_)
  refine (hc₂ k).mul ?_
  refine tendsto_finsetSum Finset.univ (fun l _ => ?_)
  refine (hc₃ l).mul ?_
  refine tendsto_finsetSum Finset.univ (fun m _ => ?_)
  exact (hc₄ m).mul (hbase j k l m)

/-- Continuity of `rmP` on four families whose chart-frame expansions are known. -/
lemma c5_rmP_of_eq_sum4 {G : ℝ → SMet I M} {J : Set ℝ} (hLC : LCSmooth I M) (hJ : IsOpen J)
    (hG : JointSmooth G J) {t₀ : ℝ} (ht₀ : t₀ ∈ J) (x : M)
    {W₁ W₂ W₃ W₄ : ℝ → TangentSpace I x}
    {c₁ c₂ c₃ c₄ : Fin (Module.finrank ℝ E) → ℝ → ℝ}
    (hc₁ : ∀ j, ContinuousAt (c₁ j) t₀) (hc₂ : ∀ j, ContinuousAt (c₂ j) t₀)
    (hc₃ : ∀ j, ContinuousAt (c₃ j) t₀) (hc₄ : ∀ j, ContinuousAt (c₄ j) t₀)
    (hW₁ : ∀ t : ℝ, W₁ t = ∑ j, c₁ j t • Work.Diff.EXT.fr (I := I) x j x)
    (hW₂ : ∀ t : ℝ, W₂ t = ∑ j, c₂ j t • Work.Diff.EXT.fr (I := I) x j x)
    (hW₃ : ∀ t : ℝ, W₃ t = ∑ j, c₃ j t • Work.Diff.EXT.fr (I := I) x j x)
    (hW₄ : ∀ t : ℝ, W₄ t = ∑ j, c₄ j t • Work.Diff.EXT.fr (I := I) x j x) :
    ContinuousAt (fun t : ℝ ↦ rmP (G t) x (W₁ t) (W₂ t) (W₃ t) (W₄ t)) t₀ := by
  have h := c5_rmP_sum4_continuousAt (I := I) (M := M) hLC hJ hG ht₀ x c₁ c₂ c₃ c₄
    hc₁ hc₂ hc₃ hc₄
  simpa only [hW₁, hW₂, hW₃, hW₄] using h

/-! ## The four connection correction terms -/

/-- The connection correction term with the moving vector in the **first** slot. -/
lemma c5_lcOf_rmP_slot1 {G : ℝ → SMet I M} {J : Set ℝ} (hLC : LCSmooth I M) (hJ : IsOpen J)
    (hG : JointSmooth G J) {t₀ : ℝ} (ht₀ : t₀ ∈ J) (x : M) (v : TangentSpace I x)
    {A : Π y : M, TangentSpace I y} (hA : Work.Diff.GE.SmoothField (I := I) (M := M) A)
    (w₁ w₂ w₃ : TangentSpace I x) :
    ContinuousAt (fun t : ℝ ↦ rmP (G t) x (lcOf (G t) A x v) w₁ w₂ w₃) t₀ := by
  have hA' : Work.Diff.EXT.SmoothFieldAt I M A x := hA.contMDiffAt (x := x)
  refine c5_rmP_of_eq_sum4 (I := I) (M := M) hLC hJ hG ht₀ x
    (W₁ := fun t => lcOf (G t) A x v) (W₂ := fun _ => w₁) (W₃ := fun _ => w₂)
    (W₄ := fun _ => w₃)
    (c₁ := fun j t => Work.Diff.EXT.reconCoef (I := I) G x (smoothExt x v) A j t x)
    (c₂ := fun j _ => c5_fixCoef (I := I) G x t₀ w₁ j)
    (c₃ := fun j _ => c5_fixCoef (I := I) G x t₀ w₂ j)
    (c₄ := fun j _ => c5_fixCoef (I := I) G x t₀ w₃ j)
    (fun j => reconCoef_continuousAt (I := I) (M := M) hJ hG ht₀ x
      (c5_smoothFieldAt_smoothExt x v) hA' j)
    (fun _ => continuousAt_const) (fun _ => continuousAt_const) (fun _ => continuousAt_const)
    (fun t => c5_lcOf_eq_sum_reconCoef (I := I) (G := G) x v hA' t)
    (fun _ => c5_eq_sum_fixCoef (I := I) G x t₀ w₁)
    (fun _ => c5_eq_sum_fixCoef (I := I) G x t₀ w₂)
    (fun _ => c5_eq_sum_fixCoef (I := I) G x t₀ w₃)

/-- The connection correction term with the moving vector in the **second** slot. -/
lemma c5_lcOf_rmP_slot2 {G : ℝ → SMet I M} {J : Set ℝ} (hLC : LCSmooth I M) (hJ : IsOpen J)
    (hG : JointSmooth G J) {t₀ : ℝ} (ht₀ : t₀ ∈ J) (x : M) (v : TangentSpace I x)
    {A : Π y : M, TangentSpace I y} (hA : Work.Diff.GE.SmoothField (I := I) (M := M) A)
    (w₀ w₂ w₃ : TangentSpace I x) :
    ContinuousAt (fun t : ℝ ↦ rmP (G t) x w₀ (lcOf (G t) A x v) w₂ w₃) t₀ := by
  have hA' : Work.Diff.EXT.SmoothFieldAt I M A x := hA.contMDiffAt (x := x)
  refine c5_rmP_of_eq_sum4 (I := I) (M := M) hLC hJ hG ht₀ x
    (W₁ := fun _ : ℝ => w₀) (W₂ := fun t => lcOf (G t) A x v) (W₃ := fun _ => w₂)
    (W₄ := fun _ => w₃)
    (c₁ := fun j _ => c5_fixCoef (I := I) G x t₀ w₀ j)
    (c₂ := fun j t => Work.Diff.EXT.reconCoef (I := I) G x (smoothExt x v) A j t x)
    (c₃ := fun j _ => c5_fixCoef (I := I) G x t₀ w₂ j)
    (c₄ := fun j _ => c5_fixCoef (I := I) G x t₀ w₃ j)
    (fun _ => continuousAt_const)
    (fun j => reconCoef_continuousAt (I := I) (M := M) hJ hG ht₀ x
      (c5_smoothFieldAt_smoothExt x v) hA' j)
    (fun _ => continuousAt_const) (fun _ => continuousAt_const)
    (fun _ => c5_eq_sum_fixCoef (I := I) G x t₀ w₀)
    (fun t => c5_lcOf_eq_sum_reconCoef (I := I) (G := G) x v hA' t)
    (fun _ => c5_eq_sum_fixCoef (I := I) G x t₀ w₂)
    (fun _ => c5_eq_sum_fixCoef (I := I) G x t₀ w₃)

/-- The connection correction term with the moving vector in the **third** slot. -/
lemma c5_lcOf_rmP_slot3 {G : ℝ → SMet I M} {J : Set ℝ} (hLC : LCSmooth I M) (hJ : IsOpen J)
    (hG : JointSmooth G J) {t₀ : ℝ} (ht₀ : t₀ ∈ J) (x : M) (v : TangentSpace I x)
    {A : Π y : M, TangentSpace I y} (hA : Work.Diff.GE.SmoothField (I := I) (M := M) A)
    (w₀ w₁ w₃ : TangentSpace I x) :
    ContinuousAt (fun t : ℝ ↦ rmP (G t) x w₀ w₁ (lcOf (G t) A x v) w₃) t₀ := by
  have hA' : Work.Diff.EXT.SmoothFieldAt I M A x := hA.contMDiffAt (x := x)
  refine c5_rmP_of_eq_sum4 (I := I) (M := M) hLC hJ hG ht₀ x
    (W₁ := fun _ : ℝ => w₀) (W₂ := fun _ => w₁) (W₃ := fun t => lcOf (G t) A x v)
    (W₄ := fun _ => w₃)
    (c₁ := fun j _ => c5_fixCoef (I := I) G x t₀ w₀ j)
    (c₂ := fun j _ => c5_fixCoef (I := I) G x t₀ w₁ j)
    (c₃ := fun j t => Work.Diff.EXT.reconCoef (I := I) G x (smoothExt x v) A j t x)
    (c₄ := fun j _ => c5_fixCoef (I := I) G x t₀ w₃ j)
    (fun _ => continuousAt_const) (fun _ => continuousAt_const)
    (fun j => reconCoef_continuousAt (I := I) (M := M) hJ hG ht₀ x
      (c5_smoothFieldAt_smoothExt x v) hA' j)
    (fun _ => continuousAt_const)
    (fun _ => c5_eq_sum_fixCoef (I := I) G x t₀ w₀)
    (fun _ => c5_eq_sum_fixCoef (I := I) G x t₀ w₁)
    (fun t => c5_lcOf_eq_sum_reconCoef (I := I) (G := G) x v hA' t)
    (fun _ => c5_eq_sum_fixCoef (I := I) G x t₀ w₃)

/-- The connection correction term with the moving vector in the **fourth** slot. -/
lemma c5_lcOf_rmP_slot4 {G : ℝ → SMet I M} {J : Set ℝ} (hLC : LCSmooth I M) (hJ : IsOpen J)
    (hG : JointSmooth G J) {t₀ : ℝ} (ht₀ : t₀ ∈ J) (x : M) (v : TangentSpace I x)
    {A : Π y : M, TangentSpace I y} (hA : Work.Diff.GE.SmoothField (I := I) (M := M) A)
    (w₀ w₁ w₂ : TangentSpace I x) :
    ContinuousAt (fun t : ℝ ↦ rmP (G t) x w₀ w₁ w₂ (lcOf (G t) A x v)) t₀ := by
  have hA' : Work.Diff.EXT.SmoothFieldAt I M A x := hA.contMDiffAt (x := x)
  refine c5_rmP_of_eq_sum4 (I := I) (M := M) hLC hJ hG ht₀ x
    (W₁ := fun _ : ℝ => w₀) (W₂ := fun _ => w₁) (W₃ := fun _ => w₂)
    (W₄ := fun t => lcOf (G t) A x v)
    (c₁ := fun j _ => c5_fixCoef (I := I) G x t₀ w₀ j)
    (c₂ := fun j _ => c5_fixCoef (I := I) G x t₀ w₁ j)
    (c₃ := fun j _ => c5_fixCoef (I := I) G x t₀ w₂ j)
    (c₄ := fun j t => Work.Diff.EXT.reconCoef (I := I) G x (smoothExt x v) A j t x)
    (fun _ => continuousAt_const) (fun _ => continuousAt_const) (fun _ => continuousAt_const)
    (fun j => reconCoef_continuousAt (I := I) (M := M) hJ hG ht₀ x
      (c5_smoothFieldAt_smoothExt x v) hA' j)
    (fun _ => c5_eq_sum_fixCoef (I := I) G x t₀ w₀)
    (fun _ => c5_eq_sum_fixCoef (I := I) G x t₀ w₁)
    (fun _ => c5_eq_sum_fixCoef (I := I) G x t₀ w₂)
    (fun t => c5_lcOf_eq_sum_reconCoef (I := I) (G := G) x v hA' t)

/-! ## Continuity of the five terms of `dRmPhi` -/

/-- **`dRmPhi` is continuous in the family parameter.** -/
lemma c5_dRmPhi_continuousAt {G : ℝ → SMet I M} {J : Set ℝ} (hLC : LCSmooth I M)
    (hJ : IsOpen J) (hG : JointSmooth G J) {t₀ : ℝ} (ht₀ : t₀ ∈ J) (x : M)
    (v : TangentSpace I x)
    {A B C D : Π y : M, TangentSpace I y}
    (hA : Work.Diff.GE.SmoothField (I := I) (M := M) A)
    (hB : Work.Diff.GE.SmoothField (I := I) (M := M) B)
    (hC : Work.Diff.GE.SmoothField (I := I) (M := M) C)
    (hD : Work.Diff.GE.SmoothField (I := I) (M := M) D) :
    ContinuousAt (fun t : ℝ ↦ dRmPhi (G t) x v A B C D) t₀ := by
  have h1 : ContinuousAt (fun t : ℝ ↦
      mvfderiv I (fun y : M ↦ rmP (G t) y (A y) (B y) (C y) (D y)) x v) t₀ :=
    Work.Diff.EXT.continuousAt_mvfderiv_family (I := I) (M := M) (F := ℝ)
      (Φ := fun p : ℝ × M ↦ rmP (G p.1) p.2 (A p.2) (B p.2) (C p.2) (D p.2))
      (t₀ := t₀) (x := x)
      (rmP_jointSmoothNoCompact (I := I) (M := M) hLC hJ hG ht₀ x hA hB hC hD) v
  have h2 := c5_lcOf_rmP_slot1 (I := I) (M := M) hLC hJ hG ht₀ x v hA (B x) (C x) (D x)
  have h3 := c5_lcOf_rmP_slot2 (I := I) (M := M) hLC hJ hG ht₀ x v hB (A x) (C x) (D x)
  have h4 := c5_lcOf_rmP_slot3 (I := I) (M := M) hLC hJ hG ht₀ x v hC (A x) (B x) (D x)
  have h5 := c5_lcOf_rmP_slot4 (I := I) (M := M) hLC hJ hG ht₀ x v hD (A x) (B x) (C x)
  have h := (((h1.sub h2).sub h3).sub h4).sub h5
  refine h.congr_of_eventuallyEq ?_
  filter_upwards with t
  simp only [dRmPhi, Pi.sub_apply]

/-! ## The target -/

theorem covRmC5_continuousAt
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ((⊤ : ENat) : WithTop ENat) M] [I.Boundaryless] [T2Space M]
    (hLC : Submission.Diff.LCSmooth I M)
    {G : ℝ → Submission.Diff.SMet I M} {J : Set ℝ} (hJ : IsOpen J)
    (hG : Submission.Diff.JointSmooth G J) {t₀ : ℝ} (ht₀ : t₀ ∈ J) (x : M)
    (m i j k l : Fin (Module.finrank ℝ E)) :
    ContinuousAt (fun t : ℝ ↦ Work.Diff.GE.covRmC5 (I := I) G x t x m i j k l) t₀ := by
  have hv := c5_dRmPhi_continuousAt (I := I) (M := M) hLC hJ hG ht₀ x
    (cFrame (I := I) x m x)
    (A := smoothExt x (cFrame (I := I) x i x))
    (B := smoothExt x (cFrame (I := I) x j x))
    (C := smoothExt x (cFrame (I := I) x k x))
    (D := smoothExt x (cFrame (I := I) x l x))
    (Work.Diff.GE.react.db.smoothExt_cmdiff x _) (Work.Diff.GE.react.db.smoothExt_cmdiff x _)
    (Work.Diff.GE.react.db.smoothExt_cmdiff x _) (Work.Diff.GE.react.db.smoothExt_cmdiff x _)
  have hkey : ∀ t : ℝ, Work.Diff.GE.covRmC5 (I := I) G x t x m i j k l
      = dRmPhi (G t) x (cFrame (I := I) x m x) (smoothExt x (cFrame (I := I) x i x))
          (smoothExt x (cFrame (I := I) x j x)) (smoothExt x (cFrame (I := I) x k x))
          (smoothExt x (cFrame (I := I) x l x)) := by
    intro t
    have h := Work.Diff.GE.Kato3.covRm_field_form (I := I) (M := M) hLC (G t) x
      (cFrame (I := I) x m x)
      (X₁ := smoothExt x (cFrame (I := I) x i x))
      (X₂ := smoothExt x (cFrame (I := I) x j x))
      (X₃ := smoothExt x (cFrame (I := I) x k x))
      (X₄ := smoothExt x (cFrame (I := I) x l x))
      (Work.Diff.GE.react.db.smoothExt_cmdiff x _) (Work.Diff.GE.react.db.smoothExt_cmdiff x _)
      (Work.Diff.GE.react.db.smoothExt_cmdiff x _) (Work.Diff.GE.react.db.smoothExt_cmdiff x _)
    simpa only [Work.Diff.GE.covRmC5, Work.Diff.GE.react.db.smoothExt_apply] using h
  rw [funext hkey]
  exact hv

end Work.Diff.GE
