import Mathlib
import Submission.Work.Diff.GE.NablaRm
import Submission.Work.Diff.GE.BoundaryPlans
import Submission.Work.Diff.GE.continuous_flow_quantities
import Submission.Work.Diff.EXT.lapCovKRm_one_eq_lapCovRmAt
import Submission.Work.Diff.GE.cov3Rm_ricci
import Submission.Work.Diff.EXT.covK_familySmooth
import Submission.Work.Diff.GE.frameMotion_cancel_cov2Rm
import Submission.Work.Diff.GE.lapRmAt_trace
import Submission.Work.Diff.GE.laplAt_eq_sum_invGram

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Continuity at the initial time of `ΔRm` along a Ricci flow

`Work.Diff.GE.lapRmAt g x a b c d = ∑_m ∇²Rm(g)(e_m,e_m,a,b,c,d)` is the rough Laplacian of the
curvature, the trace being taken over the `Classical.epsilon`-chosen orthonormal frame
`Submission.Diff.onFrame g x`, which is *not* continuous in the metric.  The file proves that, along
a Ricci flow `G` on `[0,T)`, the map `s ↦ lapRmAt (G s) x a b c d` is continuous from the right at
`0` (for fixed vectors `a b c d` at `x`).

**Route.**

1. *(algebra — `lapRmAt_eq_sum_invGram_aux`)* `ΔRm` is the trace of the `(0,6)`-tensor `∇²Rm` in the
   first two slots, so it may be computed in *any* basis `e` of `TₓM` by contracting with the
   inverse Gram matrix:
   `lapRmAt g x a b c d = ∑ i, ∑ j, (Γ⁻¹) i j * cov2Rm g x (e i) (e j) a b c d`.
   The form `β u w = cov2Rm g x u w a b c d` is bilinear but not symmetric; symmetrising it and
   using the linear-algebra result `sum_invGram_mul_eq_sum_orthonormal` (from
   `laplAt_eq_sum_invGram.lean`) together with the symmetry of `Γ⁻¹` gives the identity.
2. *(algebra — `cov2Rm_eq_covKRmExt_two`)* The frozen `(0,6)`-tensor `∇²Rm` is level `2` of the
   `EXT` tower: `cov2Rm g x (V0 x) (V1 x) (A x) … = covKRmExt g 2 (if · = 0 then V0 else V1) A … x`
   for globally smooth fields.  Proof: unfold both the tower recursion at `2` (whose successor step
   is `mvfderiv` of the level-`1` tower minus the five `lcOf` corrections) and `cov2RmExt`, and
   identify each level-`1` tower value with `covRm` by the proved level-`1` bridge
   `Work.Diff.EXT.covKRmExt_one_eq_covRm`.
3. *(analysis — `cov2Rm_continuousAt_aux`)* For a metric family jointly smooth on an open `J ∋ t₀`,
   each fixed-vector component `t ↦ cov2Rm (G t) x v w a b c d` is continuous at `t₀`: by 2 it is the
   slice of the jointly `C^∞` tower family (`Work.Diff.EXT.covK_familySmooth`, with the constant
   families of the globally smooth fields `smoothExt x ·`).
4. *(assembly)* Use the coordinate frame `cFrame x ·` of the chart at `x` — a basis of `TₓM` at `x`
   (`cfq_cFrame_span`) whose Gram matrix `GramM` is an explicit smooth function of the metric.  Each
   summand `τ ↦ (GramM …)⁻¹ i j * cov2Rm (G τ) x (cFrame x i x) (cFrame x j x) a b c d` of the right
   hand side of 1 is then continuous at `0` (inverse Gram matrix by `gramInv_jointSmooth`, the
   `cov2Rm` components by 3), and a finite sum of continuous functions is continuous.
5. Finally, the time reparametrisation `t = τ²` (jointly smooth on an *open* interval
   `Ioo (-ρ) ρ`, `cfq_jointSmooth_sqFlow`) transfers the statement from the open interval back to
   `ContinuousWithinAt … (Ico 0 T) 0` (`cfq_continuousWithinAt_of_continuousAt_comp_sq`).

The `CompactSpace` hypothesis of the frozen statement is not used: everything is local in `x`.
-/

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1600000

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology Matrix
open Bundle ContDiff Set VectorField CovariantDerivative Metric

namespace Work.Diff.GE

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ((⊤ : ℕ∞) : WithTop ℕ∞) M] [I.Boundaryless] [T2Space M]

/-! ## Step 2: the level-`2` bridge between `∇²Rm` and the `EXT` tower -/

/-- **Level `2` of the `EXT` tower is `∇²Rm`.**  For globally `C^∞` tangent fields
`V0, V1, A, B, C, D`, the tower value `covKRmExt g 2 V A B C D` at `x` (with the differentiation
slots `V = (V0, V1)`) equals the frozen `(0,6)`-tensor `cov2Rm` contracted with the values of the
fields:
`cov2Rm g x (V0 x) (V1 x) (A x) (B x) (C x) (D x)
   = covKRmExt g 2 (fun r : Fin 2 => if r = 0 then V0 else V1) A B C D x`.

Proof: `cov2RmExt` (whose value on smooth fields is `cov2Rm` on the values,
`Work.Diff.GE.cov2RmExt_eq_cov2Rm`) is exactly the `k = 2` unfolding of the recursive tower
definition: one `mvfderiv` of the level-`1` tower followed by the five `lcOf`-corrections.  The
level-`1` tower values are identified with `covRm` by
`Work.Diff.EXT.covKRmExt_one_eq_covRm`, and the correction fields `lcOf g X (V0)` are globally
smooth by `contMDiff_cov_apply`. -/
theorem cov2Rm_eq_covKRmExt_two
    (hLC : LCSmooth I M) (g : SMet I M) (x : M)
    {V0 V1 A B C D : Π y : M, TangentSpace I y}
    (hV0 : CMDiff ∞ (T% V0)) (hV1 : CMDiff ∞ (T% V1))
    (hA : CMDiff ∞ (T% A)) (hB : CMDiff ∞ (T% B))
    (hC : CMDiff ∞ (T% C)) (hD : CMDiff ∞ (T% D)) :
    cov2Rm g x (V0 x) (V1 x) (A x) (B x) (C x) (D x)
      = EXT.covKRmExt g 2 (fun r : Fin 2 => if r = 0 then V0 else V1) A B C D x := by
  rw [← cov2RmExt_eq_cov2Rm hLC g x (V0 x) hV1 hA hB hC hD]
  simp only [cov2RmExt]
  rw [show EXT.covKRmExt g 2 (fun r : Fin 2 => if r = 0 then V0 else V1) A B C D x
      = (mvfderiv I (EXT.covKRmExt g 1 (fun _ : Fin 1 => V1) A B C D) x (V0 x)
        - (∑ i : Fin 1, EXT.covKRmExt g 1 (Function.update (fun _ : Fin 1 => V1) i
            (fun y => lcOf g V1 y (V0 y))) A B C D x)
        - EXT.covKRmExt g 1 (fun _ : Fin 1 => V1) (fun y => lcOf g A y (V0 y)) B C D x
        - EXT.covKRmExt g 1 (fun _ : Fin 1 => V1) A (fun y => lcOf g B y (V0 y)) C D x
        - EXT.covKRmExt g 1 (fun _ : Fin 1 => V1) A B (fun y => lcOf g C y (V0 y)) D x
        - EXT.covKRmExt g 1 (fun _ : Fin 1 => V1) A B C (fun y => lcOf g D y (V0 y)) x)
      from rfl]
  have hfun : EXT.covKRmExt g 1 (fun _ : Fin 1 => V1) A B C D
      = fun y : M => covRm g y (V1 y) (A y) (B y) (C y) (D y) := by
    funext y
    exact EXT.covKRmExt_one_eq_covRm hLC g y hV1 hA hB hC hD
  rw [hfun]
  have hcov : ContMDiffCovariantDerivative (lcOf g) ∞ := (hLC g).1.some
  have hcV : CMDiff ∞ (T% (fun y : M => lcOf g V1 y (V0 y))) :=
    Commons.Geometry.Manifold.VectorBundle.CovariantDerivative.contMDiff_cov_apply
      (lcOf g) hcov hV1 hV0
  have hcA : CMDiff ∞ (T% (fun y : M => lcOf g A y (V0 y))) :=
    Commons.Geometry.Manifold.VectorBundle.CovariantDerivative.contMDiff_cov_apply
      (lcOf g) hcov hA hV0
  have hcB : CMDiff ∞ (T% (fun y : M => lcOf g B y (V0 y))) :=
    Commons.Geometry.Manifold.VectorBundle.CovariantDerivative.contMDiff_cov_apply
      (lcOf g) hcov hB hV0
  have hcC : CMDiff ∞ (T% (fun y : M => lcOf g C y (V0 y))) :=
    Commons.Geometry.Manifold.VectorBundle.CovariantDerivative.contMDiff_cov_apply
      (lcOf g) hcov hC hV0
  have hcD : CMDiff ∞ (T% (fun y : M => lcOf g D y (V0 y))) :=
    Commons.Geometry.Manifold.VectorBundle.CovariantDerivative.contMDiff_cov_apply
      (lcOf g) hcov hD hV0
  rw [Fin.sum_univ_one]
  rw [show (Function.update (fun _ : Fin 1 => V1) (0 : Fin 1) (fun y => lcOf g V1 y (V0 y)))
      = (fun _ : Fin 1 => fun y : M => lcOf g V1 y (V0 y)) from by
    funext i
    fin_cases i
    · simp]
  rw [EXT.covKRmExt_one_eq_covRm hLC g x hcV hA hB hC hD]
  rw [EXT.covKRmExt_one_eq_covRm hLC g x hV1 hcA hB hC hD]
  rw [EXT.covKRmExt_one_eq_covRm hLC g x hV1 hA hcB hC hD]
  rw [EXT.covKRmExt_one_eq_covRm hLC g x hV1 hA hB hcC hD]
  rw [EXT.covKRmExt_one_eq_covRm hLC g x hV1 hA hB hC hcD]

/-! ## Step 1: the trace of `∇²Rm` in an arbitrary basis -/

/-- **`ΔRm` in an arbitrary basis.**  For a basis `e` of `TₓM` (spanning, with `finrank ℝ E`
elements) with Gram matrix `Γᵢⱼ = g.inner x (e i) (e j)`,

`lapRmAt g x a b c d = ∑ i, ∑ j, (Γ⁻¹) i j * cov2Rm g x (e i) (e j) a b c d`.

This is the `lapRmAt` analogue of `Work.Diff.GE.laplAt_eq_sum_invGram`.  The form
`β u w = cov2Rm g x u w a b c d` is `ℝ`-bilinear but not symmetric in the two differentiation slots,
so one symmetrises it: with `S u w = (β u w + β w u)/2` the abstract trace lemma
`Work.Diff.GE.sum_invGram_mul_eq_sum_orthonormal` applies, and replacing `S` by `β` uses only that
`Γ⁻¹` is symmetric (as `Γ` is the Gram matrix of a basis). -/
theorem lapRmAt_eq_sum_invGram_aux
    (hLC : LCSmooth I M)
    (g : SMet I M) (x : M) (a b c d : TangentSpace I x)
    (e : Fin (Module.finrank ℝ E) → TangentSpace I x)
    (Γ : Matrix (Fin (Module.finrank ℝ E)) (Fin (Module.finrank ℝ E)) ℝ)
    (hΓ : ∀ i j, Γ i j = g.inner x (e i) (e j))
    (hb : Submodule.span ℝ (Set.range e) = ⊤) :
    lapRmAt g x a b c d
      = ∑ i, ∑ j, (Γ⁻¹) i j * cov2Rm g x (e i) (e j) a b c d := by
  classical
  letI : RiemannianBundle (fun z : M ↦ TangentSpace I z) := ⟨g.toRiemannianMetric⟩
  haveI : IsContMDiffRiemannianBundle I ∞ E (fun z : M ↦ TangentSpace I z) := inferInstance
  -- the `Classical.epsilon` frame is orthonormal for the instance inner product
  have hON : Orthonormal ℝ (Submission.Diff.onFrame g x) := by
    rw [orthonormal_iff_ite]
    intro i j
    rw [show Inner.inner ℝ (Submission.Diff.onFrame g x i) (Submission.Diff.onFrame g x j)
        = g.inner x (Submission.Diff.onFrame g x i) (Submission.Diff.onFrame g x j) from rfl]
    exact isONFrame_onFrame (I := I) g x i j
  -- the bilinear form `β` and its symmetrisation `S`
  set β : TangentSpace I x → TangentSpace I x → ℝ :=
    fun u w => cov2Rm g x u w a b c d with hβ
  set S : TangentSpace I x → TangentSpace I x → ℝ := fun u w => (β u w + β w u) / 2 with hS
  have hSadd : ∀ u₁ u₂ w : TangentSpace I x, S (u₁ + u₂) w = S u₁ w + S u₂ w := by
    intro u₁ u₂ w
    simp only [hS, hβ]
    rw [cov2Rm_add_fst (I := I) (M := M) hLC g x u₁ u₂ w a b c d,
      cov2Rm_add_snd (I := I) (M := M) hLC g x w u₁ u₂ a b c d]
    ring
  have hSsmul : ∀ (r : ℝ) (u w : TangentSpace I x), S (r • u) w = r * S u w := by
    intro r u w
    simp only [hS, hβ]
    rw [cov2Rm_smul_fst (I := I) (M := M) hLC g x r u w a b c d,
      cov2Rm_smul_snd (I := I) (M := M) hLC g x r w u a b c d]
    ring
  have hSsym : ∀ u w : TangentSpace I x, S u w = S w u := by
    intro u w
    simp only [hS]
    ring
  have htrace := sum_invGram_mul_eq_sum_orthonormal (V := TangentSpace I x) S hSadd hSsmul hSsym
    e (Submission.Diff.onFrame g x) hb hON Γ (fun i j => by rw [hΓ i j]; rfl)
  -- the diagonal of `S` is the diagonal of `β`
  have hdiag : ∀ u : TangentSpace I x, S u u = β u u := by
    intro u
    simp only [hS]
    ring
  have h1 : (∑ i, S (Submission.Diff.onFrame g x i) (Submission.Diff.onFrame g x i))
      = ∑ i, β (Submission.Diff.onFrame g x i) (Submission.Diff.onFrame g x i) :=
    Finset.sum_congr rfl (fun i _ => hdiag _)
  have h2 : (∑ i, β (Submission.Diff.onFrame g x i) (Submission.Diff.onFrame g x i))
      = lapRmAt g x a b c d := by
    simp only [hβ, lapRmAt]
  -- `Γ` is symmetric, hence so is `Γ⁻¹`
  have hGsym : Γ.IsSymm := by
    refine Matrix.IsSymm.ext (fun i j => ?_)
    rw [hΓ j i, hΓ i j]
    exact (real_inner_comm (e j) (e i)).symm
  have hinvij : ∀ i j : Fin (Module.finrank ℝ E), (Γ⁻¹) i j = (Γ⁻¹) j i :=
    fun i j => (Matrix.IsSymm.apply hGsym.inv i j).symm
  -- replacing the symmetrisation `S` by `β` in the double sum
  have hswap : (∑ i, ∑ j, (Γ⁻¹) i j * β (e j) (e i))
      = ∑ i, ∑ j, (Γ⁻¹) i j * β (e i) (e j) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [hinvij j i]
  have hSsum : (∑ i, ∑ j, (Γ⁻¹) i j * S (e i) (e j))
      = ∑ i, ∑ j, (Γ⁻¹) i j * β (e i) (e j) := by
    have htwo : 2 * (∑ i, ∑ j, (Γ⁻¹) i j * S (e i) (e j))
        = ∑ i, ∑ j, ((Γ⁻¹) i j * β (e i) (e j) + (Γ⁻¹) i j * β (e j) (e i)) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      simp only [hS]
      ring
    have hmain : 2 * (∑ i, ∑ j, (Γ⁻¹) i j * S (e i) (e j))
        = 2 * (∑ i, ∑ j, (Γ⁻¹) i j * β (e i) (e j)) := by
      rw [htwo]
      simp only [Finset.sum_add_distrib]
      rw [hswap]
      ring
    exact mul_left_cancel₀ (by norm_num : (2 : ℝ) ≠ 0) hmain
  calc lapRmAt g x a b c d
      = ∑ i, S (Submission.Diff.onFrame g x i) (Submission.Diff.onFrame g x i) :=
        (h1.trans h2).symm
    _ = ∑ i, ∑ j, (Γ⁻¹) i j * S (e i) (e j) := htrace.symm
    _ = ∑ i, ∑ j, (Γ⁻¹) i j * cov2Rm g x (e i) (e j) a b c d := by
        rw [hSsum]

/-! ## Step 3: continuity in the flow parameter of a fixed-vector component of `∇²Rm` -/

/-- **Continuity in the flow parameter of a fixed-vector component of `∇²Rm`.**  For a metric
family `G` jointly smooth on an open time set `J ∋ t₀` and fixed vectors `v w a b c d` of `TₓM`,
the map `t ↦ cov2Rm (G t) x v w a b c d` is continuous at `t₀`.

Route: by `cov2Rm_eq_covKRmExt_two`, the component is the slice of the `EXT` tower at level `2`,
whose joint smoothness on the open set `J ×ˢ univ` is `Work.Diff.EXT.covK_familySmooth` (the
constant families of the globally smooth fields `smoothExt x ·` are `JointField` by
`Work.Diff.EXT.jointField_const`); restrict to the slice `y = x` and compose with `t ↦ (t,x)`. -/
theorem cov2Rm_continuousAt_aux
    (hLC : LCSmooth I M)
    {G : ℝ → SMet I M} {J : Set ℝ} (hJ : IsOpen J)
    (hG : JointSmooth G J) {t₀ : ℝ} (ht₀ : t₀ ∈ J) (x : M)
    (v w a b c d : TangentSpace I x) :
    ContinuousAt (fun t : ℝ ↦ cov2Rm (G t) x v w a b c d) t₀ := by
  classical
  have hVopen : IsOpen (J ×ˢ (univ : Set M)) := hJ.prod isOpen_univ
  have hGmet : EXT.JointMet G (J ×ˢ (univ : Set M)) := hG
  have hfield : ∀ X : EXT.TField (I := I) (M := M), EXT.SmoothTField X →
      EXT.JointField (fun _ : ℝ => X) (J ×ˢ (univ : Set M)) := fun X hX =>
    (EXT.jointField_const (I := I) (M := M) hX).mono (Set.subset_univ _)
  -- joint smoothness of the tower at `(t₀, x)`
  have htower : ContMDiffAt ((𝓘(ℝ, ℝ)).prod I) (𝓘(ℝ, ℝ)) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun p : ℝ × M => EXT.covKRmExt (G p.1) 2
        (fun r : Fin 2 => if r = 0 then smoothExt x v else smoothExt x w)
        (smoothExt x a) (smoothExt x b) (smoothExt x c) (smoothExt x d) p.2) (t₀, x) := by
    have hVf : ∀ r : Fin 2, EXT.JointField
        (fun _ : ℝ => (fun r : Fin 2 => if r = 0 then smoothExt x v else smoothExt x w) r)
        (J ×ˢ (univ : Set M)) := by
      intro r
      fin_cases r
      · simpa using hfield (smoothExt x v) (smoothExt_cmdiff x v)
      · simpa using hfield (smoothExt x w) (smoothExt_cmdiff x w)
    exact (EXT.covK_familySmooth (I := I) (M := M) hLC hVopen hGmet 2 hVf
      (A := fun _ : ℝ => smoothExt x a) (B := fun _ : ℝ => smoothExt x b)
      (C := fun _ : ℝ => smoothExt x c) (D := fun _ : ℝ => smoothExt x d)
      (hfield _ (smoothExt_cmdiff x a)) (hfield _ (smoothExt_cmdiff x b))
      (hfield _ (smoothExt_cmdiff x c)) (hfield _ (smoothExt_cmdiff x d))).contMDiffAt
      (hVopen.mem_nhds ⟨ht₀, mem_univ x⟩)
  -- the two vocabularies agree
  have hkey : ∀ t : ℝ, cov2Rm (G t) x v w a b c d
      = EXT.covKRmExt (G t) 2
        (fun r : Fin 2 => if r = 0 then smoothExt x v else smoothExt x w)
        (smoothExt x a) (smoothExt x b) (smoothExt x c) (smoothExt x d) x :=
    fun t => by
      simpa only [smoothExt_apply] using
        cov2Rm_eq_covKRmExt_two (I := I) (M := M) (hLC := hLC) (g := G t) (x := x)
          (V0 := smoothExt x v) (V1 := smoothExt x w) (A := smoothExt x a) (B := smoothExt x b)
          (C := smoothExt x c) (D := smoothExt x d)
          (smoothExt_cmdiff x v) (smoothExt_cmdiff x w) (smoothExt_cmdiff x a)
          (smoothExt_cmdiff x b) (smoothExt_cmdiff x c) (smoothExt_cmdiff x d)
  have hcomp : ContinuousAt (fun t : ℝ => EXT.covKRmExt (G t) 2
        (fun r : Fin 2 => if r = 0 then smoothExt x v else smoothExt x w)
        (smoothExt x a) (smoothExt x b) (smoothExt x c) (smoothExt x d) x) t₀ := by
    have h2 : ContinuousAt (fun t : ℝ => (t, x)) t₀ := continuousAt_id.prodMk continuousAt_const
    have h3 := htower.continuousAt.comp (f := fun t : ℝ => (t, x)) h2
    simpa only [Function.comp_def] using h3
  exact hcomp.congr_of_eventuallyEq (Filter.Eventually.of_forall hkey)

/-! ## The target -/

theorem lapRmAt_zero_continuous
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : WithTop ℕ∞) M]
    [I.Boundaryless] [T2Space M] [CompactSpace M]
    (hLC : Submission.Diff.LCSmooth I M) :
    ∀ (G : ℝ → Submission.Diff.SMet I M) (T : ℝ), Submission.Diff.IsRicciFlow G T →
      ∀ x : M, ∀ a b c d : TangentSpace I x,
        ContinuousWithinAt (fun s : ℝ ↦ Work.Diff.GE.lapRmAt (G s) x a b c d)
          (Set.Ico 0 T) 0 := by
  intro G T hflow x a b c d
  by_cases hT : T ≤ 0
  · rw [Set.Ico_eq_empty_iff.mpr (not_lt.mpr hT)]
    simp [ContinuousWithinAt, nhdsWithin_empty]
  · have hTpos : 0 < T := not_le.mp hT
    set ρ : ℝ := Real.sqrt T / 2 with hρdef
    have hρ : 0 < ρ := by positivity
    have hρT : ρ ^ 2 < T := by
      rw [hρdef, div_pow, Real.sq_sqrt (le_of_lt hTpos)]
      nlinarith
    have hsq : JointSmooth (cfq_sqFlow G) (Set.Ioo (-ρ) ρ) :=
      cfq_jointSmooth_sqFlow (I := I) (M := M) G hTpos hρ hρT hflow.1
    have h0 : (0 : ℝ) ∈ Set.Ioo (-ρ) ρ := ⟨by linarith, hρ⟩
    -- continuity of the reparametrised family at `0`
    have hcont : ContinuousAt (fun τ : ℝ ↦ lapRmAt (cfq_sqFlow G τ) x a b c d) 0 := by
      classical
      letI : RiemannianBundle (fun z : M ↦ TangentSpace I z) :=
        ⟨(cfq_sqFlow G 0).toRiemannianMetric⟩
      haveI : IsContMDiffRiemannianBundle I ∞ E (fun z : M ↦ TangentSpace I z) := inferInstance
      -- the trace identity in the chart frame
      have hid : ∀ τ : ℝ, lapRmAt (cfq_sqFlow G τ) x a b c d
          = ∑ i, ∑ j, (GramInv (I := I) (cfq_sqFlow G) x τ x) i j *
              cov2Rm (cfq_sqFlow G τ) x (cFrame (I := I) x i x) (cFrame (I := I) x j x)
                a b c d := by
        intro τ
        have h := lapRmAt_eq_sum_invGram_aux (I := I) (M := M) hLC (cfq_sqFlow G τ) x a b c d
          (fun i => cFrame (I := I) x i x) (GramM (I := I) (cfq_sqFlow G) x τ x)
          (fun i j => rfl)
          (cfq_cFrame_span (I := I) x (mem_chart_source H x))
        simpa only [GramInv] using h
      -- each summand is continuous at `0`
      have hterm : ∀ i j : Fin (Module.finrank ℝ E),
          ContinuousAt (fun τ : ℝ ↦ (GramInv (I := I) (cfq_sqFlow G) x τ x) i j *
              cov2Rm (cfq_sqFlow G τ) x (cFrame (I := I) x i x) (cFrame (I := I) x j x)
                a b c d) 0 := by
        intro i j
        have hg : ContinuousAt (fun τ : ℝ ↦ (GramInv (I := I) (cfq_sqFlow G) x τ x) i j) 0 :=
          cfq_continuousAt_of_jointSmoothAt (I := I) (M := M)
            (gramInv_jointSmooth (I := I) (M := M) (G := cfq_sqFlow G) isOpen_Ioo hsq h0 x i j)
        have hc : ContinuousAt (fun τ : ℝ ↦
            cov2Rm (cfq_sqFlow G τ) x (cFrame (I := I) x i x) (cFrame (I := I) x j x)
              a b c d) 0 :=
          cov2Rm_continuousAt_aux (I := I) (M := M) hLC isOpen_Ioo hsq h0 x
            (cFrame (I := I) x i x) (cFrame (I := I) x j x) a b c d
        exact hg.mul hc
      have hsum : ContinuousAt (fun τ : ℝ ↦ ∑ i, ∑ j,
          (GramInv (I := I) (cfq_sqFlow G) x τ x) i j *
              cov2Rm (cfq_sqFlow G τ) x (cFrame (I := I) x i x) (cFrame (I := I) x j x)
                a b c d) 0 := by
        refine cfq_continuousAt_finsetSum Finset.univ (fun i _ => ?_)
        refine cfq_continuousAt_finsetSum Finset.univ (fun j _ => ?_)
        exact hterm i j
      exact hsum.congr_of_eventuallyEq (Filter.Eventually.of_forall fun τ => hid τ)
    refine cfq_continuousWithinAt_of_continuousAt_comp_sq hTpos hcont ?_
    intro s hs
    show lapRmAt (G s) x a b c d = lapRmAt (cfq_sqFlow G (Real.sqrt s)) x a b c d
    rw [show cfq_sqFlow G (Real.sqrt s) = G s from by
      rw [cfq_sqFlow, Real.sq_sqrt hs.1]]

end Work.Diff.GE
