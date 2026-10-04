import Mathlib
import Submission.Work.Diff.GE.deps
import Submission.Work.Diff.GE.smp_aux
import Submission.Work.Diff.T.mvfderiv_frameVector_real

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.GE

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology
open Bundle ContDiff Set VectorField CovariantDerivative Metric

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M] [IsManifold I ∞ M]

set_option linter.unusedSectionVars false

/-- A neighbourhood of `x` intersected with `t` is a neighbourhood of `x` within `t`. -/
lemma inter_mem_nhdsWithin_of_mem_nhds {α : Type*} [TopologicalSpace α] {s t : Set α} {x : α}
    (h : s ∈ 𝓝 x) : s ∩ t ∈ 𝓝[t] x :=
  mem_nhdsWithin_iff_exists_mem_nhds_inter.mpr ⟨s, h, fun _ hy => hy⟩

/-- **Chart coordinates of a smooth vector field.**  If `X` is a `C^∞` vector field, then its
coordinates in the trivialisation of the tangent bundle at `x₀` are `C^∞` on the chart at `x₀`. -/
theorem coe_smooth
    (x₀ : M) {X : Π y : M, TangentSpace I y} (hX : CMDiff ∞ (T% X)) :
    ContMDiffOn I 𝓘(ℝ,E) ∞
      (fun y : M ↦ (trivializationAt E (TangentSpace I) x₀).continuousLinearMapAt ℝ y (X y))
      (extChartAt I x₀).source := by
  rw [extChartAt_source]
  intro y hy
  have hyb : y ∈ (trivializationAt E (TangentSpace I) x₀).baseSet := by
    rwa [TangentBundle.trivializationAt_baseSet]
  have h1 : ContMDiffWithinAt I 𝓘(ℝ,E) ∞
      (fun z : M ↦ ((trivializationAt E (TangentSpace I) x₀) ⟨z, X z⟩).2)
      (chartAt H x₀).source y :=
    (Trivialization.contMDiffWithinAt_section (e := trivializationAt E (TangentSpace I) x₀)
      (s := X) (chartAt H x₀).source hyb).mp (hX y).contMDiffWithinAt
  refine h1.congr (fun z hz => ?_) ?_
  · have hzb : z ∈ (trivializationAt E (TangentSpace I) x₀).baseSet := by
      rwa [TangentBundle.trivializationAt_baseSet]
    have h1' : (Trivialization.continuousLinearMapAt ℝ
        (trivializationAt E (TangentSpace I) x₀) z) (X z)
        = (Trivialization.linearMapAt ℝ
          (trivializationAt E (TangentSpace I) x₀) z) (X z) :=
      congrFun (Trivialization.continuousLinearMapAt_apply ℝ
        (trivializationAt E (TangentSpace I) x₀) z) (X z)
    have h2' : (Trivialization.linearMapAt ℝ
        (trivializationAt E (TangentSpace I) x₀) z) (X z)
        = ((trivializationAt E (TangentSpace I) x₀) ⟨z, X z⟩).2 :=
      congrFun (Trivialization.coe_linearMapAt_of_mem
        (trivializationAt E (TangentSpace I) x₀) hzb) (X z)
    exact h1'.trans h2'
  · have h1' : (Trivialization.continuousLinearMapAt ℝ
        (trivializationAt E (TangentSpace I) x₀) y) (X y)
        = (Trivialization.linearMapAt ℝ
          (trivializationAt E (TangentSpace I) x₀) y) (X y) :=
      congrFun (Trivialization.continuousLinearMapAt_apply ℝ
        (trivializationAt E (TangentSpace I) x₀) y) (X y)
    have h2' : (Trivialization.linearMapAt ℝ
        (trivializationAt E (TangentSpace I) x₀) y) (X y)
        = ((trivializationAt E (TangentSpace I) x₀) ⟨y, X y⟩).2 :=
      congrFun (Trivialization.coe_linearMapAt_of_mem
        (trivializationAt E (TangentSpace I) x₀) hyb) (X y)
    exact h1'.trans h2'

/-- **`mvfderiv` in the chart at `x₀`.**  For `g : M → ℝ` differentiable at `y` in the chart at
`x₀`, the manifold derivative of `g` at `y` in the direction `v` is the ordinary Fréchet
derivative of the chart reading of `g`, applied to the coordinates of `v`. -/
theorem mvfderiv_chart
    [I.Boundaryless]
    (x₀ : M) {y : M} (hy : y ∈ (chartAt H x₀).source) {g : M → ℝ}
    (hg : MDifferentiableAt I 𝓘(ℝ,ℝ) g y) (v : TangentSpace I y) :
    mvfderiv I g y v
      = fderiv ℝ (fun z : E ↦ g ((extChartAt I x₀).symm z)) ((extChartAt I x₀) y)
          ((trivializationAt E (TangentSpace I) x₀).continuousLinearMapAt ℝ y v) := by
  have hyb : y ∈ (trivializationAt E (TangentSpace I) x₀).baseSet := by
    rwa [TangentBundle.trivializationAt_baseSet]
  have hv : Submission.Geodesic.frameVector (I := I) x₀ y
      ((trivializationAt E (TangentSpace I) x₀).continuousLinearMapAt ℝ y v) = v := by
    rw [Submission.Geodesic.frameVector]
    exact Trivialization.symmL_continuousLinearMapAt
      (trivializationAt E (TangentSpace I) x₀) hyb v
  have h := Work.Diff.T.mvfderiv_frameVector_real (I := I) (x₀ := x₀) hy hg
    ((trivializationAt E (TangentSpace I) x₀).continuousLinearMapAt ℝ y v)
  rw [hv] at h
  exact h

/-- **The `z`-partial derivative of a jointly smooth function is jointly smooth.**  This is the
model-space core: the map `q ↦ fderiv ℝ (fun z ↦ h (q.1, z)) q.2 (c q)` is `C^∞` within
`[0,T) × Ω` whenever `h` and `c` are. -/
theorem partial_fderiv_smooth
    {h : ℝ × E → ℝ} {c : ℝ × E → E} {Ω : Set E} {T t₀ : ℝ} {z₀ : E}
    (hΩ : IsOpen Ω) (hz₀ : z₀ ∈ Ω) (ht₀ : t₀ ∈ Ico 0 T)
    (hh : ContMDiffWithinAt ((𝓘(ℝ,ℝ)).prod (𝓘(ℝ,E))) 𝓘(ℝ,ℝ) ∞ h (Ico 0 T ×ˢ Ω) (t₀, z₀))
    (hc : ContMDiffWithinAt ((𝓘(ℝ,ℝ)).prod (𝓘(ℝ,E))) (𝓘(ℝ,E)) ∞ c (Ico 0 T ×ˢ Ω) (t₀, z₀)) :
    ContMDiffWithinAt ((𝓘(ℝ,ℝ)).prod (𝓘(ℝ,E))) 𝓘(ℝ,ℝ) ∞
      (fun q : ℝ × E ↦ fderiv ℝ (fun z : E ↦ h (q.1, z)) q.2 (c q))
      (Ico 0 T ×ˢ Ω) (t₀, z₀) := by
  -- joint smoothness of the uncurried function on the product set
  have hf : ContMDiffWithinAt (((𝓘(ℝ,ℝ)).prod (𝓘(ℝ,E))).prod (𝓘(ℝ,E))) 𝓘(ℝ,ℝ) ∞
      (fun p : (ℝ × E) × E ↦ h (p.1.1, p.2)) ((Ico 0 T ×ˢ Ω) ×ˢ Ω) ((t₀, z₀), z₀) := by
    have hproj : ContMDiffWithinAt (((𝓘(ℝ,ℝ)).prod (𝓘(ℝ,E))).prod (𝓘(ℝ,E)))
        ((𝓘(ℝ,ℝ)).prod (𝓘(ℝ,E))) ∞ (fun p : (ℝ × E) × E ↦ (p.1.1, p.2))
        ((Ico 0 T ×ˢ Ω) ×ˢ Ω) ((t₀, z₀), z₀) := by
      have h1 : ContMDiffWithinAt (((𝓘(ℝ,ℝ)).prod (𝓘(ℝ,E))).prod (𝓘(ℝ,E))) (𝓘(ℝ,ℝ)) ∞
          (fun p : (ℝ × E) × E ↦ p.1.1) ((Ico 0 T ×ˢ Ω) ×ˢ Ω) ((t₀, z₀), z₀) :=
        (contMDiffWithinAt_id.fst).fst
      exact h1.prodMk contMDiffWithinAt_snd
    have hmaps : MapsTo (fun p : (ℝ × E) × E ↦ (p.1.1, p.2))
        ((Ico 0 T ×ˢ Ω) ×ˢ Ω) (Ico 0 T ×ˢ Ω) := fun p hp => ⟨hp.1.1, hp.2⟩
    exact hh.comp ((t₀, z₀), z₀) hproj hmaps
  have hsnd : ContMDiffWithinAt ((𝓘(ℝ,ℝ)).prod (𝓘(ℝ,E))) (𝓘(ℝ,E)) ∞
      (fun q : ℝ × E ↦ q.2) (Ico 0 T ×ˢ Ω) (t₀, z₀) := contMDiffWithinAt_snd
  have huniq : UniqueMDiffOn (𝓘(ℝ,E)) Ω := uniqueMDiffOn_iff_uniqueDiffOn.mpr hΩ.uniqueDiffOn
  -- the derivative as a CLM-valued function, and its application to `c`
  have hclm : ContMDiffWithinAt ((𝓘(ℝ,ℝ)).prod (𝓘(ℝ,E))) (𝓘(ℝ, E →L[ℝ] ℝ)) ∞
      (inTangentCoordinates (𝓘(ℝ,E)) (𝓘(ℝ,ℝ)) (fun q : ℝ × E ↦ q.2)
        (fun q : ℝ × E ↦ h (q.1, q.2))
        (fun q : ℝ × E ↦ mfderivWithin (𝓘(ℝ,E)) (𝓘(ℝ,ℝ)) (fun z : E ↦ h (q.1, z)) Ω q.2)
        (t₀, z₀)) (Ico 0 T ×ˢ Ω) (t₀, z₀) :=
    ContMDiffWithinAt.mfderivWithin (𝕜 := ℝ) (E := E) (H := E) (M := E) (I := 𝓘(ℝ,E))
      (E' := ℝ) (H' := ℝ) (M' := ℝ) (I' := 𝓘(ℝ,ℝ))
      (f := fun (q : ℝ × E) (z : E) ↦ h (q.1, z)) (g := fun q : ℝ × E ↦ q.2)
      (t := Ico 0 T ×ˢ Ω) (u := Ω) (x₀ := (t₀, z₀)) (m := ∞) (n := ∞)
      hf hsnd ⟨ht₀, hz₀⟩ (fun q hq => hq.2) le_rfl huniq
  have h3 := hclm.clm_apply hc
  have hmodel : inTangentCoordinates (𝓘(ℝ,E)) (𝓘(ℝ,ℝ)) (fun q : ℝ × E ↦ q.2)
        (fun q : ℝ × E ↦ h (q.1, q.2))
        (fun q : ℝ × E ↦ mfderivWithin (𝓘(ℝ,E)) (𝓘(ℝ,ℝ)) (fun z : E ↦ h (q.1, z)) Ω q.2)
        (t₀, z₀)
      = fun q : ℝ × E ↦
          mfderivWithin (𝓘(ℝ,E)) (𝓘(ℝ,ℝ)) (fun z : E ↦ h (q.1, z)) Ω q.2 :=
    inTangentCoordinates_model_space _ _ _ _
  refine h3.congr (fun q hq => ?_) ?_
  · show fderiv ℝ (fun z : E ↦ h (q.1, z)) q.2 (c q)
        = (inTangentCoordinates (𝓘(ℝ,E)) (𝓘(ℝ,ℝ)) (fun q : ℝ × E ↦ q.2)
          (fun q : ℝ × E ↦ h (q.1, q.2))
          (fun q : ℝ × E ↦
            mfderivWithin (𝓘(ℝ,E)) (𝓘(ℝ,ℝ)) (fun z : E ↦ h (q.1, z)) Ω q.2)
          (t₀, z₀) q) (c q)
    rw [hmodel]
    show fderiv ℝ (fun z : E ↦ h (q.1, z)) q.2 (c q)
      = (mfderivWithin (𝓘(ℝ,E)) (𝓘(ℝ,ℝ)) (fun z : E ↦ h (q.1, z)) Ω q.2) (c q)
    rw [mfderivWithin_of_isOpen hΩ hq.2, mfderiv_eq_fderiv]
    rfl
  · show fderiv ℝ (fun z : E ↦ h ((t₀, z₀).1, z)) (t₀, z₀).2 (c (t₀, z₀))
        = (inTangentCoordinates (𝓘(ℝ,E)) (𝓘(ℝ,ℝ)) (fun q : ℝ × E ↦ q.2)
          (fun q : ℝ × E ↦ h (q.1, q.2))
          (fun q : ℝ × E ↦
            mfderivWithin (𝓘(ℝ,E)) (𝓘(ℝ,ℝ)) (fun z : E ↦ h (q.1, z)) Ω q.2)
          (t₀, z₀) (t₀, z₀)) (c (t₀, z₀))
    rw [hmodel]
    show fderiv ℝ (fun z : E ↦ h (t₀, z)) z₀ (c (t₀, z₀))
      = (mfderivWithin (𝓘(ℝ,E)) (𝓘(ℝ,ℝ)) (fun z : E ↦ h (t₀, z)) Ω z₀) (c (t₀, z₀))
    rw [mfderivWithin_of_isOpen hΩ hz₀, mfderiv_eq_fderiv]
    rfl

/-- **Chart representation of a jointly smooth family.**  If `(t, x) ↦ u t x` is `C^∞` on
`[0,T) × M`, then its reading `(t, z) ↦ u t ((extChartAt I x₀).symm z)` in the chart at `x₀` is
`C^∞` on `[0,T) × (extChartAt I x₀).target`. -/
theorem chart_push (x₀ : M) {u : ℝ → M → ℝ} {T : ℝ}
    (hu : ContMDiffOn ((𝓘(ℝ,ℝ)).prod I) 𝓘(ℝ,ℝ) ∞ (fun p : ℝ × M ↦ u p.1 p.2)
      (Ico 0 T ×ˢ univ)) :
    ContMDiffOn ((𝓘(ℝ,ℝ)).prod (𝓘(ℝ,E))) 𝓘(ℝ,ℝ) ∞
      (fun q : ℝ × E ↦ u q.1 ((extChartAt I x₀).symm q.2))
      (Ico 0 T ×ˢ (extChartAt I x₀).target) := by
  have hsymm : ContMDiffOn (𝓘(ℝ,E)) I ∞ (fun z : E ↦ (extChartAt I x₀).symm z)
      (extChartAt I x₀).target := contMDiffOn_extChartAt_symm x₀
  have hmap : ContMDiffOn ((𝓘(ℝ,ℝ)).prod (𝓘(ℝ,E))) ((𝓘(ℝ,ℝ)).prod I) ∞
      (fun q : ℝ × E ↦ (q.1, (extChartAt I x₀).symm q.2))
      (Ico 0 T ×ˢ (extChartAt I x₀).target) := by
    intro q hq
    refine (contMDiffWithinAt_id (s := Ico 0 T ×ˢ (extChartAt I x₀).target) (x := q)).fst |>.prodMk ?_
    exact (hsymm q.2 hq.2).comp q contMDiffWithinAt_snd (fun p hp => hp.2)
  exact hu.comp hmap (fun q hq => ⟨hq.1, mem_univ _⟩)

/-- The coordinates of a vector field `X` in the chart frame at `x₀`, as a function of the chart
coordinates `q = (t, z)`. -/
noncomputable def chartCoord (x₀ : M) (X : Π y : M, TangentSpace I y) (q : ℝ × E) : E :=
  (trivializationAt E (TangentSpace I) x₀).continuousLinearMapAt ℝ ((extChartAt I x₀).symm q.2)
    (X ((extChartAt I x₀).symm q.2))

theorem joint_deriv
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M] [IsManifold I ∞ M]
    [I.Boundaryless]
    {u : ℝ → M → ℝ} {X : Π y : M, TangentSpace I y} {T : ℝ}
    (hu : ContMDiffOn (𝓘(ℝ,ℝ).prod I) 𝓘(ℝ,ℝ) ∞ (fun p : ℝ × M ↦ u p.1 p.2)
      (Ico 0 T ×ˢ univ))
    (hX : CMDiff ∞ (T% X)) :
    ContMDiffOn (𝓘(ℝ,ℝ).prod I) 𝓘(ℝ,ℝ) ∞
      (fun p : ℝ × M ↦ mvfderiv I (u p.1) p.2 (X p.2)) (Ico 0 T ×ˢ univ) := by
  intro p hp
  obtain ⟨t₀, x₀⟩ := p
  have ht₀ : t₀ ∈ Ico 0 T := hp.1
  have hsrc₀ : x₀ ∈ (extChartAt I x₀).source := mem_extChartAt_source x₀
  have hz₀ : (extChartAt I x₀) x₀ ∈ (extChartAt I x₀).target := mem_extChartAt_target x₀
  have hopen : IsOpen (extChartAt I x₀).target := isOpen_extChartAt_target x₀
  -- Step A: the chart reading of the jointly smooth family
  have hA : ContMDiffOn ((𝓘(ℝ,ℝ)).prod (𝓘(ℝ,E))) 𝓘(ℝ,ℝ) ∞
      (fun q : ℝ × E ↦ u q.1 ((extChartAt I x₀).symm q.2))
      (Ico 0 T ×ˢ (extChartAt I x₀).target) := chart_push x₀ hu
  have hh : ContMDiffWithinAt ((𝓘(ℝ,ℝ)).prod (𝓘(ℝ,E))) 𝓘(ℝ,ℝ) ∞
      (fun q : ℝ × E ↦ u q.1 ((extChartAt I x₀).symm q.2))
      (Ico 0 T ×ˢ (extChartAt I x₀).target) (t₀, (extChartAt I x₀) x₀) :=
    hA _ ⟨ht₀, hz₀⟩
  -- Step B: the coordinates of the vector field
  have hc : ContMDiffWithinAt ((𝓘(ℝ,ℝ)).prod (𝓘(ℝ,E))) (𝓘(ℝ,E)) ∞ (chartCoord x₀ X)
      (Ico 0 T ×ˢ (extChartAt I x₀).target) (t₀, (extChartAt I x₀) x₀) := by
    have hcoe : ContMDiffOn I 𝓘(ℝ,E) ∞
        (fun y : M ↦ (trivializationAt E (TangentSpace I) x₀).continuousLinearMapAt ℝ y (X y))
        (extChartAt I x₀).source := coe_smooth x₀ hX
    have hcoe2 : ContMDiffOn (𝓘(ℝ,E)) (𝓘(ℝ,E)) ∞
        (fun z : E ↦ (trivializationAt E (TangentSpace I) x₀).continuousLinearMapAt ℝ
          ((extChartAt I x₀).symm z) (X ((extChartAt I x₀).symm z)))
        (extChartAt I x₀).target :=
      hcoe.comp (contMDiffOn_extChartAt_symm x₀)
        (fun z hz => (extChartAt I x₀).map_target hz)
    have hsnd2 : ContMDiffOn ((𝓘(ℝ,ℝ)).prod (𝓘(ℝ,E))) (𝓘(ℝ,E)) ∞ (fun q : ℝ × E ↦ q.2)
        (Ico 0 T ×ˢ (extChartAt I x₀).target) := fun q hq => contMDiffWithinAt_snd
    have hcomp : ContMDiffOn ((𝓘(ℝ,ℝ)).prod (𝓘(ℝ,E))) (𝓘(ℝ,E)) ∞ (chartCoord x₀ X)
        (Ico 0 T ×ˢ (extChartAt I x₀).target) :=
      hcoe2.comp hsnd2 (fun q hq => hq.2)
    exact hcomp (t₀, (extChartAt I x₀) x₀) ⟨ht₀, hz₀⟩
  -- Step C: differentiating in the chart direction
  have hmain : ContMDiffWithinAt ((𝓘(ℝ,ℝ)).prod (𝓘(ℝ,E))) 𝓘(ℝ,ℝ) ∞
      (fun q : ℝ × E ↦ fderiv ℝ (fun z : E ↦ u q.1 ((extChartAt I x₀).symm z)) q.2
        (chartCoord x₀ X q))
      (Ico 0 T ×ˢ (extChartAt I x₀).target) (t₀, (extChartAt I x₀) x₀) :=
    partial_fderiv_smooth (E := E) (h := fun q : ℝ × E ↦ u q.1 ((extChartAt I x₀).symm q.2))
      (Ω := (extChartAt I x₀).target) (T := T) (t₀ := t₀) (z₀ := (extChartAt I x₀) x₀)
      hopen hz₀ ht₀ hh hc
  -- Step D: pull back to the manifold by the chart
  have hφpt : ContMDiffWithinAt I 𝓘(ℝ,E) ∞ (fun y : M ↦ (extChartAt I x₀) y)
      (extChartAt I x₀).source x₀ := by
    rw [extChartAt_source]
    exact (contMDiffOn_extChartAt (I := I) (n := ∞) (x := x₀)) x₀ (mem_chart_source H x₀)
  have hθ2 : ContMDiffWithinAt ((𝓘(ℝ,ℝ)).prod I) (𝓘(ℝ,E)) ∞
      (fun p : ℝ × M ↦ (extChartAt I x₀) p.2)
      (Ico 0 T ×ˢ (extChartAt I x₀).source) (t₀, x₀) :=
    (hφpt.comp (t₀, x₀) contMDiffWithinAt_snd (fun q hq => hq.2))
  have hΘ : ContMDiffWithinAt ((𝓘(ℝ,ℝ)).prod I) ((𝓘(ℝ,ℝ)).prod (𝓘(ℝ,E))) ∞
      (fun p : ℝ × M ↦ (p.1, (extChartAt I x₀) p.2))
      (Ico 0 T ×ˢ (extChartAt I x₀).source) (t₀, x₀) :=
    ((contMDiffWithinAt_id (s := Ico 0 T ×ˢ (extChartAt I x₀).source)
      (x := (t₀, x₀))).fst).prodMk hθ2
  have hmaps : MapsTo (fun p : ℝ × M ↦ (p.1, (extChartAt I x₀) p.2))
      (Ico 0 T ×ˢ (extChartAt I x₀).source) (Ico 0 T ×ˢ (extChartAt I x₀).target) := by
    intro q hq
    exact ⟨hq.1, (extChartAt I x₀).map_source hq.2⟩
  have hcomp := hmain.comp (t₀, x₀) hΘ hmaps
  -- the two functions agree on the source of the chart
  have hkey : ∀ q ∈ (Ico 0 T ×ˢ (extChartAt I x₀).source),
      (fun p : ℝ × M ↦ mvfderiv I (u p.1) p.2 (X p.2)) q
        = ((fun q : ℝ × E ↦ fderiv ℝ (fun z : E ↦ u q.1 ((extChartAt I x₀).symm z)) q.2
            (chartCoord x₀ X q)) ∘ (fun p : ℝ × M ↦ (p.1, (extChartAt I x₀) p.2))) q := by
    intro q hq
    obtain ⟨t, x⟩ := q
    have ht : t ∈ Ico 0 T := hq.1
    have hx : x ∈ (extChartAt I x₀).source := hq.2
    have hes : (extChartAt I x₀).source = (chartAt H x₀).source :=
      extChartAt_source (I := I) (x := x₀)
    have hxc : x ∈ (chartAt H x₀).source := by rw [← hes]; exact hx
    have hleft : (extChartAt I x₀).symm ((extChartAt I x₀) x) = x :=
      (extChartAt I x₀).left_inv hx
    have hmd : MDifferentiableAt I 𝓘(ℝ,ℝ) (u t) x :=
      ((contMDiff_slice_of_contMDiffOn ht hu) x).mdifferentiableAt (by simp)
    show mvfderiv I (u t) x (X x)
      = fderiv ℝ (fun z : E ↦ u t ((extChartAt I x₀).symm z)) ((extChartAt I x₀) x)
          (chartCoord x₀ X (t, (extChartAt I x₀) x))
    rw [mvfderiv_chart x₀ hxc hmd (X x)]
    simp only [chartCoord]
    rw [hleft]
  have hcomp' : ContMDiffWithinAt ((𝓘(ℝ,ℝ)).prod I) 𝓘(ℝ,ℝ) ∞
      (fun p : ℝ × M ↦ mvfderiv I (u p.1) p.2 (X p.2))
      (Ico 0 T ×ˢ (extChartAt I x₀).source) (t₀, x₀) :=
    hcomp.congr hkey (hkey (t₀, x₀) ⟨ht₀, hsrc₀⟩)
  refine hcomp'.mono_of_mem_nhdsWithin ?_
  rw [mem_nhdsWithin]
  exact ⟨univ ×ˢ (extChartAt I x₀).source, isOpen_univ.prod (isOpen_extChartAt_source x₀),
    ⟨mem_univ x₀, hsrc₀⟩, fun y hy => ⟨hy.2.1, hy.1.2⟩⟩

end Work.Diff.GE
