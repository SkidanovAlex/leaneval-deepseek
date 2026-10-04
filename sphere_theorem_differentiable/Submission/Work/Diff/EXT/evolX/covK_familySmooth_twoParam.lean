import Mathlib
import Submission.Work.Diff.EXT.evolX.twoParam
import Submission.Work.Diff.EXT.covK_familySmooth
import Submission.Work.Diff.EXT.mvfderiv_family_jointSmooth
import Submission.Work.Diff.EXT.covK_spatialDeriv

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter

namespace Work.Diff.EXT.evolX

/-! ## Auxiliary chain for the two-parameter joint smoothness of `∇^k Rm`

The one-parameter chain lives in `Submission/Work/Diff/EXT/covK_familySmooth.lean`
(`Work.Diff.EXT.rmP_familySmooth`, `Work.Diff.EXT.covK_spatialDeriv`,
`Work.Diff.EXT.lcOf_familyJointField`, ...), where the metric time and the field time coincide.
Here we redo the chain for two *independent* times `σ` (metric) and `τ` (fields): the ambient
space is `ℝ × (ℝ × M)` with model `(𝓘(ℝ,ℝ)).prod ((𝓘(ℝ,ℝ)).prod I)` and the domain is always a
subset of `W3 V = {(σ,τ,y) | (σ,y) ∈ V ∧ (τ,y) ∈ V}`.

The genuinely new ingredients are the chart coordinates of a `JointField2` family
(`coordFun2_jointAt`), the vertical lift of a two-parameter family to `T(ℝ × M)`
(`prod_inr_section`), the two-parameter spatial derivative (`covK_spatialDeriv2`), the base case
`k = 0` (`rmP_familySmooth2`) and the Levi-Civita connection of two-parameter families
(`lcOf_familyJointField2`).  The pointwise chart chain of `covK_familySmooth.lean` is reused
through the smooth projection `q ↦ (q.1, q.2.2)` (`comp_proj_joint`).
-/

/-- A two-parameter family of tangent fields, smooth on a subset of `ℝ × (ℝ × M)`.
It is the set-parameterized version of `JointField2` (`JointField2 V X` is definitionally
`JointField3 (W3 V) X`). -/
abbrev JointField3 {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]
    (U : Set (ℝ × (ℝ × M))) (X : ℝ → ℝ → TField (I := I) (M := M)) : Prop :=
  ContMDiffOn ((𝓘(ℝ, ℝ)).prod ((𝓘(ℝ, ℝ)).prod I)) I.tangent ((⊤ : ℕ∞) : WithTop ℕ∞)
    (fun q : ℝ × (ℝ × M) => (⟨q.2.2, X q.1 q.2.1 q.2.2⟩ : TangentBundle I M)) U

theorem jointField3_of_jointField2
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]
    {V : Set (ℝ × M)} {X : ℝ → ℝ → TField (I := I) (M := M)}
    (hX : JointField2 V X) : JointField3 (W3 V) X := hX

/-- **The projection `(σ,τ,y) ↦ (σ,y)` is smooth for the two-parameter model.** -/
theorem proj_jointAt
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]
    (p : ℝ × (ℝ × M)) :
    ContMDiffAt ((𝓘(ℝ, ℝ)).prod ((𝓘(ℝ, ℝ)).prod I)) ((𝓘(ℝ, ℝ)).prod I)
      ((⊤ : ℕ∞) : WithTop ℕ∞) (fun q : ℝ × (ℝ × M) => (q.1, q.2.2)) p := by
  have h1 : ContMDiffAt ((𝓘(ℝ, ℝ)).prod ((𝓘(ℝ, ℝ)).prod I)) 𝓘(ℝ, ℝ)
      ((⊤ : ℕ∞) : WithTop ℕ∞) (fun q : ℝ × (ℝ × M) => q.1) p :=
    contMDiffAt_fst
  have h2 : ContMDiffAt ((𝓘(ℝ, ℝ)).prod ((𝓘(ℝ, ℝ)).prod I)) I
      ((⊤ : ℕ∞) : WithTop ℕ∞) (fun q : ℝ × (ℝ × M) => q.2.2) p :=
    (contMDiffAt_snd (I := 𝓘(ℝ, ℝ)) (J := I) (p := p.2)).comp p
      (contMDiffAt_snd (I := 𝓘(ℝ, ℝ)) (J := (𝓘(ℝ, ℝ)).prod I) (p := p))
  exact h1.prodMk h2

/-- **Transport of a jointly smooth function of `(σ,y)` to the two-parameter model.** -/
theorem comp_proj_joint
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {Φ : ℝ × M → F} {p : ℝ × (ℝ × M)}
    (hΦ : ContMDiffAt ((𝓘(ℝ, ℝ)).prod I) 𝓘(ℝ, F) ((⊤ : ℕ∞) : WithTop ℕ∞) Φ (p.1, p.2.2)) :
    ContMDiffAt ((𝓘(ℝ, ℝ)).prod ((𝓘(ℝ, ℝ)).prod I)) 𝓘(ℝ, F) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun q : ℝ × (ℝ × M) => Φ (q.1, q.2.2)) p :=
  hΦ.comp p (proj_jointAt (I := I) (M := M) p)

/-- **Chart coordinates of a two-parameter family, on the chart domain.** -/
theorem contMDiffOn_coordFun2
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]
    [T2Space M] [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I (⊤ : ℕ∞) E (fun x : M ↦ TangentSpace I x)]
    {A : ℝ → ℝ → TField (I := I) (M := M)} {V : Set (ℝ × M)}
    (hA : JointField2 V A) (x₀ : M) :
    ContMDiffOn ((𝓘(ℝ, ℝ)).prod ((𝓘(ℝ, ℝ)).prod I)) 𝓘(ℝ, E) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun q : ℝ × (ℝ × M) => Submission.ChartCurv.coordFun x₀ (A q.1 q.2.1) q.2.2)
      ((W3 V ∩ (univ ×ˢ (univ ×ˢ (chartAt H x₀).source)))) := by
  intro p hp
  obtain ⟨hpV, -, -, hpsrc⟩ := hp
  set triv := trivializationAt E (TangentSpace I) x₀ with htriv
  have hbase : p.2.2 ∈ triv.baseSet := by
    rw [htriv, TangentBundle.trivializationAt_baseSet]; exact hpsrc
  have hsec : ContMDiffWithinAt ((𝓘(ℝ, ℝ)).prod ((𝓘(ℝ, ℝ)).prod I)) (I.prod 𝓘(ℝ, E))
      ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun q : ℝ × (ℝ × M) => (⟨q.2.2, A q.1 q.2.1 q.2.2⟩ : TangentBundle I M))
      ((W3 V ∩ (univ ×ˢ (univ ×ˢ (chartAt H x₀).source)))) p :=
    (hA p hpV).mono inter_subset_left
  have he : (⟨p.2.2, A p.1 p.2.1 p.2.2⟩ : TangentBundle I M) ∈ triv.source :=
    triv.mem_source.mpr hbase
  have h2 := ((Trivialization.contMDiffWithinAt_iff (e := triv)
    (f := fun q : ℝ × (ℝ × M) => (⟨q.2.2, A q.1 q.2.1 q.2.2⟩ : TangentBundle I M))
    (s := (W3 V ∩ (univ ×ˢ (univ ×ˢ (chartAt H x₀).source)))) (x₀ := p) he).mp hsec).2
  refine h2.congr_of_eventuallyEq ?_ ?_
  · filter_upwards [self_mem_nhdsWithin] with q hq
    obtain ⟨-, -, -, hqsrc⟩ := hq
    show Submission.ChartCurv.coordFun x₀ (A q.1 q.2.1) q.2.2
        = (triv ⟨q.2.2, A q.1 q.2.1 q.2.2⟩).2
    rw [Submission.ChartCurv.coordFun_apply]
    exact Trivialization.continuousLinearMapAt_apply_of_mem ℝ triv
      (by rw [htriv, TangentBundle.trivializationAt_baseSet]; exact hqsrc) (A q.1 q.2.1 q.2.2)
  · show Submission.ChartCurv.coordFun x₀ (A p.1 p.2.1) p.2.2
        = (triv ⟨p.2.2, A p.1 p.2.1 p.2.2⟩).2
    rw [Submission.ChartCurv.coordFun_apply]
    exact Trivialization.continuousLinearMapAt_apply_of_mem ℝ triv hbase (A p.1 p.2.1 p.2.2)

/-- **Chart coordinates of a two-parameter family, pointwise form.** -/
theorem coordFun2_jointAt
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]
    [T2Space M] [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I (⊤ : ℕ∞) E (fun x : M ↦ TangentSpace I x)]
    {A : ℝ → ℝ → TField (I := I) (M := M)} {V : Set (ℝ × M)} (hV : IsOpen V)
    (hA : JointField2 V A) {x₀ : M} {p : ℝ × (ℝ × M)}
    (hp : p ∈ W3 V) (hsrc : p.2.2 ∈ (chartAt H x₀).source) :
    ContMDiffAt ((𝓘(ℝ, ℝ)).prod ((𝓘(ℝ, ℝ)).prod I)) 𝓘(ℝ, E) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun q : ℝ × (ℝ × M) => Submission.ChartCurv.coordFun x₀ (A q.1 q.2.1) q.2.2) p := by
  have hnhds : (W3 V ∩ (univ ×ˢ (univ ×ˢ (chartAt H x₀).source))) ∈ 𝓝 p :=
    ((isOpen_W3 hV).inter (isOpen_univ.prod (isOpen_univ.prod
      (chartAt H x₀).open_source))).mem_nhds ⟨hp, mem_univ p.1, mem_univ p.2.1, hsrc⟩
  exact ((contMDiffOn_coordFun2 (I := I) (M := M) hA x₀) p
    ⟨hp, mem_univ p.1, mem_univ p.2.1, hsrc⟩).contMDiffAt hnhds

/-- **The vertical lift of a two-parameter family.**  The section `(σ,τ,y) ↦ (0, X σ τ y)` of
`T(ℝ × M)` is `C^∞` wherever `X` is.  This is the two-time version of
`Work.Diff.EXT.contMDiffAt_prod_inr_field_family`. -/
theorem prod_inr_section
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]
    {U : Set (ℝ × (ℝ × M))} (hU : IsOpen U)
    {X : ℝ → ℝ → TField (I := I) (M := M)} (hX : JointField3 U X) :
    ContMDiffOn ((𝓘(ℝ, ℝ)).prod ((𝓘(ℝ, ℝ)).prod I)) ((𝓘(ℝ, ℝ)).prod I).tangent
      ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun q : ℝ × (ℝ × M) => (⟨q.2, ((0 : TangentSpace (𝓘(ℝ, ℝ)) q.2.1),
        X q.1 q.2.1 q.2.2)⟩ : TangentBundle ((𝓘(ℝ, ℝ)).prod I) (ℝ × M))) U := by
  intro p hp
  have hat : ContMDiffAt ((𝓘(ℝ, ℝ)).prod ((𝓘(ℝ, ℝ)).prod I))
      ((𝓘(ℝ, ℝ)).prod I).tangent ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun q : ℝ × (ℝ × M) => (⟨q.2, ((0 : TangentSpace (𝓘(ℝ, ℝ)) q.2.1),
        X q.1 q.2.1 q.2.2)⟩ : TangentBundle ((𝓘(ℝ, ℝ)).prod I) (ℝ × M))) p := by
    have h1 : ContMDiffAt ((𝓘(ℝ, ℝ)).prod ((𝓘(ℝ, ℝ)).prod I)) (𝓘(ℝ, ℝ)).tangent
        ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun q : ℝ × (ℝ × M) => zeroSection ℝ (TangentSpace (𝓘(ℝ, ℝ))) q.2.1) p :=
      (contMDiffAt_zeroSection ℝ (TangentSpace (𝓘(ℝ, ℝ)))).comp p
        ((contMDiffAt_fst (I := 𝓘(ℝ, ℝ)) (J := I) (p := p.2)).comp p
          (contMDiffAt_snd (I := 𝓘(ℝ, ℝ)) (J := (𝓘(ℝ, ℝ)).prod I) (p := p)))
    have h2 : ContMDiffAt ((𝓘(ℝ, ℝ)).prod ((𝓘(ℝ, ℝ)).prod I)) I.tangent
        ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun q : ℝ × (ℝ × M) => (⟨q.2.2, X q.1 q.2.1 q.2.2⟩ : TangentBundle I M)) p :=
      (hX p hp).contMDiffAt (hU.mem_nhds hp)
    have hg := h1.prodMk h2
    have he := (contMDiff_equivTangentBundleProd_symm (I := 𝓘(ℝ, ℝ)) (M := ℝ) (I' := I)
      (M' := M) (n := ∞)).contMDiffAt
      (x := ((zeroSection ℝ (TangentSpace (𝓘(ℝ, ℝ))) p.2.1),
        (⟨p.2.2, X p.1 p.2.1 p.2.2⟩ : TangentBundle I M)))
    exact (he.comp p hg).congr_of_eventuallyEq (EventuallyEq.of_eq (by funext q; rfl))
  exact hat.contMDiffWithinAt

/-- **Spatial derivative of a two-parameter family along a two-parameter direction field.**  The
two-time version of `Work.Diff.EXT.covK_spatialDeriv`. -/
theorem covK_spatialDeriv2
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]
    [I.Boundaryless] [T2Space M]
    {U : Set (ℝ × (ℝ × M))} (hU : IsOpen U)
    {Φ : ℝ → ℝ → M → ℝ}
    (hΦ : ContMDiffOn ((𝓘(ℝ, ℝ)).prod ((𝓘(ℝ, ℝ)).prod I)) 𝓘(ℝ, ℝ) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun q : ℝ × (ℝ × M) => Φ q.1 q.2.1 q.2.2) U)
    {X : ℝ → ℝ → TField (I := I) (M := M)} (hX : JointField3 U X) :
    ContMDiffOn ((𝓘(ℝ, ℝ)).prod ((𝓘(ℝ, ℝ)).prod I)) 𝓘(ℝ, ℝ) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun q : ℝ × (ℝ × M) => mvfderiv I (Φ q.1 q.2.1) q.2.2 (X q.1 q.2.1 q.2.2)) U := by
  have hXU : ContMDiffOn ((𝓘(ℝ, ℝ)).prod ((𝓘(ℝ, ℝ)).prod I))
      ((𝓘(ℝ, ℝ)).prod I).tangent ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun q : ℝ × (ℝ × M) => (⟨q.2, ((0 : TangentSpace (𝓘(ℝ, ℝ)) q.2.1),
        X q.1 q.2.1 q.2.2)⟩ : TangentBundle ((𝓘(ℝ, ℝ)).prod I) (ℝ × M))) U :=
    prod_inr_section (I := I) (M := M) hU hX
  have hres := Work.Diff.EXT.covK_spatialDeriv (I := (𝓘(ℝ, ℝ)).prod I) (M := ℝ × M)
    (Φ := fun (t : ℝ) (z : ℝ × M) => Φ t z.1 z.2)
    (X := fun (t : ℝ) (z : ℝ × M) =>
      ((0 : TangentSpace (𝓘(ℝ, ℝ)) z.1), X t z.1 z.2)) hU hΦ hXU
  refine hres.congr (fun p hp => ?_)
  have hslice : ContMDiffAt ((𝓘(ℝ, ℝ)).prod I) 𝓘(ℝ, ℝ) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun z : ℝ × M => Φ p.1 z.1 z.2) p.2 :=
    (hΦ.contMDiffAt (hU.mem_nhds hp)).comp p.2
      ((contMDiffAt_const (c := p.1)).prodMk contMDiffAt_id)
  exact (Work.Diff.EXT.mvfderiv_prod_slice_eq (I := I) (M := M)
    (Φ := fun z : ℝ × M => Φ p.1 z.1 z.2)
    (hslice.mdifferentiableAt (by simp))).symm

/-- **Joint smoothness of `rmP` for a two-parameter family** (the base case `k = 0`). -/
theorem rmP_familySmooth2
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]
    [I.Boundaryless] [T2Space M]
    (hLC : Submission.Diff.LCSmooth I M)
    {G : ℝ → Submission.Diff.SMet I M} {V : Set (ℝ × M)} (hV : IsOpen V)
    (hG : JointMet G V)
    {A B C D : ℝ → ℝ → TField (I := I) (M := M)}
    (hA : JointField2 V A) (hB : JointField2 V B) (hC : JointField2 V C) (hD : JointField2 V D) :
    ContMDiffOn ((𝓘(ℝ, ℝ)).prod ((𝓘(ℝ, ℝ)).prod I)) 𝓘(ℝ, ℝ) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun q : ℝ × (ℝ × M) => Submission.Diff.rmP (G q.1) q.2.2
        (A q.1 q.2.1 q.2.2) (B q.1 q.2.1 q.2.2) (C q.1 q.2.1 q.2.2) (D q.1 q.2.1 q.2.2))
      (W3 V) := by
  intro p hp
  letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨(G p.1).toRiemannianMetric⟩
  haveI : IsContMDiffRiemannianBundle I (⊤ : ℕ∞) E (fun x : M ↦ TangentSpace I x) := inferInstance
  have hmet : MetSmoothAt (I := I) (M := M) G p.1 p.2.2 := hG.metSmoothAt hV hp.1
  have hcA : ContMDiffAt ((𝓘(ℝ, ℝ)).prod ((𝓘(ℝ, ℝ)).prod I)) 𝓘(ℝ, E)
      ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun q : ℝ × (ℝ × M) => Submission.ChartCurv.coordFun p.2.2 (A q.1 q.2.1) q.2.2) p :=
    coordFun2_jointAt (I := I) (M := M) hV hA hp (mem_chart_source H p.2.2)
  have hcB : ContMDiffAt ((𝓘(ℝ, ℝ)).prod ((𝓘(ℝ, ℝ)).prod I)) 𝓘(ℝ, E)
      ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun q : ℝ × (ℝ × M) => Submission.ChartCurv.coordFun p.2.2 (B q.1 q.2.1) q.2.2) p :=
    coordFun2_jointAt (I := I) (M := M) hV hB hp (mem_chart_source H p.2.2)
  have hcC : ContMDiffAt ((𝓘(ℝ, ℝ)).prod ((𝓘(ℝ, ℝ)).prod I)) 𝓘(ℝ, E)
      ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun q : ℝ × (ℝ × M) => Submission.ChartCurv.coordFun p.2.2 (C q.1 q.2.1) q.2.2) p :=
    coordFun2_jointAt (I := I) (M := M) hV hC hp (mem_chart_source H p.2.2)
  have hcD : ContMDiffAt ((𝓘(ℝ, ℝ)).prod ((𝓘(ℝ, ℝ)).prod I)) 𝓘(ℝ, E)
      ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun q : ℝ × (ℝ × M) => Submission.ChartCurv.coordFun p.2.2 (D q.1 q.2.1) q.2.2) p :=
    coordFun2_jointAt (I := I) (M := M) hV hD hp (mem_chart_source H p.2.2)
  have hsum : ContMDiffAt ((𝓘(ℝ, ℝ)).prod ((𝓘(ℝ, ℝ)).prod I)) 𝓘(ℝ, ℝ)
      ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun q : ℝ × (ℝ × M) => ∑ i, ∑ j, ∑ k, ∑ l,
        ((Work.Diff.GE.cBasis (E := E)).coord i
            (Submission.ChartCurv.coordFun p.2.2 (A q.1 q.2.1) q.2.2))
          * ((Work.Diff.GE.cBasis (E := E)).coord j
              (Submission.ChartCurv.coordFun p.2.2 (B q.1 q.2.1) q.2.2))
          * ((Work.Diff.GE.cBasis (E := E)).coord k
              (Submission.ChartCurv.coordFun p.2.2 (C q.1 q.2.1) q.2.2))
          * ((Work.Diff.GE.cBasis (E := E)).coord l
              (Submission.ChartCurv.coordFun p.2.2 (D q.1 q.2.1) q.2.2))
          * Work.Diff.GE.rmC4 (I := I) G p.2.2 q.1 q.2.2 i j k l) p := by
    refine ContMDiffAt.sum (fun i _ ↦ ContMDiffAt.sum (fun j _ ↦ ContMDiffAt.sum (fun k _ ↦
      ContMDiffAt.sum (fun l _ ↦ ?_))))
    have h1 : ContMDiffAt ((𝓘(ℝ, ℝ)).prod ((𝓘(ℝ, ℝ)).prod I)) 𝓘(ℝ, ℝ)
        ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun q : ℝ × (ℝ × M) => (Work.Diff.GE.cBasis (E := E)).coord i
          (Submission.ChartCurv.coordFun p.2.2 (A q.1 q.2.1) q.2.2)) p :=
      (LinearMap.toContinuousLinearMap ((Work.Diff.GE.cBasis (E := E)).coord i)).contMDiffAt.comp
        p hcA
    have h2 : ContMDiffAt ((𝓘(ℝ, ℝ)).prod ((𝓘(ℝ, ℝ)).prod I)) 𝓘(ℝ, ℝ)
        ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun q : ℝ × (ℝ × M) => (Work.Diff.GE.cBasis (E := E)).coord j
          (Submission.ChartCurv.coordFun p.2.2 (B q.1 q.2.1) q.2.2)) p :=
      (LinearMap.toContinuousLinearMap ((Work.Diff.GE.cBasis (E := E)).coord j)).contMDiffAt.comp
        p hcB
    have h3 : ContMDiffAt ((𝓘(ℝ, ℝ)).prod ((𝓘(ℝ, ℝ)).prod I)) 𝓘(ℝ, ℝ)
        ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun q : ℝ × (ℝ × M) => (Work.Diff.GE.cBasis (E := E)).coord k
          (Submission.ChartCurv.coordFun p.2.2 (C q.1 q.2.1) q.2.2)) p :=
      (LinearMap.toContinuousLinearMap ((Work.Diff.GE.cBasis (E := E)).coord k)).contMDiffAt.comp
        p hcC
    have h4 : ContMDiffAt ((𝓘(ℝ, ℝ)).prod ((𝓘(ℝ, ℝ)).prod I)) 𝓘(ℝ, ℝ)
        ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun q : ℝ × (ℝ × M) => (Work.Diff.GE.cBasis (E := E)).coord l
          (Submission.ChartCurv.coordFun p.2.2 (D q.1 q.2.1) q.2.2)) p :=
      (LinearMap.toContinuousLinearMap ((Work.Diff.GE.cBasis (E := E)).coord l)).contMDiffAt.comp
        p hcD
    have h5 : ContMDiffAt ((𝓘(ℝ, ℝ)).prod ((𝓘(ℝ, ℝ)).prod I)) 𝓘(ℝ, ℝ)
        ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun q : ℝ × (ℝ × M) => Work.Diff.GE.rmC4 (I := I) G p.2.2 q.1 q.2.2 i j k l) p :=
      comp_proj_joint (I := I) (M := M) (F := ℝ)
        (Φ := fun s : ℝ × M => Work.Diff.GE.rmC4 (I := I) G p.2.2 s.1 s.2 i j k l)
        (rmC4_at (I := I) (M := M) hLC (G := G) hmet i j k l)
    exact ((((h1.mul h2).mul h3).mul h4).mul h5)
  refine (hsum.congr_of_eventuallyEq ?_).contMDiffWithinAt
  filter_upwards [prod_mem_nhds Filter.univ_mem (prod_mem_nhds Filter.univ_mem
    ((chartAt H p.2.2).open_source.mem_nhds (mem_chart_source H p.2.2)))] with q hq
  exact Work.Diff.GE.rmP_eq_sum_rmC4 (I := I) (M := M) hLC G p.2.2 q.1 hq.2.2
    (A := fun y : M => A q.1 q.2.1 y) (B := fun y : M => B q.1 q.2.1 y)
    (C := fun y : M => C q.1 q.2.1 y) (D := fun y : M => D q.1 q.2.1 y)

/-- **The Christoffel symbol along two-parameter families of model vectors.** -/
theorem chrB2_jointAt
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]
    [I.Boundaryless] [T2Space M]
    (hLC : Submission.Diff.LCSmooth I M)
    {G : ℝ → Submission.Diff.SMet I M} {V : Set (ℝ × M)} (hV : IsOpen V) (hG : JointMet G V)
    {p : ℝ × (ℝ × M)} (hp : p ∈ W3 V)
    {U W : ℝ × (ℝ × M) → E}
    (hU : ContMDiffAt ((𝓘(ℝ, ℝ)).prod ((𝓘(ℝ, ℝ)).prod I)) 𝓘(ℝ, E)
      ((⊤ : ℕ∞) : WithTop ℕ∞) U p)
    (hW : ContMDiffAt ((𝓘(ℝ, ℝ)).prod ((𝓘(ℝ, ℝ)).prod I)) 𝓘(ℝ, E)
      ((⊤ : ℕ∞) : WithTop ℕ∞) W p) :
    ContMDiffAt ((𝓘(ℝ, ℝ)).prod ((𝓘(ℝ, ℝ)).prod I)) 𝓘(ℝ, E) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun q : ℝ × (ℝ × M) => Submission.ChartCurv.chrB (Submission.Diff.lcOf (G q.1))
        p.2.2 q.2.2 (U q) (W q)) p := by
  letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨(G p.1).toRiemannianMetric⟩
  haveI : IsContMDiffRiemannianBundle I (⊤ : ℕ∞) E (fun x : M ↦ TangentSpace I x) := inferInstance
  have hmet : MetSmoothAt (I := I) (M := M) G p.1 p.2.2 := hG.metSmoothAt hV hp.1
  have hsum : ContMDiffAt ((𝓘(ℝ, ℝ)).prod ((𝓘(ℝ, ℝ)).prod I)) 𝓘(ℝ, E)
      ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun q : ℝ × (ℝ × M) => ∑ i, ∑ j,
        (((Module.finBasis ℝ E).coord i (U q)) * ((Module.finBasis ℝ E).coord j (W q))) •
          Submission.ChartCurv.chrB (Submission.Diff.lcOf (G q.1)) p.2.2 q.2.2
            (Module.finBasis ℝ E i) (Module.finBasis ℝ E j)) p := by
    refine ContMDiffAt.sum (fun i _ ↦ ContMDiffAt.sum (fun j _ ↦ ?_))
    have h1 : ContMDiffAt ((𝓘(ℝ, ℝ)).prod ((𝓘(ℝ, ℝ)).prod I)) 𝓘(ℝ, ℝ)
        ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun q : ℝ × (ℝ × M) => (Module.finBasis ℝ E).coord i (U q)) p :=
      (LinearMap.toContinuousLinearMap ((Module.finBasis ℝ E).coord i)).contMDiffAt.comp p hU
    have h2 : ContMDiffAt ((𝓘(ℝ, ℝ)).prod ((𝓘(ℝ, ℝ)).prod I)) 𝓘(ℝ, ℝ)
        ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun q : ℝ × (ℝ × M) => (Module.finBasis ℝ E).coord j (W q)) p :=
      (LinearMap.toContinuousLinearMap ((Module.finBasis ℝ E).coord j)).contMDiffAt.comp p hW
    have h3 : ContMDiffAt ((𝓘(ℝ, ℝ)).prod ((𝓘(ℝ, ℝ)).prod I)) 𝓘(ℝ, E)
        ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun q : ℝ × (ℝ × M) => Submission.ChartCurv.chrB (Submission.Diff.lcOf (G q.1))
          p.2.2 q.2.2 (Module.finBasis ℝ E i) (Module.finBasis ℝ E j)) p :=
      comp_proj_joint (I := I) (M := M) (F := E)
        (Φ := fun s : ℝ × M => Submission.ChartCurv.chrB (Submission.Diff.lcOf (G s.1))
          p.2.2 s.2 (Module.finBasis ℝ E i) (Module.finBasis ℝ E j))
        (chrB_at (I := I) (M := M) (G := G) hmet i j)
    exact (h1.mul h2).smul h3
  refine hsum.congr_of_eventuallyEq ?_
  filter_upwards [prod_mem_nhds Filter.univ_mem (prod_mem_nhds Filter.univ_mem
    ((chartAt H p.2.2).open_source.mem_nhds (mem_chart_source H p.2.2)))] with q hq
  have hU' : U q = ∑ i, ((Module.finBasis ℝ E).coord i (U q)) • Module.finBasis ℝ E i := by
    rw [Finset.sum_congr rfl (fun i _ => by rw [Module.Basis.coord_apply])]
    exact ((Module.finBasis ℝ E).sum_repr (U q)).symm
  have hW' : W q = ∑ j, ((Module.finBasis ℝ E).coord j (W q)) • Module.finBasis ℝ E j := by
    rw [Finset.sum_congr rfl (fun j _ => by rw [Module.Basis.coord_apply])]
    exact ((Module.finBasis ℝ E).sum_repr (W q)).symm
  conv_lhs => rw [hU', hW']
  rw [Submission.ChartCurv.chrB_sum_fst Finset.univ p.2.2 q.2.2 _ _
    (∑ j, ((Module.finBasis ℝ E).coord j (W q)) • Module.finBasis ℝ E j) hq.2.2]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Submission.ChartCurv.chrB_sum_snd Finset.univ p.2.2 q.2.2 _ _ (Module.finBasis ℝ E i),
    Finset.smul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [smul_smul]

/-- **Coordinates of the Levi-Civita connection along two-parameter families.** -/
theorem coordFun_lcOf2
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]
    [I.Boundaryless] [T2Space M]
    (hLC : Submission.Diff.LCSmooth I M)
    {G : ℝ → Submission.Diff.SMet I M} {V : Set (ℝ × M)} (hV : IsOpen V) (hG : JointMet G V)
    {X Z : ℝ → ℝ → TField (I := I) (M := M)}
    (hX : JointField2 V X) (hZ : JointField2 V Z)
    {p : ℝ × (ℝ × M)} (hp : p ∈ W3 V) :
    ContMDiffAt ((𝓘(ℝ, ℝ)).prod ((𝓘(ℝ, ℝ)).prod I)) 𝓘(ℝ, E) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun q : ℝ × (ℝ × M) => Submission.ChartCurv.coordFun p.2.2
        (fun y => Submission.Diff.lcOf (G q.1) (X q.1 q.2.1) y (Z q.1 q.2.1 y)) q.2.2) p := by
  letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨(G p.1).toRiemannianMetric⟩
  haveI : IsContMDiffRiemannianBundle I (⊤ : ℕ∞) E (fun x : M ↦ TangentSpace I x) :=
    inferInstance
  have hWopen : IsOpen ((W3 V ∩ (univ ×ˢ (univ ×ˢ (chartAt H p.2.2).source)))) :=
    (isOpen_W3 hV).inter (isOpen_univ.prod (isOpen_univ.prod
      (chartAt H p.2.2).open_source))
  have hpW : p ∈ (W3 V ∩ (univ ×ˢ (univ ×ˢ (chartAt H p.2.2).source))) :=
    ⟨hp, mem_univ p.1, mem_univ p.2.1, mem_chart_source H p.2.2⟩
  have hsub : (W3 V ∩ (univ ×ˢ (univ ×ˢ (chartAt H p.2.2).source))) ⊆ W3 V := inter_subset_left
  have hcoordX : ContMDiffOn ((𝓘(ℝ, ℝ)).prod ((𝓘(ℝ, ℝ)).prod I)) 𝓘(ℝ, E)
      ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun q : ℝ × (ℝ × M) => Submission.ChartCurv.coordFun p.2.2 (X q.1 q.2.1) q.2.2)
      ((W3 V ∩ (univ ×ˢ (univ ×ˢ (chartAt H p.2.2).source)))) :=
    contMDiffOn_coordFun2 (I := I) (M := M) hX p.2.2
  have hcoordZ : ContMDiffOn ((𝓘(ℝ, ℝ)).prod ((𝓘(ℝ, ℝ)).prod I)) 𝓘(ℝ, E)
      ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun q : ℝ × (ℝ × M) => Submission.ChartCurv.coordFun p.2.2 (Z q.1 q.2.1) q.2.2)
      ((W3 V ∩ (univ ×ˢ (univ ×ˢ (chartAt H p.2.2).source)))) :=
    contMDiffOn_coordFun2 (I := I) (M := M) hZ p.2.2
  have hev : (fun q : ℝ × (ℝ × M) => Submission.ChartCurv.coordFun p.2.2
        (fun y => Submission.Diff.lcOf (G q.1) (X q.1 q.2.1) y (Z q.1 q.2.1 y)) q.2.2)
      =ᶠ[𝓝 p] (fun q : ℝ × (ℝ × M) =>
        mvfderiv I (fun y => Submission.ChartCurv.coordFun p.2.2 (X q.1 q.2.1) y) q.2.2
            (Z q.1 q.2.1 q.2.2)
          + Submission.ChartCurv.chrB (Submission.Diff.lcOf (G q.1)) p.2.2 q.2.2
              (Submission.ChartCurv.coordFun p.2.2 (X q.1 q.2.1) q.2.2)
              (Submission.ChartCurv.coordFun p.2.2 (Z q.1 q.2.1) q.2.2)) := by
    filter_upwards [hWopen.mem_nhds hpW] with q hq
    have hqsrc : q.2.2 ∈ (chartAt H p.2.2).source := hq.2.2.2
    have hXat : ContMDiffAt I I.tangent ((⊤ : ℕ∞) : WithTop ℕ∞) (T% (X q.1 q.2.1)) q.2.2 :=
      ((hX q hq.1).contMDiffAt ((isOpen_W3 hV).mem_nhds hq.1)).comp q.2.2
        ((contMDiffAt_const (c := q.1)).prodMk
          ((contMDiffAt_const (c := q.2.1)).prodMk contMDiffAt_id))
    have hZat : ContMDiffAt I I.tangent ((⊤ : ℕ∞) : WithTop ℕ∞) (T% (Z q.1 q.2.1)) q.2.2 :=
      ((hZ q hq.1).contMDiffAt ((isOpen_W3 hV).mem_nhds hq.1)).comp q.2.2
        ((contMDiffAt_const (c := q.1)).prodMk
          ((contMDiffAt_const (c := q.2.1)).prodMk contMDiffAt_id))
    haveI : ContMDiffCovariantDerivative (Submission.Diff.lcOf (G q.1)) (⊤ : ℕ∞) :=
      (hLC (G q.1)).1.some
    exact coordFun_cov_at (I := I) (M := M) (cov := Submission.Diff.lcOf (G q.1)) p.2.2
      hXat hZat hqsrc
  have htermA : ContMDiffAt ((𝓘(ℝ, ℝ)).prod ((𝓘(ℝ, ℝ)).prod I)) 𝓘(ℝ, E)
      ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun q : ℝ × (ℝ × M) => mvfderiv I
        (fun y => Submission.ChartCurv.coordFun p.2.2 (X q.1 q.2.1) y) q.2.2
          (Z q.1 q.2.1 q.2.2)) p := by
    have hsum : ContMDiffAt ((𝓘(ℝ, ℝ)).prod ((𝓘(ℝ, ℝ)).prod I)) 𝓘(ℝ, E)
        ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun q : ℝ × (ℝ × M) => ∑ i, (mvfderiv I
            (fun y => (Module.finBasis ℝ E).coord i
              (Submission.ChartCurv.coordFun p.2.2 (X q.1 q.2.1) y)) q.2.2
              (Z q.1 q.2.1 q.2.2)) • Module.finBasis ℝ E i) p := by
      refine ContMDiffAt.sum (fun i _ => ?_)
      have hΦi : ContMDiffOn ((𝓘(ℝ, ℝ)).prod ((𝓘(ℝ, ℝ)).prod I)) 𝓘(ℝ, ℝ)
          ((⊤ : ℕ∞) : WithTop ℕ∞)
          (fun q : ℝ × (ℝ × M) => (Module.finBasis ℝ E).coord i
            (Submission.ChartCurv.coordFun p.2.2 (X q.1 q.2.1) q.2.2))
          ((W3 V ∩ (univ ×ˢ (univ ×ˢ (chartAt H p.2.2).source)))) :=
        (((LinearMap.toContinuousLinearMap ((Module.finBasis ℝ E).coord i)).contMDiff.contMDiffOn).comp
          (t := univ) hcoordX (fun q _ => trivial))
      have hsp := covK_spatialDeriv2 (I := I) (M := M) (U := (W3 V ∩ (univ ×ˢ (univ ×ˢ (chartAt H p.2.2).source)))) hWopen
        (Φ := fun (σ τ : ℝ) (y : M) => (Module.finBasis ℝ E).coord i
          (Submission.ChartCurv.coordFun p.2.2 (X σ τ) y)) hΦi (hZ.mono hsub)
      exact (hsp.contMDiffAt (hWopen.mem_nhds hpW)).smul
        (contMDiffAt_const (c := Module.finBasis ℝ E i))
    refine hsum.congr_of_eventuallyEq ?_
    filter_upwards [hWopen.mem_nhds hpW] with q hq
    exact Submission.ChartCurv.mvfderiv_eq_sum_coord (I := I)
      (c := fun y : M => Submission.ChartCurv.coordFun p.2.2 (X q.1 q.2.1) y)
      (((hcoordX.contMDiffAt (hWopen.mem_nhds hq)).comp q.2.2
        ((contMDiffAt_const (c := q.1)).prodMk
          ((contMDiffAt_const (c := q.2.1)).prodMk contMDiffAt_id))).mdifferentiableAt
          (by simp))
  have htermB : ContMDiffAt ((𝓘(ℝ, ℝ)).prod ((𝓘(ℝ, ℝ)).prod I)) 𝓘(ℝ, E)
      ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun q : ℝ × (ℝ × M) => Submission.ChartCurv.chrB (Submission.Diff.lcOf (G q.1))
        p.2.2 q.2.2 (Submission.ChartCurv.coordFun p.2.2 (X q.1 q.2.1) q.2.2)
        (Submission.ChartCurv.coordFun p.2.2 (Z q.1 q.2.1) q.2.2)) p :=
    chrB2_jointAt (I := I) (M := M) hLC hV hG hp
      (coordFun2_jointAt (I := I) (M := M) hV hX hp (mem_chart_source H p.2.2))
      (coordFun2_jointAt (I := I) (M := M) hV hZ hp (mem_chart_source H p.2.2))
  exact (htermA.add htermB).congr_of_eventuallyEq hev

/-- **The Levi-Civita connection along two-parameter families of fields.** -/
theorem lcOf_familyJointField2
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]
    [I.Boundaryless] [T2Space M]
    (hLC : Submission.Diff.LCSmooth I M)
    {G : ℝ → Submission.Diff.SMet I M} {V : Set (ℝ × M)} (hV : IsOpen V) (hG : JointMet G V)
    {X Z : ℝ → ℝ → TField (I := I) (M := M)}
    (hX : JointField2 V X) (hZ : JointField2 V Z) :
    JointField2 V (fun σ τ => fun y => Submission.Diff.lcOf (G σ) (X σ τ) y (Z σ τ y)) := by
  intro p hp
  letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨(G p.1).toRiemannianMetric⟩
  haveI : IsContMDiffRiemannianBundle I (⊤ : ℕ∞) E (fun x : M ↦ TangentSpace I x) :=
    inferInstance
  set triv := trivializationAt E (TangentSpace I) p.2.2 with htriv
  have hbase : p.2.2 ∈ triv.baseSet := by
    rw [htriv, TangentBundle.trivializationAt_baseSet]; exact mem_chart_source H p.2.2
  have he : (⟨p.2.2, Submission.Diff.lcOf (G p.1) (X p.1 p.2.1) p.2.2
      (Z p.1 p.2.1 p.2.2)⟩ : TangentBundle I M) ∈ triv.source :=
    triv.mem_source.mpr hbase
  have hcoord : ContMDiffAt ((𝓘(ℝ, ℝ)).prod ((𝓘(ℝ, ℝ)).prod I)) 𝓘(ℝ, E)
      ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun q : ℝ × (ℝ × M) => (triv ⟨q.2.2, Submission.Diff.lcOf (G q.1) (X q.1 q.2.1)
        q.2.2 (Z q.1 q.2.1 q.2.2)⟩).2) p := by
    refine (coordFun_lcOf2 (I := I) (M := M) hLC hV hG hX hZ hp).congr_of_eventuallyEq ?_
    filter_upwards [prod_mem_nhds Filter.univ_mem (prod_mem_nhds Filter.univ_mem
      ((chartAt H p.2.2).open_source.mem_nhds (mem_chart_source H p.2.2)))] with q hq
    show (triv ⟨q.2.2, Submission.Diff.lcOf (G q.1) (X q.1 q.2.1) q.2.2
        (Z q.1 q.2.1 q.2.2)⟩).2
      = Submission.ChartCurv.coordFun p.2.2 (fun y => Submission.Diff.lcOf (G q.1)
          (X q.1 q.2.1) y (Z q.1 q.2.1 y)) q.2.2
    rw [Submission.ChartCurv.coordFun_apply]
    exact (Trivialization.continuousLinearMapAt_apply_of_mem ℝ triv
      (by rw [htriv, TangentBundle.trivializationAt_baseSet]; exact hq.2.2) _).symm
  exact ((Trivialization.contMDiffWithinAt_iff (e := triv) (f := fun q : ℝ × (ℝ × M) =>
    (⟨q.2.2, Submission.Diff.lcOf (G q.1) (X q.1 q.2.1) q.2.2
      (Z q.1 q.2.1 q.2.2)⟩ : TangentBundle I M)) (s := W3 V) (x₀ := p) he).mpr
      ⟨((contMDiffAt_snd (I := 𝓘(ℝ, ℝ)) (J := I) (p := p.2)).comp p
          (contMDiffAt_snd (I := 𝓘(ℝ, ℝ)) (J := (𝓘(ℝ, ℝ)).prod I) (p := p))).contMDiffWithinAt,
        hcoord.contMDiffWithinAt⟩)

theorem covK_familySmooth_twoParam
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]
    [I.Boundaryless] [T2Space M]
    (hLC : Submission.Diff.LCSmooth I M)
    {G : ℝ → Submission.Diff.SMet I M} {V : Set (ℝ × M)} (hV : IsOpen V)
    (hG : Work.Diff.EXT.JointMet G V)
    (k : ℕ) {Vf : ℝ → ℝ → Fin k → Work.Diff.EXT.TField (I := I) (M := M)}
    (hVf : ∀ i, Work.Diff.EXT.evolX.JointField2 V (fun σ τ => Vf σ τ i))
    {A B C D : ℝ → ℝ → Work.Diff.EXT.TField (I := I) (M := M)}
    (hA : Work.Diff.EXT.evolX.JointField2 V A) (hB : Work.Diff.EXT.evolX.JointField2 V B)
    (hC : Work.Diff.EXT.evolX.JointField2 V C) (hD : Work.Diff.EXT.evolX.JointField2 V D) :
    ContMDiffOn ((modelWithCornersSelf ℝ ℝ).prod ((modelWithCornersSelf ℝ ℝ).prod I))
      (modelWithCornersSelf ℝ ℝ) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun q : ℝ × (ℝ × M) => Work.Diff.EXT.covKRmExt (G q.1) k (Vf q.1 q.2.1)
        (A q.1 q.2.1) (B q.1 q.2.1) (C q.1 q.2.1) (D q.1 q.2.1) q.2.2)
      (Work.Diff.EXT.evolX.W3 V) := by
  suffices h : ∀ (j : ℕ) (Vf : ℝ → ℝ → Fin j → TField (I := I) (M := M)),
      (∀ i, JointField2 V (fun σ τ => Vf σ τ i)) →
      ∀ (A B C D : ℝ → ℝ → TField (I := I) (M := M)), JointField2 V A → JointField2 V B →
        JointField2 V C → JointField2 V D →
      ContMDiffOn ((𝓘(ℝ, ℝ)).prod ((𝓘(ℝ, ℝ)).prod I)) 𝓘(ℝ, ℝ) ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun q : ℝ × (ℝ × M) => covKRmExt (G q.1) j (Vf q.1 q.2.1) (A q.1 q.2.1)
          (B q.1 q.2.1) (C q.1 q.2.1) (D q.1 q.2.1) q.2.2) (W3 V) by
    exact h k Vf hVf A B C D hA hB hC hD
  intro j
  induction j with
  | zero =>
    intro Vf hVf A B C D hA hB hC hD
    have h0 := rmP_familySmooth2 (I := I) (M := M) hLC hV hG hA hB hC hD
    simpa only [covKRmExt] using h0
  | succ k ih =>
    intro Vf hVf A B C D hA hB hC hD
    letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨(G 0).toRiemannianMetric⟩
    haveI : IsContMDiffRiemannianBundle I (⊤ : ℕ∞) E (fun x : M ↦ TangentSpace I x) :=
      inferInstance
    have hTf : ∀ i : Fin k, JointField2 V (fun σ τ => Vf σ τ i.succ) := fun i => hVf i.succ
    have hZ : ∀ i : Fin k,
        JointField2 V (fun σ τ => fun y => lcOf (G σ) (Vf σ τ i.succ) y (Vf σ τ 0 y)) :=
      fun i => lcOf_familyJointField2 (I := I) (M := M) hLC hV hG (hVf i.succ) (hVf 0)
    have hWA : JointField2 V (fun σ τ => fun y => lcOf (G σ) (A σ τ) y (Vf σ τ 0 y)) :=
      lcOf_familyJointField2 (I := I) (M := M) hLC hV hG hA (hVf 0)
    have hWB : JointField2 V (fun σ τ => fun y => lcOf (G σ) (B σ τ) y (Vf σ τ 0 y)) :=
      lcOf_familyJointField2 (I := I) (M := M) hLC hV hG hB (hVf 0)
    have hWC : JointField2 V (fun σ τ => fun y => lcOf (G σ) (C σ τ) y (Vf σ τ 0 y)) :=
      lcOf_familyJointField2 (I := I) (M := M) hLC hV hG hC (hVf 0)
    have hWD : JointField2 V (fun σ τ => fun y => lcOf (G σ) (D σ τ) y (Vf σ τ 0 y)) :=
      lcOf_familyJointField2 (I := I) (M := M) hLC hV hG hD (hVf 0)
    have hUpd : ∀ i : Fin k, ∀ j' : Fin k,
        JointField2 V (fun σ τ => Function.update (fun j' : Fin k => Vf σ τ j'.succ) i
          (fun y => lcOf (G σ) (Vf σ τ i.succ) y (Vf σ τ 0 y)) j') := by
      intro i j'
      by_cases hji : j' = i
      · subst hji
        rw [show (fun σ τ => Function.update (fun j' : Fin k => Vf σ τ j'.succ) j'
              (fun y => lcOf (G σ) (Vf σ τ j'.succ) y (Vf σ τ 0 y)) j')
            = (fun σ τ => fun y => lcOf (G σ) (Vf σ τ j'.succ) y (Vf σ τ 0 y)) from by
          funext σ τ; rw [Function.update_self]]
        exact hZ j'
      · rw [show (fun σ τ => Function.update (fun j' : Fin k => Vf σ τ j'.succ) i
              (fun y => lcOf (G σ) (Vf σ τ i.succ) y (Vf σ τ 0 y)) j')
            = (fun σ τ => Vf σ τ j'.succ) from by
          funext σ τ; rw [Function.update_of_ne hji]]
        exact hTf j'
    intro p hp
    have h1 : ContMDiffAt ((𝓘(ℝ, ℝ)).prod ((𝓘(ℝ, ℝ)).prod I)) 𝓘(ℝ, ℝ)
        ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun q : ℝ × (ℝ × M) => mvfderiv I
          (fun y => covKRmExt (G q.1) k (fun j' : Fin k => Vf q.1 q.2.1 j'.succ)
            (A q.1 q.2.1) (B q.1 q.2.1) (C q.1 q.2.1) (D q.1 q.2.1) y) q.2.2
          (Vf q.1 q.2.1 0 q.2.2)) p :=
      (covK_spatialDeriv2 (I := I) (M := M) (U := W3 V) (isOpen_W3 hV)
        (Φ := fun (σ τ : ℝ) (y : M) => covKRmExt (G σ) k (fun j' : Fin k => Vf σ τ j'.succ)
          (A σ τ) (B σ τ) (C σ τ) (D σ τ) y)
        (ih (fun σ τ j' => Vf σ τ j'.succ) hTf A B C D hA hB hC hD)
        (X := fun σ τ y => Vf σ τ 0 y) (hVf 0)).contMDiffAt ((isOpen_W3 hV).mem_nhds hp)
    have h2 : ContMDiffAt ((𝓘(ℝ, ℝ)).prod ((𝓘(ℝ, ℝ)).prod I)) 𝓘(ℝ, ℝ)
        ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun q : ℝ × (ℝ × M) => ∑ i : Fin k, covKRmExt (G q.1) k
          (Function.update (fun j' : Fin k => Vf q.1 q.2.1 j'.succ) i
            (fun y => lcOf (G q.1) (Vf q.1 q.2.1 i.succ) y (Vf q.1 q.2.1 0 y)))
          (A q.1 q.2.1) (B q.1 q.2.1) (C q.1 q.2.1) (D q.1 q.2.1) q.2.2) p := by
      refine ContMDiffAt.sum (fun i _ => ?_)
      exact (ih (fun σ τ => Function.update (fun j' : Fin k => Vf σ τ j'.succ) i
        (fun y => lcOf (G σ) (Vf σ τ i.succ) y (Vf σ τ 0 y))) (hUpd i) A B C D
        hA hB hC hD).contMDiffAt ((isOpen_W3 hV).mem_nhds hp)
    have h3 : ContMDiffAt ((𝓘(ℝ, ℝ)).prod ((𝓘(ℝ, ℝ)).prod I)) 𝓘(ℝ, ℝ)
        ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun q : ℝ × (ℝ × M) => covKRmExt (G q.1) k
          (fun j' : Fin k => Vf q.1 q.2.1 j'.succ)
          (fun y => lcOf (G q.1) (A q.1 q.2.1) y (Vf q.1 q.2.1 0 y))
          (B q.1 q.2.1) (C q.1 q.2.1) (D q.1 q.2.1) q.2.2) p :=
      (ih (fun σ τ j' => Vf σ τ j'.succ) hTf
        (fun σ τ y => lcOf (G σ) (A σ τ) y (Vf σ τ 0 y)) B C D hWA hB hC hD
        ).contMDiffAt ((isOpen_W3 hV).mem_nhds hp)
    have h4 : ContMDiffAt ((𝓘(ℝ, ℝ)).prod ((𝓘(ℝ, ℝ)).prod I)) 𝓘(ℝ, ℝ)
        ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun q : ℝ × (ℝ × M) => covKRmExt (G q.1) k
          (fun j' : Fin k => Vf q.1 q.2.1 j'.succ)
          (A q.1 q.2.1)
          (fun y => lcOf (G q.1) (B q.1 q.2.1) y (Vf q.1 q.2.1 0 y))
          (C q.1 q.2.1) (D q.1 q.2.1) q.2.2) p :=
      (ih (fun σ τ j' => Vf σ τ j'.succ) hTf A
        (fun σ τ y => lcOf (G σ) (B σ τ) y (Vf σ τ 0 y)) C D hA hWB hC hD
        ).contMDiffAt ((isOpen_W3 hV).mem_nhds hp)
    have h5 : ContMDiffAt ((𝓘(ℝ, ℝ)).prod ((𝓘(ℝ, ℝ)).prod I)) 𝓘(ℝ, ℝ)
        ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun q : ℝ × (ℝ × M) => covKRmExt (G q.1) k
          (fun j' : Fin k => Vf q.1 q.2.1 j'.succ)
          (A q.1 q.2.1) (B q.1 q.2.1)
          (fun y => lcOf (G q.1) (C q.1 q.2.1) y (Vf q.1 q.2.1 0 y))
          (D q.1 q.2.1) q.2.2) p :=
      (ih (fun σ τ j' => Vf σ τ j'.succ) hTf A B
        (fun σ τ y => lcOf (G σ) (C σ τ) y (Vf σ τ 0 y)) D hA hB hWC hD
        ).contMDiffAt ((isOpen_W3 hV).mem_nhds hp)
    have h6 : ContMDiffAt ((𝓘(ℝ, ℝ)).prod ((𝓘(ℝ, ℝ)).prod I)) 𝓘(ℝ, ℝ)
        ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun q : ℝ × (ℝ × M) => covKRmExt (G q.1) k
          (fun j' : Fin k => Vf q.1 q.2.1 j'.succ)
          (A q.1 q.2.1) (B q.1 q.2.1) (C q.1 q.2.1)
          (fun y => lcOf (G q.1) (D q.1 q.2.1) y (Vf q.1 q.2.1 0 y)) q.2.2) p :=
      (ih (fun σ τ j' => Vf σ τ j'.succ) hTf A B C
        (fun σ τ y => lcOf (G σ) (D σ τ) y (Vf σ τ 0 y)) hA hB hC hWD
        ).contMDiffAt ((isOpen_W3 hV).mem_nhds hp)
    have hfun : (fun q : ℝ × (ℝ × M) => covKRmExt (G q.1) (k + 1) (Vf q.1 q.2.1)
          (A q.1 q.2.1) (B q.1 q.2.1) (C q.1 q.2.1) (D q.1 q.2.1) q.2.2)
        = fun q : ℝ × (ℝ × M) =>
            mvfderiv I (fun y => covKRmExt (G q.1) k
              (fun j' : Fin k => Vf q.1 q.2.1 j'.succ)
              (A q.1 q.2.1) (B q.1 q.2.1) (C q.1 q.2.1) (D q.1 q.2.1) y) q.2.2
              (Vf q.1 q.2.1 0 q.2.2)
            - (∑ i : Fin k, covKRmExt (G q.1) k
                (Function.update (fun j' : Fin k => Vf q.1 q.2.1 j'.succ) i
                  (fun y => lcOf (G q.1) (Vf q.1 q.2.1 i.succ) y (Vf q.1 q.2.1 0 y)))
                (A q.1 q.2.1) (B q.1 q.2.1) (C q.1 q.2.1) (D q.1 q.2.1) q.2.2)
            - covKRmExt (G q.1) k (fun j' : Fin k => Vf q.1 q.2.1 j'.succ)
                (fun y => lcOf (G q.1) (A q.1 q.2.1) y (Vf q.1 q.2.1 0 y))
                (B q.1 q.2.1) (C q.1 q.2.1) (D q.1 q.2.1) q.2.2
            - covKRmExt (G q.1) k (fun j' : Fin k => Vf q.1 q.2.1 j'.succ) (A q.1 q.2.1)
                (fun y => lcOf (G q.1) (B q.1 q.2.1) y (Vf q.1 q.2.1 0 y))
                (C q.1 q.2.1) (D q.1 q.2.1) q.2.2
            - covKRmExt (G q.1) k (fun j' : Fin k => Vf q.1 q.2.1 j'.succ) (A q.1 q.2.1)
                (B q.1 q.2.1)
                (fun y => lcOf (G q.1) (C q.1 q.2.1) y (Vf q.1 q.2.1 0 y))
                (D q.1 q.2.1) q.2.2
            - covKRmExt (G q.1) k (fun j' : Fin k => Vf q.1 q.2.1 j'.succ) (A q.1 q.2.1)
                (B q.1 q.2.1) (C q.1 q.2.1)
                (fun y => lcOf (G q.1) (D q.1 q.2.1) y (Vf q.1 q.2.1 0 y)) q.2.2 := by
      funext q
      simp only [covKRmExt]
    rw [hfun]
    exact (((((h1.sub h2).sub h3).sub h4).sub h5).sub h6).mono (Set.subset_univ (W3 V))

end Work.Diff.EXT.evolX
