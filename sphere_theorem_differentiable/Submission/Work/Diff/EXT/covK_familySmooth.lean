import Mathlib
import Submission.Work.Diff.EXT.curvDefs
import Submission.Work.Diff.EXT.covK_spatialDeriv
import Submission.Work.Diff.EXT.covK_lcOfFamily
import Submission.Work.Diff.EXT.covK_metric_pairing_family
import Submission.Work.Diff.GE.norms_defs
import Submission.Work.Diff.GE.rmP_eq_sum_rmC4
import Submission.Work.Diff.GE.rmP_jointSmooth

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.EXT

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology
open Bundle ContDiff Set VectorField CovariantDerivative Metric

/-! ## Local (pointwise) form of the chart-smoothness chain of `Work.Diff.GE`

The chain in `Submission/Work/Diff/GE/rmP_jointSmooth.lean` proves the joint smoothness of the
chart quantities `mComp`/`GramInv`/`koszulPair`/`chrB`/`dB`/`cCurv`/`cRm`/`rmC4` for a metric
family jointly smooth on a *cylinder* `J ×ˢ univ` (`JointSmooth G J`, `IsOpen J`, `t₀ ∈ J`).  Here
we restate the whole chain with the *pointwise* hypothesis `MetSmoothAt G t₀ x₀` (the metric
section is `C^∞` at the single point `(t₀, x₀)`), which is what a family jointly smooth on an
arbitrary open `V` provides at each of its points (`JointMet.metSmoothAt`).  All the proofs are
those of the cylinder chain with the `hJ`/`ht₀` unpacking deleted.
-/

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H]

/-- The family of metrics `G` is jointly smooth at the point `(t₀, x₀)`, i.e. the section
`p ↦ ⟨p.2, (G p.1).inner p.2⟩` of the bundle of bilinear forms over `M` (pulled back along
`Prod.snd`) is `C^∞` at `(t₀, x₀)`. -/
abbrev MetSmoothAt (I : ModelWithCorners ℝ E H) (M : Type*) [TopologicalSpace M]
    [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]
    (G : ℝ → Submission.Diff.SMet I M) (t₀ : ℝ) (x₀ : M) : Prop :=
  ContMDiffAt ((𝓘(ℝ, ℝ)).prod I) (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
    (fun p : ℝ × M ↦ TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
      (E := fun x : M ↦ TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) p.2
      ((G p.1).inner p.2)) (t₀, x₀)

/-! ## The chart formula for `∇` with hypotheses only at a point

`Submission.ChartCurv.cov_eq_frameVector_chartCoord` / `coordFun_cov` state the coordinate formula
for `∇` for *globally* smooth fields.  For families jointly smooth on an open set only the
pointwise form is available, so we restate those two lemmas with `SmoothFieldAt` hypotheses (the
proofs are those of the original lemmas, which use `hW` only through `hW p`). -/

section ChartFormula

variable
  {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]
  [T2Space M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I (⊤ : ℕ∞) E (fun x : M ↦ TangentSpace I x)]
  {cov : CovariantDerivative I E (TangentSpace I (M := M))}
  [cov.ContMDiffCovariantDerivative (⊤ : ℕ∞)]

/-- The coordinate function of a field smooth at `p` is smooth at `p` (pointwise form of
`Submission.ChartCurv.contMDiffAt_coordFun`). -/
theorem contMDiffAt_coordFun_at (x₀ : M) {W : Π y : M, TangentSpace I y} {p : M}
    (hW : ContMDiffAt I I.tangent ∞ (T% W) p) (hp : p ∈ (chartAt H x₀).source) :
    ContMDiffAt I 𝓘(ℝ, E) ∞ (Submission.ChartCurv.coordFun x₀ W) p := by
  have hbase : p ∈ (trivializationAt E (TangentSpace I) x₀).baseSet := by
    rw [TangentBundle.trivializationAt_baseSet]
    exact hp
  have h1 : ContMDiffWithinAt I 𝓘(ℝ, E) ∞
      (fun q : M => ((trivializationAt E (TangentSpace I) x₀) ⟨q, W q⟩).2)
      (chartAt H x₀).source p :=
    ((Trivialization.contMDiffWithinAt_section (s := W) (chartAt H x₀).source hbase).1
      hW.contMDiffWithinAt)
  refine ((h1.congr ?_ ?_).contMDiffAt ((chartAt H x₀).open_source.mem_nhds hp))
  · intro y hy
    exact Trivialization.continuousLinearMapAt_apply_of_mem ℝ
      (trivializationAt E (TangentSpace I) x₀)
      (by rw [TangentBundle.trivializationAt_baseSet]; exact hy) (W y)
  · exact Trivialization.continuousLinearMapAt_apply_of_mem ℝ
      (trivializationAt E (TangentSpace I) x₀) hbase (W p)

/-- **The chart formula for `∇`, local hypotheses** (pointwise form of
`Submission.ChartCurv.cov_eq_frameVector_chartCoord`).  The proof is that of the original lemma,
which uses its hypothesis `hW : CMDiff ∞ (T% W)` only through `hW p`. -/
theorem cov_eq_frameVector_chartCoord_at {W : Π x : M, TangentSpace I x} {c : M → E} {x₀ p : M}
    (hp : p ∈ (chartAt H x₀).source) (hW : ContMDiffAt I I.tangent ∞ (T% W) p)
    (hc : ContMDiffAt I 𝓘(ℝ, E) ∞ c p)
    (heq : W =ᶠ[𝓝 p] fun q => Submission.Geodesic.frameVector (I := I) x₀ q (c q)) (v : E) :
    cov W p (Submission.Geodesic.frameVector (I := I) x₀ p v)
      = Submission.Geodesic.frameVector (I := I) x₀ p
          (mvfderiv I c p (Submission.Geodesic.frameVector (I := I) x₀ p v)
            + Submission.ChartCurv.chrB cov x₀ p (c p) v) := by
  classical
  -- the frame field of `c` as a sum over the basis
  have hfr : (fun q : M => Submission.Geodesic.frameVector (I := I) x₀ q (c q))
      = (fun q : M => ∑ i, (Module.finBasis ℝ E).coord i (c q) •
          Submission.Geodesic.frameSection (I := I) x₀ (Module.finBasis ℝ E i) q) := by
    funext q
    show Submission.Geodesic.frameVector (I := I) x₀ q (c q)
      = ∑ i, (Module.finBasis ℝ E).coord i (c q) •
          Submission.Geodesic.frameSection (I := I) x₀ (Module.finBasis ℝ E i) q
    conv_lhs => rw [← Submission.ChartCurv.sum_coord_smul_eq (E := E) (c q)]
    rw [Submission.Geodesic.frameVector_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    show (Module.finBasis ℝ E).coord i (c q) •
        Submission.Geodesic.frameVector (I := I) x₀ q (Module.finBasis ℝ E i)
      = (Module.finBasis ℝ E).coord i (c q) •
          Submission.Geodesic.frameSection (I := I) x₀ (Module.finBasis ℝ E i) q
    rw [show Submission.Geodesic.frameSection (I := I) x₀ (Module.finBasis ℝ E i) q
        = Submission.Geodesic.frameVector (I := I) x₀ q (Module.finBasis ℝ E i) from rfl]
  have hkey :=
    Commons.Geometry.Manifold.VectorBundle.CovariantDerivative.cov_eq_sum_of_eventuallyEq_pointwise
      (cov := cov) Finset.univ
      (fun i (q : M) => (Module.finBasis ℝ E).coord i (c q))
      (fun i (q : M) => Submission.Geodesic.frameSection (I := I) x₀ (Module.finBasis ℝ E i) q)
      (Z := W) (x := p) (v := Submission.Geodesic.frameVector (I := I) x₀ p v) hW
      (fun i => Submission.Geodesic.contMDiffAt_frameSection (I := I) x₀
        (Module.finBasis ℝ E i) hp)
      (fun i => (((Module.finBasis ℝ E).coord i : E →ₗ[ℝ] ℝ).toContinuousLinearMap).contMDiffAt.comp
        p hc)
      (heq.trans (Filter.Eventually.of_forall (fun q => congrFun hfr q)))
  rw [hkey]
  -- identify the two sums
  have hsum1 : (∑ i, (Module.finBasis ℝ E).coord i (c p) •
        cov (Submission.Geodesic.frameSection (I := I) x₀ (Module.finBasis ℝ E i)) p
          (Submission.Geodesic.frameVector (I := I) x₀ p v))
      = Submission.Geodesic.frameVector (I := I) x₀ p
          (Submission.ChartCurv.chrB cov x₀ p (c p) v) := by
    have h1 : ∀ i, cov (Submission.Geodesic.frameSection (I := I) x₀ (Module.finBasis ℝ E i)) p
        (Submission.Geodesic.frameVector (I := I) x₀ p v)
        = Submission.Geodesic.frameVector (I := I) x₀ p
            (Submission.Geodesic.christoffelEval cov x₀ p (Module.finBasis ℝ E i)
              (Submission.Geodesic.frameVector (I := I) x₀ p v)) :=
      fun i => Submission.Geodesic.cov_frameSection_eq cov x₀ p (Module.finBasis ℝ E i)
        (Submission.Geodesic.frameVector (I := I) x₀ p v) hp
    simp only [h1]
    rw [← Submission.Geodesic.frameVector_sum, ← Submission.Geodesic.christoffelEval_sum_left
      Finset.univ cov x₀ p (fun i => (Module.finBasis ℝ E).coord i (c p))
      (fun i => Module.finBasis ℝ E i) (Submission.Geodesic.frameVector (I := I) x₀ p v) hp]
    congr 1
    rw [Submission.ChartCurv.chrB_apply, Submission.ChartCurv.sum_coord_smul_eq]
  have hsum2 : (∑ i, mvfderiv I (fun q : M => (Module.finBasis ℝ E).coord i (c q)) p
        (Submission.Geodesic.frameVector (I := I) x₀ p v) •
          Submission.Geodesic.frameSection (I := I) x₀ (Module.finBasis ℝ E i) p)
      = Submission.Geodesic.frameVector (I := I) x₀ p
          (mvfderiv I c p (Submission.Geodesic.frameVector (I := I) x₀ p v)) := by
    simp only [Submission.Geodesic.frameSection_eq_frameVector]
    rw [← Submission.Geodesic.frameVector_sum, Submission.ChartCurv.mvfderiv_eq_sum_coord
      (I := I) (hc.mdifferentiableAt (by simp))]
  rw [hsum1, hsum2, ← Submission.Geodesic.frameVector_add, add_comm]

/-- **The coordinate formula for `∇`, local hypotheses** (pointwise form of
`Submission.ChartCurv.coordFun_cov`). -/
theorem coordFun_cov_at (x₀ : M) {W T : Π x : M, TangentSpace I x} {p : M}
    (hW : ContMDiffAt I I.tangent ∞ (T% W) p) (hT : ContMDiffAt I I.tangent ∞ (T% T) p)
    (hp : p ∈ (chartAt H x₀).source) :
    Submission.ChartCurv.coordFun x₀ (fun y : M => cov W y (T y)) p
      = mvfderiv I (Submission.ChartCurv.coordFun x₀ W) p (T p)
        + Submission.ChartCurv.chrB cov x₀ p (Submission.ChartCurv.coordFun x₀ W p)
            (Submission.ChartCurv.coordFun x₀ T p) := by
  have h := cov_eq_frameVector_chartCoord_at (cov := cov) (x₀ := x₀)
    (W := W) (c := Submission.ChartCurv.coordFun x₀ W) hp hW
    (contMDiffAt_coordFun_at (I := I) (M := M) x₀ hW hp)
    ?_ (Submission.ChartCurv.coordFun x₀ T p)
  · rw [Submission.ChartCurv.frameVector_coordFun_eq (x₀ := x₀) hp] at h
    conv_lhs => rw [Submission.ChartCurv.coordFun_apply, h]
    exact Submission.ChartCurv.coordFun_frameVector (x₀ := x₀) hp _
  · filter_upwards [((chartAt H x₀).open_source).mem_nhds hp] with q hq
    exact (Submission.ChartCurv.frameVector_coordFun_eq (x₀ := x₀) hq).symm


/-- **Coordinates of a jointly smooth family (on the set).**  The chart coordinates
`q ↦ coordFun x₀ (A q.1) q.2` of a family `A` of tangent fields jointly smooth on `V` are jointly
smooth on `V ∩ (univ ×ˢ (chartAt H x₀).source)`, where the coordinates make sense.

This is the "base map" form of the section criterion, via
`Trivialization.contMDiffWithinAt_iff` for the trivialisation `trivializationAt E (TangentSpace I)
x₀` (which has base set `(chartAt H x₀).source`). -/
theorem contMDiffOn_coordFun_of_jointField {A : ℝ → TField (I := I) (M := M)} {V : Set (ℝ × M)}
    (hA : JointField A V) (x₀ : M) :
    ContMDiffOn ((𝓘(ℝ, ℝ)).prod I) 𝓘(ℝ, E) ∞
      (fun q : ℝ × M => Submission.ChartCurv.coordFun x₀ (A q.1) q.2)
      (V ∩ (univ ×ˢ (chartAt H x₀).source)) := by
  set triv := trivializationAt E (TangentSpace I) x₀ with htriv
  set W : Set (ℝ × M) := V ∩ (univ ×ˢ (chartAt H x₀).source) with hWdef
  intro p hp
  rw [hWdef] at hp
  obtain ⟨hpV, -, hpsrc⟩ := hp
  have hbase : p.2 ∈ triv.baseSet := by
    rw [htriv, TangentBundle.trivializationAt_baseSet]; exact hpsrc
  have hsec : ContMDiffWithinAt ((𝓘(ℝ, ℝ)).prod I) (I.prod 𝓘(ℝ, E)) ∞
      (fun q : ℝ × M => (⟨q.2, A q.1 q.2⟩ : TangentBundle I M)) W p :=
    (hA p hpV).mono inter_subset_left
  have he : (⟨p.2, A p.1 p.2⟩ : TangentBundle I M) ∈ triv.source :=
    triv.mem_source.mpr hbase
  have h2 := ((Trivialization.contMDiffWithinAt_iff (e := triv) (f := fun q : ℝ × M =>
      (⟨q.2, A q.1 q.2⟩ : TangentBundle I M)) (s := W) (x₀ := p) he).mp hsec).2
  refine h2.congr_of_eventuallyEq ?_ ?_
  · filter_upwards [self_mem_nhdsWithin] with q hq
    rw [hWdef] at hq
    obtain ⟨-, -, hqsrc⟩ := hq
    show Submission.ChartCurv.coordFun x₀ (A q.1) q.2 = (triv ⟨q.2, A q.1 q.2⟩).2
    rw [Submission.ChartCurv.coordFun_apply]
    exact Trivialization.continuousLinearMapAt_apply_of_mem ℝ triv
      (by rw [htriv, TangentBundle.trivializationAt_baseSet]; exact hqsrc) (A q.1 q.2)
  · show Submission.ChartCurv.coordFun x₀ (A p.1) p.2 = (triv ⟨p.2, A p.1 p.2⟩).2
    rw [Submission.ChartCurv.coordFun_apply]
    exact Trivialization.continuousLinearMapAt_apply_of_mem ℝ triv hbase (A p.1 p.2)

/-- **The section criterion.**  A family of tangent fields is jointly smooth on the open set `V` as
soon as its chart coordinates `q ↦ coordFun x₀ (A q.1) q.2` are jointly smooth and `q.2` stays in
the chart source of `x₀` (the trivialisation's base set) throughout `V`. -/
theorem jointField_of_coordFun {A : ℝ → TField (I := I) (M := M)} {V : Set (ℝ × M)}
    {x₀ : M} (hsrc : ∀ p ∈ V, p.2 ∈ (chartAt H x₀).source)
    (hcoord : ∀ p ∈ V, ContMDiffAt ((𝓘(ℝ, ℝ)).prod I) 𝓘(ℝ, E) ∞
      (fun q : ℝ × M => Submission.ChartCurv.coordFun x₀ (A q.1) q.2) p) :
    JointField A V := by
  set triv := trivializationAt E (TangentSpace I) x₀ with htriv
  intro p hp
  have hbase : p.2 ∈ triv.baseSet := by
    rw [htriv, TangentBundle.trivializationAt_baseSet]; exact hsrc p hp
  have he : (⟨p.2, A p.1 p.2⟩ : TangentBundle I M) ∈ triv.source :=
    triv.mem_source.mpr hbase
  have hcoord' : ContMDiffWithinAt ((𝓘(ℝ, ℝ)).prod I) 𝓘(ℝ, E) ∞
      (fun q : ℝ × M => Submission.ChartCurv.coordFun x₀ (A q.1) q.2) V p :=
    (hcoord p hp).contMDiffWithinAt
  have hcoord'' : ContMDiffWithinAt ((𝓘(ℝ, ℝ)).prod I) 𝓘(ℝ, E) ∞
      (fun q : ℝ × M => (triv ⟨q.2, A q.1 q.2⟩).2) V p := by
    refine hcoord'.congr_of_eventuallyEq ?_ ?_
    · filter_upwards [self_mem_nhdsWithin] with q hq
      show (triv ⟨q.2, A q.1 q.2⟩).2 = Submission.ChartCurv.coordFun x₀ (A q.1) q.2
      rw [Submission.ChartCurv.coordFun_apply]
      exact (Trivialization.continuousLinearMapAt_apply_of_mem ℝ triv
        (by rw [htriv, TangentBundle.trivializationAt_baseSet]; exact hsrc q hq) (A q.1 q.2)).symm
    · show (triv ⟨p.2, A p.1 p.2⟩).2 = Submission.ChartCurv.coordFun x₀ (A p.1) p.2
      rw [Submission.ChartCurv.coordFun_apply]
      exact (Trivialization.continuousLinearMapAt_apply_of_mem ℝ triv hbase (A p.1 p.2)).symm
  exact ((Trivialization.contMDiffWithinAt_iff (e := triv) (f := fun q : ℝ × M =>
    (⟨q.2, A q.1 q.2⟩ : TangentBundle I M)) (s := V) (x₀ := p) he).mpr
      ⟨contMDiffWithinAt_snd, hcoord''⟩)

/-- **Coordinates of a jointly smooth family, pointwise form.** -/
theorem coordFun_jointAt_of_jointField {A : ℝ → TField (I := I) (M := M)} {V : Set (ℝ × M)}
    (hV : IsOpen V) (hA : JointField A V) {x₀ : M} {p : ℝ × M} (hp : p ∈ V)
    (hsrc : p.2 ∈ (chartAt H x₀).source) :
    ContMDiffAt ((𝓘(ℝ, ℝ)).prod I) 𝓘(ℝ, E) ∞
      (fun q : ℝ × M => Submission.ChartCurv.coordFun x₀ (A q.1) q.2) p :=
  ((contMDiffOn_coordFun_of_jointField (I := I) (M := M) hA x₀) p
    ⟨hp, mem_univ p.1, hsrc⟩).contMDiffAt
    (Filter.inter_mem (hV.mem_nhds hp) (prod_mem_nhds Filter.univ_mem
      ((chartAt H x₀).open_source.mem_nhds hsrc)))

end ChartFormula

section Chain

variable
  {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]
  [I.Boundaryless] [T2Space M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I (⊤ : ℕ∞) E (fun x : M ↦ TangentSpace I x)]

/-- A metric family jointly smooth on the open set `V` is `MetSmoothAt` at each of its points. -/
theorem JointMet.metSmoothAt {G : ℝ → Submission.Diff.SMet I M} {V : Set (ℝ × M)}
    (hV : IsOpen V) (hG : JointMet G V) {p : ℝ × M} (hp : p ∈ V) :
    MetSmoothAt (I := I) (M := M) G p.1 p.2 :=
  hG.contMDiffAt (hV.mem_nhds hp)

/-- **The metric pairing of two fields smooth at a point, for a family smooth at that point.** -/
theorem metric_pairing_at {G : ℝ → Submission.Diff.SMet I M} {t₀ : ℝ} {x₀ : M}
    (hG : MetSmoothAt (I := I) (M := M) G t₀ x₀) {Y Z : Π y : M, TangentSpace I y}
    (hY : SmoothFieldAt I M Y x₀) (hZ : SmoothFieldAt I M Z x₀) :
    JointSmoothAt I M (fun p : ℝ × M ↦ (G p.1).inner p.2 (Y p.2) (Z p.2)) t₀ x₀ := by
  have hYc : ContMDiffAt ((𝓘(ℝ, ℝ)).prod I) (I.prod 𝓘(ℝ, E)) ∞
      ((T% Y) ∘ (Prod.snd : ℝ × M → M)) (t₀, x₀) :=
    hY.comp (t₀, x₀) contMDiffAt_snd
  have hZc : ContMDiffAt ((𝓘(ℝ, ℝ)).prod I) (I.prod 𝓘(ℝ, E)) ∞
      ((T% Z) ∘ (Prod.snd : ℝ × M → M)) (t₀, x₀) :=
    hZ.comp (t₀, x₀) contMDiffAt_snd
  have hmain : ContMDiffWithinAt ((𝓘(ℝ, ℝ)).prod I) (I.prod 𝓘(ℝ, ℝ)) ∞
      (fun m : ℝ × M => TotalSpace.mk' ℝ (E := Bundle.Trivial M ℝ) (Prod.snd m)
        ((G m.1).inner (Prod.snd m) (Y (Prod.snd m)) (Z (Prod.snd m)))) univ (t₀, x₀) :=
    ContMDiffWithinAt.clm_bundle_apply₂ (𝕜 := ℝ) (B := M) (F₁ := E) (F₂ := E) (F₃ := ℝ)
      (E₁ := fun x : M => TangentSpace I x) (E₂ := fun x : M => TangentSpace I x)
      (E₃ := Bundle.Trivial M ℝ) (b := fun m : ℝ × M => Prod.snd m)
      (v := fun m : ℝ × M => Y (Prod.snd m)) (w := fun m : ℝ × M => Z (Prod.snd m))
      (ψ := fun m : ℝ × M => (G m.1).inner (Prod.snd m)) (s := univ) (x := (t₀, x₀))
      hG hYc hZc
  simp only [contMDiffWithinAt_totalSpace] at hmain
  exact hmain.2

/-- The coordinate frame vectors of the chart at `x₀` are smooth sections at `x₀`. -/
theorem smoothFieldAt_cFrameAt (x₀ : M) (i : Fin (Module.finrank ℝ E)) :
    SmoothFieldAt I M (Work.Diff.GE.cFrame (I := I) x₀ i) x₀ := by
  have h := Work.Diff.EXT.contMDiffAt_frameVector (I := I) x₀
    (Work.Diff.GE.cBasis (E := E) i) (mem_chart_source H x₀)
  simpa only [Work.Diff.EXT.SmoothFieldAt, Work.Diff.GE.cFrame,
    Submission.Geodesic.frameSection_eq_frameVector, Submission.Geodesic.frameVector] using h

/-- **The components of a family of metrics in the coordinate frame.** -/
theorem mComp_at {G : ℝ → Submission.Diff.SMet I M} {t₀ : ℝ} {x₀ : M}
    (hG : MetSmoothAt (I := I) (M := M) G t₀ x₀)
    (i j : Fin (Module.finrank ℝ E)) :
    JointSmoothAt I M (fun p : ℝ × M ↦ Work.Diff.GE.mComp (I := I) G x₀ i j p.1 p.2) t₀ x₀ := by
  have h := metric_pairing_at (I := I) (M := M) (G := G) hG
    (smoothFieldAt_cFrameAt (I := I) (M := M) x₀ i) (smoothFieldAt_cFrameAt (I := I) (M := M) x₀ j)
  simpa only [Work.Diff.GE.mComp] using h

/-- **The inverse Gram matrix of the coordinate frame.** -/
theorem gramInv_at {G : ℝ → Submission.Diff.SMet I M} {t₀ : ℝ} {x₀ : M}
    (hG : MetSmoothAt (I := I) (M := M) G t₀ x₀) (k m : Fin (Module.finrank ℝ E)) :
    JointSmoothAt I M
      (fun p : ℝ × M ↦ Work.Diff.GE.GramInv (I := I) G x₀ p.1 p.2 k m) t₀ x₀ := by
  classical
  have hentry : ∀ i j : Fin (Module.finrank ℝ E),
      JointSmoothAt I M (fun p : ℝ × M => Work.Diff.GE.GramM (I := I) G x₀ p.1 p.2 i j) t₀ x₀ := by
    intro i j
    have h := mComp_at (I := I) (M := M) (G := G) hG i j
    simpa only [Work.Diff.GE.GramM, Work.Diff.GE.mComp] using h
  have hMx : JointSmoothAt I M
      (fun p : ℝ × M => fun i j => Work.Diff.GE.GramM (I := I) G x₀ p.1 p.2 i j) t₀ x₀ := by
    show ContMDiffAt _ _ _ (fun p : ℝ × M => fun i j =>
      Work.Diff.GE.GramM (I := I) G x₀ p.1 p.2 i j) _
    rw [contMDiffAt_pi_space]
    intro i
    rw [contMDiffAt_pi_space]
    exact hentry i
  have hdet : (Matrix.of (fun i j => Work.Diff.GE.GramM (I := I) G x₀ t₀ x₀ i j)).det ≠ 0 := by
    have hnd : (Work.Diff.GE.CGramInv.gramBil (I := I) G x₀ x₀ t₀).Nondegenerate :=
      Work.Diff.GE.CGramInv.gramBil_nondegenerate (I := I) G x₀ (mem_chart_source H x₀) t₀
    have h := (LinearMap.BilinForm.nondegenerate_iff_det_ne_zero
      (Work.Diff.GE.cBasis (E := E))).mp hnd
    rwa [← Work.Diff.GE.CGramInv.GramM_eq_toMatrix (I := I) G x₀ x₀ t₀] at h
  have hinv := Work.Diff.EXT.contMDiffAt_matrix_inv (I := I) (M := M)
    (n := Module.finrank ℝ E)
    (Mx := fun p : ℝ × M => fun i j => Work.Diff.GE.GramM (I := I) G x₀ p.1 p.2 i j) hMx hdet
  have hg : ContDiffAt ℝ ∞
      (fun A : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → ℝ => A k m)
      ((fun p : ℝ × M => fun i j =>
        ((Matrix.of (fun i j => Work.Diff.GE.GramM (I := I) G x₀ p.1 p.2 i j))⁻¹) i j)
        (t₀, x₀)) := by
    fun_prop
  exact hg.comp_contMDiffAt hinv

/-- **The lowered Christoffel pairings of the coordinate frame.** -/
theorem koszulPair_at {G : ℝ → Submission.Diff.SMet I M} {t₀ : ℝ} {x₀ : M}
    (hG : MetSmoothAt (I := I) (M := M) G t₀ x₀)
    (a b c : Fin (Module.finrank ℝ E)) :
    JointSmoothAt I M
      (fun p : ℝ × M ↦ Work.Diff.GE.koszulPair (I := I) G x₀ a b c p.1 p.2) t₀ x₀ := by
  have h1 : JointSmoothAt I M
      (fun p : ℝ × M ↦ mvfderiv I (fun y' ↦ Work.Diff.GE.mComp (I := I) G x₀ b c p.1 y') p.2
        (Work.Diff.GE.cFrame (I := I) x₀ a p.2)) t₀ x₀ :=
    Work.Diff.GE.mvfderiv_jointSmooth_frame (I := I) (F := ℝ)
      (Φ := fun p : ℝ × M ↦ Work.Diff.GE.mComp (I := I) G x₀ b c p.1 p.2)
      (mComp_at (I := I) (M := M) (G := G) hG b c) x₀ a (mem_chart_source H x₀)
  have h2 : JointSmoothAt I M
      (fun p : ℝ × M ↦ mvfderiv I (fun y' ↦ Work.Diff.GE.mComp (I := I) G x₀ c a p.1 y') p.2
        (Work.Diff.GE.cFrame (I := I) x₀ b p.2)) t₀ x₀ :=
    Work.Diff.GE.mvfderiv_jointSmooth_frame (I := I) (F := ℝ)
      (Φ := fun p : ℝ × M ↦ Work.Diff.GE.mComp (I := I) G x₀ c a p.1 p.2)
      (mComp_at (I := I) (M := M) (G := G) hG c a) x₀ b (mem_chart_source H x₀)
  have h3 : JointSmoothAt I M
      (fun p : ℝ × M ↦ mvfderiv I (fun y' ↦ Work.Diff.GE.mComp (I := I) G x₀ a b p.1 y') p.2
        (Work.Diff.GE.cFrame (I := I) x₀ c p.2)) t₀ x₀ :=
    Work.Diff.GE.mvfderiv_jointSmooth_frame (I := I) (F := ℝ)
      (Φ := fun p : ℝ × M ↦ Work.Diff.GE.mComp (I := I) G x₀ a b p.1 p.2)
      (mComp_at (I := I) (M := M) (G := G) hG a b) x₀ c (mem_chart_source H x₀)
  have hmain : JointSmoothAt I M
      (fun p : ℝ × M ↦ (1 / 2 : ℝ) *
        (mvfderiv I (fun y' ↦ Work.Diff.GE.mComp (I := I) G x₀ b c p.1 y') p.2
            (Work.Diff.GE.cFrame (I := I) x₀ a p.2)
          + mvfderiv I (fun y' ↦ Work.Diff.GE.mComp (I := I) G x₀ c a p.1 y') p.2
              (Work.Diff.GE.cFrame (I := I) x₀ b p.2)
          - mvfderiv I (fun y' ↦ Work.Diff.GE.mComp (I := I) G x₀ a b p.1 y') p.2
              (Work.Diff.GE.cFrame (I := I) x₀ c p.2))) t₀ x₀ :=
    (contMDiffAt_const (c := (1 / 2 : ℝ))).mul ((h1.add h2).sub h3)
  simpa only [Work.Diff.GE.koszulPair, Work.Diff.GE.mComp, Work.Diff.GE.cFrame,
    Submission.Geodesic.frameSection_eq_frameVector] using hmain

/-- **The coordinate derivative of a lowered Christoffel pairing.** -/
theorem dOp_koszulPair_at {G : ℝ → Submission.Diff.SMet I M} {t₀ : ℝ} {x₀ : M}
    (hG : MetSmoothAt (I := I) (M := M) G t₀ x₀)
    (i j l k : Fin (Module.finrank ℝ E)) :
    JointSmoothAt I M
      (fun p : ℝ × M ↦ Work.Diff.GE.dOp (I := I) x₀ i
        (Work.Diff.GE.koszulPair (I := I) G x₀ j l k) p.1 p.2) t₀ x₀ := by
  have h : JointSmoothAt I M
      (fun p : ℝ × M ↦ mvfderiv I
        (fun y' ↦ Work.Diff.GE.koszulPair (I := I) G x₀ j l k p.1 y') p.2
        (Work.Diff.GE.cFrame (I := I) x₀ i p.2)) t₀ x₀ :=
    Work.Diff.GE.mvfderiv_jointSmooth_frame (I := I) (F := ℝ)
      (Φ := fun p : ℝ × M ↦ Work.Diff.GE.koszulPair (I := I) G x₀ j l k p.1 p.2)
      (koszulPair_at (I := I) (M := M) (G := G) hG j l k) x₀ i (mem_chart_source H x₀)
  simpa only [Work.Diff.GE.dOp] using h

/-- **The Christoffel symbol in coordinates.** -/
theorem chrB_at {G : ℝ → Submission.Diff.SMet I M} {t₀ : ℝ} {x₀ : M}
    (hG : MetSmoothAt (I := I) (M := M) G t₀ x₀)
    (a b : Fin (Module.finrank ℝ E)) :
    JointSmoothAt I M
      (fun p : ℝ × M ↦ Submission.ChartCurv.chrB (Submission.Diff.lcOf (G p.1)) x₀ p.2
        (Work.Diff.GE.cBasis (E := E) a) (Work.Diff.GE.cBasis (E := E) b)) t₀ x₀ := by
  have hex : JointSmoothAt I M
      (fun p : ℝ × M ↦ ∑ k, (Matrix.mulVec (Work.Diff.GE.GramInv (I := I) G x₀ p.1 p.2)
          (fun k ↦ Work.Diff.GE.koszulPair (I := I) G x₀ a b k p.1 p.2)) k
          • Work.Diff.GE.cBasis (E := E) k) t₀ x₀ := by
    refine ContMDiffAt.sum (fun k _ ↦ ?_)
    have hmv : JointSmoothAt I M
        (fun p : ℝ × M ↦ (Matrix.mulVec (Work.Diff.GE.GramInv (I := I) G x₀ p.1 p.2)
          (fun k ↦ Work.Diff.GE.koszulPair (I := I) G x₀ a b k p.1 p.2)) k) t₀ x₀ := by
      have hmv' : JointSmoothAt I M
          (fun p : ℝ × M ↦ ∑ m, Work.Diff.GE.GramInv (I := I) G x₀ p.1 p.2 k m
            * Work.Diff.GE.koszulPair (I := I) G x₀ a b m p.1 p.2) t₀ x₀ :=
        ContMDiffAt.sum (fun m _ ↦
          (gramInv_at (I := I) (M := M) (G := G) hG k m).mul
            (koszulPair_at (I := I) (M := M) (G := G) hG a b m))
      simpa only [Matrix.mulVec_apply, dotProduct, Matrix.row_apply] using hmv'
    exact (ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) (Work.Diff.GE.cBasis (E := E) k)).contMDiffAt.comp
      (t₀, x₀) hmv
  refine hex.congr_of_eventuallyEq ?_
  rw [nhds_prod_eq]
  filter_upwards [Filter.prod_mem_prod Filter.univ_mem
      ((chartAt H x₀).open_source.mem_nhds (mem_chart_source H x₀))] with p hp
  exact Work.Diff.GE.chrB_eq_sum_gramInv (I := I) G x₀ p.1 hp.2 a b

/-- **The derivative of the Christoffel symbol in the base point.** -/
theorem dB_at {G : ℝ → Submission.Diff.SMet I M} {t₀ : ℝ} {x₀ : M}
    (hG : MetSmoothAt (I := I) (M := M) G t₀ x₀)
    (v a b : Fin (Module.finrank ℝ E)) :
    JointSmoothAt I M
      (fun p : ℝ × M ↦ Submission.ChartCurv.dB (Submission.Diff.lcOf (G p.1)) x₀ p.2
        (Work.Diff.GE.cBasis (E := E) v) (Work.Diff.GE.cBasis (E := E) a)
        (Work.Diff.GE.cBasis (E := E) b)) t₀ x₀ := by
  have hchr : JointSmoothAt I M
      (fun p : ℝ × M ↦ Submission.ChartCurv.chrB (Submission.Diff.lcOf (G p.1)) x₀ p.2
        (Work.Diff.GE.cBasis (E := E) a) (Work.Diff.GE.cBasis (E := E) b)) t₀ x₀ :=
    chrB_at (I := I) (M := M) (G := G) hG a b
  have h : JointSmoothAt I M
      (fun p : ℝ × M ↦ mvfderiv I
        (fun y' ↦ Submission.ChartCurv.chrB (Submission.Diff.lcOf (G p.1)) x₀ y'
          (Work.Diff.GE.cBasis (E := E) a) (Work.Diff.GE.cBasis (E := E) b)) p.2
        (Work.Diff.GE.cFrame (I := I) x₀ v p.2)) t₀ x₀ :=
    Work.Diff.GE.mvfderiv_jointSmooth_frame (I := I) (F := E)
      (Φ := fun p : ℝ × M ↦ Submission.ChartCurv.chrB (Submission.Diff.lcOf (G p.1)) x₀ p.2
        (Work.Diff.GE.cBasis (E := E) a) (Work.Diff.GE.cBasis (E := E) b)) hchr x₀ v
      (mem_chart_source H x₀)
  simpa only [Submission.ChartCurv.dB, Work.Diff.GE.cFrame,
    Submission.Geodesic.frameSection_eq_frameVector] using h

/-- **The Christoffel symbol with a smooth family in its first argument.** -/
theorem chrB_arg_at {G : ℝ → Submission.Diff.SMet I M} {t₀ : ℝ} {x₀ : M}
    (hG : MetSmoothAt (I := I) (M := M) G t₀ x₀)
    {W : ℝ × M → E} (hW : JointSmoothAt I M W t₀ x₀)
    (a : Fin (Module.finrank ℝ E)) :
    JointSmoothAt I M
      (fun p : ℝ × M ↦ Submission.ChartCurv.chrB (Submission.Diff.lcOf (G p.1)) x₀ p.2
        (W p) (Work.Diff.GE.cBasis (E := E) a)) t₀ x₀ := by
  have hex : JointSmoothAt I M
      (fun p : ℝ × M ↦ ∑ m, ((Work.Diff.GE.cBasis (E := E)).coord m (W p)) •
        Submission.ChartCurv.chrB (Submission.Diff.lcOf (G p.1)) x₀ p.2
          (Work.Diff.GE.cBasis (E := E) m) (Work.Diff.GE.cBasis (E := E) a)) t₀ x₀ := by
    refine ContMDiffAt.sum (fun m _ ↦ ?_)
    have hcoef : ContMDiffAt ((𝓘(ℝ,ℝ)).prod I) 𝓘(ℝ,ℝ) ∞
        (fun p : ℝ × M ↦ (Work.Diff.GE.cBasis (E := E)).coord m (W p)) (t₀, x₀) :=
      (LinearMap.toContinuousLinearMap ((Work.Diff.GE.cBasis (E := E)).coord m)).contMDiffAt.comp
        (t₀, x₀) hW
    have hvec : ContMDiffAt ((𝓘(ℝ,ℝ)).prod I) 𝓘(ℝ,E) ∞
        (fun p : ℝ × M ↦ Submission.ChartCurv.chrB (Submission.Diff.lcOf (G p.1)) x₀ p.2
          (Work.Diff.GE.cBasis (E := E) m) (Work.Diff.GE.cBasis (E := E) a)) (t₀, x₀) :=
      chrB_at (I := I) (M := M) (G := G) hG m a
    exact hcoef.smul hvec
  refine hex.congr_of_eventuallyEq ?_
  rw [nhds_prod_eq]
  filter_upwards [Filter.prod_mem_prod Filter.univ_mem
      ((chartAt H x₀).open_source.mem_nhds (mem_chart_source H x₀))] with p hp
  conv_lhs => rw [← Submission.ChartCurv.sum_coord_smul_eq (E := E) (W p)]
  rw [Submission.ChartCurv.chrB_sum_fst Finset.univ x₀ p.2 _ _ (Work.Diff.GE.cBasis (E := E) a) hp.2]

/-- **The chart curvature tensor.** -/
theorem cCurv_at {G : ℝ → Submission.Diff.SMet I M} {t₀ : ℝ} {x₀ : M}
    (hG : MetSmoothAt (I := I) (M := M) G t₀ x₀)
    (i j l : Fin (Module.finrank ℝ E)) :
    JointSmoothAt I M
      (fun p : ℝ × M ↦ Work.Diff.GE.cCurv (G p.1) x₀ p.2 (Work.Diff.GE.cBasis (E := E) i)
        (Work.Diff.GE.cBasis (E := E) j) (Work.Diff.GE.cBasis (E := E) l)) t₀ x₀ := by
  have h1 := dB_at (I := I) (M := M) (G := G) hG i l j
  have h2 := dB_at (I := I) (M := M) (G := G) hG j l i
  have h3 := chrB_arg_at (I := I) (M := M) (G := G) hG
    (W := fun p : ℝ × M ↦ Submission.ChartCurv.chrB (Submission.Diff.lcOf (G p.1)) x₀ p.2
      (Work.Diff.GE.cBasis (E := E) l) (Work.Diff.GE.cBasis (E := E) j))
    (chrB_at (I := I) (M := M) (G := G) hG l j) i
  have h4 := chrB_arg_at (I := I) (M := M) (G := G) hG
    (W := fun p : ℝ × M ↦ Submission.ChartCurv.chrB (Submission.Diff.lcOf (G p.1)) x₀ p.2
      (Work.Diff.GE.cBasis (E := E) l) (Work.Diff.GE.cBasis (E := E) i))
    (chrB_at (I := I) (M := M) (G := G) hG l i) j
  have hc := (((h1.sub h2).add h3).sub h4)
  refine hc.congr_of_eventuallyEq ?_
  filter_upwards with p
  rfl

/-- **The chart curvature components lowered with the coordinate frame.** -/
theorem cRm_at {G : ℝ → Submission.Diff.SMet I M} {t₀ : ℝ} {x₀ : M}
    (hG : MetSmoothAt (I := I) (M := M) G t₀ x₀)
    (i j k l : Fin (Module.finrank ℝ E)) :
    JointSmoothAt I M
      (fun p : ℝ × M ↦ Work.Diff.GE.cRm (G p.1) x₀ p.2 (Work.Diff.GE.cBasis (E := E) i)
        (Work.Diff.GE.cBasis (E := E) j) (Work.Diff.GE.cBasis (E := E) k)
        (Work.Diff.GE.cBasis (E := E) l)) t₀ x₀ := by
  have hV : JointSmoothAt I M
      (fun p : ℝ × M ↦ Work.Diff.GE.cCurv (G p.1) x₀ p.2 (Work.Diff.GE.cBasis (E := E) i)
        (Work.Diff.GE.cBasis (E := E) j) (Work.Diff.GE.cBasis (E := E) l)) t₀ x₀ :=
    cCurv_at (I := I) (M := M) (G := G) hG i j l
  have hex : JointSmoothAt I M
      (fun p : ℝ × M ↦ ∑ m, ((Work.Diff.GE.cBasis (E := E)).coord m
          (Work.Diff.GE.cCurv (G p.1) x₀ p.2 (Work.Diff.GE.cBasis (E := E) i)
            (Work.Diff.GE.cBasis (E := E) j) (Work.Diff.GE.cBasis (E := E) l)))
        * Work.Diff.GE.mComp (I := I) G x₀ m k p.1 p.2) t₀ x₀ :=
    ContMDiffAt.sum (fun m _ ↦
      ((LinearMap.toContinuousLinearMap ((Work.Diff.GE.cBasis (E := E)).coord m)).contMDiffAt.comp
        (t₀, x₀) hV).mul (mComp_at (I := I) (M := M) (G := G) hG m k))
  refine hex.congr_of_eventuallyEq ?_
  rw [nhds_prod_eq]
  filter_upwards [Filter.prod_mem_prod Filter.univ_mem
      ((chartAt H x₀).open_source.mem_nhds (mem_chart_source H x₀))] with p hp
  exact Work.Diff.GE.cGram_eq_sum_coord (I := I) G x₀ hp.2 p.1
    (Work.Diff.GE.cCurv (G p.1) x₀ p.2 (Work.Diff.GE.cBasis (E := E) i)
      (Work.Diff.GE.cBasis (E := E) j) (Work.Diff.GE.cBasis (E := E) l)) k

/-- **The curvature components in the coordinate frame (local form).** -/
theorem rmC4_at (hLC : Submission.Diff.LCSmooth I M)
    {G : ℝ → Submission.Diff.SMet I M} {t₀ : ℝ} {x₀ : M}
    (hG : MetSmoothAt (I := I) (M := M) G t₀ x₀)
    (i j k l : Fin (Module.finrank ℝ E)) :
    JointSmoothAt I M
      (fun p : ℝ × M ↦ Work.Diff.GE.rmC4 (I := I) G x₀ p.1 p.2 i j k l) t₀ x₀ := by
  refine (cRm_at (I := I) (M := M) (G := G) hG i j k l).congr_of_eventuallyEq ?_
  rw [nhds_prod_eq]
  filter_upwards [Filter.prod_mem_prod Filter.univ_mem
      ((chartAt H x₀).open_source.mem_nhds (mem_chart_source H x₀))] with p hp
  exact Work.Diff.GE.rmC4_eq_cRm (I := I) (M := M) hLC G x₀ p.1 hp.2 i j k l


/-- **The Christoffel symbol with jointly smooth families in both arguments.** -/
theorem chrB_family_at (hLC : Submission.Diff.LCSmooth I M)
    {G : ℝ → Submission.Diff.SMet I M} {t₀ : ℝ} {x₀ : M}
    (hG : MetSmoothAt (I := I) (M := M) G t₀ x₀)
    {A B : ℝ × M → E} (hA : JointSmoothAt I M A t₀ x₀) (hB : JointSmoothAt I M B t₀ x₀) :
    JointSmoothAt I M
      (fun p : ℝ × M ↦ Submission.ChartCurv.chrB (Submission.Diff.lcOf (G p.1)) x₀ p.2
        (A p) (B p)) t₀ x₀ := by
  have hsum : JointSmoothAt I M
      (fun p : ℝ × M ↦ ∑ i, ∑ j,
        (((Module.finBasis ℝ E).coord i (A p)) * ((Module.finBasis ℝ E).coord j (B p))) •
          Submission.ChartCurv.chrB (Submission.Diff.lcOf (G p.1)) x₀ p.2
            (Module.finBasis ℝ E i) (Module.finBasis ℝ E j)) t₀ x₀ := by
    refine ContMDiffAt.sum (fun i _ ↦ ContMDiffAt.sum (fun j _ ↦ ?_))
    have h1 : ContMDiffAt ((𝓘(ℝ,ℝ)).prod I) 𝓘(ℝ,ℝ) ∞
        (fun p : ℝ × M ↦ (Module.finBasis ℝ E).coord i (A p)) (t₀, x₀) :=
      (LinearMap.toContinuousLinearMap ((Module.finBasis ℝ E).coord i)).contMDiffAt.comp
        (t₀, x₀) hA
    have h2 : ContMDiffAt ((𝓘(ℝ,ℝ)).prod I) 𝓘(ℝ,ℝ) ∞
        (fun p : ℝ × M ↦ (Module.finBasis ℝ E).coord j (B p)) (t₀, x₀) :=
      (LinearMap.toContinuousLinearMap ((Module.finBasis ℝ E).coord j)).contMDiffAt.comp
        (t₀, x₀) hB
    exact (h1.mul h2).smul (chrB_at (I := I) (M := M) (G := G) hG i j)
  refine hsum.congr_of_eventuallyEq ?_
  filter_upwards [prod_mem_nhds Filter.univ_mem
      ((chartAt H x₀).open_source.mem_nhds (mem_chart_source H x₀))] with p hp
  have hA' : A p = ∑ i, ((Module.finBasis ℝ E).coord i (A p)) • Module.finBasis ℝ E i := by
    rw [Finset.sum_congr rfl (fun i _ => by rw [Module.Basis.coord_apply])]
    exact ((Module.finBasis ℝ E).sum_repr (A p)).symm
  have hB' : B p = ∑ j, ((Module.finBasis ℝ E).coord j (B p)) • Module.finBasis ℝ E j := by
    rw [Finset.sum_congr rfl (fun j _ => by rw [Module.Basis.coord_apply])]
    exact ((Module.finBasis ℝ E).sum_repr (B p)).symm
  conv_lhs => rw [hA', hB']
  rw [Submission.ChartCurv.chrB_sum_fst Finset.univ x₀ p.2 _ _
    (∑ j, ((Module.finBasis ℝ E).coord j (B p)) • Module.finBasis ℝ E j) hp.2]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Submission.ChartCurv.chrB_sum_snd Finset.univ x₀ p.2 _ _ (Module.finBasis ℝ E i),
    Finset.smul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [smul_smul]

/-- **Coordinates of the Levi-Civita connection along jointly smooth families.** -/
theorem coordFun_lcOf_family (hLC : Submission.Diff.LCSmooth I M)
    {G : ℝ → Submission.Diff.SMet I M} {V : Set (ℝ × M)} (hV : IsOpen V) (hG : JointMet G V)
    {X Z : ℝ → TField (I := I) (M := M)} (hX : JointField X V) (hZ : JointField Z V)
    {p : ℝ × M} (hp : p ∈ V) :
    ContMDiffAt ((𝓘(ℝ, ℝ)).prod I) 𝓘(ℝ, E) ∞
      (fun q : ℝ × M => Submission.ChartCurv.coordFun p.2
        (fun y => lcOf (G q.1) (X q.1) y (Z q.1 y)) q.2) p := by
  letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨(G p.1).toRiemannianMetric⟩
  haveI : IsContMDiffRiemannianBundle I (⊤ : ℕ∞) E (fun x : M ↦ TangentSpace I x) := inferInstance
  set W : Set (ℝ × M) := V ∩ (univ ×ˢ (chartAt H p.2).source) with hWdef
  have hWopen : IsOpen W := hV.inter (isOpen_univ.prod (chartAt H p.2).open_source)
  have hpW : p ∈ W := ⟨hp, mem_univ p.1, mem_chart_source H p.2⟩
  have hsub : W ⊆ V := fun q hq => hq.1
  -- joint smoothness of the coordinate functions of `X` and `Z`
  have hcoordX : ContMDiffOn ((𝓘(ℝ, ℝ)).prod I) 𝓘(ℝ, E) ∞
      (fun q : ℝ × M => Submission.ChartCurv.coordFun p.2 (X q.1) q.2) W :=
    (contMDiffOn_coordFun_of_jointField (I := I) (M := M) hX p.2).mono
      (fun q hq => ⟨hq.1, hq.2⟩)
  have hcoordZ : ContMDiffOn ((𝓘(ℝ, ℝ)).prod I) 𝓘(ℝ, E) ∞
      (fun q : ℝ × M => Submission.ChartCurv.coordFun p.2 (Z q.1) q.2) W :=
    (contMDiffOn_coordFun_of_jointField (I := I) (M := M) hZ p.2).mono
      (fun q hq => ⟨hq.1, hq.2⟩)
  -- the pointwise identities
  have hpoint : ∀ q ∈ W,
      (fun y => lcOf (G q.1) (X q.1) y (Z q.1 y)) = fun y =>
        lcOf (G q.1) (X q.1) y (Z q.1 y) := fun _ _ => rfl
  have hev : (fun q : ℝ × M => Submission.ChartCurv.coordFun p.2
        (fun y => lcOf (G q.1) (X q.1) y (Z q.1 y)) q.2)
      =ᶠ[𝓝 p] (fun q : ℝ × M =>
        mvfderiv I (fun y => Submission.ChartCurv.coordFun p.2 (X q.1) y) q.2 (Z q.1 q.2)
          + Submission.ChartCurv.chrB (Submission.Diff.lcOf (G q.1)) p.2 q.2
              (Submission.ChartCurv.coordFun p.2 (X q.1) q.2)
              (Submission.ChartCurv.coordFun p.2 (Z q.1) q.2)) := by
    filter_upwards [hWopen.mem_nhds hpW] with q hq
    have hqV : q ∈ V := hq.1
    have hqsrc : q.2 ∈ (chartAt H p.2).source := hq.2.2
    have hXat : ContMDiffAt I I.tangent ∞ (T% (X q.1)) q.2 :=
      (hX.contMDiffAt (hV.mem_nhds hqV)).comp q.2
        ((contMDiffAt_const (c := q.1)).prodMk contMDiffAt_id)
    have hZat : ContMDiffAt I I.tangent ∞ (T% (Z q.1)) q.2 :=
      (hZ.contMDiffAt (hV.mem_nhds hqV)).comp q.2
        ((contMDiffAt_const (c := q.1)).prodMk contMDiffAt_id)
    haveI : ContMDiffCovariantDerivative (lcOf (G q.1)) ∞ := (hLC (G q.1)).1.some
    exact coordFun_cov_at (I := I) (M := M) (cov := lcOf (G q.1)) p.2 hXat hZat hqsrc
  -- smoothness of the two pieces of the limit function
  have htermA : ContMDiffAt ((𝓘(ℝ, ℝ)).prod I) 𝓘(ℝ, E) ∞
      (fun q : ℝ × M =>
        mvfderiv I (fun y => Submission.ChartCurv.coordFun p.2 (X q.1) y) q.2 (Z q.1 q.2)) p := by
    have hsum : ContMDiffAt ((𝓘(ℝ, ℝ)).prod I) 𝓘(ℝ, E) ∞
        (fun q : ℝ × M => ∑ i, (mvfderiv I
            (fun y => (Module.finBasis ℝ E).coord i
              (Submission.ChartCurv.coordFun p.2 (X q.1) y)) q.2 (Z q.1 q.2)) •
            Module.finBasis ℝ E i) p := by
      refine ContMDiffAt.sum (fun i _ => ?_)
      have hΦi : ContMDiffOn ((𝓘(ℝ, ℝ)).prod I) 𝓘(ℝ, ℝ) ∞
          (fun q : ℝ × M => (Module.finBasis ℝ E).coord i
            (Submission.ChartCurv.coordFun p.2 (X q.1) q.2)) W :=
        (((LinearMap.toContinuousLinearMap ((Module.finBasis ℝ E).coord i)).contMDiff.contMDiffOn).comp
          (t := univ) hcoordX (fun q _ => trivial))
      have hsp := Work.Diff.EXT.covK_spatialDeriv (I := I) (M := M)
        (Φ := fun t y => (Module.finBasis ℝ E).coord i
          (Submission.ChartCurv.coordFun p.2 (X t) y)) hWopen hΦi (hZ.mono hsub)
      have := hsp.contMDiffAt (hWopen.mem_nhds hpW)
      exact this.smul (contMDiffAt_const (c := Module.finBasis ℝ E i))
    refine hsum.congr_of_eventuallyEq ?_
    filter_upwards [hWopen.mem_nhds hpW] with q hq
    exact Submission.ChartCurv.mvfderiv_eq_sum_coord (I := I)
      (c := fun y : M => Submission.ChartCurv.coordFun p.2 (X q.1) y)
      (((hcoordX.contMDiffAt (hWopen.mem_nhds hq)).comp q.2
        ((contMDiffAt_const (c := q.1)).prodMk contMDiffAt_id)).mdifferentiableAt (by simp))
  have htermB : ContMDiffAt ((𝓘(ℝ, ℝ)).prod I) 𝓘(ℝ, E) ∞
      (fun q : ℝ × M => Submission.ChartCurv.chrB (Submission.Diff.lcOf (G q.1)) p.2 q.2
        (Submission.ChartCurv.coordFun p.2 (X q.1) q.2)
        (Submission.ChartCurv.coordFun p.2 (Z q.1) q.2)) p :=
    chrB_family_at (I := I) (M := M) hLC (hG.metSmoothAt hV hp)
      (coordFun_jointAt_of_jointField (I := I) (M := M) hV hX hp (mem_chart_source H p.2))
      (coordFun_jointAt_of_jointField (I := I) (M := M) hV hZ hp (mem_chart_source H p.2))
  exact (htermA.add htermB).congr_of_eventuallyEq hev

/-- **The Levi-Civita connection along jointly smooth families** (my own copy of
`Work.Diff.EXT.covK_lcOfFamily`, proved here so that this file does not depend on it). -/
theorem lcOf_familyJointField (hLC : Submission.Diff.LCSmooth I M)
    {G : ℝ → Submission.Diff.SMet I M} {V : Set (ℝ × M)} (hV : IsOpen V) (hG : JointMet G V)
    {X Z : ℝ → TField (I := I) (M := M)} (hX : JointField X V) (hZ : JointField Z V) :
    JointField (fun t ↦ fun y ↦ lcOf (G t) (X t) y (Z t y)) V := by
  intro p hp
  set triv := trivializationAt E (TangentSpace I) p.2 with htriv
  have hbase : p.2 ∈ triv.baseSet := by
    rw [htriv, TangentBundle.trivializationAt_baseSet]; exact mem_chart_source H p.2
  have he : (⟨p.2, lcOf (G p.1) (X p.1) p.2 (Z p.1 p.2)⟩ : TangentBundle I M) ∈ triv.source :=
    triv.mem_source.mpr hbase
  have hcoord : ContMDiffAt ((𝓘(ℝ, ℝ)).prod I) 𝓘(ℝ, E) ∞
      (fun q : ℝ × M => (triv ⟨q.2, lcOf (G q.1) (X q.1) q.2 (Z q.1 q.2)⟩).2) p := by
    refine (coordFun_lcOf_family (I := I) (M := M) hLC hV hG hX hZ hp).congr_of_eventuallyEq ?_
    filter_upwards [prod_mem_nhds Filter.univ_mem
      ((chartAt H p.2).open_source.mem_nhds (mem_chart_source H p.2))] with q hq
    have hq : q.2 ∈ (chartAt H p.2).source := hq.2
    show (triv ⟨q.2, lcOf (G q.1) (X q.1) q.2 (Z q.1 q.2)⟩).2
      = Submission.ChartCurv.coordFun p.2 (fun y => lcOf (G q.1) (X q.1) y (Z q.1 y)) q.2
    rw [Submission.ChartCurv.coordFun_apply]
    exact (Trivialization.continuousLinearMapAt_apply_of_mem ℝ triv
      (by rw [htriv, TangentBundle.trivializationAt_baseSet]; exact hq)
      (lcOf (G q.1) (X q.1) q.2 (Z q.1 q.2))).symm
  exact ((Trivialization.contMDiffWithinAt_iff (e := triv) (f := fun q : ℝ × M =>
    (⟨q.2, lcOf (G q.1) (X q.1) q.2 (Z q.1 q.2)⟩ : TangentBundle I M)) (s := V) (x₀ := p) he).mpr
      ⟨contMDiffWithinAt_snd, hcoord.contMDiffWithinAt⟩)

end Chain

section Main

variable
  {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]
  [I.Boundaryless] [T2Space M]

/-- **The `k = 0` case of `covK_familySmooth`**: the curvature form `rmP` of a jointly smooth
family of metrics, evaluated on four jointly smooth families of fields, is jointly smooth.

The proof is the chart expansion `Work.Diff.GE.rmP_eq_sum_rmC4`
`rmP (G t) y (A y)(B y)(C y)(D y) = Σ_i Σ_j Σ_k Σ_l α^i β^j γ^k δ^l · rmC4 (G t) x₀ t y i j k l`,
whose coefficients `α^i = (cBasis).coord i (coordFun x₀ A y)` are jointly smooth by
`coordFun_jointAt_of_jointField` and whose curvature components are jointly smooth by
`rmC4_at`. -/
theorem rmP_familySmooth (hLC : Submission.Diff.LCSmooth I M)
    {G : ℝ → Submission.Diff.SMet I M} {V : Set (ℝ × M)} (hV : IsOpen V) (hG : JointMet G V)
    {A B C D : ℝ → TField (I := I) (M := M)}
    (hA : JointField A V) (hB : JointField B V) (hC : JointField C V) (hD : JointField D V) :
    ContMDiffOn ((𝓘(ℝ, ℝ)).prod I) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M ↦ Submission.Diff.rmP (G p.1) p.2 (A p.1 p.2) (B p.1 p.2)
        (C p.1 p.2) (D p.1 p.2)) V := by
  intro p hp
  letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨(G p.1).toRiemannianMetric⟩
  haveI : IsContMDiffRiemannianBundle I (⊤ : ℕ∞) E (fun x : M ↦ TangentSpace I x) := inferInstance
  have hmet : MetSmoothAt (I := I) (M := M) G p.1 p.2 := hG.metSmoothAt hV hp
  have hcA : ContMDiffAt ((𝓘(ℝ, ℝ)).prod I) 𝓘(ℝ, E) ∞
      (fun q : ℝ × M => Submission.ChartCurv.coordFun p.2 (A q.1) q.2) p :=
    coordFun_jointAt_of_jointField (I := I) (M := M) hV hA hp (mem_chart_source H p.2)
  have hcB : ContMDiffAt ((𝓘(ℝ, ℝ)).prod I) 𝓘(ℝ, E) ∞
      (fun q : ℝ × M => Submission.ChartCurv.coordFun p.2 (B q.1) q.2) p :=
    coordFun_jointAt_of_jointField (I := I) (M := M) hV hB hp (mem_chart_source H p.2)
  have hcC : ContMDiffAt ((𝓘(ℝ, ℝ)).prod I) 𝓘(ℝ, E) ∞
      (fun q : ℝ × M => Submission.ChartCurv.coordFun p.2 (C q.1) q.2) p :=
    coordFun_jointAt_of_jointField (I := I) (M := M) hV hC hp (mem_chart_source H p.2)
  have hcD : ContMDiffAt ((𝓘(ℝ, ℝ)).prod I) 𝓘(ℝ, E) ∞
      (fun q : ℝ × M => Submission.ChartCurv.coordFun p.2 (D q.1) q.2) p :=
    coordFun_jointAt_of_jointField (I := I) (M := M) hV hD hp (mem_chart_source H p.2)
  have hsum : ContMDiffAt ((𝓘(ℝ, ℝ)).prod I) 𝓘(ℝ, ℝ) ∞
      (fun q : ℝ × M ↦ ∑ i, ∑ j, ∑ k, ∑ l,
        ((Work.Diff.GE.cBasis (E := E)).coord i
            (Submission.ChartCurv.coordFun p.2 (A q.1) q.2))
          * ((Work.Diff.GE.cBasis (E := E)).coord j
              (Submission.ChartCurv.coordFun p.2 (B q.1) q.2))
          * ((Work.Diff.GE.cBasis (E := E)).coord k
              (Submission.ChartCurv.coordFun p.2 (C q.1) q.2))
          * ((Work.Diff.GE.cBasis (E := E)).coord l
              (Submission.ChartCurv.coordFun p.2 (D q.1) q.2))
          * Work.Diff.GE.rmC4 (I := I) G p.2 q.1 q.2 i j k l) p := by
    refine ContMDiffAt.sum (fun i _ ↦ ContMDiffAt.sum (fun j _ ↦ ContMDiffAt.sum (fun k _ ↦
      ContMDiffAt.sum (fun l _ ↦ ?_))))
    have h1 : ContMDiffAt ((𝓘(ℝ, ℝ)).prod I) 𝓘(ℝ, ℝ) ∞
        (fun q : ℝ × M ↦ (Work.Diff.GE.cBasis (E := E)).coord i
          (Submission.ChartCurv.coordFun p.2 (A q.1) q.2)) p :=
      (LinearMap.toContinuousLinearMap ((Work.Diff.GE.cBasis (E := E)).coord i)).contMDiffAt.comp p hcA
    have h2 : ContMDiffAt ((𝓘(ℝ, ℝ)).prod I) 𝓘(ℝ, ℝ) ∞
        (fun q : ℝ × M ↦ (Work.Diff.GE.cBasis (E := E)).coord j
          (Submission.ChartCurv.coordFun p.2 (B q.1) q.2)) p :=
      (LinearMap.toContinuousLinearMap ((Work.Diff.GE.cBasis (E := E)).coord j)).contMDiffAt.comp p hcB
    have h3 : ContMDiffAt ((𝓘(ℝ, ℝ)).prod I) 𝓘(ℝ, ℝ) ∞
        (fun q : ℝ × M ↦ (Work.Diff.GE.cBasis (E := E)).coord k
          (Submission.ChartCurv.coordFun p.2 (C q.1) q.2)) p :=
      (LinearMap.toContinuousLinearMap ((Work.Diff.GE.cBasis (E := E)).coord k)).contMDiffAt.comp p hcC
    have h4 : ContMDiffAt ((𝓘(ℝ, ℝ)).prod I) 𝓘(ℝ, ℝ) ∞
        (fun q : ℝ × M ↦ (Work.Diff.GE.cBasis (E := E)).coord l
          (Submission.ChartCurv.coordFun p.2 (D q.1) q.2)) p :=
      (LinearMap.toContinuousLinearMap ((Work.Diff.GE.cBasis (E := E)).coord l)).contMDiffAt.comp p hcD
    exact ((((h1.mul h2).mul h3).mul h4).mul
      (rmC4_at (I := I) (M := M) hLC (G := G) hmet i j k l))
  refine (hsum.congr_of_eventuallyEq ?_).mono (Set.subset_univ V)
  filter_upwards [prod_mem_nhds Filter.univ_mem
    ((chartAt H p.2).open_source.mem_nhds (mem_chart_source H p.2))] with q hq
  have hq' : q.2 ∈ (chartAt H p.2).source := hq.2
  exact Work.Diff.GE.rmP_eq_sum_rmC4 (I := I) (M := M) hLC G p.2 q.1 hq'
    (A := A q.1) (B := B q.1) (C := C q.1) (D := D q.1)

/-- **Joint smoothness of the iterated covariant derivative tower `∇^k Rm` along a family.**
Let `G` be a family of smooth metrics jointly smooth on an open set `V ⊆ ℝ × M`, and let `Vf t`
(`Fin k`-indexed) and `A t`, `B t`, `C t`, `D t` be families of tangent fields jointly smooth on `V`
(`JointField`).  Then `(t,y) ↦ covKRmExt (G t) k (Vf t) (A t) (B t) (C t) (D t) y` is `C^∞` on `V`.

PROOF: induction on `k` from the recursion defining `covKRmExt`.
* `k = 0`: `rmP_familySmooth`.
* `k + 1`: the `mvfderiv` term is handled by `covK_spatialDeriv` (its joint smoothness input is the
  induction hypothesis at `k`), and each correction term replaces one slot by
  `fun y ↦ lcOf (G t) (·) y (Vf t 0 y)`, a jointly smooth family by `lcOf_familyJointField`, so the
  induction hypothesis at `k` applies. -/
theorem covK_familySmooth
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]
    [I.Boundaryless] [T2Space M]
    (hLC : Submission.Diff.LCSmooth I M)
    {G : ℝ → Submission.Diff.SMet I M} {V : Set (ℝ × M)} (hV : IsOpen V) (hG : JointMet G V)
    (k : ℕ) {Vf : ℝ → Fin k → TField (I := I) (M := M)}
    (hVf : ∀ i, JointField (fun t ↦ Vf t i) V)
    {A B C D : ℝ → TField (I := I) (M := M)}
    (hA : JointField A V) (hB : JointField B V) (hC : JointField C V) (hD : JointField D V) :
    ContMDiffOn ((𝓘(ℝ, ℝ)).prod I) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M ↦ covKRmExt (G p.1) k (Vf p.1) (A p.1) (B p.1) (C p.1) (D p.1) p.2) V := by
  suffices h : ∀ (j : ℕ) (Vf : ℝ → Fin j → TField (I := I) (M := M)),
      (∀ i, JointField (fun t ↦ Vf t i) V) →
      ∀ (A B C D : ℝ → TField (I := I) (M := M)), JointField A V → JointField B V →
        JointField C V → JointField D V →
      ContMDiffOn ((𝓘(ℝ, ℝ)).prod I) 𝓘(ℝ, ℝ) ∞
        (fun p : ℝ × M ↦ covKRmExt (G p.1) j (Vf p.1) (A p.1) (B p.1) (C p.1) (D p.1) p.2) V by
    exact h k Vf hVf A B C D hA hB hC hD
  intro j
  induction j with
  | zero =>
    intro Vf hVf A B C D hA hB hC hD
    have h0 := rmP_familySmooth (I := I) (M := M) hLC hV hG hA hB hC hD
    simpa only [covKRmExt] using h0
  | succ k ih =>
    intro Vf hVf A B C D hA hB hC hD
    letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨(G 0).toRiemannianMetric⟩
    haveI : IsContMDiffRiemannianBundle I (⊤ : ℕ∞) E (fun x : M ↦ TangentSpace I x) := inferInstance
    have hTf : ∀ i : Fin k, JointField (fun t ↦ Vf t i.succ) V := fun i => hVf i.succ
    have hZ : ∀ i : Fin k, JointField (fun t ↦ fun y ↦ lcOf (G t) (Vf t i.succ) y (Vf t 0 y)) V :=
      fun i => lcOf_familyJointField (I := I) (M := M) hLC hV hG (hVf i.succ) (hVf 0)
    have hWA : JointField (fun t ↦ fun y ↦ lcOf (G t) (A t) y (Vf t 0 y)) V :=
      lcOf_familyJointField (I := I) (M := M) hLC hV hG hA (hVf 0)
    have hWB : JointField (fun t ↦ fun y ↦ lcOf (G t) (B t) y (Vf t 0 y)) V :=
      lcOf_familyJointField (I := I) (M := M) hLC hV hG hB (hVf 0)
    have hWC : JointField (fun t ↦ fun y ↦ lcOf (G t) (C t) y (Vf t 0 y)) V :=
      lcOf_familyJointField (I := I) (M := M) hLC hV hG hC (hVf 0)
    have hWD : JointField (fun t ↦ fun y ↦ lcOf (G t) (D t) y (Vf t 0 y)) V :=
      lcOf_familyJointField (I := I) (M := M) hLC hV hG hD (hVf 0)
    have hUpd : ∀ i : Fin k, ∀ j' : Fin k,
        JointField (fun t ↦ Function.update (fun j' : Fin k => Vf t j'.succ) i
          (fun y ↦ lcOf (G t) (Vf t i.succ) y (Vf t 0 y)) j') V := by
      intro i j'
      by_cases hji : j' = i
      · subst hji
        rw [show (fun t ↦ Function.update (fun j' : Fin k => Vf t j'.succ) j'
              (fun y ↦ lcOf (G t) (Vf t j'.succ) y (Vf t 0 y)) j')
            = (fun t ↦ fun y ↦ lcOf (G t) (Vf t j'.succ) y (Vf t 0 y)) from by
          funext t; rw [Function.update_self]]
        exact hZ j'
      · rw [show (fun t ↦ Function.update (fun j' : Fin k => Vf t j'.succ) i
              (fun y ↦ lcOf (G t) (Vf t i.succ) y (Vf t 0 y)) j')
            = (fun t ↦ Vf t j'.succ) from by
          funext t; rw [Function.update_of_ne hji]]
        exact hTf j'
    intro p hp
    have h1 : ContMDiffAt ((𝓘(ℝ, ℝ)).prod I) 𝓘(ℝ, ℝ) ∞
        (fun q : ℝ × M ↦ mvfderiv I
          (fun y ↦ covKRmExt (G q.1) k (fun j' : Fin k => Vf q.1 j'.succ)
            (A q.1) (B q.1) (C q.1) (D q.1) y) q.2 (Vf q.1 0 q.2)) p :=
      (Work.Diff.EXT.covK_spatialDeriv (I := I) (M := M)
        (Φ := fun t y ↦ covKRmExt (G t) k (fun j' : Fin k => Vf t j'.succ)
          (A t) (B t) (C t) (D t) y)
        hV (ih (fun t j' => Vf t j'.succ) hTf A B C D hA hB hC hD) (hVf 0)).contMDiffAt
        (hV.mem_nhds hp)
    have h2 : ContMDiffAt ((𝓘(ℝ, ℝ)).prod I) 𝓘(ℝ, ℝ) ∞
        (fun q : ℝ × M ↦ ∑ i : Fin k, covKRmExt (G q.1) k
          (Function.update (fun j' : Fin k => Vf q.1 j'.succ) i
            (fun y ↦ lcOf (G q.1) (Vf q.1 i.succ) y (Vf q.1 0 y)))
          (A q.1) (B q.1) (C q.1) (D q.1) q.2) p := by
      refine ContMDiffAt.sum (fun i _ ↦ ?_)
      exact (ih (fun t => Function.update (fun j' : Fin k => Vf t j'.succ) i
        (fun y ↦ lcOf (G t) (Vf t i.succ) y (Vf t 0 y))) (hUpd i) A B C D
        hA hB hC hD).contMDiffAt (hV.mem_nhds hp)
    have h3 : ContMDiffAt ((𝓘(ℝ, ℝ)).prod I) 𝓘(ℝ, ℝ) ∞
        (fun q : ℝ × M ↦ covKRmExt (G q.1) k (fun j' : Fin k => Vf q.1 j'.succ)
          (fun y ↦ lcOf (G q.1) (A q.1) y (Vf q.1 0 y)) (B q.1) (C q.1) (D q.1) q.2) p :=
      (ih (fun t j' => Vf t j'.succ) hTf
        (fun t y ↦ lcOf (G t) (A t) y (Vf t 0 y)) B C D hWA hB hC hD).contMDiffAt
        (hV.mem_nhds hp)
    have h4 : ContMDiffAt ((𝓘(ℝ, ℝ)).prod I) 𝓘(ℝ, ℝ) ∞
        (fun q : ℝ × M ↦ covKRmExt (G q.1) k (fun j' : Fin k => Vf q.1 j'.succ)
          (A q.1) (fun y ↦ lcOf (G q.1) (B q.1) y (Vf q.1 0 y)) (C q.1) (D q.1) q.2) p :=
      (ih (fun t j' => Vf t j'.succ) hTf A
        (fun t y ↦ lcOf (G t) (B t) y (Vf t 0 y)) C D hA hWB hC hD).contMDiffAt
        (hV.mem_nhds hp)
    have h5 : ContMDiffAt ((𝓘(ℝ, ℝ)).prod I) 𝓘(ℝ, ℝ) ∞
        (fun q : ℝ × M ↦ covKRmExt (G q.1) k (fun j' : Fin k => Vf q.1 j'.succ)
          (A q.1) (B q.1) (fun y ↦ lcOf (G q.1) (C q.1) y (Vf q.1 0 y)) (D q.1) q.2) p :=
      (ih (fun t j' => Vf t j'.succ) hTf A B
        (fun t y ↦ lcOf (G t) (C t) y (Vf t 0 y)) D hA hB hWC hD).contMDiffAt
        (hV.mem_nhds hp)
    have h6 : ContMDiffAt ((𝓘(ℝ, ℝ)).prod I) 𝓘(ℝ, ℝ) ∞
        (fun q : ℝ × M ↦ covKRmExt (G q.1) k (fun j' : Fin k => Vf q.1 j'.succ)
          (A q.1) (B q.1) (C q.1) (fun y ↦ lcOf (G q.1) (D q.1) y (Vf q.1 0 y)) q.2) p :=
      (ih (fun t j' => Vf t j'.succ) hTf A B C
        (fun t y ↦ lcOf (G t) (D t) y (Vf t 0 y)) hA hB hC hWD).contMDiffAt
        (hV.mem_nhds hp)
    have hfun : (fun q : ℝ × M ↦ covKRmExt (G q.1) (k + 1) (Vf q.1)
          (A q.1) (B q.1) (C q.1) (D q.1) q.2)
        = fun q : ℝ × M ↦
            mvfderiv I (fun y ↦ covKRmExt (G q.1) k (fun j' : Fin k => Vf q.1 j'.succ)
              (A q.1) (B q.1) (C q.1) (D q.1) y) q.2 (Vf q.1 0 q.2)
            - (∑ i : Fin k, covKRmExt (G q.1) k
                (Function.update (fun j' : Fin k => Vf q.1 j'.succ) i
                  (fun y ↦ lcOf (G q.1) (Vf q.1 i.succ) y (Vf q.1 0 y)))
                (A q.1) (B q.1) (C q.1) (D q.1) q.2)
            - covKRmExt (G q.1) k (fun j' : Fin k => Vf q.1 j'.succ)
                (fun y ↦ lcOf (G q.1) (A q.1) y (Vf q.1 0 y)) (B q.1) (C q.1) (D q.1) q.2
            - covKRmExt (G q.1) k (fun j' : Fin k => Vf q.1 j'.succ) (A q.1)
                (fun y ↦ lcOf (G q.1) (B q.1) y (Vf q.1 0 y)) (C q.1) (D q.1) q.2
            - covKRmExt (G q.1) k (fun j' : Fin k => Vf q.1 j'.succ) (A q.1) (B q.1)
                (fun y ↦ lcOf (G q.1) (C q.1) y (Vf q.1 0 y)) (D q.1) q.2
            - covKRmExt (G q.1) k (fun j' : Fin k => Vf q.1 j'.succ) (A q.1) (B q.1) (C q.1)
                (fun y ↦ lcOf (G q.1) (D q.1) y (Vf q.1 0 y)) q.2 := by
      funext q
      simp only [covKRmExt]
    rw [hfun]
    exact (((((h1.sub h2).sub h3).sub h4).sub h5).sub h6).mono (Set.subset_univ V)

/-- A constant family of metrics is jointly smooth on all of `ℝ × M`. -/
theorem jointMet_const {g : Submission.Diff.SMet I M} :
    JointMet (I := I) (M := M) (fun _ : ℝ => g) univ :=
  g.contMDiff.comp_contMDiffOn
    (contMDiffOn_snd (I := 𝓘(ℝ, ℝ)) (J := I) (M := ℝ) (N := M))

/-- A constant family of globally smooth fields is jointly smooth. -/
theorem jointField_const {X : TField (I := I) (M := M)}
    (hX : SmoothTField (I := I) (M := M) X) :
    JointField (I := I) (M := M) (fun _ : ℝ => X) univ :=
  hX.contMDiffOn.comp (t := univ)
    (contMDiffOn_snd (I := 𝓘(ℝ, ℝ)) (J := I) (M := ℝ) (N := M)) (fun y _ => trivial)

/-- **Fixed-metric corollary of `covK_familySmooth`.**  For a single smooth metric `g` and globally
smooth fields (`V : Fin k → TField`, `A B C D`), the iterated covariant derivative `∇^k Rm`
evaluated on them is a `C^∞` function on `M`.  (This is the case `G ≡ g`, `V = univ` of
`covK_familySmooth`.)  It is needed by `Work.Diff.EXT.covK_linear`. -/
theorem covK_fixedSmooth (hLC : Submission.Diff.LCSmooth I M) (g : Submission.Diff.SMet I M)
    (k : ℕ) {V : Fin k → TField (I := I) (M := M)}
    (hV : ∀ i, SmoothTField (I := I) (M := M) (V i))
    {A B C D : TField (I := I) (M := M)} (hA : SmoothTField (I := I) (M := M) A)
    (hB : SmoothTField (I := I) (M := M) B) (hC : SmoothTField (I := I) (M := M) C)
    (hD : SmoothTField (I := I) (M := M) D) :
    CMDiff ∞ (fun y : M => covKRmExt g k V A B C D y) := by
  have hjoint := covK_familySmooth (I := I) (M := M) hLC (G := fun _ : ℝ => g) (V := univ)
    isOpen_univ (jointMet_const (I := I) (M := M) (g := g)) k
    (Vf := fun _ : ℝ => V) (fun i => jointField_const (I := I) (M := M) (hV i))
    (A := fun _ : ℝ => A) (B := fun _ : ℝ => B) (C := fun _ : ℝ => C) (D := fun _ : ℝ => D)
    (jointField_const (I := I) (M := M) hA) (jointField_const (I := I) (M := M) hB)
    (jointField_const (I := I) (M := M) hC) (jointField_const (I := I) (M := M) hD)
  have hslice : ContMDiffOn I 𝓘(ℝ, ℝ) ∞ (fun y : M => covKRmExt g k V A B C D y) univ := by
    simpa only [Function.comp_def, id_eq] using hjoint.comp
      ((contMDiffOn_const (s := univ) (c := (0 : ℝ))).prodMk
        (contMDiffOn_id (I := I) (M := M) (s := univ)))
      (fun y _ => mem_univ _)
  rw [contMDiffOn_univ] at hslice
  exact hslice

end Main
end Work.Diff.EXT
