import Submission.Work.Tubular.DiscManifold.ChartPartial

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option maxHeartbeats 400000

/-!
# The disc chart of the normal disc bundle

This file completes the chart data of `Chart.lean`/`ChartPartial.lean` into an
`OpenPartialHomeomorph` (`discChart`) and proves the openness of its target and the continuity of
its two maps.
-/

open scoped Manifold ContDiff Topology InnerProduct InnerProductSpace
open Function Filter
open OpenPartialHomeomorph

open Work.ThomBordism.PontryaginThom (EmbeddingData coverIndexAt mem_coverBaseSet_indexAt
  coverBaseSet)

namespace Work.Tubular

open Work.ThomBordism Work.ThomBordism.PontryaginThom Work.SignatureBordism

noncomputable section

variable {V : Work.ThomBordism.Man8} {k : ℕ} [NeZero k] {ε : ℝ}

/-- **The product model of the normal disc bundle**: the base model `ℝ⁸` times the half-space model
of the fibre disc `D^k = Half (k-1)`.  The disc bundle is naturally charted on this model; the
reindexing `Work.Tubular.DiscManifold.HalfModelReindex` converts it into the half-space
`EuclideanHalfSpace (8+k)`. -/
abbrev Iprod (k : ℕ) : ModelWithCorners ℝ (Euc 8 × Euc ((k - 1) + 1)) (Euc 8 × Half (k - 1)) :=
  (𝓡 8).prod (hModel (k - 1))

section Chart

variable {E : EmbeddingData V (8 + k)} (C : TubeChart E ε) (p : NormalDiscSub E ε)

/-! ## The continuity and openness of the chart data -/

/-- **Continuity into a subtype**, read through the ambient space: a `ContinuousOn` map into a
subtype is the same thing as the `ContinuousOn` composite with the coercion. -/
theorem continuousOn_subtype_iff {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {p : Y → Prop} {g : X → Subtype p} {s : Set X} :
    ContinuousOn g s ↔ ContinuousOn (fun x => (g x : Y)) s := by
  rw [continuousOn_iff_continuous_domRestrict, continuousOn_iff_continuous_domRestrict]
  constructor
  · intro h
    exact continuous_subtype_val.comp h
  · intro h
    exact Continuous.subtype_mk h (fun x => (g x).2)

theorem isOpen_chartTarget : IsOpen (chartTarget C p) := by
  have h1 : IsOpen ((chartBaseC p).target ∩
      (chartBaseC p).symm ⁻¹' coverBaseSet E.e (discPiece p)) :=
    (chartBaseC p).isOpen_inter_preimage_symm
      (isOpen_coverBaseSet E.e (embedding_contMDiff_one (E := E)) (discPiece p))
  have hset : chartTarget C p =
      ((fun z : ModelProd (Euc 8) (Half (k - 1)) => z.1) ⁻¹'
        ((chartBaseC p).target ∩ (chartBaseC p).symm ⁻¹' coverBaseSet E.e (discPiece p)))
      ∩ ((fun z : ModelProd (Euc 8) (Half (k - 1)) => z.2) ⁻¹' (chartFibC C p).target) := by
    ext z
    simp only [chartTarget, Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_preimage]
    tauto
  rw [hset]
  exact (h1.preimage continuous_fst).inter ((chartFibC C p).open_target.preimage continuous_snd)

theorem continuousOn_chartToFun : ContinuousOn (chartToFun C p) (chartSource C p) := by
  have hbase : ContinuousOn (fun q : NormalDiscSub E ε =>
      (chartBaseC p) (NormalTotal.proj q.1)) (chartSource C p) :=
    (chartBaseC p).continuousOn_toFun.comp continuous_discProj.continuousOn
      (fun q hq => hq.2.1)
  have hfib : ContinuousOn (fun q : NormalDiscSub E ε =>
      (chartFibC C p) (discPt (k - 1) (ballVecI C (discPiece p) q))) (chartSource C p) := by
    rw [continuousOn_subtype_iff]
    have hball : ContinuousOn (fun q : NormalDiscSub E ε => ballVecI C (discPiece p) q)
        (chartSource C p) :=
      (continuousOn_ballVecI C (discPiece p)).mono (fun q hq => hq.1)
    have hchart : ContinuousOn (fun v : Euc ((k - 1) + 1) =>
        ((chartFibC C p) (discPt (k - 1) v) : Half (k - 1)).val)
        {v | v ∈ Ball (k - 1) ∧ discPt (k - 1) v ∈ (chartFibC C p).source} :=
      (DiscManifold.contDiffOn_ballChartAt (k - 1) (chartFibPt C p)).continuousOn
    exact hchart.comp hball (fun q hq => ⟨mem_ball_ballVecI hq.1,
      ((DiscManifold.ballChartAmb_spec (k - 1) (chartFibPt C p)).2 _
        (mem_ball_ballVecI hq.1)).mpr hq.2.2⟩)
  show ContinuousOn (fun q : NormalDiscSub E ε =>
    ((chartBaseC p) (NormalTotal.proj q.1),
      (chartFibC C p) (discPt (k - 1) (ballVecI C (discPiece p) q)))) (chartSource C p)
  exact hbase.prodMk hfib

theorem continuousOn_chartInvFun : ContinuousOn (chartInvFun C p) (chartTarget C p) := by
  rw [continuousOn_subtype_iff, continuousOn_subtype_iff]
  have hx : ContinuousOn (fun z : ModelProd (Euc 8) (Half (k - 1)) => (chartBaseC p).symm z.1)
      (chartTarget C p) :=
    (chartBaseC p).continuousOn_invFun.comp continuous_fst.continuousOn (fun z hz => hz.2.1)
  have hc : ContinuousOn (fun z : ModelProd (Euc 8) (Half (k - 1)) =>
      ((chartFibC C p).symm z.2).val) (chartTarget C p) :=
    continuous_subtype_val.comp_continuousOn
      ((chartFibC C p).continuousOn_invFun.comp continuous_snd.continuousOn
        (fun z hz => hz.2.2))
  have hpair : ContinuousOn (fun z : ModelProd (Euc 8) (Half (k - 1)) =>
      ((chartBaseC p).symm z.1, ε • ((chartFibC C p).symm z.2).val)) (chartTarget C p) :=
    hx.prodMk (hc.const_smul ε)
  have hv0 : ContinuousOn ((fun q : V.pt × Euc ((k - 1) + 1) => insFE C (discPiece p) q.1 q.2) ∘
      fun z : ModelProd (Euc 8) (Half (k - 1)) =>
        ((chartBaseC p).symm z.1, ε • ((chartFibC C p).symm z.2).val)) (chartTarget C p) :=
    (continuousOn_insFE C (discPiece p)).comp hpair (fun z hz => ⟨hz.1, trivial⟩)
  have hv : ContinuousOn (fun z : ModelProd (Euc 8) (Half (k - 1)) =>
      insFE C (discPiece p) ((chartBaseC p).symm z.1) (ε • ((chartFibC C p).symm z.2).val))
      (chartTarget C p) := hv0.congr (fun z _ => rfl)
  refine ContinuousOn.congr (hx.prodMk hv) (fun z hz => ?_)
  have hcond : chartInvCond C p z := ⟨hz.1, hz.2.2⟩
  rw [chartInvFun, dif_pos hcond]

/-! ## The chart -/

/-- **The chart of the normal disc bundle at a point `p`**: the base chart at `proj p`, followed by
the preferred chart of the fibre disc at the fibre coordinate of `p`. -/
noncomputable def discChart :
    OpenPartialHomeomorph (NormalDiscSub E ε) (ModelProd (Euc 8) (Half (k - 1))) where
  source := chartSource C p
  target := chartTarget C p
  toFun := chartToFun C p
  invFun := chartInvFun C p
  map_source' := fun q hq => chartToFun_mem_target C p hq
  map_target' := fun z hz => chartInvFun_mem_source C p hz
  left_inv' := fun q hq => chartInvFun_toFun C p hq
  right_inv' := fun z hz => chartToFun_invFun C p hz
  open_source := isOpen_chartSource C p
  open_target := isOpen_chartTarget C p
  continuousOn_toFun := continuousOn_chartToFun C p
  continuousOn_invFun := continuousOn_chartInvFun C p

@[simp] theorem discChart_source : (discChart C p).source = chartSource C p := rfl

@[simp] theorem discChart_target : (discChart C p).target = chartTarget C p := rfl

@[simp] theorem discChart_apply (q : NormalDiscSub E ε) :
    discChart C p q = chartToFun C p q := rfl

@[simp] theorem discChart_symm_apply (z : ModelProd (Euc 8) (Half (k - 1))) :
    (discChart C p).symm z = chartInvFun C p z := rfl


end Chart

end

end Work.Tubular
