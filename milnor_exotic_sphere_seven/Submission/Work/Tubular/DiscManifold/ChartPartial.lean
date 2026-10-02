import Submission.Work.Tubular.DiscManifold.Chart
import Submission.Work.Tubular.DiscManifold.ballChartAmb_spec

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option maxHeartbeats 8000000

/-!
# The chart of the normal disc bundle as an open partial homeomorphism

This file assembles the chart data of `Chart.lean` into an `OpenPartialHomeomorph`, using the
regularity of the preferred chart of the closed fibre disc (`contDiffOn_ballChartAt`, proved by a
colleague) and the ambient description of its source (`ballChartAmb`, proved by a colleague).
-/

open scoped Manifold ContDiff Topology InnerProduct InnerProductSpace
open Function Filter

open Work.ThomBordism.PontryaginThom (EmbeddingData coverIndexAt mem_coverBaseSet_indexAt
  coverBaseSet)

namespace Work.Tubular

open Work.ThomBordism Work.ThomBordism.PontryaginThom Work.SignatureBordism

noncomputable section

variable {V : Work.ThomBordism.Man8} {k : ℕ} [NeZero k] {ε : ℝ}

section Chart

variable {E : EmbeddingData V (8 + k)} (C : TubeChart E ε) (p : NormalDiscSub E ε)

/-- The base chart of the disc chart at `p`. -/
noncomputable def chartBaseC : OpenPartialHomeomorph V.pt (Euc 8) :=
  chartAt (Euc 8) (NormalTotal.proj p.1)

/-- The point of the fibre disc used to choose the fibre chart. -/
noncomputable def chartFibPt : Ball (k - 1) :=
  ballPtI C (discPiece p) p (mem_coverBaseSet_discPiece p)

/-- The fibre chart of the disc chart at `p`. -/
noncomputable def chartFibC : OpenPartialHomeomorph (Ball (k - 1)) (Half (k - 1)) :=
  chartAt (Half (k - 1)) (chartFibPt C p)

/-- **The source of the disc chart at `p`.** -/
noncomputable def chartSource : Set (NormalDiscSub E ε) :=
  {q | NormalTotal.proj q.1 ∈ coverBaseSet E.e (discPiece p)} ∩
    ({q | NormalTotal.proj q.1 ∈ (chartBaseC p).source} ∩
      {q | ballVecI C (discPiece p) q
        ∈ DiscManifold.ballChartAmb (k - 1) (chartFibPt C p)})

theorem mem_chartSource_iff {q : NormalDiscSub E ε} :
    q ∈ chartSource C p ↔ NormalTotal.proj q.1 ∈ coverBaseSet E.e (discPiece p) ∧
      NormalTotal.proj q.1 ∈ (chartBaseC p).source ∧
      ballVecI C (discPiece p) q ∈ DiscManifold.ballChartAmb (k - 1) (chartFibPt C p) :=
  ⟨fun h => ⟨h.1, h.2.1, h.2.2⟩, fun h => ⟨h.1, h.2.1, h.2.2⟩⟩

/-- **The target of the disc chart at `p`.** -/
noncomputable def chartTarget : Set (ModelProd (Euc 8) (Half (k - 1))) :=
  {z | (chartBaseC p).symm z.1 ∈ coverBaseSet E.e (discPiece p)} ∩
    ({z | z.1 ∈ (chartBaseC p).target} ∩ {z | z.2 ∈ (chartFibC C p).target})

theorem mem_chartTarget_iff {z : ModelProd (Euc 8) (Half (k - 1))} :
    z ∈ chartTarget C p ↔ (chartBaseC p).symm z.1 ∈ coverBaseSet E.e (discPiece p) ∧
      z.1 ∈ (chartBaseC p).target ∧ z.2 ∈ (chartFibC C p).target :=
  ⟨fun h => ⟨h.1, h.2.1, h.2.2⟩, fun h => ⟨h.1, h.2.1, h.2.2⟩⟩

/-- **The forward map of the disc chart at `p`.** -/
noncomputable def chartToFun (q : NormalDiscSub E ε) : ModelProd (Euc 8) (Half (k - 1)) :=
  ((chartBaseC p) (NormalTotal.proj q.1),
    (chartFibC C p) (discPt (k - 1) (ballVecI C (discPiece p) q)))

/-- The discriminant of the inverse of the disc chart. -/
def chartInvCond (z : ModelProd (Euc 8) (Half (k - 1))) : Prop :=
  (chartBaseC p).symm z.1 ∈ coverBaseSet E.e (discPiece p) ∧
    z.2 ∈ (chartFibC C p).target

/-- **The inverse of the disc chart at `p`.** -/
noncomputable def chartInvFun (z : ModelProd (Euc 8) (Half (k - 1))) : NormalDiscSub E ε := by
  classical
  by_cases h : chartInvCond C p z
  · refine ⟨⟨((chartBaseC p).symm z.1,
      insFE C (discPiece p) ((chartBaseC p).symm z.1)
        (ε • ((chartFibC C p).symm z.2).val)), ?_⟩, ?_⟩
    · exact insFE_mem C (discPiece p) h.1 _
    · rw [mem_normalClosedDiscSet, normalNorm_mk, norm_insFE C (discPiece p) h.1]
      have hb : ‖((chartFibC C p).symm z.2).val‖ ≤ 1 := by
        rw [← dist_zero_right, ← Metric.mem_closedBall]
        exact ((chartFibC C p).symm z.2).2
      calc ‖ε • ((chartFibC C p).symm z.2).val‖ = ε * ‖((chartFibC C p).symm z.2).val‖ := by
            rw [norm_smul, Real.norm_eq_abs, abs_of_pos C.eps_pos]
        _ ≤ ε * 1 := mul_le_mul_of_nonneg_left hb C.eps_pos.le
        _ = ε := mul_one ε
  · exact ⟨⟨(NormalTotal.proj p.1, 0), by simp⟩, by simp [C.eps_pos.le]⟩

/-! ## Openness -/

theorem isOpen_chartSource : IsOpen (chartSource C p) := by
  have h1 : IsOpen {q : NormalDiscSub E ε | NormalTotal.proj q.1 ∈
      coverBaseSet E.e (discPiece p)} :=
    (isOpen_coverBaseSet E.e (embedding_contMDiff_one (E := E)) (discPiece p)).preimage
      continuous_discProj
  have h2 : IsOpen {q : NormalDiscSub E ε | NormalTotal.proj q.1
      ∈ (chartBaseC p).source} :=
    (chartBaseC p).open_source.preimage continuous_discProj
  have h3 : IsOpen ({q : NormalDiscSub E ε | NormalTotal.proj q.1 ∈ coverBaseSet E.e (discPiece p)}
        ∩ {q : NormalDiscSub E ε | ballVecI C (discPiece p) q
          ∈ DiscManifold.ballChartAmb (k - 1) (chartFibPt C p)}) :=
    (continuousOn_ballVecI C (discPiece p)).isOpen_inter_preimage h1
      (DiscManifold.ballChartAmb_spec (k - 1) (chartFibPt C p)).1
  have hset : chartSource C p = {q : NormalDiscSub E ε |
        NormalTotal.proj q.1 ∈ coverBaseSet E.e (discPiece p)} ∩
      ({q : NormalDiscSub E ε | NormalTotal.proj q.1 ∈ (chartBaseC p).source} ∩
        ({q : NormalDiscSub E ε | NormalTotal.proj q.1 ∈ coverBaseSet E.e (discPiece p)} ∩
          {q : NormalDiscSub E ε | ballVecI C (discPiece p) q
            ∈ DiscManifold.ballChartAmb (k - 1) (chartFibPt C p)})) := by
    ext q
    simp only [chartSource, Set.mem_inter_iff, Set.mem_setOf_eq]
    tauto
  rw [hset]
  exact h1.inter (h2.inter h3)


/-- The fibre coordinate is a point of the fibre disc. -/
theorem mem_ball_ballVecI {E : EmbeddingData V (8 + k)} {C : TubeChart E ε} {i : CoverIdx V k}
    {q : NormalDiscSub E ε} (hx : NormalTotal.proj q.1 ∈ coverBaseSet E.e i) :
    ballVecI C i q ∈ Ball (k - 1) := by
  rw [Metric.mem_closedBall, dist_zero_right]
  exact norm_ballVecI_le C i hx

theorem chartToFun_mem_target {q : NormalDiscSub E ε} (hq : q ∈ chartSource C p) :
    chartToFun C p q ∈ chartTarget C p := by
  obtain ⟨h1, h2, h3⟩ := (mem_chartSource_iff C p).mp hq
  refine (mem_chartTarget_iff C p).mpr ⟨?_, ?_, ?_⟩
  · simp only [chartToFun]
    rw [(chartBaseC p).left_inv h2]
    exact h1
  · simp only [chartToFun]
    exact (chartBaseC p).map_source h2
  · simp only [chartToFun]
    exact (chartFibC C p).map_source
      (((DiscManifold.ballChartAmb_spec (k - 1) (chartFibPt C p)).2
        (ballVecI C (discPiece p) q) (mem_ball_ballVecI h1)).mpr h3)

theorem chartInvFun_mem_source {z : ModelProd (Euc 8) (Half (k - 1))} (hz : z ∈ chartTarget C p) :
    chartInvFun C p z ∈ chartSource C p := by
  have hc : chartInvCond C p z := ⟨hz.1, hz.2.2⟩
  have hB : ((chartFibC C p).symm z.2).val ∈ DiscManifold.ballChartAmb (k - 1) (chartFibPt C p) := by
    refine ((DiscManifold.ballChartAmb_spec (k - 1) (chartFibPt C p)).2
      ((chartFibC C p).symm z.2).val ((chartFibC C p).symm z.2).2).mp ?_
    rw [discPt_of_mem _ ((chartFibC C p).symm z.2).2]
    exact (chartFibC C p).map_target hz.2.2
  rw [chartInvFun, dif_pos hc]
  refine (mem_chartSource_iff C p).mpr ⟨hc.1, (chartBaseC p).map_target hz.2.1, ?_⟩
  simp only [ballVecI, NormalTotal.proj, NormalTotal.vec]
  rw [readFE_insFE C (discPiece p) hc.1, inv_smul_smul₀ (ne_of_gt C.eps_pos)]
  exact hB

theorem chartInvFun_toFun {q : NormalDiscSub E ε} (hq : q ∈ chartSource C p) :
    chartInvFun C p (chartToFun C p q) = q := by
  obtain ⟨h1, h2, h3⟩ := (mem_chartSource_iff C p).mp hq
  have hsrc : discPt (k - 1) (ballVecI C (discPiece p) q) ∈ (chartFibC C p).source :=
    ((DiscManifold.ballChartAmb_spec (k - 1) (chartFibPt C p)).2
      (ballVecI C (discPiece p) q) (mem_ball_ballVecI h1)).mpr h3
  have hc : chartInvCond C p (chartToFun C p q) := by
    refine ⟨?_, ?_⟩
    · simp only [chartToFun]
      rw [(chartBaseC p).left_inv h2]
      exact h1
    · simp only [chartToFun]
      exact (chartFibC C p).map_source hsrc
  rw [chartInvFun, dif_pos hc]
  refine Subtype.ext (Subtype.ext (Prod.ext ?_ ?_))
  · show (chartBaseC p).symm ((chartBaseC p) (NormalTotal.proj q.1)) = NormalTotal.proj q.1
    rw [(chartBaseC p).left_inv h2]
  · show insFE C (discPiece p) ((chartBaseC p).symm ((chartBaseC p) (NormalTotal.proj q.1)))
        (ε • ((chartFibC C p).symm
          ((chartFibC C p) (discPt (k - 1) (ballVecI C (discPiece p) q)))).val)
        = NormalTotal.vec q.1
    rw [(chartBaseC p).left_inv h2, (chartFibC C p).left_inv hsrc,
      discPt_of_mem (k - 1) (mem_ball_ballVecI h1)]
    simp only [ballVecI, Subtype.coe_mk]
    rw [smul_inv_smul₀ (ne_of_gt C.eps_pos),
      insFE_readFE C (discPiece p) h1 (NormalTotal.vec_mem q.1)]

theorem chartToFun_invFun {z : ModelProd (Euc 8) (Half (k - 1))} (hz : z ∈ chartTarget C p) :
    chartToFun C p (chartInvFun C p z) = z := by
  have hc : chartInvCond C p z := ⟨hz.1, hz.2.2⟩
  rw [chartInvFun, dif_pos hc]
  refine Prod.ext ?_ ?_
  · simp only [chartToFun, NormalTotal.proj]
    rw [(chartBaseC p).right_inv hz.2.1]
  · simp only [chartToFun, NormalTotal.vec]
    rw [show discPt (k - 1) (ballVecI C (discPiece p) _) = (chartFibC C p).symm z.2 from ?_,
      (chartFibC C p).right_inv hz.2.2]
    simp only [ballVecI, NormalTotal.proj, NormalTotal.vec]
    rw [readFE_insFE C (discPiece p) hc.1, inv_smul_smul₀ (ne_of_gt C.eps_pos)]
    exact discPt_of_mem (k - 1) ((chartFibC C p).symm z.2).2


end Chart

end

end Work.Tubular
