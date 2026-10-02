import Submission.Work.Tubular.DiscManifold.Fibre
import Submission.Work.Tubular.DiscManifold.BallChartAmb
import Submission.Work.Tubular.DiscManifold.contDiffOn_ballChartAt
import Submission.Work.Tubular.DiscManifold.contDiffOn_ballChartAt_symm

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option maxHeartbeats 8000000

/-!
# The charts of the normal disc bundle

Take a point `p` of the disc bundle, let `i` be an index of the chart cover of the base with
`proj p ∈ coverBaseSet i`, and let `c` be the preferred chart of the base at `proj p`.  Then the
chart at `p` is

  `q ↦ (c (proj q), ballChart (ε⁻¹ readFE_i (proj q) (vec q)))`,

where `ballChart` is the preferred chart of the fibre disc `Ball (k-1)` at the fibre coordinate of
`p`.  This file builds the data of that chart and proves its continuity.
-/

open scoped Manifold ContDiff Topology InnerProduct InnerProductSpace
open Function Filter

open Work.ThomBordism.PontryaginThom (EmbeddingData coverIndexAt mem_coverBaseSet_indexAt
  coverBaseSet)

namespace Work.Tubular

open Work.ThomBordism Work.ThomBordism.PontryaginThom Work.SignatureBordism

noncomputable section

variable {V : Work.ThomBordism.Man8} {k : ℕ} [NeZero k] {ε : ℝ}

/-! ## The piece index of a point -/

theorem embedding_contMDiff_one {E : EmbeddingData V (8 + k)} :
    ContMDiff (𝓡 8) (𝓡 (8 + k)) 1 E.e :=
  E.smooth.of_le (ENat.LEInfty.out : (1 : ℕ∞ω) ≤ ∞)

/-- **The piece index** of a point of the disc bundle: an index of the chart cover whose base set
contains the base point. -/
noncomputable def discPiece {E : EmbeddingData V (8 + k)} (p : NormalDiscSub E ε) : CoverIdx V k :=
  coverIndexAt E.e (embedding_contMDiff_one (E := E)) E.injective_mfderiv (NormalTotal.proj p.1)

theorem mem_coverBaseSet_discPiece {E : EmbeddingData V (8 + k)} (p : NormalDiscSub E ε) :
    NormalTotal.proj p.1 ∈ coverBaseSet E.e (discPiece p) :=
  mem_coverBaseSet_indexAt E.e (embedding_contMDiff_one (E := E)) E.injective_mfderiv
    (NormalTotal.proj p.1)

/-! ## The fibre coordinate of a point -/

theorem norm_readFE {E : EmbeddingData V (8 + k)} (C : TubeChart E ε) (i : CoverIdx V k)
    {x : V.pt} (hx : x ∈ coverBaseSet E.e i) {v : Euc (8 + k)} (hv : v ∈ normalSpace E x) :
    ‖readFE C i x v‖ = ‖v‖ := by
  rw [readFE_apply, (reindexFibre k).norm_map]
  exact norm_readF C i hx hv

/-- **The fibre coordinate** of a point of the disc bundle, in a fixed piece `i`: the ambient vector
of the fibre disc `Ball (k-1)`. -/
noncomputable def ballVecI {E : EmbeddingData V (8 + k)} (C : TubeChart E ε) (i : CoverIdx V k)
    (q : NormalDiscSub E ε) : Euc ((k - 1) + 1) :=
  ε⁻¹ • readFE C i (NormalTotal.proj q.1) (NormalTotal.vec q.1)

theorem norm_ballVecI_le {E : EmbeddingData V (8 + k)} (C : TubeChart E ε) (i : CoverIdx V k)
    {q : NormalDiscSub E ε} (hx : NormalTotal.proj q.1 ∈ coverBaseSet E.e i) :
    ‖ballVecI C i q‖ ≤ 1 := by
  have h1 : ‖ballVecI C i q‖ = ε⁻¹ * ‖NormalTotal.vec q.1‖ := by
    rw [ballVecI, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos C.eps_pos,
      norm_readFE C i hx (NormalTotal.vec_mem q.1)]
  have h2 : ‖NormalTotal.vec q.1‖ ≤ ε := q.2
  rw [h1]
  calc ε⁻¹ * ‖NormalTotal.vec q.1‖ ≤ ε⁻¹ * ε :=
        mul_le_mul_of_nonneg_left h2 (inv_pos.mpr C.eps_pos).le
    _ = 1 := inv_mul_cancel₀ (ne_of_gt C.eps_pos)

/-- **The fibre coordinate**, as a point of the fibre disc `Ball (k-1)`. -/
noncomputable def ballPtI {E : EmbeddingData V (8 + k)} (C : TubeChart E ε) (i : CoverIdx V k)
    (q : NormalDiscSub E ε) (hx : NormalTotal.proj q.1 ∈ coverBaseSet E.e i) : Ball (k - 1) :=
  ⟨ballVecI C i q, by
    rw [Metric.mem_closedBall, dist_zero_right]
    exact norm_ballVecI_le C i hx⟩

/-! ## Continuity of the data -/

theorem continuous_discProj {E : EmbeddingData V (8 + k)} :
    Continuous (fun q : NormalDiscSub E ε => NormalTotal.proj q.1) :=
  ((continuous_subtype_val : Continuous
      (Subtype.val : NormalTotal E → V.pt × Euc (8 + k))).fst).comp continuous_subtype_val

theorem continuous_discVec {E : EmbeddingData V (8 + k)} :
    Continuous (fun q : NormalDiscSub E ε => NormalTotal.vec q.1) :=
  ((continuous_subtype_val : Continuous
      (Subtype.val : NormalTotal E → V.pt × Euc (8 + k))).snd).comp continuous_subtype_val

/-- Continuity of the fibre coordinate, on the piece. -/
theorem continuousOn_ballVecI {E : EmbeddingData V (8 + k)} (C : TubeChart E ε)
    (i : CoverIdx V k) :
    ContinuousOn (fun q : NormalDiscSub E ε => ballVecI C i q)
      {q | NormalTotal.proj q.1 ∈ coverBaseSet E.e i} := by
  have hpair : ContinuousOn (fun q : NormalDiscSub E ε =>
      (NormalTotal.proj q.1, NormalTotal.vec q.1))
      {q | NormalTotal.proj q.1 ∈ coverBaseSet E.e i} :=
    (continuous_discProj.prodMk continuous_discVec).continuousOn
  refine ((continuousOn_readFE C i).comp hpair (fun q hq => ⟨hq, Set.mem_univ _⟩)).const_smul
    ε⁻¹ |>.congr fun q _ => ?_
  simp only [Function.comp_apply, Pi.smul_apply, ballVecI]

end

end Work.Tubular
