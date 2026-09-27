import Mathlib
import Submission.Work.Drive.chartPertGroup
import Submission.Work.Drive.chartShiftHsurj
import Submission.Work.Drive.classRowVocab
import Submission.Work.Drive.t6GenAtDBox_refTriple_block1_bundles

/-- Shortcut instance (Lean v4.34 port): on v4.34 Mathlib the generic search for
`ContinuousSMul ℝ E` on real normed spaces such as `EuclideanSpace ℝ (Fin n)` or products of them
detours through `PolynormableSpace.continuousSMul` and exhausts the synthesis budget. -/
private local instance (priority := high) normedSpace_continuousSMul_real_v434 {E : Type*}
    [SeminormedAddCommGroup E] [NormedSpace ℝ E] : ContinuousSMul ℝ E :=
  IsBoundedSMul.continuousSMul


/-!
# The **re-basing of the design parameter** by the perturbation group

This module turns the exact composition law `Work.Drive.chartPert_mul` of `chartPertGroup.lean` into
the consumer-facing statement of the re-basing argument
(`Submission/Work/Drive/CLASSROWS_DENSITY_MECHANISM.md` §2):

> the re-based presentation `chartPert σ k ∘ chartPert χ k ∘ P k` **is** the design's presentation
> `chartPert (qMul σ χ) k ∘ P k` at the parameter `qMul σ χ`,

where `qMul12` is the blockwise product `qMul` on the parameter `𝔼¹²` (level coordinates add, class
coordinates multiply as quaternions).  Consequently **every** condition that is a function of the
triple of presentations — the seven class-level rows, `Meet3Hyp` of the sweeps, `classTripleSet` and
its parity — transfers *exactly*, with no approximation and no openness hypothesis.
-/

namespace Work.Drive

open scoped Manifold ContDiff LinearAlgebra.Projectivization Topology

noncomputable section

set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false

/-! ## 1. The blockwise product on the design parameter `𝔼¹²` -/

/-- **The product of two design parameters**: the blockwise `qMul`. -/
def qMul12 (u x : EuclideanSpace ℝ (Fin 12)) : EuclideanSpace ℝ (Fin 12) :=
  ∑ k : Fin 3, blkSpan k (qMul (blk k u) (blk k x))

/-- The defining property of `qMul12`: the `k`-th block is the `qMul` of the blocks. -/
@[simp] theorem blk_qMul12 (k : Fin 3) (u x : EuclideanSpace ℝ (Fin 12)) :
    blk k (qMul12 u x) = qMul (blk k u) (blk k x) := by
  classical
  rw [qMul12, map_sum]
  rw [Finset.sum_eq_single k]
  · exact blk_blkSpan k _
  · intro j _ hj
    exact blk_blkSpan_of_ne (k := j) (j := k) (Ne.symm hj) _
  · intro hk
    exact absurd (Finset.mem_univ k) hk

/-- **Two parameters of `𝔼¹²` with equal blocks are equal.** -/
theorem eq_of_blk_eq {u x : EuclideanSpace ℝ (Fin 12)}
    (h : ∀ k : Fin 3, blk k u = blk k x) : u = x := by
  refine WithLp.ofLp_injective 2 ?_
  funext i
  set k : Fin 3 := ⟨i.val / 4, by have := i.isLt; omega⟩ with hk
  set j : Fin 4 := ⟨i.val % 4, Nat.mod_lt _ (by norm_num)⟩ with hj
  have hidx : i = blkIdx k j := Fin.ext (by rw [hk, hj]; simp only [blkIdx]; omega)
  rw [hidx, ← blk_apply k u j, ← blk_apply k x j, h k]

/-- The blockwise `qMul` with the zero parameter on the left. -/
@[simp] theorem qMul12_zero_left (x : EuclideanSpace ℝ (Fin 12)) :
    qMul12 0 x = x :=
  eq_of_blk_eq (fun k => by rw [blk_qMul12, map_zero, qMul_zero_left])

/-- The blockwise `qMul` with the zero parameter on the right. -/
@[simp] theorem qMul12_zero_right (u : EuclideanSpace ℝ (Fin 12)) :
    qMul12 u 0 = u :=
  eq_of_blk_eq (fun k => by rw [blk_qMul12, map_zero, qMul_zero_right])

/-! ## 1bis. Continuity of the product in the left factor -/

/-- `pureInner · x` is continuous. -/
theorem continuous_pureInner_right (x : Eucl 3) : Continuous fun σ : Eucl 3 => pureInner σ x := by
  simp only [pureInner]
  fun_prop

/-- `pureCross · x` is continuous. -/
theorem continuous_pureCross_right (x : Eucl 3) : Continuous fun σ : Eucl 3 => pureCross σ x := by
  simp only [pureCross]
  fun_prop

/-- **The left multiplication is continuous at the origin** (where the denominator `1 - ⟪σ,x⟫` does not
vanish). -/
theorem continuousAt_qMul_zero_left (x : Eucl 3) :
    ContinuousAt (fun σ : Eucl 3 => qMul σ x) 0 := by
  have h1 : ContinuousAt (fun σ : Eucl 3 => pureInner σ x) 0 :=
    (continuous_pureInner_right x).continuousAt
  have h2 : ContinuousAt (fun σ : Eucl 3 => pureCross σ x) 0 :=
    (continuous_pureCross_right x).continuousAt
  have h3 : ContinuousAt (fun σ : Eucl 3 => σ 0) 0 :=
    (by fun_prop : Continuous fun σ : Eucl 3 => σ 0).continuousAt
  have hden : ContinuousAt (fun σ : Eucl 3 => (1 - pureInner σ x)⁻¹) 0 :=
    (continuousAt_const.sub h1).inv₀ (by simp [pureInner])
  have hlev : ContinuousAt (fun σ : Eucl 3 => σ 0 + x 0) 0 := h3.add continuousAt_const
  have he0 : ContinuousAt (fun _ : Eucl 3 => (e0 : Eucl 3)) 0 := continuousAt_const
  have hid : ContinuousAt (fun σ : Eucl 3 => σ) 0 := continuousAt_id
  have hxc : ContinuousAt (fun _ : Eucl 3 => x) 0 := continuousAt_const
  have h4 : ContinuousAt (fun σ : Eucl 3 => (-(σ 0 + x 0)) • (e0 : Eucl 3)) 0 :=
    hlev.neg.smul he0
  have hnum : ContinuousAt (fun σ : Eucl 3 =>
      σ + x + pureCross σ x + (-(σ 0 + x 0)) • (e0 : Eucl 3)) 0 :=
    ((hid.add hxc).add h2).add h4
  have hmain : ContinuousAt (fun σ : Eucl 3 =>
      (σ 0 + x 0) • (e0 : Eucl 3) + (1 - pureInner σ x)⁻¹ •
        (σ + x + pureCross σ x + (-(σ 0 + x 0)) • (e0 : Eucl 3))) 0 :=
    (hlev.smul he0).add (hden.smul hnum)
  simpa only [qMul, qPure] using hmain

/-- **The left multiplication tends to the identity**: `qMul σ x → x` as `σ → 0`. -/
theorem tendsto_qMul_zero_left (x : Eucl 3) :
    Filter.Tendsto (fun σ : Eucl 3 => qMul σ x) (𝓝 0) (𝓝 x) := by
  have h : Filter.Tendsto (fun σ : Eucl 3 => qMul σ x) (𝓝 0) (𝓝 (qMul 0 x)) :=
    continuousAt_qMul_zero_left x
  rw [qMul_zero_left] at h
  exact h

/-- **The blockwise product tends to the identity**: `qMul12 σ x → x` as `σ → 0`. -/
theorem tendsto_qMul12_zero_left (x : EuclideanSpace ℝ (Fin 12)) :
    Filter.Tendsto (fun σ : EuclideanSpace ℝ (Fin 12) => qMul12 σ x) (𝓝 0) (𝓝 x) := by
  have hblk : ∀ k : Fin 3, Filter.Tendsto
      (fun σ : EuclideanSpace ℝ (Fin 12) => qMul (blk k σ) (blk k x)) (𝓝 0) (𝓝 (blk k x)) := by
    intro k
    have h1 : Filter.Tendsto (fun σ : EuclideanSpace ℝ (Fin 12) => blk k σ) (𝓝 0) (𝓝 0) := by
      simpa only [map_zero] using (blk k).continuous.tendsto 0
    exact (tendsto_qMul_zero_left (blk k x)).comp h1
  have hsum : (fun σ : EuclideanSpace ℝ (Fin 12) => qMul12 σ x)
      = fun σ => blkSpanCLM 0 (qMul (blk 0 σ) (blk 0 x))
        + blkSpanCLM 1 (qMul (blk 1 σ) (blk 1 x))
        + blkSpanCLM 2 (qMul (blk 2 σ) (blk 2 x)) := by
    funext σ
    rw [qMul12, Fin.sum_univ_three]
    simp only [blkSpanCLM_apply]
  have htarget : blkSpanCLM 0 (blk 0 x) + blkSpanCLM 1 (blk 1 x) + blkSpanCLM 2 (blk 2 x) = x := by
    have h := congrFun hsum 0
    rw [qMul12_zero_left] at h
    simpa only [map_zero, qMul_zero_left] using h.symm
  have h0 : Filter.Tendsto
      (fun σ : EuclideanSpace ℝ (Fin 12) => blkSpanCLM 0 (qMul (blk 0 σ) (blk 0 x)))
      (𝓝 0) (𝓝 (blkSpanCLM 0 (blk 0 x))) :=
    ((blkSpanCLM 0).continuous.tendsto (blk 0 x)).comp (hblk 0)
  have h1 : Filter.Tendsto
      (fun σ : EuclideanSpace ℝ (Fin 12) => blkSpanCLM 1 (qMul (blk 1 σ) (blk 1 x)))
      (𝓝 0) (𝓝 (blkSpanCLM 1 (blk 1 x))) :=
    ((blkSpanCLM 1).continuous.tendsto (blk 1 x)).comp (hblk 1)
  have h2 : Filter.Tendsto
      (fun σ : EuclideanSpace ℝ (Fin 12) => blkSpanCLM 2 (qMul (blk 2 σ) (blk 2 x)))
      (𝓝 0) (𝓝 (blkSpanCLM 2 (blk 2 x))) :=
    ((blkSpanCLM 2).continuous.tendsto (blk 2 x)).comp (hblk 2)
  have hmain : Filter.Tendsto
      (fun σ : EuclideanSpace ℝ (Fin 12) =>
        blkSpanCLM 0 (qMul (blk 0 σ) (blk 0 x)) + blkSpanCLM 1 (qMul (blk 1 σ) (blk 1 x))
          + blkSpanCLM 2 (qMul (blk 2 σ) (blk 2 x))) (𝓝 0) (𝓝 x) := by
    have h := (h0.add h1).add h2
    rwa [htarget] at h
  rw [hsum]
  exact hmain

/-- **The explicit smallness form of the re-basing**, in the shape the density argument of
`CLASSROWS_DENSITY_MECHANISM.md` §2 consumes it: the re-based parameter can be taken arbitrarily
close to the base point `x`. -/
theorem exists_norm_qMul12_sub_lt (x : EuclideanSpace ℝ (Fin 12)) {δ : ℝ} (hδ : 0 < δ) :
    ∃ η : ℝ, 0 < η ∧ ∀ σ : EuclideanSpace ℝ (Fin 12), ‖σ‖ < η →
      ‖qMul12 σ x - x‖ < δ := by
  have h1 : Filter.Tendsto (fun σ : EuclideanSpace ℝ (Fin 12) => qMul12 σ x - x) (𝓝 0) (𝓝 0) := by
    have hc : Filter.Tendsto (fun _ : EuclideanSpace ℝ (Fin 12) => x) (𝓝 0) (𝓝 x) :=
      tendsto_const_nhds
    simpa using (tendsto_qMul12_zero_left x).sub hc
  have hball : {y : EuclideanSpace ℝ (Fin 12) | ‖y‖ < δ} ∈ 𝓝 (0 : EuclideanSpace ℝ (Fin 12)) := by
    have h2 : Metric.ball (0 : EuclideanSpace ℝ (Fin 12)) δ
        = {y : EuclideanSpace ℝ (Fin 12) | ‖y‖ < δ} := by
      ext y
      simp only [Metric.mem_ball, Set.mem_ofPred_eq, dist_zero_right]
    rw [← h2]
    exact Metric.ball_mem_nhds 0 hδ
  obtain ⟨η, hη, hsub⟩ := Metric.mem_nhds_iff.mp (h1.eventually hball)
  exact ⟨η, hη, fun σ hσ => hsub (by rwa [Metric.mem_ball, dist_zero_right])⟩

/-!
## 2. The exact re-basing of the presentations -/

/-- **The re-basing of one presentation.**  If the `k`-th block of the parameter `t` is the product of
the blocks of `σ` and `x`, then the presentation at `t` is the re-based presentation at `σ`. -/
theorem chartPert_rebase {σ x t : EuclideanSpace ℝ (Fin 12)} {k : Fin 3}
    (h : blk k t = qMul (blk k σ) (blk k x)) (hnd : pureInner (blk k σ) (blk k x) ≠ 1) :
    chartPert (blk k t) = chartPert (blk k σ) ∘ chartPert (blk k x) := by
  rw [h]
  exact chartPert_mul (blk k σ) (blk k x) hnd

/-- **The exact re-basing of the design's presentation**: the presentation at the re-based parameter is
the composition `chartPert σ ∘ chartPert x`. -/
theorem designPertPlane_rebase {Q : ℂ → CappingSpace} {u : Fin 3 → UnitAddCircle}
    {σ x t : EuclideanSpace ℝ (Fin 12)} (h : ∀ k : Fin 3, blk k t = qMul (blk k σ) (blk k x))
    (hnd : ∀ k : Fin 3, pureInner (blk k σ) (blk k x) ≠ 1) (k : Fin 3) :
    designPertPlane Q (u k) t k = fun y => chartPert (blk k σ) (designPertPlane Q (u k) x k y) := by
  funext y
  show chartPert (blk k t) (rotPresentation Q (u k) y)
      = chartPert (blk k σ) (chartPert (blk k x) (rotPresentation Q (u k) y))
  rw [chartPert_rebase (h k) (hnd k), Function.comp_apply]

/-- **The exact re-basing of a triple of presentations**, at the level of functions: a pointwise
equality of the three presentations. -/
theorem chartPert_qMul_rebase {P : Fin 3 → EuclideanSpace ℝ (Fin 2) → CappingSpace}
    {σ x t : EuclideanSpace ℝ (Fin 12)} (h : ∀ k : Fin 3, blk k t = qMul (blk k σ) (blk k x))
    (hnd : ∀ k : Fin 3, pureInner (blk k σ) (blk k x) ≠ 1) :
    (fun k z => chartPert (blk k t) (P k z))
      = fun k z => chartPert (blk k σ) (chartPert (blk k x) (P k z)) := by
  funext k z
  rw [chartPert_rebase (h k) (hnd k), Function.comp_apply]

/-- **The exact re-basing of `classTripleSet`**: the class-triple set of the design's triple at the
re-based parameter is the class-triple set of the re-based triple. -/
theorem classTripleSet_rebase {P : Fin 3 → EuclideanSpace ℝ (Fin 2) → CappingSpace}
    {σ x t : EuclideanSpace ℝ (Fin 12)} (h : ∀ k : Fin 3, blk k t = qMul (blk k σ) (blk k x))
    (hnd : ∀ k : Fin 3, pureInner (blk k σ) (blk k x) ≠ 1) :
    classTripleSet (fun k z => chartPert (blk k t) (P k z))
      = classTripleSet (fun k z => chartPert (blk k σ) (chartPert (blk k x) (P k z))) := by
  rw [chartPert_qMul_rebase h hnd]

/-- **The exact re-basing of `classTripleSet` for the design's triple** in the form of the `hn2`/`hdense`
producers: the class-triple set at the parameter `qMul12 σ x` is that of the re-based triple. -/
theorem classTripleSet_rebase_qMul12 {P : Fin 3 → EuclideanSpace ℝ (Fin 2) → CappingSpace}
    (σ x : EuclideanSpace ℝ (Fin 12)) (hnd : ∀ k : Fin 3, pureInner (blk k σ) (blk k x) ≠ 1) :
    classTripleSet (fun k z => chartPert (blk k (qMul12 σ x)) (P k z))
      = classTripleSet (fun k z => chartPert (blk k σ) (chartPert (blk k x) (P k z))) :=
  classTripleSet_rebase (fun k => blk_qMul12 k σ x) hnd

/-! ## 3. The class-triple set is blind to the level coordinates -/

/-- The class-triple set depends only on the *class maps* of the three presentations. -/
theorem classTripleSet_congr {F G : Fin 3 → EuclideanSpace ℝ (Fin 2) → CappingSpace}
    (h : ∀ k : Fin 3, planeClassMap (F k) = planeClassMap (G k)) :
    classTripleSet F = classTripleSet G := by
  simp only [classTripleSet, h]

/-- **The class-triple set is invariant under a shift of the perturbation parameter in the level
direction** (`Work.Drive.classMap_add_smul_e0`): only the class coordinates of `τ` matter. -/
theorem classTripleSet_levelShift (P : Fin 3 → EuclideanSpace ℝ (Fin 2) → CappingSpace)
    (τ : Fin 3 → Eucl 3) (a : Fin 3 → ℝ) :
    classTripleSet (fun k z => chartPert (τ k + a k • (e0 : Eucl 3)) (P k z))
      = classTripleSet (fun k z => chartPert (τ k) (P k z)) :=
  classTripleSet_congr fun k => planeClassMap_chartPert_add_smul_e0 (τ k) (a k) (P k)

/-! ## 4. The density transfer: from the accumulation at `0` of a re-based triple to density at every
point of the ball

This is the exact form of the re-basing argument of `CLASSROWS_DENSITY_MECHANISM.md` §2, with the
transfer made *exact* by `Work.Drive.classTripleSet_rebase_qMul12`: **no openness hypothesis** and no
approximation is needed.  The hypothesis `hbase` is what the one-point producers supply for the
*re-based* triple `k ↦ chartPert (blk k x) ∘ P k` (they are generic in the three presentations, and
`Work.Drive.classTripleSet_levelShift` allows the level coordinates of `x` to be adjusted first, which
is what the producers' level hypotheses require). -/

/-- The smallness set of `qMul12 · x - x` is a neighbourhood of `0`. -/
theorem eventually_norm_qMul12_sub_lt (x : EuclideanSpace ℝ (Fin 12)) {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ σ : EuclideanSpace ℝ (Fin 12) in 𝓝 0, ‖qMul12 σ x - x‖ < δ := by
  have h1 : Filter.Tendsto (fun σ : EuclideanSpace ℝ (Fin 12) => qMul12 σ x - x) (𝓝 0) (𝓝 0) := by
    have hc : Filter.Tendsto (fun _ : EuclideanSpace ℝ (Fin 12) => x) (𝓝 0) (𝓝 x) :=
      tendsto_const_nhds
    simpa using (tendsto_qMul12_zero_left x).sub hc
  have hball : {y : EuclideanSpace ℝ (Fin 12) | ‖y‖ < δ} ∈ 𝓝 (0 : EuclideanSpace ℝ (Fin 12)) := by
    have h2 : Metric.ball (0 : EuclideanSpace ℝ (Fin 12)) δ
        = {y : EuclideanSpace ℝ (Fin 12) | ‖y‖ < δ} := by
      ext y
      simp only [Metric.mem_ball, Set.mem_ofPred_eq, dist_zero_right]
    rw [← h2]
    exact Metric.ball_mem_nhds 0 hδ
  exact h1.eventually hball

/-- **THE DENSITY TRANSFER.**  If for the *re-based* triple `k ↦ chartPert (blk k x) ∘ P k` the
oddness of the class-triple set holds at parameters arbitrarily close to `0`, then the oddness of the
class-triple set of `P` (perturbed at the parameter `t`) holds at parameters `t` arbitrarily close to
`x`. -/
theorem exists_odd_classTripleSet_near_qMul {P : Fin 3 → EuclideanSpace ℝ (Fin 2) → CappingSpace}
    {x : EuclideanSpace ℝ (Fin 12)}
    (hbase : ∀ η : ℝ, 0 < η → ∃ σ : EuclideanSpace ℝ (Fin 12), ‖σ‖ < η ∧
      Odd (classTripleSet (fun k z => chartPert (blk k σ) (chartPert (blk k x) (P k z)))).ncard)
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ t : EuclideanSpace ℝ (Fin 12), ‖t - x‖ < δ ∧
      Odd (classTripleSet (fun k z => chartPert (blk k t) (P k z))).ncard := by
  have hev : ∀ᶠ σ : EuclideanSpace ℝ (Fin 12) in 𝓝 0,
      ∀ k : Fin 3, pureInner (blk k σ) (blk k x) ≠ 1 := by
    rw [Filter.eventually_all]
    intro k
    have hcont : Continuous fun σ : EuclideanSpace ℝ (Fin 12) =>
        pureInner (blk k σ) (blk k x) :=
      (continuous_pureInner_right (blk k x)).comp (blk k).continuous
    refine hcont.continuousAt.eventually_ne ?_
    simp [map_zero, pureInner]
  have hmem : {σ : EuclideanSpace ℝ (Fin 12) |
        ‖qMul12 σ x - x‖ < δ ∧ (∀ k : Fin 3, pureInner (blk k σ) (blk k x) ≠ 1)} ∈
      𝓝 (0 : EuclideanSpace ℝ (Fin 12)) :=
    (eventually_norm_qMul12_sub_lt x hδ).and hev
  obtain ⟨η', hη', hsub⟩ := Metric.mem_nhds_iff.mp hmem
  obtain ⟨σ, hσ, hodd⟩ := hbase η' hη'
  have hσmem : σ ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin 12)) η' := by
    rwa [Metric.mem_ball, dist_zero_right]
  obtain ⟨hd, hnd⟩ := hsub hσmem
  exact ⟨qMul12 σ x, hd, by rw [classTripleSet_rebase_qMul12 σ x hnd]; exact hodd⟩

end

end Work.Drive
