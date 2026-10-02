import Mathlib

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.ThomBordism

open scoped Manifold ContDiff ENNReal Topology
open Set Filter

noncomputable section

/-- The ambient quadratic function `y ↦ ‖y‖ ^ 2 - 6 * y 0 + 8` on `ℝⁿ`.

It is the "amended" height function whose sublevel set `{Φ ≤ 0}` is the ball of radius one
around `(3, 0, …, 0)`; in particular it is negative exactly on a compact set strictly inside the
open half-space `{y 0 > 0}`. -/
def tangentBallAmb (n : ℕ) [NeZero n] : EuclideanSpace ℝ (Fin n) → ℝ :=
  fun y => ‖y‖ ^ 2 - 6 * (y 0) + 8

/-- The restriction of `tangentBallAmb` to the Euclidean half-space `{x 0 ≥ 0}`. -/
def tangentBallHs (n : ℕ) [NeZero n] : EuclideanHalfSpace n → ℝ :=
  fun x => tangentBallAmb n x.1

lemma contDiff_tangentBallAmb (n : ℕ) [NeZero n] :
    ContDiff ℝ ∞ (tangentBallAmb n) := by
  have h1 : ContDiff ℝ ∞ (fun y : EuclideanSpace ℝ (Fin n) => ‖y‖ ^ 2) :=
    contDiff_norm_sq ℝ
  have h2 : ContDiff ℝ ∞ (fun y : EuclideanSpace ℝ (Fin n) => y 0) :=
    (EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin n)).contDiff
  have h3 : ContDiff ℝ ∞ (fun y : EuclideanSpace ℝ (Fin n) => 6 * (y 0)) :=
    (contDiff_const (c := (6:ℝ))).mul h2
  have h4 : ContDiff ℝ ∞ (fun _ : EuclideanSpace ℝ (Fin n) => (8:ℝ)) := contDiff_const
  unfold tangentBallAmb
  exact (h1.sub h3).add h4

lemma contMDiff_tangentBallHs (n : ℕ) [NeZero n] :
    ContMDiff (𝓡∂ n) 𝓘(ℝ,ℝ) ∞ (tangentBallHs n) := by
  intro x
  rw [contMDiffAt_iff_source, contMDiffWithinAt_iff_contDiffWithinAt]
  have hΘ : ContDiffOn ℝ ∞
      (fun y : EuclideanSpace ℝ (Fin n) => tangentBallHs n ((𝓡∂ n).symm y))
      (range (𝓡∂ n)) := by
    refine (contDiff_tangentBallAmb n).contDiffOn.congr ?_
    intro y hy
    obtain ⟨w, hw⟩ := hy
    have hy0 : 0 ≤ y 0 := by rw [← hw]; exact w.2
    rw [modelWithCornersEuclideanHalfSpace_symm_apply_of_le hy0]
    rfl
  exact hΘ.contDiffWithinAt (mem_range_self x)

lemma mfderiv_tangentBallHs_ne_zero (n : ℕ) [NeZero n] {x : EuclideanHalfSpace n}
    (hx : tangentBallHs n x = 0) :
    mfderiv (𝓡∂ n) 𝓘(ℝ,ℝ) (tangentBallHs n) x ≠ 0 := by
  have hcont : ContinuousAt (tangentBallHs n) x :=
    ((contDiff_tangentBallAmb n).continuous.comp continuous_subtype_val).continuousAt
  set l : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ :=
    2 • innerSL ℝ (x.1) - (6:ℝ) • (EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin n)) with hl_def
  have hfd_at : HasFDerivAt (tangentBallAmb n) l (x.1) := by
    have h1 : HasFDerivAt (fun y : EuclideanSpace ℝ (Fin n) => ‖y‖ ^ 2)
        (2 • innerSL ℝ (x.1)) (x.1) := by
      have h := ((contDiff_norm_sq (𝕜 := ℝ) (E := EuclideanSpace ℝ (Fin n))
        (n := ∞)).differentiable (by simp) (x.1)).hasFDerivAt
      rw [fderiv_norm_sq] at h
      simpa using h
    have h2 : HasFDerivAt (fun y : EuclideanSpace ℝ (Fin n) => y 0)
        (EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin n)) (x.1) := by
      simpa using ContinuousLinearMap.hasFDerivAt (EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin n))
    have h3 : HasFDerivAt (fun y : EuclideanSpace ℝ (Fin n) => 6 * (y 0))
        ((6:ℝ) • (EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin n))) (x.1) := by
      simpa using h2.const_mul (6 : ℝ)
    have h4 : HasFDerivAt (fun _ : EuclideanSpace ℝ (Fin n) => (8:ℝ))
        (0 : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) (x.1) := hasFDerivAt_const 8 _
    have hall := (h1.sub h3).add h4
    convert hall using 1
    all_goals first | rfl | simp [hl_def]
  have hwritten : writtenInExtChartAt (𝓡∂ n) 𝓘(ℝ,ℝ) x (tangentBallHs n)
      = fun y : EuclideanSpace ℝ (Fin n) => tangentBallHs n ((𝓡∂ n).symm y) := by
    funext y
    simp only [writtenInExtChartAt, Function.comp_apply]
    rfl
  have hΘeq : (fun y : EuclideanSpace ℝ (Fin n) => tangentBallHs n ((𝓡∂ n).symm y))
      =ᶠ[𝓝[range (⇑(𝓡∂ n))] (x.1)] (tangentBallAmb n) := by
    filter_upwards [self_mem_nhdsWithin] with y hy
    obtain ⟨w, hw⟩ := hy
    have hy0 : 0 ≤ y 0 := by rw [← hw]; exact w.2
    rw [modelWithCornersEuclideanHalfSpace_symm_apply_of_le hy0]
    rfl
  have hxeq : (fun y : EuclideanSpace ℝ (Fin n) => tangentBallHs n ((𝓡∂ n).symm y)) (x.1)
      = tangentBallAmb n (x.1) := by
    simp only []
    rw [modelWithCornersEuclideanHalfSpace_symm_apply_of_le x.2]
    rfl
  have hfdw : HasFDerivWithinAt (writtenInExtChartAt (𝓡∂ n) 𝓘(ℝ,ℝ) x (tangentBallHs n)) l
      (range (⇑(𝓡∂ n))) (x.1) := by
    rw [hwritten]
    exact (Filter.EventuallyEq.hasFDerivWithinAt_iff hΘeq hxeq).2 hfd_at.hasFDerivWithinAt
  have hmfd : HasMFDerivAt (𝓡∂ n) 𝓘(ℝ,ℝ) (tangentBallHs n) x l := ⟨hcont, hfdw⟩
  have hm : mfderiv (𝓡∂ n) 𝓘(ℝ,ℝ) (tangentBallHs n) x = l := hmfd.mfderiv
  rw [hm]
  intro hl
  set v : EuclideanSpace ℝ (Fin n) := x.1 - (3:ℝ) • EuclideanSpace.single (0 : Fin n) 1
    with hv_def
  have hv0 : v 0 = x.1 0 - 3 := by
    simp only [hv_def, PiLp.sub_apply, PiLp.smul_apply, PiLp.single_apply,
      ↓reduceIte, smul_eq_mul, mul_one]
  have hinner : inner ℝ x.1 v = ‖x.1‖ ^ 2 - 3 * (x.1 0) := by
    rw [hv_def, inner_sub_right, inner_smul_right, real_inner_self_eq_norm_sq,
      EuclideanSpace.inner_single_right]
    simp
  have hev : l v = 2 := by
    have h1 : l v = 2 * inner ℝ x.1 v - 6 * (v 0) := by
      simp only [hl_def, sub_apply, smul_apply, innerSL_apply_apply, EuclideanSpace.coe_proj,
        nsmul_eq_mul, smul_eq_mul]
      norm_num
    rw [h1, hinner, hv0]
    have h2 := hx
    simp only [tangentBallHs, tangentBallAmb] at h2
    linarith
  have hv : l v = 0 := by rw [hl]; rfl
  rw [hev] at hv
  norm_num at hv

lemma tangentBallHs_ne_zero_of_mem_boundary (n : ℕ) [NeZero n] {x : EuclideanHalfSpace n}
    (hx : x ∈ (𝓡∂ n).boundary (EuclideanHalfSpace n)) : tangentBallHs n x ≠ 0 := by
  have hx' : x.1 ∈ frontier (range (⇑(𝓡∂ n))) := hx
  rw [range_modelWithCornersEuclideanHalfSpace, frontier_halfSpace] at hx'
  have h0 : x.1 0 = 0 := hx'.symm
  have hval : tangentBallHs n x = ‖x.1‖ ^ 2 + 8 := by
    simp only [tangentBallHs, tangentBallAmb, h0, mul_zero, sub_zero]
  rw [hval]
  positivity

lemma isCompact_tangentBallHs (n : ℕ) [NeZero n] :
    IsCompact {x : EuclideanHalfSpace n | tangentBallHs n x ≤ 0} := by
  have hclosed : IsClosed {y : EuclideanSpace ℝ (Fin n) | tangentBallAmb n y ≤ 0} :=
    isClosed_le (contDiff_tangentBallAmb n).continuous continuous_const
  have hbdd : {y : EuclideanSpace ℝ (Fin n) | tangentBallAmb n y ≤ 0} ⊆
      Metric.closedBall 0 4 := by
    intro y hy
    have hy' : tangentBallAmb n y ≤ 0 := hy
    rw [Metric.mem_closedBall, dist_zero_right]
    by_contra h
    have hlt : 4 < ‖y‖ := not_le.mp h
    have hy0 : y 0 ≤ ‖y‖ := by
      have h1 := PiLp.norm_apply_le (p := 2) (β := fun _ : Fin n => ℝ) y 0
      have h2 : ‖y.ofLp 0‖ = |y 0| := by simp
      rw [h2] at h1
      calc y 0 ≤ |y 0| := le_abs_self _
        _ ≤ ‖y‖ := h1
    have h3 : 0 < ‖y‖ ^ 2 - 6 * ‖y‖ + 8 := by nlinarith [norm_nonneg y]
    have h4 : 0 < tangentBallAmb n y := by
      simp only [tangentBallAmb]
      linarith
    linarith
  have hS : IsCompact {y : EuclideanSpace ℝ (Fin n) | tangentBallAmb n y ≤ 0} :=
    IsCompact.of_isClosed_subset (isCompact_closedBall 0 4) hclosed hbdd
  have hEmb : Topology.IsClosedEmbedding
      (Subtype.val : EuclideanHalfSpace n → EuclideanSpace ℝ (Fin n)) :=
    (show IsClosed {y : EuclideanSpace ℝ (Fin n) | 0 ≤ y 0} from
      isClosed_le continuous_const
        (EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin n)).continuous).isClosedEmbedding_subtypeVal
  have hset : {x : EuclideanHalfSpace n | tangentBallHs n x ≤ 0} =
      Subtype.val ⁻¹' {y : EuclideanSpace ℝ (Fin n) | tangentBallAmb n y ≤ 0} := rfl
  rw [hset]
  exact hEmb.isCompact_preimage hS

theorem tangentBall_regionSetupCore (k : ℕ) :
    let Φ : EuclideanHalfSpace ((8 + k) + 1) → ℝ := fun x => ‖x.1‖ ^ 2 - 6 * (x.1 0) + 8
    ContMDiff (modelWithCornersEuclideanHalfSpace ((8 + k) + 1)) (modelWithCornersSelf ℝ ℝ)
        ((⊤ : ENat) : WithTop ENat) Φ ∧
      (∀ x : EuclideanHalfSpace ((8 + k) + 1), Φ x = 0 →
        mfderiv (modelWithCornersEuclideanHalfSpace ((8 + k) + 1)) (modelWithCornersSelf ℝ ℝ)
          Φ x ≠ 0) ∧
      (∀ x ∈ (modelWithCornersEuclideanHalfSpace ((8 + k) + 1)).boundary
            (EuclideanHalfSpace ((8 + k) + 1)), Φ x ≠ 0) ∧
      IsCompact {x : EuclideanHalfSpace ((8 + k) + 1) | Φ x ≤ 0} := by
  dsimp only
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact contMDiff_tangentBallHs ((8 + k) + 1)
  · intro x hx
    exact mfderiv_tangentBallHs_ne_zero ((8 + k) + 1) hx
  · intro x hx
    exact tangentBallHs_ne_zero_of_mem_boundary ((8 + k) + 1) hx
  · exact isCompact_tangentBallHs ((8 + k) + 1)

end

end Work.ThomBordism
