/-
# Savin's Proposition 4.1: assembly of the linear theory at the limit

This file assembles the two halves built earlier:

* `Submission.Savin.Equicont.exists_subseq_tendstoUniformly` / `isViscSolution_limit_s2` produce a
  limit `g` of a family `v k` of solutions of the small-perturbation equation with `e k → 0`, and
  show that `g` is a genuine viscosity solution of the linearised equation
  `-tr (cofOp Nlim ∘ D²·) = 0`;
* `Submission.Savin.LinearQuad.linear_quadratic_approx` then produces a quadratic approximation of
  `g` by a quadratic `P` with `trOp (cofOp Nlim * D²P) = 0`, with error `≤ C θ³`.

The main result of the file is `Submission.quadratic_approx_of_limit`.
-/
import Mathlib
import ChallengeDeps
import Submission.Savin.Equicont
import Submission.Savin.LinearQuad
import Submission.Savin.Stability

open Metric MeasureTheory Filter Set
open scoped BigOperators RealInnerProductSpace Topology ENNReal Pointwise

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 4000000

namespace Submission

local notation "ℝ⁴" => EuclideanSpace ℝ (Fin 4)

noncomputable section

/-- The quadratic form of an operator is continuous in the operator. -/
theorem continuous_quadform (u : ℝ⁴) :
    Continuous (fun M : ℝ⁴ →L[ℝ] ℝ⁴ => ⟪M u, u⟫) :=
  Continuous.inner ((ContinuousLinearMap.apply ℝ ℝ⁴ u).continuous) continuous_const

/-- Symmetry is preserved by limits. -/
theorem isSymmetric_of_tendsto {N : ℕ → ℝ⁴ →L[ℝ] ℝ⁴} {Nlim : ℝ⁴ →L[ℝ] ℝ⁴}
    (h : Tendsto N atTop (𝓝 Nlim)) (hN : ∀ k, (N k).IsSymmetric) : Nlim.IsSymmetric := by
  change ∀ u w, ⟪Nlim u, w⟫ = ⟪u, Nlim w⟫
  intro u w
  have h1 : Tendsto (fun k => ⟪N k u, w⟫) atTop (𝓝 ⟪Nlim u, w⟫) := by
    have hc : Continuous (fun M : ℝ⁴ →L[ℝ] ℝ⁴ => ⟪M u, w⟫) :=
      Continuous.inner ((ContinuousLinearMap.apply ℝ ℝ⁴ u).continuous) continuous_const
    exact (hc.tendsto Nlim).comp h
  have h2 : Tendsto (fun k => ⟪u, N k w⟫) atTop (𝓝 ⟪u, Nlim w⟫) := by
    have hc : Continuous (fun M : ℝ⁴ →L[ℝ] ℝ⁴ => ⟪u, M w⟫) :=
      Continuous.inner continuous_const ((ContinuousLinearMap.apply ℝ ℝ⁴ w).continuous)
    exact (hc.tendsto Nlim).comp h
  have h3 : (fun k => ⟪N k u, w⟫) = fun k => ⟪u, N k w⟫ := by
    funext k
    exact hN k u w
  rw [h3] at h1
  exact tendsto_nhds_unique h1 h2

/-- **The quadratic approximation of the limit of a family of small-perturbation solutions.**

Given `v k` solving `s2 (N k + e k • D²v k) = 1` with the positive branch on `ball 0 1`, with
`e k → 0`, `N k` in the ellipticity class (`cofOp (N k) ∈ [c,c']`), `‖v k‖ ≤ 1`, converging locally
uniformly to `g` (along a subsequence, with `N k → Nlim`), the limit `g` is approximated on
`closedBall 0 θ` by a quadratic `P` with `trOp (cofOp Nlim * D²P) = 0`, with error `≤ C θ³` and `C`
depending only on `c`, `c'`. -/
theorem quadratic_approx_of_limit {c c' : ℝ} (hc : 0 < c) (hc' : 0 < c') :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ → ℝ⁴ →L[ℝ] ℝ⁴) (e : ℕ → ℝ) (v : ℕ → ℝ⁴ → ℝ)
      (Nlim : ℝ⁴ →L[ℝ] ℝ⁴) (g : ℝ⁴ → ℝ) (φ : ℕ → ℕ)
      (hN : ∀ k, (N (φ k)).IsSymmetric) (hN1 : ∀ k, s2 (N (φ k)) = 1)
      (htrN : ∀ k, 0 < trOp (N (φ k))) (he0 : ∀ k, 0 < e (φ k))
      (hcq : ∀ k u, c * ‖u‖ ^ 2 ≤ ⟪cofOp (N (φ k)) u, u⟫)
      (hcq' : ∀ k u, ⟪cofOp (N (φ k)) u, u⟫ ≤ c' * ‖u‖ ^ 2)
      (hNtend : Tendsto (fun k => N (φ k)) atTop (𝓝 Nlim))
      (hetend : Tendsto (fun k => e (φ k)) atTop (𝓝 0))
      (hv : ∀ k, ContDiffOn ℝ 2 (v (φ k)) (ball 0 1))
      (heq : ∀ k, ∀ x ∈ ball 0 1, s2 (N (φ k) + e (φ k) • hessOp (v (φ k)) x) = 1)
      (hpos : ∀ k, ∀ x ∈ ball 0 1, 0 < trOp (N (φ k) + e (φ k) • hessOp (v (φ k)) x))
      (hbdd : ∀ k, ∀ x ∈ ball 0 1, |v (φ k) x| ≤ 1)
      (hconv : ∀ K, K ⊆ ball 0 1 → IsCompact K → TendstoUniformlyOn (fun k => v (φ k)) g atTop K)
      (θ : ℝ) (hθ : 0 < θ) (hθ2 : θ ≤ 1 / 2) (hθ1 : 2 * θ * Real.sqrt (c' / c) ≤ 1 / 2),
      ∃ (P₂ : ℝ⁴ →L[ℝ] ℝ⁴) (P₁ : ℝ⁴ →L[ℝ] ℝ) (P₀ : ℝ),
        P₂.IsSymmetric ∧ trOp (cofOp Nlim * P₂) = 0 ∧
        ∀ x ∈ closedBall 0 θ, |g x - (⟪P₂ x, x⟫ / 2 + P₁ x + P₀)| ≤ C * θ ^ 3 := by
  obtain ⟨C, hCpos, hC⟩ := linear_quadratic_approx_uniform hc hc'
  refine ⟨C, hCpos, ?_⟩
  intro N e v Nlim g φ hN hN1 htrN he0 hcq hcq' hNtend hetend hv heq hpos hbdd hconv
    θ hθ hθ2 hθ1
  have hNlim : Nlim.IsSymmetric := isSymmetric_of_tendsto hNtend hN
  have hcq_lim : ∀ u : ℝ⁴, c * ‖u‖ ^ 2 ≤ ⟪cofOp Nlim u, u⟫ := by
    intro u
    have h1 : Tendsto (fun k => ⟪cofOp (N (φ k)) u, u⟫) atTop (𝓝 ⟪cofOp Nlim u, u⟫) :=
      ((continuous_quadform u).tendsto (cofOp Nlim)).comp (tendsto_cofOp hNtend)
    exact ge_of_tendsto h1 (Filter.Eventually.of_forall fun k => hcq k u)
  have hcq'_lim : ∀ u : ℝ⁴, ⟪cofOp Nlim u, u⟫ ≤ c' * ‖u‖ ^ 2 := by
    intro u
    have h1 : Tendsto (fun k => ⟪cofOp (N (φ k)) u, u⟫) atTop (𝓝 ⟪cofOp Nlim u, u⟫) :=
      ((continuous_quadform u).tendsto (cofOp Nlim)).comp (tendsto_cofOp hNtend)
    exact le_of_tendsto h1 (Filter.Eventually.of_forall fun k => hcq' k u)
  have hisvisc : IsViscSolution (fun M => -trOp (cofOp Nlim * M)) g (ball 0 1) := by
    have h := isViscSolution_limit_s2 (s := ball 0 1) isOpen_ball (N := fun k => N (φ k))
      (e := fun k => e (φ k))
      (v := fun k => v (φ k)) (Nlim := Nlim) (g := g) hc hc'.le hN hN1 htrN he0 hcq hcq'
      hNtend hetend hv heq hpos hconv
    have h1 : (fun M => -pairOp (cofOp Nlim) M) = fun M => -trOp (cofOp Nlim * M) := by
      funext M
      rw [show pairOp (cofOp Nlim) M = trOp (cofOp Nlim * M) from by
        rw [pairOp_eq_trace, trOp]; rfl]
    rwa [h1] at h
  have hK : IsCompact (closedBall (0 : ℝ⁴) θ) := isCompact_closedBall 0 θ
  have hsub : closedBall (0 : ℝ⁴) θ ⊆ ball 0 1 := by
    intro z hz
    rw [mem_closedBall, dist_zero_right] at hz
    rw [mem_ball, dist_zero_right]
    linarith
  have hconvθ : TendstoUniformlyOn (fun k => v (φ k)) g atTop (closedBall 0 θ) :=
    hconv _ hsub hK
  have hgcont : ContinuousOn g (ball 0 1) := by
    intro x hx
    obtain ⟨r, hrpos, hrsub⟩ := Metric.mem_nhds_iff.mp (isOpen_ball.mem_nhds hx)
    have h1 : closedBall x (r / 2) ⊆ ball 0 1 := fun z hz =>
      hrsub (closedBall_subset_ball (by linarith) hz)
    have h2 : TendstoUniformlyOn (fun k => v (φ k)) g atTop (closedBall x (r / 2)) :=
      hconv _ h1 (isCompact_closedBall x (r / 2))
    have h3 : ContinuousOn g (closedBall x (r / 2)) := by
      refine h2.continuousOn (Filter.Frequently.of_forall ?_)
      intro k
      exact ((hv k).continuousOn).mono h1
    have h4 : x ∈ closedBall x (r / 2) := by rw [mem_closedBall, dist_self]; positivity
    exact (h3.continuousWithinAt h4).mono_of_mem_nhdsWithin
      (mem_nhdsWithin_of_mem_nhds (closedBall_mem_nhds x (by linarith)))
  have hgbdd : ∀ x ∈ ball 0 1, |g x| ≤ 1 := by
    intro x hx
    obtain ⟨r, hrpos, hrsub⟩ := Metric.mem_nhds_iff.mp (isOpen_ball.mem_nhds hx)
    have h1 : closedBall x (r / 2) ⊆ ball 0 1 := fun z hz =>
      hrsub (closedBall_subset_ball (by linarith) hz)
    have h2 : TendstoUniformlyOn (fun k => v (φ k)) g atTop (closedBall x (r / 2)) :=
      hconv _ h1 (isCompact_closedBall x (r / 2))
    have hxmem : x ∈ closedBall x (r / 2) := by rw [mem_closedBall, dist_self]; positivity
    have h3 : Tendsto (fun k => v (φ k) x) atTop (𝓝 (g x)) := by
      rw [Metric.tendsto_atTop]
      intro ε hε
      rw [← Filter.eventually_atTop]
      have h4 := (tendstoUniformlyOn_iff.mp h2) ε hε
      filter_upwards [h4] with k hk
      have h5 := hk x hxmem
      rw [Real.dist_eq] at h5 ⊢
      rwa [abs_sub_comm]
    exact le_of_tendsto h3.abs (Filter.Eventually.of_forall fun k => hbdd k x hx)
  exact hC Nlim hNlim hcq_lim hcq'_lim θ hθ hθ1 g hgcont hisvisc hgbdd

/-- The matrix entries of a symmetric operator are bounded by any bound for its quadratic form. -/
theorem abs_entry_le {T : ℝ⁴ →L[ℝ] ℝ⁴} (hT : T.IsSymmetric) {K : ℝ} (hK : 0 ≤ K)
    (h : ∀ v : ℝ⁴, |⟪T v, v⟫| ≤ K * ‖v‖ ^ 2) (i j : Fin 4) :
    |⟪T (stdB4 i), stdB4 j⟫| ≤ K := by
  by_cases hij : i = j
  · rw [hij]
    have h1 := h (stdB4 j)
    rw [OrthonormalBasis.norm_eq_one stdB4 j, one_pow, mul_one] at h1
    exact h1
  · have hsym : ∀ x y : ℝ⁴, ⟪T x, y⟫ = ⟪x, T y⟫ := fun x y => hT x y
    have hpol : 4 * ⟪T (stdB4 i), stdB4 j⟫
        = ⟪T (stdB4 i + stdB4 j), stdB4 i + stdB4 j⟫
          - ⟪T (stdB4 i - stdB4 j), stdB4 i - stdB4 j⟫ := by
      simp only [map_add, map_sub, inner_add_left, inner_add_right, inner_sub_left,
        inner_sub_right]
      rw [hsym (stdB4 j) (stdB4 i), real_inner_comm (stdB4 j) (T (stdB4 i))]
      ring
    have h1 := h (stdB4 i + stdB4 j)
    have h2 := h (stdB4 i - stdB4 j)
    have h3 : ‖stdB4 i + stdB4 j‖ ^ 2 + ‖stdB4 i - stdB4 j‖ ^ 2 = 4 := by
      rw [parallelogram_law_with_norm ℝ, OrthonormalBasis.norm_eq_one stdB4 i,
        OrthonormalBasis.norm_eq_one stdB4 j]
      norm_num
    have h4 : |⟪T (stdB4 i + stdB4 j), stdB4 i + stdB4 j⟫
        - ⟪T (stdB4 i - stdB4 j), stdB4 i - stdB4 j⟫| ≤ K * 4 := by
      have ha1 := (abs_le.mp h1).1
      have ha2 := (abs_le.mp h1).2
      have hb1 := (abs_le.mp h2).1
      have hb2 := (abs_le.mp h2).2
      have h8 : K * ‖stdB4 i + stdB4 j‖ ^ 2 + K * ‖stdB4 i - stdB4 j‖ ^ 2 = K * 4 := by
        rw [← mul_add, h3]
      rw [abs_le]
      constructor <;> linarith [ha1, ha2, hb1, hb2, h8]
    have h7 : (4:ℝ) * |⟪T (stdB4 i), stdB4 j⟫|
        = |⟪T (stdB4 i + stdB4 j), stdB4 i + stdB4 j⟫
          - ⟪T (stdB4 i - stdB4 j), stdB4 i - stdB4 j⟫| := by
      rw [← hpol, abs_mul, abs_of_pos (by norm_num : (0:ℝ) < 4)]
    have h5 : (4:ℝ) * |⟪T (stdB4 i), stdB4 j⟫| ≤ 4 * K := by
      rw [h7]
      linarith [h4]
    nlinarith [h5]

/-- The operator norm of `cofOp N` for `N` in the ellipticity class. -/
theorem norm_cofOp_le {N : ℝ⁴ →L[ℝ] ℝ⁴} (hN : N.IsSymmetric) {c c' : ℝ} (hc : 0 < c)
    (hc' : 0 ≤ c') (hcq : ∀ u : ℝ⁴, c * ‖u‖ ^ 2 ≤ ⟪cofOp N u, u⟫)
    (hcq' : ∀ u : ℝ⁴, ⟪cofOp N u, u⟫ ≤ c' * ‖u‖ ^ 2) :
    ‖cofOp N‖ ≤ 16 * max c c' := by
  have hK : 0 ≤ max c c' := le_trans hc.le (le_max_left _ _)
  have hsym : (cofOp N).IsSymmetric := cofOp_isSymmetric hN
  have habs : ∀ v : ℝ⁴, |⟪cofOp N v, v⟫| ≤ max c c' * ‖v‖ ^ 2 := by
    intro v
    rw [abs_le]
    constructor
    · nlinarith [hcq v, sq_nonneg ‖v‖, le_max_left c c', hc.le]
    · nlinarith [hcq' v, sq_nonneg ‖v‖, le_max_right c c']
  refine le_trans (norm_le_sum_abs_inner _) ?_
  refine le_trans (Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ =>
    abs_entry_le hsym hK habs i j) ?_
  refine le_of_eq ?_
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  ring

/-- A base in the ellipticity class is bounded. -/
theorem norm_base_le {N : ℝ⁴ →L[ℝ] ℝ⁴} (hN : N.IsSymmetric) {c c' : ℝ} (hc : 0 < c)
    (hc' : 0 ≤ c') (hcq : ∀ u : ℝ⁴, c * ‖u‖ ^ 2 ≤ ⟪cofOp N u, u⟫)
    (hcq' : ∀ u : ℝ⁴, ⟪cofOp N u, u⟫ ≤ c' * ‖u‖ ^ 2) :
    ‖N‖ ≤ 4 * c' / 3 + 16 * max c c' := by
  have hNdef : N = trOp N • (1 : ℝ⁴ →L[ℝ] ℝ⁴) - cofOp N := by
    rw [cofOp]; abel
  have htr : trOp N ≤ 4 * c' / 3 := by
    have h1 : trOp (cofOp N) ≤ 4 * c' := trOp_le_of_quadform_le hcq'
    have h2 : trOp (cofOp N) = 3 * trOp N := by
      rw [cofOp, trOp_sub, trOp_smul, trOp_one]
      ring_nf
    linarith
  have htrco : 0 ≤ trOp (cofOp N) := by
    rw [trOp_eq_sum]
    refine Finset.sum_nonneg fun i _ => ?_
    have h1 := hcq (stdB4 i)
    rw [OrthonormalBasis.norm_eq_one stdB4 i, one_pow, mul_one] at h1
    linarith [h1, hc]
  have htrnn : 0 ≤ trOp N := by
    have h2 : trOp (cofOp N) = 3 * trOp N := by
      rw [cofOp, trOp_sub, trOp_smul, trOp_one]
      ring
    linarith
  calc ‖N‖ = ‖trOp N • (1 : ℝ⁴ →L[ℝ] ℝ⁴) - cofOp N‖ := by
        conv_lhs => rw [hNdef]
    _ ≤ ‖trOp N • (1 : ℝ⁴ →L[ℝ] ℝ⁴)‖ + ‖cofOp N‖ := norm_sub_le _ _
    _ = trOp N + ‖cofOp N‖ := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg htrnn, norm_one, mul_one]
    _ ≤ 4 * c' / 3 + 16 * max c c' := by
        linarith [norm_cofOp_le hN hc hc' hcq hcq']

/-- **Compactness of the ellipticity class**: a sequence of bases has a convergent subsequence. -/
theorem exists_subseq_base_tendsto {N : ℕ → ℝ⁴ →L[ℝ] ℝ⁴} (hN : ∀ m, (N m).IsSymmetric)
    {c c' : ℝ} (hc : 0 < c) (hc' : 0 ≤ c')
    (hcq : ∀ m u, c * ‖u‖ ^ 2 ≤ ⟪cofOp (N m) u, u⟫)
    (hcq' : ∀ m u, ⟪cofOp (N m) u, u⟫ ≤ c' * ‖u‖ ^ 2) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ Nlim : ℝ⁴ →L[ℝ] ℝ⁴,
      Tendsto (fun m => N (φ m)) atTop (𝓝 Nlim) := by
  have hmem : ∀ m : ℕ, N m ∈ closedBall (0 : ℝ⁴ →L[ℝ] ℝ⁴) (4 * c' / 3 + 16 * max c c') := by
    intro m
    rw [mem_closedBall, dist_zero_right]
    exact norm_base_le (hN m) hc hc' (hcq m) (hcq' m)
  obtain ⟨Nlim, -, φ, hφ, htend⟩ :=
    (isCompact_closedBall (0 : ℝ⁴ →L[ℝ] ℝ⁴) (4 * c' / 3 + 16 * max c c')).tendsto_subseq hmem
  exact ⟨φ, hφ, Nlim, htend⟩

end

end Submission
