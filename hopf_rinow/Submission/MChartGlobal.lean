import Submission.MChartMetric2
import Mathlib

/-!
# Smooth global extension of the coordinate metric

The local (per-chart) `C³` metric family `g` of `chart_metric_contDiffOn` is glued with the
Euclidean constant form `euclidForm` using a smooth bump function built from `ContDiffBump`
on the Euclidean structure of the finite-dimensional model space `E`.
-/

open scoped Manifold ContDiff Bundle Topology RealInnerProductSpace
open Set Bundle Metric

namespace Submission

open LeanEval.Geometry

noncomputable section

/-- The constant Euclidean bilinear form on the finite-dimensional space `E`, transported from the
standard inner product of `EuclideanSpace ℝ (Fin (finrank ℝ E))` by `toEuclidean`. -/
def euclidForm {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] :
    E →L[ℝ] (E →L[ℝ] ℝ) :=
  pull (innerSL ℝ (E := EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))) (toEuclidean (E := E))

@[simp]
lemma euclidForm_apply {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (u v : E) :
    euclidForm u v = inner ℝ (toEuclidean u) (toEuclidean v) := by
  simp [euclidForm, pull]
  rfl

/-- `euclidForm` is symmetric. -/
lemma euclidForm_symm {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (u v : E) : euclidForm u v = euclidForm v u := by
  rw [euclidForm_apply, euclidForm_apply]
  exact real_inner_comm (toEuclidean (E := E) v) (toEuclidean (E := E) u)

/-- `euclidForm` is positive definite. -/
lemma euclidForm_pos {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (v : E) (hv : v ≠ 0) : 0 < euclidForm v v := by
  have hne : (toEuclidean (E := E)) v ≠ 0 := by
    intro h
    apply hv
    exact (toEuclidean (E := E)).injective (by simpa using h)
  have h : 0 < inner ℝ (toEuclidean v) (toEuclidean v) := real_inner_self_pos.mpr hne
  simpa [euclidForm_apply] using h

/-- A strictly positive convex combination of positive numbers is positive. -/
lemma convex_pos {a b c d : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hsum : a + b = 1)
    (hc : 0 < c) (hd : 0 < d) : 0 < a * c + b * d := by
  by_cases hz : a = 0
  · rw [hz, zero_mul, zero_add]
    have : b = 1 := by linarith
    rw [this, one_mul]
    exact hd
  · have hapos : 0 < a := lt_of_le_of_ne ha (Ne.symm hz)
    have hbc : 0 ≤ b * d := mul_nonneg hb hd.le
    exact add_pos_of_pos_of_nonneg (mul_pos hapos hc) hbc

/-- Evaluation of a scalar-combination of bilinear forms on a pair of vectors. -/
lemma clm_eval_smul_add {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (A B : E →L[ℝ] (E →L[ℝ] ℝ)) (c d : ℝ) (u v : E) :
    ((c • A + d • B) u) v = c * (A u v) + d * (B u v) := by
  rfl

/-- A convex combination of symmetric bilinear forms is symmetric. -/
lemma convex_symm {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (A B : E →L[ℝ] (E →L[ℝ] ℝ)) (c : ℝ)
    (hA : ∀ u v : E, A u v = A v u) (hB : ∀ u v : E, B u v = B v u) :
    ∀ u v : E, ((c • A + (1 - c) • B) u) v = ((c • A + (1 - c) • B) v) u := by
  intro u v
  rw [clm_eval_smul_add, clm_eval_smul_add]
  rw [hA u v, hB u v]

/-- A convex combination of positive-definite bilinear forms is positive definite. -/
lemma convex_pos_smul {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (A B : E →L[ℝ] (E →L[ℝ] ℝ)) (c : ℝ) (hc0 : 0 ≤ c) (hc1 : c ≤ 1)
    (hA : ∀ v : E, v ≠ 0 → 0 < A v v) (hB : ∀ v : E, v ≠ 0 → 0 < B v v)
    {v : E} (hv : v ≠ 0) : 0 < ((c • A + (1 - c) • B) v) v := by
  rw [clm_eval_smul_add]
  have hc' : 0 ≤ 1 - c := by linarith
  have hsum : c + (1 - c) = 1 := by ring
  exact convex_pos hc0 hc' hsum (hA v hv) (hB v hv)

/-- The coordinate metric extends to a globally C³ symmetric positive metric family agreeing
with the fibre inner products on a neighbourhood of the chart centre. -/
theorem chart_metric_global {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H) [I.Boundaryless]
    (M : Type*) [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [Bundle.RiemannianBundle (fun x : M => TangentSpace I x)]
    [IsContMDiffRiemannianBundle I ∞ E (fun x : M => TangentSpace I x)]
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
    (p : M) :
    ∃ ρ > 0, ∃ ge : E → E →L[ℝ] E →L[ℝ] ℝ,
      ContDiff ℝ 3 ge ∧
      (∀ y u v : E, (ge y) u v = (ge y) v u) ∧
      (∀ y : E, ∀ v : E, v ≠ 0 → 0 < (ge y) v v) ∧
      (∀ y ∈ ball (extChartAt I p p) ρ, ∀ u v : E,
         (ge y) u v = (Bundle.RiemannianBundle.g (E := fun x : M => TangentSpace I x)).inner
                       ((extChartAt I p).symm y)
                       ((mfderiv[range I] (extChartAt I p).symm y) u)
                       ((mfderiv[range I] (extChartAt I p).symm y) v)) := by
  classical
  let φp : E := extChartAt I p p
  -- local C^3 metric on an open neighbourhood U' of φp, from the per-chart theorem
  rcases chart_metric_contDiffOn (I := I) (M := M) (p := p) with
    ⟨U', hφpU', hU'open, g, hgC, hgSymm, hgPos, hgAgree⟩
  -- U' is a neighbourhood of φp, hence it contains a Euclidean ball around φp
  have hUnhd : U' ∈ 𝓝 φp := hU'open.mem_nhds hφpU'
  rcases (Euclidean.nhds_basis_ball (x := φp)).mem_iff.mp hUnhd with ⟨ε₀, hε₀pos, hε₀ball⟩
  let rOut : ℝ := ε₀ / 2
  let rIn : ℝ := ε₀ / 4
  have hrOut_pos : 0 < rOut := by dsimp [rOut]; linarith
  have hrIn_pos : 0 < rIn := by dsimp [rIn]; linarith
  have hrIn_lt_rOut : rIn < rOut := by dsimp [rOut, rIn]; linarith
  have hrOut_lt_eps : rOut < ε₀ := by dsimp [rOut]; linarith
  -- smooth Euclidean bump with ψ = 1 on Euclidean.closedBall φp rIn, supported in
  -- Euclidean.ball φp rOut
  let b : ContDiffBump (toEuclidean (E := E) φp) := ⟨rIn, rOut, hrIn_pos, hrIn_lt_rOut⟩
  let ψ : E → ℝ := fun y => b (toEuclidean (E := E) y)
  have hψ_one : ∀ y : E, Euclidean.dist y φp ≤ rIn → ψ y = 1 := by
    intro y hy
    dsimp [ψ]
    have hy' : dist (toEuclidean (E := E) y) (toEuclidean (E := E) φp) ≤ rIn := by
      simpa [Euclidean.dist] using hy
    exact b.one_of_mem_closedBall (by simpa [Metric.mem_closedBall] using hy')
  have hψ_zero : ∀ y : E, rOut ≤ Euclidean.dist y φp → ψ y = 0 := by
    intro y hy
    dsimp [ψ]
    have hy' : rOut ≤ dist (toEuclidean (E := E) y) (toEuclidean (E := E) φp) := by
      simpa [Euclidean.dist] using hy
    exact b.zero_of_le_dist hy'
  have hψ_nonneg : ∀ y : E, 0 ≤ ψ y := by
    intro y
    dsimp [ψ]
    exact b.nonneg
  have hψ_le_one : ∀ y : E, ψ y ≤ 1 := by
    intro y
    dsimp [ψ]
    exact b.le_one
  have hψC : ContDiff ℝ 3 ψ := by
    dsimp [ψ]
    have hbC : ContDiff ℝ 3
        (fun z : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) => b z) := by
      exact b.contDiff
    exact hbC.comp (ContinuousLinearEquiv.contDiff (toEuclidean (E := E)))
  -- a standard ball inside the ψ = 1 region; this radius is the one we export
  have hclNhd : Euclidean.closedBall φp rIn ∈ 𝓝 φp := Euclidean.closedBall_mem_nhds hrIn_pos
  rcases (Metric.nhds_basis_ball (x := φp)).mem_iff.mp hclNhd with ⟨ρ, hρ_pos, hρ_sub⟩
  -- the global family
  let ge : E → E →L[ℝ] E →L[ℝ] ℝ := fun y => ψ y • g y + (1 - ψ y) • euclidForm
  -- ψ vanishes in the region {rOut ≤ Euclidean.dist · φp}, where ge = euclidForm
  have hge_euclid : ∀ y : E, rOut ≤ Euclidean.dist y φp → ∀ u v : E,
      (ge y) u v = euclidForm u v := by
    intro y hy u v
    have hψ0 : ψ y = 0 := hψ_zero y hy
    dsimp [ge]
    rw [hψ0, clm_eval_smul_add]
    norm_num
  -- ContDiffOn on U'
  have hψOn : ContDiffOn ℝ 3 ψ U' := (hψC.contDiffOn).mono (subset_univ U')
  have hEvalAll : ∀ u v : E, ∀ y : E,
      (ge y) u v = ψ y * (g y) u v + (1 - ψ y) * euclidForm u v := by
    intro u v y
    dsimp [ge]
    rw [clm_eval_smul_add]
  have hEvalOnU' : ∀ u v : E, ContDiffOn ℝ 3 (fun y : E => (ge y) u v) U' := by
    intro u v
    have hgEv : ContDiffOn ℝ 3 (fun y : E => (g y) u v) U' := by
      have h1 : ContDiffOn ℝ 3 (fun y : E => (g y) u) U' :=
        hgC.clm_apply (contDiffOn_const (c := u) (s := U'))
      exact h1.clm_apply (contDiffOn_const (c := v) (s := U'))
    have hComb : ContDiffOn ℝ 3
        (fun y : E => ψ y * (g y) u v + (1 - ψ y) * euclidForm u v) U' := by
      have hψMul : ContDiffOn ℝ 3 (fun y : E => ψ y * (g y) u v) U' :=
        ContDiffOn.mul hψOn hgEv
      have hsub : ContDiffOn ℝ 3 (fun y : E => 1 - ψ y) U' :=
        ContDiffOn.sub (contDiffOn_const (c := (1 : ℝ)) (s := U')) hψOn
      have hrest : ContDiffOn ℝ 3 (fun y : E => (1 - ψ y) * euclidForm u v) U' :=
        ContDiffOn.mul hsub (contDiffOn_const (c := euclidForm u v) (s := U'))
      exact ContDiffOn.add hψMul hrest
    have hEq : (fun y : E => (ge y) u v) =
        (fun y : E => ψ y * (g y) u v + (1 - ψ y) * euclidForm u v) := by
      funext y
      exact hEvalAll u v y
    rw [hEq]
    exact hComb
  have hgeOnU' : ContDiffOn ℝ 3 ge U' := by
    rw [contDiffOn_clm_apply]
    intro u
    rw [contDiffOn_clm_apply]
    intro v
    exact hEvalOnU' u v
  -- ContDiffOn on the open region {rOut < Euclidean.dist · φp}
  let O : Set E := {y | rOut < Euclidean.dist y φp}
  have hOopen : IsOpen O := by
    have hcont : Continuous (fun y : E => Euclidean.dist y φp) := by
      dsimp [Euclidean.dist]
      fun_prop
    have hEq : O = (fun y : E => Euclidean.dist y φp) ⁻¹' (Ioi rOut) := by
      ext y
      simp [O, Ioi]
    rw [hEq]
    exact hcont.isOpen_preimage (s := (Ioi rOut)) (isOpen_Ioi : IsOpen (Ioi rOut))
  have hEvalOnO : ∀ u v : E, ContDiffOn ℝ 3 (fun y : E => (ge y) u v) O := by
    intro u v
    refine ContDiffOn.congr (contDiffOn_const (c := euclidForm u v) (s := O)) ?_
    intro y hyO
    exact hge_euclid y (le_of_lt hyO) u v
  have hgeOnO : ContDiffOn ℝ 3 ge O := by
    rw [contDiffOn_clm_apply]
    intro u
    rw [contDiffOn_clm_apply]
    intro v
    exact hEvalOnO u v
  -- global smoothness
  have hgeC : ContDiff ℝ 3 ge := by
    rw [contDiff_iff_contDiffAt]
    intro y0
    by_cases hy0U : y0 ∈ U'
    · exact hgeOnU'.contDiffAt (hU'open.mem_nhds hy0U)
    · have hnot : y0 ∉ Euclidean.ball φp ε₀ := fun hb => hy0U (hε₀ball hb)
      have hdist : ε₀ ≤ Euclidean.dist y0 φp := le_of_not_gt hnot
      have hyO : y0 ∈ O := by
        dsimp [O, rOut]
        linarith
      exact hgeOnO.contDiffAt (hOopen.mem_nhds hyO)
  -- symmetry
  have hgeSymm : ∀ y u v : E, (ge y) u v = (ge y) v u := by
    intro y u v
    by_cases hyU : y ∈ U'
    · dsimp [ge]
      rw [clm_eval_smul_add, clm_eval_smul_add]
      rw [hgSymm y hyU u v, euclidForm_symm u v]
    · have hdist0 : rOut ≤ Euclidean.dist y φp := by
        have hnot : y ∉ Euclidean.ball φp ε₀ := fun hb => hyU (hε₀ball hb)
        have hbig : ε₀ ≤ Euclidean.dist y φp := le_of_not_gt hnot
        dsimp [rOut]
        linarith
      rw [hge_euclid y hdist0 u v, euclidForm_symm u v]
      rw [hge_euclid y hdist0 v u]
  -- positive definiteness
  have hgePos : ∀ y : E, ∀ v : E, v ≠ 0 → 0 < (ge y) v v := by
    intro y v hv
    by_cases hyU : y ∈ U'
    · dsimp [ge]
      rw [clm_eval_smul_add]
      have hc' : 0 ≤ 1 - ψ y := by linarith [hψ_le_one y]
      have hsum : ψ y + (1 - ψ y) = 1 := by ring
      exact convex_pos (hψ_nonneg y) hc' hsum (hgPos y hyU v hv) (euclidForm_pos v hv)
    · have hdist0 : rOut ≤ Euclidean.dist y φp := by
        have hnot : y ∉ Euclidean.ball φp ε₀ := fun hb => hyU (hε₀ball hb)
        have hbig : ε₀ ≤ Euclidean.dist y φp := le_of_not_gt hnot
        dsimp [rOut]
        linarith
      rw [hge_euclid y hdist0 v v]
      exact euclidForm_pos v hv
  -- agreement with the fibre inner products on ball φp ρ
  have hgeAgree : ∀ y ∈ ball (extChartAt I p p) ρ, ∀ u v : E,
         (ge y) u v = (Bundle.RiemannianBundle.g (E := fun x : M => TangentSpace I x)).inner
                       ((extChartAt I p).symm y)
                       ((mfderiv[range I] (extChartAt I p).symm y) u)
                       ((mfderiv[range I] (extChartAt I p).symm y) v) := by
    intro y hyρ u v
    have hycl : y ∈ Euclidean.closedBall φp rIn := hρ_sub hyρ
    have hdist : Euclidean.dist y φp ≤ rIn := by simpa [Euclidean.closedBall] using hycl
    have hyOut : y ∈ Euclidean.ball φp rOut := by
      simpa [Euclidean.ball] using lt_of_le_of_lt hdist hrIn_lt_rOut
    have hyEps : y ∈ Euclidean.ball φp ε₀ := by
      simpa [Euclidean.ball] using lt_trans (by simpa [Euclidean.ball] using hyOut) hrOut_lt_eps
    have hyU : y ∈ U' := hε₀ball hyEps
    have hψ1 : ψ y = 1 := hψ_one y hdist
    have hgey : (ge y) u v = (g y) u v := by
      dsimp [ge]
      rw [clm_eval_smul_add, hψ1]
      norm_num
    rw [hgey]
    simpa [φp] using hgAgree y hyU u v
  -- assemble the answer
  refine ⟨ρ, hρ_pos, ge, hgeC, hgeSymm, hgePos, ?_⟩
  simpa [φp] using hgeAgree

end

end Submission
