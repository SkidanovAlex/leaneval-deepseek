import Mathlib
import Submission.Work.Diff.STE.LieMet
import Submission.Work.Diff.GE.norms_defs
import Submission.Work.Diff.EXT.splice_defs
import Submission.Work.Diff.EXT.koszulPair_eq_sKz
import Submission.Work.Diff.EXT.contMDiffAt_matrix_inv
import Submission.Work.Diff.EXT.gRmC_eq_jRm
import Submission.Work.Diff.STE.deTurck.posDef_gmat
import Submission.ChartCurvCont
import Submission.Work.Diff.GE.scal_lapl_basic

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The manifold derivative of the inverse Gram matrix

This file proves `Work.Diff.STE.deTurck.gramInv_mvfderiv`, the bridge identifying the manifold
derivative of an entry of the inverse Gram matrix of the coordinate frame of the chart at `x₀`

`mvfderiv I (fun q ↦ (GramM (fun _ ↦ g) x₀ 0 q)⁻¹ a b) x (σ_i)`

with the *scalar* derivative `jdInv` of the inverse chart matrix
`∂_i (g^{-1})^{ab} = -∑_{pq} (g^{-1})^{ap} (g^{-1})^{bq} ∂_i g_{pq}`
of `Submission.Work.Diff.STE.DeTurck.pPhi_decomp` / the DeTurck bridge.

The auxiliary ingredients, all proved here, are

* `gramM_eq_chartMatFun`, `gramInv_eq_chartMatFun_inv`: the Gram matrix of the coordinate frame at
  `q` is the chart matrix `chartMatFun g x₀` at the chart coordinate of `q`;
* `chartMatFun_transpose`, `chartMatFun_inv_symm`: the chart matrix and its inverse are symmetric;
* `det_chartMatFun_ne_zero`: the chart matrix is positive definite, hence invertible;
* `contDiffAt_chartMatFun_inv`, `contDiffAt_chartMatFun_inv_entry`: the inverse chart matrix (and
  its entries) are smooth in the chart coordinate;
* `fderiv_pi_entry`: the entries of the Fréchet derivative of a matrix-valued function;
* `fderiv_matrix_inv_entry`: **the derivative of the inverse of a matrix family**,
  `d(A⁻¹) = -A⁻¹ dA A⁻¹`, in the entrywise form needed here.
-/

set_option linter.unusedSectionVars false
open scoped Manifold ContDiff Bundle Topology BigOperators
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter

namespace Work.Diff.STE.deTurck

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]
  [I.Boundaryless] [T2Space M]

/-- The Gram matrix of the coordinate frame at `q` is the chart matrix at the chart coordinate
of `q`. -/
lemma gramM_eq_chartMatFun (g : Submission.Diff.SMet I M) (x₀ : M) {q : M}
    (hq : q ∈ (extChartAt I x₀).source) :
    Work.Diff.GE.GramM (I := I) (fun _ : ℝ => g) x₀ 0 q
      = Matrix.of (Work.Diff.EXT.chartMatFun (I := I) g x₀ ((extChartAt I x₀) q)) := by
  have hleft : (extChartAt I x₀).symm ((extChartAt I x₀) q) = q := (extChartAt I x₀).left_inv hq
  ext i j
  simp only [Work.Diff.GE.GramM, Work.Diff.GE.mComp, Work.Diff.EXT.chartMatFun,
    Work.Diff.GE.cFrame_apply, Matrix.of_apply]
  rw [hleft]

/-- The inverse Gram matrix of the coordinate frame is the inverse of the chart matrix. -/
lemma gramInv_eq_chartMatFun_inv (g : Submission.Diff.SMet I M) (x₀ : M) {q : M}
    (hq : q ∈ (extChartAt I x₀).source) (a b : Fin (Module.finrank ℝ E)) :
    Work.Diff.GE.GramInv (I := I) (fun _ : ℝ => g) x₀ 0 q a b
      = (Matrix.of (Work.Diff.EXT.chartMatFun (I := I) g x₀ ((extChartAt I x₀) q)))⁻¹ a b := by
  rw [Work.Diff.GE.GramInv, gramM_eq_chartMatFun (I := I) g x₀ hq]

/-- The chart matrix is symmetric. -/
lemma chartMatFun_transpose (g : Submission.Diff.SMet I M) (x₀ : M) (z : E) :
    Matrix.transpose (Matrix.of (Work.Diff.EXT.chartMatFun (I := I) g x₀ z))
      = Matrix.of (Work.Diff.EXT.chartMatFun (I := I) g x₀ z) := by
  ext i j
  rw [Matrix.transpose_apply, Matrix.of_apply, Matrix.of_apply]
  exact g.symm ((extChartAt I x₀).symm z) _ _

/-- The inverse chart matrix is symmetric. -/
lemma chartMatFun_inv_symm (g : Submission.Diff.SMet I M) (x₀ : M) (z : E)
    (i j : Fin (Module.finrank ℝ E)) :
    (Matrix.of (Work.Diff.EXT.chartMatFun (I := I) g x₀ z))⁻¹ i j
      = (Matrix.of (Work.Diff.EXT.chartMatFun (I := I) g x₀ z))⁻¹ j i := by
  have h2 : Matrix.transpose ((Matrix.of (Work.Diff.EXT.chartMatFun (I := I) g x₀ z))⁻¹)
      = (Matrix.of (Work.Diff.EXT.chartMatFun (I := I) g x₀ z))⁻¹ := by
    rw [Matrix.transpose_nonsing_inv, chartMatFun_transpose (I := I) g x₀ z]
  calc (Matrix.of (Work.Diff.EXT.chartMatFun (I := I) g x₀ z))⁻¹ i j
      = (Matrix.transpose ((Matrix.of (Work.Diff.EXT.chartMatFun (I := I) g x₀ z))⁻¹)) j i :=
        (Matrix.transpose_apply _ j i).symm
    _ = (Matrix.of (Work.Diff.EXT.chartMatFun (I := I) g x₀ z))⁻¹ j i := by rw [h2]

/-- The chart matrix at a chart coordinate in the target is invertible. -/
lemma det_chartMatFun_ne_zero (g : Submission.Diff.SMet I M) (x₀ : M) {y : E}
    (hy : y ∈ (extChartAt I x₀).target) :
    (Matrix.of (Work.Diff.EXT.chartMatFun (I := I) g x₀ y)).det ≠ 0 := by
  have hp : (extChartAt I x₀).symm y ∈ (chartAt H x₀).source := by
    rw [← extChartAt_source (I := I) x₀]
    exact PartialEquiv.map_target (extChartAt I x₀) hy
  have hpd : (Matrix.of (Work.Diff.EXT.gmat (I := I) g x₀ ((extChartAt I x₀).symm y))).PosDef :=
    posDef_gmat (I := I) g x₀ hp
  have hpos : 0 < (Matrix.of (Work.Diff.EXT.chartMatFun (I := I) g x₀ y)).det := by
    have := hpd.det_pos
    rwa [show Work.Diff.EXT.gmat (I := I) g x₀ ((extChartAt I x₀).symm y)
        = Work.Diff.EXT.chartMatFun (I := I) g x₀ y from rfl] at this
  exact ne_of_gt hpos

/-- The inverse chart matrix, read as a family of matrices (i.e. into the pi-type of entries),
is smooth at every chart coordinate in the target. -/
lemma contDiffAt_chartMatFun_inv (g : Submission.Diff.SMet I M) (x₀ : M) {y : E}
    (hy : y ∈ (extChartAt I x₀).target) :
    ContDiffAt ℝ (⊤ : ℕ∞)
      (fun x : E => fun i j : Fin (Module.finrank ℝ E) =>
        (Matrix.of (Work.Diff.EXT.chartMatFun (I := I) g x₀ x))⁻¹ i j) y :=
  (Work.Diff.EXT.contDiffAt_matrix_inv_pi (n := Module.finrank ℝ E)
      (M := Work.Diff.EXT.chartMatFun (I := I) g x₀ y)
      (det_chartMatFun_ne_zero (I := I) g x₀ hy)).comp y
    (Work.Diff.EXT.kz_contDiffAt_chartMatFun (I := I) g x₀ hy)

/-- The entries of the inverse chart matrix are smooth at every chart coordinate in the target. -/
lemma contDiffAt_chartMatFun_inv_entry (g : Submission.Diff.SMet I M) (x₀ : M) {y : E}
    (hy : y ∈ (extChartAt I x₀).target) (a b : Fin (Module.finrank ℝ E)) :
    ContDiffAt ℝ (⊤ : ℕ∞)
      (fun x : E => (Matrix.of (Work.Diff.EXT.chartMatFun (I := I) g x₀ x))⁻¹ a b) y :=
  contDiffAt_pi.mp (contDiffAt_pi.mp (contDiffAt_chartMatFun_inv (I := I) g x₀ hy) a) b

lemma fderiv_pi_entry {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {n : ℕ} {N : E → Fin n → Fin n → ℝ} {y : E} (hN : DifferentiableAt ℝ N y)
    (i k : Fin n) (v : E) :
    fderiv ℝ (fun x : E => N x i k) y v = ((fderiv ℝ N y) v) i k := by
  have hd2 : DifferentiableAt ℝ (fun x : E => N x i) y := differentiableAt_pi.mp hN i
  have h1 := fderiv_apply (𝕜 := ℝ) hN i
  have h2 := fderiv_apply (𝕜 := ℝ) hd2 k
  simp only [h2, h1, ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply]

theorem fderiv_matrix_inv_entry
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {n : ℕ} {A : E → Fin n → Fin n → ℝ} {y : E} (a b : Fin n)
    (hA : DifferentiableAt ℝ A y)
    (hN : DifferentiableAt ℝ (fun x : E => fun i j => (Matrix.of (A x))⁻¹ i j) y)
    (hmul : ∀ᶠ x in nhds y, (Matrix.of (A x))⁻¹ * Matrix.of (A x) = 1)
    (hmul' : Matrix.of (A y) * (Matrix.of (A y))⁻¹ = 1) :
    ∀ v : E, fderiv ℝ (fun x : E => (Matrix.of (A x))⁻¹ a b) y v
      = -∑ p, ∑ q, (Matrix.of (A y))⁻¹ a p * ((fderiv ℝ A y) v) p q
          * (Matrix.of (A y))⁻¹ q b := by
  intro v
  have hdN2 : ∀ i k : Fin n, DifferentiableAt ℝ (fun x : E => (Matrix.of (A x))⁻¹ i k) y :=
    fun i k => differentiableAt_pi.mp (differentiableAt_pi.mp hN i) k
  have hdA2 : ∀ i k : Fin n, DifferentiableAt ℝ (fun x : E => A x i k) y :=
    fun i k => differentiableAt_pi.mp (differentiableAt_pi.mp hA i) k
  have hdNentry : ∀ i k : Fin n,
      fderiv ℝ (fun x : E => (Matrix.of (A x))⁻¹ i k) y v
        = ((fderiv ℝ (fun x : E => fun i j => (Matrix.of (A x))⁻¹ i j) y) v) i k :=
    fun i k => fderiv_pi_entry hN i k v
  have hdAentry : ∀ i k : Fin n,
      fderiv ℝ (fun x : E => A x i k) y v = ((fderiv ℝ A y) v) i k :=
    fun i k => fderiv_pi_entry hA i k v
  have hIsum : ∀ i j : Fin n,
      (fun x : E => ∑ k, (Matrix.of (A x))⁻¹ i k * A x k j)
        = (fun x : E => ((Matrix.of (A x))⁻¹ * Matrix.of (A x)) i j) := by
    intro i j
    funext x
    rw [Matrix.mul_apply]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [Matrix.of_apply]
  have hzero : ∀ i j : Fin n,
      fderiv ℝ (fun x : E => ∑ k, (Matrix.of (A x))⁻¹ i k * A x k j) y v = 0 := by
    intro i j
    have hconst : (fun x : E => ∑ k, (Matrix.of (A x))⁻¹ i k * A x k j) =ᶠ[nhds y]
        fun _ => (1 : Matrix (Fin n) (Fin n) ℝ) i j := by
      filter_upwards [hmul] with x hx
      rw [congrFun (hIsum i j) x, hx]
    rw [hconst.fderiv_eq]
    simp
  have hexp : ∀ i j : Fin n,
      fderiv ℝ (fun x : E => ∑ k, (Matrix.of (A x))⁻¹ i k * A x k j) y v
        = ∑ k, (((fderiv ℝ (fun x : E => fun i j => (Matrix.of (A x))⁻¹ i j)) y v) i k * A y k j
                + (Matrix.of (A y))⁻¹ i k * ((fderiv ℝ A y) v) k j) := by
    intro i j
    have hsum_fun : (fun x : E => ∑ k, (Matrix.of (A x))⁻¹ i k * A x k j)
        = (∑ k : Fin n, fun x : E => (Matrix.of (A x))⁻¹ i k * A x k j) := by
      funext x
      exact (Finset.sum_apply x Finset.univ
        (fun k : Fin n => fun x : E => (Matrix.of (A x))⁻¹ i k * A x k j)).symm
    rw [hsum_fun]
    rw [fderiv_sum (u := Finset.univ) (A := fun k : Fin n => fun x : E => (Matrix.of (A x))⁻¹ i k * A x k j)
      (fun k _ => (hdN2 i k).mul (hdA2 k j))]
    rw [sum_apply]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [fderiv_fun_mul (hdN2 i k) (hdA2 k j)]
    rw [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
        ContinuousLinearMap.smul_apply, smul_eq_mul, smul_eq_mul]
    rw [hdNentry i k, hdAentry k j]
    ring
  have hE : ∀ i j : Fin n,
      ∑ k, ((fderiv ℝ (fun x : E => fun i j => (Matrix.of (A x))⁻¹ i j)) y v) i k * A y k j
        = -∑ k, ((Matrix.of (A y))⁻¹ i k * ((fderiv ℝ A y) v) k j) := by
    intro i j
    have h0 : ∑ k, (((fderiv ℝ (fun x : E => fun i j => (Matrix.of (A x))⁻¹ i j)) y v) i k * A y k j
        + (Matrix.of (A y))⁻¹ i k * ((fderiv ℝ A y) v) k j) = 0 := by
      rw [← hexp i j, hzero i j]
    rw [Finset.sum_add_distrib] at h0
    linarith
  have hmat : Matrix.of ((fderiv ℝ (fun x : E => fun i j => (Matrix.of (A x))⁻¹ i j)) y v)
      * Matrix.of (A y)
      = -((Matrix.of (A y))⁻¹ * Matrix.of ((fderiv ℝ A y) v)) := by
    ext i j
    simp only [Matrix.mul_apply, Matrix.neg_apply, Matrix.of_apply]
    rw [hE i j]
  have hsolve : Matrix.of ((fderiv ℝ (fun x : E => fun i j => (Matrix.of (A x))⁻¹ i j)) y v)
      = -((Matrix.of (A y))⁻¹ * Matrix.of ((fderiv ℝ A y) v) * (Matrix.of (A y))⁻¹) := by
    calc Matrix.of ((fderiv ℝ (fun x : E => fun i j => (Matrix.of (A x))⁻¹ i j)) y v)
        = Matrix.of ((fderiv ℝ (fun x : E => fun i j => (Matrix.of (A x))⁻¹ i j)) y v) * 1 :=
          (Matrix.mul_one _).symm
      _ = Matrix.of ((fderiv ℝ (fun x : E => fun i j => (Matrix.of (A x))⁻¹ i j)) y v)
            * (Matrix.of (A y) * (Matrix.of (A y))⁻¹) := by rw [hmul']
      _ = (Matrix.of ((fderiv ℝ (fun x : E => fun i j => (Matrix.of (A x))⁻¹ i j)) y v)
            * Matrix.of (A y)) * (Matrix.of (A y))⁻¹ := (Matrix.mul_assoc _ _ _).symm
      _ = (-((Matrix.of (A y))⁻¹ * Matrix.of ((fderiv ℝ A y) v))) * (Matrix.of (A y))⁻¹ := by
            rw [hmat]
      _ = -((Matrix.of (A y))⁻¹ * Matrix.of ((fderiv ℝ A y) v) * (Matrix.of (A y))⁻¹) := by
            rw [Matrix.neg_mul]
  have hfinal : fderiv ℝ (fun x : E => (Matrix.of (A x))⁻¹ a b) y v
      = Matrix.of ((fderiv ℝ (fun x : E => fun i j => (Matrix.of (A x))⁻¹ i j)) y v) a b := by
    rw [fderiv_pi_entry hN a b v]
    rfl
  rw [hfinal, hsolve, Matrix.neg_apply]
  congr 1
  simp only [Matrix.mul_apply, Finset.sum_mul]
  rw [Finset.sum_comm]
  simp only [Matrix.of_apply]

/-- **The manifold derivative of the entries of the inverse Gram matrix** is the scalar expression
`jdInv` of the jet of the chart matrix: `∂_i (g^{-1})^{ab} = -∑_{pq} (g^{-1})^{ap}(g^{-1})^{bq}∂_i g_{pq}`. -/
theorem gramInv_mvfderiv
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]
    [I.Boundaryless] [T2Space M]
    (g : Submission.Diff.SMet I M) (x₀ : M) {y : E} (hy : y ∈ (extChartAt I x₀).target)
    (i a b : Fin (Module.finrank ℝ E)) :
    mvfderiv I (fun q : M => Work.Diff.GE.GramInv (fun _ : ℝ => g) (I := I) x₀ 0 q a b)
        ((extChartAt I x₀).symm y)
        (Work.Diff.GE.cFrame (I := I) x₀ i ((extChartAt I x₀).symm y))
      = Work.Diff.STE.DeTurck.jdInv (Work.Diff.EXT.chartMatFun (I := I) g x₀ y)
          (fderiv ℝ (Work.Diff.EXT.chartMatFun (I := I) g x₀) y) i a b := by
  set p : M := (extChartAt I x₀).symm y with hpdef
  have hps : p ∈ (extChartAt I x₀).source := by
    rw [hpdef]
    exact PartialEquiv.map_target (extChartAt I x₀) hy
  have hp : p ∈ (chartAt H x₀).source := by
    rw [← extChartAt_source (I := I) x₀]; exact hps
  have hpy : (extChartAt I x₀) p = y := by
    rw [hpdef]; exact PartialEquiv.right_inv (extChartAt I x₀) hy
  -- Step 1: the manifold function is the inverse chart matrix along the chart
  have hev : (fun q : M => Work.Diff.GE.GramInv (fun _ : ℝ => g) (I := I) x₀ 0 q a b)
      =ᶠ[𝓝 p] (fun q : M =>
        (Matrix.of (Work.Diff.EXT.chartMatFun (I := I) g x₀ ((extChartAt I x₀) q)))⁻¹ a b) := by
    filter_upwards [(chartAt H x₀).open_source.mem_nhds hp] with q hq
    have hqs : q ∈ (extChartAt I x₀).source := by rw [extChartAt_source]; exact hq
    exact gramInv_eq_chartMatFun_inv (I := I) g x₀ hqs a b
  rw [Work.Diff.EXT.mvfderiv_congr_of_eventuallyEq_real (I := I) hev]
  -- Step 2: the chart representative is mdifferentiable
  have hMd : MDifferentiableAt I 𝓘(ℝ,ℝ)
      (fun q : M =>
        (Matrix.of (Work.Diff.EXT.chartMatFun (I := I) g x₀ ((extChartAt I x₀) q)))⁻¹ a b) p := by
    have hF0 : ContMDiffAt 𝓘(ℝ,E) 𝓘(ℝ,ℝ) (⊤ : ℕ∞)
        (fun x : E => (Matrix.of (Work.Diff.EXT.chartMatFun (I := I) g x₀ x))⁻¹ a b) y :=
      contMDiffAt_iff_contDiffAt.mpr (contDiffAt_chartMatFun_inv_entry (I := I) g x₀ hy a b)
    have hχ : ContMDiffAt I 𝓘(ℝ,E) (⊤ : ℕ∞) (extChartAt I x₀) p :=
      contMDiffAt_extChartAt' (I := I) (n := (⊤ : ℕ∞)) hp
    have hF0' : ContMDiffAt 𝓘(ℝ,E) 𝓘(ℝ,ℝ) (⊤ : ℕ∞)
        (fun x : E => (Matrix.of (Work.Diff.EXT.chartMatFun (I := I) g x₀ x))⁻¹ a b)
        ((extChartAt I x₀) p) := by
      rw [hpy]; exact hF0
    exact (hF0'.comp p hχ).mdifferentiableAt (by simp)
  -- Step 3: pass to the chart derivative
  rw [Work.Diff.GE.cFrame_apply]
  rw [Work.Diff.T.mvfderiv_frameVector_real (I := I) x₀ hp hMd (Module.finBasis ℝ E i)]
  rw [hpy]
  have hev2 : (fun x : E => (Matrix.of (Work.Diff.EXT.chartMatFun (I := I) g x₀
        ((extChartAt I x₀) ((extChartAt I x₀).symm x))))⁻¹ a b)
      =ᶠ[𝓝 y] (fun x : E => (Matrix.of (Work.Diff.EXT.chartMatFun (I := I) g x₀ x))⁻¹ a b) := by
    filter_upwards [(isOpen_extChartAt_target (I := I) x₀).mem_nhds hy] with x hx
    rw [PartialEquiv.right_inv (extChartAt I x₀) hx]
  rw [hev2.fderiv_eq]
  -- Step 4: the derivative of the inverse of the chart matrix
  have hAc : DifferentiableAt ℝ (Work.Diff.EXT.chartMatFun (I := I) g x₀) y :=
    (Work.Diff.EXT.kz_contDiffAt_chartMatFun (I := I) g x₀ hy).differentiableAt (by simp)
  have hNc : DifferentiableAt ℝ
      (fun x : E => fun i j => (Matrix.of (Work.Diff.EXT.chartMatFun (I := I) g x₀ x))⁻¹ i j) y :=
    (contDiffAt_chartMatFun_inv (I := I) g x₀ hy).differentiableAt (by simp)
  have hmulc : ∀ᶠ x in 𝓝 y,
      (Matrix.of (Work.Diff.EXT.chartMatFun (I := I) g x₀ x))⁻¹
        * Matrix.of (Work.Diff.EXT.chartMatFun (I := I) g x₀ x) = 1 := by
    have hdetc : ContinuousAt (fun x : E =>
        (Matrix.of (Work.Diff.EXT.chartMatFun (I := I) g x₀ x)).det) y :=
      ((Work.Diff.EXT.contDiff_matrix_det_pi (n := Module.finrank ℝ E)).contDiffAt.comp y
        (Work.Diff.EXT.kz_contDiffAt_chartMatFun (I := I) g x₀ hy)).continuousAt
    filter_upwards [hdetc.eventually_ne (det_chartMatFun_ne_zero (I := I) g x₀ hy)] with x hx
    exact Matrix.nonsing_inv_mul _ (IsUnit.mk0 _ hx)
  have hmulc' : Matrix.of (Work.Diff.EXT.chartMatFun (I := I) g x₀ y)
      * (Matrix.of (Work.Diff.EXT.chartMatFun (I := I) g x₀ y))⁻¹ = 1 :=
    Matrix.mul_nonsing_inv _ (IsUnit.mk0 _ (det_chartMatFun_ne_zero (I := I) g x₀ hy))
  have hcore := fderiv_matrix_inv_entry (E := E) (n := Module.finrank ℝ E)
      (A := Work.Diff.EXT.chartMatFun (I := I) g x₀) (y := y) a b
      hAc hNc hmulc hmulc' (Module.finBasis ℝ E i)
  rw [hcore]
  -- Step 5: the index bookkeeping
  simp only [Work.Diff.STE.DeTurck.jdInv, Work.Diff.EXT.jInv]
  congr 1
  refine Finset.sum_congr rfl (fun p _ => Finset.sum_congr rfl (fun q _ => ?_))
  rw [chartMatFun_inv_symm (I := I) g x₀ y q b]
  ring

end Work.Diff.STE.deTurck
