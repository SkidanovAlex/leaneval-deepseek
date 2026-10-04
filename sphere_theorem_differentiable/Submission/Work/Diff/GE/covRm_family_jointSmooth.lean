import Mathlib
import Submission.Work.Diff.GE.rmP_family_jointSmooth
import Submission.Work.Diff.GE.metric_pairing_family_jointSmooth
import Submission.Work.Diff.GE.koszul_pairing_jointSmooth
import Submission.Work.Diff.GE.norms_defs
import Submission.Work.Diff.GE.gramInv_jointSmooth
import Submission.Work.Diff.EXT.eq_sum_frameVector_of_pairing
import Submission.Work.Diff.EXT.contMDiffAt_mvfderiv_along_field
import Submission.Work.Diff.GE.rmP_jointSmooth
import Submission.Work.Diff.T.lcOf_apply_inner_koszul
import Submission.Work.Diff.GE.covRm_sum_expand
import Submission.Work.Diff.GE.covRmChartExpr_eq

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Joint smoothness of `∇Rm` along a family of fields

The target `Work.Diff.GE.covRm_family_jointSmooth` states that for a jointly smooth family of
Riemannian metrics `G` on an open time set `J ∋ t` and jointly `C^∞` families of tangent fields
`V A B C D`, the function

`(s,y) ↦ covRm (G s) y (V s y) (A s y) (B s y) (C s y) (D s y)`

is jointly `C^∞` at `(t,x)`.

The proof expands the five arguments of `covRm` in the *chart frame* `σ_k = cFrame x k` of the
chart at `x` (`Work.Diff.EXT.eq_sum_frameVector_of_pairing`), with coefficients
`coefW G x W k p = ∑_j (GramInv (G p.1) x p.2) k j * ⟪W p.1 p.2, σ_j p.2⟫_{G p.1}`
that are jointly smooth by `Work.Diff.GE.gramInv_jointSmooth` and
`Work.Diff.GE.metric_pairing_family_jointSmooth`.  The `ℝ`-multilinearity of `covRm`
(`Work.Diff.GE.covRm_sum_expand`) turns the expression into the finite sum `covRmExpand5` of
products of these coefficients with the *frame components*
`covRmC5 G x p.1 p.2 m i j k l = covRm (G p.1) p.2 (σ_m p.2) (σ_i p.2) (σ_j p.2) (σ_k p.2) (σ_l p.2)`,
which are jointly smooth by the chain

* `chrCoord_jointSmooth`, `rmChartExpr_jointSmooth`, `covRmChartExpr_jointSmooth` — the chart
  expressions of the Christoffel symbols and of the curvature/its covariant derivative, built from
  `Work.Diff.GE.gramInv_jointSmooth`, `Work.Diff.GE.koszulPair_jointSmooth` and
  `Work.Diff.GE.mvfderiv_jointSmooth_frame`;
* `covRmC5_jointSmooth` — the identification of the frame components with the chart expression
  `Work.Diff.GE.covRmChartExpr_eq` on the chart.
-/

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology BigOperators
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter

namespace Work.Diff.GE

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1600000

section Kit

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M]
  [IsManifold I ((⊤ : ℕ∞) : WithTop ℕ∞) M]

/-- A time-dependent family of tangent fields is jointly `C^∞` at `(t, x)`. -/
abbrev FamSmooth (W : ℝ → Π y : M, TangentSpace I y) (t : ℝ) (x : M) : Prop :=
  ContMDiffAt ((modelWithCornersSelf ℝ ℝ).prod I) I.tangent ((⊤ : ℕ∞) : WithTop ℕ∞)
    (fun p : ℝ × M ↦ (⟨p.2, W p.1 p.2⟩ : TangentBundle I M)) (t, x)

/-- Joint `C^∞`-ness of a real-valued function of `(s, y)` at `(t, x)`. -/
abbrev FunSmooth (u : ℝ × M → ℝ) (t : ℝ) (x : M) : Prop :=
  ContMDiffAt ((modelWithCornersSelf ℝ ℝ).prod I) (modelWithCornersSelf ℝ ℝ)
    ((⊤ : ℕ∞) : WithTop ℕ∞) u (t, x)

/-- A section which is `C^∞` at `x`, viewed as a *constant* family, is jointly `C^∞` at `(t, x)`. -/
theorem covRmf5_const_family {Y : Π y : M, TangentSpace I y} {x : M}
    (hY : ContMDiffAt I I.tangent ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun y : M ↦ (⟨y, Y y⟩ : TangentBundle I M)) x) (t : ℝ) :
    FamSmooth (I := I) (fun _ => Y) t x :=
  hY.comp (t, x) contMDiffAt_snd

/-- The Gram matrix of the chart frame of the chart at `x`, in the `Matrix.of` form in which
`Work.Diff.EXT.eq_sum_frameVector_of_pairing` produces it. -/
noncomputable def covFramMat (G : ℝ → SMet I M) (x : M) (p : ℝ × M) :
    Matrix (Fin (Module.finrank ℝ E)) (Fin (Module.finrank ℝ E)) ℝ :=
  Matrix.of (fun i j => (G p.1).inner p.2
    (Submission.Geodesic.frameVector (I := I) x p.2 (Module.finBasis ℝ E i))
    (Submission.Geodesic.frameVector (I := I) x p.2 (Module.finBasis ℝ E j)))

/-- `covFramMat` is the Gram matrix `GramM` of the chart frame. -/
theorem covFramMat_eq_GramM (G : ℝ → SMet I M) (x : M) (p : ℝ × M) :
    covFramMat (I := I) G x p = GramM (I := I) G x p.1 p.2 := by
  ext i j
  simp only [covFramMat, Matrix.of_apply, GramM, mComp, cFrame_apply, cBasis]

/-- The coefficient of the tangent vector `W p.1 p.2` on the chart frame vector `cFrame x k p.2`
(the coordinates of `W p.1 p.2` in the chart frame of the chart at `x`). -/
noncomputable def coefW (G : ℝ → SMet I M) (x : M) (W : ℝ → Π y : M, TangentSpace I y)
    (k : Fin (Module.finrank ℝ E)) (p : ℝ × M) : ℝ :=
  Matrix.mulVec (covFramMat (I := I) G x p)⁻¹
    (fun j => (G p.1).inner p.2 (W p.1 p.2)
      (Submission.Geodesic.frameVector (I := I) x p.2 (Module.finBasis ℝ E j))) k

/-- **Coordinates from pairings.**  On the chart at `x`, any tangent vector `W p.1 p.2` is the sum of
the coefficients `coefW` times the chart frame vectors. -/
theorem eq_sum_coefW_cFrame (G : ℝ → SMet I M) (x : M) (W : ℝ → Π y : M, TangentSpace I y)
    {p : ℝ × M} (hp : p.2 ∈ (chartAt H x).source) :
    W p.1 p.2 = ∑ k, coefW (I := I) G x W k p • cFrame (I := I) x k p.2 := by
  have h := Work.Diff.EXT.eq_sum_frameVector_of_pairing (I := I) (g := G p.1) (x₀ := x) hp
    (W p.1 p.2)
  rw [h]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  simp only [coefW, covFramMat, cFrame_apply]

/-- The frame coefficient `coefW` written as the `GramInv`-contracted pairing sum. -/
theorem coefW_eq_sum (G : ℝ → SMet I M) (x : M) (W : ℝ → Π y : M, TangentSpace I y)
    (k : Fin (Module.finrank ℝ E)) (p : ℝ × M) :
    coefW (I := I) G x W k p = ∑ j, GramInv (I := I) G x p.1 p.2 k j *
      (G p.1).inner p.2 (W p.1 p.2) (cFrame (I := I) x j p.2) := by
  have hmat := covFramMat_eq_GramM (I := I) G x p
  show Matrix.mulVec (covFramMat (I := I) G x p)⁻¹
      (fun j => (G p.1).inner p.2 (W p.1 p.2)
        (Submission.Geodesic.frameVector (I := I) x p.2 (Module.finBasis ℝ E j))) k = _
  rw [hmat]
  simp only [GramInv, Matrix.mulVec_apply_eq_sum, cFrame_apply]

/-- The chart-frame coefficients of a jointly smooth family of fields are jointly smooth. -/
theorem coefW_jointSmooth {G : ℝ → SMet I M} {J : Set ℝ} (hJ : IsOpen J)
    (hG : JointSmooth G J) {t : ℝ} (ht : t ∈ J) {x : M}
    {W : ℝ → Π y : M, TangentSpace I y} (hW : FamSmooth (I := I) W t x)
    (k : Fin (Module.finrank ℝ E)) :
    FunSmooth (I := I) (fun p : ℝ × M ↦ coefW (I := I) G x W k p) t x := by
  letI : RiemannianBundle (fun y : M ↦ TangentSpace I y) := ⟨(G t).toRiemannianMetric⟩
  haveI : IsContMDiffRiemannianBundle I ((⊤ : ℕ∞) : WithTop ℕ∞) E
      (fun y : M ↦ TangentSpace I y) := inferInstance
  have hsum : FunSmooth (I := I)
      (fun p : ℝ × M ↦ ∑ j, GramInv (I := I) G x p.1 p.2 k j *
        (G p.1).inner p.2 (W p.1 p.2) (cFrame (I := I) x j p.2)) t x := by
    refine ContMDiffAt.sum (fun j _ => ?_)
    exact (gramInv_jointSmooth (I := I) hJ hG ht x k j).mul
      (metric_pairing_family_jointSmooth (I := I) (Z := fun _ => cFrame (I := I) x j) hJ hG ht hW
        (covRmf5_const_family (I := I)
          (Work.Diff.EXT.contMDiffAt_frameVector (I := I) x (cBasis (E := E) j)
            (mem_chart_source H x)) t))
  simpa only [coefW_eq_sum] using hsum

/-- Joint smoothness of the chart Christoffel symbols `chrCoord`. -/
theorem chrCoord_jointSmooth {G : ℝ → SMet I M} {J : Set ℝ} (hJ : IsOpen J)
    (hG : JointSmooth G J) {t : ℝ} (ht : t ∈ J) (x : M)
    (n a b : Fin (Module.finrank ℝ E)) :
    FunSmooth (I := I) (fun p : ℝ × M ↦ chrCoord (I := I) G x n a b p.1 p.2) t x := by
  letI : RiemannianBundle (fun y : M ↦ TangentSpace I y) := ⟨(G t).toRiemannianMetric⟩
  haveI : IsContMDiffRiemannianBundle I ((⊤ : ℕ∞) : WithTop ℕ∞) E
      (fun y : M ↦ TangentSpace I y) := inferInstance
  have hsum : FunSmooth (I := I)
      (fun p : ℝ × M ↦ ∑ q, GramInv (I := I) G x p.1 p.2 n q *
        koszulPair (I := I) G x a b q p.1 p.2) t x := by
    refine ContMDiffAt.sum (fun q _ => ?_)
    exact (gramInv_jointSmooth (I := I) hJ hG ht x n q).mul
      (koszulPair_jointSmooth (I := I) hJ hG ht x a b q)
  simpa only [chrCoord] using hsum

/-- Joint smoothness of `dOp x k u = ∂_k u` along the chart frame, for jointly smooth `u`. -/
theorem covRmf5_dOp_jointSmooth {G : ℝ → SMet I M} {J : Set ℝ} (hJ : IsOpen J)
    (hG : JointSmooth G J) {t : ℝ} (ht : t ∈ J) (x : M)
    {u : ℝ → M → ℝ} (hu : FunSmooth (I := I) (fun p : ℝ × M ↦ u p.1 p.2) t x)
    (k : Fin (Module.finrank ℝ E)) :
    FunSmooth (I := I) (fun p : ℝ × M ↦ dOp (I := I) x k u p.1 p.2) t x := by
  letI : RiemannianBundle (fun y : M ↦ TangentSpace I y) := ⟨(G t).toRiemannianMetric⟩
  haveI : IsContMDiffRiemannianBundle I ((⊤ : ℕ∞) : WithTop ℕ∞) E
      (fun y : M ↦ TangentSpace I y) := inferInstance
  have h := mvfderiv_jointSmooth_frame (I := I) (F := ℝ)
    (Φ := fun p : ℝ × M ↦ u p.1 p.2) hu x k (mem_chart_source H x)
  simpa only [dOp] using h

/-- Joint smoothness of the chart Koszul pairings along the frame vectors. -/
theorem covRmf5_dOp_koszulPair {G : ℝ → SMet I M} {J : Set ℝ} (hJ : IsOpen J)
    (hG : JointSmooth G J) {t : ℝ} (ht : t ∈ J) (x : M)
    (i j l k : Fin (Module.finrank ℝ E)) :
    FunSmooth (I := I)
      (fun p : ℝ × M ↦ dOp (I := I) x i (koszulPair (I := I) G x j l k) p.1 p.2) t x := by
  letI : RiemannianBundle (fun y : M ↦ TangentSpace I y) := ⟨(G t).toRiemannianMetric⟩
  haveI : IsContMDiffRiemannianBundle I ((⊤ : ℕ∞) : WithTop ℕ∞) E
      (fun y : M ↦ TangentSpace I y) := inferInstance
  have hΦ : Work.Diff.EXT.JointSmoothAt I M
      (fun p : ℝ × M ↦ koszulPair (I := I) G x j l k p.1 p.2) t x :=
    koszulPair_jointSmooth (I := I) hJ hG ht x j l k
  have h := mvfderiv_jointSmooth_frame (I := I) (F := ℝ)
    (Φ := fun p : ℝ × M ↦ koszulPair (I := I) G x j l k p.1 p.2) hΦ x i
    (mem_chart_source H x)
  simpa only [dOp] using h

/-- Joint smoothness of the chart curvature components `rmChartExpr`. -/
theorem rmChartExpr_jointSmooth {G : ℝ → SMet I M} {J : Set ℝ} (hJ : IsOpen J)
    (hG : JointSmooth G J) {t : ℝ} (ht : t ∈ J) (x : M)
    (i j k l : Fin (Module.finrank ℝ E)) :
    FunSmooth (I := I) (fun p : ℝ × M ↦ rmChartExpr (I := I) G x i j k l p.1 p.2) t x := by
  letI : RiemannianBundle (fun y : M ↦ TangentSpace I y) := ⟨(G t).toRiemannianMetric⟩
  haveI : IsContMDiffRiemannianBundle I ((⊤ : ℕ∞) : WithTop ℕ∞) E
      (fun y : M ↦ TangentSpace I y) := inferInstance
  have h1 : FunSmooth (I := I)
      (fun p : ℝ × M ↦ dOp (I := I) x i (koszulPair (I := I) G x j l k) p.1 p.2) t x :=
    covRmf5_dOp_koszulPair (I := I) hJ hG ht x i j l k
  have h2 : FunSmooth (I := I)
      (fun p : ℝ × M ↦ ∑ m, ∑ n, GramInv (I := I) G x p.1 p.2 m n *
        koszulPair (I := I) G x j l m p.1 p.2 *
        koszulPair (I := I) G x i k n p.1 p.2) t x := by
    refine ContMDiffAt.sum (fun m _ => ?_)
    refine ContMDiffAt.sum (fun n _ => ?_)
    exact ((gramInv_jointSmooth (I := I) hJ hG ht x m n).mul
      (koszulPair_jointSmooth (I := I) hJ hG ht x j l m)).mul
      (koszulPair_jointSmooth (I := I) hJ hG ht x i k n)
  have h3 : FunSmooth (I := I)
      (fun p : ℝ × M ↦ dOp (I := I) x j (koszulPair (I := I) G x i l k) p.1 p.2) t x :=
    covRmf5_dOp_koszulPair (I := I) hJ hG ht x j i l k
  have h4 : FunSmooth (I := I)
      (fun p : ℝ × M ↦ ∑ m, ∑ n, GramInv (I := I) G x p.1 p.2 m n *
        koszulPair (I := I) G x i l m p.1 p.2 *
        koszulPair (I := I) G x j k n p.1 p.2) t x := by
    refine ContMDiffAt.sum (fun m _ => ?_)
    refine ContMDiffAt.sum (fun n _ => ?_)
    exact ((gramInv_jointSmooth (I := I) hJ hG ht x m n).mul
      (koszulPair_jointSmooth (I := I) hJ hG ht x i l m)).mul
      (koszulPair_jointSmooth (I := I) hJ hG ht x j k n)
  have hmain := ((h1.sub h2).sub h3).add h4
  refine hmain.congr_of_eventuallyEq ?_
  filter_upwards with p
  simp only [rmChartExpr, Pi.add_apply, Pi.sub_apply]

/-- Joint smoothness of the explicit chart expression `covRmChartExpr` of the `∇Rm` components. -/
theorem covRmChartExpr_jointSmooth {G : ℝ → SMet I M} {J : Set ℝ} (hJ : IsOpen J)
    (hG : JointSmooth G J) {t : ℝ} (ht : t ∈ J) (x : M)
    (m i j k l : Fin (Module.finrank ℝ E)) :
    FunSmooth (I := I) (fun p : ℝ × M ↦ covRmChartExpr (I := I) G x m i j k l p.1 p.2) t x := by
  letI : RiemannianBundle (fun y : M ↦ TangentSpace I y) := ⟨(G t).toRiemannianMetric⟩
  haveI : IsContMDiffRiemannianBundle I ((⊤ : ℕ∞) : WithTop ℕ∞) E
      (fun y : M ↦ TangentSpace I y) := inferInstance
  have hrm : FunSmooth (I := I)
      (fun p : ℝ × M ↦ rmChartExpr (I := I) G x i j k l p.1 p.2) t x :=
    rmChartExpr_jointSmooth (I := I) hJ hG ht x i j k l
  have h1 : FunSmooth (I := I)
      (fun p : ℝ × M ↦ dOp (I := I) x m (rmChartExpr (I := I) G x i j k l) p.1 p.2) t x :=
    covRmf5_dOp_jointSmooth (I := I) hJ hG ht x hrm m
  have h2 : FunSmooth (I := I)
      (fun p : ℝ × M ↦ ∑ n, chrCoord (I := I) G x n m i p.1 p.2 *
        rmChartExpr (I := I) G x n j k l p.1 p.2) t x := by
    refine ContMDiffAt.sum (fun n _ => ?_)
    exact (chrCoord_jointSmooth (I := I) hJ hG ht x n m i).mul
      (rmChartExpr_jointSmooth (I := I) hJ hG ht x n j k l)
  have h3 : FunSmooth (I := I)
      (fun p : ℝ × M ↦ ∑ n, chrCoord (I := I) G x n m j p.1 p.2 *
        rmChartExpr (I := I) G x i n k l p.1 p.2) t x := by
    refine ContMDiffAt.sum (fun n _ => ?_)
    exact (chrCoord_jointSmooth (I := I) hJ hG ht x n m j).mul
      (rmChartExpr_jointSmooth (I := I) hJ hG ht x i n k l)
  have h4 : FunSmooth (I := I)
      (fun p : ℝ × M ↦ ∑ n, chrCoord (I := I) G x n m k p.1 p.2 *
        rmChartExpr (I := I) G x i j n l p.1 p.2) t x := by
    refine ContMDiffAt.sum (fun n _ => ?_)
    exact (chrCoord_jointSmooth (I := I) hJ hG ht x n m k).mul
      (rmChartExpr_jointSmooth (I := I) hJ hG ht x i j n l)
  have h5 : FunSmooth (I := I)
      (fun p : ℝ × M ↦ ∑ n, chrCoord (I := I) G x n m l p.1 p.2 *
        rmChartExpr (I := I) G x i j k n p.1 p.2) t x := by
    refine ContMDiffAt.sum (fun n _ => ?_)
    exact (chrCoord_jointSmooth (I := I) hJ hG ht x n m l).mul
      (rmChartExpr_jointSmooth (I := I) hJ hG ht x i j k n)
  have hmain := (((h1.sub h2).sub h3).sub h4).sub h5
  simpa only [covRmChartExpr] using hmain

/-- Joint smoothness of the chart-frame components of `∇Rm`. -/
theorem covRmC5_jointSmooth {G : ℝ → SMet I M} {J : Set ℝ} (hLC : LCSmooth I M) (hJ : IsOpen J)
    (hG : JointSmooth G J) {t : ℝ} (ht : t ∈ J) (x : M)
    (m i j k l : Fin (Module.finrank ℝ E)) :
    FunSmooth (I := I) (fun p : ℝ × M ↦ covRmC5 (I := I) G x p.1 p.2 m i j k l) t x := by
  letI : RiemannianBundle (fun y : M ↦ TangentSpace I y) := ⟨(G t).toRiemannianMetric⟩
  haveI : IsContMDiffRiemannianBundle I ((⊤ : ℕ∞) : WithTop ℕ∞) E
      (fun y : M ↦ TangentSpace I y) := inferInstance
  refine (covRmChartExpr_jointSmooth (I := I) hJ hG ht x m i j k l).congr_of_eventuallyEq ?_
  rw [nhds_prod_eq]
  filter_upwards [Filter.prod_mem_prod Filter.univ_mem
    ((chartAt H x).open_source.mem_nhds (mem_chart_source H x))] with p hp
  exact covRmChartExpr_eq (I := I) hLC G x p.1 hp.2 m i j k l

/-- The five-fold multilinear expansion of `covRm` in the chart frame, with the frame components
`covRmC5` kept together. -/
noncomputable def covRmExpand5 (G : ℝ → SMet I M) (x : M)
    (V A B C D : ℝ → Π y : M, TangentSpace I y) (p : ℝ × M) : ℝ :=
  ∑ m, ∑ i, ∑ j, ∑ k, ∑ l,
    coefW (I := I) G x V m p * coefW (I := I) G x A i p * coefW (I := I) G x B j p *
      coefW (I := I) G x C k p * coefW (I := I) G x D l p *
      covRmC5 (I := I) G x p.1 p.2 m i j k l

/-- `covRm` on five finite linear combinations, expanded with explicit coefficient functions. -/
theorem covRmf5_expand (hLC : LCSmooth I M) (g : SMet I M) (x : M)
    (a : Fin (Module.finrank ℝ E) → TangentSpace I x)
    (c0 c1 c2 c3 c4 : Fin (Module.finrank ℝ E) → ℝ) :
    covRm g x (∑ m, c0 m • a m) (∑ i, c1 i • a i) (∑ j, c2 j • a j) (∑ k, c3 k • a k)
        (∑ l, c4 l • a l)
      = ∑ m, ∑ i, ∑ j, ∑ k, ∑ l,
          c0 m * c1 i * c2 j * c3 k * c4 l *
            covRm g x (a m) (a i) (a j) (a k) (a l) := by
  let c : Fin 5 → Fin (Module.finrank ℝ E) → ℝ :=
    Fin.cases c0 (Fin.cases c1 (Fin.cases c2 (Fin.cases c3 (Fin.cases c4 (fun _ => c4)))))
  have hc0 : c 0 = c0 := rfl
  have hc1 : c 1 = c1 := rfl
  have hc2 : c 2 = c2 := rfl
  have hc3 : c 3 = c3 := rfl
  have hc4 : c 4 = c4 := rfl
  have h := kato_covRm_multilinear (I := I) hLC g x a c
  rw [hc0, hc1, hc2, hc3, hc4] at h
  exact h

/-- **The expansion of `covRm` on a family of fields** in the chart frame at `x`. -/
theorem covRm_eq_covRmExpand5 (hLC : LCSmooth I M) (G : ℝ → SMet I M) (x : M)
    (V A B C D : ℝ → Π y : M, TangentSpace I y) {p : ℝ × M}
    (hp : p.2 ∈ (chartAt H x).source) :
    covRm (G p.1) p.2 (V p.1 p.2) (A p.1 p.2) (B p.1 p.2) (C p.1 p.2) (D p.1 p.2)
      = covRmExpand5 (I := I) G x V A B C D p := by
  conv_lhs => rw [eq_sum_coefW_cFrame (I := I) G x V hp]
  conv_lhs => rw [eq_sum_coefW_cFrame (I := I) G x A hp]
  conv_lhs => rw [eq_sum_coefW_cFrame (I := I) G x B hp]
  conv_lhs => rw [eq_sum_coefW_cFrame (I := I) G x C hp]
  conv_lhs => rw [eq_sum_coefW_cFrame (I := I) G x D hp]
  rw [covRmf5_expand (I := I) hLC (G p.1) p.2 (fun k => cFrame (I := I) x k p.2)
    (fun k => coefW (I := I) G x V k p) (fun k => coefW (I := I) G x A k p)
    (fun k => coefW (I := I) G x B k p) (fun k => coefW (I := I) G x C k p)
    (fun k => coefW (I := I) G x D k p)]
  simp only [covRmExpand5, covRmC5]

/-- Joint smoothness of the expanded expression `covRmExpand5`. -/
theorem covRmExpand5_jointSmooth {G : ℝ → SMet I M} {J : Set ℝ} (hLC : LCSmooth I M)
    (hJ : IsOpen J) (hG : JointSmooth G J) {t : ℝ} (ht : t ∈ J) {x : M}
    {V A B C D : ℝ → Π y : M, TangentSpace I y}
    (hV : FamSmooth (I := I) V t x) (hA : FamSmooth (I := I) A t x)
    (hB : FamSmooth (I := I) B t x) (hC : FamSmooth (I := I) C t x)
    (hD : FamSmooth (I := I) D t x) :
    FunSmooth (I := I) (fun p : ℝ × M ↦ covRmExpand5 (I := I) G x V A B C D p) t x := by
  have hcV : ∀ k, FunSmooth (I := I) (fun p : ℝ × M ↦ coefW (I := I) G x V k p) t x :=
    fun k => coefW_jointSmooth (I := I) hJ hG ht hV k
  have hcA : ∀ k, FunSmooth (I := I) (fun p : ℝ × M ↦ coefW (I := I) G x A k p) t x :=
    fun k => coefW_jointSmooth (I := I) hJ hG ht hA k
  have hcB : ∀ k, FunSmooth (I := I) (fun p : ℝ × M ↦ coefW (I := I) G x B k p) t x :=
    fun k => coefW_jointSmooth (I := I) hJ hG ht hB k
  have hcC : ∀ k, FunSmooth (I := I) (fun p : ℝ × M ↦ coefW (I := I) G x C k p) t x :=
    fun k => coefW_jointSmooth (I := I) hJ hG ht hC k
  have hcD : ∀ k, FunSmooth (I := I) (fun p : ℝ × M ↦ coefW (I := I) G x D k p) t x :=
    fun k => coefW_jointSmooth (I := I) hJ hG ht hD k
  have hc5 : ∀ m i j k l, FunSmooth (I := I)
      (fun p : ℝ × M ↦ covRmC5 (I := I) G x p.1 p.2 m i j k l) t x :=
    fun m i j k l => covRmC5_jointSmooth (I := I) hLC hJ hG ht x m i j k l
  refine ContMDiffAt.sum (fun m _ => ?_)
  refine ContMDiffAt.sum (fun i _ => ?_)
  refine ContMDiffAt.sum (fun j _ => ?_)
  refine ContMDiffAt.sum (fun k _ => ?_)
  refine ContMDiffAt.sum (fun l _ => ?_)
  exact (((((hcV m).mul (hcA i)).mul (hcB j)).mul (hcC k)).mul (hcD l)).mul
    (hc5 m i j k l)

end Kit

/-- **Joint smoothness of the `(0,5)`-tensor `∇Rm` along a family of fields.**  For a metric family
`G` jointly smooth on an open `J ∋ t` and jointly `C^∞` families of tangent fields `V A B C D`, the
map `(s,y) ↦ covRm (G s) y (V s y) (A s y) (B s y) (C s y) (D s y)` is jointly `C^∞` at `(t,x)`.

Proof route: unfold `covRm g y V A B C D = mvfderiv I (fun y' ↦ rmP g y' (A y') (B y') (C y') (D y'))
y (V y) − rmP g y (lcOf g A y (V y)) (B y) (C y) (D y) − (three more Leibniz corrections)`.  Each of
the five terms is jointly smooth: the `mvfderiv` term by expanding the direction `V p.1 p.2` in the
coordinate frame of the chart at `x` (`Work.Diff.EXT.eq_sum_frameVector_of_pairing`; coefficients
jointly smooth by `Work.Diff.GE.metric_pairing_family_jointSmooth` and
`Work.Diff.GE.gramInv_jointSmooth`), using `ℝ`-linearity of `mvfderiv` in its direction and
`Work.Diff.EXT.contMDiffAt_mvfderiv_along_field` with the fixed coordinate-frame fields, and
`Work.Diff.GE.rmP_family_jointSmooth` for the inner function; the four correction terms by writing
`lcOf (G s) A y (V y) = ∑ⱼ (∑ᵢ GramInv · (G s).inner y (lcOf (G s) A y (V y)) (σᵢ y)) σⱼ y` (the
pairing is jointly smooth by `Work.Diff.GE.koszul_pairing_jointSmooth`, or by
`Work.Diff.T.lcOf_apply_inner_koszul` applied at each `s`), then using the `ℝ`-multilinearity of
`rmP` (`Work.Diff.GE.rmP_add_*`, `Work.Diff.GE.rmP_smul_*`) and
`Work.Diff.GE.rmP_family_jointSmooth` once more. -/
theorem covRm_family_jointSmooth
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M]
    [IsManifold I ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    (hLC : Submission.Diff.LCSmooth I M)
    {G : ℝ → Submission.Diff.SMet I M} {J : Set ℝ} (hJ : IsOpen J)
    (hG : Submission.Diff.JointSmooth G J) {t : ℝ} (ht : t ∈ J) {x : M}
    {V A B C D : ℝ → Π y : M, TangentSpace I y}
    (hV : ContMDiffAt ((modelWithCornersSelf ℝ ℝ).prod I) I.tangent ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun p : ℝ × M ↦ (⟨p.2, V p.1 p.2⟩ : TangentBundle I M)) (t, x))
    (hA : ContMDiffAt ((modelWithCornersSelf ℝ ℝ).prod I) I.tangent ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun p : ℝ × M ↦ (⟨p.2, A p.1 p.2⟩ : TangentBundle I M)) (t, x))
    (hB : ContMDiffAt ((modelWithCornersSelf ℝ ℝ).prod I) I.tangent ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun p : ℝ × M ↦ (⟨p.2, B p.1 p.2⟩ : TangentBundle I M)) (t, x))
    (hC : ContMDiffAt ((modelWithCornersSelf ℝ ℝ).prod I) I.tangent ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun p : ℝ × M ↦ (⟨p.2, C p.1 p.2⟩ : TangentBundle I M)) (t, x))
    (hD : ContMDiffAt ((modelWithCornersSelf ℝ ℝ).prod I) I.tangent ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun p : ℝ × M ↦ (⟨p.2, D p.1 p.2⟩ : TangentBundle I M)) (t, x)) :
    ContMDiffAt ((modelWithCornersSelf ℝ ℝ).prod I) (modelWithCornersSelf ℝ ℝ)
      ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun p : ℝ × M ↦ Submission.Diff.covRm (G p.1) p.2 (V p.1 p.2) (A p.1 p.2)
        (B p.1 p.2) (C p.1 p.2) (D p.1 p.2)) (t, x) := by
  refine (covRmExpand5_jointSmooth (I := I) hLC hJ hG ht hV hA hB hC hD).congr_of_eventuallyEq ?_
  rw [nhds_prod_eq]
  filter_upwards [Filter.prod_mem_prod Filter.univ_mem
    ((chartAt H x).open_source.mem_nhds (mem_chart_source H x))] with p hp
  exact covRm_eq_covRmExpand5 (I := I) hLC G x V A B C D hp.2

end Work.Diff.GE
