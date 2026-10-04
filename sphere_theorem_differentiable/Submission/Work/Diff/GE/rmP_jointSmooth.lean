import Mathlib
import Submission.Work.Diff.GE.rmPDeps
import Submission.Work.Diff.GE.gramInv_jointSmooth
import Submission.Work.Diff.GE.chrB_eq_sum_gramInv
import Submission.Work.Diff.GE.rmP_eq_sum_rmC4

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology
open Bundle ContDiff Set VectorField CovariantDerivative Metric

/-!
# Joint smoothness of the frozen curvature form `rmP`

For a jointly smooth family `t ↦ G t` of Riemannian metrics on `M` and smooth fields
`A B C D`, the pointwise curvature form

`(t, x) ↦ rmP (G t) x (A x) (B x) (C x) (D x) = (G t).inner x (R(A,B)D(x)) (C x)`

is jointly `C^∞`.  This is the smoothness statement on which the contraction lemmas of Hamilton's
gradient estimate (`rmNormSq`, `scalAt`, ... as joint functions of `(t, x)`) rest.

Route.  All objects are computed in the coordinate frame `σ_i y = cFrame x₀ i y = frameVector x₀ y
(cBasis i)` of the chart at `x₀ = x`:

* `rmP` is `C^∞(M)`-multilinear in its four vector slots (`Work.Diff.GE.rmVec_sum_*`,
  `rmVec_smul_*`), so with `A y = Σ_i α^i(y) • σ_i y` (the coefficients `α^i` are the coordinates
  `coordFun x₀ A` of `A`, smooth by `Submission.ChartCurv.contMDiffAt_coordFun`) we get
  `rmP (G t) y (A y) (B y) (C y) (D y) = Σ_{i j k l} α^i β^j γ^k δ^l · rmC4 G x₀ t y i j k l`
  (the delegated expansion `rmP_eq_sum_rmC4`);
* `rmC4 G x₀ t y i j k l` are the curvature components in the coordinate frame; they equal the
  chart expression `cRm (G t) x₀ y (cBasis i) (cBasis j) (cBasis k) (cBasis l)` of
  `Submission.Work.Diff.GE.chartcalc` (`rmC4_eq_cRm`, via `curvVec_eq_chart`), whose joint
  smoothness is then reduced to that of the Christoffel symbol `chrB` and of its chart derivative
  `dB`;
* `chrB` is recovered from the lowered Christoffel pairings `koszulPair` and the inverse Gram
  matrix (`chrB_eq_sum_gramInv`), and `koszulPair` is a first coordinate derivative of the metric
  coefficients `mComp`, so everything is a finite sum of products of jointly smooth functions;
* the spatial derivative `mvfderiv` of a jointly smooth family along the coordinate frame is
  jointly smooth (`mvfderiv_jointSmooth_frame`, from
  `Work.Diff.EXT.contMDiffAt_mvfderiv_along_field` and the bump-extension
  `Submission.ChartConnection.exists_contMDiff_section_eventuallyEq_frameSection`).

The Riemannian bundle instance used inside the helpers is an arbitrary smooth metric of the family;
none of the statements involved depends on it (they only mention `(G t).inner` and `cov`).
-/

namespace Work.Diff.GE

/-! ## The bridge: the frozen coordinate-frame components are the chart curvature -/

section Helpers
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]
  [T2Space M] [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I (⊤ : ℕ∞) E (fun x : M ↦ TangentSpace I x)]

theorem rmC4_eq_cRm (hLC : LCSmooth I M) (G : ℝ → SMet I M) (x₀ : M) (t : ℝ) {y : M}
    (hy : y ∈ (chartAt H x₀).source) (i j k l : Fin (Module.finrank ℝ E)) :
    rmC4 (I := I) G x₀ t y i j k l
      = cRm (G t) x₀ y (cBasis (E := E) i) (cBasis (E := E) j)
          (cBasis (E := E) k) (cBasis (E := E) l) := by
  haveI : ContMDiffCovariantDerivative (lcOf (G t)) ∞ := (hLC (G t)).1.some
  have htor : (lcOf (G t)).torsion = 0 := (hLC (G t)).2.1
  show (G t).inner y (rmVec (lcOf (G t)) y (Submission.Geodesic.frameVector x₀ y (cBasis i))
        (Submission.Geodesic.frameVector x₀ y (cBasis j))
        (Submission.Geodesic.frameVector x₀ y (cBasis l)))
      (Submission.Geodesic.frameVector x₀ y (cBasis k))
    = cGram (G t) x₀ y (cCurv (G t) x₀ y (cBasis i) (cBasis j) (cBasis l)) (cBasis k)
  rw [rmVec_eq_curvVec (lcOf (G t)) (inferInstance) y,
    Submission.ChartCurv.curvVec_eq_chart (cov := lcOf (G t)) htor x₀ y (cBasis l) (cBasis j)
      (cBasis i) hy]
  rfl

/-! ## Joint smoothness of the metric coefficients -/

theorem mComp_jointSmooth {G : ℝ → SMet I M} {J : Set ℝ} (hJ : IsOpen J)
    (hG : JointSmooth G J) {t₀ : ℝ} (ht₀ : t₀ ∈ J) (x₀ : M)
    (i j : Fin (Module.finrank ℝ E)) :
    Work.Diff.EXT.JointSmoothAt I M
      (fun p : ℝ × M ↦ mComp (I := I) G x₀ i j p.1 p.2) t₀ x₀ :=
  Work.Diff.EXT.contMDiffAt_metric_pairing (I := I) (M := M) hJ hG ht₀
    (by
      simp only [Work.Diff.EXT.SmoothFieldAt, cFrame, Submission.Geodesic.frameSection_eq_frameVector]
      exact Work.Diff.EXT.contMDiffAt_frameVector (I := I) x₀ (cBasis (E := E) i)
        (mem_chart_source H x₀))
    (by
      simp only [Work.Diff.EXT.SmoothFieldAt, cFrame, Submission.Geodesic.frameSection_eq_frameVector]
      exact Work.Diff.EXT.contMDiffAt_frameVector (I := I) x₀ (cBasis (E := E) j)
        (mem_chart_source H x₀))


/-! ## The joint smoothness of the spatial derivative along the coordinate frame -/

theorem mvfderiv_jointSmooth_frame {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {Φ : ℝ × M → F} {t₀ : ℝ} {x : M} (hΦ : Work.Diff.EXT.JointSmoothAt I M Φ t₀ x)
    (x₀ : M) (k : Fin (Module.finrank ℝ E)) (hx : x ∈ (chartAt H x₀).source) :
    Work.Diff.EXT.JointSmoothAt I M
      (fun p : ℝ × M ↦ mvfderiv I (fun y ↦ Φ (p.1, y)) p.2 (cFrame (I := I) x₀ k p.2)) t₀ x := by
  obtain ⟨S, hSsm, hSeq⟩ :=
    Submission.ChartConnection.exists_contMDiff_section_eventuallyEq_frameSection (I := I) x₀
      (cBasis (E := E) k) hx
  have h := Work.Diff.EXT.contMDiffAt_mvfderiv_along_field (I := I) (M := M) (Φ := Φ) (A := S) hΦ
    (by simpa [Work.Diff.EXT.SmoothField] using hSsm)
  refine h.congr_of_eventuallyEq ?_
  filter_upwards [(continuous_snd.tendsto (t₀, x)).eventually hSeq] with p hp
  simp only [cFrame, hp]

/-! ## Joint smoothness of `koszulPair` and of its coordinate derivatives -/

theorem koszulPair_jointSmooth {G : ℝ → SMet I M} {J : Set ℝ} (hJ : IsOpen J)
    (hG : JointSmooth G J) {t₀ : ℝ} (ht₀ : t₀ ∈ J) (x₀ : M)
    (a b c : Fin (Module.finrank ℝ E)) :
    Work.Diff.EXT.JointSmoothAt I M
      (fun p : ℝ × M ↦ koszulPair (I := I) G x₀ a b c p.1 p.2) t₀ x₀ := by
  have h1 : Work.Diff.EXT.JointSmoothAt I M
      (fun p : ℝ × M ↦ mvfderiv I (fun y' ↦ mComp (I := I) G x₀ b c p.1 y') p.2
        (cFrame (I := I) x₀ a p.2)) t₀ x₀ :=
    mvfderiv_jointSmooth_frame (I := I) (F := ℝ)
      (Φ := fun p : ℝ × M ↦ mComp (I := I) G x₀ b c p.1 p.2)
      (mComp_jointSmooth (I := I) hJ hG ht₀ x₀ b c) x₀ a (mem_chart_source H x₀)
  have h2 : Work.Diff.EXT.JointSmoothAt I M
      (fun p : ℝ × M ↦ mvfderiv I (fun y' ↦ mComp (I := I) G x₀ c a p.1 y') p.2
        (cFrame (I := I) x₀ b p.2)) t₀ x₀ :=
    mvfderiv_jointSmooth_frame (I := I) (F := ℝ)
      (Φ := fun p : ℝ × M ↦ mComp (I := I) G x₀ c a p.1 p.2)
      (mComp_jointSmooth (I := I) hJ hG ht₀ x₀ c a) x₀ b (mem_chart_source H x₀)
  have h3 : Work.Diff.EXT.JointSmoothAt I M
      (fun p : ℝ × M ↦ mvfderiv I (fun y' ↦ mComp (I := I) G x₀ a b p.1 y') p.2
        (cFrame (I := I) x₀ c p.2)) t₀ x₀ :=
    mvfderiv_jointSmooth_frame (I := I) (F := ℝ)
      (Φ := fun p : ℝ × M ↦ mComp (I := I) G x₀ a b p.1 p.2)
      (mComp_jointSmooth (I := I) hJ hG ht₀ x₀ a b) x₀ c (mem_chart_source H x₀)
  have hmain : Work.Diff.EXT.JointSmoothAt I M
      (fun p : ℝ × M ↦ (1 / 2 : ℝ) *
        (mvfderiv I (fun y' ↦ mComp (I := I) G x₀ b c p.1 y') p.2 (cFrame (I := I) x₀ a p.2)
          + mvfderiv I (fun y' ↦ mComp (I := I) G x₀ c a p.1 y') p.2 (cFrame (I := I) x₀ b p.2)
          - mvfderiv I (fun y' ↦ mComp (I := I) G x₀ a b p.1 y') p.2
              (cFrame (I := I) x₀ c p.2))) t₀ x₀ :=
    (contMDiffAt_const (c := (1 / 2 : ℝ))).mul ((h1.add h2).sub h3)
  simpa only [koszulPair, mComp, cFrame, Submission.Geodesic.frameSection_eq_frameVector]
    using hmain

theorem dOp_koszulPair_jointSmooth {G : ℝ → SMet I M} {J : Set ℝ} (hJ : IsOpen J)
    (hG : JointSmooth G J) {t₀ : ℝ} (ht₀ : t₀ ∈ J) (x₀ : M)
    (i j l k : Fin (Module.finrank ℝ E)) :
    Work.Diff.EXT.JointSmoothAt I M
      (fun p : ℝ × M ↦ dOp (I := I) x₀ i (koszulPair (I := I) G x₀ j l k) p.1 p.2) t₀ x₀ := by
  have h : Work.Diff.EXT.JointSmoothAt I M
      (fun p : ℝ × M ↦ mvfderiv I (fun y' ↦ koszulPair (I := I) G x₀ j l k p.1 y') p.2
        (cFrame (I := I) x₀ i p.2)) t₀ x₀ :=
    mvfderiv_jointSmooth_frame (I := I) (F := ℝ)
      (Φ := fun p : ℝ × M ↦ koszulPair (I := I) G x₀ j l k p.1 p.2)
      (koszulPair_jointSmooth (I := I) hJ hG ht₀ x₀ j l k) x₀ i (mem_chart_source H x₀)
  simpa only [dOp] using h

/-! ## Joint smoothness of the Christoffel symbol and of its derivatives -/

theorem chrB_const_jointSmooth {G : ℝ → SMet I M} {J : Set ℝ} (hJ : IsOpen J)
    (hG : JointSmooth G J) {t₀ : ℝ} (ht₀ : t₀ ∈ J) (x₀ : M)
    (a b : Fin (Module.finrank ℝ E)) :
    Work.Diff.EXT.JointSmoothAt I M
      (fun p : ℝ × M ↦ Submission.ChartCurv.chrB (lcOf (G p.1)) x₀ p.2
        (cBasis (E := E) a) (cBasis (E := E) b)) t₀ x₀ := by
  have hex : Work.Diff.EXT.JointSmoothAt I M
      (fun p : ℝ × M ↦ ∑ k, (Matrix.mulVec (GramInv (I := I) G x₀ p.1 p.2)
          (fun k ↦ koszulPair (I := I) G x₀ a b k p.1 p.2)) k • cBasis (E := E) k) t₀ x₀ := by
    refine ContMDiffAt.sum (fun k _ ↦ ?_)
    have hmv : Work.Diff.EXT.JointSmoothAt I M
        (fun p : ℝ × M ↦ (Matrix.mulVec (GramInv (I := I) G x₀ p.1 p.2)
          (fun k ↦ koszulPair (I := I) G x₀ a b k p.1 p.2)) k) t₀ x₀ := by
      have hmv' : Work.Diff.EXT.JointSmoothAt I M
          (fun p : ℝ × M ↦ ∑ m, GramInv (I := I) G x₀ p.1 p.2 k m
            * koszulPair (I := I) G x₀ a b m p.1 p.2) t₀ x₀ :=
        ContMDiffAt.sum (fun m _ ↦
          (gramInv_jointSmooth (I := I) hJ hG ht₀ x₀ k m).mul
            (koszulPair_jointSmooth (I := I) hJ hG ht₀ x₀ a b m))
      simpa only [Matrix.mulVec_apply, dotProduct, Matrix.row_apply] using hmv'
    exact (ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) (cBasis (E := E) k)).contMDiffAt.comp
      (t₀, x₀) hmv
  refine hex.congr_of_eventuallyEq ?_
  rw [nhds_prod_eq]
  filter_upwards [Filter.prod_mem_prod Filter.univ_mem
      ((chartAt H x₀).open_source.mem_nhds (mem_chart_source H x₀))] with p hp
  exact chrB_eq_sum_gramInv (I := I) G x₀ p.1 hp.2 a b

theorem dB_const_jointSmooth {G : ℝ → SMet I M} {J : Set ℝ} (hJ : IsOpen J)
    (hG : JointSmooth G J) {t₀ : ℝ} (ht₀ : t₀ ∈ J) (x₀ : M)
    (v a b : Fin (Module.finrank ℝ E)) :
    Work.Diff.EXT.JointSmoothAt I M
      (fun p : ℝ × M ↦ Submission.ChartCurv.dB (lcOf (G p.1)) x₀ p.2 (cBasis (E := E) v)
        (cBasis (E := E) a) (cBasis (E := E) b)) t₀ x₀ := by
  have hchr : Work.Diff.EXT.JointSmoothAt I M
      (fun p : ℝ × M ↦ Submission.ChartCurv.chrB (lcOf (G p.1)) x₀ p.2
        (cBasis (E := E) a) (cBasis (E := E) b)) t₀ x₀ :=
    chrB_const_jointSmooth (I := I) hJ hG ht₀ x₀ a b
  have h : Work.Diff.EXT.JointSmoothAt I M
      (fun p : ℝ × M ↦ mvfderiv I
        (fun y' ↦ Submission.ChartCurv.chrB (lcOf (G p.1)) x₀ y'
          (cBasis (E := E) a) (cBasis (E := E) b)) p.2 (cFrame (I := I) x₀ v p.2)) t₀ x₀ :=
    mvfderiv_jointSmooth_frame (I := I) (F := E)
      (Φ := fun p : ℝ × M ↦ Submission.ChartCurv.chrB (lcOf (G p.1)) x₀ p.2
        (cBasis (E := E) a) (cBasis (E := E) b)) hchr x₀ v (mem_chart_source H x₀)
  simpa only [Submission.ChartCurv.dB, cFrame,
    Submission.Geodesic.frameSection_eq_frameVector] using h

theorem chrB_arg_jointSmooth {G : ℝ → SMet I M} {J : Set ℝ} (hJ : IsOpen J)
    (hG : JointSmooth G J) {t₀ : ℝ} (ht₀ : t₀ ∈ J) (x₀ : M)
    {W : ℝ × M → E} (hW : Work.Diff.EXT.JointSmoothAt I M W t₀ x₀)
    (a : Fin (Module.finrank ℝ E)) :
    Work.Diff.EXT.JointSmoothAt I M
      (fun p : ℝ × M ↦ Submission.ChartCurv.chrB (lcOf (G p.1)) x₀ p.2 (W p)
        (cBasis (E := E) a)) t₀ x₀ := by
  have hex : Work.Diff.EXT.JointSmoothAt I M
      (fun p : ℝ × M ↦ ∑ m, ((cBasis (E := E)).coord m (W p)) •
        Submission.ChartCurv.chrB (lcOf (G p.1)) x₀ p.2 (cBasis (E := E) m)
          (cBasis (E := E) a)) t₀ x₀ := by
    refine ContMDiffAt.sum (fun m _ ↦ ?_)
    have hcoef : ContMDiffAt ((𝓘(ℝ,ℝ)).prod I) 𝓘(ℝ,ℝ) ∞
        (fun p : ℝ × M ↦ (cBasis (E := E)).coord m (W p)) (t₀, x₀) :=
      (LinearMap.toContinuousLinearMap ((cBasis (E := E)).coord m)).contMDiffAt.comp (t₀, x₀) hW
    have hvec : ContMDiffAt ((𝓘(ℝ,ℝ)).prod I) 𝓘(ℝ,E) ∞
        (fun p : ℝ × M ↦ Submission.ChartCurv.chrB (lcOf (G p.1)) x₀ p.2
          (cBasis (E := E) m) (cBasis (E := E) a)) (t₀, x₀) :=
      chrB_const_jointSmooth (I := I) hJ hG ht₀ x₀ m a
    exact hcoef.smul hvec
  refine hex.congr_of_eventuallyEq ?_
  rw [nhds_prod_eq]
  filter_upwards [Filter.prod_mem_prod Filter.univ_mem
      ((chartAt H x₀).open_source.mem_nhds (mem_chart_source H x₀))] with p hp
  conv_lhs => rw [← Submission.ChartCurv.sum_coord_smul_eq (E := E) (W p)]
  rw [Submission.ChartCurv.chrB_sum_fst Finset.univ x₀ p.2 _ _ (cBasis (E := E) a) hp.2]

/-! ## Joint smoothness of the chart curvature -/

theorem cCurv_jointSmooth {G : ℝ → SMet I M} {J : Set ℝ} (hJ : IsOpen J)
    (hG : JointSmooth G J) {t₀ : ℝ} (ht₀ : t₀ ∈ J) (x₀ : M)
    (i j l : Fin (Module.finrank ℝ E)) :
    Work.Diff.EXT.JointSmoothAt I M
      (fun p : ℝ × M ↦ cCurv (G p.1) x₀ p.2 (cBasis (E := E) i) (cBasis (E := E) j)
        (cBasis (E := E) l)) t₀ x₀ := by
  have h1 := dB_const_jointSmooth (I := I) hJ hG ht₀ x₀ i l j
  have h2 := dB_const_jointSmooth (I := I) hJ hG ht₀ x₀ j l i
  have h3 := chrB_arg_jointSmooth (I := I) (M := M) hJ hG ht₀ x₀
    (W := fun p : ℝ × M ↦ Submission.ChartCurv.chrB (lcOf (G p.1)) x₀ p.2
      (cBasis (E := E) l) (cBasis (E := E) j))
    (chrB_const_jointSmooth (I := I) hJ hG ht₀ x₀ l j) i
  have h4 := chrB_arg_jointSmooth (I := I) (M := M) hJ hG ht₀ x₀
    (W := fun p : ℝ × M ↦ Submission.ChartCurv.chrB (lcOf (G p.1)) x₀ p.2
      (cBasis (E := E) l) (cBasis (E := E) i))
    (chrB_const_jointSmooth (I := I) hJ hG ht₀ x₀ l i) j
  have hc := (((h1.sub h2).add h3).sub h4)
  refine hc.congr_of_eventuallyEq ?_
  filter_upwards with p
  rfl

theorem cGram_eq_sum_coord (G : ℝ → SMet I M) (x₀ : M) {y : M}
    (hy : y ∈ (chartAt H x₀).source) (t : ℝ) (V : E)
    (k : Fin (Module.finrank ℝ E)) :
    cGram (G t) x₀ y V (cBasis (E := E) k)
      = ∑ m, ((cBasis (E := E)).coord m V) * mComp (I := I) G x₀ m k t y := by
  rw [cGram]
  have hV : Submission.Geodesic.frameVector (I := I) x₀ y V
      = ∑ m, ((cBasis (E := E)).coord m V) •
          Submission.Geodesic.frameVector (I := I) x₀ y (cBasis (E := E) m) := by
    conv_lhs => rw [← Submission.ChartCurv.sum_coord_smul_eq (E := E) V]
    rw [Submission.Geodesic.frameVector_sum Finset.univ x₀ y]
  rw [hV]
  simp only [mComp, cFrame, Submission.Geodesic.frameSection_eq_frameVector, map_sum, map_smul,
    sum_apply, smul_apply, smul_eq_mul]

theorem cRm_jointSmooth {G : ℝ → SMet I M} {J : Set ℝ} (hJ : IsOpen J)
    (hG : JointSmooth G J) {t₀ : ℝ} (ht₀ : t₀ ∈ J) (x₀ : M)
    (i j k l : Fin (Module.finrank ℝ E)) :
    Work.Diff.EXT.JointSmoothAt I M
      (fun p : ℝ × M ↦ cRm (G p.1) x₀ p.2 (cBasis (E := E) i) (cBasis (E := E) j)
        (cBasis (E := E) k) (cBasis (E := E) l)) t₀ x₀ := by
  have hV : Work.Diff.EXT.JointSmoothAt I M
      (fun p : ℝ × M ↦ cCurv (G p.1) x₀ p.2 (cBasis (E := E) i) (cBasis (E := E) j)
        (cBasis (E := E) l)) t₀ x₀ := cCurv_jointSmooth (I := I) hJ hG ht₀ x₀ i j l
  have hex : Work.Diff.EXT.JointSmoothAt I M
      (fun p : ℝ × M ↦ ∑ m, ((cBasis (E := E)).coord m
          (cCurv (G p.1) x₀ p.2 (cBasis (E := E) i) (cBasis (E := E) j) (cBasis (E := E) l)))
        * mComp (I := I) G x₀ m k p.1 p.2) t₀ x₀ :=
    ContMDiffAt.sum (fun m _ ↦
      ((LinearMap.toContinuousLinearMap ((cBasis (E := E)).coord m)).contMDiffAt.comp
        (t₀, x₀) hV).mul (mComp_jointSmooth (I := I) hJ hG ht₀ x₀ m k))
  refine hex.congr_of_eventuallyEq ?_
  rw [nhds_prod_eq]
  filter_upwards [Filter.prod_mem_prod Filter.univ_mem
      ((chartAt H x₀).open_source.mem_nhds (mem_chart_source H x₀))] with p hp
  exact cGram_eq_sum_coord (I := I) G x₀ hp.2 p.1
    (cCurv (G p.1) x₀ p.2 (cBasis (E := E) i) (cBasis (E := E) j) (cBasis (E := E) l)) k

theorem rmC4_jointSmooth {G : ℝ → SMet I M} {J : Set ℝ} (hLC : LCSmooth I M) (hJ : IsOpen J)
    (hG : JointSmooth G J) {t₀ : ℝ} (ht₀ : t₀ ∈ J) (x₀ : M)
    (i j k l : Fin (Module.finrank ℝ E)) :
    Work.Diff.EXT.JointSmoothAt I M
      (fun p : ℝ × M ↦ rmC4 (I := I) G x₀ p.1 p.2 i j k l) t₀ x₀ := by
  refine (cRm_jointSmooth (I := I) hJ hG ht₀ x₀ i j k l).congr_of_eventuallyEq ?_
  rw [nhds_prod_eq]
  filter_upwards [Filter.prod_mem_prod Filter.univ_mem
      ((chartAt H x₀).open_source.mem_nhds (mem_chart_source H x₀))] with p hp
  exact rmC4_eq_cRm (I := I) hLC G x₀ p.1 hp.2 i j k l

end Helpers

theorem rmP_jointSmooth
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ((⊤ : ENat) : WithTop ENat) M]
    [I.Boundaryless] [T2Space M] [CompactSpace M]
    (hLC : Submission.Diff.LCSmooth I M) :
    ∀ (G : ℝ → Submission.Diff.SMet I M) (J : Set ℝ), IsOpen J →
      Submission.Diff.JointSmooth G J →
      ∀ (A B C D : Π y : M, TangentSpace I y),
        Work.Diff.GE.SmoothField (I := I) (M := M) A →
        Work.Diff.GE.SmoothField (I := I) (M := M) B →
        Work.Diff.GE.SmoothField (I := I) (M := M) C →
        Work.Diff.GE.SmoothField (I := I) (M := M) D →
      ∀ t ∈ J, ∀ x : M,
        ContMDiffAt ((modelWithCornersSelf ℝ ℝ).prod I) (modelWithCornersSelf ℝ ℝ)
          (⊤ : ℕ∞)
          (fun p : ℝ × M ↦ Submission.Diff.rmP (G p.1) p.2 (A p.2) (B p.2) (C p.2) (D p.2))
          (t, x) := by
  intro G J hJ hG A B C D hA hB hC hD t ht x
  letI : RiemannianBundle (fun y : M ↦ TangentSpace I y) := ⟨(G t).toRiemannianMetric⟩
  haveI : IsContMDiffRiemannianBundle I (⊤ : ℕ∞) E (fun y : M ↦ TangentSpace I y) := inferInstance
  set Ψ : ℝ × M → ℝ := fun p ↦ ∑ i, ∑ j, ∑ k, ∑ l,
      ((cBasis (E := E)).coord i (Submission.ChartCurv.coordFun (I := I) x A p.2))
      * ((cBasis (E := E)).coord j (Submission.ChartCurv.coordFun (I := I) x B p.2))
      * ((cBasis (E := E)).coord k (Submission.ChartCurv.coordFun (I := I) x C p.2))
      * ((cBasis (E := E)).coord l (Submission.ChartCurv.coordFun (I := I) x D p.2))
      * cRm (G p.1) x p.2 (cBasis (E := E) i) (cBasis (E := E) j) (cBasis (E := E) k)
          (cBasis (E := E) l) with hΨdef
  have hcoef : ∀ (V : Π y : M, TangentSpace I y), Work.Diff.GE.SmoothField (I := I) (M := M) V →
      ∀ m : Fin (Module.finrank ℝ E),
        ContMDiffAt ((𝓘(ℝ,ℝ)).prod I) 𝓘(ℝ,ℝ) ∞
          (fun p : ℝ × M ↦ (cBasis (E := E)).coord m
            (Submission.ChartCurv.coordFun (I := I) x V p.2)) (t, x) := by
    intro V hV m
    have hV' : ContMDiffAt I 𝓘(ℝ,E) ∞ (Submission.ChartCurv.coordFun (I := I) x V) x :=
      Submission.ChartCurv.contMDiffAt_coordFun (I := I) x hV (mem_chart_source H x)
    exact (LinearMap.toContinuousLinearMap ((cBasis (E := E)).coord m)).contMDiffAt.comp
      (t, x) (hV'.comp (t, x) contMDiffAt_snd)
  have hΨ : ContMDiffAt ((modelWithCornersSelf ℝ ℝ).prod I) (modelWithCornersSelf ℝ ℝ)
      (⊤ : ℕ∞) Ψ (t, x) := by
    rw [hΨdef]
    refine ContMDiffAt.sum (fun i _ ↦ ?_)
    refine ContMDiffAt.sum (fun j _ ↦ ?_)
    refine ContMDiffAt.sum (fun k _ ↦ ?_)
    refine ContMDiffAt.sum (fun l _ ↦ ?_)
    exact ((((hcoef A hA i).mul (hcoef B hB j)).mul (hcoef C hC k)).mul (hcoef D hD l)).mul
      (cRm_jointSmooth (I := I) (M := M) hJ hG ht x i j k l)
  refine hΨ.congr_of_eventuallyEq ?_
  rw [nhds_prod_eq, hΨdef]
  filter_upwards [Filter.prod_mem_prod Filter.univ_mem
      ((chartAt H x).open_source.mem_nhds (mem_chart_source H x))] with p hp
  rw [rmP_eq_sum_rmC4 (I := I) hLC G x p.1 hp.2]
  refine Finset.sum_congr rfl (fun i _ ↦ Finset.sum_congr rfl (fun j _ ↦
    Finset.sum_congr rfl (fun k _ ↦ Finset.sum_congr rfl (fun l _ ↦ ?_))))
  rw [rmC4_eq_cRm (I := I) hLC G x p.1 hp.2 i j k l]


end Work.Diff.GE
