import Mathlib
import Submission.Work.Diff.GE.deps
import Submission.Work.Diff.GE.koszul
import Submission.Work.Diff.GE.chartcalc
import Submission.Work.Diff.GE.Frame
import Submission.Work.Diff.GE.rmChartExpr_kit
import Submission.Work.Diff.GE.cGram_chrB_eq_koszulPair
import Submission.Work.Diff.GE.cGram_eq_sum_gramInv

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.GE

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology BigOperators
open Bundle ContDiff Set VectorField CovariantDerivative Metric
open Submission.Curvature Submission.CurvatureVec Submission.Geodesic Submission.ChartCurv
open Submission.ChartConnection Commons.Geometry.Manifold.VectorBundle.CovariantDerivative

namespace RmChartAux

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M] [IsManifold I ∞ M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]

noncomputable section

theorem rmC4_eq_cGram_cCurv (hLC : LCSmooth I M) (G : ℝ → SMet I M) (x₀ : M) (t : ℝ) {y : M}
    (hy : y ∈ (chartAt H x₀).source) (i j k l : Fin (Module.finrank ℝ E)) :
    rmC4 (I := I) G x₀ t y i j k l
      = cGram (G t) x₀ y (cCurv (G t) x₀ y (cBasis (E := E) i) (cBasis (E := E) j)
          (cBasis (E := E) l)) (cBasis (E := E) k) := by
  letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨(G t).toRiemannianMetric⟩
  haveI : IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x) := inferInstance
  obtain ⟨hcov, htor, -⟩ := hLC (G t)
  obtain ⟨hcov⟩ := hcov
  show (G t).inner y (rmVec (lcOf (G t)) y (frameVector (I := I) x₀ y (cBasis (E := E) i))
      (frameVector (I := I) x₀ y (cBasis (E := E) j))
      (frameVector (I := I) x₀ y (cBasis (E := E) l))) (frameVector (I := I) x₀ y (cBasis (E := E) k))
    = _
  rw [rmVec_eq_curvVec (lcOf (G t)) hcov y _ _ _,
    curvVec_eq_chart (cov := lcOf (G t)) htor x₀ y (cBasis (E := E) l) (cBasis (E := E) j)
      (cBasis (E := E) i) hy]
  rfl

/-- `mvfderiv` respects eventual equality (for an arbitrary normed codomain). -/
lemma mvfderiv_congr_of_eventuallyEq' {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {g₁ g₂ : M → F} {x : M} (h : g₁ =ᶠ[𝓝 x] g₂) : mvfderiv I g₁ x = mvfderiv I g₂ x := by
  rw [mvfderiv, mvfderiv, h.eq_of_nhds, Filter.EventuallyEq.mfderiv_eq h]
  all_goals first | rfl | (ext v; rfl)

/-- A section that is smooth on an open set has a globally smooth representative agreeing with it
near any of its points. -/
lemma exists_contMDiff_section_eventuallyEq_of_contMDiffOn
    {V : Π x : M, TangentSpace I x} {p : M} {u : Set M} (hu : IsOpen u) (hpu : p ∈ u)
    (hV : CMDiff[u] ∞ (T% V)) :
    ∃ W : Π x : M, TangentSpace I x, CMDiff ∞ (T% W) ∧ W =ᶠ[𝓝 p] V := by
  obtain ⟨ψ, -, hψts⟩ := (SmoothBumpFunction.nhds_basis_tsupport (I := I) p).mem_iff.mp
    (hu.mem_nhds hpu)
  refine ⟨fun q => ψ q • V q, ?_, ?_⟩
  · exact ContMDiffOn.smul_section_of_tsupport (I := I) (F := E) (V := TangentSpace I)
      ψ.contMDiff.contMDiffOn hu hψts hV
  · filter_upwards [ψ.eventuallyEq_one] with q hq
    rw [hq, Pi.one_apply, one_smul]

/-- **Product rule for the lowered Christoffel pairing in the coordinate frame.** -/
theorem dOp_fPair_eq (hLC : LCSmooth I M) (G : ℝ → SMet I M) (x₀ : M) {y : M}
    (hy : y ∈ (chartAt H x₀).source) (t : ℝ) (A B D K : Fin (Module.finrank ℝ E)) :
    dOp (I := I) x₀ A (fPair (I := I) G x₀ B D K) t y
      = cGram (G t) x₀ y (dB (lcOf (G t)) x₀ y (cBasis (E := E) A) (cBasis (E := E) D)
            (cBasis (E := E) B)
          + chrB (lcOf (G t)) x₀ y (chrB (lcOf (G t)) x₀ y (cBasis (E := E) D) (cBasis (E := E) B))
              (cBasis (E := E) A))
          (cBasis (E := E) K)
        + cGram (G t) x₀ y (chrB (lcOf (G t)) x₀ y (cBasis (E := E) D) (cBasis (E := E) B))
            (chrB (lcOf (G t)) x₀ y (cBasis (E := E) K) (cBasis (E := E) A)) := by
  letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨(G t).toRiemannianMetric⟩
  haveI : IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x) := inferInstance
  obtain ⟨hcov, htor, hmet⟩ := hLC (G t)
  obtain ⟨hcov⟩ := hcov
  obtain ⟨X, hXsm, hXeq⟩ :=
    exists_contMDiff_section_eventuallyEq_frameSection (I := I) x₀ (cBasis (E := E) K) hy
  obtain ⟨T, hTsm, hTeq⟩ :=
    exists_contMDiff_section_eventuallyEq_frameSection (I := I) x₀ (cBasis (E := E) A) hy
  have hXy : X y = frameVector (I := I) x₀ y (cBasis (E := E) K) := hXeq.eq_of_nhds
  have hTy : T y = frameVector (I := I) x₀ y (cBasis (E := E) A) := hTeq.eq_of_nhds
  -- the field `∇_{σ_B}σ_D`, smooth on the chart, extended globally
  have hσ : ∀ i : Fin (Module.finrank ℝ E), CMDiff[(chartAt H x₀).source] ∞
      (T% (fun q : M => (trivializationAt E (TangentSpace I) x₀).symmL ℝ q (cBasis (E := E) i))) :=
    fun i => contMDiffOn_trivializationAt_symmL_section (I := I) (M := M) x₀ (cBasis (E := E) i)
  have hVsm : CMDiff[(chartAt H x₀).source] ∞
      (T% (fun q : M => (lcOf (G t)) (frameSection (I := I) x₀ (cBasis (E := E) D)) q
          (frameVector (I := I) x₀ q (cBasis (E := E) B)))) :=
    contMDiffOn_cov_apply (lcOf (G t)) hcov (chartAt H x₀).open_source (hσ D) (hσ B)
  obtain ⟨W, hWsm, hWeq⟩ := exists_contMDiff_section_eventuallyEq_of_contMDiffOn (I := I)
    (chartAt H x₀).open_source hy hVsm
  -- the function whose derivative is taken
  have hfun : (fun q : M => inner ℝ (W q) (X q)) =ᶠ[𝓝 y] fPair (I := I) G x₀ B D K t := by
    filter_upwards [hWeq, hXeq] with q hWq hXq
    rw [hWq, hXq]
    rfl
  have hLHS : mvfderiv I (fun q : M => inner ℝ (W q) (X q)) y (T y)
      = dOp (I := I) x₀ A (fPair (I := I) G x₀ B D K) t y := by
    rw [mvfderiv_congr_of_eventuallyEq' (I := I) hfun, hTy]
    rfl
  -- the product rule
  have hprod := hmet W X hWsm hXsm y (T y)
  -- the coordinates of the field
  have hcoord : coordFun (I := I) x₀ W =ᶠ[𝓝 y]
      (fun q : M => chrB (lcOf (G t)) x₀ q (cBasis (E := E) D) (cBasis (E := E) B)) := by
    filter_upwards [hWeq] with q hq
    rw [coordFun_apply, hq]
    rfl
  have hcy : coordFun (I := I) x₀ W y
      = chrB (lcOf (G t)) x₀ y (cBasis (E := E) D) (cBasis (E := E) B) := hcoord.eq_of_nhds
  have hmvf : mvfderiv I (coordFun (I := I) x₀ W) y
      (frameVector (I := I) x₀ y (cBasis (E := E) A))
      = dB (lcOf (G t)) x₀ y (cBasis (E := E) A) (cBasis (E := E) D) (cBasis (E := E) B) := by
    rw [mvfderiv_congr_of_eventuallyEq' (I := I) hcoord]
    rfl
  have hcovW : (lcOf (G t)) W y (T y) = frameVector (I := I) x₀ y
      (dB (lcOf (G t)) x₀ y (cBasis (E := E) A) (cBasis (E := E) D) (cBasis (E := E) B)
        + chrB (lcOf (G t)) x₀ y
            (chrB (lcOf (G t)) x₀ y (cBasis (E := E) D) (cBasis (E := E) B))
            (cBasis (E := E) A)) := by
    have hcf := cov_eq_frameVector_coordFun (cov := lcOf (G t)) (x₀ := x₀) hWsm hy
      (v := cBasis (E := E) A)
    rw [hmvf, hcy] at hcf
    rw [hTy]
    exact hcf
  have hWy : W y = frameVector (I := I) x₀ y
      (chrB (lcOf (G t)) x₀ y (cBasis (E := E) D) (cBasis (E := E) B)) := by
    rw [← frameVector_coordFun_eq (I := I) (x₀ := x₀) (W := W) hy, hcy]
  have hcovX : (lcOf (G t)) X y (T y) = frameVector (I := I) x₀ y
      (chrB (lcOf (G t)) x₀ y (cBasis (E := E) K) (cBasis (E := E) A)) := by
    have hcg : (lcOf (G t)) X y
        = (lcOf (G t)) (frameSection (I := I) x₀ (cBasis (E := E) K)) y :=
      (CovariantDerivative.isCovariantDerivativeOn (cov := lcOf (G t)) (s := Set.univ)).congr_of_eventuallyEq
        (hXsm.mdifferentiableAt (by simp))
        (mdiffAt_frameSection (I := I) x₀ (cBasis (E := E) K) hy) Filter.univ_mem hXeq
    rw [hcg, hTy, cov_frameSection_eq (cov := lcOf (G t)) x₀ y (cBasis (E := E) K)
      (frameVector (I := I) x₀ y (cBasis (E := E) A)) hy]
    rfl
  rw [← hLHS, hprod, hcovW, hcovX, hXy, hWy]
  rfl

/-- `koszulPair` is symmetric in its first two (lower) slots. -/
theorem koszulPair_comm (hLC : LCSmooth I M) (G : ℝ → SMet I M) (x₀ : M) {y : M}
    (hy : y ∈ (chartAt H x₀).source) (a b c : Fin (Module.finrank ℝ E)) (t : ℝ) :
    koszulPair (I := I) G x₀ a b c t y = koszulPair (I := I) G x₀ b a c t y := by
  letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨(G t).toRiemannianMetric⟩
  haveI : IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x) := inferInstance
  obtain ⟨-, htor, -⟩ := hLC (G t)
  rw [← fPair_eq_koszul G x₀ t hy a b c, ← fPair_eq_koszul G x₀ t hy b a c]
  simp only [fPair]
  show (G t).inner y ((lcOf (G t)) (frameSection (I := I) x₀ (cBasis (E := E) b)) y
        (frameVector (I := I) x₀ y (cBasis (E := E) a))) (frameVector (I := I) x₀ y (cBasis (E := E) c))
      = (G t).inner y ((lcOf (G t)) (frameSection (I := I) x₀ (cBasis (E := E) a)) y
        (frameVector (I := I) x₀ y (cBasis (E := E) b))) (frameVector (I := I) x₀ y (cBasis (E := E) c))
  rw [cov_frameSection_frameVector_comm (cov := lcOf (G t)) htor x₀ y hy
    (cBasis (E := E) b) (cBasis (E := E) a)]

/-- `dOp` of `fPair` is `dOp` of `koszulPair` (they agree on the chart). -/
theorem dOp_fPair_eq_koszul (G : ℝ → SMet I M) (x₀ : M) {y : M}
    (hy : y ∈ (chartAt H x₀).source) (t : ℝ) (A B D K : Fin (Module.finrank ℝ E)) :
    dOp (I := I) x₀ A (fPair (I := I) G x₀ B D K) t y
      = dOp (I := I) x₀ A (koszulPair (I := I) G x₀ B D K) t y := by
  show mvfderiv I (fPair (I := I) G x₀ B D K t) y (cFrame (I := I) x₀ A y) = _
  rw [mvfderiv_congr_of_eventuallyEq' (I := I) ?_]
  · rfl
  · filter_upwards [(chartAt H x₀).open_source.mem_nhds hy] with q hq
    exact fPair_eq_koszul G x₀ t hq B D K

/-- The chart pairing of the coordinate Christoffel vectors `chrB` in the inverse Gram matrix. -/
theorem cGram_chrB_chrB_eq_sum (hLC : LCSmooth I M) (G : ℝ → SMet I M) (x₀ : M) {y : M}
    (hy : y ∈ (chartAt H x₀).source) (t : ℝ) (B D K A : Fin (Module.finrank ℝ E)) :
    cGram (G t) x₀ y (chrB (lcOf (G t)) x₀ y (cBasis (E := E) D) (cBasis (E := E) B))
        (chrB (lcOf (G t)) x₀ y (cBasis (E := E) K) (cBasis (E := E) A))
      = ∑ m, ∑ n, GramInv (I := I) G x₀ t y m n * koszulPair (I := I) G x₀ B D m t y
          * koszulPair (I := I) G x₀ A K n t y := by
  rw [cGram_eq_sum_gramInv (I := I) G x₀ hy t _ _]
  refine Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun n _ => ?_
  rw [cGram_chrB_eq_koszulPair (I := I) G x₀ hy t D B m,
    cGram_chrB_eq_koszulPair (I := I) G x₀ hy t K A n,
    koszulPair_comm hLC G x₀ hy D B m t, koszulPair_comm hLC G x₀ hy K A n t]

end

end RmChartAux

/-- **The chart expression for the curvature components.** -/
theorem rmChartExpr_eq
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M] [IsManifold I ∞ M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
    (hLC : LCSmooth I M) (G : ℝ → SMet I M) (x₀ : M) (t : ℝ) {y : M}
    (hy : y ∈ (chartAt H x₀).source) (i j k l : Fin (Module.finrank ℝ E)) :
    rmC4 (I := I) G x₀ t y i j k l = rmChartExpr (I := I) G x₀ i j k l t y := by
  rw [RmChartAux.rmC4_eq_cGram_cCurv (I := I) hLC G x₀ t hy i j k l]
  -- `cCurv` is the difference of the two "Christoffel derivative plus Christoffel product" terms
  have hcv : cCurv (G t) x₀ y (cBasis (E := E) i) (cBasis (E := E) j) (cBasis (E := E) l)
      = (dB (lcOf (G t)) x₀ y (cBasis (E := E) i) (cBasis (E := E) l) (cBasis (E := E) j)
          + chrB (lcOf (G t)) x₀ y
              (chrB (lcOf (G t)) x₀ y (cBasis (E := E) l) (cBasis (E := E) j))
              (cBasis (E := E) i))
        - (dB (lcOf (G t)) x₀ y (cBasis (E := E) j) (cBasis (E := E) l) (cBasis (E := E) i)
          + chrB (lcOf (G t)) x₀ y
              (chrB (lcOf (G t)) x₀ y (cBasis (E := E) l) (cBasis (E := E) i))
              (cBasis (E := E) j)) := by
    simp only [cCurv]
    abel
  rw [hcv, cGram_sub_fst]
  -- the product rule, applied to the two terms separately
  have hP' : cGram (G t) x₀ y
        (dB (lcOf (G t)) x₀ y (cBasis (E := E) i) (cBasis (E := E) l) (cBasis (E := E) j)
          + chrB (lcOf (G t)) x₀ y
              (chrB (lcOf (G t)) x₀ y (cBasis (E := E) l) (cBasis (E := E) j))
              (cBasis (E := E) i))
        (cBasis (E := E) k)
      = dOp (I := I) x₀ i (fPair (I := I) G x₀ j l k) t y
        - cGram (G t) x₀ y (chrB (lcOf (G t)) x₀ y (cBasis (E := E) l) (cBasis (E := E) j))
            (chrB (lcOf (G t)) x₀ y (cBasis (E := E) k) (cBasis (E := E) i)) := by
    rw [RmChartAux.dOp_fPair_eq (I := I) hLC G x₀ hy t i j l k]
    ring
  have hQ' : cGram (G t) x₀ y
        (dB (lcOf (G t)) x₀ y (cBasis (E := E) j) (cBasis (E := E) l) (cBasis (E := E) i)
          + chrB (lcOf (G t)) x₀ y
              (chrB (lcOf (G t)) x₀ y (cBasis (E := E) l) (cBasis (E := E) i))
              (cBasis (E := E) j))
        (cBasis (E := E) k)
      = dOp (I := I) x₀ j (fPair (I := I) G x₀ i l k) t y
        - cGram (G t) x₀ y (chrB (lcOf (G t)) x₀ y (cBasis (E := E) l) (cBasis (E := E) i))
            (chrB (lcOf (G t)) x₀ y (cBasis (E := E) k) (cBasis (E := E) j)) := by
    rw [RmChartAux.dOp_fPair_eq (I := I) hLC G x₀ hy t j i l k]
    ring
  rw [hP', hQ',
    RmChartAux.dOp_fPair_eq_koszul (I := I) G x₀ hy t i j l k,
    RmChartAux.dOp_fPair_eq_koszul (I := I) G x₀ hy t j i l k,
    RmChartAux.cGram_chrB_chrB_eq_sum (I := I) hLC G x₀ hy t j l k i,
    RmChartAux.cGram_chrB_chrB_eq_sum (I := I) hLC G x₀ hy t i l k j]
  have hrm : rmChartExpr (I := I) G x₀ i j k l t y
      = (dOp (I := I) x₀ i (koszulPair (I := I) G x₀ j l k) t y
          - ∑ m, ∑ n, GramInv (I := I) G x₀ t y m n * koszulPair (I := I) G x₀ j l m t y
              * koszulPair (I := I) G x₀ i k n t y
          - dOp (I := I) x₀ j (koszulPair (I := I) G x₀ i l k) t y
          + ∑ m, ∑ n, GramInv (I := I) G x₀ t y m n * koszulPair (I := I) G x₀ i l m t y
              * koszulPair (I := I) G x₀ j k n t y) := rfl
  rw [hrm]
  ring

end Work.Diff.GE
