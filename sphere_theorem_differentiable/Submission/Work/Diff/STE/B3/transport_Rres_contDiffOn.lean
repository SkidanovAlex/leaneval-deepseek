import Mathlib
import Submission.Work.Diff.STE.B3.TransportDefs
import Submission.Work.Diff.STE.B3.R_contDiff_of_chartData
import Submission.Work.Diff.STE.D.psi.contDiffOn_secChartVal_chart
import Submission.Work.Diff.STE.deTurck.posDef_gmat

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The residual `Rres` is smooth

`Work.Diff.STE.B3.Rres` is the residual of the transport identity of the DeTurck operator in the
localised components of Layer B3: the localised component `R_j(P h)` of the DeTurck operator minus
the second-order operator `Σ_{pq} A^{pq}∂_p∂_q (R_j h)` with coefficient `A`.  This module proves
that it is `C^∞` (indeed that it is `C^∞` *everywhere*, so the statement's restriction to the set
where the chart coordinate lies in the target and the chart matrix of `h` is invertible is
automatic).

The proof is a difference of two smooth functions:

* the second term is a finite sum of products of the smooth `A` with second partial derivatives of
  `R_j h` — smooth because `R_j h` is smooth (`Work.Diff.STE.B3.R_contDiff_of_chartData`) and
  partial derivatives of smooth functions are smooth (`contDiff_pdR_top`);
* the first term is the localised component of the DeTurck section
  `P h = deTurckSec hLC g₀ h …`, which is smooth because `ChartData (P h)` holds: the chart matrix
  of `P h` in *any* chart is the jet-level DeTurck operator `pPhiJetOf g₀ h x₀` evaluated at the
  chart coordinate (`chartMatOf_deTurckSec_eq_pPhiJetOf`), and that is smooth in the coordinate
  because the spatial `2`-jets of the chart matrices of `h` and of the background `g₀` are smooth
  and the jet-level operator `pPhi` is smooth on the locus where both Gram matrices are invertible
  (`Work.Diff.STE.deTurck.contDiffOn_pPhi`); the invertibility of the Gram matrix of `h` is
  positivity of `h` (`det_chartMatOf_of_pos`).
-/

namespace Work.Diff.STE.B3

section Helpers

open scoped Manifold ContDiff Bundle Topology BigOperators
open Bundle ContDiff Set

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ((⊤ : ENat) : WithTop ENat) M] [T2Space M] [I.Boundaryless]
  {g₀ : Submission.Diff.SMet I M}

/-- **Partial derivatives of a smooth function of the flat coordinate are smooth.** -/
lemma contDiff_pdR_top {d : ℕ} (f : (Fin d → ℝ) → ℝ)
    (hf : ContDiff ℝ ((⊤ : ENat) : WithTop ENat) f) (i : Fin d) :
    ContDiff ℝ ((⊤ : ENat) : WithTop ENat) (Work.Diff.STE.pdR i f) := by
  unfold Work.Diff.STE.pdR
  rw [contDiff_infty] at hf ⊢
  intro m
  have hm : ContDiff ℝ (((m : ℕ)) : WithTop ℕ∞) (fderiv ℝ f) :=
    (hf (m + 1)).fderiv_right (m := ((m : ℕ) : WithTop ℕ∞)) (by rw [← Nat.cast_add_one])
  exact (ContinuousLinearMap.apply ℝ ℝ (Pi.single i (1 : ℝ))).contDiff.comp hm

/-- **The chart matrix of a positive definite section is invertible.** -/
lemma det_chartMatOf_of_pos
    (h : Work.Diff.STE.Bil (I := I) (M := M))
    (hsym : ∀ (x : M) (u v : TangentSpace I x), h x u v = h x v u)
    (hpos : ∀ (x : M) (v : TangentSpace I x), v ≠ 0 → 0 < h x v v)
    (x₀ : M) {y : E} (hy : y ∈ (extChartAt I x₀).target) :
    (Matrix.of (Work.Diff.STE.D.chartMatOf (I := I) (M := M) h x₀ y)).det ≠ 0 := by
  classical
  have hx : (extChartAt I x₀).symm y ∈ (chartAt H x₀).source :=
    Work.Diff.STE.D.psi.symm_target_mem_chart_source (I := I) hy
  have hp' : (extChartAt I x₀).symm y
      ∈ (trivializationAt E (TangentSpace I) x₀).baseSet := by
    rw [TangentBundle.trivializationAt_baseSet]; exact hx
  have hL : Function.Injective
      (((trivializationAt E (TangentSpace I) x₀).symmL ℝ
        ((extChartAt I x₀).symm y)).toLinearMap) := by
    intro a b hab
    have hab' : (trivializationAt E (TangentSpace I) x₀).symmL ℝ
          ((extChartAt I x₀).symm y) a
        = (trivializationAt E (TangentSpace I) x₀).symmL ℝ ((extChartAt I x₀).symm y) b := hab
    have h1 := congrArg ((trivializationAt E (TangentSpace I) x₀).continuousLinearMapAt ℝ
      ((extChartAt I x₀).symm y)) hab'
    simpa only [Trivialization.continuousLinearMapAt_symmL _ (R := ℝ) hp' a,
      Trivialization.continuousLinearMapAt_symmL _ (R := ℝ) hp' b] using h1
  have hpd : (Matrix.of (fun i j : Fin (Module.finrank ℝ E) =>
      h ((extChartAt I x₀).symm y) ((trivializationAt E (TangentSpace I) x₀).symmL ℝ
          ((extChartAt I x₀).symm y) ((Module.finBasis ℝ E) i))
        ((trivializationAt E (TangentSpace I) x₀).symmL ℝ
          ((extChartAt I x₀).symm y) ((Module.finBasis ℝ E) j)))).PosDef :=
    Work.Diff.STE.deTurck.posDef_gram_of_injective _ hL
      (h ((extChartAt I x₀).symm y)) (hsym _) (hpos _)
  have hfun : Work.Diff.STE.D.chartMatOf (I := I) (M := M) h x₀ y
      = (fun i j : Fin (Module.finrank ℝ E) =>
        h ((extChartAt I x₀).symm y) ((trivializationAt E (TangentSpace I) x₀).symmL ℝ
            ((extChartAt I x₀).symm y) ((Module.finBasis ℝ E) i))
          ((trivializationAt E (TangentSpace I) x₀).symmL ℝ
            ((extChartAt I x₀).symm y) ((Module.finBasis ℝ E) j))) := by
    funext i j
    simp only [Work.Diff.STE.D.chartMatOf_apply, Submission.Geodesic.frameVector]
  rw [hfun]
  exact ne_of_gt hpd.det_pos

/-- **Smoothness of the jet-level DeTurck operator in the flat coordinate.** -/
lemma contDiffOn_pPhiJetOf
    (g₀ : Submission.Diff.SMet I M)
    (h : Work.Diff.STE.Bil (I := I) (M := M)) (x₀ : M)
    (hchart : ContDiffOn ℝ (⊤ : ℕ∞) (Work.Diff.STE.D.chartMatOf (I := I) (M := M) h x₀)
      (extChartAt I x₀).target)
    (hdet : ∀ y ∈ (extChartAt I x₀).target,
      (Matrix.of (Work.Diff.STE.D.chartMatOf (I := I) (M := M) h x₀ y)).det ≠ 0)
    (i j : Fin (Module.finrank ℝ E)) :
    ContDiffOn ℝ (⊤ : ℕ∞)
      (fun y : E => Work.Diff.STE.D.pPhiJetOf (I := I) (M := M) g₀ h x₀ y i j)
      (extChartAt I x₀).target := by
  have hjetH : ContDiffOn ℝ (⊤ : ℕ∞)
      (fun y : E => Work.Diff.STE.D.chartJetOf (I := I) (M := M) h x₀ y)
      (extChartAt I x₀).target :=
    Work.Diff.STE.D.psi.contDiffOn_chartJetOf (I := I) (M := M) h x₀ hchart
  have hjetG : ContDiffOn ℝ (⊤ : ℕ∞)
      (fun y : E => Work.Diff.STE.D.chartJetOf (I := I) (M := M) g₀.inner x₀ y)
      (extChartAt I x₀).target := by
    refine Work.Diff.STE.D.psi.contDiffOn_chartJetOf (I := I) (M := M) g₀.inner x₀ ?_
    intro y hy
    exact (Work.Diff.EXT.kz_contDiffAt_chartMatFun (I := I) g₀ x₀ hy).contDiffWithinAt
  have hpair : ContDiffOn ℝ (⊤ : ℕ∞)
      (fun y : E => (Work.Diff.STE.D.chartJetOf (I := I) (M := M) g₀.inner x₀ y,
        Work.Diff.STE.D.chartJetOf (I := I) (M := M) h x₀ y)) (extChartAt I x₀).target :=
    hjetG.prodMk hjetH
  have hmem : ∀ y ∈ (extChartAt I x₀).target,
      (Work.Diff.STE.D.chartJetOf (I := I) (M := M) g₀.inner x₀ y,
        Work.Diff.STE.D.chartJetOf (I := I) (M := M) h x₀ y) ∈
      Work.Diff.STE.deTurck.pPhiDom E := by
    intro y hy
    refine ⟨?_, ?_⟩
    · have hp : (extChartAt I x₀).symm y ∈ (chartAt H x₀).source :=
        Work.Diff.STE.D.psi.symm_target_mem_chart_source (I := I) hy
      have hpos := (Work.Diff.STE.deTurck.posDef_gmat (I := I) g₀ x₀ hp).det_pos
      have hne : (Matrix.of (Work.Diff.EXT.gmat (I := I) g₀ x₀
          ((extChartAt I x₀).symm y))).det ≠ 0 := ne_of_gt hpos
      simpa only [Work.Diff.STE.D.psi.chartJetOf_fst_inner (I := I) g₀ x₀ y] using hne
    · simpa only [Work.Diff.STE.D.psi.chartJetOf_fst (I := I) h x₀ y] using hdet y hy
  have hpPhi := (Work.Diff.STE.deTurck.contDiffOn_pPhi (E := E)).comp hpair hmem
  have hpPhi' : ContDiffOn ℝ (⊤ : ℕ∞) (fun y : E => fun i j : Fin (Module.finrank ℝ E) =>
      Work.Diff.STE.DeTurck.pPhi
        (Work.Diff.STE.D.chartJetOf (I := I) (M := M) g₀.inner x₀ y).1
        (Work.Diff.STE.D.chartJetOf (I := I) (M := M) g₀.inner x₀ y).2.1
        (Work.Diff.STE.D.chartJetOf (I := I) (M := M) g₀.inner x₀ y).2.2
        (Work.Diff.STE.D.chartJetOf (I := I) (M := M) h x₀ y).1
        (Work.Diff.STE.D.chartJetOf (I := I) (M := M) h x₀ y).2.1
        (Work.Diff.STE.D.chartJetOf (I := I) (M := M) h x₀ y).2.2 i j)
      (extChartAt I x₀).target :=
    hpPhi.congr (fun y hy => rfl)
  have h2 := (contDiffOn_pi.mp ((contDiffOn_pi.mp hpPhi') i)) j
  exact h2.congr (fun y hy => rfl)

/-- **The chart matrix of the DeTurck section is the jet-level DeTurck operator.** -/
lemma chartMatOf_deTurckSec_eq_pPhiJetOf
    (hLC : Submission.Diff.LCSmooth I M)
    (h : Work.Diff.STE.Bil (I := I) (M := M))
    (hsym : ∀ (x : M) (u v : TangentSpace I x), h x u v = h x v u)
    (hpos : ∀ (x : M) (v : TangentSpace I x), v ≠ 0 → 0 < h x v v)
    (hsmooth : Work.Diff.STE.D.ChartData (I := I) (M := M) h)
    (x₀ : M) {y : E} (hy : y ∈ (extChartAt I x₀).target)
    (i j : Fin (Module.finrank ℝ E)) :
    Work.Diff.STE.D.chartMatOf (I := I) (M := M)
        (Work.Diff.STE.D.deTurckSec (I := I) hLC g₀ h hsym hpos hsmooth) x₀ y i j
      = Work.Diff.STE.D.pPhiJetOf (I := I) (M := M) g₀ h x₀ y i j := by
  have key : Work.Diff.STE.D.pPhiJetOf (I := I) (M := M) g₀
        (Work.Diff.STE.D.smetOf (I := I) h hsym hpos hsmooth).inner x₀ y i j
      = Work.Diff.STE.DeTurck.pPhiJet (I := I) (M := M)
        (Work.Diff.STE.D.smetOf (I := I) h hsym hpos hsmooth) g₀ x₀ y i j := rfl
  rw [show Work.Diff.STE.D.pPhiJetOf (I := I) (M := M) g₀ h x₀ y i j
      = Work.Diff.STE.DeTurck.pPhiJet (I := I) (M := M)
        (Work.Diff.STE.D.smetOf (I := I) h hsym hpos hsmooth) g₀ x₀ y i j from key]
  rw [Work.Diff.STE.D.psi.pPhiJet_eq_chartDeTurckMat (I := I)
    (Work.Diff.STE.D.smetOf (I := I) h hsym hpos hsmooth) g₀ x₀ hy]
  rw [Work.Diff.STE.DeTurck.chartDeTurckMat_apply]
  rw [Work.Diff.STE.D.chartMatOf_apply, Work.Diff.STE.D.deTurckSec_apply]
  simp only [Work.Diff.GE.cFrame_apply]

/-- **The DeTurck section of a section with smooth chart data has smooth chart data.** -/
lemma chartData_deTurckSec
    (hLC : Submission.Diff.LCSmooth I M)
    (h : Work.Diff.STE.Bil (I := I) (M := M))
    (hsym : ∀ (x : M) (u v : TangentSpace I x), h x u v = h x v u)
    (hpos : ∀ (x : M) (v : TangentSpace I x), v ≠ 0 → 0 < h x v v)
    (hsmooth : Work.Diff.STE.D.ChartData (I := I) (M := M) h) :
    Work.Diff.STE.D.ChartData (I := I) (M := M)
      (Work.Diff.STE.D.deTurckSec (I := I) hLC g₀ h hsym hpos hsmooth) := by
  intro x₀
  have hsm : ContDiffOn ℝ (⊤ : ℕ∞)
      (fun y : E => Work.Diff.STE.D.pPhiJetOf (I := I) (M := M) g₀ h x₀ y)
      (extChartAt I x₀).target :=
    contDiffOn_pi.mpr (fun i => contDiffOn_pi.mpr (fun j =>
      contDiffOn_pPhiJetOf (I := I) (M := M) g₀ h x₀ (hsmooth x₀)
        (fun y hy => det_chartMatOf_of_pos (I := I) (M := M) h hsym hpos x₀ hy) i j))
  refine hsm.congr (fun y hy => ?_)
  funext i j
  exact chartMatOf_deTurckSec_eq_pPhiJetOf (I := I) (M := M) (g₀ := g₀) hLC h hsym hpos hsmooth
    x₀ hy i j

end Helpers

theorem transport_Rres_contDiffOn
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ((⊤ : ENat) : WithTop ENat) M] [T2Space M] [I.Boundaryless]
    {ι₀ : Type*} [Fintype ι₀] {g₀ : Submission.Diff.SMet I M}
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (hLC : Submission.Diff.LCSmooth I M)
    (h : Work.Diff.STE.Bil (I := I) (M := M))
    (hsym : ∀ (x : M) (u v : TangentSpace I x), h x u v = h x v u)
    (hpos : ∀ (x : M) (v : TangentSpace I x), v ≠ 0 → 0 < h x v v)
    (hsmooth : Work.Diff.STE.D.ChartData (I := I) (M := M) h)
    (j : ι₀)
    (A : (Fin (Module.finrank ℝ E) → ℝ) → Fin (Module.finrank ℝ E) →
      Fin (Module.finrank ℝ E) → ℝ)
    (hA : ContDiff ℝ ((⊤ : ENat) : WithTop ENat) A)
    (a b : Fin (Module.finrank ℝ E)) :
    ContDiffOn ℝ ((⊤ : ENat) : WithTop ENat)
      (fun z : Fin (Module.finrank ℝ E) → ℝ =>
        Work.Diff.STE.B3.Rres (I := I) (M := M) D hLC h hsym hpos hsmooth j A z a b)
      {z : Fin (Module.finrank ℝ E) → ℝ |
        ‖z‖ < 2 * D.σ j + 1 ∧
        Work.Diff.STE.B3.yf (I := I) (M := M) D j z ∈ (extChartAt I (D.x₀ j)).target ∧
        (Matrix.of (Work.Diff.STE.B3.Gf (I := I) (M := M) D h j z)).det ≠ 0} := by
  -- the localised component of the DeTurck section is smooth
  have hP : ContDiff ℝ ((⊤ : ENat) : WithTop ENat)
      (fun z : Fin (Module.finrank ℝ E) → ℝ =>
        D.R j (Work.Diff.STE.D.deTurckSec (I := I) hLC g₀ h hsym hpos hsmooth) a b z) :=
    R_contDiff_of_chartData (I := I) (M := M) D
      (Work.Diff.STE.D.deTurckSec (I := I) hLC g₀ h hsym hpos hsmooth)
      (chartData_deTurckSec (I := I) (M := M) (g₀ := g₀) hLC h hsym hpos hsmooth) j a b
  -- the localised component of `h` is smooth
  have hH : ContDiff ℝ ((⊤ : ENat) : WithTop ENat)
      (fun z : Fin (Module.finrank ℝ E) → ℝ => D.R j h a b z) :=
    R_contDiff_of_chartData (I := I) (M := M) D h hsmooth j a b
  -- ... hence so are its second partial derivatives
  have hpd : ∀ p q : Fin (Module.finrank ℝ E), ContDiff ℝ ((⊤ : ENat) : WithTop ENat)
      (fun z : Fin (Module.finrank ℝ E) → ℝ =>
        Work.Diff.STE.pdR p (Work.Diff.STE.pdR q (D.R j h a b)) z) :=
    fun p q => contDiff_pdR_top (Work.Diff.STE.pdR q (D.R j h a b))
      (contDiff_pdR_top (D.R j h a b) hH q) p
  -- the coefficient `A` is smooth
  have hApq : ∀ p q : Fin (Module.finrank ℝ E), ContDiff ℝ ((⊤ : ENat) : WithTop ENat)
      (fun z : Fin (Module.finrank ℝ E) → ℝ => A z p q) := by
    intro p q
    fun_prop
  -- the second-order term is smooth
  have hsum : ContDiff ℝ ((⊤ : ENat) : WithTop ENat)
      (fun z : Fin (Module.finrank ℝ E) → ℝ =>
        ∑ p, ∑ q, A z p q * Work.Diff.STE.pdR p (Work.Diff.STE.pdR q (D.R j h a b)) z) := by
    refine ContDiff.sum (fun p _ => ContDiff.sum (fun q _ => ?_))
    exact (hApq p q).mul (hpd p q)
  have hmain : ContDiff ℝ ((⊤ : ENat) : WithTop ENat)
      (fun z : Fin (Module.finrank ℝ E) → ℝ =>
        Work.Diff.STE.B3.Rres (I := I) (M := M) D hLC h hsym hpos hsmooth j A z a b) := by
    unfold Work.Diff.STE.B3.Rres
    exact hP.sub (by simpa only [B3Data.R] using hsum)
  exact hmain.contDiffOn

end Work.Diff.STE.B3
