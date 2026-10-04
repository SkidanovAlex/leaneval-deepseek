import Mathlib
import Submission.Work.Diff.STE.B3.LowJetDefs
import Submission.Work.Diff.STE.B3.LowJetAux
import Submission.Work.Diff.STE.B3.tmNom_aux
import Submission.Work.Diff.STE.B3.CompSmooth
import Submission.Work.Diff.STE.B3.densGood
import Submission.Work.Diff.STE.Lead.matA_jets
import Submission.Work.Diff.EXT.contMDiffAt_matrix_inv
import Submission.Work.Diff.STE.Lead.Gal.gardJet_holds
import Submission.Work.Diff.STE.deTurck.contDiffOn_pPhi
import Submission.Work.Diff.STE.D.psi.contDiffOn_secChartVal_chart

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Smoothness of the nominal residual on its state domain

`Work.Diff.STE.B3.nresC D j a b` is the complexified nominal residual
(`Work.Diff.STE.B3.LowJetDefs`), a function of the state `p = (z, V, dV)`.  This module proves that
it is smooth on `lowJetDom D j` (flat coordinate in the chart target, frame matrix `Ff` invertible,
`V` invertible).

The nominal residual is an explicit expression (`Work.Diff.STE.B3.body`) in the fixed chart data of
`g₀` (`Jets0`, `wf`, `Ff` and their partial derivatives — all smooth on the chart target) and in the
two nominal matrices `nG z V` (bilinear in `V` with `Finvf` coefficients) and `nDGc z V dV` (linear in
`(V, dV)` with `∂ Finvf` coefficients).  The only non-polynomial ingredient is `Matrix.inv` of the
nominal matrix `nG z V`, which is smooth because
`det (nG z V) = det (Finvf z) ^ 2 · det V ≠ 0` on the domain.  The lower-order term
`pN Abar Lbar Bbar A L = pPhi Abar Lbar Bbar A L 0` is smooth because it is `pPhi` with the second
jet set to `0` (`pN_contDiffOn_gal`, from `Work.Diff.STE.deTurck.contDiffOn_pPhi`).
-/

namespace Work.Diff.STE.Lead.Gal

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology BigOperators Matrix
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ((⊤ : ENat) : WithTop ENat) M] [T2Space M] [I.Boundaryless]
  {ι₀ : Type*} [Fintype ι₀] {g₀ : Submission.Diff.SMet I M}

/-- The state space of the nominal residual. -/
abbrev NarStGal : Type _ :=
  (Fin (Module.finrank ℝ E) → ℝ)
    × (Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → ℝ)
    × (Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → ℝ)

/-- The first partial derivative of a smooth function is smooth. -/
lemma contDiffAt_pdR_gal' {d : ℕ} {φ : (Fin d → ℝ) → ℝ} {z : Fin d → ℝ}
    (hφ : ContDiffAt ℝ ((⊤ : ENat) : WithTop ENat) φ z) (c : Fin d) :
    ContDiffAt ℝ ((⊤ : ENat) : WithTop ENat) (Work.Diff.STE.pdR c φ) z := by
  have hfd : ContDiffAt ℝ ((⊤ : ENat) : WithTop ENat) (fderiv ℝ φ) z :=
    hφ.fderiv_right (m := ((⊤ : ENat) : WithTop ENat)) (by simp)
  have h2 := (((ContinuousLinearMap.apply ℝ ℝ (Pi.single c (1 : ℝ) : Fin d → ℝ))).contDiff)
    |>.contDiffAt.comp z hfd
  show ContDiffAt ℝ ((⊤ : ENat) : WithTop ENat)
    (fun x : Fin d → ℝ => fderiv ℝ φ x (Pi.single c (1 : ℝ))) z
  exact h2

/-- **The lower-order term `pN` of the DeTurck operator is smooth in its matrix arguments.**  It is
`pPhi` with the second jet set to `0`, so this is `contDiffOn_pPhi` composed with the smooth
map `w ↦ (w.1, w.2, 0)`. -/
theorem pN_contDiffOn_gal :
    ContDiffOn ℝ (⊤ : ENat)
      (fun w : (Work.Diff.EXT.MatE (E := E) × Work.Diff.STE.DeTurck.LinMat E ×
            Work.Diff.STE.DeTurck.BilMat E) ×
          (Work.Diff.EXT.MatE (E := E) × Work.Diff.STE.DeTurck.LinMat E) =>
        Work.Diff.STE.DeTurck.pN w.1.1 w.1.2.1 w.1.2.2 w.2.1 w.2.2)
      {w | (Matrix.of w.1.1).det ≠ 0 ∧ (Matrix.of w.2.1).det ≠ 0} := by
  have hΦ := Work.Diff.STE.deTurck.contDiffOn_pPhi (E := E)
  have hg : ContDiffOn ℝ (⊤ : ENat)
      (fun w : (Work.Diff.EXT.MatE (E := E) × Work.Diff.STE.DeTurck.LinMat E ×
            Work.Diff.STE.DeTurck.BilMat E) ×
          (Work.Diff.EXT.MatE (E := E) × Work.Diff.STE.DeTurck.LinMat E) =>
        ((w.1.1, w.1.2.1, w.1.2.2),
          (w.2.1, w.2.2, (0 : Work.Diff.STE.DeTurck.BilMat E))))
      {w | (Matrix.of w.1.1).det ≠ 0 ∧ (Matrix.of w.2.1).det ≠ 0} := by
    fun_prop
  have h := hΦ.comp hg (fun w hw => ⟨hw.1, hw.2⟩)
  exact h.congr (fun w hw => rfl)

/-- **Smoothness of the nominal residual on `lowJetDom`**, complexified form.

The proof collects the `ContDiffAt` facts for every atom of `Work.Diff.STE.B3.body` (the fixed
smooth functions `wf` and `Ff` of the flat coordinate together with their first and second partial
derivatives, the frame inverse `Finvf`, the nominal matrices `nG` and `nDGc`, the polynomial
`nEight`, the matrix inverse, the background jet `Jets0` and the `pN` term) and closes the
expression by the usual closure rules. -/
theorem nresSmooth
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (j : ι₀)
    (a b : Fin (Module.finrank ℝ E)) :
    ContDiffOn ℝ ((⊤ : ENat) : WithTop ENat)
      (Work.Diff.STE.B3.nresC (I := I) (M := M) D j a b)
      (Work.Diff.STE.B3.lowJetDom (I := I) (M := M) D j) := by
  classical
  intro p hp
  obtain ⟨htgt, hdetFf, hdetV⟩ := hp
  -- ## 0. the fixed smooth functions of the flat coordinate
  have hwf : ContDiffAt ℝ ((⊤ : ENat) : WithTop ENat)
      (fun p : NarStGal (E := E) => Work.Diff.STE.B3.wf (I := I) (M := M) D j p.1) p :=
    ((show ContDiff ℝ ((⊤ : ENat) : WithTop ENat)
        (Work.Diff.STE.B3.wf (I := I) (M := M) D j) from
      Work.Diff.STE.Lead.matA_contDiff (I := I) (M := M) D j).contDiffAt).comp p contDiffAt_fst
  have hpdn : ∀ (c : Fin (Module.finrank ℝ E)),
      ContDiffAt ℝ ((⊤ : ENat) : WithTop ENat)
        (fun p : NarStGal (E := E) =>
          Work.Diff.STE.pdR c (Work.Diff.STE.B3.wf (I := I) (M := M) D j) p.1) p :=
    fun c => (contDiffAt_pdR_gal'
      (φ := Work.Diff.STE.B3.wf (I := I) (M := M) D j)
      (show ContDiff ℝ ((⊤ : ENat) : WithTop ENat)
          (Work.Diff.STE.B3.wf (I := I) (M := M) D j) from
        Work.Diff.STE.Lead.matA_contDiff (I := I) (M := M) D j).contDiffAt c).comp p contDiffAt_fst
  have hpd2n : ∀ (c c' : Fin (Module.finrank ℝ E)),
      ContDiffAt ℝ ((⊤ : ENat) : WithTop ENat)
        (fun p : NarStGal (E := E) =>
          Work.Diff.STE.pdR c (Work.Diff.STE.pdR c'
            (Work.Diff.STE.B3.wf (I := I) (M := M) D j)) p.1) p :=
    fun c c' => (contDiffAt_pdR_gal'
      (φ := Work.Diff.STE.pdR c' (Work.Diff.STE.B3.wf (I := I) (M := M) D j))
      (contDiffAt_pdR_gal'
        (φ := Work.Diff.STE.B3.wf (I := I) (M := M) D j)
        (show ContDiff ℝ ((⊤ : ENat) : WithTop ENat)
            (Work.Diff.STE.B3.wf (I := I) (M := M) D j) from
          Work.Diff.STE.Lead.matA_contDiff (I := I) (M := M) D j).contDiffAt c') c).comp p
      contDiffAt_fst
  have hFfa : ∀ (c : Fin (Module.finrank ℝ E)),
      ContDiffAt ℝ ((⊤ : ENat) : WithTop ENat)
        (fun p : NarStGal (E := E) => Work.Diff.STE.B3.Ff (I := I) (M := M) D j p.1 a c) p :=
    fun c => (Work.Diff.STE.B3.Ff_contDiffAt (I := I) (M := M) D j a c htgt).comp p contDiffAt_fst
  have hFfb : ∀ (c : Fin (Module.finrank ℝ E)),
      ContDiffAt ℝ ((⊤ : ENat) : WithTop ENat)
        (fun p : NarStGal (E := E) => Work.Diff.STE.B3.Ff (I := I) (M := M) D j p.1 b c) p :=
    fun c => (Work.Diff.STE.B3.Ff_contDiffAt (I := I) (M := M) D j b c htgt).comp p contDiffAt_fst
  have hpdFf : ∀ (c d d' : Fin (Module.finrank ℝ E)),
      ContDiffAt ℝ ((⊤ : ENat) : WithTop ENat)
        (fun p : NarStGal (E := E) =>
          Work.Diff.STE.pdR c (fun y : Fin (Module.finrank ℝ E) → ℝ =>
            Work.Diff.STE.B3.Ff (I := I) (M := M) D j y d d') p.1) p :=
    fun c d d' => (contDiffAt_pdR_gal'
      (φ := fun y => Work.Diff.STE.B3.Ff (I := I) (M := M) D j y d d')
      (Work.Diff.STE.B3.Ff_contDiffAt (I := I) (M := M) D j d d' htgt) c).comp p contDiffAt_fst
  have hpd2Ff : ∀ (c c' d d' : Fin (Module.finrank ℝ E)),
      ContDiffAt ℝ ((⊤ : ENat) : WithTop ENat)
        (fun p : NarStGal (E := E) =>
          Work.Diff.STE.pdR c (Work.Diff.STE.pdR c'
            (fun y : Fin (Module.finrank ℝ E) → ℝ =>
              Work.Diff.STE.B3.Ff (I := I) (M := M) D j y d d')) p.1) p :=
    fun c c' d d' => (contDiffAt_pdR_gal'
      (φ := Work.Diff.STE.pdR c' (fun y => Work.Diff.STE.B3.Ff (I := I) (M := M) D j y d d'))
      (contDiffAt_pdR_gal'
        (φ := fun y => Work.Diff.STE.B3.Ff (I := I) (M := M) D j y d d')
        (Work.Diff.STE.B3.Ff_contDiffAt (I := I) (M := M) D j d d' htgt) c') c).comp p
      contDiffAt_fst
  -- ## 1. the frame inverse
  have hFin : ∀ (i c : Fin (Module.finrank ℝ E)),
      ContDiffAt ℝ ((⊤ : ENat) : WithTop ENat)
        (fun p : NarStGal (E := E) =>
          Work.Diff.STE.B3.Finvf (I := I) (M := M) D j p.1 i c) p := by
    intro i c
    have h1 : ∀ (i' c' : Fin (Module.finrank ℝ E)),
        ContDiffAt ℝ ((⊤ : ENat) : WithTop ENat)
          (fun y : Fin (Module.finrank ℝ E) → ℝ =>
            (Matrix.of (Work.Diff.STE.B3.Ff (I := I) (M := M) D j y))⁻¹ i' c') p.1 := by
      intro i' c'
      have hX : ∀ r s : Fin (Module.finrank ℝ E), ContDiffAt ℝ ((⊤ : ENat) : WithTop ENat)
          (fun y : Fin (Module.finrank ℝ E) → ℝ =>
            (Matrix.of (Work.Diff.STE.B3.Ff (I := I) (M := M) D j y)) r s) p.1 :=
        fun r s => Work.Diff.STE.B3.Ff_contDiffAt (I := I) (M := M) D j r s htgt
      exact Work.Diff.STE.B3.tmNom_inv_entry_ContDiffAt hX hdetFf i' c'
    exact ((h1 i c).comp p contDiffAt_fst).congr_of_eventuallyEq
      (Filter.EventuallyEq.of_eq (by funext q; rfl))
  have hpdFin : ∀ (c i a' : Fin (Module.finrank ℝ E)),
      ContDiffAt ℝ ((⊤ : ENat) : WithTop ENat)
        (fun p : NarStGal (E := E) =>
          Work.Diff.STE.pdR c (fun y : Fin (Module.finrank ℝ E) → ℝ =>
            Work.Diff.STE.B3.Finvf (I := I) (M := M) D j y i a') p.1) p := by
    intro c i a'
    have hX : ∀ r s : Fin (Module.finrank ℝ E), ContDiffAt ℝ ((⊤ : ENat) : WithTop ENat)
        (fun y : Fin (Module.finrank ℝ E) → ℝ =>
          (Matrix.of (Work.Diff.STE.B3.Ff (I := I) (M := M) D j y)) r s) p.1 :=
      fun r s => Work.Diff.STE.B3.Ff_contDiffAt (I := I) (M := M) D j r s htgt
    have hinv : ContDiffAt ℝ ((⊤ : ENat) : WithTop ENat)
        (fun y : Fin (Module.finrank ℝ E) → ℝ =>
          Work.Diff.STE.B3.Finvf (I := I) (M := M) D j y i a') p.1 :=
      (Work.Diff.STE.B3.tmNom_inv_entry_ContDiffAt hX hdetFf i a').congr_of_eventuallyEq
        (Filter.EventuallyEq.of_eq (by funext q; rfl))
    exact (contDiffAt_pdR_gal' (φ := fun y => Work.Diff.STE.B3.Finvf (I := I) (M := M) D j y i a')
      hinv c).comp p contDiffAt_fst
  -- ## 2. the nominal matrices
  have hnG : ∀ (i k : Fin (Module.finrank ℝ E)),
      ContDiffAt ℝ ((⊤ : ENat) : WithTop ENat)
        (fun p : NarStGal (E := E) =>
          Work.Diff.STE.B3.nG (I := I) (M := M) D j p.1 p.2.1 i k) p := by
    intro i k
    simp only [Work.Diff.STE.B3.nG]
    fun_prop
  have hnDGc : ∀ (c i k : Fin (Module.finrank ℝ E)),
      ContDiffAt ℝ ((⊤ : ENat) : WithTop ENat)
        (fun p : NarStGal (E := E) =>
          Work.Diff.STE.B3.nDGc (I := I) (M := M) D j p.1 p.2.1 p.2.2 c i k) p := by
    intro c i k
    simp only [Work.Diff.STE.B3.nDGc]
    fun_prop
  have hdetFin : (Matrix.of (Work.Diff.STE.B3.Finvf (I := I) (M := M) D j p.1)).det ≠ 0 := by
    have hdFf : IsUnit (Matrix.of (Work.Diff.STE.B3.Ff (I := I) (M := M) D j p.1)).det :=
      isUnit_iff_ne_zero.mpr hdetFf
    have hmul : (Matrix.of (Work.Diff.STE.B3.Finvf (I := I) (M := M) D j p.1)).det
        * (Matrix.of (Work.Diff.STE.B3.Ff (I := I) (M := M) D j p.1)).det = 1 := by
      rw [← Matrix.det_mul, Work.Diff.STE.B3.Finvf_eq_inv, Matrix.nonsing_inv_mul _ hdFf,
        Matrix.det_one]
    intro h0
    rw [h0, zero_mul] at hmul
    exact one_ne_zero hmul.symm
  have hmatN : Matrix.of (Work.Diff.STE.B3.nG (I := I) (M := M) D j p.1 p.2.1)
      = Matrix.of (Work.Diff.STE.B3.Finvf (I := I) (M := M) D j p.1) * Matrix.of p.2.1
        * (Matrix.of (Work.Diff.STE.B3.Finvf (I := I) (M := M) D j p.1))ᵀ := by
    ext i k
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.of_apply, Work.Diff.STE.B3.nG,
      Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
  have hdetN : (Matrix.of (Work.Diff.STE.B3.nG (I := I) (M := M) D j p.1 p.2.1)).det ≠ 0 := by
    rw [hmatN, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose]
    exact mul_ne_zero (mul_ne_zero hdetFin hdetV) hdetFin
  have hinv : ∀ (r s : Fin (Module.finrank ℝ E)),
      ContDiffAt ℝ ((⊤ : ENat) : WithTop ENat)
        (fun p : NarStGal (E := E) =>
          (Matrix.of (Work.Diff.STE.B3.nG (I := I) (M := M) D j p.1 p.2.1))⁻¹ r s) p := by
    intro r s
    have hnGmat : ContDiffAt ℝ ((⊤ : ENat) : WithTop ENat)
        (fun p : NarStGal (E := E) => (fun i k : Fin (Module.finrank ℝ E) =>
            Work.Diff.STE.B3.nG (I := I) (M := M) D j p.1 p.2.1 i k)) p :=
      contDiffAt_pi.mpr (fun i => contDiffAt_pi.mpr (fun k => hnG i k))
    have hout := Work.Diff.EXT.contDiffAt_matrix_inv_pi
      (M := (fun i k : Fin (Module.finrank ℝ E) =>
        Work.Diff.STE.B3.nG (I := I) (M := M) D j p.1 p.2.1 i k)) hdetN
    exact (((contDiffAt_pi.mp (contDiffAt_pi.mp hout r)) s)).comp p hnGmat
  -- ## 3. the linear map `clmOf` and the background jets
  have hclm : ContDiffAt ℝ ((⊤ : ENat) : WithTop ENat)
      (fun p : NarStGal (E := E) => Work.Diff.STE.B3.clmOf (E := E) p.2.2) p := by
    have hsm : ∀ c : Fin (Module.finrank ℝ E),
        ContDiffAt ℝ ((⊤ : ENat) : WithTop ENat)
          (fun p : NarStGal (E := E) =>
            (((Work.Diff.EXT.bB (E := E)).coord c)).toContinuousLinearMap.smulRight (p.2.2 c)) p :=
      fun c => ((((ContinuousLinearMap.smulRightL ℝ E (Work.Diff.EXT.MatE (E := E)))
        (((Work.Diff.EXT.bB (E := E)).coord c)).toContinuousLinearMap).contDiff).contDiffAt).comp p
        (by fun_prop)
    have hsum : ContDiffAt ℝ ((⊤ : ENat) : WithTop ENat)
        (fun p : NarStGal (E := E) =>
          ∑ c : Fin (Module.finrank ℝ E),
            (((Work.Diff.EXT.bB (E := E)).coord c)).toContinuousLinearMap.smulRight (p.2.2 c)) p :=
      ContDiffAt.sum (fun c _ => hsm c)
    refine hsum.congr_of_eventuallyEq (Filter.EventuallyEq.of_eq ?_)
    funext q
    simp only [Work.Diff.STE.B3.clmOf]
  have hJets : ContDiffAt ℝ ((⊤ : ENat) : WithTop ENat)
      (fun p : NarStGal (E := E) => Work.Diff.STE.B3.Jets0 (I := I) (M := M) D j p.1) p := by
    have hchart : ContDiffOn ℝ ((⊤ : ENat) : WithTop ENat)
        (Work.Diff.EXT.chartMatFun (I := I) g₀ (D.x₀ j)) (extChartAt I (D.x₀ j)).target :=
      fun y hy => (Work.Diff.EXT.kz_contDiffAt_chartMatFun (I := I) g₀ (D.x₀ j) hy).contDiffWithinAt
    have hjet := (Work.Diff.STE.D.psi.contDiffOn_chartJetOf (I := I) (M := M) g₀.inner (D.x₀ j)
      hchart).contDiffAt ((isOpen_extChartAt_target (I := I) (D.x₀ j)).mem_nhds htgt)
    have hfl : ContDiffAt ℝ ((⊤ : ENat) : WithTop ENat)
        (fun p : NarStGal (E := E) => Work.Diff.STE.flatToE (I := I) (D.x₀ j) p.1) p :=
      (Work.Diff.STE.contDiff_flatToE (I := I) (x₀ := D.x₀ j)).contDiffAt.comp p contDiffAt_fst
    exact (hjet.comp p hfl).congr_of_eventuallyEq (Filter.EventuallyEq.of_eq rfl)
  -- the background chart matrix is invertible on the chart target
  have hdetJets0 : (Matrix.of (Work.Diff.STE.B3.Jets0 (I := I) (M := M) D j p.1).1).det ≠ 0 := by
    have hdens : 0 < D.dens j p.1 := (Work.Diff.STE.B3.densGood (I := I) (M := M) D j p.1 htgt).1
    have h1 : D.dens j p.1
        = Real.sqrt (Matrix.det (Matrix.of (Work.Diff.STE.B3.Jets0 (I := I) (M := M) D j p.1).1)) :=
      rfl
    rw [h1] at hdens
    exact ne_of_gt (Real.sqrt_pos.mp hdens)
  -- ## 4. the `pN` term
  have hpn : ∀ (i k : Fin (Module.finrank ℝ E)),
      ContDiffAt ℝ ((⊤ : ENat) : WithTop ENat)
        (fun p : NarStGal (E := E) =>
          Work.Diff.STE.DeTurck.pN (Work.Diff.STE.B3.Jets0 (I := I) (M := M) D j p.1).1
            (Work.Diff.STE.B3.Jets0 (I := I) (M := M) D j p.1).2.1
            (Work.Diff.STE.B3.Jets0 (I := I) (M := M) D j p.1).2.2
            (Matrix.of (Work.Diff.STE.B3.nG (I := I) (M := M) D j p.1 p.2.1))
            (Work.Diff.STE.B3.clmOf (E := E)
              (Work.Diff.STE.B3.nDGc (I := I) (M := M) D j p.1 p.2.1 p.2.2)) i k) p := by
    intro i k
    set Φ : NarStGal (E := E) → (Work.Diff.EXT.MatE (E := E) ×
          Work.Diff.STE.DeTurck.LinMat E × Work.Diff.STE.DeTurck.BilMat E) ×
        (Work.Diff.EXT.MatE (E := E) × Work.Diff.STE.DeTurck.LinMat E) :=
      fun p => (((Work.Diff.STE.B3.Jets0 (I := I) (M := M) D j p.1).1,
          (Work.Diff.STE.B3.Jets0 (I := I) (M := M) D j p.1).2.1,
          (Work.Diff.STE.B3.Jets0 (I := I) (M := M) D j p.1).2.2),
        (Matrix.of (Work.Diff.STE.B3.nG (I := I) (M := M) D j p.1 p.2.1),
          Work.Diff.STE.B3.clmOf (E := E)
            (Work.Diff.STE.B3.nDGc (I := I) (M := M) D j p.1 p.2.1 p.2.2))) with hΦdef
    have hclm_univ : ContDiff ℝ ((⊤ : ENat) : WithTop ENat)
        (fun dG : Fin (Module.finrank ℝ E) → Work.Diff.EXT.MatE (E := E) =>
          Work.Diff.STE.B3.clmOf (E := E) dG) := by
      rw [show (fun dG : Fin (Module.finrank ℝ E) → Work.Diff.EXT.MatE (E := E) =>
            Work.Diff.STE.B3.clmOf (E := E) dG)
          = (fun dG : Fin (Module.finrank ℝ E) → Work.Diff.EXT.MatE (E := E) =>
            ∑ c : Fin (Module.finrank ℝ E),
              (((Work.Diff.EXT.bB (E := E)).coord c)).toContinuousLinearMap.smulRight (dG c))
          from rfl]
      refine ContDiff.sum (fun c _ => ?_)
      fun_prop
    have hstate : ContDiffAt ℝ ((⊤ : ENat) : WithTop ENat) Φ p := by
      rw [hΦdef]
      refine ContDiffAt.prodMk hJets ?_
      refine ContDiffAt.prodMk ?_ ?_
      · exact contDiffAt_pi.mpr (fun i' => contDiffAt_pi.mpr (fun k' => hnG i' k'))
      · refine hclm_univ.contDiffAt.comp p ?_
        exact contDiffAt_pi.mpr (fun c => contDiffAt_pi.mpr (fun i' =>
          contDiffAt_pi.mpr (fun k' => hnDGc c i' k')))
    have hcont1 : Continuous (fun w : (Work.Diff.EXT.MatE (E := E) ×
          Work.Diff.STE.DeTurck.LinMat E × Work.Diff.STE.DeTurck.BilMat E) ×
        (Work.Diff.EXT.MatE (E := E) × Work.Diff.STE.DeTurck.LinMat E) =>
        (Matrix.of w.1.1).det) := by fun_prop
    have hcont2 : Continuous (fun w : (Work.Diff.EXT.MatE (E := E) ×
          Work.Diff.STE.DeTurck.LinMat E × Work.Diff.STE.DeTurck.BilMat E) ×
        (Work.Diff.EXT.MatE (E := E) × Work.Diff.STE.DeTurck.LinMat E) =>
        (Matrix.of w.2.1).det) := by fun_prop
    have hopen : IsOpen {w : (Work.Diff.EXT.MatE (E := E) ×
          Work.Diff.STE.DeTurck.LinMat E × Work.Diff.STE.DeTurck.BilMat E) ×
        (Work.Diff.EXT.MatE (E := E) × Work.Diff.STE.DeTurck.LinMat E) |
        (Matrix.of w.1.1).det ≠ 0 ∧ (Matrix.of w.2.1).det ≠ 0} :=
      (isOpen_ne.preimage hcont1).inter (isOpen_ne.preimage hcont2)
    have hmem : Φ p ∈ {w : (Work.Diff.EXT.MatE (E := E) × Work.Diff.STE.DeTurck.LinMat E ×
          Work.Diff.STE.DeTurck.BilMat E) ×
        (Work.Diff.EXT.MatE (E := E) × Work.Diff.STE.DeTurck.LinMat E) |
        (Matrix.of w.1.1).det ≠ 0 ∧ (Matrix.of w.2.1).det ≠ 0} := ⟨hdetJets0, hdetN⟩
    have hpN : ContDiffAt ℝ ((⊤ : ENat) : WithTop ENat)
        (fun w : (Work.Diff.EXT.MatE (E := E) × Work.Diff.STE.DeTurck.LinMat E ×
              Work.Diff.STE.DeTurck.BilMat E) ×
            (Work.Diff.EXT.MatE (E := E) × Work.Diff.STE.DeTurck.LinMat E) =>
          Work.Diff.STE.DeTurck.pN w.1.1 w.1.2.1 w.1.2.2 w.2.1 w.2.2) (Φ p) :=
      (pN_contDiffOn_gal (E := E) (Φ p) hmem).contDiffAt (hopen.mem_nhds hmem)
    have hcomp := hpN.comp p hstate
    have hcomp' : ContDiffAt ℝ ((⊤ : ENat) : WithTop ENat)
        (fun p : NarStGal (E := E) =>
          Work.Diff.STE.DeTurck.pN (Work.Diff.STE.B3.Jets0 (I := I) (M := M) D j p.1).1
            (Work.Diff.STE.B3.Jets0 (I := I) (M := M) D j p.1).2.1
            (Work.Diff.STE.B3.Jets0 (I := I) (M := M) D j p.1).2.2
            (Matrix.of (Work.Diff.STE.B3.nG (I := I) (M := M) D j p.1 p.2.1))
            (Work.Diff.STE.B3.clmOf (E := E)
              (Work.Diff.STE.B3.nDGc (I := I) (M := M) D j p.1 p.2.1 p.2.2))) p :=
      hcomp.congr_of_eventuallyEq (Filter.EventuallyEq.of_eq (by funext q; rfl))
    exact contDiffAt_pi.mp (contDiffAt_pi.mp hcomp' i) k
  -- ## 5. the polynomial `nEight`
  have hEight : ∀ (p' q' : Fin (Module.finrank ℝ E)),
      ContDiffAt ℝ ((⊤ : ENat) : WithTop ENat)
        (fun p : NarStGal (E := E) =>
          Work.Diff.STE.B3.nEight (I := I) (M := M) D j p.1
            (Work.Diff.STE.B3.nG (I := I) (M := M) D j p.1 p.2.1)
            (Work.Diff.STE.B3.nDGc (I := I) (M := M) D j p.1 p.2.1 p.2.2) p' q' a b) p := by
    intro p' q'
    simp only [Work.Diff.STE.B3.nEight]
    fun_prop
  -- ## 6. assembly of the body
  have hV : ∀ (r s : Fin (Module.finrank ℝ E)),
      ContDiffAt ℝ ((⊤ : ENat) : WithTop ENat)
        (fun p : NarStGal (E := E) => p.2.1 r s) p := by
    intro r s
    fun_prop
  have hdV : ∀ (r s t : Fin (Module.finrank ℝ E)),
      ContDiffAt ℝ ((⊤ : ENat) : WithTop ENat)
        (fun p : NarStGal (E := E) => p.2.2 r s t) p := by
    intro r s t
    fun_prop
  have hbody : ContDiffAt ℝ ((⊤ : ENat) : WithTop ENat)
      (fun p : NarStGal (E := E) =>
        Work.Diff.STE.B3.body (I := I) (M := M) D j p.1
          (Work.Diff.STE.B3.nG (I := I) (M := M) D j p.1 p.2.1)
          (Work.Diff.STE.B3.nDGc (I := I) (M := M) D j p.1 p.2.1 p.2.2) p.2.1 p.2.2 a b) p := by
    simp only [Work.Diff.STE.B3.body]
    refine ContDiffAt.sub (ContDiffAt.sub ?_ ?_) ?_
    · exact ContDiffAt.mul hwf (ContDiffAt.sum (fun i _ => ContDiffAt.sum (fun k _ =>
        ContDiffAt.mul (hpn i k) (ContDiffAt.mul (hFfa i) (hFfb k)))))
    · exact ContDiffAt.mul hwf (ContDiffAt.sum (fun r _ => ContDiffAt.sum (fun s _ =>
        ContDiffAt.mul (hinv r s) (hEight r s))))
    · exact ContDiffAt.sum (fun r _ => ContDiffAt.sum (fun s _ =>
        ContDiffAt.mul (hinv r s) (ContDiffAt.add
          (ContDiffAt.mul (ContDiffAt.mul contDiffAt_const (hpdn r)) (hdV s a b))
          (ContDiffAt.mul (hV a b) (hpd2n r s)))))
  -- ## 7. complexification
  have hC : ContDiffAt ℝ ((⊤ : ENat) : WithTop ENat)
      (Work.Diff.STE.B3.nresC (I := I) (M := M) D j a b) p := by
    refine (Complex.ofRealCLM.contDiff.contDiffAt.comp p hbody).congr_of_eventuallyEq
      (Filter.EventuallyEq.of_eq ?_)
    funext q
    simp only [Function.comp_apply, Complex.ofRealCLM_apply, Work.Diff.STE.B3.nresC,
      Work.Diff.STE.B3.nres]
  exact hC.contDiffWithinAt

end

end Work.Diff.STE.Lead.Gal
