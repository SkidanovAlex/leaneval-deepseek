import Mathlib
import Submission.Work.Diff.STE.B3.LowJetDefs
import Submission.Work.Diff.STE.B3.tmNom_aux
import Submission.Work.Diff.STE.B3.secOp_weight_sum_eq
import Submission.Work.Diff.STE.B3.densGood
import Submission.Work.Diff.STE.deTurck.contDiffOn_pPhi
import Submission.Work.Diff.STE.B3.tmPsi_state_contDiffOn

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Smoothness of the nominal residual

`Work.Diff.STE.B3.nres` (see `Submission/Work/Diff/STE/B3/LowJetDefs.lean`) is the residual of the
transport identity written as an explicit function of the *state* `(z, V, W)`: the flat coordinate
`z`, the orthonormal-frame chart matrix `V` and its first jet `W`:

`nres D j z V W a b = body D j z (nG z V) (nDGc z V W) V W a b`,

where `nG` is the nominal coordinate-frame chart matrix (`Gf = Finvf · Mf · Finvfᵀ`) and `nDGc` its
nominal first jet.  This module proves that its complexified version `nresC` is `C^∞` on
`lowJetDom D j`, the set where the flat coordinate lies in the chart target and the matrices
`Ff z` and `V` are invertible.

The proof is the exact analogue of `Work.Diff.STE.B3.tmPsi_state_contDiffOn` for the residual `tmPsi`
(the difference is that `tmPsi` uses the clamped inverse `tmGKi` for the principal part, while the
nominal residual uses the honest inverse of `nG z V`, which is smooth precisely on `lowJetDom`).
The generic calculus helpers (`contDiffAt_pdR`, `contDiffAt_clm_comp`, `contDiffAt_state_V/W`,
`contDiffAt_wf_state`, `contDiffAt_Ff_state`, `contDiffAt_invEntry_of_entries`, …) are reused from
that module; the atoms specific to `nG`, `nDGc` and `nEight` are proved here.
-/

namespace Work.Diff.STE.B3

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.unusedSectionVars false

open scoped Manifold ContDiff Bundle Topology BigOperators Matrix
open Bundle ContDiff Set

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ((⊤ : ENat) : WithTop ENat) M] [T2Space M] [I.Boundaryless]
  {ι₀ : Type*} [Fintype ι₀] {g₀ : Submission.Diff.SMet I M}

local notation "Idx" => Fin (Module.finrank ℝ E)

/-! ## 1. The nominal coordinate-frame chart matrix `nG` and its first jet `nDGc` -/

/-- The nominal coordinate-frame chart matrix `nG z V`, as a function of the state, is `C^∞`
wherever the frame matrix `Ff z` is invertible and the flat coordinate lies in the chart target. -/
private lemma nresC_nG_contDiffAt (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (j : ι₀)
    {w : St E}
    (hz : Work.Diff.STE.flatToE (I := I) (D.x₀ j) w.1 ∈ (extChartAt I (D.x₀ j)).target)
    (hdet : (Matrix.of (Ff (I := I) (M := M) D j w.1)).det ≠ 0) (i k : Idx) :
    ContDiffAt ℝ ∞ (fun w' : St E => nG (I := I) (M := M) D j w'.1 w'.2.1 i k) w := by
  have hF : ∀ i a : Idx,
      ContDiffAt ℝ ∞ (fun w' : St E => Finvf (I := I) (M := M) D j w'.1 i a) w :=
    fun i a => contDiffAt_Finvf_state (I := I) (M := M) D j hz hdet i a
  have hV : ∀ a b : Idx, ContDiffAt ℝ ∞ (fun w' : St E => w'.2.1 a b) w :=
    fun a b => contDiffAt_state_V a b
  simp only [nG]
  refine ContDiffAt.sum (fun a _ => ContDiffAt.sum (fun b _ => ?_))
  exact ((hF i a).mul (hV a b)).mul (hF k b)

/-- The nominal first jet of the coordinate-frame chart matrix, as a function of the state. -/
private lemma nresC_nDGc_contDiffAt (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (j : ι₀)
    {w : St E}
    (hz : Work.Diff.STE.flatToE (I := I) (D.x₀ j) w.1 ∈ (extChartAt I (D.x₀ j)).target)
    (hdet : (Matrix.of (Ff (I := I) (M := M) D j w.1)).det ≠ 0) (c i k : Idx) :
    ContDiffAt ℝ ∞
      (fun w' : St E => nDGc (I := I) (M := M) D j w'.1 w'.2.1 w'.2.2 c i k) w := by
  have hF : ∀ i a : Idx,
      ContDiffAt ℝ ∞ (fun w' : St E => Finvf (I := I) (M := M) D j w'.1 i a) w :=
    fun i a => contDiffAt_Finvf_state (I := I) (M := M) D j hz hdet i a
  have hV : ∀ a b : Idx, ContDiffAt ℝ ∞ (fun w' : St E => w'.2.1 a b) w :=
    fun a b => contDiffAt_state_V a b
  have hW : ∀ a b r : Idx, ContDiffAt ℝ ∞ (fun w' : St E => w'.2.2 a b r) w :=
    fun a b r => contDiffAt_state_W a b r
  have hDF : ∀ c i a : Idx, ContDiffAt ℝ ∞
      (fun w' : St E => Work.Diff.STE.pdR c
        (fun y => Finvf (I := I) (M := M) D j y i a) w'.1) w :=
    fun c i a => contDiffAt_pdR_state (contDiffAt_Finvf_z (I := I) (M := M) D j hz hdet i a) c
  simp only [nDGc]
  refine ContDiffAt.sum (fun a _ => ContDiffAt.sum (fun b _ => ?_))
  refine ContDiffAt.add (ContDiffAt.add ?_ ?_) ?_
  · exact ((hDF c i a).mul (hV a b)).mul (hF k b)
  · exact ((hF i a).mul (hW c a b)).mul (hF k b)
  · exact ((hF i a).mul (hV a b)).mul (hDF c k b)

/-- The nominal first jet of the coordinate-frame chart matrix, in the continuous-linear-map form
in which the jet-level DeTurck operator `pN` expects it. -/
private lemma nresC_clmOf_contDiffAt (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (j : ι₀)
    {w : St E}
    (hz : Work.Diff.STE.flatToE (I := I) (D.x₀ j) w.1 ∈ (extChartAt I (D.x₀ j)).target)
    (hdet : (Matrix.of (Ff (I := I) (M := M) D j w.1)).det ≠ 0) :
    ContDiffAt ℝ ∞
      (fun w' : St E => clmOf (E := E) (nDGc (I := I) (M := M) D j w'.1 w'.2.1 w'.2.2)) w := by
  have hD : ∀ c i k : Idx, ContDiffAt ℝ ∞
      (fun w' : St E => nDGc (I := I) (M := M) D j w'.1 w'.2.1 w'.2.2 c i k) w :=
    fun c i k => nresC_nDGc_contDiffAt (I := I) (M := M) D j hz hdet c i k
  simp only [clmOf]
  refine ContDiffAt.sum (fun c _ => ?_)
  refine contDiffAt_clm_comp
    (L := ContinuousLinearMap.smulRightL ℝ E (Work.Diff.EXT.MatE (E := E))
      ((Work.Diff.EXT.bB (E := E)).coord c).toContinuousLinearMap)
    (f := fun w' : St E => (fun i k : Idx =>
      nDGc (I := I) (M := M) D j w'.1 w'.2.1 w'.2.2 c i k)) ?_
  rw [contDiffAt_pi]
  intro i
  rw [contDiffAt_pi]
  intro k
  exact hD c i k

/-! ## 2. The inverse of the nominal coordinate-frame chart matrix -/

/-- `Matrix.of (nG z V)` is the matrix product `Finvf z · V · Finvf zᵀ`. -/
private lemma nresC_matrix_of_nG_eq (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (j : ι₀)
    (z : Idx → ℝ) (V : Idx → Idx → ℝ) :
    Matrix.of (nG (I := I) (M := M) D j z V)
      = Matrix.of (Finvf (I := I) (M := M) D j z) * Matrix.of V
        * (Matrix.of (Finvf (I := I) (M := M) D j z))ᵀ := by
  ext i k
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.of_apply, nG]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [Finset.sum_mul]

/-- The determinant of the nominal coordinate-frame chart matrix is nonvanishing whenever `Ff z`
and `V` are invertible. -/
private lemma nresC_det_nG_ne_zero (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (j : ι₀)
    {z : Idx → ℝ} {V : Idx → Idx → ℝ}
    (hdet : (Matrix.of (Ff (I := I) (M := M) D j z)).det ≠ 0)
    (hV : (Matrix.of V).det ≠ 0) :
    (Matrix.of (nG (I := I) (M := M) D j z V)).det ≠ 0 := by
  rw [nresC_matrix_of_nG_eq (I := I) (M := M) D j z V, Matrix.det_mul, Matrix.det_mul,
    Matrix.det_transpose]
  have h1 : (Matrix.of (Finvf (I := I) (M := M) D j z)).det ≠ 0 := by
    rw [Finvf_eq_inv (I := I) (M := M) D j z, Matrix.det_nonsing_inv,
      congrFun Ring.inverse_eq_inv']
    exact inv_ne_zero hdet
  exact mul_ne_zero (mul_ne_zero h1 hV) h1

/-- The entries of the inverse of the nominal coordinate-frame chart matrix are `C^∞` on
`lowJetDom`. -/
private lemma nresC_invEntry_contDiffAt (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (j : ι₀)
    {w : St E}
    (hz : Work.Diff.STE.flatToE (I := I) (D.x₀ j) w.1 ∈ (extChartAt I (D.x₀ j)).target)
    (hdet : (Matrix.of (Ff (I := I) (M := M) D j w.1)).det ≠ 0)
    (hV : (Matrix.of w.2.1).det ≠ 0) (r s : Idx) :
    ContDiffAt ℝ ∞
      (fun w' : St E => ((Matrix.of (nG (I := I) (M := M) D j w'.1 w'.2.1))⁻¹) r s) w :=
  contDiffAt_invEntry_of_entries
    (X := fun w' : St E => Matrix.of (nG (I := I) (M := M) D j w'.1 w'.2.1))
    (fun i k => by
      simpa only [Matrix.of_apply] using nresC_nG_contDiffAt (I := I) (M := M) D j hz hdet i k)
    (nresC_det_nG_ne_zero (I := I) (M := M) D j hdet hV) r s

/-! ## 3. The eight-term correction `nEight` -/

/-- The eight-term correction `nEight`, evaluated at the nominal chart matrix `nG z V` and its
nominal first jet `nDGc z V W`, is `C^∞` in the state. -/
private lemma nresC_nEight_contDiffAt (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (j : ι₀)
    {w : St E}
    (hz : Work.Diff.STE.flatToE (I := I) (D.x₀ j) w.1 ∈ (extChartAt I (D.x₀ j)).target)
    (hdet : (Matrix.of (Ff (I := I) (M := M) D j w.1)).det ≠ 0) (c d a b : Idx) :
    ContDiffAt ℝ ∞
      (fun w' : St E => nEight (I := I) (M := M) D j w'.1
        (nG (I := I) (M := M) D j w'.1 w'.2.1)
        (nDGc (I := I) (M := M) D j w'.1 w'.2.1 w'.2.2) c d a b) w := by
  have hF : ∀ a i : Idx, ContDiffAt ℝ ∞
      (fun w' : St E => Ff (I := I) (M := M) D j w'.1 a i) w :=
    fun a i => contDiffAt_Ff_state (I := I) (M := M) D j hz a i
  have hDF : ∀ c a i : Idx, ContDiffAt ℝ ∞
      (fun w' : St E => Work.Diff.STE.pdR c
        (fun y => Ff (I := I) (M := M) D j y a i) w'.1) w :=
    fun c a i => contDiffAt_pdR_Ff_state (I := I) (M := M) D j hz a i c
  have hDDF : ∀ c d a i : Idx, ContDiffAt ℝ ∞
      (fun w' : St E => Work.Diff.STE.pdR c (Work.Diff.STE.pdR d
        (fun y => Ff (I := I) (M := M) D j y a i)) w'.1) w :=
    fun c d a i => contDiffAt_pdR_pdR_Ff_state (I := I) (M := M) D j hz a i c d
  have hG : ∀ i k : Idx, ContDiffAt ℝ ∞
      (fun w' : St E => nG (I := I) (M := M) D j w'.1 w'.2.1 i k) w :=
    fun i k => nresC_nG_contDiffAt (I := I) (M := M) D j hz hdet i k
  have hDG : ∀ c i k : Idx, ContDiffAt ℝ ∞
      (fun w' : St E => nDGc (I := I) (M := M) D j w'.1 w'.2.1 w'.2.2 c i k) w :=
    fun c i k => nresC_nDGc_contDiffAt (I := I) (M := M) D j hz hdet c i k
  simp only [nEight]
  refine ContDiffAt.sum (fun i _ => ContDiffAt.sum (fun k _ => ?_))
  refine ContDiffAt.add (ContDiffAt.add (ContDiffAt.add (ContDiffAt.add (ContDiffAt.add
    (ContDiffAt.add (ContDiffAt.add ?_ ?_) ?_) ?_) ?_) ?_) ?_) ?_
  · exact ((hDDF c d a i).mul (hG i k)).mul (hF b k)
  · exact ((hDF c a i).mul (hDG d i k)).mul (hF b k)
  · exact ((hDF c a i).mul (hG i k)).mul (hDF d b k)
  · exact ((hDF d a i).mul (hDG c i k)).mul (hF b k)
  · exact ((hDF d a i).mul (hG i k)).mul (hDF c b k)
  · exact ((hF a i).mul (hDG c i k)).mul (hDF d b k)
  · exact ((hF a i).mul (hDG d i k)).mul (hDF c b k)
  · exact ((hF a i).mul (hG i k)).mul (hDDF c d b k)

/-! ## 4. The `pN`-term -/

/-- The pair of `2`-jets on which the jet-level DeTurck operator `pPhi` is evaluated in the
nominal residual, as a function of the state. -/
private def nresC_pNMap (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (j : ι₀)
    (w : St E) : Work.Diff.STE.deTurck.JetPair E :=
  (((Jets0 (I := I) (M := M) D j w.1).1,
    (Jets0 (I := I) (M := M) D j w.1).2.1,
    (Jets0 (I := I) (M := M) D j w.1).2.2),
   (nG (I := I) (M := M) D j w.1 w.2.1,
    clmOf (E := E) (nDGc (I := I) (M := M) D j w.1 w.2.1 w.2.2), 0))

private lemma nresC_pNMap_contDiffAt (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (j : ι₀)
    {w : St E}
    (hz : Work.Diff.STE.flatToE (I := I) (D.x₀ j) w.1 ∈ (extChartAt I (D.x₀ j)).target)
    (hdet : (Matrix.of (Ff (I := I) (M := M) D j w.1)).det ≠ 0) :
    ContDiffAt ℝ ∞ (fun w' : St E => nresC_pNMap (I := I) (M := M) D j w') w := by
  have hjet : ContDiffAt ℝ ∞
      (fun w' : St E => Jets0 (I := I) (M := M) D j w'.1) w := by
    simpa only [Jets0, yf] using
      contDiffAt_gJet_state (I := I) (M := M) (g₀ := g₀) D j hz
  have hG : ∀ i k : Idx, ContDiffAt ℝ ∞
      (fun w' : St E => nG (I := I) (M := M) D j w'.1 w'.2.1 i k) w :=
    fun i k => nresC_nG_contDiffAt (I := I) (M := M) D j hz hdet i k
  have hA : ContDiffAt ℝ ∞
      (fun w' : St E => (fun i k : Idx => nG (I := I) (M := M) D j w'.1 w'.2.1 i k)) w := by
    rw [contDiffAt_pi]
    intro i
    rw [contDiffAt_pi]
    intro k
    exact hG i k
  have hL := nresC_clmOf_contDiffAt (I := I) (M := M) D j hz hdet
  have h2 : ContDiffAt ℝ ∞ (fun w' : St E =>
      ((fun i k : Idx => nG (I := I) (M := M) D j w'.1 w'.2.1 i k),
        clmOf (E := E) (nDGc (I := I) (M := M) D j w'.1 w'.2.1 w'.2.2),
        (0 : E →L[ℝ] E →L[ℝ] Work.Diff.EXT.MatE (E := E)))) w :=
    ContDiffAt.prodMk hA (ContDiffAt.prodMk hL contDiffAt_const)
  have hmain : ContDiffAt ℝ ∞ (fun w' : St E =>
      (((Jets0 (I := I) (M := M) D j w'.1).1,
        (Jets0 (I := I) (M := M) D j w'.1).2.1,
        (Jets0 (I := I) (M := M) D j w'.1).2.2),
       ((fun i k : Idx => nG (I := I) (M := M) D j w'.1 w'.2.1 i k),
        clmOf (E := E) (nDGc (I := I) (M := M) D j w'.1 w'.2.1 w'.2.2),
        (0 : E →L[ℝ] E →L[ℝ] Work.Diff.EXT.MatE (E := E))))) w :=
    ContDiffAt.prodMk
      (ContDiffAt.prodMk hjet.fst (ContDiffAt.prodMk hjet.snd.fst hjet.snd.snd)) h2
  exact hmain

private lemma nresC_pNMap_mapsTo (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (j : ι₀) :
    MapsTo (fun w' : St E => nresC_pNMap (I := I) (M := M) D j w')
      (Sset (I := I) (M := M) D j) (Work.Diff.STE.deTurck.pPhiDom E) := by
  intro y hy
  obtain ⟨hy1, hy2, hy3⟩ := hy
  refine ⟨?_, ?_⟩
  · have hpd : (Matrix.of (Work.Diff.EXT.gmat (I := I) g₀ (D.x₀ j)
        ((extChartAt I (D.x₀ j)).symm (yf (I := I) (M := M) D j y.1)))).PosDef :=
      Work.Diff.STE.deTurck.posDef_gmat (I := I) g₀ (D.x₀ j)
        (Work.Diff.STE.D.psi.symm_target_mem_chart_source (I := I) hy1)
    have hne : (Matrix.of (Work.Diff.EXT.gmat (I := I) g₀ (D.x₀ j)
        ((extChartAt I (D.x₀ j)).symm (yf (I := I) (M := M) D j y.1)))).det ≠ 0 :=
      ne_of_gt hpd.det_pos
    simpa only [nresC_pNMap, Jets0, yf, Work.Diff.STE.D.psi.chartJetOf_fst_inner] using hne
  · have h := nresC_det_nG_ne_zero (I := I) (M := M) D j hy2 hy3
    simpa only [nresC_pNMap] using h

/-- The `pN`-term of the nominal residual is `C^∞` in the state on `lowJetDom`. -/
private lemma nresC_pN_contDiffWithinAt (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀)
    (j : ι₀) (i k : Idx) {w : St E}
    (hz : Work.Diff.STE.flatToE (I := I) (D.x₀ j) w.1 ∈ (extChartAt I (D.x₀ j)).target)
    (hdet : (Matrix.of (Ff (I := I) (M := M) D j w.1)).det ≠ 0)
    (hV : (Matrix.of w.2.1).det ≠ 0) :
    ContDiffWithinAt ℝ ∞
      (fun w' : St E => Work.Diff.STE.DeTurck.pN
        (Jets0 (I := I) (M := M) D j w'.1).1
        (Jets0 (I := I) (M := M) D j w'.1).2.1
        (Jets0 (I := I) (M := M) D j w'.1).2.2
        (Matrix.of (nG (I := I) (M := M) D j w'.1 w'.2.1))
        (clmOf (E := E) (nDGc (I := I) (M := M) D j w'.1 w'.2.1 w'.2.2)) i k)
      (Sset (I := I) (M := M) D j) w := by
  have hG : ContDiffWithinAt ℝ ∞ (fun w' : St E => nresC_pNMap (I := I) (M := M) D j w')
      (Sset (I := I) (M := M) D j) w :=
    (nresC_pNMap_contDiffAt (I := I) (M := M) D j hz hdet).contDiffWithinAt
  have hmem := nresC_pNMap_mapsTo (I := I) (M := M) (g₀ := g₀) D j
  have hwS : w ∈ Sset (I := I) (M := M) D j := ⟨hz, hdet, hV⟩
  have hcomp := ContDiffWithinAt.comp (x := w)
    ((Work.Diff.STE.deTurck.contDiffOn_pPhi (E := E)).contDiffWithinAt (hmem hwS)) hG hmem
  have h1 : ContDiffWithinAt ℝ ∞
      (fun w' : St E => Work.Diff.STE.DeTurck.pN
        (Jets0 (I := I) (M := M) D j w'.1).1
        (Jets0 (I := I) (M := M) D j w'.1).2.1
        (Jets0 (I := I) (M := M) D j w'.1).2.2
        (Matrix.of (nG (I := I) (M := M) D j w'.1 w'.2.1))
        (clmOf (E := E) (nDGc (I := I) (M := M) D j w'.1 w'.2.1 w'.2.2)))
      (Sset (I := I) (M := M) D j) w :=
    hcomp.congr (fun y hy => by unfold Work.Diff.STE.DeTurck.pN nresC_pNMap; rfl)
      (by unfold Work.Diff.STE.DeTurck.pN nresC_pNMap; rfl)
  exact contDiffWithinAt_clm_comp
    ((ContinuousLinearMap.proj k : (Idx → ℝ) →L[ℝ] ℝ).comp
      (ContinuousLinearMap.proj i : Work.Diff.EXT.MatE (E := E) →L[ℝ] (Idx → ℝ))) h1

/-! ## 5. Assembly -/

private lemma nresC_body_contDiffWithinAt (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀)
    (j : ι₀) (a b : Idx) {w : St E}
    (hz : Work.Diff.STE.flatToE (I := I) (D.x₀ j) w.1 ∈ (extChartAt I (D.x₀ j)).target)
    (hdet : (Matrix.of (Ff (I := I) (M := M) D j w.1)).det ≠ 0)
    (hV : (Matrix.of w.2.1).det ≠ 0) :
    ContDiffWithinAt ℝ ∞
      (fun w' : St E => body (I := I) (M := M) D j w'.1
        (nG (I := I) (M := M) D j w'.1 w'.2.1)
        (nDGc (I := I) (M := M) D j w'.1 w'.2.1 w'.2.2) w'.2.1 w'.2.2 a b)
      (Sset (I := I) (M := M) D j) w := by
  have hT1 : ContDiffWithinAt ℝ ∞ (fun w' : St E =>
      wf (I := I) (M := M) D j w'.1
        * (∑ i : Idx, ∑ k : Idx, Work.Diff.STE.DeTurck.pN
            (Jets0 (I := I) (M := M) D j w'.1).1
            (Jets0 (I := I) (M := M) D j w'.1).2.1
            (Jets0 (I := I) (M := M) D j w'.1).2.2
            (Matrix.of (nG (I := I) (M := M) D j w'.1 w'.2.1))
            (clmOf (E := E) (nDGc (I := I) (M := M) D j w'.1 w'.2.1 w'.2.2)) i k
              * (Ff (I := I) (M := M) D j w'.1 a i
                * Ff (I := I) (M := M) D j w'.1 b k)))
      (Sset (I := I) (M := M) D j) w := by
    refine ContDiffWithinAt.mul (contDiffAt_wf_state (I := I) (M := M) D j hz).contDiffWithinAt ?_
    refine ContDiffWithinAt.sum (fun i _ => ContDiffWithinAt.sum (fun k _ => ?_))
    refine ContDiffWithinAt.mul (nresC_pN_contDiffWithinAt (I := I) (M := M) D j i k hz hdet hV) ?_
    exact ((contDiffAt_Ff_state (I := I) (M := M) D j hz a i).contDiffWithinAt).mul
      ((contDiffAt_Ff_state (I := I) (M := M) D j hz b k).contDiffWithinAt)
  have hT2 : ContDiffWithinAt ℝ ∞ (fun w' : St E =>
      wf (I := I) (M := M) D j w'.1
        * (∑ p : Idx, ∑ q : Idx,
            ((Matrix.of (nG (I := I) (M := M) D j w'.1 w'.2.1))⁻¹) p q
              * nEight (I := I) (M := M) D j w'.1
                  (nG (I := I) (M := M) D j w'.1 w'.2.1)
                  (nDGc (I := I) (M := M) D j w'.1 w'.2.1 w'.2.2) p q a b))
      (Sset (I := I) (M := M) D j) w := by
    refine ContDiffWithinAt.mul (contDiffAt_wf_state (I := I) (M := M) D j hz).contDiffWithinAt ?_
    refine ContDiffWithinAt.sum (fun p _ => ContDiffWithinAt.sum (fun q _ => ?_))
    exact ((nresC_invEntry_contDiffAt (I := I) (M := M) D j hz hdet hV p q).contDiffWithinAt).mul
      ((nresC_nEight_contDiffAt (I := I) (M := M) D j hz hdet p q a b).contDiffWithinAt)
  have hT3 : ContDiffWithinAt ℝ ∞ (fun w' : St E =>
      ∑ p : Idx, ∑ q : Idx,
        ((Matrix.of (nG (I := I) (M := M) D j w'.1 w'.2.1))⁻¹) p q
          * (2 * Work.Diff.STE.pdR p (wf (I := I) (M := M) D j) w'.1 * w'.2.2 q a b
            + w'.2.1 a b
              * Work.Diff.STE.pdR p (Work.Diff.STE.pdR q
                (wf (I := I) (M := M) D j)) w'.1))
      (Sset (I := I) (M := M) D j) w := by
    refine ContDiffWithinAt.sum (fun p _ => ContDiffWithinAt.sum (fun q _ => ?_))
    refine ContDiffWithinAt.mul
      ((nresC_invEntry_contDiffAt (I := I) (M := M) D j hz hdet hV p q).contDiffWithinAt) ?_
    refine ContDiffWithinAt.add (ContDiffWithinAt.mul (ContDiffWithinAt.mul ?_ ?_) ?_)
      (ContDiffWithinAt.mul ?_ ?_)
    · exact contDiffWithinAt_const
    · exact (contDiffAt_pdR_wf_state (I := I) (M := M) D j hz p).contDiffWithinAt
    · exact (contDiffAt_state_W q a b).contDiffWithinAt
    · exact (contDiffAt_state_V a b).contDiffWithinAt
    · exact (contDiffAt_pdR_pdR_wf_state (I := I) (M := M) D j hz p q).contDiffWithinAt
  refine (((hT1.sub hT2).sub hT3)).congr (fun y hy => ?_) ?_
  · simp only [body]
  · simp only [body]

/-- **The nominal residual is `C^∞` in the state** on `lowJetDom`. -/
private lemma nres_contDiffWithinAt_state (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀)
    (j : ι₀) (a b : Idx) {w : St E}
    (hz : Work.Diff.STE.flatToE (I := I) (D.x₀ j) w.1 ∈ (extChartAt I (D.x₀ j)).target)
    (hdet : (Matrix.of (Ff (I := I) (M := M) D j w.1)).det ≠ 0)
    (hV : (Matrix.of w.2.1).det ≠ 0) :
    ContDiffWithinAt ℝ ∞
      (fun w' : St E => nres (I := I) (M := M) D j w'.1 w'.2.1 w'.2.2 a b)
      (Sset (I := I) (M := M) D j) w :=
  (nresC_body_contDiffWithinAt (I := I) (M := M) D j a b hz hdet hV).congr
    (fun y hy => rfl) rfl

end

theorem nresC_contDiffOn
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ((⊤ : ENat) : WithTop ENat) M] [T2Space M] [I.Boundaryless]
    {ι₀ : Type*} [Fintype ι₀] {g₀ : Submission.Diff.SMet I M}
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (j : ι₀)
    (a b : Fin (Module.finrank ℝ E)) :
    ContDiffOn ℝ (⊤ : ℕ∞) (Work.Diff.STE.B3.nresC (I := I) (M := M) D j a b)
      (Work.Diff.STE.B3.lowJetDom (I := I) (M := M) D j) := by
  intro w hw
  obtain ⟨hz, hdet, hV⟩ := hw
  show ContDiffWithinAt ℝ ∞
    (fun w' : (Fin (Module.finrank ℝ E) → ℝ) ×
        (Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → ℝ) ×
        (Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) →
          Fin (Module.finrank ℝ E) → ℝ) =>
      ((nres (I := I) (M := M) D j w'.1 w'.2.1 w'.2.2 a b : ℝ) : ℂ))
    (Work.Diff.STE.B3.lowJetDom (I := I) (M := M) D j) w
  have hreal : ContDiffWithinAt ℝ ∞
      (fun w' : (Fin (Module.finrank ℝ E) → ℝ) ×
          (Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → ℝ) ×
          (Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) →
            Fin (Module.finrank ℝ E) → ℝ) =>
        nres (I := I) (M := M) D j w'.1 w'.2.1 w'.2.2 a b)
      (Work.Diff.STE.B3.lowJetDom (I := I) (M := M) D j) w :=
    nres_contDiffWithinAt_state (I := I) (M := M) D j a b hz hdet hV
  have hcomp := ContDiffWithinAt.comp (x := w) (t := Set.univ)
    (g := (Complex.ofRealCLM : ℝ → ℂ)) (s := Work.Diff.STE.B3.lowJetDom (I := I) (M := M) D j)
    (f := fun w' : (Fin (Module.finrank ℝ E) → ℝ) ×
        (Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → ℝ) ×
        (Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) →
          Fin (Module.finrank ℝ E) → ℝ) =>
      nres (I := I) (M := M) D j w'.1 w'.2.1 w'.2.2 a b)
    ((Complex.ofRealCLM.contDiff : ContDiff ℝ ∞ (Complex.ofRealCLM : ℝ → ℂ)).contDiffAt.contDiffWithinAt)
    hreal (fun _ _ => Set.mem_univ _)
  refine hcomp.congr (fun y hy => ?_) ?_
  · simp only [Function.comp_apply, Complex.ofRealCLM_apply]
  · simp only [Function.comp_apply, Complex.ofRealCLM_apply]

end Work.Diff.STE.B3
