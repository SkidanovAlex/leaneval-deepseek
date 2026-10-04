/-
# The residual as a function of the orthonormal-frame chart matrix and its first jet

This module proves that the residual `Work.Diff.STE.B3.residualLow` of the transport identity is the
composite of the **nominal residual** `Work.Diff.STE.B3.nres` with the `g₀`-orthonormal-frame chart
matrix of the section and its first jet:

`residualLow D h j z a b = nres D j z (Mf D h j z) (dMf D h j z) a b`   for `‖z‖ ≤ 2 D.σ j`.

The two ingredients are the frame-change identities of `B3/tmNom_aux.lean` and
`B3/transport_Mf_second.lean` / `B3/transport_jet_data.lean`:

* `Gf = Finvf · Mf · Finvfᵀ` (`tmNom_Gf_eq_dual_of_target`, hence `Gf = nG (Mf)`),
* `∂_c Gf = nDGc (Mf) (∂Mf) c` (`dGf_eq_nDGc`),
* `(chartJetOf h x₀ (yf j z)).2.1 = clmOf (dGf)`, i.e. the spatial `1`-jet of the coordinate-frame
  chart matrix, in the continuous-linear-map form expected by `Work.Diff.STE.DeTurck.pN`.
-/
import Mathlib
import Submission.Work.Diff.STE.B3.LowJetDefs
import Submission.Work.Diff.STE.B3.tmNom_aux
import Submission.Work.Diff.STE.B3.transport_jet_data
import Submission.Work.Diff.STE.B3.secOp_weight_sum_eq
import Submission.Work.Diff.STE.B3.dGf_eq_nDGc

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology BigOperators Matrix
open Bundle ContDiff Set VectorField CovariantDerivative Metric

namespace Work.Diff.STE.B3

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.unusedSectionVars false

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ((⊤ : ENat) : WithTop ENat) M] [T2Space M] [I.Boundaryless]
  {ι₀ : Type*} [Fintype ι₀] {g₀ : Submission.Diff.SMet I M}

noncomputable section

local notation "Idx" => Fin (Module.finrank ℝ E)

/-- **The spatial `1`-jet of the coordinate-frame chart matrix** of a section, in the
continuous-linear-map form in which `Work.Diff.STE.DeTurck.pN` is evaluated: the second component
of `chartJetOf` is `clmOf` applied to the family of coordinate partial derivatives of `Gf`. -/
lemma clmOf_dGf_eq (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀)
    (h : Work.Diff.STE.Bil (I := I) (M := M))
    (hsmooth : Work.Diff.STE.D.ChartData (I := I) (M := M) h) (j : ι₀)
    {z : Idx → ℝ} (hz : ‖z‖ ≤ 2 * D.σ j) :
    clmOf (E := E) (dGf (I := I) (M := M) D h j z)
      = (Jetsh (I := I) (M := M) D h j z).2.1 := by
  have hjet := (transport_jet_data (I := I) (M := M) D h hsmooth j hz).2.1
  have hstep : clmOf (E := E) (dGf (I := I) (M := M) D h j z)
      = ∑ c : Idx, (((Work.Diff.EXT.bB (E := E)).coord c).toContinuousLinearMap).smulRight
          ((Jetsh (I := I) (M := M) D h j z).2.1 (Work.Diff.EXT.bB (E := E) c)) := by
    simp only [clmOf]
    refine Finset.sum_congr rfl (fun c _ => ?_)
    congr 1
    funext i k
    simp only [dGf]
    exact (hjet c i k).symm
  rw [hstep, tmNom_clm_eq_sum_coord_smulRight
    (L := (Jetsh (I := I) (M := M) D h j z).2.1)]

/-- **`Gf = nG (Mf)`**: the coordinate-frame chart matrix of the section is the conjugate of the
orthonormal-frame chart matrix by the (fixed) inverse frame matrix. -/
lemma Gf_eq_nG (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀)
    (h : Work.Diff.STE.Bil (I := I) (M := M)) (j : ι₀)
    {z : Idx → ℝ} (hz : ‖z‖ ≤ 2 * D.σ j) (i k : Idx) :
    Gf (I := I) (M := M) D h j z i k
      = nG (I := I) (M := M) D j z (Mf (I := I) (M := M) D h j z) i k :=
  tmNom_Gf_eq_dual_of_target (I := I) (M := M) D h j (D.htarget j z hz)
    (det_Ff_ne_zero (I := I) (M := M) D j hz) i k

/-- **The residual as the body evaluated at the chart matrices**: `residualLow` is the body
`Work.Diff.STE.B3.body` of the nominal residual, evaluated at the coordinate-frame chart matrix of
the section, its first jet, the orthonormal-frame chart matrix and its first jet. -/
lemma residualLow_eq_body (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀)
    (h : Work.Diff.STE.Bil (I := I) (M := M))
    (hsmooth : Work.Diff.STE.D.ChartData (I := I) (M := M) h) (j : ι₀)
    {z : Idx → ℝ} (hz : ‖z‖ ≤ 2 * D.σ j) (a b : Idx) :
    residualLow (I := I) (M := M) D h j z a b
      = body (I := I) (M := M) D j z (Gf (I := I) (M := M) D h j z)
          (dGf (I := I) (M := M) D h j z) (Mf (I := I) (M := M) D h j z)
          (dMf (I := I) (M := M) D h j z) a b := by
  have hclm := clmOf_dGf_eq (I := I) (M := M) D h hsmooth j hz
  simp only [residualLow, body, nEight, eightTerm, dGf, dMf]
  rw [← hclm]
  rfl

/-- **The residual as the nominal residual evaluated at the orthonormal-frame chart matrix and its
first jet.** -/
theorem residualLow_eq_nres (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀)
    (h : Work.Diff.STE.Bil (I := I) (M := M))
    (hsmooth : Work.Diff.STE.D.ChartData (I := I) (M := M) h) (j : ι₀)
    {z : Idx → ℝ} (hz : ‖z‖ ≤ 2 * D.σ j) (a b : Idx) :
    residualLow (I := I) (M := M) D h j z a b
      = nres (I := I) (M := M) D j z (Mf (I := I) (M := M) D h j z)
          (dMf (I := I) (M := M) D h j z) a b := by
  rw [residualLow_eq_body (I := I) (M := M) D h hsmooth j hz a b]
  have hG : Gf (I := I) (M := M) D h j z = nG (I := I) (M := M) D j z
      (Mf (I := I) (M := M) D h j z) :=
    funext fun i => funext fun k => Gf_eq_nG (I := I) (M := M) D h j hz i k
  have hdG : dGf (I := I) (M := M) D h j z
      = nDGc (I := I) (M := M) D j z (Mf (I := I) (M := M) D h j z)
          (dMf (I := I) (M := M) D h j z) :=
    funext fun c => funext fun i => funext fun k =>
      dGf_eq_nDGc (I := I) (M := M) D h hsmooth j hz c i k
  rw [hG, hdG]
  rfl

/-! ## The target-based form of the identity

For the jet bound the identity has to hold on an **open neighbourhood** of the point `z` of the
closed `2σ j`-ball (the composition estimate is applied on a neighbourhood).  The natural open
condition is membership of the flat coordinate in the chart *target* together with
`det (Ff z) ≠ 0` (`tmNom_Gf_eq_dual_of_target`); on the closed ball both hold, and they hold on a
whole neighbourhood of any point of the ball.  The lemmas of this section are therefore stated with
that open hypothesis. -/

/-- Component extraction for the first Fréchet derivative of a `Pi`-valued map. -/
private lemma fderiv_proj_apply {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
    {ι : Type*} [Fintype ι] {F' : Type*} [NormedAddCommGroup F'] [NormedSpace ℝ F']
    (A : E' → (ι → F')) {y : E'} (hA : DifferentiableAt ℝ A y) (i : ι) (v : E') :
    fderiv ℝ (fun x : E' => A x i) y v = (fderiv ℝ A y v) i := by
  have h := (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ι => F') i).hasFDerivAt.comp y
    hA.hasFDerivAt
  have h' : (fun x : E' => A x i)
      = ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ι => F') i) ∘ A) := rfl
  rw [h', h.fderiv]
  rfl

/-- The components of a differentiable `Pi`-valued map are differentiable. -/
private lemma differentiableAt_proj {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
    {ι : Type*} [Fintype ι] {F' : Type*} [NormedAddCommGroup F'] [NormedSpace ℝ F']
    (A : E' → (ι → F')) {y : E'} (hA : DifferentiableAt ℝ A y) (i : ι) :
    DifferentiableAt ℝ (fun x : E' => A x i) y :=
  (((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ι => F') i).hasFDerivAt).comp y
    hA.hasFDerivAt).differentiableAt

/-- Component extraction for the first Fréchet derivative of a matrix-valued map. -/
private lemma fderiv_entry_aux {n : ℕ} (A : E → (Fin n → Fin n → ℝ)) {y : E}
    (hA : DifferentiableAt ℝ A y) (i k : Fin n) (v : E) :
    fderiv ℝ (fun x : E => A x i k) y v = (fderiv ℝ A y v) i k := by
  have h1 := fderiv_proj_apply A hA i v
  have h2 := fderiv_proj_apply (fun x : E => A x i) (differentiableAt_proj A hA i) k v
  rw [h2, h1]

/-- **The spatial `1`-jet of the coordinate-frame chart matrix in flat coordinates** (on the chart
target): `(chartJetOf h x₀ (yf j z)).2.1 (bB c) i k = pdR c (Gf · i k) z`.  This is the target-based
form of the corresponding conjunct of `Work.Diff.STE.B3.transport_jet_data`. -/
lemma jet_data_snd_of_target (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀)
    (h : Work.Diff.STE.Bil (I := I) (M := M))
    (hsmooth : Work.Diff.STE.D.ChartData (I := I) (M := M) h) (j : ι₀)
    {z : Idx → ℝ} (htgt : Work.Diff.STE.flatToE (I := I) (D.x₀ j) z
      ∈ (extChartAt I (D.x₀ j)).target)
    (c i k : Idx) :
    (Jetsh (I := I) (M := M) D h j z).2.1 (Work.Diff.EXT.bB (E := E) c) i k
      = Work.Diff.STE.pdR c (fun y => Gf (I := I) (M := M) D h j y i k) z := by
  have hA : ContDiffAt ℝ (⊤ : ℕ∞)
      (fun y : E => Work.Diff.STE.D.chartMatOf (I := I) (M := M) h (D.x₀ j) y)
      (Work.Diff.STE.B3.yf (I := I) (M := M) D j z) :=
    (hsmooth (D.x₀ j)).contDiffAt
      ((isOpen_extChartAt_target (I := I) (D.x₀ j)).mem_nhds htgt)
  have hA2 : ContDiffAt ℝ 2
      (fun y : E => Work.Diff.STE.D.chartMatOf (I := I) (M := M) h (D.x₀ j) y)
      (Work.Diff.STE.B3.yf (I := I) (M := M) D j z) := hA.of_le (by norm_num)
  have hdA : DifferentiableAt ℝ
      (fun y : E => Work.Diff.STE.D.chartMatOf (I := I) (M := M) h (D.x₀ j) y)
      (Work.Diff.STE.B3.yf (I := I) (M := M) D j z) := hA2.differentiableAt (by norm_num)
  have hF : ContDiffAt ℝ 2
      (fun x : E => Work.Diff.STE.D.chartMatOf (I := I) (M := M) h (D.x₀ j) x i k)
      (Work.Diff.STE.Lead.flatAffine (E := E)
        ((Module.finBasis ℝ E).equivFun ((extChartAt I (D.x₀ j)) (D.x₀ j))) z) :=
    contDiffAt_pi.mp (contDiffAt_pi.mp hA2 i) k
  show (fderiv ℝ
      (fun y : E => Work.Diff.STE.D.chartMatOf (I := I) (M := M) h (D.x₀ j) y)
      (Work.Diff.STE.B3.yf (I := I) (M := M) D j z) (Work.Diff.EXT.bB (E := E) c)) i k = _
  rw [← fderiv_entry_aux
    (fun y : E => Work.Diff.STE.D.chartMatOf (I := I) (M := M) h (D.x₀ j) y) hdA i k
    (Work.Diff.EXT.bB (E := E) c)]
  change fderiv ℝ
      (fun x : E => Work.Diff.STE.D.chartMatOf (I := I) (M := M) h (D.x₀ j) x i k)
      (Work.Diff.STE.Lead.flatAffine (E := E)
        ((Module.finBasis ℝ E).equivFun ((extChartAt I (D.x₀ j)) (D.x₀ j))) z)
      (Work.Diff.EXT.bB (E := E) c)
    = Work.Diff.STE.pdR c (fun w =>
        (fun x : E => Work.Diff.STE.D.chartMatOf (I := I) (M := M) h (D.x₀ j) x i k)
          (Work.Diff.STE.Lead.flatAffine (E := E)
            ((Module.finBasis ℝ E).equivFun ((extChartAt I (D.x₀ j)) (D.x₀ j))) w)) z
  rw [Work.Diff.STE.Lead.fderiv_flatAffine_pdR (E := E)
    ((Module.finBasis ℝ E).equivFun ((extChartAt I (D.x₀ j)) (D.x₀ j))) hF c]

/-- **The spatial `1`-jet of `Gf` in the continuous-linear-map form expected by
`Work.Diff.STE.DeTurck.pN`**, on the chart target. -/
lemma clmOf_dGf_eq_of_target (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀)
    (h : Work.Diff.STE.Bil (I := I) (M := M))
    (hsmooth : Work.Diff.STE.D.ChartData (I := I) (M := M) h) (j : ι₀)
    {z : Idx → ℝ} (htgt : Work.Diff.STE.flatToE (I := I) (D.x₀ j) z
      ∈ (extChartAt I (D.x₀ j)).target) :
    clmOf (E := E) (dGf (I := I) (M := M) D h j z)
      = (Jetsh (I := I) (M := M) D h j z).2.1 := by
  have hstep : clmOf (E := E) (dGf (I := I) (M := M) D h j z)
      = ∑ c : Idx, (((Work.Diff.EXT.bB (E := E)).coord c).toContinuousLinearMap).smulRight
          ((Jetsh (I := I) (M := M) D h j z).2.1 (Work.Diff.EXT.bB (E := E) c)) := by
    simp only [clmOf]
    refine Finset.sum_congr rfl (fun c _ => ?_)
    congr 1
    funext i k
    simp only [dGf]
    exact (jet_data_snd_of_target (I := I) (M := M) D h hsmooth j htgt c i k).symm
  rw [hstep, tmNom_clm_eq_sum_coord_smulRight
    (L := (Jetsh (I := I) (M := M) D h j z).2.1)]

/-- **`Gf = nG (Mf)` on the chart target** (with the frame matrix invertible). -/
lemma Gf_eq_nG_of_target (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀)
    (h : Work.Diff.STE.Bil (I := I) (M := M)) (j : ι₀)
    {z : Idx → ℝ} (htgt : Work.Diff.STE.flatToE (I := I) (D.x₀ j) z
      ∈ (extChartAt I (D.x₀ j)).target)
    (hdet : (Matrix.of (Ff (I := I) (M := M) D j z)).det ≠ 0) (i k : Idx) :
    Gf (I := I) (M := M) D h j z i k
      = nG (I := I) (M := M) D j z (Mf (I := I) (M := M) D h j z) i k :=
  tmNom_Gf_eq_dual_of_target (I := I) (M := M) D h j htgt hdet i k

/-- **`dGf = nDGc (Mf, dMf)` on the chart target**: the first jet of the coordinate-frame chart
matrix, computed by the product rule from the frame-change identity. -/
lemma dGf_eq_nDGc_of_target (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀)
    (h : Work.Diff.STE.Bil (I := I) (M := M))
    (hsmooth : Work.Diff.STE.D.ChartData (I := I) (M := M) h) (j : ι₀)
    {z : Idx → ℝ} (htgt : Work.Diff.STE.flatToE (I := I) (D.x₀ j) z
      ∈ (extChartAt I (D.x₀ j)).target)
    (hdet : (Matrix.of (Ff (I := I) (M := M) D j z)).det ≠ 0) (c i k : Idx) :
    dGf (I := I) (M := M) D h j z c i k
      = nDGc (I := I) (M := M) D j z (Mf (I := I) (M := M) D h j z)
          (dMf (I := I) (M := M) D h j z) c i k := by
  -- the frame-change identity holds on a whole neighbourhood of `z`
  have hdet_ev : ∀ᶠ y in nhds z, (Matrix.of (Ff (I := I) (M := M) D j y)).det ≠ 0 :=
    (tmNom_det_ContDiffAt (X := fun y : Idx → ℝ => Matrix.of (Ff (I := I) (M := M) D j y))
      (fun p q => Ff_contDiffAt (I := I) (M := M) D j p q htgt)).continuousAt.eventually_ne hdet
  have hev : (fun y => Gf (I := I) (M := M) D h j y i k)
      =ᶠ[nhds z] (fun y => ∑ a, ∑ b,
        Finvf (I := I) (M := M) D j y i a * Mf (I := I) (M := M) D h j y a b
          * Finvf (I := I) (M := M) D j y k b) := by
    filter_upwards [tmNom_eventually_mem_target (I := I) (M := M) D j htgt, hdet_ev]
      with y hy hdy
    exact tmNom_Gf_eq_dual_of_target (I := I) (M := M) D h j hy hdy i k
  -- smoothness of the three factor families
  have hFfsm : ∀ p q : Idx, ContDiffAt ℝ (⊤ : ℕ∞)
      (fun y : Idx → ℝ => Matrix.of (Ff (I := I) (M := M) D j y) p q) z :=
    fun p q => Ff_contDiffAt (I := I) (M := M) D j p q htgt
  have hFin : ∀ a b : Idx, ContDiffAt ℝ 2
      (fun y : Idx → ℝ => Finvf (I := I) (M := M) D j y a b) z := by
    intro a b
    exact (tmNom_inv_entry_ContDiffAt (X := fun y : Idx → ℝ =>
        Matrix.of (Ff (I := I) (M := M) D j y)) hFfsm hdet a b).of_le (by norm_num)
  have hMf2 : ∀ a b : Idx, ContDiffAt ℝ 2
      (fun y : Idx → ℝ => Mf (I := I) (M := M) D h j y a b) z := by
    intro a b
    have hsum : ContDiffAt ℝ (⊤ : ℕ∞) (fun y : Idx → ℝ =>
        ∑ p, ∑ q, Ff (I := I) (M := M) D j y a p * Gf (I := I) (M := M) D h j y p q
          * Ff (I := I) (M := M) D j y b q) z := by
      refine ContDiffAt.sum (fun p _ => ContDiffAt.sum (fun q _ => ?_))
      exact ((Ff_contDiffAt (I := I) (M := M) D j a p htgt).mul
        (Gf_contDiffAt (I := I) (M := M) D h hsmooth j p q htgt)).mul
        (Ff_contDiffAt (I := I) (M := M) D j b q htgt)
    refine (hsum.of_le (by norm_num)).congr_of_eventuallyEq ?_
    filter_upwards [tmNom_eventually_mem_target (I := I) (M := M) D j htgt] with y hy
    exact Mf_eq_of_target (I := I) (M := M) D h j a b hy
  rw [dGf, pdR_congr hev c]
  -- differentiate the finite sum
  have hsum1 : ∀ a : Idx, ContDiffAt ℝ 2
      (fun y : Idx → ℝ => ∑ b, Finvf (I := I) (M := M) D j y i a
        * Mf (I := I) (M := M) D h j y a b * Finvf (I := I) (M := M) D j y k b) z := by
    intro a
    refine ContDiffAt.sum (fun b _ => ContDiffAt.mul (ContDiffAt.mul ?_ ?_) ?_)
    · exact hFin i a
    · exact hMf2 a b
    · exact hFin k b
  rw [pdR_fun_sum_at c (fun a => (hsum1 a).differentiableAt (by norm_num))]
  rw [Finset.sum_congr rfl (fun a _ => pdR_fun_sum_at c (fun b =>
    (ContDiffAt.mul (ContDiffAt.mul (hFin i a) (hMf2 a b)) (hFin k b)).differentiableAt
      (by norm_num)))]
  rw [nDGc]
  refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => ?_))
  rw [pdR_mul_at c ((ContDiffAt.mul (hFin i a) (hMf2 a b)).differentiableAt (by norm_num))
      ((hFin k b).differentiableAt (by norm_num)),
    pdR_mul_at c ((hFin i a).differentiableAt (by norm_num))
      ((hMf2 a b).differentiableAt (by norm_num))]
  simp only [dMf]
  ring

/-- **The residual as the body evaluated at the chart matrices** (on the chart target). -/
lemma residualLow_eq_body_of_target (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀)
    (h : Work.Diff.STE.Bil (I := I) (M := M))
    (hsmooth : Work.Diff.STE.D.ChartData (I := I) (M := M) h) (j : ι₀)
    {z : Idx → ℝ} (htgt : Work.Diff.STE.flatToE (I := I) (D.x₀ j) z
      ∈ (extChartAt I (D.x₀ j)).target) (a b : Idx) :
    residualLow (I := I) (M := M) D h j z a b
      = body (I := I) (M := M) D j z (Gf (I := I) (M := M) D h j z)
          (dGf (I := I) (M := M) D h j z) (Mf (I := I) (M := M) D h j z)
          (dMf (I := I) (M := M) D h j z) a b := by
  have hclm := clmOf_dGf_eq_of_target (I := I) (M := M) D h hsmooth j htgt
  simp only [residualLow, body, nEight, eightTerm, dGf, dMf]
  rw [← hclm]
  rfl

/-- **The residual as the nominal residual evaluated at the orthonormal-frame chart matrix and its
first jet** (on the chart target). -/
theorem residualLow_eq_nres_of_target (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀)
    (h : Work.Diff.STE.Bil (I := I) (M := M))
    (hsmooth : Work.Diff.STE.D.ChartData (I := I) (M := M) h) (j : ι₀)
    {z : Idx → ℝ} (htgt : Work.Diff.STE.flatToE (I := I) (D.x₀ j) z
      ∈ (extChartAt I (D.x₀ j)).target)
    (hdet : (Matrix.of (Ff (I := I) (M := M) D j z)).det ≠ 0) (a b : Idx) :
    residualLow (I := I) (M := M) D h j z a b
      = nres (I := I) (M := M) D j z (Mf (I := I) (M := M) D h j z)
          (dMf (I := I) (M := M) D h j z) a b := by
  rw [residualLow_eq_body_of_target (I := I) (M := M) D h hsmooth j htgt a b]
  have hG : Gf (I := I) (M := M) D h j z = nG (I := I) (M := M) D j z
      (Mf (I := I) (M := M) D h j z) :=
    funext fun i => funext fun k => Gf_eq_nG_of_target (I := I) (M := M) D h j htgt hdet i k
  have hdG : dGf (I := I) (M := M) D h j z
      = nDGc (I := I) (M := M) D j z (Mf (I := I) (M := M) D h j z)
          (dMf (I := I) (M := M) D h j z) :=
    funext fun c => funext fun i => funext fun k =>
      dGf_eq_nDGc_of_target (I := I) (M := M) D h hsmooth j htgt hdet c i k
  rw [hG, hdG]
  rfl

/-! ## Smoothness of the state map on the chart target -/

/-- **The orthonormal-frame chart matrix is smooth on the chart target**: it is the conjugate of
the (smooth) coordinate-frame chart matrix by the (smooth) frame matrix. -/
lemma Mf_contDiffAt_of_target (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀)
    (h : Work.Diff.STE.Bil (I := I) (M := M))
    (hsmooth : Work.Diff.STE.D.ChartData (I := I) (M := M) h) (j : ι₀)
    (af bf : Idx) {z : Idx → ℝ}
    (htgt : Work.Diff.STE.flatToE (I := I) (D.x₀ j) z ∈ (extChartAt I (D.x₀ j)).target) :
    ContDiffAt ℝ (⊤ : ℕ∞) (fun w => Mf (I := I) (M := M) D h j w af bf) z := by
  have hsum : ContDiffAt ℝ (⊤ : ℕ∞) (fun y : Idx → ℝ =>
      ∑ p, ∑ q, Ff (I := I) (M := M) D j y af p * Gf (I := I) (M := M) D h j y p q
        * Ff (I := I) (M := M) D j y bf q) z := by
    refine ContDiffAt.sum (fun p _ => ContDiffAt.sum (fun q _ => ?_))
    exact ((Ff_contDiffAt (I := I) (M := M) D j af p htgt).mul
      (Gf_contDiffAt (I := I) (M := M) D h hsmooth j p q htgt)).mul
      (Ff_contDiffAt (I := I) (M := M) D j bf q htgt)
  refine hsum.congr_of_eventuallyEq ?_
  filter_upwards [tmNom_eventually_mem_target (I := I) (M := M) D j htgt] with y hy
  exact Mf_eq_of_target (I := I) (M := M) D h j af bf hy

/-- **The orthonormal-frame chart matrix is smooth on the chart target**, as a `Pi`-valued map. -/
lemma Mf_pi_contDiffAt_of_target (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀)
    (h : Work.Diff.STE.Bil (I := I) (M := M))
    (hsmooth : Work.Diff.STE.D.ChartData (I := I) (M := M) h) (j : ι₀)
    {z : Idx → ℝ}
    (htgt : Work.Diff.STE.flatToE (I := I) (D.x₀ j) z ∈ (extChartAt I (D.x₀ j)).target) :
    ContDiffAt ℝ (⊤ : ℕ∞) (fun w : Idx → ℝ => Mf (I := I) (M := M) D h j w) z :=
  contDiffAt_pi.mpr (fun af => contDiffAt_pi.mpr (fun bf =>
    Mf_contDiffAt_of_target (I := I) (M := M) D h hsmooth j af bf htgt))

/-- **The first jet of the orthonormal-frame chart matrix is smooth on the chart target.** -/
lemma dMf_contDiffAt_of_target (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀)
    (h : Work.Diff.STE.Bil (I := I) (M := M))
    (hsmooth : Work.Diff.STE.D.ChartData (I := I) (M := M) h) (j : ι₀)
    (c af bf : Idx) {z : Idx → ℝ}
    (htgt : Work.Diff.STE.flatToE (I := I) (D.x₀ j) z ∈ (extChartAt I (D.x₀ j)).target) :
    ContDiffAt ℝ (⊤ : ℕ∞) (fun w => dMf (I := I) (M := M) D h j w c af bf) z := by
  have h1 := Mf_contDiffAt_of_target (I := I) (M := M) D h hsmooth j af bf htgt
  have h2 : ContDiffAt ℝ (⊤ : ℕ∞)
      (fun w => fderiv ℝ (fun y : Idx → ℝ => Mf (I := I) (M := M) D h j y af bf) w) z :=
    h1.fderiv_right (by simp)
  have h3 := h2.clm_apply (contDiffAt_const (c := (Pi.single c (1 : ℝ) : Idx → ℝ)))
  refine h3.congr_of_eventuallyEq (Filter.EventuallyEq.of_eq ?_)
  funext w
  rfl

/-- **The state map of the jet bound is smooth on the chart target.** -/
lemma state_contDiffAt_of_target (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀)
    (h : Work.Diff.STE.Bil (I := I) (M := M))
    (hsmooth : Work.Diff.STE.D.ChartData (I := I) (M := M) h) (j : ι₀)
    {z : Idx → ℝ}
    (htgt : Work.Diff.STE.flatToE (I := I) (D.x₀ j) z ∈ (extChartAt I (D.x₀ j)).target) :
    ContDiffAt ℝ (⊤ : ℕ∞)
      (fun y : Idx → ℝ => (y, Mf (I := I) (M := M) D h j y,
        dMf (I := I) (M := M) D h j y)) z := by
  refine ContDiffAt.prodMk contDiffAt_id ?_
  refine ContDiffAt.prodMk (Mf_pi_contDiffAt_of_target (I := I) (M := M) D h hsmooth j htgt) ?_
  refine contDiffAt_pi.mpr (fun c => contDiffAt_pi.mpr (fun af => contDiffAt_pi.mpr (fun bf =>
    dMf_contDiffAt_of_target (I := I) (M := M) D h hsmooth j c af bf htgt)))

/-- **The state domain of the jet bound is open.** -/
lemma isOpen_lowJetDom (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (j : ι₀) :
    IsOpen (lowJetDom (I := I) (M := M) D j) := by
  rw [isOpen_iff_mem_nhds]
  intro p hp
  obtain ⟨hp1, hp2, hp3⟩ := hp
  have h1 : ∀ᶠ q in nhds p,
      Work.Diff.STE.flatToE (I := I) (D.x₀ j) q.1 ∈ (extChartAt I (D.x₀ j)).target :=
    ((isOpen_extChartAt_target (I := I) (D.x₀ j)).preimage
      ((Work.Diff.STE.contDiff_flatToE (I := I) (D.x₀ j)).continuous.comp continuous_fst)
      ).mem_nhds hp1
  have h2 : ∀ᶠ q in nhds p, (Matrix.of (Ff (I := I) (M := M) D j q.1)).det ≠ 0 :=
    ((tmNom_det_ContDiffAt (X := fun w : Idx → ℝ => Matrix.of (Ff (I := I) (M := M) D j w))
      (fun r s => Ff_contDiffAt (I := I) (M := M) D j r s hp1)).continuousAt.comp
        continuousAt_fst).eventually_ne hp2
  have h3 : ∀ᶠ q in nhds p, (Matrix.of (q.2.1)).det ≠ 0 := by
    have hc : Continuous fun q : (Idx → ℝ) × (Idx → Idx → ℝ) × (Idx → Idx → Idx → ℝ) =>
        (Matrix.of (q.2.1)).det := by fun_prop
    exact hc.continuousAt.eventually_ne hp3
  filter_upwards [h1, h2, h3] with q hq1 hq2 hq3
  exact ⟨hq1, hq2, hq3⟩

end

end Work.Diff.STE.B3
