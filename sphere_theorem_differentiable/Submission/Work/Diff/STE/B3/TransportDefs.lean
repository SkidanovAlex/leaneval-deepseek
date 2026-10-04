/-
# Transport of the DeTurck operator to the B3 components: definitions

This module fixes the vocabulary used by `Work.Diff.STE.B3.transport_deTurck_general`: the flat
coordinate `yf`, the `g₀`-orthonormal frame chart matrix `Mf` of a section, the frame matrix `Ff`,
the coordinate-frame chart matrix `Gf` of the section and `G0f` of the background, the dual frame
coefficient `dd`, the localised weight `wf`, and the basic identities relating them
(`Mf = Ff · Gf · Ffᵀ`, `Ff · dd = 1`).
-/
import Mathlib
import Submission.Work.Diff.STE.B3.Comp
import Submission.Work.Diff.STE.D.Setup
import Submission.Work.Diff.EXT.Basic
import Submission.Work.Diff.STE.D.psi.secChartVal_eq_deTurckOp
import Submission.Work.Diff.STE.deTurck.pPhi_decomp

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

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ((⊤ : ENat) : WithTop ENat) M] [T2Space M] [I.Boundaryless]
  {ι₀ : Type*} [Fintype ι₀] {g₀ : Submission.Diff.SMet I M}

noncomputable section

variable (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (hLC : Submission.Diff.LCSmooth I M)
  (h : Work.Diff.STE.Bil (I := I) (M := M))
  (hsym : ∀ (x : M) (u v : TangentSpace I x), h x u v = h x v u)
  (hpos : ∀ (x : M) (v : TangentSpace I x), v ≠ 0 → 0 < h x v v)
  (hsmooth : Work.Diff.STE.D.ChartData (I := I) (M := M) h)

/-- the chart coordinate of the point with flat coordinate `z` -/
def yf (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (j : ι₀)
    (z : Fin (Module.finrank ℝ E) → ℝ) : E :=
  flatToE (I := I) (D.x₀ j) z

/-- the ON-frame chart matrix -/
def Mf (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (h : Work.Diff.STE.Bil (I := I) (M := M))
    (j : ι₀) (z : Fin (Module.finrank ℝ E) → ℝ) : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → ℝ :=
  fun a b => D.mat j h a b z

/-- the frame matrix: coordinates of `e_j a` in the coordinate frame of the chart at `x₀ j` -/
def Ff (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (j : ι₀)
    (z : Fin (Module.finrank ℝ E) → ℝ) :
    Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → ℝ :=
  fun a i => Work.Diff.STE.D.coordCLM (I := I) (M := M) (D.x₀ j) (D.pt j z) i (D.e j a (D.pt j z))

/-- the localised weight -/
def wf (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (j : ι₀)
    (z : Fin (Module.finrank ℝ E) → ℝ) : ℝ :=
  D.psi j z * Real.sqrt (D.dens j z)

/-- the coordinate-frame chart matrix of the section `h` at flat coordinate `z` -/
def Gf (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (h : Work.Diff.STE.Bil (I := I) (M := M)) (j : ι₀) (z : Fin (Module.finrank ℝ E) → ℝ) : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → ℝ :=
  Work.Diff.STE.D.chartMatOf (I := I) (M := M) h (D.x₀ j) (yf D j z)

/-- the coordinate-frame chart matrix of the background `g₀` -/
def G0f (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (j : ι₀) (z : Fin (Module.finrank ℝ E) → ℝ) : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → ℝ :=
  Work.Diff.EXT.chartMatFun (I := I) g₀ (D.x₀ j) (yf D j z)

lemma pt_mem_chart (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (j : ι₀) {z : Fin (Module.finrank ℝ E) → ℝ} (hz : ‖z‖ ≤ 2 * D.σ j) :
    D.pt j z ∈ (chartAt H (D.x₀ j)).source := by
  have h1 : D.pt j z ∈ (extChartAt I (D.x₀ j)).source :=
    (extChartAt I (D.x₀ j)).map_target (D.htarget j z hz)
  rwa [extChartAt_source] at h1

lemma yf_eq_chart (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (j : ι₀) {z : Fin (Module.finrank ℝ E) → ℝ} (hz : ‖z‖ ≤ 2 * D.σ j) :
    (extChartAt I (D.x₀ j)) (D.pt j z) = yf D j z := D.extChartAt_pt j hz

/-- **The chart expression of the DeTurck operator in the ON frame.** -/
lemma bridge (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (j : ι₀) (a b : Fin (Module.finrank ℝ E)) {z : Fin (Module.finrank ℝ E) → ℝ}
    (hz : ‖z‖ ≤ 2 * D.σ j) :
    D.R j (Work.Diff.STE.D.deTurckSec (I := I) hLC g₀ h hsym hpos hsmooth) a b z
      = wf (I := I) (M := M) D j z * ∑ i, ∑ k,
          (Work.Diff.STE.D.pPhiJetOf (I := I) (M := M) g₀ h (D.x₀ j) (yf (I := I) (M := M) D j z) i k)
            * (Ff (I := I) (M := M) D j z a i * Ff (I := I) (M := M) D j z b k) := by
  have hmem : D.pt j z ∈ (chartAt H (D.x₀ j)).source := pt_mem_chart (I := I) (M := M) D j hz
  have hbridge := Work.Diff.STE.D.psi.secChartVal_eq_deTurckOp (I := I) (M := M) hLC
    (Work.Diff.STE.D.smetOf (I := I) h hsym hpos hsmooth) g₀ (D.x₀ j) hmem
    (D.e j a (D.pt j z)) (D.e j b (D.pt j z))
  simp only [Work.Diff.STE.B3Data.R, wf, Work.Diff.STE.B3Data.mat, mul_assoc]
  rw [Work.Diff.STE.D.deTurckSec_apply]
  rw [← hbridge]
  have hs : (Work.Diff.STE.D.smetOf (I := I) h hsym hpos hsmooth).inner = h := rfl
  simp only [Work.Diff.STE.D.secChartVal, Ff]
  rw [D.extChartAt_pt j hz]
  simp only [yf, hs]

/-- The expansion of the ON frame vector `e j a` in the coordinate frame of the chart at `x₀ j`. -/
lemma ef_expand (j : ι₀) (a : Fin (Module.finrank ℝ E))
    {z : Fin (Module.finrank ℝ E) → ℝ} (hz : ‖z‖ ≤ 2 * D.σ j) :
    D.e j a (D.pt j z)
      = ∑ i, Ff (I := I) (M := M) D j z a i
          • Work.Diff.GE.cFrame (I := I) (D.x₀ j) i (D.pt j z) := by
  have hmem : D.pt j z ∈ (chartAt H (D.x₀ j)).source := pt_mem_chart (I := I) (M := M) D j hz
  exact Work.Diff.STE.D.psi.self_eq_sum_coordCLM_smul_cFrame (I := I) (M := M) (D.x₀ j) hmem
    (D.e j a (D.pt j z))

/-- **`Mf = Ff · Gf · Ffᵀ`** (as functions of `z`), by bilinearity of `h` and the frame expansion. -/
lemma Mf_eq (j : ι₀) (a b : Fin (Module.finrank ℝ E))
    {z : Fin (Module.finrank ℝ E) → ℝ} (hz : ‖z‖ ≤ 2 * D.σ j) :
    Mf (I := I) (M := M) D h j z a b
      = ∑ i, ∑ k, Ff (I := I) (M := M) D j z a i * Gf (I := I) (M := M) D h j z i k
          * Ff (I := I) (M := M) D j z b k := by
  simp only [Mf, Gf, Work.Diff.STE.B3Data.mat, Work.Diff.STE.D.chartMatOf_apply]
  rw [ef_expand (I := I) (M := M) D j a hz, ef_expand (I := I) (M := M) D j b hz]
  simp only [map_sum, ContinuousLinearMap.sum_apply, map_smul, ContinuousLinearMap.smul_apply,
    smul_eq_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => ?_
  simp only [Gf, yf, Work.Diff.STE.B3Data.pt, Work.Diff.GE.cFrame_apply, Work.Diff.GE.cBasis,
    Work.Diff.EXT.bB]
  ac_rfl

/-- The **dual frame coefficient** `dd z i b = Σ_p (g₀)_{ip}(z) · Ff z b p`: the coordinates of the
coordinate frame vector `i` in the ON frame `e j ·`. -/
def dd (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (j : ι₀)
    (z : Fin (Module.finrank ℝ E) → ℝ) :
    Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → ℝ :=
  fun i b => ∑ p, G0f (I := I) D j z i p * Ff (I := I) (M := M) D j z b p

/-- **The `g₀`-orthonormality of the frame `e j ·` in matrix form**: `Ff · dd = 1`. -/
lemma Ff_mul_dd (j : ι₀) {z : Fin (Module.finrank ℝ E) → ℝ} (hz : ‖z‖ ≤ 2 * D.σ j) :
    (Matrix.of (Ff (I := I) (M := M) D j z)) * (Matrix.of (dd (I := I) (M := M) D j z)) = 1 := by
  have hON : ∀ a b : Fin (Module.finrank ℝ E),
      g₀.inner (D.pt j z) (D.e j a (D.pt j z)) (D.e j b (D.pt j z)) = if a = b then 1 else 0 :=
    D.heON j z hz
  ext a b
  rw [Matrix.mul_apply, Matrix.one_apply]
  simp only [Matrix.of_apply, dd, Finset.mul_sum]
  have key : ∑ i, ∑ p, Ff (I := I) (M := M) D j z a i
        * (G0f (I := I) D j z i p * Ff (I := I) (M := M) D j z b p)
      = g₀.inner (D.pt j z)
        (∑ i, Ff (I := I) (M := M) D j z a i
          • Work.Diff.GE.cFrame (I := I) (D.x₀ j) i (D.pt j z))
        (∑ p, Ff (I := I) (M := M) D j z b p
          • Work.Diff.GE.cFrame (I := I) (D.x₀ j) p (D.pt j z)) := by
    simp only [map_sum, ContinuousLinearMap.sum_apply, map_smul, ContinuousLinearMap.smul_apply,
      smul_eq_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun p _ => ?_
    simp only [G0f, yf, Work.Diff.STE.B3Data.pt, Work.Diff.GE.cFrame_apply,
      Work.Diff.EXT.chartMatFun, Work.Diff.GE.cBasis, Work.Diff.EXT.bB]
    ac_rfl
  rw [key, ← ef_expand (I := I) (M := M) D j a hz, ← ef_expand (I := I) (M := M) D j b hz]
  exact hON a b


/-- **The inverse of the frame matrix**: the coefficients of the coordinate frame vectors in the
orthonormal frame. -/
def Finvf (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (j : ι₀)
    (z : Fin (Module.finrank ℝ E) → ℝ) :
    Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → ℝ :=
  fun i a => ((Matrix.of (Ff (I := I) (M := M) D j z))⁻¹) i a

lemma Finvf_eq_inv (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (j : ι₀)
    (z : Fin (Module.finrank ℝ E) → ℝ) :
    Matrix.of (Finvf (I := I) (M := M) D j z) = (Matrix.of (Ff (I := I) (M := M) D j z))⁻¹ := rfl

/-- The frame matrix `Ff` is invertible on the `2σ`-ball: this is the matrix form of the
`g₀`-orthonormality of the frame `e j ·`. -/
lemma det_Ff_ne_zero (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (j : ι₀)
    {z : Fin (Module.finrank ℝ E) → ℝ} (hz : ‖z‖ ≤ 2 * D.σ j) :
    (Matrix.of (Ff (I := I) (M := M) D j z)).det ≠ 0 := by
  have h := Ff_mul_dd (I := I) (M := M) D j hz
  have h2 : (Matrix.of (Ff (I := I) (M := M) D j z)).det
      * (Matrix.of (dd (I := I) (M := M) D j z)).det = 1 := by
    rw [← Matrix.det_mul, h, Matrix.det_one]
  intro h0
  rw [h0, zero_mul] at h2
  exact one_ne_zero h2.symm

/-- **`Mf = Ff · Gf · Ffᵀ` in matrix form.** -/
lemma Mf_matrix_eq (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀)
    (h : Work.Diff.STE.Bil (I := I) (M := M)) (j : ι₀)
    {z : Fin (Module.finrank ℝ E) → ℝ} (hz : ‖z‖ ≤ 2 * D.σ j) :
    Matrix.of (Mf (I := I) (M := M) D h j z)
      = Matrix.of (Ff (I := I) (M := M) D j z) * Matrix.of (Gf (I := I) (M := M) D h j z)
        * (Matrix.of (Ff (I := I) (M := M) D j z))ᵀ := by
  ext a b
  rw [Matrix.mul_apply]
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Finset.sum_mul, Matrix.of_apply]
  rw [Mf_eq (I := I) (M := M) D h j a b hz]
  conv_rhs => rw [Finset.sum_comm]

/-- **`Gf = Ff⁻¹ · Mf · Ff⁻¹ᵀ`**: the chart matrix of the section in the coordinate frame, in terms
of the orthonormal-frame chart matrix and the inverse frame matrix. -/
lemma Gf_eq_dual (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀)
    (h : Work.Diff.STE.Bil (I := I) (M := M)) (j : ι₀)
    {z : Fin (Module.finrank ℝ E) → ℝ} (hz : ‖z‖ ≤ 2 * D.σ j)
    (i k : Fin (Module.finrank ℝ E)) :
    Gf (I := I) (M := M) D h j z i k
      = ∑ a, ∑ b, Finvf (I := I) (M := M) D j z i a * Mf (I := I) (M := M) D h j z a b
          * Finvf (I := I) (M := M) D j z k b := by
  have hdet : IsUnit (Matrix.of (Ff (I := I) (M := M) D j z)).det :=
    isUnit_iff_ne_zero.mpr (det_Ff_ne_zero (I := I) (M := M) D j hz)
  have hdetT : IsUnit ((Matrix.of (Ff (I := I) (M := M) D j z))ᵀ).det := by
    rwa [Matrix.det_transpose]
  have hkey : Matrix.of (Mf (I := I) (M := M) D h j z)
      = Matrix.of (Ff (I := I) (M := M) D j z)
        * (Matrix.of (Gf (I := I) (M := M) D h j z)
          * (Matrix.of (Ff (I := I) (M := M) D j z))ᵀ) := by
    rw [Mf_matrix_eq (I := I) (M := M) D h j hz, Matrix.mul_assoc]
  have h1 : (Matrix.of (Ff (I := I) (M := M) D j z))⁻¹ * Matrix.of (Mf (I := I) (M := M) D h j z)
      = Matrix.of (Gf (I := I) (M := M) D h j z)
        * (Matrix.of (Ff (I := I) (M := M) D j z))ᵀ := by
    rw [hkey, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hdet, Matrix.one_mul]
  have h2 : (Matrix.of (Finvf (I := I) (M := M) D j z)) * Matrix.of (Mf (I := I) (M := M) D h j z)
      * (Matrix.of (Finvf (I := I) (M := M) D j z))ᵀ
      = Matrix.of (Gf (I := I) (M := M) D h j z) := by
    rw [Finvf_eq_inv (I := I) (M := M) D j z, Matrix.transpose_nonsing_inv, h1,
      Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hdetT, Matrix.mul_one]
  have hG := h2.symm
  change (Matrix.of (Gf (I := I) (M := M) D h j z)) i k = _
  rw [hG]
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Finset.sum_mul, Matrix.of_apply]
  conv_lhs => rw [Finset.sum_comm]

/-- **The eight terms in the second derivative of the product identity.**

Differentiating the function identity `Mf = Σ_{ik} Ff a i · Gf i k · Ff b k` twice (the nine-term
Leibniz rule `Work.Diff.STE.B3.transport_triple2`) gives
`∂_c∂_d Mf a b = Σ_{ik} [nine terms]`; this definition collects the *eight* terms that do **not**
involve the second derivative `∂_c∂_d Gf i k`.  Consequently
`Σ_{ik} Ff a i · (∂_c∂_d Gf i k) · Ff b k = ∂_c∂_d Mf a b − eightTerm` (see
`Work.Diff.STE.B3.transport_Mf_second`). -/
def eightTerm (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀)
    (h : Work.Diff.STE.Bil (I := I) (M := M)) (j : ι₀) (z : Fin (Module.finrank ℝ E) → ℝ)
    (c d a b : Fin (Module.finrank ℝ E)) : ℝ :=
  ∑ i, ∑ k,
      ( Work.Diff.STE.pdR c (Work.Diff.STE.pdR d (fun y => Ff (I := I) (M := M) D j y a i)) z
          * Gf (I := I) (M := M) D h j z i k * Ff (I := I) (M := M) D j z b k
      + Work.Diff.STE.pdR c (fun y => Ff (I := I) (M := M) D j y a i) z
          * Work.Diff.STE.pdR d (fun y => Gf (I := I) (M := M) D h j y i k) z
          * Ff (I := I) (M := M) D j z b k
      + Work.Diff.STE.pdR c (fun y => Ff (I := I) (M := M) D j y a i) z
          * Gf (I := I) (M := M) D h j z i k
          * Work.Diff.STE.pdR d (fun y => Ff (I := I) (M := M) D j y b k) z
      + Work.Diff.STE.pdR d (fun y => Ff (I := I) (M := M) D j y a i) z
          * Work.Diff.STE.pdR c (fun y => Gf (I := I) (M := M) D h j y i k) z
          * Ff (I := I) (M := M) D j z b k
      + Work.Diff.STE.pdR d (fun y => Ff (I := I) (M := M) D j y a i) z
          * Gf (I := I) (M := M) D h j z i k
          * Work.Diff.STE.pdR c (fun y => Ff (I := I) (M := M) D j y b k) z
      + Ff (I := I) (M := M) D j z a i
          * Work.Diff.STE.pdR c (fun y => Gf (I := I) (M := M) D h j y i k) z
          * Work.Diff.STE.pdR d (fun y => Ff (I := I) (M := M) D j y b k) z
      + Ff (I := I) (M := M) D j z a i
          * Work.Diff.STE.pdR d (fun y => Gf (I := I) (M := M) D h j y i k) z
          * Work.Diff.STE.pdR c (fun y => Ff (I := I) (M := M) D j y b k) z
      + Ff (I := I) (M := M) D j z a i * Gf (I := I) (M := M) D h j z i k
          * Work.Diff.STE.pdR c (Work.Diff.STE.pdR d (fun y => Ff (I := I) (M := M) D j y b k)) z )

/-- The spatial `2`-jet of the chart matrix of the background `g₀` at the flat coordinate `z`. -/
def Jets0 (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (j : ι₀)
    (z : Fin (Module.finrank ℝ E) → ℝ) :
    Work.Diff.EXT.MatE (E := E) × (E →L[ℝ] Work.Diff.EXT.MatE (E := E))
      × (E →L[ℝ] E →L[ℝ] Work.Diff.EXT.MatE (E := E)) :=
  Work.Diff.STE.D.chartJetOf (I := I) (M := M) g₀.inner (D.x₀ j) (yf (I := I) (M := M) D j z)

/-- The spatial `2`-jet of the chart matrix of the section `h` at the flat coordinate `z`. -/
def Jetsh (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀)
    (h : Work.Diff.STE.Bil (I := I) (M := M)) (j : ι₀)
    (z : Fin (Module.finrank ℝ E) → ℝ) :
    Work.Diff.EXT.MatE (E := E) × (E →L[ℝ] Work.Diff.EXT.MatE (E := E))
      × (E →L[ℝ] E →L[ℝ] Work.Diff.EXT.MatE (E := E)) :=
  Work.Diff.STE.D.chartJetOf (I := I) (M := M) h (D.x₀ j) (yf (I := I) (M := M) D j z)

/-- **The residual** `R h := R_j(P h) − Σ A^{pq} ∂_p∂_q(R_j h)`: the difference between the
localised DeTurck operator of the section and the second-order operator with coefficient `A`. -/
def Rres (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (hLC : Submission.Diff.LCSmooth I M)
    (h : Work.Diff.STE.Bil (I := I) (M := M))
    (hsym : ∀ (x : M) (u v : TangentSpace I x), h x u v = h x v u)
    (hpos : ∀ (x : M) (v : TangentSpace I x), v ≠ 0 → 0 < h x v v)
    (hsmooth : Work.Diff.STE.D.ChartData (I := I) (M := M) h)
    (j : ι₀) (A : (Fin (Module.finrank ℝ E) → ℝ) → Fin (Module.finrank ℝ E) →
      Fin (Module.finrank ℝ E) → ℝ) (z : Fin (Module.finrank ℝ E) → ℝ)
    (a b : Fin (Module.finrank ℝ E)) : ℝ :=
  D.R j (Work.Diff.STE.D.deTurckSec (I := I) hLC g₀ h hsym hpos hsmooth) a b z
    - ∑ p, ∑ q, A z p q
        * Work.Diff.STE.pdR p (Work.Diff.STE.pdR q (D.R j h a b)) z

/-- **The residual in lower-order form**: the residual `Rres` with the second derivative of the
orthonormal-frame chart matrix eliminated (via `transport_Mf_second`), the second-order part
cancelled (the principal part of the DeTurck operator in the orthonormal frame is the inverse
coordinate-frame chart matrix), so that only first derivatives of the chart matrices remain. -/
def residualLow (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀)
    (h : Work.Diff.STE.Bil (I := I) (M := M)) (j : ι₀)
    (z : Fin (Module.finrank ℝ E) → ℝ) (a b : Fin (Module.finrank ℝ E)) : ℝ :=
    wf (I := I) (M := M) D j z
        * (∑ i, ∑ k, Work.Diff.STE.DeTurck.pN
            (Jets0 (I := I) (M := M) D j z).1 (Jets0 (I := I) (M := M) D j z).2.1
            (Jets0 (I := I) (M := M) D j z).2.2
            (Jetsh (I := I) (M := M) D h j z).1 (Jetsh (I := I) (M := M) D h j z).2.1 i k
            * (Ff (I := I) (M := M) D j z a i * Ff (I := I) (M := M) D j z b k))
  - wf (I := I) (M := M) D j z * ∑ p, ∑ q,
      ((Matrix.of (Gf (I := I) (M := M) D h j z))⁻¹) p q
        * eightTerm (I := I) (M := M) D h j z p q a b
  - ∑ p, ∑ q, ((Matrix.of (Gf (I := I) (M := M) D h j z))⁻¹) p q
      * (2 * Work.Diff.STE.pdR p (wf (I := I) (M := M) D j) z
          * Work.Diff.STE.pdR q (fun y => Mf (I := I) (M := M) D h j y a b) z
        + Mf (I := I) (M := M) D h j z a b
          * Work.Diff.STE.pdR p (Work.Diff.STE.pdR q (wf (I := I) (M := M) D j)) z)

end

end Work.Diff.STE.B3
