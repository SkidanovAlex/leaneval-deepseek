/-
# Uniform two-sided bounds for the coordinate-frame chart matrix of the B3 transport

This file proves `Work.Diff.STE.B3.tmGamma_uniform`: the coefficient family of the Layer B3
transport (the inverse of the coordinate-frame chart matrix `Gf` of the section) is uniformly
elliptic, uniformly bounded, has a determinant in a fixed window and its entries have uniformly
bounded first flat jets -- **uniformly** over all sections `h` that are sandwiched between
`lam · g₀` and `K · g₀` and whose orthonormal-frame chart matrices have jet bound `K` on the
`2σ`-balls.

The strategy:

* the sandwich `lam · g₀ ≤ h ≤ K · g₀` compares the quadratic form of `Gf` with the quadratic form
  of the *background* chart matrix (`tmw_Gf_window`, the quadratic forms of the two chart matrices
  being the values of `h` resp. `g₀` on `∑ a, ξ a • ∂_a`), and the background chart matrix
  is uniformly elliptic and bounded on the enlarged balls `‖z‖ ≤ 2σ j + δ` (the child
  `tmw_bgwin`, which also supplies the margin on which the flat coordinate stays in the chart
  target and the frame matrix `Ff` stays invertible);
* the resulting uniform quadratic-form window for `Gf` is turned into uniform bounds for the
  inverse (quadratic form, entries, determinant) by the abstract compactness lemmas
  `tmw_matrix_inv_bounds` and `tmw_matrix_det_bounds`;
* the first jet of `Gf` is computed by the *proved* frame-change lemma
  `Work.Diff.STE.B3.dGf_eq_nDGc_of_target` (the region version of the product rule for
  `Gf = Finvf · Mf · Finvfᵀ`), whose summands involve only the frame inverse `Finvf` and its jet
  (`tmw_finvf_bound`) and the orthonormal-frame chart matrix `Mf` with its jet
  (`Work.Diff.STE.B3.mat_jet_bound_global`);
* the first jet of the *inverse* entries is obtained from the general formula for the derivative
  of a matrix inverse (`Work.Diff.STE.deTurck.fderiv_matrix_inv_entry`).
-/
import Mathlib
import Submission.Work.Diff.STE.B3.TransportDefs
import Submission.Work.Diff.STE.B3.transport_tame_defs
import Submission.Work.Diff.STE.B3.mat_jet_bound_global
import Submission.Work.Diff.STE.B3.tmGamma_props
import Submission.Work.Diff.STE.B3.transport_inv_pdR
import Submission.Work.Diff.STE.B3.CoeffDefs
import Submission.Work.Diff.STE.B3.LowJetAux
import Submission.Work.Diff.STE.B3.chartMatOf_posDef
import Submission.Work.Diff.STE.deTurck.gramInv_mvfderiv
import Submission.Work.Diff.STE.B3.tmw_finvf_bound
import Submission.Work.Diff.STE.B3.tmw_matrix_det_bounds
import Submission.Work.Diff.STE.B3.tmw_bgwin
import Submission.Work.Diff.STE.B3.tmw_matrix_inv_bounds

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.STE.B3

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology BigOperators Matrix
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter

set_option maxHeartbeats 1000000
set_option linter.unusedSectionVars false

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ((⊤ : ENat) : WithTop ENat) M] [T2Space M] [I.Boundaryless]
  {ι₀ : Type*} [Fintype ι₀] {g₀ : Submission.Diff.SMet I M}

/-- **The coordinate-frame chart matrix of a symmetric section is symmetric.** -/
theorem tmw_Gf_transpose (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀)
    (h : Work.Diff.STE.Bil (I := I) (M := M))
    (hsym : ∀ (x : M) (u v : TangentSpace I x), h x u v = h x v u) (j : ι₀)
    (z : Fin (Module.finrank ℝ E) → ℝ) :
    (Matrix.of (Gf (I := I) (M := M) D h j z)).transpose
      = Matrix.of (Gf (I := I) (M := M) D h j z) := by
  ext p q
  rw [Matrix.transpose_apply, Matrix.of_apply, Matrix.of_apply]
  show Gf (I := I) (M := M) D h j z q p = Gf (I := I) (M := M) D h j z p q
  simp only [Gf, yf, Work.Diff.STE.D.chartMatOf_apply]
  exact hsym _ _ _

/-- The chart matrix of `h` in the coordinate frame is the value of `h` on the coordinate-frame
vectors (definitional). -/
theorem tmw_Gf_eq_bilin (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀)
    (h : Work.Diff.STE.Bil (I := I) (M := M)) (j : ι₀)
    (z : Fin (Module.finrank ℝ E) → ℝ) (a b : Fin (Module.finrank ℝ E)) :
    Gf (I := I) (M := M) D h j z a b
      = h (D.pt j z) (cFrameAt (I := I) (M := M) D j z a)
          (cFrameAt (I := I) (M := M) D j z b) := rfl

/-- The quadratic form of the coordinate-frame chart matrix of `h` is the value of `h` on
`∑ a, ξ a • ∂_a`. -/
theorem tmw_Gf_quadForm (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀)
    (h : Work.Diff.STE.Bil (I := I) (M := M)) (j : ι₀)
    (z : Fin (Module.finrank ℝ E) → ℝ) (ξ : Fin (Module.finrank ℝ E) → ℝ) :
    (∑ a, ∑ b, Gf (I := I) (M := M) D h j z a b * ξ a * ξ b)
      = h (D.pt j z) (∑ a, ξ a • cFrameAt (I := I) (M := M) D j z a)
          (∑ b, ξ b • cFrameAt (I := I) (M := M) D j z b) := by
  simp only [tmw_Gf_eq_bilin, map_sum, ContinuousLinearMap.sum_apply, map_smul,
    ContinuousLinearMap.smul_apply, smul_eq_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  ring

/-- The chart matrix of the background in the coordinate frame is the value of `g₀` on the
coordinate-frame vectors (definitional). -/
theorem tmw_G0f_eq_bilin (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (j : ι₀)
    (z : Fin (Module.finrank ℝ E) → ℝ) (a b : Fin (Module.finrank ℝ E)) :
    Work.Diff.EXT.chartMatFun (I := I) g₀ (D.x₀ j)
        (Work.Diff.STE.flatToE (I := I) (D.x₀ j) z) a b
      = g₀.inner (D.pt j z) (cFrameAt (I := I) (M := M) D j z a)
          (cFrameAt (I := I) (M := M) D j z b) := rfl

/-- The quadratic form of the coordinate-frame chart matrix of the *background* `g₀` is the value
of `g₀` on `∑ a, ξ a • ∂_a`. -/
theorem tmw_G0f_quadForm (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (j : ι₀)
    (z : Fin (Module.finrank ℝ E) → ℝ) (ξ : Fin (Module.finrank ℝ E) → ℝ) :
    (∑ a, ∑ b, Work.Diff.EXT.chartMatFun (I := I) g₀ (D.x₀ j)
        (Work.Diff.STE.flatToE (I := I) (D.x₀ j) z) a b * ξ a * ξ b)
      = g₀.inner (D.pt j z) (∑ a, ξ a • cFrameAt (I := I) (M := M) D j z a)
          (∑ b, ξ b • cFrameAt (I := I) (M := M) D j z b) := by
  simp only [tmw_G0f_eq_bilin, map_sum, ContinuousLinearMap.sum_apply, map_smul,
    ContinuousLinearMap.smul_apply, smul_eq_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  ring

/-- **The quadratic-form window of the coordinate-frame chart matrix of `h`**, from the two-sided
bound on the *background* chart matrix and the sandwich `lam · g₀ ≤ h ≤ K · g₀`. -/
theorem tmw_Gf_window (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀)
    (h : Work.Diff.STE.Bil (I := I) (M := M)) {lam K mlo Mhi : ℝ} (hlam : 0 ≤ lam)
    (hK : 0 ≤ K)
    (hell : ∀ (x : M) (v : TangentSpace I x), lam * g₀.inner x v v ≤ h x v v)
    (hub : ∀ (x : M) (v : TangentSpace I x), h x v v ≤ K * g₀.inner x v v)
    (j : ι₀) (z : Fin (Module.finrank ℝ E) → ℝ)
    (hlo : ∀ ξ : Fin (Module.finrank ℝ E) → ℝ, mlo * ∑ i, (ξ i) ^ 2
      ≤ ∑ a, ∑ b, Work.Diff.EXT.chartMatFun (I := I) g₀ (D.x₀ j)
          (Work.Diff.STE.flatToE (I := I) (D.x₀ j) z) a b * ξ a * ξ b)
    (hhi : ∀ ξ : Fin (Module.finrank ℝ E) → ℝ,
      (∑ a, ∑ b, Work.Diff.EXT.chartMatFun (I := I) g₀ (D.x₀ j)
          (Work.Diff.STE.flatToE (I := I) (D.x₀ j) z) a b * ξ a * ξ b)
        ≤ Mhi * ∑ i, (ξ i) ^ 2)
    (ξ : Fin (Module.finrank ℝ E) → ℝ) :
    (lam * mlo) * ∑ i, (ξ i) ^ 2
        ≤ ∑ a, ∑ b, Gf (I := I) (M := M) D h j z a b * ξ a * ξ b
      ∧ (∑ a, ∑ b, Gf (I := I) (M := M) D h j z a b * ξ a * ξ b)
        ≤ (K * Mhi) * ∑ i, (ξ i) ^ 2 := by
  have hV := tmw_Gf_quadForm (I := I) (M := M) D h j z ξ
  have hV0 := tmw_G0f_quadForm (I := I) (M := M) D j z ξ
  constructor
  · rw [hV]
    calc (lam * mlo) * ∑ i, (ξ i) ^ 2
        = lam * (mlo * ∑ i, (ξ i) ^ 2) := by ring
      _ ≤ lam * (∑ a, ∑ b, Work.Diff.EXT.chartMatFun (I := I) g₀ (D.x₀ j)
            (Work.Diff.STE.flatToE (I := I) (D.x₀ j) z) a b * ξ a * ξ b) :=
          mul_le_mul_of_nonneg_left (hlo ξ) hlam
      _ = lam * g₀.inner (D.pt j z) (∑ a, ξ a • cFrameAt (I := I) (M := M) D j z a)
            (∑ b, ξ b • cFrameAt (I := I) (M := M) D j z b) := by rw [hV0]
      _ ≤ h (D.pt j z) (∑ a, ξ a • cFrameAt (I := I) (M := M) D j z a)
            (∑ b, ξ b • cFrameAt (I := I) (M := M) D j z b) :=
          hell (D.pt j z) _
  · rw [hV]
    calc h (D.pt j z) (∑ a, ξ a • cFrameAt (I := I) (M := M) D j z a)
          (∑ b, ξ b • cFrameAt (I := I) (M := M) D j z b)
        ≤ K * g₀.inner (D.pt j z) (∑ a, ξ a • cFrameAt (I := I) (M := M) D j z a)
            (∑ b, ξ b • cFrameAt (I := I) (M := M) D j z b) := hub (D.pt j z) _
      _ = K * (∑ a, ∑ b, Work.Diff.EXT.chartMatFun (I := I) g₀ (D.x₀ j)
            (Work.Diff.STE.flatToE (I := I) (D.x₀ j) z) a b * ξ a * ξ b) := by rw [hV0]
      _ ≤ K * (Mhi * ∑ i, (ξ i) ^ 2) := mul_le_mul_of_nonneg_left (hhi ξ) hK
      _ = (K * Mhi) * ∑ i, (ξ i) ^ 2 := by ring

theorem tmGamma_uniform
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ((⊤ : ENat) : WithTop ENat) M] [T2Space M] [I.Boundaryless]
    {ι₀ : Type*} [Fintype ι₀] {g₀ : Submission.Diff.SMet I M}
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (lam K : ℝ)
    (hlam : 0 < lam) (hK : 0 < K) :
    ∃ (δ mlo Mhi c Kr Kr₁ cl ch : ℝ),
      0 < δ ∧ 0 < mlo ∧ 0 < Mhi ∧ 0 < c ∧ 0 ≤ Kr ∧ 0 ≤ Kr₁ ∧ 0 < cl ∧ cl < ch ∧
      ∀ (h : Work.Diff.STE.Bil (I := I) (M := M))
        (hsym : ∀ (x : M) (u v : TangentSpace I x), h x u v = h x v u)
        (hpos : ∀ (x : M) (v : TangentSpace I x), v ≠ 0 → 0 < h x v v)
        (hsmooth : Work.Diff.STE.D.ChartData (I := I) (M := M) h)
        (hell : ∀ (x : M) (v : TangentSpace I x), lam * g₀.inner x v v ≤ h x v v)
        (hub : ∀ (x : M) (v : TangentSpace I x), h x v v ≤ K * g₀.inner x v v)
        (hjet : ∀ (i : ι₀) (cc dd r : Fin (Module.finrank ℝ E))
          (z : Fin (Module.finrank ℝ E) → ℝ), ‖z‖ ≤ 2 * D.σ i →
          |Work.Diff.STE.pdR r (D.mat i h cc dd) z| ≤ K),
        ∀ (j : ι₀) (z : Fin (Module.finrank ℝ E) → ℝ), ‖z‖ ≤ 2 * D.σ j + δ →
          (∀ ξ : Fin (Module.finrank ℝ E) → ℝ,
            mlo * ∑ i, (ξ i) ^ 2 ≤ ∑ p, ∑ q,
              Work.Diff.STE.B3.Gf (I := I) (M := M) D h j z p q * ξ p * ξ q) ∧
          (∀ ξ : Fin (Module.finrank ℝ E) → ℝ,
            (∑ p, ∑ q, Work.Diff.STE.B3.Gf (I := I) (M := M) D h j z p q * ξ p * ξ q)
              ≤ Mhi * ∑ i, (ξ i) ^ 2) ∧
          (cl ≤ (Matrix.of (fun i k => Work.Diff.STE.B3.Gf (I := I) (M := M) D h j z i k)).det ∧
            (Matrix.of (fun i k => Work.Diff.STE.B3.Gf (I := I) (M := M) D h j z i k)).det ≤ ch) ∧
          (∀ ξ : Fin (Module.finrank ℝ E) → ℝ,
            c * ∑ i, (ξ i) ^ 2 ≤ ∑ p, ∑ q,
              ((Matrix.of (fun i k => Work.Diff.STE.B3.Gf (I := I) (M := M) D h j z i k))⁻¹) p q
                * ξ p * ξ q) ∧
          (∀ p q : Fin (Module.finrank ℝ E),
            |((Matrix.of (fun i k => Work.Diff.STE.B3.Gf (I := I) (M := M) D h j z i k))⁻¹) p q|
              ≤ Kr) ∧
          (∀ (r p q : Fin (Module.finrank ℝ E)),
            |Work.Diff.STE.pdR r (fun w => ((Matrix.of (fun i k =>
                Work.Diff.STE.B3.Gf (I := I) (M := M) D h j w i k))⁻¹) p q) z| ≤ Kr₁) := by
  classical
  -- ## Step 1: the enlargement margin and the uniform background window
  obtain ⟨δ₁, m0, M0, hδ₁, hm0, hM0, hreg, hlo, hhi⟩ := tmw_bgwin (I := I) (M := M) D
  -- ## Step 2: the uniform jet bound for the orthonormal-frame chart matrix
  obtain ⟨δ₂, C₂, hδ₂, hC₂, hjetM⟩ := mat_jet_bound_global (I := I) (M := M) D lam K hlam
  -- ## Step 3: the common margin
  set δ : ℝ := min δ₁ δ₂ with hδdef
  have hδpos : 0 < δ := lt_min hδ₁ hδ₂
  have hδle₁ : δ ≤ δ₁ := min_le_left _ _
  have hδle₂ : δ ≤ δ₂ := min_le_right _ _
  have hreg' : ∀ (j : ι₀) (z : Fin (Module.finrank ℝ E) → ℝ), ‖z‖ ≤ 2 * D.σ j + δ →
      Work.Diff.STE.flatToE (I := I) (D.x₀ j) z ∈ (extChartAt I (D.x₀ j)).target ∧
        (Matrix.of (Ff (I := I) (M := M) D j z)).det ≠ 0 :=
    fun j z hz => hreg j z (le_trans hz (by linarith))
  have hlo' : ∀ (j : ι₀) (z : Fin (Module.finrank ℝ E) → ℝ), ‖z‖ ≤ 2 * D.σ j + δ →
      ∀ ξ : Fin (Module.finrank ℝ E) → ℝ, m0 * ∑ i, (ξ i) ^ 2 ≤
        ∑ a, ∑ b, Work.Diff.EXT.chartMatFun (I := I) g₀ (D.x₀ j)
          (Work.Diff.STE.flatToE (I := I) (D.x₀ j) z) a b * ξ a * ξ b :=
    fun j z hz => hlo j z (le_trans hz (by linarith))
  have hhi' : ∀ (j : ι₀) (z : Fin (Module.finrank ℝ E) → ℝ), ‖z‖ ≤ 2 * D.σ j + δ →
      ∀ ξ : Fin (Module.finrank ℝ E) → ℝ,
        (∑ a, ∑ b, Work.Diff.EXT.chartMatFun (I := I) g₀ (D.x₀ j)
            (Work.Diff.STE.flatToE (I := I) (D.x₀ j) z) a b * ξ a * ξ b)
          ≤ M0 * ∑ i, (ξ i) ^ 2 :=
    fun j z hz => hhi j z (le_trans hz (by linarith))
  -- ## Step 4: uniform bounds for the frame inverse and its jet
  obtain ⟨C₄, hC₄, hFinv, hDFin⟩ := tmw_finvf_bound (I := I) (M := M) D hδpos hreg'
  -- ## Step 5: the matrix constants
  obtain ⟨c, C, hc, hC, hmat⟩ :=
    tmw_matrix_inv_bounds (Module.finrank ℝ E) (lam * m0) (K * M0) (mul_pos hlam hm0)
  obtain ⟨cl, ch, hcl, hclch, hdets⟩ :=
    tmw_matrix_det_bounds (Module.finrank ℝ E) (lam * m0) (K * M0) (mul_pos hlam hm0)
  -- ## Step 6: the jet constant
  set Kdg : ℝ := (Module.finrank ℝ E : ℝ) ^ 2 * (3 * (C₄ * C₂ * C₄)) with hKdg
  set Kr₁ : ℝ := (Module.finrank ℝ E : ℝ) ^ 2 * (C * Kdg * C) with hKr₁
  have hKdg0 : 0 ≤ Kdg := by
    rw [hKdg]
    exact mul_nonneg (by positivity) (by positivity)
  have hKr₁0 : 0 ≤ Kr₁ := by
    rw [hKr₁]
    exact mul_nonneg (by positivity) (mul_nonneg (mul_nonneg hC hKdg0) hC)
  refine ⟨δ, lam * m0, K * M0, c, C, Kr₁, cl, ch, hδpos, mul_pos hlam hm0, mul_pos hK hM0,
    hc, hC, hKr₁0, hcl, hclch, ?_⟩
  intro h hsym hpos hsmooth hell hub hjet j z hz
  -- ## The region hypotheses at `(j, z)`
  have htz : Work.Diff.STE.flatToE (I := I) (D.x₀ j) z ∈ (extChartAt I (D.x₀ j)).target :=
    (hreg' j z hz).1
  have hdz : (Matrix.of (Ff (I := I) (M := M) D j z)).det ≠ 0 := (hreg' j z hz).2
  have hz₂ : ‖z‖ ≤ 2 * D.σ j + δ₂ := le_trans hz (by linarith)
  -- ## Symmetry of the chart matrix
  have hsymG : ∀ p q : Fin (Module.finrank ℝ E),
      Gf (I := I) (M := M) D h j z p q = Gf (I := I) (M := M) D h j z q p := by
    have htr := tmw_Gf_transpose (I := I) (M := M) D h hsym j z
    intro p q
    have hpq := congrFun (congrFun htr q) p
    simpa only [Matrix.transpose_apply, Matrix.of_apply] using hpq
  -- ## The quadratic-form window of the chart matrix
  have hquad : ∀ ξ : Fin (Module.finrank ℝ E) → ℝ,
      (lam * m0) * ∑ i, (ξ i) ^ 2
          ≤ ∑ p, ∑ q, Gf (I := I) (M := M) D h j z p q * ξ p * ξ q ∧
      (∑ p, ∑ q, Gf (I := I) (M := M) D h j z p q * ξ p * ξ q)
          ≤ (K * M0) * ∑ i, (ξ i) ^ 2 := fun ξ =>
    tmw_Gf_window (I := I) (M := M) D h (lam := lam) (K := K) (mlo := m0) (Mhi := M0)
      hlam.le hK.le hell hub j z (hlo' j z hz) (hhi' j z hz) ξ
  -- ## The eta bridge between the target's matrices and the chart matrix
  have heta : (fun i k : Fin (Module.finrank ℝ E) => Gf (I := I) (M := M) D h j z i k)
      = Gf (I := I) (M := M) D h j z := by
    funext i k; rfl
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro ξ
    exact (hquad ξ).1
  · intro ξ
    exact (hquad ξ).2
  · -- the determinant window
    have hd := hdets (Gf (I := I) (M := M) D h j z) hsymG
      (fun ξ => (hquad ξ).1) (fun ξ => (hquad ξ).2)
    exact ⟨by simpa only [heta] using hd.1, by simpa only [heta] using hd.2⟩
  · -- the ellipticity of the inverse
    intro ξ
    have hd := (hmat (Gf (I := I) (M := M) D h j z) hsymG
      (fun ξ => (hquad ξ).1) (fun ξ => (hquad ξ).2)).1 ξ
    simpa only [heta] using hd
  · -- the entrywise bound for the inverse
    intro p q
    have hd := (hmat (Gf (I := I) (M := M) D h j z) hsymG
      (fun ξ => (hquad ξ).1) (fun ξ => (hquad ξ).2)).2 p q
    simpa only [heta] using hd
  · -- the first jet of the inverse entries
    intro r p q
    -- the jet of the chart matrix is the nominal jet `nDGc`
    have hjetG : ∀ pp qq : Fin (Module.finrank ℝ E),
        |Work.Diff.STE.pdR r (fun y => Gf (I := I) (M := M) D h j y pp qq) z| ≤ Kdg := by
      intro pp qq
      have h1 : Work.Diff.STE.pdR r (fun y => Gf (I := I) (M := M) D h j y pp qq) z
          = nDGc (I := I) (M := M) D j z (Mf (I := I) (M := M) D h j z)
              (dMf (I := I) (M := M) D h j z) r pp qq :=
        dGf_eq_nDGc_of_target (I := I) (M := M) D h hsmooth j htz hdz r pp qq
      rw [h1, nDGc]
      -- the three product-rule terms
      have hV : ∀ a b : Fin (Module.finrank ℝ E), |Mf (I := I) (M := M) D h j z a b| ≤ C₂ :=
        fun a b => by
          simpa only [Mf] using (hjetM h hsym hsmooth hell hub hjet j a b r z hz₂).1
      have hW : ∀ a b : Fin (Module.finrank ℝ E),
          |dMf (I := I) (M := M) D h j z r a b| ≤ C₂ := fun a b => by
        simpa only [dMf, Mf] using (hjetM h hsym hsmooth hell hub hjet j a b r z hz₂).2
      have hU : ∀ i a : Fin (Module.finrank ℝ E), |Finvf (I := I) (M := M) D j z i a| ≤ C₄ :=
        fun i a => hFinv j z hz i a
      have hDU : ∀ c i a : Fin (Module.finrank ℝ E),
          |Work.Diff.STE.pdR c (fun y => Finvf (I := I) (M := M) D j y i a) z| ≤ C₄ :=
        fun c i a => by simpa only [tmDFin] using hDFin j z hz c i a
      have hterm : ∀ a b : Fin (Module.finrank ℝ E),
          |( Work.Diff.STE.pdR r (fun y => Finvf (I := I) (M := M) D j y pp a) z
                * Mf (I := I) (M := M) D h j z a b * Finvf (I := I) (M := M) D j z qq b
              + Finvf (I := I) (M := M) D j z pp a * dMf (I := I) (M := M) D h j z r a b
                * Finvf (I := I) (M := M) D j z qq b
              + Finvf (I := I) (M := M) D j z pp a * Mf (I := I) (M := M) D h j z a b
                * Work.Diff.STE.pdR r (fun y => Finvf (I := I) (M := M) D j y qq b) z )|
            ≤ 3 * (C₄ * C₂ * C₄) := by
        intro a b
        have h1 : |Work.Diff.STE.pdR r (fun y => Finvf (I := I) (M := M) D j y pp a) z
              * Mf (I := I) (M := M) D h j z a b * Finvf (I := I) (M := M) D j z qq b|
            ≤ C₄ * C₂ * C₄ := by
          rw [abs_mul, abs_mul]
          exact mul_le_mul (mul_le_mul (hDU r pp a) (hV a b) (abs_nonneg _) hC₄) (hU qq b)
            (abs_nonneg _) (mul_nonneg hC₄ hC₂)
        have h2 : |Finvf (I := I) (M := M) D j z pp a * dMf (I := I) (M := M) D h j z r a b
              * Finvf (I := I) (M := M) D j z qq b| ≤ C₄ * C₂ * C₄ := by
          rw [abs_mul, abs_mul]
          exact mul_le_mul (mul_le_mul (hU pp a) (hW a b) (abs_nonneg _) hC₄) (hU qq b)
            (abs_nonneg _) (mul_nonneg hC₄ hC₂)
        have h3 : |Finvf (I := I) (M := M) D j z pp a * Mf (I := I) (M := M) D h j z a b
              * Work.Diff.STE.pdR r (fun y => Finvf (I := I) (M := M) D j y qq b) z|
            ≤ C₄ * C₂ * C₄ := by
          rw [abs_mul, abs_mul]
          exact mul_le_mul (mul_le_mul (hU pp a) (hV a b) (abs_nonneg _) hC₄) (hDU r qq b)
            (abs_nonneg _) (mul_nonneg hC₄ hC₂)
        calc |( Work.Diff.STE.pdR r (fun y => Finvf (I := I) (M := M) D j y pp a) z
                  * Mf (I := I) (M := M) D h j z a b * Finvf (I := I) (M := M) D j z qq b
                + Finvf (I := I) (M := M) D j z pp a * dMf (I := I) (M := M) D h j z r a b
                  * Finvf (I := I) (M := M) D j z qq b
                + Finvf (I := I) (M := M) D j z pp a * Mf (I := I) (M := M) D h j z a b
                  * Work.Diff.STE.pdR r (fun y => Finvf (I := I) (M := M) D j y qq b) z )|
            ≤ |Work.Diff.STE.pdR r (fun y => Finvf (I := I) (M := M) D j y pp a) z
                  * Mf (I := I) (M := M) D h j z a b * Finvf (I := I) (M := M) D j z qq b
                + Finvf (I := I) (M := M) D j z pp a * dMf (I := I) (M := M) D h j z r a b
                  * Finvf (I := I) (M := M) D j z qq b|
              + |Finvf (I := I) (M := M) D j z pp a * Mf (I := I) (M := M) D h j z a b
                  * Work.Diff.STE.pdR r (fun y => Finvf (I := I) (M := M) D j y qq b) z| :=
              abs_add_le _ _
          _ ≤ (|Work.Diff.STE.pdR r (fun y => Finvf (I := I) (M := M) D j y pp a) z
                  * Mf (I := I) (M := M) D h j z a b * Finvf (I := I) (M := M) D j z qq b|
                + |Finvf (I := I) (M := M) D j z pp a * dMf (I := I) (M := M) D h j z r a b
                    * Finvf (I := I) (M := M) D j z qq b|)
              + |Finvf (I := I) (M := M) D j z pp a * Mf (I := I) (M := M) D h j z a b
                  * Work.Diff.STE.pdR r (fun y => Finvf (I := I) (M := M) D j y qq b) z| :=
              add_le_add (abs_add_le _ _) le_rfl
          _ ≤ (C₄ * C₂ * C₄ + C₄ * C₂ * C₄) + C₄ * C₂ * C₄ := add_le_add (add_le_add h1 h2) h3
          _ = 3 * (C₄ * C₂ * C₄) := by ring
      calc |∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
              ( Work.Diff.STE.pdR r (fun y => Finvf (I := I) (M := M) D j y pp a) z
                  * Mf (I := I) (M := M) D h j z a b * Finvf (I := I) (M := M) D j z qq b
                + Finvf (I := I) (M := M) D j z pp a * dMf (I := I) (M := M) D h j z r a b
                  * Finvf (I := I) (M := M) D j z qq b
                + Finvf (I := I) (M := M) D j z pp a * Mf (I := I) (M := M) D h j z a b
                  * Work.Diff.STE.pdR r (fun y => Finvf (I := I) (M := M) D j y qq b) z )|
          ≤ ∑ a : Fin (Module.finrank ℝ E), |∑ b : Fin (Module.finrank ℝ E),
              ( Work.Diff.STE.pdR r (fun y => Finvf (I := I) (M := M) D j y pp a) z
                  * Mf (I := I) (M := M) D h j z a b * Finvf (I := I) (M := M) D j z qq b
                + Finvf (I := I) (M := M) D j z pp a * dMf (I := I) (M := M) D h j z r a b
                  * Finvf (I := I) (M := M) D j z qq b
                + Finvf (I := I) (M := M) D j z pp a * Mf (I := I) (M := M) D h j z a b
                  * Work.Diff.STE.pdR r (fun y => Finvf (I := I) (M := M) D j y qq b) z )| :=
            Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
              3 * (C₄ * C₂ * C₄) :=
            Finset.sum_le_sum (fun a _ => le_trans (Finset.abs_sum_le_sum_abs _ _)
              (Finset.sum_le_sum (fun b _ => hterm a b)))
        _ = (Module.finrank ℝ E : ℝ) * ((Module.finrank ℝ E : ℝ) * (3 * (C₄ * C₂ * C₄))) := by
            simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        _ = Kdg := by rw [hKdg]; ring
    -- the derivative of the inverse entries
    have hAc : ∀ a b : Fin (Module.finrank ℝ E),
        ContDiffAt ℝ (⊤ : ℕ∞) (fun y => Gf (I := I) (M := M) D h j y a b) z :=
      fun a b => Gf_contDiffAt (I := I) (M := M) D h hsmooth j a b htz
    have hAdiff : DifferentiableAt ℝ
        (fun y : Fin (Module.finrank ℝ E) → ℝ => Gf (I := I) (M := M) D h j y) z := by
      rw [differentiableAt_pi]
      intro a
      rw [differentiableAt_pi]
      intro b
      exact (hAc a b).differentiableAt (by simp)
    have hdetG : (Matrix.of (Gf (I := I) (M := M) D h j z)).det ≠ 0 :=
      ne_of_gt ((chartMatOf_posDef (I := I) (M := M) h (D.x₀ j) hsym hpos htz).det_pos)
    have hNc : ∀ a b : Fin (Module.finrank ℝ E), ContDiffAt ℝ (⊤ : ℕ∞)
        (fun y => (Matrix.of (Gf (I := I) (M := M) D h j y))⁻¹ a b) z := fun a b =>
      tmNom_inv_entry_ContDiffAt
        (X := fun y : Fin (Module.finrank ℝ E) → ℝ =>
          Matrix.of (Gf (I := I) (M := M) D h j y)) (fun a b => hAc a b) hdetG a b
    have hNdiff : DifferentiableAt ℝ
        (fun x : Fin (Module.finrank ℝ E) → ℝ =>
          fun μ ν => (Matrix.of (Gf (I := I) (M := M) D h j x))⁻¹ μ ν) z := by
      rw [differentiableAt_pi]
      intro μ
      rw [differentiableAt_pi]
      intro ν
      exact (hNc μ ν).differentiableAt (by simp)
    have hdetcont : ContinuousAt
        (fun y : Fin (Module.finrank ℝ E) → ℝ => (Matrix.of (Gf (I := I) (M := M) D h j y)).det)
        z :=
      (tmNom_det_ContDiffAt (X := fun y : Fin (Module.finrank ℝ E) → ℝ =>
        Matrix.of (Gf (I := I) (M := M) D h j y)) (fun a b => hAc a b)).continuousAt
    have hmul : ∀ᶠ x in nhds z,
        (Matrix.of (Gf (I := I) (M := M) D h j x))⁻¹ * Matrix.of (Gf (I := I) (M := M) D h j x)
          = 1 := by
      filter_upwards [hdetcont.eventually_ne hdetG] with x hx
      exact Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hx)
    have hmul' : Matrix.of (Gf (I := I) (M := M) D h j z)
        * (Matrix.of (Gf (I := I) (M := M) D h j z))⁻¹ = 1 :=
      Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hdetG)
    have hcore := Work.Diff.STE.deTurck.fderiv_matrix_inv_entry
      (E := Fin (Module.finrank ℝ E) → ℝ) (n := Module.finrank ℝ E)
      (A := fun y : Fin (Module.finrank ℝ E) → ℝ => Gf (I := I) (M := M) D h j y)
      (y := z) p q hAdiff hNdiff hmul hmul' (Pi.single r (1 : ℝ))
    have hfde : ∀ pp qq : Fin (Module.finrank ℝ E),
        ((fderiv ℝ (fun y : Fin (Module.finrank ℝ E) → ℝ =>
            Gf (I := I) (M := M) D h j y) z) (Pi.single r (1 : ℝ))) pp qq
          = Work.Diff.STE.pdR r (fun y => Gf (I := I) (M := M) D h j y pp qq) z := by
      intro pp qq
      rw [← Work.Diff.STE.deTurck.fderiv_pi_entry hAdiff pp qq (Pi.single r 1)]
      rfl
    have hstep : Work.Diff.STE.pdR r (fun w : Fin (Module.finrank ℝ E) → ℝ =>
          (Matrix.of (Gf (I := I) (M := M) D h j w))⁻¹ p q) z
        = -∑ pp : Fin (Module.finrank ℝ E), ∑ qq : Fin (Module.finrank ℝ E),
            (Matrix.of (Gf (I := I) (M := M) D h j z))⁻¹ p pp
              * Work.Diff.STE.pdR r (fun y => Gf (I := I) (M := M) D h j y pp qq) z
              * (Matrix.of (Gf (I := I) (M := M) D h j z))⁻¹ qq q := by
      rw [Work.Diff.STE.pdR, hcore]
      refine congrArg Neg.neg ?_
      refine Finset.sum_congr rfl (fun pp _ => Finset.sum_congr rfl (fun qq _ => ?_))
      rw [hfde pp qq]
    have hUinv : ∀ pp : Fin (Module.finrank ℝ E),
        |(Matrix.of (Gf (I := I) (M := M) D h j z))⁻¹ p pp| ≤ C :=
      fun pp => by
        simpa only [heta] using (hmat (Gf (I := I) (M := M) D h j z) hsymG
          (fun ξ => (hquad ξ).1) (fun ξ => (hquad ξ).2)).2 p pp
    have hVinv : ∀ qq : Fin (Module.finrank ℝ E),
        |(Matrix.of (Gf (I := I) (M := M) D h j z))⁻¹ qq q| ≤ C :=
      fun qq => by
        simpa only [heta] using (hmat (Gf (I := I) (M := M) D h j z) hsymG
          (fun ξ => (hquad ξ).1) (fun ξ => (hquad ξ).2)).2 qq q
    show |Work.Diff.STE.pdR r (fun w : Fin (Module.finrank ℝ E) → ℝ =>
          (Matrix.of (fun i k => Gf (I := I) (M := M) D h j w i k))⁻¹ p q) z| ≤ Kr₁
    have heqfun : (fun w : Fin (Module.finrank ℝ E) → ℝ =>
          (Matrix.of (fun i k => Gf (I := I) (M := M) D h j w i k))⁻¹ p q)
        = (fun w : Fin (Module.finrank ℝ E) → ℝ =>
          (Matrix.of (Gf (I := I) (M := M) D h j w))⁻¹ p q) := by
      funext w; rfl
    rw [heqfun, hstep, abs_neg]
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
    refine le_trans (Finset.sum_le_sum (fun pp _ => Finset.abs_sum_le_sum_abs _ _)) ?_
    have hterm2 : ∀ pp qq : Fin (Module.finrank ℝ E),
        |(Matrix.of (Gf (I := I) (M := M) D h j z))⁻¹ p pp
            * Work.Diff.STE.pdR r (fun y => Gf (I := I) (M := M) D h j y pp qq) z
            * (Matrix.of (Gf (I := I) (M := M) D h j z))⁻¹ qq q| ≤ C * Kdg * C := by
      intro pp qq
      rw [abs_mul, abs_mul]
      exact mul_le_mul (mul_le_mul (hUinv pp) (hjetG pp qq) (abs_nonneg _) hC) (hVinv qq)
        (abs_nonneg _) (mul_nonneg hC hKdg0)
    calc ∑ pp : Fin (Module.finrank ℝ E), ∑ qq : Fin (Module.finrank ℝ E),
            |(Matrix.of (Gf (I := I) (M := M) D h j z))⁻¹ p pp
              * Work.Diff.STE.pdR r (fun y => Gf (I := I) (M := M) D h j y pp qq) z
              * (Matrix.of (Gf (I := I) (M := M) D h j z))⁻¹ qq q|
        ≤ ∑ pp : Fin (Module.finrank ℝ E), ∑ qq : Fin (Module.finrank ℝ E), C * Kdg * C :=
          Finset.sum_le_sum (fun pp _ => Finset.sum_le_sum (fun qq _ => hterm2 pp qq))
      _ = (Module.finrank ℝ E : ℝ) * ((Module.finrank ℝ E : ℝ) * (C * Kdg * C)) := by
          simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      _ = Kr₁ := by rw [hKr₁]; ring

end Work.Diff.STE.B3
