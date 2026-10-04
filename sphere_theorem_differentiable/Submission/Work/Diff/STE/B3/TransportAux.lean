/-
# Auxiliary estimates for the transport of the DeTurck operator (B3, general form)

The fixed-data estimates that `Work.Diff.STE.B3.transport_deTurck_general` and its auxiliary results
need: the enlarged ball on which the frame matrix is invertible, the quadratic forms of the chart
matrices (`G0f`, `Gf`, `Mf`) and their two-sided bounds, and the pointwise jet bounds for the
orthonormal-frame chart matrix.

They live in this separate module so that the auxiliary results of the transport development
(`Diff/STE/B3/window_clamp`, `Diff/STE/B3/gamma_elliptic`, ...) can import them without importing
`Submission.Work.Diff.STE.B3.transport_deTurck_general`, which must in turn import those results.
-/
import Mathlib
import Submission.Work.Diff.STE.B3.Comp
import Submission.Work.Diff.STE.D.Setup
import Submission.Work.Diff.EXT.Basic
import Submission.Work.Diff.STE.B3.TransportDefs
import Submission.Work.Diff.STE.B3.transport_tame_defs
import Submission.Work.Diff.STE.B3.Mf_matrix_eq_of_target
import Submission.Work.Diff.STE.B3.chartMatOf_posDef
import Submission.Work.Diff.STE.B3.det_Mf_metric_ne_zero
import Submission.Work.Diff.STE.B3.quadForm_bounds
import Submission.Work.Diff.STE.B3.CoeffDefs
import Submission.Work.Diff.STE.B3.mat_jet_bound_global
import Submission.Work.Diff.STE.flat.compact_iteratedFDeriv_bound
import Submission.Work.Diff.STE.Comp.pdVec_eq_iteratedFDeriv
import Submission.Work.Diff.STE.B3.contDiff_mul_cutoff
import Submission.Work.Diff.STE.B3.phi_jets_bound
import Submission.Work.Diff.STE.B3.tmGK_eq_Gf

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology BigOperators Matrix
open Bundle ContDiff Set VectorField CovariantDerivative Metric

namespace Work.Diff.STE.B3

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedSectionVars false

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ((⊤ : ENat) : WithTop ENat) M] [T2Space M] [I.Boundaryless]
  {ι₀ : Type*} [Fintype ι₀] {g₀ : Submission.Diff.SMet I M}

noncomputable section

lemma isOpen_flatToE_preimage_target (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (j : ι₀) :
    IsOpen (Work.Diff.STE.flatToE (I := I) (D.x₀ j) ⁻¹' (extChartAt I (D.x₀ j)).target) :=
  (isOpen_extChartAt_target (I := I) (D.x₀ j)).preimage
    ((Work.Diff.STE.contDiff_flatToE (I := I) (x₀ := D.x₀ j)).continuous)

/-- The closed ball of radius `R + δ / 2` is contained in the `δ`-thickening of the closed ball of
radius `R` (the `δ / 2` gives room for the passage from a *closed* ball to an open set). -/
lemma closedBall_add_subset_thickening {k : ℕ} {R δ : ℝ} (hR : 0 ≤ R) (hδ : 0 < δ) :
    Metric.closedBall (0 : Fin k → ℝ) (R + δ / 2) ⊆
      Metric.thickening δ (Metric.closedBall (0 : Fin k → ℝ) R) := by
  intro z hz
  rw [Metric.mem_closedBall, dist_eq_norm, sub_zero] at hz
  rw [Metric.mem_thickening_iff]
  by_cases h : ‖z‖ ≤ R
  · exact ⟨z, by rw [Metric.mem_closedBall, dist_eq_norm, sub_zero]; exact h, by simpa using hδ⟩
  · push_neg at h
    have hzpos : 0 < ‖z‖ := lt_of_le_of_lt hR h
    refine ⟨(R / ‖z‖) • z, ?_, ?_⟩
    · rw [Metric.mem_closedBall, dist_eq_norm, sub_zero, norm_smul, Real.norm_eq_abs,
        abs_of_nonneg (div_nonneg hR (norm_nonneg z)), div_mul_cancel₀ _ hzpos.ne']
    · rw [dist_eq_norm]
      have hsub : z - (R / ‖z‖) • z = (1 - R / ‖z‖) • z := by
        rw [sub_smul, one_smul]
      rw [hsub, norm_smul, Real.norm_eq_abs, abs_of_nonneg (by
        rw [sub_nonneg, div_le_one hzpos]
        exact le_of_lt h), sub_mul, one_mul, div_mul_cancel₀ _ hzpos.ne']
      linarith

/-- **Invertibility of the frame matrix just outside the `2σ`-ball.**  On the closed `2σ`-ball the
frame `e j ·` is `g₀`-orthonormal, so there the background chart matrix `Mf D g₀.inner j ·` is the
identity and its determinant does not vanish; the congruence `Mf = Ff · Gf · Ffᵀ`
(`Work.Diff.STE.B3.Mf_matrix_eq_of_target`) together with the positive definiteness of the
coordinate-frame chart matrix of the *background* metric then turns that into the non-vanishing of
the determinant of `Ff`. -/
lemma det_Ff_ne_zero_of_region (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (j : ι₀)
    {z : Fin (Module.finrank ℝ E) → ℝ}
    (htgt : Work.Diff.STE.flatToE (I := I) (D.x₀ j) z ∈ (extChartAt I (D.x₀ j)).target)
    (hEM : (Matrix.of (Mf (I := I) (M := M) D g₀.inner j z)).det ≠ 0) :
    (Matrix.of (Ff (I := I) (M := M) D j z)).det ≠ 0 := by
  have hdetGf : 0 < (Matrix.of (Gf (I := I) (M := M) D g₀.inner j z)).det :=
    Matrix.PosDef.det_pos (chartMatOf_posDef (I := I) (M := M) g₀.inner (D.x₀ j)
      (fun x u v => g₀.symm x u v) (fun x v hv => g₀.pos x v hv) htgt)
  have hcong := Mf_matrix_eq_of_target (I := I) (M := M) D g₀.inner j z htgt
  have hdet := congrArg Matrix.det hcong
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose] at hdet
  intro h0
  exact hEM (by rw [hdet, h0]; ring)


/-- **The region of the B3 data**: there is `δ₀ > 0` such that for *every* chart `j` the enlarged
ball `‖z‖ ≤ 2 σ j + δ₀` stays inside the chart target and the frame matrix `Ff` is invertible there.
All the fixed data of the construction (the frame, the weight, the background chart data) are smooth
and non-degenerate on that region, uniformly in `j` and uniformly in the section. -/
lemma region_all (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ (j : ι₀) (z : Fin (Module.finrank ℝ E) → ℝ),
      ‖z‖ ≤ 2 * D.σ j + δ₀ →
      (Work.Diff.STE.flatToE (I := I) (D.x₀ j) z ∈ (extChartAt I (D.x₀ j)).target ∧
        (Matrix.of (Ff (I := I) (M := M) D j z)).det ≠ 0) := by
  classical
  have hmargin : ∀ j : ι₀, ∃ δj : ℝ, 0 < δj ∧ ∀ z : Fin (Module.finrank ℝ E) → ℝ,
      ‖z‖ ≤ 2 * D.σ j + δj →
      (Work.Diff.STE.flatToE (I := I) (D.x₀ j) z ∈ (extChartAt I (D.x₀ j)).target ∧
        (Matrix.of (Ff (I := I) (M := M) D j z)).det ≠ 0) := by
    intro j
    have hσ : 0 ≤ 2 * D.σ j := by linarith [D.hσ j]
    have hKc : IsCompact (Metric.closedBall (0 : Fin (Module.finrank ℝ E) → ℝ) (2 * D.σ j)) :=
      isCompact_closedBall _ _
    have hKU : Metric.closedBall (0 : Fin (Module.finrank ℝ E) → ℝ) (2 * D.σ j) ⊆
        Work.Diff.STE.flatToE (I := I) (D.x₀ j) ⁻¹' (extChartAt I (D.x₀ j)).target := by
      intro z hz
      rw [Metric.mem_closedBall, dist_eq_norm, sub_zero] at hz
      exact D.htarget j z hz
    obtain ⟨δ₁, hδ₁pos, hδ₁sub⟩ := hKc.exists_thickening_subset_open
      (isOpen_flatToE_preimage_target (I := I) (M := M) D j) hKU
    obtain ⟨δ₂, hδ₂pos, hδ₂⟩ := det_Mf_metric_ne_zero (I := I) (M := M) (g₀ := g₀) D j
    refine ⟨min (δ₁ / 2) δ₂, lt_min (by linarith) hδ₂pos, fun z hz => ?_⟩
    have hz₁ : ‖z‖ ≤ 2 * D.σ j + δ₁ / 2 :=
      le_trans hz (by linarith [min_le_left (δ₁ / 2) δ₂])
    have hz₂ : ‖z‖ ≤ 2 * D.σ j + δ₂ := le_trans hz (by linarith [min_le_right (δ₁ / 2) δ₂])
    have htgt : Work.Diff.STE.flatToE (I := I) (D.x₀ j) z ∈ (extChartAt I (D.x₀ j)).target :=
      hδ₁sub (closedBall_add_subset_thickening (k := Module.finrank ℝ E) hσ hδ₁pos
        (by rw [Metric.mem_closedBall, dist_eq_norm, sub_zero]; exact hz₁))
    exact ⟨htgt, det_Ff_ne_zero_of_region (I := I) (M := M) D j htgt (hδ₂ z hz₂)⟩
  by_cases hne : Nonempty ι₀
  · haveI : Nonempty ι₀ := hne
    choose δj hδjpos hδj using hmargin
    refine ⟨Finset.univ.inf' Finset.univ_nonempty δj, ?_, ?_⟩
    · exact (Finset.lt_inf'_iff Finset.univ_nonempty).mpr (fun i _ => hδjpos i)
    · intro j z hz
      refine hδj j z ?_
      have hle : Finset.univ.inf' Finset.univ_nonempty δj ≤ δj j :=
        Finset.inf'_le δj (Finset.mem_univ j)
      linarith
  · refine ⟨1, one_pos, ?_⟩
    intro j
    exact (hne ⟨j⟩).elim

/-! ## 2. The quadratic forms of the chart matrices -/

lemma dotProduct_form {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (ξ : Fin n → ℝ) :
    ξ ⬝ᵥ A.mulVec ξ = ∑ p, ∑ q, A p q * ξ p * ξ q := by
  simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]
  refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
  ring

lemma form_le_of_entries {n : ℕ} (A : Fin n → Fin n → ℝ) {C : ℝ} (hCnn : 0 ≤ C)
    (hC : ∀ p q, |A p q| ≤ C) (ξ : Fin n → ℝ) :
    (∑ a, ∑ b, A a b * ξ a * ξ b) ≤ C * (Fintype.card (Fin n) : ℝ) * ∑ i, (ξ i) ^ 2 := by
  have h1 : (∑ a, ∑ b, A a b * ξ a * ξ b) ≤ ∑ a, ∑ b, |A a b| * |ξ a| * |ξ b| := by
    refine Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun b _ => ?_
    calc A a b * ξ a * ξ b ≤ |A a b * ξ a * ξ b| := le_abs_self _
      _ = |A a b| * |ξ a| * |ξ b| := by rw [abs_mul, abs_mul]
  have h2 : (∑ a, ∑ b, |A a b| * |ξ a| * |ξ b|) ≤ ∑ a, ∑ b, C * |ξ a| * |ξ b| := by
    refine Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun b _ => ?_
    have hab : 0 ≤ |ξ a| * |ξ b| := mul_nonneg (abs_nonneg _) (abs_nonneg _)
    calc |A a b| * |ξ a| * |ξ b| = |A a b| * (|ξ a| * |ξ b|) := by ring
      _ ≤ C * (|ξ a| * |ξ b|) := mul_le_mul_of_nonneg_right (hC a b) hab
      _ = C * |ξ a| * |ξ b| := by ring
  have h3 : (∑ a, ∑ b, C * |ξ a| * |ξ b|) = C * (∑ i, |ξ i|) ^ 2 := by
    rw [sq, Finset.sum_mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    ring
  rw [h3] at h2
  have h4 : (∑ i : Fin n, |ξ i|) ^ 2 ≤ (Fintype.card (Fin n) : ℝ) * ∑ i, (ξ i) ^ 2 := by
    have h := sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := fun i : Fin n => |ξ i|)
    have h' : (∑ i : Fin n, |ξ i| ^ 2) = ∑ i : Fin n, (ξ i) ^ 2 :=
      Finset.sum_congr rfl fun i _ => by rw [sq_abs]
    rwa [h', Finset.card_univ] at h
  nlinarith [h1, h2, h4, hCnn]

lemma vecMul_eq_transpose_mulVec {n : ℕ} (F : Matrix (Fin n) (Fin n) ℝ) (v : Fin n → ℝ) :
    Matrix.vecMul v F = Fᵀ.mulVec v := by
  funext j
  simp only [Matrix.vecMul, Matrix.mulVec, Matrix.transpose_apply]
  rw [dotProduct_comm]

lemma sum_sq_transpose_mulVec {n : ℕ} (F : Matrix (Fin n) (Fin n) ℝ) (ξ : Fin n → ℝ) :
    (∑ i, (Fᵀ.mulVec ξ) i ^ 2) = ∑ i, ∑ k, (F * Fᵀ) i k * ξ i * ξ k := by
  have h1 : (∑ i, (Fᵀ.mulVec ξ) i ^ 2) = (Fᵀ.mulVec ξ) ⬝ᵥ (Fᵀ.mulVec ξ) := by
    simp only [dotProduct, sq]
  rw [h1, ← vecMul_eq_transpose_mulVec F ξ,
    ← Matrix.dotProduct_mulVec ξ F (Matrix.vecMul ξ F),
    vecMul_eq_transpose_mulVec F ξ, Matrix.mulVec_mulVec]
  exact dotProduct_form (F * Fᵀ) ξ


/-- The quadratic form of the background chart matrix `G0f D j z` is the `g₀`-square of the
coordinate combination `∑ a, ξ a • ∂_a` of `ξ` in the coordinate frame of the chart at `x₀ j`. -/
lemma G0f_form_eq (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (j : ι₀)
    (z : Fin (Module.finrank ℝ E) → ℝ) (ξ : Fin (Module.finrank ℝ E) → ℝ) :
    (∑ a, ∑ b, G0f (I := I) D j z a b * ξ a * ξ b)
      = g₀.inner (D.pt j z) (∑ a, ξ a • cFrameAt (I := I) (M := M) D j z a)
          (∑ b, ξ b • cFrameAt (I := I) (M := M) D j z b) := by
  have hbil : ∀ a b : Fin (Module.finrank ℝ E), G0f (I := I) D j z a b
      = g₀.inner (D.pt j z) (cFrameAt (I := I) (M := M) D j z a)
          (cFrameAt (I := I) (M := M) D j z b) := fun a b => rfl
  simp only [hbil, map_sum, ContinuousLinearMap.sum_apply, map_smul,
    ContinuousLinearMap.smul_apply, smul_eq_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  ring

/-- The quadratic form of the coordinate-frame chart matrix `Gf D h j z` of a section is the value
of `h` at `D.pt j z` on the coordinate combination `∑ a, ξ a • ∂_a`. -/
lemma Gf_form_eq (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀)
    (h : Work.Diff.STE.Bil (I := I) (M := M)) (j : ι₀)
    (z : Fin (Module.finrank ℝ E) → ℝ) (ξ : Fin (Module.finrank ℝ E) → ℝ) :
    (∑ a, ∑ b, Gf (I := I) (M := M) D h j z a b * ξ a * ξ b)
      = h (D.pt j z) (∑ a, ξ a • cFrameAt (I := I) (M := M) D j z a)
          (∑ b, ξ b • cFrameAt (I := I) (M := M) D j z b) := by
  have hbil : ∀ a b : Fin (Module.finrank ℝ E), Gf (I := I) (M := M) D h j z a b
      = h (D.pt j z) (cFrameAt (I := I) (M := M) D j z a)
          (cFrameAt (I := I) (M := M) D j z b) := fun a b => rfl
  simp only [hbil, map_sum, ContinuousLinearMap.sum_apply, map_smul,
    ContinuousLinearMap.smul_apply, smul_eq_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  ring

/-- **The quadratic form of the orthonormal-frame chart matrix** `Mf D h j z` is the quadratic form
of the coordinate-frame chart matrix `Gf` at the frame-change dual combination `Ffᵀξ`.  This is the
congruence `Mf = Ff · Gf · Ffᵀ` (`Work.Diff.STE.B3.Mf_matrix_eq_of_target`) read as an identity of
quadratic forms. -/
lemma Mf_form_eq (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀)
    (h : Work.Diff.STE.Bil (I := I) (M := M)) (j : ι₀)
    {z : Fin (Module.finrank ℝ E) → ℝ}
    (htgt : Work.Diff.STE.flatToE (I := I) (D.x₀ j) z ∈ (extChartAt I (D.x₀ j)).target)
    (ξ : Fin (Module.finrank ℝ E) → ℝ) :
    (∑ a, ∑ b, Mf (I := I) (M := M) D h j z a b * ξ a * ξ b)
      = ∑ i, ∑ k, Gf (I := I) (M := M) D h j z i k
          * (∑ a, Ff (I := I) (M := M) D j z a i * ξ a)
          * (∑ b, Ff (I := I) (M := M) D j z b k * ξ b) := by
  change (∑ a, ∑ b, Matrix.of (Mf (I := I) (M := M) D h j z) a b * ξ a * ξ b)
      = ∑ i, ∑ k, Matrix.of (Gf (I := I) (M := M) D h j z) i k
          * (∑ a, Matrix.of (Ff (I := I) (M := M) D j z) a i * ξ a)
          * (∑ b, Matrix.of (Ff (I := I) (M := M) D j z) b k * ξ b)
  have hcong := Mf_matrix_eq_of_target (I := I) (M := M) D h j z htgt
  have hkey := dotProduct_form (Matrix.of (Gf (I := I) (M := M) D h j z))
    ((Matrix.of (Ff (I := I) (M := M) D j z))ᵀ.mulVec ξ)
  rw [← dotProduct_form (Matrix.of (Mf (I := I) (M := M) D h j z)) ξ, hcong,
    ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec,
    vecMul_eq_transpose_mulVec, hkey]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => ?_
  simp only [dotProduct, Matrix.mulVec, Matrix.transpose_apply, Matrix.of_apply]

lemma G0f_form_bounds (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (j : ι₀)
    {δ₀ : ℝ}
    (hregion : ∀ z : Fin (Module.finrank ℝ E) → ℝ, ‖z‖ ≤ 2 * D.σ j + δ₀ →
      (Work.Diff.STE.flatToE (I := I) (D.x₀ j) z ∈ (extChartAt I (D.x₀ j)).target ∧
        (Matrix.of (Ff (I := I) (M := M) D j z)).det ≠ 0)) :
    ∃ mlo Mhi : ℝ, 0 < mlo ∧ 0 ≤ Mhi ∧ ∀ z : Fin (Module.finrank ℝ E) → ℝ,
      ‖z‖ ≤ 2 * D.σ j + δ₀ → ∀ ξ : Fin (Module.finrank ℝ E) → ℝ,
      mlo * ∑ i, (ξ i) ^ 2 ≤ (∑ a, ∑ b, G0f (I := I) D j z a b * ξ a * ξ b) ∧
      (∑ a, ∑ b, G0f (I := I) D j z a b * ξ a * ξ b) ≤ Mhi * ∑ i, (ξ i) ^ 2 := by
  classical
  have hKc : IsCompact (Metric.closedBall (0 : Fin (Module.finrank ℝ E) → ℝ)
      (2 * D.σ j + δ₀)) := isCompact_closedBall _ _
  have hmem : ∀ z : Fin (Module.finrank ℝ E) → ℝ, ‖z‖ ≤ 2 * D.σ j + δ₀ →
      z ∈ Metric.closedBall (0 : Fin (Module.finrank ℝ E) → ℝ) (2 * D.σ j + δ₀) := by
    intro z hz
    rw [Metric.mem_closedBall, dist_eq_norm, sub_zero]
    exact hz
  have hcont : ∀ p q : Fin (Module.finrank ℝ E),
      ContinuousOn (fun z : Fin (Module.finrank ℝ E) → ℝ => G0f (I := I) D j z p q)
        (Metric.closedBall (0 : Fin (Module.finrank ℝ E) → ℝ) (2 * D.σ j + δ₀)) := by
    intro p q z hz
    rw [Metric.mem_closedBall, dist_eq_norm, sub_zero] at hz
    have hsm : ContinuousAt (Work.Diff.EXT.chartMatFun (I := I) g₀ (D.x₀ j))
        (Work.Diff.STE.flatToE (I := I) (D.x₀ j) z) :=
      (Work.Diff.EXT.kz_contDiffAt_chartMatFun (I := I) g₀ (D.x₀ j) (hregion z hz).1).continuousAt
    have hev : Continuous (fun A : Work.Diff.EXT.MatE (E := E) => A p q) := by fun_prop
    have h1 : ContinuousAt (fun A : Work.Diff.EXT.MatE (E := E) => A p q)
        (Work.Diff.EXT.chartMatFun (I := I) g₀ (D.x₀ j)
          (Work.Diff.STE.flatToE (I := I) (D.x₀ j) z)) := hev.continuousAt
    have h2 : ContinuousAt (fun w : E =>
        Work.Diff.EXT.chartMatFun (I := I) g₀ (D.x₀ j) w p q)
        (Work.Diff.STE.flatToE (I := I) (D.x₀ j) z) := h1.comp hsm
    exact (h2.comp (Work.Diff.STE.contDiff_flatToE (I := I)
      (x₀ := D.x₀ j)).continuous.continuousAt).continuousWithinAt
  have hpos : ∀ z ∈ Metric.closedBall (0 : Fin (Module.finrank ℝ E) → ℝ) (2 * D.σ j + δ₀),
      ∀ ξ : Fin (Module.finrank ℝ E) → ℝ, ξ ≠ 0 →
        0 < ∑ p, ∑ q, G0f (I := I) D j z p q * ξ p * ξ q := by
    intro z hz ξ hξ
    rw [Metric.mem_closedBall, dist_eq_norm, sub_zero] at hz
    have hpd := chartMatOf_posDef (I := I) (M := M) g₀.inner (D.x₀ j)
      (fun x u v => g₀.symm x u v) (fun x v hv => g₀.pos x v hv) (hregion z hz).1
    have h2 := (Matrix.posDef_iff_dotProduct_mulVec.mp hpd).2 hξ
    have hfun : G0f (I := I) D j z = Work.Diff.STE.D.chartMatOf (I := I) (M := M) g₀.inner
        (D.x₀ j) (Work.Diff.STE.flatToE (I := I) (D.x₀ j) z) := rfl
    simpa only [hfun, dotProduct_form, Matrix.of_apply, star_trivial] using h2
  obtain ⟨c, C, hc, hCnn, hlow, hentry⟩ := quadForm_bounds
    (Metric.closedBall (0 : Fin (Module.finrank ℝ E) → ℝ) (2 * D.σ j + δ₀)) hKc
    (fun z => Matrix.of (G0f (I := I) D j z)) hcont hpos
  obtain ⟨Cent, hCentnn, hCent⟩ := exists_abs_entry_bound
    (Metric.closedBall (0 : Fin (Module.finrank ℝ E) → ℝ) (2 * D.σ j + δ₀)) hKc
    (fun z => Matrix.of (G0f (I := I) D j z)) hcont
  refine ⟨c, Cent * (Fintype.card (Fin (Module.finrank ℝ E)) : ℝ), hc, by positivity,
    fun z hz ξ => ⟨hlow z (hmem z hz) ξ, ?_⟩⟩
  have hup := form_le_of_entries (fun a b => G0f (I := I) D j z a b) hCentnn
    (fun p q => by simpa only [Matrix.of_apply] using hCent z (hmem z hz) p q) ξ
  calc (∑ a, ∑ b, G0f (I := I) D j z a b * ξ a * ξ b)
      ≤ Cent * (Fintype.card (Fin (Module.finrank ℝ E)) : ℝ) * ∑ i, (ξ i) ^ 2 := hup
    _ = (Cent * (Fintype.card (Fin (Module.finrank ℝ E)) : ℝ)) * ∑ i, (ξ i) ^ 2 := by ring

lemma FfT_form_bounds (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (j : ι₀)
    {δ₀ : ℝ}
    (hregion : ∀ z : Fin (Module.finrank ℝ E) → ℝ, ‖z‖ ≤ 2 * D.σ j + δ₀ →
      (Work.Diff.STE.flatToE (I := I) (D.x₀ j) z ∈ (extChartAt I (D.x₀ j)).target ∧
        (Matrix.of (Ff (I := I) (M := M) D j z)).det ≠ 0)) :
    ∃ ε Cf : ℝ, 0 < ε ∧ 0 ≤ Cf ∧ ∀ z : Fin (Module.finrank ℝ E) → ℝ,
      ‖z‖ ≤ 2 * D.σ j + δ₀ → ∀ ξ : Fin (Module.finrank ℝ E) → ℝ,
      ε * ∑ i, (ξ i) ^ 2 ≤
        ∑ i, (((Matrix.of (Ff (I := I) (M := M) D j z))ᵀ).mulVec ξ) i ^ 2 ∧
      (∑ i, (((Matrix.of (Ff (I := I) (M := M) D j z))ᵀ).mulVec ξ) i ^ 2)
        ≤ Cf * ∑ i, (ξ i) ^ 2 := by
  classical
  have hKc : IsCompact (Metric.closedBall (0 : Fin (Module.finrank ℝ E) → ℝ)
      (2 * D.σ j + δ₀)) := isCompact_closedBall _ _
  have hmem : ∀ z : Fin (Module.finrank ℝ E) → ℝ, ‖z‖ ≤ 2 * D.σ j + δ₀ →
      z ∈ Metric.closedBall (0 : Fin (Module.finrank ℝ E) → ℝ) (2 * D.σ j + δ₀) := by
    intro z hz
    rw [Metric.mem_closedBall, dist_eq_norm, sub_zero]
    exact hz
  have hcont : ∀ p q : Fin (Module.finrank ℝ E),
      ContinuousOn (fun z : Fin (Module.finrank ℝ E) → ℝ =>
        (Matrix.of (Ff (I := I) (M := M) D j z)
          * (Matrix.of (Ff (I := I) (M := M) D j z))ᵀ) p q)
        (Metric.closedBall (0 : Fin (Module.finrank ℝ E) → ℝ) (2 * D.σ j + δ₀)) := by
    intro p q z hz
    rw [Metric.mem_closedBall, dist_eq_norm, sub_zero] at hz
    have hFf : ∀ a i : Fin (Module.finrank ℝ E),
        ContDiffAt ℝ ∞ (fun w : Fin (Module.finrank ℝ E) → ℝ =>
          Ff (I := I) (M := M) D j w a i) z :=
      fun a i => Work.Diff.STE.B3.Ff_contDiffAt (I := I) (M := M) D j a i (hregion z hz).1
    have h2 : (fun w : Fin (Module.finrank ℝ E) → ℝ =>
          (Matrix.of (Ff (I := I) (M := M) D j w)
            * (Matrix.of (Ff (I := I) (M := M) D j w))ᵀ) p q)
        = fun w => ∑ a, Ff (I := I) (M := M) D j w p a * Ff (I := I) (M := M) D j w q a := by
      funext w
      rw [Matrix.mul_apply]
      refine Finset.sum_congr rfl fun a _ => ?_
      simp only [Matrix.transpose_apply, Matrix.of_apply]
    rw [h2]
    exact (ContDiffAt.sum (s := Finset.univ) fun a _ => (hFf p a).mul (hFf q a)).continuousAt.continuousWithinAt
  have hpos : ∀ z ∈ Metric.closedBall (0 : Fin (Module.finrank ℝ E) → ℝ) (2 * D.σ j + δ₀),
      ∀ ξ : Fin (Module.finrank ℝ E) → ℝ, ξ ≠ 0 →
        0 < ∑ p, ∑ q, (Matrix.of (Ff (I := I) (M := M) D j z)
          * (Matrix.of (Ff (I := I) (M := M) D j z))ᵀ) p q * ξ p * ξ q := by
    intro z hz ξ hξ
    rw [Metric.mem_closedBall, dist_eq_norm, sub_zero] at hz
    have hdet : (Matrix.of (Ff (I := I) (M := M) D j z)).det ≠ 0 := (hregion z hz).2
    have hdetT : IsUnit ((Matrix.of (Ff (I := I) (M := M) D j z))ᵀ).det := by
      rw [Matrix.det_transpose]
      exact isUnit_iff_ne_zero.mpr hdet
    have hinj : ∀ v : Fin (Module.finrank ℝ E) → ℝ,
        ((Matrix.of (Ff (I := I) (M := M) D j z))ᵀ).mulVec v = 0 → v = 0 := by
      intro v h0
      have h1 : (((Matrix.of (Ff (I := I) (M := M) D j z))ᵀ)⁻¹).mulVec
          (((Matrix.of (Ff (I := I) (M := M) D j z))ᵀ).mulVec v) = v := by
        rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hdetT, Matrix.one_mulVec]
      rw [h0, Matrix.mulVec_zero] at h1
      exact h1.symm
    have hw : ((Matrix.of (Ff (I := I) (M := M) D j z))ᵀ).mulVec ξ ≠ 0 :=
      fun h0 => hξ (hinj ξ h0)
    have hsq : 0 < ∑ i, (((Matrix.of (Ff (I := I) (M := M) D j z))ᵀ).mulVec ξ) i ^ 2 := by
      by_contra hc
      push_neg at hc
      have hsum : ∑ i, (((Matrix.of (Ff (I := I) (M := M) D j z))ᵀ).mulVec ξ) i ^ 2 ≤ 0 := hc
      have hz0 : ∀ i, (((Matrix.of (Ff (I := I) (M := M) D j z))ᵀ).mulVec ξ) i = 0 := by
        intro i
        have h1 : (((Matrix.of (Ff (I := I) (M := M) D j z))ᵀ).mulVec ξ) i ^ 2 ≤ 0 :=
          le_trans (Finset.single_le_sum
            (f := fun i' => (((Matrix.of (Ff (I := I) (M := M) D j z))ᵀ).mulVec ξ) i' ^ 2)
            (fun i' _ => sq_nonneg _) (Finset.mem_univ i)) hsum
        exact sq_eq_zero_iff.mp (le_antisymm h1 (sq_nonneg _))
      exact hw (funext hz0)
    rw [← sum_sq_transpose_mulVec (Matrix.of (Ff (I := I) (M := M) D j z)) ξ]
    exact hsq
  obtain ⟨c, C, hc, hCnn, hlow, hentry⟩ := quadForm_bounds
    (Metric.closedBall (0 : Fin (Module.finrank ℝ E) → ℝ) (2 * D.σ j + δ₀)) hKc
    (fun z => Matrix.of (Ff (I := I) (M := M) D j z)
      * (Matrix.of (Ff (I := I) (M := M) D j z))ᵀ) hcont hpos
  obtain ⟨Cent, hCentnn, hCent⟩ := exists_abs_entry_bound
    (Metric.closedBall (0 : Fin (Module.finrank ℝ E) → ℝ) (2 * D.σ j + δ₀)) hKc
    (fun z => Matrix.of (Ff (I := I) (M := M) D j z)
      * (Matrix.of (Ff (I := I) (M := M) D j z))ᵀ) hcont
  refine ⟨c, Cent * (Fintype.card (Fin (Module.finrank ℝ E)) : ℝ), hc, by positivity,
    fun z hz ξ => ⟨?_, ?_⟩⟩
  · rw [sum_sq_transpose_mulVec]
    exact hlow z (hmem z hz) ξ
  · rw [sum_sq_transpose_mulVec]
    have hup := form_le_of_entries (fun a b => (Matrix.of (Ff (I := I) (M := M) D j z)
      * (Matrix.of (Ff (I := I) (M := M) D j z))ᵀ) a b) hCentnn
      (fun p q => by simpa only [Matrix.of_apply] using hCent z (hmem z hz) p q) ξ
    calc (∑ a, ∑ b, (Matrix.of (Ff (I := I) (M := M) D j z)
          * (Matrix.of (Ff (I := I) (M := M) D j z))ᵀ) a b * ξ a * ξ b)
        ≤ Cent * (Fintype.card (Fin (Module.finrank ℝ E)) : ℝ) * ∑ i, (ξ i) ^ 2 := hup
      _ = (Cent * (Fintype.card (Fin (Module.finrank ℝ E)) : ℝ)) * ∑ i, (ξ i) ^ 2 := by ring

lemma Gf_loewner (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀)
    (h : Work.Diff.STE.Bil (I := I) (M := M)) (j : ι₀) {δ₀ δ : ℝ}
    (hδ : δ ≤ δ₀) {lam K mlo Mhi : ℝ} (hlam : 0 < lam) (hK : 0 < K)
    (hell : ∀ (x : M) (v : TangentSpace I x), lam * g₀.inner x v v ≤ h x v v)
    (hub : ∀ (x : M) (v : TangentSpace I x), h x v v ≤ K * g₀.inner x v v)
    (hlo : ∀ z : Fin (Module.finrank ℝ E) → ℝ, ‖z‖ ≤ 2 * D.σ j + δ₀ →
      ∀ ξ : Fin (Module.finrank ℝ E) → ℝ,
      mlo * ∑ i, (ξ i) ^ 2 ≤ ∑ a, ∑ b, G0f (I := I) D j z a b * ξ a * ξ b)
    (hhi : ∀ z : Fin (Module.finrank ℝ E) → ℝ, ‖z‖ ≤ 2 * D.σ j + δ₀ →
      ∀ ξ : Fin (Module.finrank ℝ E) → ℝ,
      (∑ a, ∑ b, G0f (I := I) D j z a b * ξ a * ξ b) ≤ Mhi * ∑ i, (ξ i) ^ 2) :
    ∀ z : Fin (Module.finrank ℝ E) → ℝ, ‖z‖ ≤ 2 * D.σ j + δ → ∀ ξ : Fin (Module.finrank ℝ E) → ℝ,
      (lam * mlo) * ∑ i, (ξ i) ^ 2 ≤ (∑ a, ∑ b, Gf (I := I) (M := M) D h j z a b * ξ a * ξ b) ∧
      (∑ a, ∑ b, Gf (I := I) (M := M) D h j z a b * ξ a * ξ b) ≤ (K * Mhi) * ∑ i, (ξ i) ^ 2 := by
  intro z hz ξ
  have hz' : ‖z‖ ≤ 2 * D.σ j + δ₀ := le_trans hz (by linarith)
  have h1 := hlo z hz' ξ
  have h2 := hhi z hz' ξ
  have h3 := hell (D.pt j z) (∑ a, ξ a • cFrameAt (I := I) (M := M) D j z a)
  have h4 := hub (D.pt j z) (∑ a, ξ a • cFrameAt (I := I) (M := M) D j z a)
  rw [Gf_form_eq]
  rw [G0f_form_eq] at h1 h2
  constructor
  · calc (lam * mlo) * ∑ i, (ξ i) ^ 2 = lam * (mlo * ∑ i, (ξ i) ^ 2) := by ring
      _ ≤ lam * (g₀.inner (D.pt j z) (∑ a, ξ a • cFrameAt (I := I) (M := M) D j z a)
            (∑ b, ξ b • cFrameAt (I := I) (M := M) D j z b)) :=
          mul_le_mul_of_nonneg_left h1 hlam.le
      _ ≤ h (D.pt j z) (∑ a, ξ a • cFrameAt (I := I) (M := M) D j z a)
            (∑ b, ξ b • cFrameAt (I := I) (M := M) D j z b) := h3
  · calc h (D.pt j z) (∑ a, ξ a • cFrameAt (I := I) (M := M) D j z a)
          (∑ b, ξ b • cFrameAt (I := I) (M := M) D j z b)
        ≤ K * (g₀.inner (D.pt j z) (∑ a, ξ a • cFrameAt (I := I) (M := M) D j z a)
            (∑ b, ξ b • cFrameAt (I := I) (M := M) D j z b)) := h4
      _ ≤ K * (Mhi * ∑ i, (ξ i) ^ 2) := mul_le_mul_of_nonneg_left h2 hK.le
      _ = (K * Mhi) * ∑ i, (ξ i) ^ 2 := by ring

lemma Mf_loewner (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀)
    (h : Work.Diff.STE.Bil (I := I) (M := M)) (j : ι₀) {δ₀ : ℝ}
    (hregion : ∀ z : Fin (Module.finrank ℝ E) → ℝ, ‖z‖ ≤ 2 * D.σ j + δ₀ →
      (Work.Diff.STE.flatToE (I := I) (D.x₀ j) z ∈ (extChartAt I (D.x₀ j)).target ∧
        (Matrix.of (Ff (I := I) (M := M) D j z)).det ≠ 0))
    {mlo ε : ℝ} (hmlo : 0 ≤ mlo) (hε : 0 ≤ ε)
    (hGf : ∀ z : Fin (Module.finrank ℝ E) → ℝ, ‖z‖ ≤ 2 * D.σ j + δ₀ →
      ∀ w : Fin (Module.finrank ℝ E) → ℝ,
      mlo * ∑ i, (w i) ^ 2 ≤ ∑ i, ∑ k, Gf (I := I) (M := M) D h j z i k * w i * w k)
    (hFf : ∀ z : Fin (Module.finrank ℝ E) → ℝ, ‖z‖ ≤ 2 * D.σ j + δ₀ →
      ∀ ξ : Fin (Module.finrank ℝ E) → ℝ,
      ε * ∑ i, (ξ i) ^ 2 ≤
        ∑ i, (((Matrix.of (Ff (I := I) (M := M) D j z))ᵀ).mulVec ξ) i ^ 2) :
    ∀ z : Fin (Module.finrank ℝ E) → ℝ, ‖z‖ ≤ 2 * D.σ j + δ₀ →
      ∀ ξ : Fin (Module.finrank ℝ E) → ℝ,
      (mlo * ε) * ∑ i, (ξ i) ^ 2 ≤
        ∑ a, ∑ b, Mf (I := I) (M := M) D h j z a b * ξ a * ξ b := by
  intro z hz ξ
  rw [Mf_form_eq (I := I) (M := M) D h j (hregion z hz).1 ξ]
  have hw := hGf z hz (fun i => ∑ a, Ff (I := I) (M := M) D j z a i * ξ a)
  have hεξ := hFf z hz ξ
  have hbridge : (∑ i, (((Matrix.of (Ff (I := I) (M := M) D j z))ᵀ).mulVec ξ) i ^ 2)
      = ∑ i, (∑ a, Ff (I := I) (M := M) D j z a i * ξ a) ^ 2 := by
    refine Finset.sum_congr rfl fun i _ => ?_
    congr 1
  rw [hbridge] at hεξ
  nlinarith [hw, hεξ, hmlo, hε]



/-! ## Elementary matrix lemmas for the ellipticity of the clamped inverse -/

/-- The `∑∑` form of a matrix quadratic form is the matrix-vector pairing. -/
private lemma sum_sum_mul_eq_dotProduct {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (x y : Fin n → ℝ) :
    (∑ i, ∑ j, A i j * x i * y j) = x ⬝ᵥ (A *ᵥ y) := by
  simp only [dotProduct, Matrix.mulVec_apply_eq_sum, Finset.mul_sum]
  exact Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => by ring))

/-- Nonnegativity of the quadratic form of a positive semidefinite matrix, in `∑∑` form. -/
private lemma posSemidef_sum_nonneg {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.PosSemidef)
    (x : Fin n → ℝ) : 0 ≤ ∑ i, ∑ j, A i j * x i * x j := by
  have h := hA.dotProduct_mulVec_nonneg x
  simpa only [star_trivial, ← sum_sum_mul_eq_dotProduct A x x] using h

/-- Cauchy–Schwarz for a positive semidefinite quadratic form. -/
private lemma posSemidef_cauchy_schwarz {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : A.PosSemidef) (x y : Fin n → ℝ) :
    (x ⬝ᵥ (A *ᵥ y)) ^ 2 ≤ (x ⬝ᵥ (A *ᵥ x)) * (y ⬝ᵥ (A *ᵥ y)) := by
  have hsym : ∀ u v : Fin n → ℝ, u ⬝ᵥ (A *ᵥ v) = v ⬝ᵥ (A *ᵥ u) := fun u v => by
    simpa only [star_trivial] using hA.isHermitian.star_dotProduct_mulVec_comm u v
  have hexp : ∀ t : ℝ, (x + t • y) ⬝ᵥ (A *ᵥ (x + t • y))
      = (y ⬝ᵥ (A *ᵥ y)) * (t * t) + ((x ⬝ᵥ (A *ᵥ y)) + (y ⬝ᵥ (A *ᵥ x))) * t
        + (x ⬝ᵥ (A *ᵥ x)) := by
    intro t
    simp only [Matrix.mulVec_add, Matrix.mulVec_smul, add_dotProduct, smul_dotProduct,
      dotProduct_add, dotProduct_smul, smul_eq_mul]
    ring
  have hquad : ∀ t : ℝ, 0 ≤ (y ⬝ᵥ (A *ᵥ y)) * (t * t)
      + ((x ⬝ᵥ (A *ᵥ y)) + (y ⬝ᵥ (A *ᵥ x))) * t + (x ⬝ᵥ (A *ᵥ x)) := by
    intro t
    rw [← hexp t]
    simpa only [star_trivial] using hA.dotProduct_mulVec_nonneg (x + t • y)
  have hd := discrim_le_zero (a := y ⬝ᵥ (A *ᵥ y))
    (b := (x ⬝ᵥ (A *ᵥ y)) + (y ⬝ᵥ (A *ᵥ x))) (c := x ⬝ᵥ (A *ᵥ x)) hquad
  rw [discrim] at hd
  have hs := hsym x y
  rw [hs] at hd ⊢
  nlinarith [hd]

/-- **Lower bound for the quadratic form of the inverse matrix**, from an upper bound on the
quadratic form of the matrix itself (Cauchy–Schwarz for the positive definite form). -/
private lemma inv_quadForm_lower {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef)
    (β : ℝ) (hβ : 0 < β)
    (hup : ∀ w : Fin n → ℝ, ∑ i, ∑ j, A i j * w i * w j ≤ β * ∑ i, (w i) ^ 2) :
    ∀ ξ : Fin n → ℝ, β⁻¹ * ∑ i, (ξ i) ^ 2 ≤ ∑ i, ∑ j, (A⁻¹) i j * ξ i * ξ j := by
  intro ξ
  have hAA : A * A⁻¹ = 1 :=
    Matrix.mul_nonsing_inv A ((Matrix.isUnit_iff_isUnit_det (A := A)).mp hA.isUnit)
  have hAv : A *ᵥ (A⁻¹ *ᵥ ξ) = ξ := by
    rw [Matrix.mulVec_mulVec, hAA, Matrix.one_mulVec]
  have hcs := posSemidef_cauchy_schwarz hA.posSemidef ξ (A⁻¹ *ᵥ ξ)
  rw [hAv] at hcs
  rw [dotProduct_comm (A⁻¹ *ᵥ ξ) ξ] at hcs
  have h1 : ξ ⬝ᵥ ξ = ∑ i, (ξ i) ^ 2 := by simp only [dotProduct, pow_two]
  have h2 : ξ ⬝ᵥ (A *ᵥ ξ) = ∑ i, ∑ j, A i j * ξ i * ξ j :=
    (sum_sum_mul_eq_dotProduct A ξ ξ).symm
  have h3 : ξ ⬝ᵥ (A⁻¹ *ᵥ ξ) = ∑ i, ∑ j, (A⁻¹) i j * ξ i * ξ j :=
    (sum_sum_mul_eq_dotProduct A⁻¹ ξ ξ).symm
  rw [h1, h2, h3] at hcs
  have hSnn : 0 ≤ ∑ i, (ξ i) ^ 2 := Finset.sum_nonneg (fun i _ => sq_nonneg (ξ i))
  have hWnn : 0 ≤ ∑ i, ∑ j, (A⁻¹) i j * ξ i * ξ j :=
    posSemidef_sum_nonneg hA.posSemidef.inv ξ
  have hupξ := hup ξ
  rcases eq_or_lt_of_le hSnn with hS0 | hSpos
  · rw [← hS0, mul_zero]
    exact hWnn
  · have hstep : (∑ i, (ξ i) ^ 2) * (∑ i, (ξ i) ^ 2)
        ≤ (∑ i, (ξ i) ^ 2) * (β * (∑ i, ∑ j, (A⁻¹) i j * ξ i * ξ j)) := by
      calc (∑ i, (ξ i) ^ 2) * (∑ i, (ξ i) ^ 2) = (∑ i, (ξ i) ^ 2) ^ 2 := by ring
        _ ≤ (∑ i, ∑ j, A i j * ξ i * ξ j) * (∑ i, ∑ j, (A⁻¹) i j * ξ i * ξ j) := hcs
        _ ≤ (β * ∑ i, (ξ i) ^ 2) * (∑ i, ∑ j, (A⁻¹) i j * ξ i * ξ j) :=
            mul_le_mul_of_nonneg_right hupξ hWnn
        _ = (∑ i, (ξ i) ^ 2) * (β * (∑ i, ∑ j, (A⁻¹) i j * ξ i * ξ j)) := by ring
    have h2' : ∑ i, (ξ i) ^ 2 ≤ β * (∑ i, ∑ j, (A⁻¹) i j * ξ i * ξ j) :=
      (mul_le_mul_iff_of_pos_left hSpos).mp hstep
    rwa [inv_mul_le_iff₀ hβ]

/-- The quadratic form is additive in the matrix. -/
private lemma qform_add {n : ℕ} (B C : Matrix (Fin n) (Fin n) ℝ) (ξ : Fin n → ℝ) :
    ∑ p, ∑ q, (B + C) p q * ξ p * ξ q
      = (∑ p, ∑ q, B p q * ξ p * ξ q) + ∑ p, ∑ q, C p q * ξ p * ξ q := by
  simp only [Matrix.add_apply, add_mul, Finset.sum_add_distrib]

/-- The quadratic form is homogeneous in the matrix. -/
private lemma qform_smul {n : ℕ} (s : ℝ) (B : Matrix (Fin n) (Fin n) ℝ) (ξ : Fin n → ℝ) :
    ∑ p, ∑ q, (s • B) p q * ξ p * ξ q = s * (∑ p, ∑ q, B p q * ξ p * ξ q) := by
  simp only [Matrix.smul_apply, smul_eq_mul]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun q _ => ?_
  ring

/-- The quadratic form of the identity matrix is the squared norm of the vector. -/
private lemma qform_one {n : ℕ} (ξ : Fin n → ℝ) :
    ∑ p, ∑ q, (1 : Matrix (Fin n) (Fin n) ℝ) p q * ξ p * ξ q = ∑ i, (ξ i) ^ 2 := by
  rw [sum_sum_mul_eq_dotProduct (1 : Matrix (Fin n) (Fin n) ℝ) ξ ξ, Matrix.one_mulVec]
  simp only [dotProduct, pow_two]

/-- The purely arithmetic comparison behind the clamped-inverse bound: for `t ∈ [0,1]` the convex
combination `(1 - t) · 1 + t · x` is at least `min x 1`. -/
private lemma min_le_of_convex_combo {t x : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    min x 1 ≤ 1 + t * (x - 1) := by
  rcases le_total x 1 with h | h
  · rw [min_eq_left h]
    have h1 : (1 : ℝ) * (x - 1) ≤ t * (x - 1) := mul_le_mul_of_nonpos_right ht1 (by linarith)
    linarith
  · rw [min_eq_right h]
    have h1 : 0 ≤ t * (x - 1) := mul_nonneg ht0 (by linarith)
    linarith

/-- **Ellipticity of the clamped inverse.**  If `A` is positive definite with quadratic form
bounded above by `C · ‖·‖²`, then the clamped inverse `tmInv a b ha hab A` is `min C⁻¹ 1`-elliptic,
uniformly in the clamp parameters. -/
private lemma tmInv_qform_lower {n : ℕ} (a b : ℝ) (ha : 0 < a) (hab : a < b)
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef) (C : ℝ) (hC : 0 < C)
    (hup : ∀ ξ : Fin n → ℝ, ∑ p, ∑ q, A p q * ξ p * ξ q ≤ C * ∑ i, (ξ i) ^ 2) :
    ∀ ξ : Fin n → ℝ, min C⁻¹ 1 * ∑ i, (ξ i) ^ 2 ≤
      ∑ p, ∑ q, tmInv a b ha hab A p q * ξ p * ξ q := by
  intro ξ
  have hinv := inv_quadForm_lower A hA C hC hup ξ
  have ht0 : 0 ≤ tmClampBump (n := n) a b ha hab A.det := ContDiffBump.nonneg _
  have ht1 : tmClampBump (n := n) a b ha hab A.det ≤ 1 := ContDiffBump.le_one _
  have hS : 0 ≤ ∑ i, (ξ i) ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
  have hkey : ∑ p, ∑ q, tmInv a b ha hab A p q * ξ p * ξ q
      = tmClampBump (n := n) a b ha hab A.det
          * (∑ p, ∑ q, A⁻¹ p q * ξ p * ξ q)
        + (1 - tmClampBump (n := n) a b ha hab A.det) * ∑ i, (ξ i) ^ 2 := by
    unfold tmInv
    rw [qform_add, qform_smul, qform_smul, qform_one]
  rw [hkey]
  have hmain : min C⁻¹ 1 * ∑ i, (ξ i) ^ 2
      ≤ (1 + tmClampBump (n := n) a b ha hab A.det * (C⁻¹ - 1)) * ∑ i, (ξ i) ^ 2 :=
    mul_le_mul_of_nonneg_right (min_le_of_convex_combo ht0 ht1) hS
  have hstep : (1 + tmClampBump (n := n) a b ha hab A.det * (C⁻¹ - 1)) * ∑ i, (ξ i) ^ 2
      = tmClampBump (n := n) a b ha hab A.det * (C⁻¹ * ∑ i, (ξ i) ^ 2)
        + (1 - tmClampBump (n := n) a b ha hab A.det) * ∑ i, (ξ i) ^ 2 := by ring
  have hle : tmClampBump (n := n) a b ha hab A.det * (C⁻¹ * ∑ i, (ξ i) ^ 2)
      ≤ tmClampBump (n := n) a b ha hab A.det
        * (∑ p, ∑ q, A⁻¹ p q * ξ p * ξ q) :=
    mul_le_mul_of_nonneg_left hinv ht0
  linarith

/-- **Uniform ellipticity of the clamped inverse family `γ z p q = tmGKi (z, Mf z) p q`.**

This is the coefficient family of the transport identity
(`Work.Diff.STE.B3.transport_identity` uses exactly `tmGKi (z, Mf z) * ∂∂ (R j h)`), and the
transport result needs it uniformly elliptic on the enlarged ball `‖z‖ ≤ 2 σ j + δ₀`, with a constant
independent of the section `h` *and* of the clamp parameters `a, b`.

ROUTE (both reviewers).  `tmGK z V = Finvf z * V * Finvf zᵀ` and `tmGK_eq_Gf` (proved) gives
`tmGK z (Mf …) = Matrix.of (Gf …)` on the region, where `Gf` is the coordinate-frame chart matrix of
`h`.  From `hsym`, `hell` and `hub`, `lam • G0f ≤ Gf ≤ K • G0f` as quadratic forms (use
`Gf_form_eq`, `G0f_form_eq` and the proved `Work.Diff.STE.B3.G0f_form_bounds` in the importing
module, which supplies *uniform* constants `mlo ≤ Mhi` with `mlo • 1 ≤ G0f ≤ Mhi • 1` on
`‖z‖ ≤ 2 σ j + δ₀`).  Hence `Gf ⪯ (K * Mhi) • 1`, and the completing-the-square identity
`ξᵀA⁻¹ξ = 2 ξᵀη − ηᵀAη + (η − A⁻¹ξ)ᵀA(η − A⁻¹ξ)` (for symmetric `A`, with `η := ξ/C`) gives
`ξᵀ(Gf)⁻¹ξ ≥ ‖ξ‖²/C` for `C := K * Mhi`.  Finally
`tmInv a b ha hab A = t • A⁻¹ + (1 - t) • 1` with `t := tmClampBump a b ha hab A.det ∈ [0,1]`
(`ContDiffBump.nonneg`, `ContDiffBump.le_one`), and both terms are `≥ min (1/C) 1 • 1`, so
`c := min (1/C) 1` works — uniformly in `a, b, h, j, z`. -/
theorem gamma_elliptic_ta
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ((⊤ : ENat) : WithTop ENat) M] [T2Space M] [I.Boundaryless]
    {ι₀ : Type*} [Fintype ι₀] {g₀ : Submission.Diff.SMet I M}
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀)
    (lam K : ℝ) (hlam : 0 < lam) (hK : 0 < K) (j : ι₀) (δ₀ : ℝ) :
    ∃ c : ℝ, 0 < c ∧
      ∀ (a b : ℝ) (ha : 0 < a) (hab : a < b)
        (h : Work.Diff.STE.Bil (I := I) (M := M))
        (hsym : ∀ (x : M) (u v : TangentSpace I x), h x u v = h x v u)
        (hell : ∀ (x : M) (v : TangentSpace I x), lam * g₀.inner x v v ≤ h x v v)
        (hub : ∀ (x : M) (v : TangentSpace I x), h x v v ≤ K * g₀.inner x v v)
        (hregion : ∀ z : Fin (Module.finrank ℝ E) → ℝ, ‖z‖ ≤ 2 * D.σ j + δ₀ →
          (Work.Diff.STE.flatToE (I := I) (D.x₀ j) z ∈ (extChartAt I (D.x₀ j)).target ∧
            (Matrix.of (Ff (I := I) (M := M) D j z)).det ≠ 0)),
        ∀ z : Fin (Module.finrank ℝ E) → ℝ, ‖z‖ ≤ 2 * D.σ j + δ₀ →
          ∀ ξ : Fin (Module.finrank ℝ E) → ℝ,
          c * ∑ i, (ξ i) ^ 2 ≤ ∑ p, ∑ q,
            (Work.Diff.STE.B3.tmGKi (I := I) (M := M) D j a b ha hab z
              (Mf (I := I) (M := M) D h j z)) p q * ξ p * ξ q := by
  classical
  by_cases hreg : (∀ z : Fin (Module.finrank ℝ E) → ℝ, ‖z‖ ≤ 2 * D.σ j + δ₀ →
      (Work.Diff.STE.flatToE (I := I) (D.x₀ j) z ∈ (extChartAt I (D.x₀ j)).target ∧
        (Matrix.of (Ff (I := I) (M := M) D j z)).det ≠ 0))
  · obtain ⟨mlo, Mhi, _hmlo, hMhi, hG0⟩ := G0f_form_bounds (I := I) (M := M) D j hreg
    have hCpos : 0 < K * Mhi + 1 := by
      have : 0 ≤ K * Mhi := mul_nonneg hK.le hMhi
      linarith
    refine ⟨min (K * Mhi + 1)⁻¹ 1, lt_min (inv_pos.mpr hCpos) one_pos, ?_⟩
    intro a b ha hab h hsym hell hub hregion z hz ξ
    have hpos : ∀ (x : M) (v : TangentSpace I x), v ≠ 0 → 0 < h x v v := by
      intro x v hv
      have h1 := hell x v
      have h2 : 0 < lam * g₀.inner x v v := mul_pos hlam (g₀.pos x v hv)
      linarith
    obtain ⟨htgt, hdetFf⟩ := hregion z hz
    have hpd : (Matrix.of (Gf (I := I) (M := M) D h j z)).PosDef :=
      chartMatOf_posDef (I := I) (M := M) h (D.x₀ j) hsym hpos htgt
    have hwin : ∀ w : Fin (Module.finrank ℝ E) → ℝ,
        (∑ p, ∑ q, Gf (I := I) (M := M) D h j z p q * w p * w q)
          ≤ (K * Mhi) * ∑ i, (w i) ^ 2 := fun w =>
      (Gf_loewner (I := I) (M := M) D h j (δ₀ := δ₀) (δ := δ₀) le_rfl hlam hK hell hub
        (fun z hz ξ => (hG0 z hz ξ).1) (fun z hz ξ => (hG0 z hz ξ).2) z hz w).2
    have hup : ∀ w : Fin (Module.finrank ℝ E) → ℝ,
        ∑ p, ∑ q, (Matrix.of (Gf (I := I) (M := M) D h j z)) p q * w p * w q
          ≤ (K * Mhi + 1) * ∑ i, (w i) ^ 2 := by
      intro w
      have h1 : (∑ p, ∑ q, (Matrix.of (Gf (I := I) (M := M) D h j z)) p q * w p * w q)
          = ∑ p, ∑ q, Gf (I := I) (M := M) D h j z p q * w p * w q := rfl
      rw [h1]
      have hS : 0 ≤ ∑ i, (w i) ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
      have h3 : (K * Mhi) * ∑ i, (w i) ^ 2 ≤ (K * Mhi + 1) * ∑ i, (w i) ^ 2 :=
        mul_le_mul_of_nonneg_right (by linarith) hS
      linarith [hwin w]
    have hbound := tmInv_qform_lower a b ha hab (Matrix.of (Gf (I := I) (M := M) D h j z))
      hpd (K * Mhi + 1) hCpos hup ξ
    have hrew : tmGKi (I := I) (M := M) D j a b ha hab z (Mf (I := I) (M := M) D h j z)
        = tmInv a b ha hab (Matrix.of (Gf (I := I) (M := M) D h j z)) := by
      unfold tmGKi
      rw [tmGK_eq_Gf (I := I) (M := M) D h j z htgt hdetFf]
    rw [hrew]
    exact hbound
  · exact ⟨1, one_pos,
      fun a b ha hab h hsym hell hub hregion z hz ξ => absurd hregion hreg⟩


end

end Work.Diff.STE.B3
