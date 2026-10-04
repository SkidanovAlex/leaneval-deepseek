/-
# Auxiliary lemmas for `Work.Diff.STE.B3.tmNom_tame`

This module collects the two kinds of auxiliary results needed by the proof of the *nominal
matching* lemma `Work.Diff.STE.B3.tmNom_tame`:

* **local smoothness of the entries of a matrix inverse** (`tmNom_inv_entry_ContDiffAt`): if every
  entry of a matrix family `X` is `C^∞` at `z` and `det (X z) ≠ 0`, then so is every entry of
  `y ↦ (X y)⁻¹` (Cramer's rule, `A⁻¹ = (det A)⁻¹ • A.adjugate`).  This is the `ContDiffAt` version
  of `Work.Diff.STE.B3.transport_contDiffOn_inv_entry`; it gives, in particular, the
  differentiability of the frame inverse `Finvf` (`tmNom_Finvf_ContDiffAt`), which is what the
  product rule for `Gf = Finvf · Mf · Finvfᵀ` needs.

* **the inverted frame-change identity on the chart target** (`tmNom_Gf_eq_dual_of_target`): the
  coordinate-frame chart matrix is the conjugate of the orthonormal-frame chart matrix by the
  inverse frame matrix.  `Work.Diff.STE.B3.Gf_eq_dual` states this on the `2σ`-ball; the version
  here only assumes membership of the flat coordinate in the chart *target* together with
  `det (Ff z) ≠ 0`, which is an *open* condition, so that the identity holds on a whole
  neighbourhood of `z` (`tmNom_Gf_eventuallyEq`).  That is what lets one differentiate it.

* **the identification of a continuous linear map with its basis data**
  (`tmNom_clm_eq_sum_coord_smulRight`): every `L : E →L[ℝ] MatE` equals `Σ_c (bB.coord c) ⊗ L (bB c)`,
  the form in which `Work.Diff.STE.B3.tmDGKclm` is written.
-/
import Mathlib
import Submission.Work.Diff.STE.B3.TransportDefs
import Submission.Work.Diff.STE.B3.transport_tame_defs
import Submission.Work.Diff.STE.B3.transport_Mf_second
import Submission.Work.Diff.STE.B3.Mf_matrix_eq_of_target
import Submission.Work.Diff.STE.B3.transport_tame_leibniz

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

open scoped BigOperators Matrix ContDiff
open LeanEval.Geometry.SphereTheorem Submission.Diff

namespace Work.Diff.STE.B3

set_option maxHeartbeats 1000000
set_option linter.unusedSectionVars false

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ((⊤ : ENat) : WithTop ENat) M] [T2Space M] [I.Boundaryless]
  {ι₀ : Type*} [Fintype ι₀] {g₀ : Submission.Diff.SMet I M}

noncomputable section

/-! ## 1. Local smoothness of the entries of a matrix inverse -/

/-- The determinant of a matrix family whose entries are `C^∞` at `z` is `C^∞` at `z`. -/
lemma tmNom_det_ContDiffAt {n : ℕ} {X : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ}
    {z : Fin n → ℝ} (hX : ∀ i j, ContDiffAt ℝ ∞ (fun y => X y i j) z) :
    ContDiffAt ℝ ∞ (fun y => (X y).det) z := by
  have hfun : (fun y : Fin n → ℝ => (X y).det)
      = fun y => ∑ σ : Equiv.Perm (Fin n), (↑↑(Equiv.Perm.sign σ) : ℝ) * ∏ k, X y (σ k) k := by
    funext y; rw [Matrix.det_apply']
  rw [hfun]
  refine ContDiffAt.sum (fun σ _ => contDiffAt_const.mul ?_)
  exact contDiffAt_prod (t := Finset.univ) (f := fun k y => X y (σ k) k) (fun k _ => hX (σ k) k)

/-- Replacing one row of a matrix family with a constant row preserves local smoothness. -/
lemma tmNom_updateRow_ContDiffAt {n : ℕ} {X : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ}
    {z : Fin n → ℝ} (hX : ∀ i j, ContDiffAt ℝ ∞ (fun y => X y i j) z) (q : Fin n)
    (b : Fin n → ℝ) :
    ∀ k l, ContDiffAt ℝ ∞ (fun y => (X y).updateRow q b k l) z := by
  intro k l
  have h2 : (fun y : Fin n → ℝ => (X y).updateRow q b k l)
      = fun y => if k = q then b l else X y k l := by
    funext y; rw [Matrix.updateRow_apply]
  rw [h2]
  by_cases hk : k = q
  · simp only [hk, ite_true]; exact contDiffAt_const
  · simp only [hk, ite_false]; exact hX k l

/-- The adjugate of a matrix family whose entries are `C^∞` at `z` is `C^∞` at `z`. -/
lemma tmNom_adjugate_ContDiffAt {n : ℕ} {X : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ}
    {z : Fin n → ℝ} (hX : ∀ i j, ContDiffAt ℝ ∞ (fun y => X y i j) z) (i j : Fin n) :
    ContDiffAt ℝ ∞ (fun y => (X y).adjugate i j) z := by
  classical
  have hrw : (fun y : Fin n → ℝ => (X y).adjugate i j)
      = fun y => ((X y).updateRow j (Pi.single i 1)).det := by
    funext y; rw [Matrix.adjugate_apply]
  rw [hrw]
  exact tmNom_det_ContDiffAt (tmNom_updateRow_ContDiffAt hX j (Pi.single i 1))

/-- **Local smoothness of the entries of a matrix inverse.**  If the entries of `X` are `C^∞` at
`z` and `det (X z) ≠ 0`, then every entry of `y ↦ (X y)⁻¹` is `C^∞` at `z`. -/
lemma tmNom_inv_entry_ContDiffAt {n : ℕ} {X : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ}
    {z : Fin n → ℝ} (hX : ∀ i j, ContDiffAt ℝ ∞ (fun y => X y i j) z)
    (hdet : (X z).det ≠ 0) (i j : Fin n) :
    ContDiffAt ℝ ∞ (fun y => ((X y)⁻¹) i j) z := by
  have hd : ContDiffAt ℝ ∞ (fun y => (X y).det) z := tmNom_det_ContDiffAt hX
  have hdi : ContDiffAt ℝ ∞ (fun y : Fin n → ℝ => Ring.inverse ((X y).det)) z := by
    have h1 : ContDiffAt ℝ ∞ (fun y : Fin n → ℝ => (X y).det)⁻¹ z := hd.inv hdet
    refine h1.congr_of_eventuallyEq (Filter.EventuallyEq.of_eq ?_)
    funext y
    exact congrFun Ring.inverse_eq_inv' ((X y).det)
  have hmul := hdi.mul (tmNom_adjugate_ContDiffAt hX i j)
  refine hmul.congr_of_eventuallyEq (Filter.EventuallyEq.of_eq ?_)
  funext y
  rw [Matrix.inv_def, Matrix.smul_apply, smul_eq_mul]

/-! ## 2. Basis data of a continuous linear map -/

/-- The canonical-basis expansion of a vector of the model space. -/
lemma tmNom_bB_sum_repr (v : E) :
    (∑ c, ((Work.Diff.EXT.bB (E := E)).coord c) v • Work.Diff.EXT.bB (E := E) c) = v := by
  conv_rhs => rw [← Module.Basis.sum_repr (Work.Diff.EXT.bB (E := E)) v]
  refine Finset.sum_congr rfl (fun c _ => ?_)
  rw [Module.Basis.coord_apply]

/-- **A continuous linear map is determined by its values on the canonical basis**, in the normal
form used by `Work.Diff.STE.B3.tmDGKclm`. -/
lemma tmNom_clm_eq_sum_coord_smulRight (L : E →L[ℝ] Work.Diff.EXT.MatE (E := E)) :
    (∑ c, (((Work.Diff.EXT.bB (E := E)).coord c).toContinuousLinearMap).smulRight
        (L (Work.Diff.EXT.bB (E := E) c))) = L := by
  apply ContinuousLinearMap.ext
  intro v
  rw [show (∑ c : Fin (Module.finrank ℝ E),
        (((Work.Diff.EXT.bB (E := E)).coord c).toContinuousLinearMap).smulRight
          (L (Work.Diff.EXT.bB (E := E) c))) v
      = ∑ c, (((Work.Diff.EXT.bB (E := E)).coord c).toContinuousLinearMap).smulRight
          (L (Work.Diff.EXT.bB (E := E) c)) v from
    map_sum (ContinuousLinearMap.apply ℝ (Work.Diff.EXT.MatE (E := E)) v)
      (fun c : Fin (Module.finrank ℝ E) =>
        (((Work.Diff.EXT.bB (E := E)).coord c).toContinuousLinearMap).smulRight
          (L (Work.Diff.EXT.bB (E := E) c))) Finset.univ]
  rw [Finset.sum_congr rfl (fun c _ => ContinuousLinearMap.smulRight_apply)]
  have hsum : (∑ c : Fin (Module.finrank ℝ E),
        (LinearMap.toContinuousLinearMap ((Work.Diff.EXT.bB (E := E)).coord c)) v
          • L (Work.Diff.EXT.bB (E := E) c)) = L v := by
    conv_rhs => rw [← tmNom_bB_sum_repr (E := E) v]
    rw [map_sum L (fun c => ((Work.Diff.EXT.bB (E := E)).coord c) v • Work.Diff.EXT.bB (E := E) c)
      Finset.univ]
    refine Finset.sum_congr rfl (fun c _ => ?_)
    rw [map_smul L (((Work.Diff.EXT.bB (E := E)).coord c) v) (Work.Diff.EXT.bB (E := E) c)]
    simp only [LinearMap.coe_toContinuousLinearMap']
  exact hsum

/-! ## 3. The inverted frame-change identity on the chart target -/

/-- **`Gf = Finvf · Mf · Finvfᵀ` on the chart target**: the coordinate-frame chart matrix of the
section `h` is the conjugate of the orthonormal-frame chart matrix by the inverse frame matrix.
This is `Work.Diff.STE.B3.Gf_eq_dual` with the ball-hypothesis `‖z‖ ≤ 2 σ j` replaced by membership
of the flat coordinate in the chart target (an open condition) together with `det (Ff z) ≠ 0`. -/
lemma tmNom_Gf_eq_dual_of_target (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀)
    (h : Work.Diff.STE.Bil (I := I) (M := M)) (j : ι₀)
    {z : Fin (Module.finrank ℝ E) → ℝ}
    (htgt : Work.Diff.STE.flatToE (I := I) (D.x₀ j) z ∈ (extChartAt I (D.x₀ j)).target)
    (hdet : (Matrix.of (Ff (I := I) (M := M) D j z)).det ≠ 0)
    (i k : Fin (Module.finrank ℝ E)) :
    Gf (I := I) (M := M) D h j z i k
      = ∑ a, ∑ b, Finvf (I := I) (M := M) D j z i a
          * Mf (I := I) (M := M) D h j z a b
          * Finvf (I := I) (M := M) D j z k b := by
  have hdetU : IsUnit (Matrix.of (Ff (I := I) (M := M) D j z)).det :=
    isUnit_iff_ne_zero.mpr hdet
  have hdetT : IsUnit ((Matrix.of (Ff (I := I) (M := M) D j z))ᵀ).det := by
    rwa [Matrix.det_transpose]
  have hkey : Matrix.of (Mf (I := I) (M := M) D h j z)
      = Matrix.of (Ff (I := I) (M := M) D j z)
        * (Matrix.of (Gf (I := I) (M := M) D h j z)
          * (Matrix.of (Ff (I := I) (M := M) D j z))ᵀ) := by
    rw [Mf_matrix_eq_of_target (I := I) (M := M) D h j z htgt, Matrix.mul_assoc]
  have h1 : (Matrix.of (Ff (I := I) (M := M) D j z))⁻¹
      * Matrix.of (Mf (I := I) (M := M) D h j z)
      = Matrix.of (Gf (I := I) (M := M) D h j z)
        * (Matrix.of (Ff (I := I) (M := M) D j z))ᵀ := by
    rw [hkey, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hdetU, Matrix.one_mul]
  have h2 : Matrix.of (Finvf (I := I) (M := M) D j z)
      * Matrix.of (Mf (I := I) (M := M) D h j z)
      * (Matrix.of (Finvf (I := I) (M := M) D j z))ᵀ
      = Matrix.of (Gf (I := I) (M := M) D h j z) := by
    rw [Finvf_eq_inv (I := I) (M := M) D j z, Matrix.transpose_nonsing_inv, h1,
      Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hdetT, Matrix.mul_one]
  have hG := h2.symm
  change (Matrix.of (Gf (I := I) (M := M) D h j z)) i k = _
  rw [hG]
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Finset.sum_mul, Matrix.of_apply]
  conv_lhs => rw [Finset.sum_comm]

/-! ## 4. Consequences at the `2σ`-ball -/

/-- **The frame inverse is `C^∞` at every point of the `2σ`-ball.** -/
lemma tmNom_Finvf_ContDiffAt (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (j : ι₀)
    (i a : Fin (Module.finrank ℝ E)) {z : Fin (Module.finrank ℝ E) → ℝ}
    (hz : ‖z‖ ≤ 2 * D.σ j) :
    ContDiffAt ℝ ∞ (fun y => Finvf (I := I) (M := M) D j y i a) z :=
  tmNom_inv_entry_ContDiffAt
    (X := fun y : Fin (Module.finrank ℝ E) → ℝ => Matrix.of (Ff (I := I) (M := M) D j y))
    (fun p q => Ff_contDiffAt (I := I) (M := M) D j p q (D.htarget j z hz))
    (det_Ff_ne_zero (I := I) (M := M) D j hz) i a

/-- The flat coordinates stay in the chart target on a neighbourhood of a point of the target. -/
lemma tmNom_eventually_mem_target (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (j : ι₀)
    {z : Fin (Module.finrank ℝ E) → ℝ}
    (htgt : Work.Diff.STE.flatToE (I := I) (D.x₀ j) z ∈ (extChartAt I (D.x₀ j)).target) :
    ∀ᶠ y in nhds z, Work.Diff.STE.flatToE (I := I) (D.x₀ j) y
      ∈ (extChartAt I (D.x₀ j)).target :=
  ((isOpen_extChartAt_target (I := I) (D.x₀ j)).preimage
    (Work.Diff.STE.contDiff_flatToE (I := I) (D.x₀ j)).continuous).mem_nhds htgt

/-- Invertibility of the frame matrix persists on a neighbourhood of a point of the `2σ`-ball. -/
lemma tmNom_eventually_det_Ff_ne_zero (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀)
    (j : ι₀) {z : Fin (Module.finrank ℝ E) → ℝ} (hz : ‖z‖ ≤ 2 * D.σ j) :
    ∀ᶠ y in nhds z, (Matrix.of (Ff (I := I) (M := M) D j y)).det ≠ 0 := by
  have hcont : ContinuousAt
      (fun y : Fin (Module.finrank ℝ E) → ℝ => (Matrix.of (Ff (I := I) (M := M) D j y)).det) z :=
    ((tmNom_det_ContDiffAt (X := fun y => Matrix.of (Ff (I := I) (M := M) D j y))
      (fun p q => Ff_contDiffAt (I := I) (M := M) D j p q (D.htarget j z hz)))).continuousAt
  exact hcont.eventually_ne (det_Ff_ne_zero (I := I) (M := M) D j hz)

/-- **The frame-change identity holds on a whole neighbourhood of every point of the `2σ`-ball**,
in the inverted (frame-inverse) form.  This is the form in which it can be differentiated. -/
lemma tmNom_Gf_eventuallyEq (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀)
    (h : Work.Diff.STE.Bil (I := I) (M := M)) (j : ι₀)
    {z : Fin (Module.finrank ℝ E) → ℝ} (hz : ‖z‖ ≤ 2 * D.σ j)
    (i k : Fin (Module.finrank ℝ E)) :
    (fun y => Gf (I := I) (M := M) D h j y i k)
      =ᶠ[nhds z] (fun y => ∑ a, ∑ b, Finvf (I := I) (M := M) D j y i a
          * Mf (I := I) (M := M) D h j y a b
          * Finvf (I := I) (M := M) D j y k b) := by
  filter_upwards [tmNom_eventually_mem_target (I := I) (M := M) D j (D.htarget j z hz),
    tmNom_eventually_det_Ff_ne_zero (I := I) (M := M) D j hz] with y hy hdy
  exact tmNom_Gf_eq_dual_of_target (I := I) (M := M) D h j hy hdy i k


end

end Work.Diff.STE.B3
