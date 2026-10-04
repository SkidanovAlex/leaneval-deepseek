/-
# The principal part of the transport identity (the `hSec` hypothesis)

This module supplies the *principal-part lemma* `Work.Diff.STE.B3.tmSecJet`, which is the hypothesis
`hSec` of `Work.Diff.STE.B3.transport_identity`:

`Σ_{ik} Ff a i · (jet₂ Gf)(bB c)(bB d) i k · Ff b k = ∂_c∂_d (Mf a b) − eightTerm c d a b`

on the closed `2σ j`-ball.  The proof combines

* `Work.Diff.STE.B3.transport_jet_data` (the identification of the components of the chart `2`-jet
  of `Gf` with the partial derivatives `pdR c (pdR d (Gf · i k))`), and
* `Work.Diff.STE.B3.transport_Mf_second_tame` (the second-order Leibniz rule for the frame-change
  identity `Mf = Σ_{ik} Ff a i · Gf i k · Ff b k`),

whose germ hypothesis is supplied by `Mf_germ` below (the frame-change identity holds on the *open*
chart-target region, hence on a neighbourhood of every point of the closed `2σ`-ball — this is what
makes the boundary case `‖z‖ = 2σ j` work).

The auxiliary `Gf_dual_of_target` / `Gf_germ` (the dual formula `Gf = Finvf · Mf · Finvfᵀ`, with the
invertibility of the frame matrix isolated as a pointwise hypothesis rather than the ball
hypothesis of `Work.Diff.STE.B3.Gf_eq_dual`) are provided here as well; they are the germ input for
the jet-matching of the *nominal* objects (`tmDGK`, `tmEight`).
-/
import Mathlib
import Submission.Work.Diff.STE.B3.TransportDefs
import Submission.Work.Diff.STE.B3.transport_Mf_second
import Submission.Work.Diff.STE.B3.transport_Mf_second_tame
import Submission.Work.Diff.STE.B3.transport_jet_data
import Submission.Work.Diff.STE.B3.transport_tame_leibniz
import Submission.Work.Diff.STE.B3.CompSmooth
import Submission.Work.Diff.EXT.contMDiffAt_matrix_inv

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

open LeanEval.Geometry.SphereTheorem Submission.Diff
open scoped Manifold ContDiff Bundle Topology BigOperators Matrix
open Bundle ContDiff Set

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

/-! ## 1. The frame-change identity in matrix form on the chart target -/

/-- `Mf = Ff · Gf · Ffᵀ` in matrix form, on the chart target. -/
lemma Mf_matrix_eq_target (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀)
    (h : Work.Diff.STE.Bil (I := I) (M := M)) (j : ι₀)
    {z : Fin (Module.finrank ℝ E) → ℝ}
    (hz : flatToE (I := I) (D.x₀ j) z ∈ (extChartAt I (D.x₀ j)).target) :
    Matrix.of (Mf (I := I) (M := M) D h j z)
      = Matrix.of (Ff (I := I) (M := M) D j z)
        * Matrix.of (Gf (I := I) (M := M) D h j z)
        * (Matrix.of (Ff (I := I) (M := M) D j z))ᵀ := by
  ext a b
  rw [Matrix.mul_apply]
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Finset.sum_mul, Matrix.of_apply]
  rw [Mf_eq_of_target (I := I) (M := M) D h j a b hz]
  conv_rhs => rw [Finset.sum_comm]

/-- **The dual formula `Gf = Finvf · Mf · Finvfᵀ`**, on the chart target and given the invertibility
of the frame matrix.  This is `Work.Diff.STE.B3.Gf_eq_dual` with the ball hypothesis
`‖z‖ ≤ 2 σ j` (used only to produce `htgt` and `det Ff ≠ 0`) split into its two pointwise
consequences, so that it can be used on an open neighbourhood of a boundary point. -/
lemma Gf_dual_of_target (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀)
    (h : Work.Diff.STE.Bil (I := I) (M := M)) (j : ι₀)
    {z : Fin (Module.finrank ℝ E) → ℝ}
    (hz : flatToE (I := I) (D.x₀ j) z ∈ (extChartAt I (D.x₀ j)).target)
    (hdet : (Matrix.of (Ff (I := I) (M := M) D j z)).det ≠ 0)
    (i k : Fin (Module.finrank ℝ E)) :
    Gf (I := I) (M := M) D h j z i k
      = ∑ a, ∑ b, Finvf (I := I) (M := M) D j z i a
          * Mf (I := I) (M := M) D h j z a b * Finvf (I := I) (M := M) D j z k b := by
  have hdetU : IsUnit (Matrix.of (Ff (I := I) (M := M) D j z)).det :=
    isUnit_iff_ne_zero.mpr hdet
  have hdetT : IsUnit ((Matrix.of (Ff (I := I) (M := M) D j z))ᵀ).det := by
    rwa [Matrix.det_transpose]
  have hkey : Matrix.of (Mf (I := I) (M := M) D h j z)
      = Matrix.of (Ff (I := I) (M := M) D j z)
        * (Matrix.of (Gf (I := I) (M := M) D h j z)
          * (Matrix.of (Ff (I := I) (M := M) D j z))ᵀ) := by
    rw [Mf_matrix_eq_target (I := I) (M := M) D h j hz, Matrix.mul_assoc]
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

/-! ## 2. The germ forms -/

/-- **The frame-change identity, eventually**: at every point of the closed `2σ`-ball the identity
`Mf = Σ_{ik} Ff a i · Gf i k · Ff b k` holds on a neighbourhood. -/
lemma Mf_germ (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀)
    (h : Work.Diff.STE.Bil (I := I) (M := M)) (j : ι₀)
    (a b : Fin (Module.finrank ℝ E)) {z : Fin (Module.finrank ℝ E) → ℝ}
    (hz : ‖z‖ ≤ 2 * D.σ j) :
    (fun w : Fin (Module.finrank ℝ E) → ℝ => Mf (I := I) (M := M) D h j w a b)
      =ᶠ[nhds z] (fun w : Fin (Module.finrank ℝ E) → ℝ =>
        ∑ i, ∑ k, Ff (I := I) (M := M) D j w a i * Gf (I := I) (M := M) D h j w i k
          * Ff (I := I) (M := M) D j w b k) := by
  have hU : ∀ᶠ y in nhds z,
      flatToE (I := I) (D.x₀ j) y ∈ (extChartAt I (D.x₀ j)).target :=
    ((isOpen_extChartAt_target (I := I) (D.x₀ j)).preimage
      (Work.Diff.STE.contDiff_flatToE (I := I) (D.x₀ j)).continuous).mem_nhds (D.htarget j z hz)
  filter_upwards [hU] with y hy
  exact Mf_eq_of_target (I := I) (M := M) D h j a b hy

/-- **The dual formula, eventually**: at every point of the closed `2σ`-ball the identity
`Gf = Σ_{ab} Finvf i a · Mf a b · Finvf k b` holds on a neighbourhood. -/
lemma Gf_germ (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀)
    (h : Work.Diff.STE.Bil (I := I) (M := M)) (j : ι₀)
    (i k : Fin (Module.finrank ℝ E)) {z : Fin (Module.finrank ℝ E) → ℝ}
    (hz : ‖z‖ ≤ 2 * D.σ j) :
    (fun w : Fin (Module.finrank ℝ E) → ℝ => Gf (I := I) (M := M) D h j w i k)
      =ᶠ[nhds z] (fun w : Fin (Module.finrank ℝ E) → ℝ =>
        ∑ a, ∑ b, Finvf (I := I) (M := M) D j w i a
          * Mf (I := I) (M := M) D h j w a b * Finvf (I := I) (M := M) D j w k b) := by
  have hzt : flatToE (I := I) (D.x₀ j) z ∈ (extChartAt I (D.x₀ j)).target := D.htarget j z hz
  have hU : ∀ᶠ y in nhds z,
      flatToE (I := I) (D.x₀ j) y ∈ (extChartAt I (D.x₀ j)).target :=
    ((isOpen_extChartAt_target (I := I) (D.x₀ j)).preimage
      (Work.Diff.STE.contDiff_flatToE (I := I) (D.x₀ j)).continuous).mem_nhds hzt
  have hdetcont : ContinuousAt (fun y : Fin (Module.finrank ℝ E) → ℝ =>
      (Matrix.of (fun a i : Fin (Module.finrank ℝ E) =>
        Ff (I := I) (M := M) D j y a i)).det) z := by
    refine (((Work.Diff.EXT.contDiff_matrix_det_pi (n := Module.finrank ℝ E)).contDiffAt.comp z
      ?_)).continuousAt
    rw [contDiffAt_pi]
    intro a
    rw [contDiffAt_pi]
    intro i
    exact Ff_contDiffAt (I := I) (M := M) D j a i hzt
  have hdet : ∀ᶠ y in nhds z, (Matrix.of (Ff (I := I) (M := M) D j y)).det ≠ 0 := by
    filter_upwards [hdetcont.eventually_ne (det_Ff_ne_zero (I := I) (M := M) D j hz)]
      with y hy
    exact hy
  filter_upwards [hU, hdet] with y hy hy'
  exact Gf_dual_of_target (I := I) (M := M) D h j hy hy' i k

/-! ## 3. The principal-part lemma -/

/-- **The principal part of the transport identity.**  The contraction of the second spatial jet of
the coordinate chart matrix `Gf` with the frame weights is the second derivative of the
orthonormal-frame chart matrix `Mf` minus the eight lower-order terms of the Leibniz rule. -/
theorem tmSecJet (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀)
    (h : Work.Diff.STE.Bil (I := I) (M := M))
    (hsmooth : Work.Diff.STE.D.ChartData (I := I) (M := M) h) (j : ι₀)
    (af bf : Fin (Module.finrank ℝ E)) {z : Fin (Module.finrank ℝ E) → ℝ}
    (hz : ‖z‖ ≤ 2 * D.σ j) :
    ∀ c d : Fin (Module.finrank ℝ E),
      (∑ i, ∑ k, Ff (I := I) (M := M) D j z af i
          * (Work.Diff.STE.D.chartJetOf (I := I) (M := M) h (D.x₀ j)
              (yf (I := I) (M := M) D j z)).2.2
              (Work.Diff.EXT.bB (E := E) c) (Work.Diff.EXT.bB (E := E) d) i k
          * Ff (I := I) (M := M) D j z bf k)
        = Work.Diff.STE.pdR c (Work.Diff.STE.pdR d
            (fun w => Mf (I := I) (M := M) D h j w af bf)) z
          - eightTerm (I := I) (M := M) D h j z c d af bf := by
  intro c d
  obtain ⟨-, -, hJ3⟩ := transport_jet_data (I := I) (M := M) D h hsmooth j hz
  have hzt : flatToE (I := I) (D.x₀ j) z ∈ (extChartAt I (D.x₀ j)).target := D.htarget j z hz
  have h2 := transport_Mf_second_tame (I := I) (M := M) D h j af bf
    (Mf_germ (I := I) (M := M) D h j af bf hz)
    (fun i => (Ff_contDiffAt (I := I) (M := M) D j af i hzt).of_le (by norm_num))
    (fun k => (Ff_contDiffAt (I := I) (M := M) D j bf k hzt).of_le (by norm_num))
    (fun i k => (Gf_contDiffAt (I := I) (M := M) D h hsmooth j i k hzt).of_le (by norm_num))
    c d
  rw [h2]
  rw [Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun k _ => by
    rw [show (Work.Diff.STE.D.chartJetOf (I := I) (M := M) h (D.x₀ j)
          (yf (I := I) (M := M) D j z)).2.2
          (Work.Diff.EXT.bB (E := E) c) (Work.Diff.EXT.bB (E := E) d) i k
        = Work.Diff.STE.pdR c (Work.Diff.STE.pdR d
            (fun y => Gf (I := I) (M := M) D h j y i k)) z from hJ3 c d i k]))]
  ring

end Work.Diff.STE.B3
