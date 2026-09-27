import Mathlib
import Submission.Work.Drive.BoxParityAux
import Submission.Work.Drive.exists_local_normalForm
import Submission.Work.Drive.flowField_on_box
import Submission.Work.Drive.cofactorVec_apply_ne_zero

/-!
# The `i`-th component of the flow field is nonzero at a chart zero

Let `F : ℝ^{m+1} → ℝ^m` be a smooth map and let `x` be a zero of `F` inside the unit box which lies
in the chart region of a local normal form (as produced by `Work.Drive.exists_local_normalForm`):
there are `δ₀, ρ₀` and a graph `η` such that

* for `|u - p i| < δ₀` the point `u • eᵢ + η u` is a zero of `F` at which `fderiv ℝ F` is
  surjective on the hyperplane `{v | v i = 0}`;
* `F` vanishes in the tubular neighbourhood of the graph exactly on the graph.

Then the `i`-th component of `flowField F` at `x` is nonzero.

Indeed, the chart hypotheses put `x` on the graph, `x = (x i) • eᵢ + η (x i)`, where the derivative
of `F` is surjective on the hyperplane `{v | v i = 0}`; by `cofactorVec_apply_ne_zero` the `i`-th
cofactor of that derivative is nonzero, i.e. `cofactorVectorF F x ≠ 0` in the `i`-th coordinate.
Since on the unit box `flowField F x` is a positive multiple of `cofactorVectorF F x`
(`flowField_on_box`), the `i`-th component of the former is nonzero as well.
-/

namespace Work.Drive

theorem flowField_apply_ne_zero_of_chart {m : ℕ} {F : Work.Drive.Amb m → Work.Drive.Tgt m}
    {p : Work.Drive.Amb m} {i : Fin (m + 1)} {δ₀ ρ₀ : ℝ} {η : ℝ → Work.Drive.Amb m}
    (hnormal : ∀ u : ℝ, |u - p i| < δ₀ →
      F (u • EuclideanSpace.single i 1 + η u) = 0 ∧
      Function.Surjective (fun v : {v : Work.Drive.Amb m // v i = 0} =>
        fderiv ℝ F (u • EuclideanSpace.single i 1 + η u) v.1))
    (hchar : ∀ x : Work.Drive.Amb m, |x i - p i| < δ₀ →
      ‖x - (x i) • EuclideanSpace.single i 1 - η (x i)‖ < ρ₀ →
      (F x = 0 ↔ x = (x i) • EuclideanSpace.single i 1 + η (x i)))
    {x : Work.Drive.Amb m} (hxbox : x ∈ Submission.Drive.unitBox m) (hxF : F x = 0)
    (hδ : |x i - p i| < δ₀) (hρ : ‖x - (x i) • EuclideanSpace.single i 1 - η (x i)‖ < ρ₀) :
    Work.Drive.flowField F x i ≠ 0 := by
  -- The chart characterisation puts `x` on the graph.
  have hxeq : x = (x i) • EuclideanSpace.single i 1 + η (x i) := (hchar x hδ hρ).1 hxF
  -- The derivative of `F` at that graph point is surjective on the hyperplane `{v | v i = 0}`.
  have hsurj : Function.Surjective (fun v : {v : Work.Drive.Amb m // v i = 0} =>
      fderiv ℝ F x v.1) := by
    rw [hxeq]
    exact (hnormal (x i) hδ).2
  -- Hence the `i`-th cofactor of the derivative is nonzero.
  have hcof : Work.Drive.cofactorVectorF F x i ≠ 0 := by
    have h := cofactorVec_apply_ne_zero (fderiv ℝ F x) i hsurj
    simpa [Work.Drive.cofactorVectorF] using h
  -- On the box, `flowField` is a positive multiple of the cofactor field.
  intro h
  have hb := flowField_on_box (F := F) hxbox
  rw [hb] at h
  simp only [PiLp.smul_apply, smul_eq_mul] at h
  have hspos : 0 < Real.sqrt (1 + ‖Work.Drive.cofactorVectorF F x‖ ^ 2) :=
    Real.sqrt_pos.mpr (by positivity)
  have hs : (Real.sqrt (1 + ‖Work.Drive.cofactorVectorF F x‖ ^ 2))⁻¹ ≠ 0 :=
    inv_ne_zero (ne_of_gt hspos)
  rcases mul_eq_zero.mp h with h1 | h1
  · exact absurd h1 hs
  · exact hcof h1

end Work.Drive
