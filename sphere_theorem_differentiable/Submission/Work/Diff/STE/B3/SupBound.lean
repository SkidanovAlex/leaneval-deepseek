import Mathlib
import Submission.Work.Diff.STE.B3.Comp
import Submission.Work.Diff.STE.Man.SectSup

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Layer B3: the sup norm of a periodised component is controlled by the composite norm

This is the B3 analogue of `Work.Diff.STE.bilPer_norm_le_sqrt_BNorm`: for `card ι < 2 k`, every
value of `D.Rper i h a b` is bounded by `C √(D.BNorm k h)`, with `C` independent of `i`, `a`, `b`,
`z` and of the section `h`.
-/

noncomputable section

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology BigOperators
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter

namespace Work.Diff.STE

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]
  {ι₀ : Type*} [Fintype ι₀] {g₀ : SMet I M}

namespace B3Data

variable (D : B3Data (I := I) (M := M) ι₀ g₀)

/-- **The sup norm of a periodised component is controlled by the composite norm.** -/
theorem Rper_norm_le_sqrt_BNorm (k : ℕ)
    (hk : Fintype.card (Fin (Module.finrank ℝ E)) < 2 * k)
    (h : Bil (I := I) (M := M))
    (hsm : ∀ (i : ι₀) (a b : Fin (Module.finrank ℝ E)),
      ContDiff ℝ (⊤ : ℕ∞) (D.Rper i h a b))
    (hper : ∀ (i : ι₀) (a b : Fin (Module.finrank ℝ E)),
      Periodic1 (D.Rper i h a b)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (i : ι₀) (a b : Fin (Module.finrank ℝ E))
      (z : Fin (Module.finrank ℝ E) → ℝ),
      ‖D.Rper i h a b z‖ ≤ C * Real.sqrt (D.BNorm k h) := by
  obtain ⟨C, hC, hCb⟩ := norm_seriesFun_le (ι := Fin (Module.finrank ℝ E)) k hk
  refine ⟨C, hC, fun i a b z => ?_⟩
  have hinv : seriesFun (fourierCoeff (D.Rper i h a b)) z = D.Rper i h a b z :=
    flat.seriesFun_fourierCoeff (D.Rper i h a b) (hsm i a b) (hper i a b) z
  rw [← hinv]
  refine (hCb _ (summable_weighted_fourierCoeff_of_contDiff _ (hsm i a b) (hper i a b) k) z).trans
    (mul_le_mul_of_nonneg_left ?_ hC)
  refine Real.sqrt_le_sqrt ?_
  have hle : CSq k (fourierCoeff (D.Rper i h a b)) ≤ D.BNorm k h := by
    change CSq k (fourierCoeff (D.Rper i h a b)) ≤
      ∑ i' : ι₀, ∑ a' : Fin (Module.finrank ℝ E),
        ∑ b' : Fin (Module.finrank ℝ E), CSq k (fourierCoeff (D.Rper i' h a' b'))
    exact sum3_single_le (fun i' a' b' => CSq k (fourierCoeff (D.Rper i' h a' b')))
      (fun i' a' b' => CSq_nonneg k _) i a b
  exact hle

end B3Data

end Work.Diff.STE
