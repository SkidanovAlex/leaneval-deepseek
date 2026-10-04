import Mathlib
import Submission.Work.Diff.STE.Man.Sect
import Submission.Work.Diff.STE.norm_seriesFun_le
import Submission.Work.Diff.STE.flat.seriesFun_fourierCoeff

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Layer B2, first estimate: the sup norm of a localised chart component is controlled by `BNorm`

For a smooth, `1`-periodic localised component `bilPer χ x₀ h i a b` (which is what
`Work.Diff.STE.fill.contDiff_bilPer_of_bump` produces from the cut-off data), the flat Sobolev
estimate `Work.Diff.STE.norm_seriesFun_le` gives

  `‖bilPer χ x₀ h i a b z‖ ≤ C √(CSq s (fourierCoeff (bilPer χ x₀ h i a b)))`,   `card ι < 2 s`,

and the right-hand side is bounded by `√(BNorm χ x₀ s h)` because `BNorm` is the sum of the `CSq`s
of all the components.  This is the first of the two ingredients of the pointwise control
`|h x u v| ≤ C ‖h‖_s ‖u‖ ‖v‖` of Layer B2 (the second one is the expansion of `h x u v` in the
coordinate frame, i.e. the recovery of the section from its chart matrices).
-/

noncomputable section

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology BigOperators
open Bundle ContDiff Set VectorField CovariantDerivative Metric

namespace Work.Diff.STE

set_option maxHeartbeats 1000000

/-- A single entry of a triple finite sum is at most the whole sum (all entries nonnegative). -/
lemma sum3_single_le {ι₀ : Type*} [Fintype ι₀] {n : ℕ} (G : ι₀ → Fin n → Fin n → ℝ)
    (hG : ∀ i a b, 0 ≤ G i a b) (i : ι₀) (a b : Fin n) :
    G i a b ≤ ∑ i' : ι₀, ∑ a' : Fin n, ∑ b' : Fin n, G i' a' b' := by
  calc G i a b ≤ ∑ b' : Fin n, G i a b' :=
        Finset.single_le_sum (fun j _ => hG i a j) (Finset.mem_univ b)
    _ ≤ ∑ a' : Fin n, ∑ b' : Fin n, G i a' b' :=
        Finset.single_le_sum (fun j _ => Finset.sum_nonneg fun j' _ => hG i j j')
          (Finset.mem_univ a)
    _ ≤ ∑ i' : ι₀, ∑ a' : Fin n, ∑ b' : Fin n, G i' a' b' :=
        Finset.single_le_sum
          (fun j _ => Finset.sum_nonneg fun j' _ =>
            Finset.sum_nonneg fun j'' _ => hG j j' j'') (Finset.mem_univ i)

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]

/-- **The sup norm of a localised chart component is controlled by the composite norm.**  For a
family of components that are smooth and `1`-periodic, the value at any point is bounded by
`√(BNorm χ x₀ s h)`, `card ι < 2 s`. -/
theorem bilPer_norm_le_sqrt_BNorm {ι₀ : Type*} [Fintype ι₀]
    (χ : ι₀ → (Fin (Module.finrank ℝ E) → ℝ) → ℝ) (x₀ : ι₀ → M)
    (s : ℕ) (hs : Fintype.card (Fin (Module.finrank ℝ E)) < 2 * s)
    (h : Bil (I := I) (M := M))
    (hsm : ∀ (i : ι₀) (a b : Fin (Module.finrank ℝ E)),
      ContDiff ℝ (⊤ : ℕ∞) (bilPer χ x₀ h i a b))
    (hper : ∀ (i : ι₀) (a b : Fin (Module.finrank ℝ E)),
      Periodic1 (bilPer χ x₀ h i a b)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (i : ι₀) (a b : Fin (Module.finrank ℝ E))
      (z : Fin (Module.finrank ℝ E) → ℝ),
      ‖bilPer χ x₀ h i a b z‖ ≤ C * Real.sqrt (BNorm χ x₀ s h) := by
  obtain ⟨C, hC, hCb⟩ := norm_seriesFun_le (ι := Fin (Module.finrank ℝ E)) s hs
  refine ⟨C, hC, fun i a b z => ?_⟩
  -- the component is the Fourier series of its coefficients
  have hinv : seriesFun (fourierCoeff (bilPer χ x₀ h i a b)) z = bilPer χ x₀ h i a b z :=
    flat.seriesFun_fourierCoeff (bilPer χ x₀ h i a b) (hsm i a b) (hper i a b) z
  rw [← hinv]
  refine (hCb _ (summable_weighted_fourierCoeff_of_contDiff _ (hsm i a b) (hper i a b) s) z).trans
    (mul_le_mul_of_nonneg_left ?_ hC)
  -- the single `CSq` is dominated by the sum `BNorm`
  refine Real.sqrt_le_sqrt ?_
  have hle : CSq s (fourierCoeff (bilPer χ x₀ h i a b)) ≤ BNorm χ x₀ s h := by
    change CSq s (fourierCoeff (bilPer χ x₀ h i a b)) ≤
      ∑ i' : ι₀, ∑ a' : Fin (Module.finrank ℝ E), ∑ b' : Fin (Module.finrank ℝ E),
        CSq s (fourierCoeff (bilPer χ x₀ h i' a' b'))
    exact sum3_single_le
      (fun i' a' b' => CSq s (fourierCoeff (bilPer χ x₀ h i' a' b')))
      (fun i' a' b' => CSq_nonneg s _) i a b
  exact hle

/-- **On the fundamental cube the component agrees with the localised chart matrix.**  If the
localised component is supported in the open cube `(-1/2,1/2)^n`, its periodisation `bilPer` takes
there the value of the localised component itself.  This is the step that identifies the composite
norm with the flat `H^k` norm of the (localised) chart matrix of the section. -/
theorem bilPer_apply_of_mem_cube {ι₀ : Type*}
    (χ : ι₀ → (Fin (Module.finrank ℝ E) → ℝ) → ℝ) (x₀ : ι₀ → M)
    (h : Bil (I := I) (M := M)) (i : ι₀) (a b : Fin (Module.finrank ℝ E))
    (hsmall : Function.support (bilLoc χ x₀ h i a b) ⊆
      Set.pi Set.univ (fun _ : Fin (Module.finrank ℝ E) => Set.Ioo (-(1 / 2 : ℝ)) (1 / 2)))
    {z : Fin (Module.finrank ℝ E) → ℝ}
    (hz : ∀ j, z j ∈ Set.Ioo (-(1 / 2 : ℝ)) (1 / 2)) :
    bilPer χ x₀ h i a b z = ((bilLoc χ x₀ h i a b z : ℝ) : ℂ) := by
  have hsupp : Function.support
      (fun z : Fin (Module.finrank ℝ E) → ℝ => ((bilLoc χ x₀ h i a b z : ℝ) : ℂ)) ⊆
      Set.pi Set.univ (fun _ : Fin (Module.finrank ℝ E) => Set.Ioo (-(1 / 2 : ℝ)) (1 / 2)) := by
    intro z hz'
    exact hsmall (by
      intro h0
      exact hz' (by simp [h0]))
  exact periodization_eq_self hsupp hz

end Work.Diff.STE