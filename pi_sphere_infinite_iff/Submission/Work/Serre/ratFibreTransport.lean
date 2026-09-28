import Mathlib
import Submission.Work.Serre.serreFibration_fibre_homology_iso
import Submission.Work.Serre.strictFibre_ratH_homotopyFibre

/-!
# The rational fibre homology of a Serre fibration is independent of the base point

`Work.Serre.serreFibration_fibre_homology_iso` is the *integral* statement: the fibres of a Serre
fibration over the two ends of a path have isomorphic singular homology with `ℤ` coefficients.  This
file records the `ℚ`-coefficient consequences, which is the form the rational Serre engine
(`Work.Serre.ratSerrePairComparison` and its tower induction) consumes: the fibre hypotheses of the
stable-range comparison have to be transported from one point of the CW model to another.

* `ratH_fibre_iso_of_path` — `H_n(q⁻¹{x₀};ℚ) ≅ H_n(q⁻¹{x₁};ℚ)` for a path from `x₀` to `x₁`;
* `isZero_ratH_fibre_of_path` — the vanishing `H_j(q⁻¹{x₀};ℚ) = 0` for `0 < j < φ` transfers.

Both are immediate from `serreFibration_fibre_homology_iso` and
`Work.Serre.nonempty_ratH_iso_of_intHomology_iso` (flat base change `ℤ → ℚ` on homology).
-/

open CategoryTheory CategoryTheory.Limits
open scoped Topology unitInterval

namespace Work.Serre

noncomputable section

/-- **Rational fibre homology is base-point independent along a path.**  The `ℚ`-coefficient form of
`Work.Serre.serreFibration_fibre_homology_iso`. -/
theorem ratH_fibre_iso_of_path {X B : Type} [TopologicalSpace X] [TopologicalSpace B]
    (q : C(X, B)) (hq : Work.StemsB.IsSerreFibration q) (γ : C(unitInterval, B)) (n : ℕ) :
    Nonempty (ratH (TopCat.of (Work.StemsB.fibre q (γ 0))) n ≅
      ratH (TopCat.of (Work.StemsB.fibre q (γ 1))) n) :=
  nonempty_ratH_iso_of_intHomology_iso (TopCat.of (Work.StemsB.fibre q (γ 0)))
    (TopCat.of (Work.StemsB.fibre q (γ 1))) n
    (serreFibration_fibre_homology_iso q hq γ n)

/-- **The rational fibre vanishing transfers along a path in the base.**  If `H_j(q⁻¹{x₀};ℚ) = 0`
for `0 < j < φ`, then the same holds at `x₁`, for any path from `x₀` to `x₁`. -/
theorem isZero_ratH_fibre_of_path {X B : Type} [TopologicalSpace X] [TopologicalSpace B]
    (q : C(X, B)) (hq : Work.StemsB.IsSerreFibration q) (x₀ x₁ : B)
    (γ : C(unitInterval, B)) (h0 : γ 0 = x₀) (h1 : γ 1 = x₁) (φ : ℕ)
    (h : ∀ j : ℕ, 0 < j → j < φ →
      IsZero (ratH (TopCat.of (Work.StemsB.fibre q x₀)) j)) :
    ∀ j : ℕ, 0 < j → j < φ → IsZero (ratH (TopCat.of (Work.StemsB.fibre q x₁)) j) := by
  intro j hj hjφ
  obtain ⟨e⟩ := ratH_fibre_iso_of_path q hq γ j
  rw [h0] at e
  rw [h1] at e
  exact IsZero.of_iso (h j hj hjφ) e.symm

end

end Work.Serre
