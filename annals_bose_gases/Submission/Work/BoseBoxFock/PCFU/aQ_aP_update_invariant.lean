import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBoxFock.PCFU.frameSmear
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.PCFU.aQ_aP_update_invariant`

The projection `aP ℓ i` averages the `i`-th slot of a configuration over the centred box
`acube ℓ` (`Submission.BoseGases.aP ℓ i Φ x = (1/ℓ³)·∫_{y ∈ acube ℓ} Φ (x[i ↦ y])`), and
`aQ ℓ i := id − aP ℓ i` is its complement.  The target records the elementary structural fact
that the *pair* operator `aQ ℓ j ∘ aP ℓ i` does not see the `i`-th slot, for `i ≠ j`:

    (aQ ℓ j (aP ℓ i Θ)) (x[i ↦ z]) = (aQ ℓ j (aP ℓ i Θ)) x          (i ≠ j) .

This is the `i ≠ j` instance of the standard "sector operators act only on their own slot"
calculus; it is stated for an **arbitrary** `Θ : X n → ℝ` (no measurability or integrability
hypothesis), because the argument never needs one:

* `aP ℓ i Θ` is *constant in the `i`-th slot*, i.e.
  `aP ℓ i Θ (x[i ↦ z]) = aP ℓ i Θ x`, since the two defining integrals have integrands related by
  the double update `(x[i ↦ z])[i ↦ y] = x[i ↦ y]` (definitionally, no measure theory);
* writing `Ψ := aP ℓ i Θ`, the second term is `(1/ℓ³)∫_w Ψ ((x[i ↦ z])[j ↦ w])`; since `i ≠ j`
  the inner configuration equals `(x[j ↦ w])[i ↦ z]`, and `Ψ` ignores its `i`-th slot.  So the
  integrand is *pointwise* equal to the integrand of `aP ℓ j Ψ x`, and the integrals agree.

Both steps are pure `Function.update` bookkeeping, so the identity holds even when the defining
integrals are junk (non-integrable integrands, or `ℓ = 0`), which is what makes it usable as a
rewriting rule in arbitrary state expressions.

The two structural inputs are proved as `aP_update_self` and `aP_aP_update_inner` below; they are
hypothesis-free strengthenings of `Submission.BoseGases.aP_const_in_coord` and of the `i ≠ j`
case of `Submission.BoseGases.aP_pair_const_in_j` (those carry `0 < ℓ` and `Continuous Φ`, which
the proofs do not use).
-/

namespace Work.BoseBoxFock.PCFU

/-- `aP ℓ i Θ` does not depend on the value of the `i`-th coordinate. -/
lemma aP_update_self {n : ℕ} {ℓ : ℝ} (i : Fin n) (Θ : Submission.BoseGases.X n → ℝ)
    (x : Submission.BoseGases.X n) (z : EuclideanSpace ℝ (Fin 3)) :
    Submission.BoseGases.aP ℓ i Θ (Function.update x i z) = Submission.BoseGases.aP ℓ i Θ x := by
  unfold Submission.BoseGases.aP
  congr 1
  apply MeasureTheory.integral_congr_ae
  filter_upwards with y
  simp only [Function.update_idem]

/-- `aP ℓ j (aP ℓ i Θ)` does not depend on the value of the `i`-th coordinate, for `i ≠ j`
(the inner projection already averages the `i`-th slot away). -/
lemma aP_aP_update_inner {n : ℕ} {ℓ : ℝ} {i j : Fin n} (hij : i ≠ j)
    (Θ : Submission.BoseGases.X n → ℝ) (x : Submission.BoseGases.X n)
    (z : EuclideanSpace ℝ (Fin 3)) :
    Submission.BoseGases.aP ℓ j (Submission.BoseGases.aP ℓ i Θ) (Function.update x i z)
      = Submission.BoseGases.aP ℓ j (Submission.BoseGases.aP ℓ i Θ) x := by
  unfold Submission.BoseGases.aP
  congr 1
  apply MeasureTheory.integral_congr_ae
  filter_upwards with w
  congr 1
  apply MeasureTheory.integral_congr_ae
  filter_upwards with y
  congr 1
  rw [Function.update_comm hij, Function.update_idem]

theorem aQ_aP_update_invariant {n : ℕ} {i j : Fin n} (hij : i ≠ j) {ℓ : ℝ}
    {Θ : Submission.BoseGases.X n → ℝ} (x : Submission.BoseGases.X n)
    (z : EuclideanSpace ℝ (Fin 3)) :
    Submission.BoseGases.aQ ℓ j (Submission.BoseGases.aP ℓ i Θ) (Function.update x i z)
      = Submission.BoseGases.aQ ℓ j (Submission.BoseGases.aP ℓ i Θ) x := by
  have hA := aP_update_self (ℓ := ℓ) i Θ x z
  have hB := aP_aP_update_inner (ℓ := ℓ) hij Θ x z
  simp only [Submission.BoseGases.aQ, hA, hB]

end Work.BoseBoxFock.PCFU
