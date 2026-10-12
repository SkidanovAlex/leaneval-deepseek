import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixR.LatticeW1sqParseval
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixR.GramMassWide` — the mass Gram bound for the real part of a lattice sum

For any finite family `z : Lab N → ℂ` of coefficients supported on a finite set `S` of
box-lattice mode labels, the **real part** of the lattice sum

  `u(y) = ∑_{k ∈ S} z k · labChar ℓ N k y`,  `labChar ℓ N k y = e^{i⟪kmomLab ℓ N k, y⟫}`

satisfies the `L²` mass bound

  `∫_{boxL ℓ} (Re u)² ≤ ℓ³ ∑_{k ∈ S} ‖z k‖²`.

This is the mass counterpart of `Work.BoseFixR.GramEnergyWide` (which bounds the gradient).
The proof is two lines of mathematics: pointwise, `(Re w)² ≤ ‖w‖²` for a complex number,
so the real part may be replaced by the full complex sum, and then the Parseval identity
`Work.BoseFixR.integral_normSq_labChar_sum` (orthogonality of the lattice characters,
`Work.BoseFixR.LatticeParsevalGram`) computes the integral exactly as `ℓ³ ∑ ‖z k‖²`.

Note the smul in the statement is the scalar multiplication of `ℂ` on itself, i.e. the
product `z k * labChar ℓ N k y`; this is the only rewriting step needed.
-/

noncomputable section

open scoped BigOperators
open MeasureTheory Filter

namespace Work.BoseFixR

set_option maxHeartbeats 1000000

-- `Integrable.of_bound` takes `IsFiniteMeasure` as an instance argument, so the local
-- `haveI` below is not a stylistic choice; silence the linter that suggests otherwise.
set_option linter.style.haveILetI false

/-- A lattice character has norm one.  (Local copy, kept for self-containedness.) -/
lemma norm_labChar_wide (ℓ : ℝ) (N : ℕ) (k : Work.BoseBoxFock.Lab N)
    (x : EuclideanSpace ℝ (Fin 3)) : ‖labChar ℓ N k x‖ = 1 := by
  rw [labChar, Complex.norm_exp_I_mul_ofReal]

/-- A finite lattice sum of characters with complex coefficients is integrable in squared norm
on the box `boxL ℓ`: it is continuous, and bounded by `(∑_k ‖c k‖)²` there, while the box has
finite volume. -/
lemma integrableOn_normSq_labChar_sum_wide {ℓ : ℝ} (N : ℕ)
    (K : Finset (Work.BoseBoxFock.Lab N)) (c : Work.BoseBoxFock.Lab N → ℂ) :
    IntegrableOn (fun x : EuclideanSpace ℝ (Fin 3) =>
      ‖∑ k ∈ K, c k * labChar ℓ N k x‖ ^ 2) (boxL ℓ) := by
  haveI : IsFiniteMeasure (volume.restrict (boxL ℓ)) :=
    isFiniteMeasure_restrict.mpr (volume_boxL_ne_top ℓ)
  have hcont : Continuous (fun x : EuclideanSpace ℝ (Fin 3) =>
      ∑ k ∈ K, c k * labChar ℓ N k x) :=
    continuous_finsetSum K (fun k _ => continuous_const.mul (continuous_labChar ℓ N k))
  refine Integrable.of_bound (hcont.norm.pow 2).aestronglyMeasurable ((∑ k ∈ K, ‖c k‖) ^ 2)
    (Eventually.of_forall fun x => ?_)
  have h1 : ‖∑ k ∈ K, c k * labChar ℓ N k x‖ ≤ ∑ k ∈ K, ‖c k‖ := by
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ => ?_)
    rw [norm_mul, norm_labChar_wide, mul_one]
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  exact pow_le_pow_left₀ (norm_nonneg _) h1 2

/-- **The mass Gram bound.**  The `L²` norm squared on the box of the real part of a finite
lattice sum is bounded by `ℓ³` times the sum of the squared moduli of its coefficients. -/
theorem GramMassWide {ℓ : ℝ} (hℓ : 0 < ℓ) {N : ℕ} (S : Finset (Work.BoseBoxFock.Lab N))
    (z : Work.BoseBoxFock.Lab N → ℂ) :
    ∫ x in boxL ℓ, ((∑ k ∈ S, z k • Work.BoseFixR.labChar ℓ N k x).re) ^ 2
      ≤ ℓ ^ 3 * ∑ k ∈ S, ‖z k‖ ^ 2 := by
  -- the scalar multiplication of `ℂ` on itself is the product
  have hsmul : ∀ x : EuclideanSpace ℝ (Fin 3),
      (∑ k ∈ S, z k • labChar ℓ N k x) = ∑ k ∈ S, z k * labChar ℓ N k x :=
    fun x => Finset.sum_congr rfl fun k _ => smul_eq_mul _ _
  calc ∫ x in boxL ℓ, ((∑ k ∈ S, z k • labChar ℓ N k x).re) ^ 2
      = ∫ x in boxL ℓ, ((∑ k ∈ S, z k * labChar ℓ N k x).re) ^ 2 :=
        integral_congr_ae (Eventually.of_forall fun x => by simp only [hsmul x])
    _ ≤ ∫ x in boxL ℓ, ‖∑ k ∈ S, z k * labChar ℓ N k x‖ ^ 2 :=
        integral_mono_of_nonneg (Eventually.of_forall fun x => sq_nonneg _)
          (integrableOn_normSq_labChar_sum_wide N S z)
          (Eventually.of_forall fun x => re_sq_le_normSq _)
    _ = ℓ ^ 3 * ∑ k ∈ S, ‖z k‖ ^ 2 := integral_normSq_labChar_sum hℓ N S z

end Work.BoseFixR
