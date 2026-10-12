import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Submission.Work.OneBodyKin.kinFT_chi_eq
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.OneBodyKin.SymAPI` — elementary API of the symbol terms

The trivial estimates that make `famSym` usable, all consequence of the definitions:

* `symA_nonneg`, `symC_nonneg` — the two explicitly nonnegative terms;
* `abs_boxHat_le` — the box profile is bounded by the box volume, `|boxHat ℓ q| ≤ ℓ³`;
* `profHat_bound` — the bump profile is bounded by `profHat 0 = ∫χ`;
* `symD_zero` — the value of the cross symbol at `q = 0`;
**Warning.** These elementary estimates are *not* the pointwise symbol bound `SymBound`.  The
Cauchy–Schwarz bound on `symD` (`OneBodyKin/symD_abs_le_cs`) is an *equality* at `q = 0`
(`famSym ℓ F 0 = 0`, `famSym_zero`), but for `q ≠ 0` it loses exactly the correlation between
`symD(q)` and `symD(0)` that the true statement needs; the criterion it yields (see `README.md`
§5) is strictly stronger than `SymBound`.
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped ContDiff Topology Real BigOperators ENNReal

namespace Work.OneBodyKin

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

open Submission.BoseGases

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option linter.unusedVariables false

/-- The unprojected symbol term is nonnegative for a nonnegative symbol. -/
theorem symA_nonneg {F : ℝ → ℝ} (hF : ∀ r : ℝ, 0 ≤ F r) (ℓ : ℝ) (q : ℝ³) :
    0 ≤ symA ℓ F q := by
  unfold symA
  refine mul_nonneg (by positivity) (integral_nonneg (fun p => ?_))
  exact mul_nonneg (hF _) (sq_nonneg _)

/-- The mass symbol term is nonnegative for a nonnegative symbol. -/
theorem symC_nonneg {F : ℝ → ℝ} (hF : ∀ r : ℝ, 0 ≤ F r) (ℓ : ℝ) (q : ℝ³) :
    0 ≤ symC ℓ F q := by
  unfold symC
  refine mul_nonneg (mul_nonneg (symA_nonneg hF ℓ 0) (by positivity)) (sq_nonneg _)

/-- **The box profile is bounded by the box volume**, `|boxHat ℓ q| ≤ ℓ³` for `ℓ ≥ 0`.  (The
indicator of `acube ℓ` has `L¹`-norm `ℓ³`, and `boxHat` is its real Fourier transform.) -/
theorem abs_boxHat_le {ℓ : ℝ} (hℓ : 0 ≤ ℓ) (q : ℝ³) : |boxHat ℓ q| ≤ ℓ ^ 3 := by
  rw [boxHat]
  have hμ : (volume : Measure ℝ³) (acube ℓ) < ⊤ := acube_lt_top ℓ hℓ
  have h : ‖∫ z in acube ℓ, Real.cos (inner ℝ q z)‖
      ≤ (1 : ℝ) * (volume : Measure ℝ³).real (acube ℓ) :=
    norm_setIntegral_le_of_norm_le_const hμ
      (fun z _ => by simpa using Real.abs_cos_le_one (inner ℝ q z))
  rw [one_mul, MeasureTheory.measureReal_def, acube_volume ℓ hℓ,
    ENNReal.toReal_ofReal (by positivity : (0 : ℝ) ≤ ℓ ^ 3)] at h
  simpa using h

/-- The value of the cross symbol at `q = 0`. -/
theorem symD_zero (ℓ : ℝ) (F : ℝ → ℝ) :
    symD ℓ F 0 = ∫ p : ℝ³, F ‖p‖ * (profHat (ℓ • p)) ^ 2 := by
  unfold symD
  refine integral_congr_ae (Filter.Eventually.of_forall (fun p => ?_))
  simp only [zero_sub]
  rw [show ℓ • (-p) = -(ℓ • p) from by module, profHat_even]
  ring

end Work.OneBodyKin
