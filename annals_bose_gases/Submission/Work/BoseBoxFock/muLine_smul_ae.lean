import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBoxFock.chiRowDefs2
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.muLine_smul_ae` — the `μ`-line is `ℝ`-linear in the weight

The `μ`-line of the χ-row is

    `muLine n ℓ w Φ = 2 * Σ_j ∫_{abox}(Q_jΦ)·w(x_j)·(P_jΦ)`

(`chiRowDefs.muLine`).  Its integrand at slot `j` is `(Q_jΦ x)·(w (x j))·(P_jΦ x)`, i.e. it is
the *pointwise* product of the slot factor `w (x j)` with the two slot fields; hence multiplying
the weight by a constant `c` multiplies the integrand by `c` **pointwise** (not merely a.e.), and
the Bochner integral is `ℝ`-homogeneous (`MeasureTheory.integral_const_mul`, which is
unconditional — no integrability hypothesis, since for `c ≠ 0` the two integrands are
simultaneously integrable and both integrals vanish otherwise).

This closes the statement with no analytic input at all: the hypotheses `hℓ`, `hΦc`, `hwm`, `hw`
are not used and are kept only because the request fixes the statement verbatim.

Everything here is `sorry`-free.
-/

namespace Work.BoseBoxFock

open MeasureTheory
open scoped BigOperators
open Submission.BoseGases

theorem muLine_smul_ae {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {Φ : Submission.BoseGases.X n → ℝ}
    (hΦc : Continuous Φ) {w : EuclideanSpace ℝ (Fin 3) → ℝ}
    (hwm : MeasureTheory.AEStronglyMeasurable w
      (MeasureTheory.volume.restrict (Submission.BoseGases.acube ℓ)))
    {K : ℝ} (hw : ∀ z ∈ Submission.BoseGases.acube ℓ, |w z| ≤ K) (c : ℝ) :
    Work.BoseBoxFock.muLine n ℓ (fun z => c * w z) Φ
      = c * Work.BoseBoxFock.muLine n ℓ w Φ := by
  simp only [muLine]
  -- the slot sum is `c` times the original slot sum, slot by slot
  have hsum : (∑ j : Fin n, ∫ x in Submission.BoseGases.abox n ℓ,
        (aQ ℓ j Φ x) * (c * w (x j)) * (aP ℓ j Φ x))
      = c * ∑ j : Fin n, ∫ x in Submission.BoseGases.abox n ℓ,
        (aQ ℓ j Φ x) * w (x j) * (aP ℓ j Φ x) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [← integral_const_mul c (fun x : Submission.BoseGases.X n =>
      (aQ ℓ j Φ x) * w (x j) * (aP ℓ j Φ x))]
    refine integral_congr_ae (Filter.Eventually.of_forall (fun x => ?_))
    ring
  rw [hsum]
  ring

end Work.BoseBoxFock
