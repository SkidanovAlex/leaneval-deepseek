import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixR.FarLatDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixR.FarLat.ofRealPeriodAeEqLatticeSum`

The passage from the **real** lattice sum `LatGreen.period W ℓ x = Σ'_{n∈ℤ³} W (x - ℓn)` to the
`ℝ≥0∞`-valued lattice sum `Σ'_{n∈ℤ³} ENNReal.ofReal (W (x - ℓn))`, a.e. in `x`.

Mathematically there is nothing to prove: `ENNReal.ofReal` is additive on nonnegative reals and
commutes with infinite sums of nonnegative terms.  The two side conditions in the statement do
exactly what is needed:

* `hWnn : 0 ≤ᵐ W` upgrades, by `ae_all_iff` (the index `Fin 3 → ℤ` is countable) and the
  measure preservation of the translations `x ↦ x - ℓn`, to the *pointwise-in-`n`* a.e. statement
  `0 ≤ W (x - ℓn)` for every `n`, at the same a.e. `x`;
* `hper` supplies the `Summable` hypothesis of `ENNReal.ofReal_tsum_of_nonneg`, which is what makes
  `ofReal (∑' n, f n) = ∑' n, ofReal (f n)` true for a real `tsum` (without summability the real
  `tsum` of a non-summable family is the junk value `0`).
-/

noncomputable section

open MeasureTheory Filter
open scoped ENNReal BigOperators

namespace Work.BoseFixR.FarLat

/-- **A.e. nonnegativity propagates to every lattice translate, simultaneously in the label.**
For an a.e. nonnegative charge `W`, for a.e. `x` every summand `W (x - ℓn)` of the periodisation
is nonnegative.  (Countability of `Fin 3 → ℤ` + measure preservation of the translations.) -/
lemma ae_forall_nonneg_sub_lat {ℓ : ℝ} {W : EuclideanSpace ℝ (Fin 3) → ℝ}
    (hWnn : 0 ≤ᵐ[(MeasureTheory.volume : Measure (EuclideanSpace ℝ (Fin 3)))] W) :
    ∀ᵐ x : EuclideanSpace ℝ (Fin 3), ∀ n : Fin 3 → ℤ,
      0 ≤ W (x - Work.BoseFixR.lat ℓ n) := by
  rw [MeasureTheory.ae_all_iff]
  intro n
  exact (MeasureTheory.measurePreserving_sub_right MeasureTheory.volume
    (Work.BoseFixR.lat ℓ n)).quasiMeasurePreserving.ae hWnn

theorem ofRealPeriodAeEqLatticeSum {ℓ : ℝ} {W : EuclideanSpace ℝ (Fin 3) → ℝ}
    (hWnn : 0 ≤ᵐ[MeasureTheory.volume] W)
    (hper : ∀ x : EuclideanSpace ℝ (Fin 3),
      Summable (fun n : Fin 3 → ℤ => W (x - Work.BoseFixR.lat ℓ n))) :
    (fun x : EuclideanSpace ℝ (Fin 3) =>
        ENNReal.ofReal (Work.BoseFixR.LatGreen.period W ℓ x))
      =ᵐ[MeasureTheory.volume]
      fun x : EuclideanSpace ℝ (Fin 3) =>
        ∑' n : Fin 3 → ℤ, ENNReal.ofReal (W (x - Work.BoseFixR.lat ℓ n)) := by
  filter_upwards [ae_forall_nonneg_sub_lat (ℓ := ℓ) hWnn] with x hx
  exact ENNReal.ofReal_tsum_of_nonneg hx (hper x)

end Work.BoseFixR.FarLat
