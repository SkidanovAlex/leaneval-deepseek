import ChallengeDeps
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseSym.Bridge.abs_symAvgF_le
import Submission.Work.BoseSym.Bridge.aestronglyMeasurable_symAvgF
import Submission.Work.BoseSym.Bridge.intOnBox_symAvgF
import Submission.Work.BoseSym.Bridge.integral_symAvgF_mul_eq
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseSym.Bridge.integral_Vpot_symAvgF_sq_le_meas`

The weighted symmetrisation inequality on the box, for a merely a.e. strongly
measurable, bounded test function `f`:

`∫_{box N L} V · (symAvgF N f)² ≤ ∫_{box N L} (symAvgF N V) · f²`

whenever `0 ≤ V` and `V` is integrable on the box.

## Route

Write `symAvgF N u x = (N!)⁻¹ · ∑_σ u (actPerm σ x)`.  Two facts are used.

* *Pointwise Jensen.*  Cauchy–Schwarz on the finite group `Equiv.Perm (Fin N)`
  gives `(symAvgF N f x)² ≤ symAvgF N (f²) x` (already proved as
  `IntegralSqSymAvg.sq_symAvgF_le_symAvgF_sq`).  Multiplying by the weight
  `V x ≥ 0` and integrating (monotone convergence for integrals) yields

  `∫ V · (symAvgF N f)² ≤ ∫ V · (symAvgF N (f²))`.

* *Self-adjointness of `symAvgF`* (`Bridge.integral_symAvgF_mul_eq`): for
  `V` integrable on the box and `g` bounded and a.e. strongly measurable,

  `∫ (symAvgF N V) · g = ∫ V · (symAvgF N g)`,

  obtained by expanding the average, exchanging the finite sum with the
  integral and changing variables `x ↦ actPerm σ x` (the box and Lebesgue
  measure on it are invariant under relabelling the particles).  With
  `g = f²` this turns the right-hand side of the previous display into the
  right-hand side of the statement.

Integrability of the intermediate quantities comes from
`Integrable.mul_bdd`: `V` is integrable and both `symAvgF N (f²)` and
`symAvgF N V` are bounded (`abs_symAvgF_le`), so all products are integrable.
-/

namespace Work.BoseSym.Bridge

open MeasureTheory Filter
open scoped Topology Real

theorem integral_Vpot_symAvgF_sq_le_meas {N : ℕ} {L : ℝ} {V : Work.BoseSym.Conf N → ℝ}
    (hV0 : 0 ≤ V) (hVint : Work.BoseSym.IntOnBox N L V) {f : Work.BoseSym.Conf N → ℝ}
    (hfm : MeasureTheory.AEStronglyMeasurable f
      (MeasureTheory.volume.restrict (BoseGases.box N L)))
    {C : ℝ} (hC : 0 ≤ C) (hf : ∀ x, |f x| ≤ C) :
    ∫ x in BoseGases.box N L, V x * (Work.BoseSym.symAvgF N f x) ^ 2 ≤
      ∫ x in BoseGases.box N L, (Work.BoseSym.symAvgF N V) x * (f x) ^ 2 := by
  -- the squared modulus `f²` is a.e. strongly measurable and bounded by `C²`
  have hgm : MeasureTheory.AEStronglyMeasurable (fun y : Work.BoseSym.Conf N => (f y) ^ 2)
      (volume.restrict (BoseGases.box N L)) := by
    have h : (fun y : Work.BoseSym.Conf N => (f y) ^ 2) = f * f := by
      funext y; rw [Pi.mul_apply, pow_two]
    rw [h]
    exact hfm.mul hfm
  have hgD : ∀ x : Work.BoseSym.Conf N, |(f x) ^ 2| ≤ C ^ 2 := by
    intro x
    rw [abs_of_nonneg (sq_nonneg _), sq_le_sq, abs_of_nonneg hC]
    exact hf x
  -- the weighted average `V · symAvgF (f²)` is integrable
  have hgint : Integrable (fun x : Work.BoseSym.Conf N =>
      V x * Work.BoseSym.symAvgF N (fun y => (f y) ^ 2) x)
      (volume.restrict (BoseGases.box N L)) :=
    hVint.mul_bdd (aestronglyMeasurable_symAvgF hgm)
      (Eventually.of_forall (fun x => by
        rw [Real.norm_eq_abs]
        exact abs_symAvgF_le (sq_nonneg C) hgD x))
  -- pointwise Jensen, multiplied by the nonnegative weight `V`
  have hmono : ∫ x in BoseGases.box N L, V x * (Work.BoseSym.symAvgF N f x) ^ 2 ≤
      ∫ x in BoseGases.box N L, V x * Work.BoseSym.symAvgF N (fun y => (f y) ^ 2) x :=
    integral_mono_of_nonneg
      (Eventually.of_forall (fun x => mul_nonneg (hV0 x) (sq_nonneg _)))
      hgint
      (Eventually.of_forall (fun x => mul_le_mul_of_nonneg_left
        (Work.BoseSym.Perm.IntegralSqSymAvg.sq_symAvgF_le_symAvgF_sq f x) (hV0 x)))
  -- self-adjointness of `symAvgF` identifies the two weighted integrals
  have heq : ∫ x in BoseGases.box N L,
        V x * Work.BoseSym.symAvgF N (fun y => (f y) ^ 2) x =
      ∫ x in BoseGases.box N L, (Work.BoseSym.symAvgF N V) x * (f x) ^ 2 :=
    (integral_symAvgF_mul_eq hVint hgm (sq_nonneg C) hgD).symm
  linarith [hmono, heq]

end Work.BoseSym.Bridge
