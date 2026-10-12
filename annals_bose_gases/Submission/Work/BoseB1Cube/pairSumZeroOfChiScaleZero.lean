import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixB1.boxQ1CrossSqrtB1
import Submission.Work.BoseFixB1P.boxPeel_general
import Submission.Work.BoseFixB1P.boxQ1_pair_replace
import Submission.Work.BoseFixB1S.PQIdentAux
import Submission.Work.BoseFixB1S.boxPeelGen
import Submission.Work.BoseFixB1S.pqwCutGeom
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseB1Cube

-- INTENDED PROOF SKETCH: `Work.BoseFixB1.pairSum v M ℓ d u Φ` is definitionally
-- `∫ x in abox n ℓ, (Φ x)^2 * ((1/2) * ∑ p ∈ pairSet n, wSmallPair M ℓ d u v (x p.1) (x p.2))`;
-- `Submission.BoseGases.wSmallPair M ℓ d u h x y = chiSmallB M ℓ d u x * (…) * chiSmallB M ℓ d u y`
-- and `chiSmallB M ℓ d u z = chiScale ℓ z * chiSmall M ((ℓ*d)⁻¹ • z - u)` is a product, so
-- `hzero` makes the kernel `0` as soon as one coordinate lies in `dlBox ℓ d u`; `hIn` puts all
-- coordinates in `dlBox` on the a.e. set `{Φ ≠ 0}`.  So the integrand is `0` a.e. on `abox n ℓ`
-- and `MeasureTheory.integral_eq_zero_of_ae` finishes.  No smoothness/measurability of `Φ` needed.
theorem pairSumZeroOfChiScaleZero {v : EuclideanSpace ℝ (Fin 3) → ℝ} (h : Work.UBB.ScatSol v)
    {M : ℕ} {ℓ d : ℝ} (u : EuclideanSpace ℝ (Fin 3)) {n : ℕ}
    {Φ : Submission.BoseGases.X n → ℝ}
    (hzero : ∀ x ∈ Submission.BoseGases.dlBox ℓ d u, Submission.BoseGases.chiScale ℓ x = 0)
    (hIn : ∀ᵐ x ∂(MeasureTheory.volume.restrict (Submission.BoseGases.abox n ℓ)),
      Φ x ≠ 0 → ∀ i : Fin n, x i ∈ Submission.BoseGases.dlBox ℓ d u) :
    Work.BoseFixB1.pairSum v M ℓ d u Φ = 0 := by
  -- `pairSum` is the set integral of `Φ²·½Σ_{p∈pairSet n} wSmallPair(x_{p.1},x_{p.2})` over
  -- `abox n ℓ`; it suffices to show the integrand vanishes a.e. there.
  unfold Work.BoseFixB1.pairSum
  refine MeasureTheory.integral_eq_zero_of_ae ?_
  filter_upwards [hIn] with x hx
  by_cases hΦ : Φ x = 0
  · -- the `Φ²` prefactor already vanishes
    simp [hΦ]
  · -- otherwise every coordinate lies in `dlBox`, so the *first* `chiSmallB` factor of the
    -- kernel `wSmallPair` vanishes by `hzero` and the whole kernel is `0`.
    have hall : ∀ i : Fin n, x i ∈ Submission.BoseGases.dlBox ℓ d u := hx hΦ
    have hker : ∀ p ∈ Submission.BoseGases.pairSet n,
        Submission.BoseGases.wSmallPair M ℓ d u v (x p.1) (x p.2) = 0 := by
      intro p _
      rw [Submission.BoseGases.wSmallPair]
      have hchi : Submission.BoseGases.chiSmallB M ℓ d u (x p.1) = 0 := by
        rw [Submission.BoseGases.chiSmallB, hzero (x p.1) (hall p.1), zero_mul]
      simp [hchi]
    rw [Finset.sum_eq_zero hker]
    simp

end Work.BoseB1Cube
