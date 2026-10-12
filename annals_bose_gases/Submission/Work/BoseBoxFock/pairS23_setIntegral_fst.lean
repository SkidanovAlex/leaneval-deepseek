import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Submission.Work.BoseBoxFock.pairGc23Aux
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseBoxFock

open MeasureTheory

-- The integrability hypothesis `hf` is part of the requested statement but is not needed: the
-- identity is a Fubini statement about a function of the first coordinate alone, and
-- `MeasureTheory.integral_fun_fst` has no integrability side condition.
set_option linter.unusedVariables false in

/-- **The `prod`-integral of a fibre function over the clean `pairGc23` box.**

The box `pairS23 ℓ p` is the product of the `n − 2`-particle box `boxPiSet (pairFib23 n p) ℓ`
with the two kernel boxes `boxL ℓ ×ˢ boxL ℓ` (of volume `ℓ ^ 6`), and the integrand depends only
on the fibre coordinate.  Hence the integral factors as the volume of the kernel boxes times the
integral of the fibre function. -/
theorem pairS23_setIntegral_fst {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) (p : Fin n × Fin n)
    {f : (Work.BoseBoxFock.pairFib23 n p → EuclideanSpace ℝ (Fin 3)) → ℝ}
    (hf : MeasureTheory.IntegrableOn f (Work.BoseBoxFock.boxPiSet (Work.BoseBoxFock.pairFib23 n p) ℓ)) :
    (∫ z in Work.BoseBoxFock.pairS23 ℓ p, f z.1)
      = ℓ ^ 6 * ∫ x'' in Work.BoseBoxFock.boxPiSet (Work.BoseBoxFock.pairFib23 n p) ℓ, f x'' := by
  -- The restriction of the product volume to `pairS23 ℓ p` is the product of the restricted
  -- fibre measure with the product of the two restricted kernel measures.
  rw [pairS23_restrict_eq_prod]
  -- The integrand depends only on the first coordinate: Fubini for such integrands.
  rw [integral_fun_fst]
  -- The two kernel boxes have volume `ℓ ^ 6`.
  rw [pairS23_second_volume_real ℓ hℓ]
  simp

end Work.BoseBoxFock
