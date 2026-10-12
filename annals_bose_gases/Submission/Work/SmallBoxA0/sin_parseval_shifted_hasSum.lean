import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Submission.Work.SmallBoxA0.sin_coeff_sq_summable
import Submission.Work.SmallBoxA0.sin_parseval_shifted
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The `HasSum` form of the shifted sine (Dirichlet) Parseval identity

`Work.SmallBoxA0.sin_parseval_shifted` gives the *equality of the `tsum`* with the
`L²`-integral of `F`: the Dirichlet (sine) basis `sin ((kπ/ℓ)(· + ℓ/2))`, `k ≥ 1`, is
complete in `L²[−ℓ/2, ℓ/2]`:

    ∫_{−ℓ/2}^{ℓ/2} F² = ∑'_{k≥0} (2/ℓ) (∫_{−ℓ/2}^{ℓ/2} F(x) sin ((kπ/ℓ)(x + ℓ/2)) dx)².

The present lemma upgrades that `tsum` identity to the genuine *convergence* statement
`HasSum` for the same (nonnegative) series.  The missing ingredient is only summability
of the summands — which is *not* a formal consequence of the `ℝ`-valued `tsum` identity
(`∑'` is the junk value `0` on non-summable series) — and it is supplied separately by
`Work.SmallBoxA0.sin_coeff_sq_summable` (proved from Parseval's identity for the Fourier
series of the odd extension `oddExt F`, whose Fourier coefficients are `−I` times the
sine coefficients; see `fourierCoeff_oddExt`).

With summability in hand, `HasSum f (∑' f)` (`Summable.hasSum`) together with the `tsum`
identity gives the statement; the two summand families agree because
`x / (ℓ/2) = (2/ℓ) x`.
-/

set_option autoImplicit false

namespace Work.SmallBoxA0

open MeasureTheory

/-- **Shifted sine Parseval identity, `HasSum` form.**  For a continuous `F` and `ℓ > 0`
the series of the squared (normalised) shifted sine coefficients converges, with sum the
`L²`-integral of `F`:

    ∑_{k≥0} (∫_{−ℓ/2}^{ℓ/2} F(x) sin ((kπ/ℓ)(x + ℓ/2)) dx)² / (ℓ/2) = ∫_{−ℓ/2}^{ℓ/2} F². -/
lemma sin_parseval_shifted_hasSum {ℓ : ℝ} (hℓ : 0 < ℓ) {F : ℝ → ℝ} (hF : Continuous F) :
    HasSum (fun k : ℕ =>
        (∫ x in (-(ℓ / 2))..(ℓ / 2),
            F x * Real.sin (((k : ℝ) * Real.pi / ℓ) * (x + ℓ / 2))) ^ 2 / (ℓ / 2))
      (∫ x in (-(ℓ / 2))..(ℓ / 2), (F x) ^ 2) := by
  -- The two summand families are scalar multiples of each other.
  have hgen : ∀ a : ℝ, a / (ℓ / 2) = (2 / ℓ) * a := by
    intro a
    field_simp
  have hterm : ∀ k : ℕ,
      (∫ x in (-(ℓ / 2))..(ℓ / 2),
          F x * Real.sin (((k : ℝ) * Real.pi / ℓ) * (x + ℓ / 2))) ^ 2 / (ℓ / 2)
        = (2 / ℓ) * (∫ x in (-(ℓ / 2))..(ℓ / 2),
            F x * Real.sin (((k : ℝ) * Real.pi / ℓ) * (x + ℓ / 2))) ^ 2 :=
    fun k => hgen _
  -- Summability of the target family, from summability of the `2/ℓ`-multiple.
  have hst : Summable (fun k : ℕ =>
      (∫ x in (-(ℓ / 2))..(ℓ / 2),
          F x * Real.sin (((k : ℝ) * Real.pi / ℓ) * (x + ℓ / 2))) ^ 2 / (ℓ / 2)) := by
    refine (sin_coeff_sq_summable hℓ hF).mul_left (2 / ℓ) |>.congr (fun k => ?_)
    exact (hterm k).symm
  -- The value of the `tsum` is the already-proved `tsum` identity.
  have hval : (∑' k : ℕ,
        (∫ x in (-(ℓ / 2))..(ℓ / 2),
            F x * Real.sin (((k : ℝ) * Real.pi / ℓ) * (x + ℓ / 2))) ^ 2 / (ℓ / 2))
      = ∫ x in (-(ℓ / 2))..(ℓ / 2), (F x) ^ 2 := by
    rw [tsum_congr hterm]
    exact (sin_parseval_shifted hℓ hF).symm
  rw [← hval]
  exact hst.hasSum

end Work.SmallBoxA0
