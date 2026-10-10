import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Submission.Work.SSGRoute.LocalFieldArith.principalUnits_deep_mem_pow
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Deep principal units of a `𝔭`-adic completion are `p`-th powers

For a number field `K`, a finite prime `𝔭`, a prime `p` and the level-`M`
exponential/logarithm `D` of `κ = 𝔭.adicCompletion K` (`NK.LocalInputs.PowerQuotient.LogData 𝔭 M`),
this file records the statement of `Work.SSGRoute.LocalFieldArith.principalUnits_deep_mem_pow`
for units of the field `κ` rather than of its ring of integers `𝒪_κ`.

A unit `w ∈ κˣ` whose valuation is `1` is an integral unit, i.e. it lies in the image of
`𝒪_κˣ → κˣ`; if moreover `v (w - 1) ≤ exp (-(M + e))`, where `e` is the exponent of `p` in the
valuation of `κ` (i.e. `v p = exp (-e)`), then `w` is a `p`-th power of a unit of `κ`.  This is
`principalUnits_deep_mem_pow` applied to the integral unit representing `w`, transported back to
`κˣ` along the inclusion `𝒪_κˣ → κˣ`.
-/

open IsDedekindDomain.HeightOneSpectrum
open scoped NumberField WithZero
open IsDedekindDomain

namespace Work.SSGRoute

noncomputable section

theorem adicCompletion_pow_of_deep_principalUnit (K : Type) [Field K] [NumberField K]
    (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    {M : ℕ} (D : NK.LocalInputs.PowerQuotient.LogData Q M) (p : ℕ) [Fact p.Prime] {e : ℕ}
    (hpe : (Valued.v : Valuation (Q.adicCompletion K) (WithZero (Multiplicative ℤ)))
        ((p : ℕ) : Q.adicCompletion K) = WithZero.exp (-(e : ℤ)))
    {w : (Q.adicCompletion K)ˣ}
    (hval : Valued.v ((w : Q.adicCompletion K)) = 1)
    (hsub : Valued.v ((w : Q.adicCompletion K) - 1) ≤ WithZero.exp (-(((M + e : ℕ) : ℤ)))) :
    ∃ c : (Q.adicCompletion K)ˣ, c ^ p = w := by
  -- `w` has valuation `1`, hence is an integral unit `⟨w, _⟩ ∈ 𝒪_κ`.
  have hw_mem : (w : Q.adicCompletion K) ∈ Q.adicCompletionIntegers K :=
    (IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers
      (NumberField.RingOfIntegers K) K Q).mpr (le_of_eq hval)
  have hw_isUnit : IsUnit (⟨(w : Q.adicCompletion K), hw_mem⟩ : Q.adicCompletionIntegers K) :=
    (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one).mpr hval
  -- the corresponding unit of `𝒪_κˣ`
  set u : (Q.adicCompletionIntegers K)ˣ := hw_isUnit.unit with hu
  have hu_spec : ((u : Q.adicCompletionIntegers K)) = ⟨(w : Q.adicCompletion K), hw_mem⟩ :=
    hw_isUnit.unit_spec
  have hu_coe : ((u : Q.adicCompletionIntegers K) : Q.adicCompletion K)
      = (w : Q.adicCompletion K) := by
    rw [hu_spec]
  -- `v (w - 1) ≤ exp (-(M + e))` says exactly `u ∈ pu 𝔭 (M + e)`
  have hu_mem : u ∈ NK.LocalInputs.PowerQuotient.pu Q (M + e) := by
    rw [NK.LocalInputs.PowerQuotient.mem_pu_iff_val]
    rw [hu_coe]
    exact hsub
  -- the deep principal unit `u` is a `p`-th power in `𝒪_κˣ`
  obtain ⟨y, hy⟩ :=
    Work.SSGRoute.LocalFieldArith.principalUnits_deep_mem_pow Q D p hpe hu_mem
  -- transport along `𝒪_κˣ → κˣ`
  refine ⟨Units.map (ValuationSubring.subtype (Q.adicCompletionIntegers K)).toMonoidHom y, ?_⟩
  have hmapu : Units.map (ValuationSubring.subtype (Q.adicCompletionIntegers K)).toMonoidHom u
      = w := by
    apply Units.ext
    rw [Units.coe_map]
    change ((u : Q.adicCompletionIntegers K) : Q.adicCompletion K) = (w : Q.adicCompletion K)
    rw [hu_coe]
  rw [← map_pow, hy, hmapu]

end

end Work.SSGRoute
