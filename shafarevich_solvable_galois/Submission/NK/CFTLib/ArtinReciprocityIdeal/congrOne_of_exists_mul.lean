import Mathlib
import Submission.NK.CFTLib.ArtinReciprocityIdeal.LangDefs
import Submission.NK.CFTLib.Arl.exists_isCongruenceSubgroup_and_adjust
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `a ≡ 1 mod* (m)` from `a - 1 = m · c` with `c` an algebraic integer

The congruence condition `CongrOne m a` of the principal ray (Lang's `P(c)`) has two parts:
the `𝔭`-adic congruence `a ≡ 1 mod m` at every finite prime `𝔭` dividing `(m)`, and total
positivity at the real places.

This file proves that the *finite* part follows from the purely algebraic hypothesis that
`a - 1 = m · c` for an algebraic integer `c`: at a prime `𝔭` containing `m`, the adic valuation
of `a - 1 = m · c` is that of `m` times the valuation of the algebraic integer `c`, and the
latter is `≤ 1` because `𝓞 K` is contained in the valuation ring of the adic completion.
(The real-place part is a hypothesis, being a genuine sign condition.)
-/

open scoped NumberField
open NumberField IsDedekindDomain

namespace NK.CFTLib.ArtinReciprocityIdeal

theorem congrOne_of_exists_mul {K : Type} [Field K] [NumberField K] (m : ℕ) (a : Kˣ)
    (c : NumberField.RingOfIntegers K)
    (hc : (a : K) - 1 = (m : K) * (c : K))
    (hpos : ∀ (w : NumberField.InfinitePlace K) (hw : w.IsReal),
      0 < (NumberField.InfinitePlace.Completion.ringEquivRealOfIsReal hw)
            (algebraMap K w.Completion (a : K))) :
    NK.CFTLib.ArtinReciprocityIdeal.CongrOne m a := by
  constructor
  · intro v hv
    -- an algebraic integer has adic valuation `≤ 1`
    have hval_c : Valued.v (algebraMap K (v.adicCompletion K) (c : K)) ≤ 1 := by
      have h := IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation
        (K := K) (R := 𝓞 K) v c
      rw [← IsScalarTower.algebraMap_apply (𝓞 K) K (v.adicCompletion K) c]
      exact h.trans_le (IsDedekindDomain.HeightOneSpectrum.valuation_le_one v c)
    -- `algebraMap K κ (a - 1) = m · algebraMap K κ c`
    have hkey : algebraMap K (v.adicCompletion K) (a : K) - 1
        = ((m : ℕ) : v.adicCompletion K) * algebraMap K (v.adicCompletion K) (c : K) := by
      calc algebraMap K (v.adicCompletion K) (a : K) - 1
          = algebraMap K (v.adicCompletion K) (a : K)
              - algebraMap K (v.adicCompletion K) (1 : K) := by rw [map_one]
        _ = algebraMap K (v.adicCompletion K) ((a : K) - 1) := by rw [map_sub]
        _ = algebraMap K (v.adicCompletion K) ((m : K) * (c : K)) := by rw [hc]
        _ = algebraMap K (v.adicCompletion K) (m : K)
              * algebraMap K (v.adicCompletion K) (c : K) := by rw [map_mul]
        _ = ((m : ℕ) : v.adicCompletion K) * algebraMap K (v.adicCompletion K) (c : K) := by
              rw [map_natCast]
    rw [hkey, map_mul]
    simpa using mul_le_mul_right hval_c (Valued.v (((m : ℕ) : v.adicCompletion K)))
  · exact hpos

end NK.CFTLib.ArtinReciprocityIdeal
