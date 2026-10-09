import Mathlib
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The norm of a rational prime in a `𝔮`-adic completion, when `𝔮` does not divide it

For a number field `K`, a finite prime `𝔮` of `K` (a nonzero prime ideal of `𝓞 K`) and a natural
number `p` with `(p : 𝓞 K) ∉ 𝔮`, the image of `p` in the `𝔮`-adic completion `K_𝔮` is a unit,
hence has norm `1`:

  `‖(p : K_𝔮)‖ = 1`.

The mathematical content is that the normalized `𝔮`-adic absolute value of an algebraic integer
is `1` exactly when the integer is not divisible by `𝔮`
(`IsDedekindDomain.HeightOneSpectrum.adicAbv_coe_eq_one_iff`), combined with the identification of
the norm on `v.adicCompletion K` with `NumberField.HeightOneSpectrum.adicAbv`
(`NumberField.FinitePlace.norm_embedding`).
-/

namespace NK.GlobalCFTdeep.SecondInequality.KummerCase

open IsDedekindDomain.HeightOneSpectrum

/-- **The `𝔮`-adic norm of a rational prime not lying in `𝔮` is `1`.**

If the rational integer `p` is not contained in the finite prime `𝔮` of the number field `K`,
then the image of `p` in the `𝔮`-adic completion `K_𝔮` has norm `1`. -/
theorem norm_algebraMap_natCast_adicCompletion_eq_one_of_notMem {K : Type} [Field K]
    [NumberField K] (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    {p : ℕ} (hnot : (p : NumberField.RingOfIntegers K) ∉ q.asIdeal) :
    ‖algebraMap K (q.adicCompletion K) (p : K)‖ = 1 := by
  -- The `K`-algebra structure on the completion is given by the completion of the identity, so the
  -- image of `p` there is the image of `p` under the canonical embedding `K → K_𝔮`.
  have h1 : algebraMap K (q.adicCompletion K) (p : K)
      = NumberField.FinitePlace.embedding q (p : K) := by
    rw [IsDedekindDomain.HeightOneSpectrum.algebraMap_adicCompletion]; rfl
  rw [h1, NumberField.FinitePlace.norm_embedding]
  -- Rewrite `p ∈ K` as the image of `p ∈ 𝓞 K`, and apply the criterion for the `𝔮`-adic absolute
  -- value of an algebraic integer to be `1`.
  rw [show (p : K) = algebraMap (NumberField.RingOfIntegers K) K
        (p : NumberField.RingOfIntegers K) from (map_natCast _ p).symm]
  exact (IsDedekindDomain.HeightOneSpectrum.adicAbv_coe_eq_one_iff q
    (NumberField.HeightOneSpectrum.one_lt_absNorm_nnreal q) _).mpr hnot

end NK.GlobalCFTdeep.SecondInequality.KummerCase
