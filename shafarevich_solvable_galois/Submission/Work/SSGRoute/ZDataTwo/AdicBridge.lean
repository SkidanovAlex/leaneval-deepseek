import Mathlib
import Submission.Commons.NumberTheory.NumberField.Completion.val_le_exp_neg_iff_mem_maximalIdeal_pow
import Submission.Work.SSGRoute.GrunwaldEscapeCore.exists_pow_eq_of_isCongAt
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The adic bridge: an element congruence is a congruence in the completion

The one remaining element-level ingredient of the local congruence half of the `p = 2` sign
adjustment (`Work.SSGRoute.ZDataTwo.signAdjustment_mu2`): an element congruence
`s ≡ 1 (mod 𝔭^N)` *in the number field* implies the corresponding `IsCongAt` condition *in the
`𝔭`-adic completion*, i.e. the valuation of the image of `s - 1` is at most `exp (-N)`.

The proof uses exactly two banked ingredients:

* `Commons.NumberTheory.NumberField.Completion.val_le_exp_neg_iff_mem_maximalIdeal_pow`: for an
  element of the integers of the completion, `Valued.v x ≤ exp (-n)` holds exactly when `x` lies in
  the `n`-th power of the maximal ideal (this is where the uniformiser
  `exists_uniformizer_adicCompletionIntegers` — the maximal ideal is the span of an element of
  valuation `exp (-1)` — and multiplicativity of the valuation are used);
* the `N = 1` correspondence between `𝔭.asIdeal` and the maximal ideal of the completion's integer
  ring, from `IsDedekindDomain.HeightOneSpectrum.valuation_lt_one_iff_mem` together with
  `IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation'` (the completion's
  valuation restricts to the `𝔭`-valuation of `K`) and `Valuation.mem_maximalIdeal_iff`.

Powers are handled by `Ideal.map_pow` and an induction using `Ideal.mul_le_mul`.
-/

open NumberField

namespace Work.SSGRoute.ZDataTwo

/-- The `N = 1` correspondence: an element of the ring of integers is in `𝔭.asIdeal` exactly when
its image in the integers of the completion lies in the maximal ideal. -/
theorem algebraMap_mem_maximalIdeal_iff (K : Type) [Field K] [NumberField K]
    (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (y : NumberField.RingOfIntegers K) :
    algebraMap (NumberField.RingOfIntegers K) (𝔭.adicCompletionIntegers K) y ∈
        IsLocalRing.maximalIdeal (𝔭.adicCompletionIntegers K) ↔ y ∈ 𝔭.asIdeal := by
  -- the two `Valued.v`-descriptions of the two sides
  have hcoe : ((algebraMap (NumberField.RingOfIntegers K) (𝔭.adicCompletionIntegers K) y :
      𝔭.adicCompletionIntegers K) : 𝔭.adicCompletion K) =
      algebraMap K (𝔭.adicCompletion K) (y : K) :=
    IsScalarTower.algebraMap_apply (NumberField.RingOfIntegers K) K (𝔭.adicCompletion K) y
  have hA : (algebraMap (NumberField.RingOfIntegers K) (𝔭.adicCompletionIntegers K) y ∈
      IsLocalRing.maximalIdeal (𝔭.adicCompletionIntegers K)) ↔
      Valued.v (((algebraMap (NumberField.RingOfIntegers K) (𝔭.adicCompletionIntegers K) y :
        𝔭.adicCompletionIntegers K) : 𝔭.adicCompletion K)) < 1 :=
    Valuation.mem_maximalIdeal_iff (𝔭.adicCompletion K) (Valued.v (R := 𝔭.adicCompletion K))
  rw [hA, hcoe]
  simp only [IsDedekindDomain.HeightOneSpectrum.algebraMap_adicCompletion, Function.comp_apply]
  rw [IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
  exact IsDedekindDomain.HeightOneSpectrum.valuation_lt_one_iff_mem 𝔭 y

/-- **The adic bridge.**  If `s ∈ Kˣ` satisfies the element congruence `s - 1 ≡ 0 (mod 𝔭^N)`
(witnessed by `y ∈ 𝔭.asIdeal ^ N` with `(y : K) = (s : K) - 1`), then the image of `s` in the
`𝔭`-adic completion satisfies `IsCongAt K N 𝔭`: the valuation of the image of `s - 1` is at most
`exp (-N)`. -/
theorem isCongAt_adicCompletion_of_mem_asIdeal_pow (K : Type) [Field K] [NumberField K]
    (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (s : Kˣ) (N : ℕ) (y : NumberField.RingOfIntegers K)
    (hy : y ∈ 𝔭.asIdeal ^ N) (hys : (y : K) = (s : K) - 1) :
    NK.NUV2.RouteB.IsCongAt K N 𝔭
      (Units.map (algebraMap K (𝔭.adicCompletion K)).toMonoidHom s) := by
  classical
  have hcoe : ((algebraMap (NumberField.RingOfIntegers K) (𝔭.adicCompletionIntegers K) y :
      𝔭.adicCompletionIntegers K) : 𝔭.adicCompletion K) =
      algebraMap K (𝔭.adicCompletion K) (y : K) :=
    IsScalarTower.algebraMap_apply (NumberField.RingOfIntegers K) K (𝔭.adicCompletion K) y
  -- the image of `𝔭.asIdeal` lies in the maximal ideal of the completion's integer ring
  have hmap : Ideal.map (algebraMap (NumberField.RingOfIntegers K) (𝔭.adicCompletionIntegers K))
      𝔭.asIdeal ≤ IsLocalRing.maximalIdeal (𝔭.adicCompletionIntegers K) := by
    rw [Ideal.map_le_iff_le_comap]
    intro t ht
    rw [Ideal.mem_comap]
    exact (algebraMap_mem_maximalIdeal_iff K 𝔭 t).mpr ht
  -- hence the image of `y` lies in the `N`-th power of the maximal ideal
  have hz : algebraMap (NumberField.RingOfIntegers K) (𝔭.adicCompletionIntegers K) y ∈
      IsLocalRing.maximalIdeal (𝔭.adicCompletionIntegers K) ^ N := by
    have h1 : algebraMap (NumberField.RingOfIntegers K) (𝔭.adicCompletionIntegers K) y ∈
        Ideal.map (algebraMap (NumberField.RingOfIntegers K) (𝔭.adicCompletionIntegers K))
          (𝔭.asIdeal ^ N) :=
      Ideal.mem_map_of_mem _ hy
    rw [Ideal.map_pow] at h1
    exact pow_le_pow_left' hmap N h1
  -- the valuation bound in the completion
  have hv : Valued.v (R := 𝔭.adicCompletion K) (Γ₀ := WithZero (Multiplicative ℤ))
      ((algebraMap (NumberField.RingOfIntegers K) (𝔭.adicCompletionIntegers K) y :
          𝔭.adicCompletionIntegers K) : 𝔭.adicCompletion K) ≤
      (WithZero.exp (-(N : ℤ)) : WithZero (Multiplicative ℤ)) :=
    (Commons.NumberTheory.NumberField.Completion.val_le_exp_neg_iff_mem_maximalIdeal_pow
      𝔭 (algebraMap (NumberField.RingOfIntegers K) (𝔭.adicCompletionIntegers K) y) N).mpr hz
  -- identify the two sides
  unfold NK.NUV2.RouteB.IsCongAt
  have hL : (((Units.map (algebraMap K (𝔭.adicCompletion K)).toMonoidHom s :
        (𝔭.adicCompletion K)ˣ) : 𝔭.adicCompletion K) - 1) =
      ((algebraMap (NumberField.RingOfIntegers K) (𝔭.adicCompletionIntegers K) y :
          𝔭.adicCompletionIntegers K) : 𝔭.adicCompletion K) := by
    rw [show (((Units.map (algebraMap K (𝔭.adicCompletion K)).toMonoidHom s :
          (𝔭.adicCompletion K)ˣ) : 𝔭.adicCompletion K)) =
        algebraMap K (𝔭.adicCompletion K) (s : K) from rfl,
      ← map_one (algebraMap K (𝔭.adicCompletion K)),
      ← map_sub (algebraMap K (𝔭.adicCompletion K)), ← hys, ← hcoe]
  rw [hL]
  exact hv

end Work.SSGRoute.ZDataTwo
