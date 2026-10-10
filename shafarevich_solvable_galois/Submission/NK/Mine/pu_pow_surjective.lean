import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Submission.Commons.RingTheory.Henselian.kummer_root_lift
import Submission.NK.LocalInputs.PowerQuotient.LamIndex
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

open IsDedekindDomain.HeightOneSpectrum
open scoped NumberField WithZero

namespace NK.Mine

/-- **`U¹` is `ℓ`-divisible for `ℓ` the residue characteristic.**

The principal units `U¹ = 1 + 𝔪` of the local field `K_𝔭` form a pro-`p` group, where `p` is the
residue characteristic; as such the `ℓ`-power map is an automorphism of `U¹` for every prime
`ℓ ≠ p`, whence every element of `U¹` is an `ℓ^n`-th power in `U¹`.

Formally: the polynomial `X ^ (ℓ ^ n) - u` (`u ∈ U¹`, i.e. the unit `u` reduces to `1`) has a
simple root modulo `𝔪` at `X = 1` (its derivative there is `ℓ ^ n`, a unit of `𝒪` because
`ℓ ≠ p` is the residue characteristic), so Hensel's lemma — invoked in the form
`Commons.RingTheory.Henselian.kummer_root_lift` for the Henselian local ring
`𝒪 = 𝔭.adicCompletionIntegers K` — lifts `1` to a genuine `ℓ ^ n`-th root `b` of `u`, whose residue
is still `1`, i.e. which lies in `U¹`. -/
theorem pu_pow_surjective {K : Type*} [Field K] [NumberField K]
    (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) {p ℓ : ℕ}
    (hp : p.Prime) (hℓ : ℓ.Prime) (hne : ℓ ≠ p)
    (hchar : CharP (IsLocalRing.ResidueField (𝔭.adicCompletionIntegers K)) p) (n : ℕ) :
    ∀ u : ↥(NK.LocalInputs.PowerQuotient.pu 𝔭 1),
      ∃ v : ↥(NK.LocalInputs.PowerQuotient.pu 𝔭 1), v ^ (ℓ ^ n) = u := by
  -- The valuation ring `𝒪` of the completion is a Henselian local ring.
  haveI : HenselianLocalRing (𝔭.adicCompletionIntegers K) :=
    Commons.RingTheory.Henselian.adicCompletionIntegers_henselianLocalRing
      (R := NumberField.RingOfIntegers K) (K := K) 𝔭
  intro u
  -- `ℓ` is a unit of `𝒪`: otherwise its residue would vanish, forcing `p = ℓ`.
  have hunit_l : IsUnit ((ℓ : ℕ) : 𝔭.adicCompletionIntegers K) := by
    rw [← IsLocalRing.residue_ne_zero_iff_isUnit, ne_eq, map_natCast]
    intro hzero
    have hdvd : p ∣ ℓ :=
      (CharP.cast_eq_zero_iff (IsLocalRing.ResidueField (𝔭.adicCompletionIntegers K)) p ℓ).mp
        hzero
    rcases hℓ.eq_one_or_self_of_dvd p hdvd with h | h
    · exact hp.ne_one h
    · exact hne h.symm
  have hunit : IsUnit (((ℓ ^ n : ℕ)) : 𝔭.adicCompletionIntegers K) := by
    rw [Nat.cast_pow]
    exact hunit_l.pow n
  -- A principal unit is a unit of `𝒪` and reduces to `1`.
  have hmem : (((u : (𝔭.adicCompletionIntegers K)ˣ) : 𝔭.adicCompletionIntegers K) - 1)
      ∈ IsLocalRing.maximalIdeal (𝔭.adicCompletionIntegers K) := by
    have h := u.2
    rw [NK.LocalInputs.PowerQuotient.mem_pu_iff] at h
    simpa [NK.LocalInputs.PowerQuotient.maxId] using h
  have hres_u : IsLocalRing.residue (𝔭.adicCompletionIntegers K)
      ((u : (𝔭.adicCompletionIntegers K)ˣ) : 𝔭.adicCompletionIntegers K) = 1 := by
    have h0 : IsLocalRing.residue (𝔭.adicCompletionIntegers K)
        (((u : (𝔭.adicCompletionIntegers K)ˣ) : 𝔭.adicCompletionIntegers K) - 1) = 0 :=
      (IsLocalRing.residue_eq_zero_iff _).mpr hmem
    have h1 : IsLocalRing.residue (𝔭.adicCompletionIntegers K)
        ((u : (𝔭.adicCompletionIntegers K)ˣ) : 𝔭.adicCompletionIntegers K) - 1 = 0 := by
      simpa using h0
    exact sub_eq_zero.mp h1
  -- Hensel: lift the simple root `1` of `X ^ (ℓ ^ n) - u` modulo `𝔪`.
  obtain ⟨b, hbpow, hbres⟩ :=
    Commons.RingTheory.Henselian.kummer_root_lift (R := 𝔭.adicCompletionIntegers K)
      (u := ((u : (𝔭.adicCompletionIntegers K)ˣ) : 𝔭.adicCompletionIntegers K))
      (ℓ ^ n) ((u : (𝔭.adicCompletionIntegers K)ˣ)).isUnit hunit
      (1 : IsLocalRing.ResidueField (𝔭.adicCompletionIntegers K))
      (by rw [one_pow]; exact hres_u.symm)
  -- `b` still reduces to `1`, so it is a unit lying in `U¹`.
  have hbunit : IsUnit b := by
    rw [← IsLocalRing.residue_ne_zero_iff_isUnit, hbres]
    exact one_ne_zero
  have hb_mem : b - 1 ∈ IsLocalRing.maximalIdeal (𝔭.adicCompletionIntegers K) := by
    refine (IsLocalRing.residue_eq_zero_iff (b - 1)).mp ?_
    rw [map_sub, hbres, map_one, sub_self]
  have hmemv : hbunit.unit ∈ NK.LocalInputs.PowerQuotient.pu 𝔭 1 := by
    rw [NK.LocalInputs.PowerQuotient.mem_pu_iff, NK.LocalInputs.PowerQuotient.maxId,
      pow_one, hbunit.unit_spec]
    exact hb_mem
  refine ⟨⟨hbunit.unit, hmemv⟩, ?_⟩
  have hkey : ((hbunit.unit : 𝔭.adicCompletionIntegers K) ^ (ℓ ^ n)) =
      ((u : (𝔭.adicCompletionIntegers K)ˣ) : 𝔭.adicCompletionIntegers K) := by
    rw [hbunit.unit_spec]
    exact hbpow
  apply Subtype.ext
  rw [Subgroup.coe_pow]
  apply Units.ext
  rw [Units.val_pow_eq_pow_val]
  exact hkey

end NK.Mine
