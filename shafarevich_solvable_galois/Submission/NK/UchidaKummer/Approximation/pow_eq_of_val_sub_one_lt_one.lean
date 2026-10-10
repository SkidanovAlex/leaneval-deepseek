import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Submission.Commons.NumberTheory.NumberField.Completion.mem_ker_units_residue_adicCompletion_iff
import Submission.Commons.RingTheory.Henselian.units_mem_pow_of_residue_mem_pow
import Submission.NK.UchidaKummer.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace NK.UchidaKummer.Approximation

/-- **`ℓ`-th powers near `1` in a `p`-adic completion: the Hensel route.**

Let `k = v.adicCompletion K` and let `ℓ` be a prime which is a *unit* of the ring of integers
`R = v.adicCompletionIntegers K` (equivalently, `ℓ` is not the residue characteristic).  Then every
`x : k` with `v (x - 1) < 1` (i.e. `x ≡ 1` modulo the maximal ideal) is an `ℓ`-th power of a unit
of `k`.

Proof route:
* `v (x - 1) < 1` gives `v x = 1` (`Valuation.map_add_eq_of_lt_left` applied to
  `x = 1 + (x - 1)`), so `x ∈ R` and `⟨x, _⟩ : Rˣ` is a unit by
  `IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one`;
* `haveI := Commons.RingTheory.Henselian.adicCompletionIntegers_henselianLocalRing v`;
* the residue of this unit is `1` (`Commons.NumberTheory.NumberField.Completion.mem_ker_units_residue_iff`,
  using that `u - 1 ∈ 𝔪` follows from `v (u - 1) < 1`), hence an `ℓ`-th power in the residue field;
* apply `Commons.RingTheory.Henselian.units_mem_pow_of_residue_mem_pow ℓ _ hunit u _` (`NeZero ℓ`
  from `hℓ.ne_zero`) to get `w : Rˣ` with `w ^ ℓ = u`;
* take `y := Units.map (algebraMap R k).toMonoidHom w` and use `Units.coe_map` plus `(u : R) = x`. -/
theorem pow_eq_of_val_sub_one_lt_one (K : Type*) [Field K] [NumberField K]
    (v : NK.Chebotarev.PrimeIdeal K) (ℓ : ℕ) (hℓ : ℓ.Prime)
    (hunit : IsUnit ((ℓ : ℕ) : v.adicCompletionIntegers K)) :
    ∀ x : v.adicCompletion K, Valued.v (R := v.adicCompletion K) (Γ₀ := Zstar0) (x - 1) < 1 →
      ∃ y : (v.adicCompletion K)ˣ, ((y : v.adicCompletion K)) ^ ℓ = x := by
  intro x hx
  -- `v (x - 1) < 1 = v 1`, so `v x = v (1 + (x - 1)) = v 1 = 1`.
  have hxval : Valued.v (R := v.adicCompletion K) (Γ₀ := Zstar0) x = 1 := by
    have hlt : Valued.v (R := v.adicCompletion K) (Γ₀ := Zstar0) (x - 1) <
        Valued.v (R := v.adicCompletion K) (Γ₀ := Zstar0) (1 : v.adicCompletion K) := by
      simpa using hx
    have h := Valuation.map_add_eq_of_lt_left
      (Valued.v (R := v.adicCompletion K) (Γ₀ := Zstar0)) hlt
    rw [Valuation.map_one] at h
    rwa [show (1 : v.adicCompletion K) + (x - 1) = x by ring] at h
  -- `x` is integral, and a unit of `R` because its valuation is `1`.
  have hxmem : x ∈ v.adicCompletionIntegers K :=
    (IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers
      (NumberField.RingOfIntegers K) K v).mpr (le_of_eq hxval)
  let u₀ : v.adicCompletionIntegers K := ⟨x, hxmem⟩
  have hu₀val : Valued.v (R := v.adicCompletion K) (Γ₀ := Zstar0)
      (u₀ : v.adicCompletion K) = 1 := by
    simpa [u₀] using hxval
  have hu₀unit : IsUnit u₀ :=
    (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one).mpr hu₀val
  let u : (v.adicCompletionIntegers K)ˣ := hu₀unit.unit
  have hu_coe : (u : v.adicCompletionIntegers K) = u₀ := hu₀unit.unit_spec
  have hcoe_u : ((u : v.adicCompletionIntegers K) : v.adicCompletion K) = x := by
    rw [hu_coe]
  -- Hensel's lemma applied to `X ^ ℓ - u`.
  have : HenselianLocalRing (v.adicCompletionIntegers K) :=
    Commons.RingTheory.Henselian.adicCompletionIntegers_henselianLocalRing v
  have hcoe : (((u : v.adicCompletionIntegers K) - 1 : v.adicCompletionIntegers K) :
      v.adicCompletion K) = x - 1 := by
    show ((u : v.adicCompletionIntegers K) : v.adicCompletion K) - 1 = x - 1
    rw [hcoe_u]
  have hmem : ((u : v.adicCompletionIntegers K) - 1) ∈
      IsLocalRing.maximalIdeal (v.adicCompletionIntegers K) := by
    rw [Commons.NumberTheory.NumberField.adicCompletionIntegers_mem_maximalIdeal_iff_valued_lt_one v,
      hcoe]
    exact hx
  -- the residue of `u` is `1`, hence is an `ℓ`-th power in the residue field.
  have hker : u ∈ (Units.map ((IsLocalRing.residue (v.adicCompletionIntegers K)).toMonoidHom)).ker := by
    rw [Commons.NumberTheory.NumberField.Completion.mem_ker_units_residue_iff]
    exact hmem
  have hrange : Units.map ((IsLocalRing.residue (v.adicCompletionIntegers K)).toMonoidHom) u ∈
      (powMonoidHom ℓ).range := by
    rw [MonoidHom.mem_range]
    exact ⟨1, by rw [powMonoidHom_apply, one_pow, MonoidHom.mem_ker.mp hker]⟩
  have : NeZero ℓ := ⟨hℓ.ne_zero⟩
  obtain ⟨w, hw⟩ :=
    Commons.RingTheory.Henselian.units_mem_pow_of_residue_mem_pow ℓ hunit u hrange
  have hw' : w ^ ℓ = u := by simpa [powMonoidHom_apply] using hw
  refine ⟨Units.map (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K)).toMonoidHom w, ?_⟩
  have hwval : ((w : (v.adicCompletionIntegers K)ˣ) : v.adicCompletionIntegers K) ^ ℓ = u₀ := by
    rw [← Units.val_pow_eq_pow_val, hw', hu_coe]
  show (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K)
      ((w : (v.adicCompletionIntegers K)ˣ) : v.adicCompletionIntegers K)) ^ ℓ = x
  rw [← map_pow, hwval]
  rfl

end NK.UchidaKummer.Approximation
