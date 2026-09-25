import Mathlib
import Submission.Commons.NumberTheory.NumberField.val_algebraMap_adicCompletion_eq
import Submission.Commons.NumberTheory.NumberField.adicCompletion_residueField_equiv_exists

open IsDedekindDomain
open scoped WithZero

set_option linter.style.haveILetI false

namespace NK.LocalInputs.PowerQuotient

/-- **The valuation of the rational prime `p` in the `𝔭`-adic completion of `K`.**

If `𝔭` is a finite prime of a number field `K` whose residue characteristic is the prime `p`,
then the valuation of `p ∈ K_𝔭` is `(exp (-1)) ^ (𝔭.asIdeal.ramificationIdx ℤ)`, i.e. the
negative of the ramification index of `𝔭` over `p` on the discrete scale.

The proof computes the `𝔭`-adic valuation of `p` through the global `𝔭`-adic valuation of `K`:
`Valued.v` on the completion restricts to `𝔭.valuation K` (`val_algebraMap_adicCompletion_eq`),
`𝔭.valuation K` on `𝓞 K` is the ideal valuation `𝔭.intValuation`, whose value on `p` is
`exp (-multiplicity 𝔭 (p))`, and the multiplicity of `𝔭` in the principal ideal `(p)` is the
ramification index of `𝔭` over the rational prime `p` (`Ideal.IsDedekindDomain.
ramificationIdx_eq_multiplicity`).  That `p` really is the prime under `𝔭` — needed so that the
multiplicity is a ramification index over `ℤ` — is read off from the characteristic of the
residue field. -/
theorem val_prime_adicCompletion {K : Type*} [Field K] [NumberField K]
    (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) {p : ℕ} (hp : p.Prime)
    (hres : CharP (IsLocalRing.ResidueField (𝔭.adicCompletionIntegers K)) p) :
    (Valued.v : Valuation (𝔭.adicCompletion K) (WithZero (Multiplicative ℤ)))
        ((p : ℕ) : 𝔭.adicCompletion K) =
      (WithZero.exp (-1 : ℤ)) ^ (𝔭.asIdeal.ramificationIdx ℤ) := by
  -- the residue characteristic being `p` says that `p` lies in `𝔭`
  have hpmem : (p : NumberField.RingOfIntegers K) ∈ 𝔭.asIdeal := by
    have hker := Commons.NumberTheory.NumberField.quotientMap_ker_eq_asIdeal 𝔭
    rw [← hker, RingHom.mem_ker, RingHom.comp_apply]
    show (Ideal.Quotient.mk (IsLocalRing.maximalIdeal (𝔭.adicCompletionIntegers K)))
        (algebraMap (NumberField.RingOfIntegers K) (𝔭.adicCompletionIntegers K)
          (p : NumberField.RingOfIntegers K)) = 0
    rw [map_natCast (algebraMap (NumberField.RingOfIntegers K) (𝔭.adicCompletionIntegers K)) p,
      map_natCast (Ideal.Quotient.mk (IsLocalRing.maximalIdeal (𝔭.adicCompletionIntegers K))) p]
    exact CharP.cast_eq_zero (IsLocalRing.ResidueField (𝔭.adicCompletionIntegers K)) p
  -- hence the prime of `ℤ` under `𝔭` is `(p)`
  have hunder : 𝔭.asIdeal.under ℤ = Ideal.span {(p : ℤ)} := by
    have hmemZ : (p : ℤ) ∈ 𝔭.asIdeal.under ℤ := by
      rw [Ideal.mem_under]
      show algebraMap ℤ (NumberField.RingOfIntegers K) (p : ℤ) ∈ 𝔭.asIdeal
      rw [map_natCast]
      exact hpmem
    have hle : Ideal.span {(p : ℤ)} ≤ 𝔭.asIdeal.under ℤ :=
      Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hmemZ)
    have hpr : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
    have hmax : (Ideal.span {(p : ℤ)}).IsMaximal :=
      Ideal.IsPrime.isMaximal ((Ideal.span_singleton_prime hpr.ne_zero).mpr hpr)
        (by rw [Ne, Ideal.span_singleton_eq_bot]; exact hpr.ne_zero)
    have hne : 𝔭.asIdeal.under ℤ ≠ ⊤ := (Ideal.IsPrime.under ℤ 𝔭.asIdeal).ne_top
    exact (Ideal.IsMaximal.eq_of_le hmax hne hle).symm
  -- so the ideal `(p)` of `𝓞 K` is the image of the prime of `ℤ` under `𝔭`
  have hmap : (Ideal.span {(p : ℤ)}).map (algebraMap ℤ (NumberField.RingOfIntegers K)) =
      Ideal.span {(p : NumberField.RingOfIntegers K)} := by
    rw [Ideal.map_span, Set.image_singleton, map_natCast]
  haveI hlies : 𝔭.asIdeal.LiesOver (Ideal.span {(p : ℤ)}) := Ideal.LiesOver.mk hunder.symm
  have hmapne : (Ideal.span {(p : ℤ)}).map (algebraMap ℤ (NumberField.RingOfIntegers K)) ≠ ⊥ := by
    rw [hmap, Ne, Ideal.span_singleton_eq_bot]
    exact_mod_cast hp.ne_zero
  -- the multiplicity of `𝔭` in `(p)` is the ramification index of `𝔭` over `ℤ`
  have hram : 𝔭.asIdeal.ramificationIdx ℤ =
      multiplicity 𝔭.asIdeal (Ideal.span {(p : NumberField.RingOfIntegers K)}) := by
    have h := Ideal.IsDedekindDomain.ramificationIdx_eq_multiplicity
      (p := Ideal.span {(p : ℤ)}) (q := 𝔭.asIdeal) hmapne
    rwa [hmap] at h
  -- the global `𝔭`-adic valuation of `p`
  have hvalK : 𝔭.valuation K ((p : ℕ) : K) =
      WithZero.exp (-(((𝔭.asIdeal.ramificationIdx ℤ : ℕ) : ℤ))) := by
    rw [show ((p : ℕ) : K) = algebraMap (NumberField.RingOfIntegers K) K
        ((p : ℕ) : NumberField.RingOfIntegers K) from (map_natCast _ p).symm,
      IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap]
    rw [IsDedekindDomain.HeightOneSpectrum.intValuation_eq_exp_neg_multiplicity _
      (by exact_mod_cast hp.ne_zero), ← hram]
  have hpow : (WithZero.exp (-1 : ℤ)) ^ (𝔭.asIdeal.ramificationIdx ℤ) =
      WithZero.exp (-(((𝔭.asIdeal.ramificationIdx ℤ : ℕ) : ℤ))) := by
    rw [← WithZero.exp_nsmul]
    congr 1
    simp
  -- assemble: the completion's valuation restricts to the global one
  calc (Valued.v (R := 𝔭.adicCompletion K) (Γ₀ := WithZero (Multiplicative ℤ)))
        ((p : ℕ) : 𝔭.adicCompletion K)
      = 𝔭.valuation K ((p : ℕ) : K) := by
        rw [show ((p : ℕ) : 𝔭.adicCompletion K) =
            algebraMap K (𝔭.adicCompletion K) ((p : ℕ) : K) by simp]
        exact Commons.NumberTheory.NumberField.val_algebraMap_adicCompletion_eq 𝔭 ((p : ℕ) : K)
    _ = WithZero.exp (-(((𝔭.asIdeal.ramificationIdx ℤ : ℕ) : ℤ))) := hvalK
    _ = (WithZero.exp (-1 : ℤ)) ^ (𝔭.asIdeal.ramificationIdx ℤ) := hpow.symm

end NK.LocalInputs.PowerQuotient
