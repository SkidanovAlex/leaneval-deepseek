/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import Submission.NK.HeckeL.Basic
import Submission.NK.GlobalCFT.NormFunctorial
import Submission.NK.CFTLib.exp_normIdeleHom_eq_sum

/-!
# The idèlic norm of a quotient of prime idèles is integral

Let `K / F` be a finite Galois extension of number fields, `v` a nonzero prime of `F` and
`𝔓, 𝔓'` two primes of `K` above `v`.  We show that the idèlic norm of the quotient
`ideleOfPrime K 𝔓 / ideleOfPrime K 𝔓'` is an integral idèle of `F`, i.e. a local unit at every
finite place.

This is the idèlic incarnation of the fact that the norm of an idèle supported at a single prime
above `v` has `v`-adic exponent the inertia degree `f(𝔓/v)`; since `K/F` is Galois, two primes
above `v` have the same inertia degree, so the exponents at `v` cancel and the norm is a local
unit at `v`.  At every other finite place both idèles are trivial, hence so is the norm.

The idèles `ideleOfPrime K 𝔓` and `ideleOfPrime K 𝔓'` are the ones of the Hecke chapter
(`NK.HeckeL.ideleOfPrime`); they are a local uniformiser at the prime and `1` elsewhere.

## Main results

* `exp_normIdeleHom_eq_sum'`: the `Q`-adic exponent of `N_{K/F} z` is the inertia-degree
  weighted sum of the exponents of `z` above `Q` (the version without unramifiedness hypothesis
  of `NK.CFTLib.exp_normIdeleHom_eq_sum`; the proof never uses that hypothesis).
* `normIdeleHom_ideleOfPrime_div_mem_integralIdeles`: the target lemma.
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

open Classical
open NumberField IsDedekindDomain
open scoped NumberField RestrictedProduct

noncomputable section

namespace NK.CFTLib

open NK.GlobalCFT

/-- **The `Q`-adic exponent of the idèlic norm.**  For a finite extension of number fields
`K / F`, an idèle `z` of `K` and a finite place `Q` of `F`, the `Q`-adic exponent of the idèlic
norm is the inertia-degree weighted sum of the exponents of `z` above `Q`.

This is `NK.CFTLib.exp_normIdeleHom_eq_sum` without the (unused) unramifiedness hypothesis. -/
theorem exp_normIdeleHom_eq_sum' (F K : Type) [Field F] [NumberField F] [Field K] [NumberField K]
    [Algebra F K] [FiniteDimensional F K] (z : Idele K) (Q : HeightOneSpectrum (𝓞 F)) :
    Idele.exp Q (Idele.normIdeleHom F K z) =
      ∑ q ∈ Place.primesOverFinite (K := F) (L := K) Q,
        (q.asIdeal.inertiaDeg (𝓞 F) : ℤ) * Idele.exp q z := by
  classical
  have hz : ∀ q : HeightOneSpectrum (𝓞 K),
      Valued.v (z (Place.ofFinite q) : q.adicCompletion K) ≠ 0 :=
    fun q => (Valuation.ne_zero_iff _).mpr (Units.ne_zero _)
  have hval : Valued.v ((Idele.normIdeleHom F K z) (Place.ofFinite Q) : Q.adicCompletion F)
      = ∏ q ∈ Place.primesOverFinite (K := F) (L := K) Q,
          (Valued.v (z (Place.ofFinite q) : q.adicCompletion K)) ^
            (q.asIdeal.inertiaDeg (𝓞 F)) := by
    rw [Idele.normIdeleHom_apply, Idele.normIdeleFun_ofFinite, Units.coe_prod, map_prod]
    trans ∏ x ∈ (Place.primesOverFinite (K := F) (L := K) Q).attach,
        (Valued.v (z (Place.ofFinite (x : HeightOneSpectrum (𝓞 K))) :
          (x : HeightOneSpectrum (𝓞 K)).adicCompletion K)) ^
          ((x : HeightOneSpectrum (𝓞 K)).asIdeal.inertiaDeg (𝓞 F))
    · exact Finset.prod_congr rfl (fun (x : {q : HeightOneSpectrum (𝓞 K) //
          q ∈ Place.primesOverFinite (K := F) (L := K) Q}) _ =>
        val_localNormFinite Q x.1
          ((Place.mem_primesOverFinite (K := F) (L := K) (Q := Q) (q := x.1)).mp x.2)
          (z (Place.ofFinite x.1)))
    · exact Finset.prod_attach (Place.primesOverFinite (K := F) (L := K) Q)
        (fun q => (Valued.v (z (Place.ofFinite q) : q.adicCompletion K)) ^
          (q.asIdeal.inertiaDeg (𝓞 F)))
  conv_lhs => rw [Idele.exp_def]
  rw [hval]
  rw [withZero_log_prod (fun q _ => pow_ne_zero _ (hz q))]
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl (fun q _ => ?_)
  rw [WithZero.log_pow, Idele.exp_def]
  ring

/-- **The idèlic norm of a quotient of prime idèles above a common prime is integral.**

For `K / F` a finite Galois extension of number fields, `v` a nonzero prime of `F` and `𝔓, 𝔓'`
primes of `K` above `v`, the idèlic norm of `ideleOfPrime K 𝔓 · (ideleOfPrime K 𝔓')⁻¹` is a
local unit at every finite place of `F`. -/
theorem normIdeleHom_ideleOfPrime_div_mem_integralIdeles {F K : Type} [Field F] [NumberField F]
    [Field K] [NumberField K] [Algebra F K] [FiniteDimensional F K] [IsGalois F K]
    (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F))
    (𝔓 𝔓' : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (h𝔓 : 𝔓.asIdeal.LiesOver v.asIdeal) (h𝔓' : 𝔓'.asIdeal.LiesOver v.asIdeal) :
    NK.GlobalCFT.Idele.normIdeleHom F K
        (NK.HeckeL.ideleOfPrime K 𝔓 * (NK.HeckeL.ideleOfPrime K 𝔓')⁻¹)
      ∈ NK.GlobalCFT.Idele.integralIdeles F := by
  classical
  set x : Idele K := NK.HeckeL.ideleOfPrime K 𝔓 * (NK.HeckeL.ideleOfPrime K 𝔓')⁻¹ with hxdef
  -- The exponents of `x`: `x` is a uniformiser at `𝔓`, the inverse of one at `𝔓'` and `1`
  -- everywhere else.
  have hexp : ∀ r : HeightOneSpectrum (𝓞 K), Idele.exp r x =
      (if r = 𝔓 then (1 : ℤ) else 0) - (if r = 𝔓' then (1 : ℤ) else 0) := by
    intro r
    have h1 : Idele.exp r (NK.HeckeL.ideleOfPrime K 𝔓) = (if r = 𝔓 then (1 : ℤ) else 0) := by
      unfold NK.HeckeL.ideleOfPrime
      exact IdeleClassGroup.exp_ideleOfFun _ _ r
    have h2 : Idele.exp r (NK.HeckeL.ideleOfPrime K 𝔓') = (if r = 𝔓' then (1 : ℤ) else 0) := by
      unfold NK.HeckeL.ideleOfPrime
      exact IdeleClassGroup.exp_ideleOfFun _ _ r
    have h3 : Idele.exp r ((NK.HeckeL.ideleOfPrime K 𝔓')⁻¹)
        = -Idele.exp r (NK.HeckeL.ideleOfPrime K 𝔓') := by
      have h := Idele.exp_mul r (NK.HeckeL.ideleOfPrime K 𝔓')
        ((NK.HeckeL.ideleOfPrime K 𝔓')⁻¹)
      rw [mul_inv_cancel, Idele.exp_one] at h
      omega
    rw [hxdef, Idele.exp_mul, h1, h3, h2]
    ring
  -- The exponent of the norm at every finite place of `F` vanishes.
  have hzero : ∀ Q : HeightOneSpectrum (𝓞 F), Idele.exp Q (Idele.normIdeleHom F K x) = 0 := by
    intro Q
    rw [exp_normIdeleHom_eq_sum' F K x Q]
    -- Only the two primes `𝔓` and `𝔓'` contribute to the sum.
    have hterm : ∀ r ∈ Place.primesOverFinite (K := F) (L := K) Q,
        (r.asIdeal.inertiaDeg (𝓞 F) : ℤ) * Idele.exp r x =
        (if r = 𝔓 then (𝔓.asIdeal.inertiaDeg (𝓞 F) : ℤ) else 0)
          - (if r = 𝔓' then (𝔓'.asIdeal.inertiaDeg (𝓞 F) : ℤ) else 0) := by
      intro r _
      have hA : (r.asIdeal.inertiaDeg (𝓞 F) : ℤ) * (if r = 𝔓 then (1 : ℤ) else 0)
          = (if r = 𝔓 then (𝔓.asIdeal.inertiaDeg (𝓞 F) : ℤ) else 0) := by
        by_cases h : r = 𝔓
        · rw [if_pos h, if_pos h, h]; ring
        · rw [if_neg h, if_neg h]; ring
      have hB : (r.asIdeal.inertiaDeg (𝓞 F) : ℤ) * (if r = 𝔓' then (1 : ℤ) else 0)
          = (if r = 𝔓' then (𝔓'.asIdeal.inertiaDeg (𝓞 F) : ℤ) else 0) := by
        by_cases h : r = 𝔓'
        · rw [if_pos h, if_pos h, h]; ring
        · rw [if_neg h, if_neg h]; ring
      rw [hexp r, mul_sub, hA, hB]
    rw [Finset.sum_congr rfl hterm, Finset.sum_sub_distrib]
    rw [Finset.sum_ite_eq' (Place.primesOverFinite (K := F) (L := K) Q) 𝔓
          (fun _ => (𝔓.asIdeal.inertiaDeg (𝓞 F) : ℤ)),
        Finset.sum_ite_eq' (Place.primesOverFinite (K := F) (L := K) Q) 𝔓'
          (fun _ => (𝔓'.asIdeal.inertiaDeg (𝓞 F) : ℤ))]
    by_cases hQ : Q = v
    · -- At the prime below `𝔓` and `𝔓'` the two contributions cancel: `K/F` is Galois, so the
      -- two inertia degrees are equal.
      rw [hQ, if_pos (Place.mem_primesOverFinite.mpr h𝔓),
        if_pos (Place.mem_primesOverFinite.mpr h𝔓')]
      haveI : 𝔓.asIdeal.IsPrime := 𝔓.isPrime
      haveI : 𝔓'.asIdeal.IsPrime := 𝔓'.isPrime
      haveI : 𝔓.asIdeal.LiesOver v.asIdeal := h𝔓
      haveI : 𝔓'.asIdeal.LiesOver v.asIdeal := h𝔓'
      have hf : 𝔓.asIdeal.inertiaDeg (𝓞 F) = 𝔓'.asIdeal.inertiaDeg (𝓞 F) :=
        Ideal.inertiaDeg_eq_of_isGaloisGroup v.asIdeal 𝔓.asIdeal 𝔓'.asIdeal (K ≃ₐ[F] K)
      rw [hf]; ring
    · -- At every other prime neither `𝔓` nor `𝔓'` lies above it.
      have hPhi : 𝔓 ∉ Place.primesOverFinite (K := F) (L := K) Q := by
        intro hm
        have h1 : 𝔓.asIdeal.LiesOver Q.asIdeal := Place.mem_primesOverFinite.mp hm
        exact hQ (HeightOneSpectrum.ext (by rw [h1.over, h𝔓.over]))
      have hPhi' : 𝔓' ∉ Place.primesOverFinite (K := F) (L := K) Q := by
        intro hm
        have h1 : 𝔓'.asIdeal.LiesOver Q.asIdeal := Place.mem_primesOverFinite.mp hm
        exact hQ (HeightOneSpectrum.ext (by rw [h1.over, h𝔓'.over]))
      rw [if_neg hPhi, if_neg hPhi']
      ring
  -- A finite component of the norm has exponent `0`, hence is a local unit.
  rw [Idele.mem_integralIdeles]
  intro Q hQ
  obtain ⟨q, rfl⟩ := Place.isFinite_iff.mp hQ
  rw [Place.mem_localUnits_ofFinite_iff_valued_eq_one, Idele.exp_val, hzero q, neg_zero,
    WithZero.exp_zero]

end NK.CFTLib
