import Mathlib.RingTheory.Henselian
import Mathlib.NumberTheory.Cyclotomic.Basic
import Mathlib.RingTheory.DedekindDomain.Different
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Submission.NK.NUV2.ARL.GapDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# A cyclotomic extension is unramified at every prime not dividing `n`

Let `k` be a number field, `n ≥ 1` and `Ω = k(ζ_n)` a cyclotomic extension of `k`.  If `𝔮` is a
prime of `𝓞 k` with `n ∉ 𝔮` (equivalently, the residue characteristic of `𝔮` does not divide `n`),
then `𝔮` is unramified in `Ω/k`: every prime `𝔓` of `𝓞 Ω` above `𝔮` has ramification index `1`
(`NK.CFTLib.ArtinReciprocityIdeal.IsUnramified`).

## The proof

The argument is the classical one via the different ideal, in the form of the *conductor formula*
`conductor(𝓞 k, ζ) * 𝔇(Ω/k) = (f'(ζ))`, where `f` is the minimal polynomial of `ζ` over `𝓞 k`.

* `ζ` is a primitive `n`-th root of unity and is integral over `𝓞 k`, so it gives an element
  `ζB : 𝓞 Ω` with `(ζB : Ω) = ζ`; and `k[ζ] = Ω`.
* `f := minpoly (𝓞 k) ζB` divides `X ^ n - 1` in `(𝓞 k)[X]`
  (`minpoly.isIntegrallyClosed_dvd`, using `ζB ^ n = 1`).  Writing `X ^ n - 1 = f * g` and
  differentiating, then evaluating at `ζB`, gives the key identity
  `f'(ζB) * g(ζB) = n * ζB ^ (n - 1)` in `𝓞 Ω`.
* If `f'(ζB)` lay in the prime `𝔓`, then `n * ζB ^ (n - 1) ∈ 𝔓`; but `ζB ^ (n-1)` is invertible
  (`ζB ^ n = 1`) so `ζB ^ (n-1) ∉ 𝔓`, and primality forces `n ∈ 𝔓`, i.e.
  `n ∈ 𝔓 ∩ 𝓞 k = 𝔮`, contrary to the hypothesis.  Hence `f'(ζB) ∉ 𝔓`.
* If `𝔓 ∣ 𝔇(Ω/k)` then `𝔓 ∣ conductor(𝓞 k, ζ) * 𝔇(Ω/k) = (f'(ζB))`, so `f'(ζB) ∈ 𝔓` — a
  contradiction.  Thus `𝔓 ∤ 𝔇(Ω/k)`, which by `not_dvd_differentIdeal_iff` means that `𝔓` is
  unramified over `𝓞 k`, and finally `Ideal.ramificationIdx_eq_one_of_isUnramifiedAt` gives
  `e(𝔓|𝔮) = 1`.

This is the standard proof that the only primes ramifying in `k(ζ_n)/k` divide `n`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

open NumberField IsDedekindDomain Polynomial
open scoped NumberField nonZeroDivisors

namespace NK.NUV2.ARL.Gap

theorem isUnramified_cyclotomicExtension {k Ω : Type} [Field k] [NumberField k] [Field Ω]
    [NumberField Ω] [Algebra k Ω] [FiniteDimensional k Ω] (n : ℕ) [NeZero n]
    [IsCyclotomicExtension {n} k Ω] (𝔮 : NK.Chebotarev.PrimeIdeal k)
    (h𝔮 : (n : NumberField.RingOfIntegers k) ∉ 𝔮.asIdeal) :
    NK.CFTLib.ArtinReciprocityIdeal.IsUnramified (K := k) (L := Ω) 𝔮 := by
  intro P hP
  -- A primitive `n`-th root of unity `ζ`, living in `𝓞 Ω`.
  obtain ⟨ζ, hζ⟩ :=
    IsCyclotomicExtension.exists_isPrimitiveRoot k Ω (Set.mem_singleton n) (NeZero.ne n)
  have htop : Algebra.adjoin k ({ζ} : Set Ω) = ⊤ :=
    IsCyclotomicExtension.adjoin_primitive_root_eq_top hζ
  have hintΩ : IsIntegral (𝓞 k) ζ :=
    IsIntegral.tower_top (A := 𝓞 k) (B := Ω) (hζ.isIntegral (NeZero.pos n))
  obtain ⟨ζB, hζB⟩ :=
    (IsIntegralClosure.isIntegral_iff (A := 𝓞 Ω) (R := 𝓞 k) (B := Ω)).mp hintΩ
  have hζBpow : ζB ^ n = 1 := by
    apply RingOfIntegers.coe_injective
    rw [map_pow, hζB, map_one, hζ.pow_eq_one]
  -- ## The key algebraic identity `f'(ζB) * g(ζB) = n * ζB ^ (n - 1)`
  obtain ⟨g, _hg, hEq⟩ : ∃ g : (𝓞 k)[X], minpoly (𝓞 k) ζB * g = X ^ n - C 1 ∧
      aeval ζB (derivative (minpoly (𝓞 k) ζB)) * aeval ζB g
        = algebraMap (𝓞 k) (𝓞 Ω) (n : 𝓞 k) * ζB ^ (n - 1) := by
    obtain ⟨g, hg⟩ : minpoly (𝓞 k) ζB ∣ X ^ n - C 1 := by
      refine minpoly.isIntegrallyClosed_dvd (Algebra.IsIntegral.isIntegral ζB) ?_
      rw [map_sub, map_pow, aeval_X, aeval_C, hζBpow, map_one, sub_self]
    refine ⟨g, hg.symm, ?_⟩
    have hderiv : derivative (minpoly (𝓞 k) ζB) * g + minpoly (𝓞 k) ζB * derivative g
        = C (n : 𝓞 k) * X ^ (n - 1) := by
      have h1 := congrArg derivative hg
      rw [derivative_mul, derivative_sub, derivative_X_pow, derivative_C, sub_zero] at h1
      exact h1.symm
    have hEval := congrArg (aeval ζB) hderiv
    simp only [map_add, map_mul, map_pow, aeval_C, aeval_X] at hEval
    rw [minpoly.aeval, zero_mul, add_zero] at hEval
    exact hEval
  -- ## `f'(ζB) ∉ 𝔓`
  have hFnot : aeval ζB (derivative (minpoly (𝓞 k) ζB)) ∉ P.asIdeal := by
    intro hF
    have hmem : algebraMap (𝓞 k) (𝓞 Ω) (n : 𝓞 k) * ζB ^ (n - 1) ∈ P.asIdeal := by
      rw [← hEq]
      exact Ideal.mul_mem_right _ P.asIdeal hF
    have hnot : ζB ^ (n - 1) ∉ P.asIdeal := by
      intro hmem'
      have hone : (1 : 𝓞 Ω) ∈ P.asIdeal := by
        have h2 : ζB * ζB ^ (n - 1) ∈ P.asIdeal := Ideal.mul_mem_left _ ζB hmem'
        rwa [show ζB * ζB ^ (n - 1) = 1 from by
          rw [← pow_succ', Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr (NeZero.ne n)),
            hζBpow]] at h2
      exact Ideal.IsPrime.ne_top (inferInstance) ((Ideal.eq_top_iff_one P.asIdeal).mpr hone)
    rcases Ideal.IsPrime.mem_or_mem (inferInstance : P.asIdeal.IsPrime) hmem with h1 | h1
    · have hun : (n : 𝓞 k) ∈ P.asIdeal.under (𝓞 k) := (Ideal.mem_under (𝓞 k) P.asIdeal).mpr h1
      rw [(Ideal.LiesOver.over (self := hP)).symm] at hun
      exact h𝔮 hun
    · exact hnot h1
  -- ## The conductor formula
  have hcond : conductor (𝓞 k) ζB * differentIdeal (𝓞 k) (𝓞 Ω)
      = Ideal.span {aeval ζB (derivative (minpoly (𝓞 k) ζB))} :=
    conductor_mul_differentIdeal (A := 𝓞 k) (K := k) (L := Ω) ζB (by rw [hζB]; exact htop)
  -- ## `𝔓` divides neither `(f'(ζB))` nor the different ideal
  have hunr : Algebra.IsUnramifiedAt (𝓞 k) P.asIdeal := by
    refine (not_dvd_differentIdeal_iff (P := P.asIdeal)).mp ?_
    intro hdiv
    refine hFnot ((Ideal.dvd_iff_le.mp ?_) (Ideal.subset_span (Set.mem_singleton _)))
    rw [← hcond]
    exact (dvd_mul_left _ (conductor (𝓞 k) ζB)).trans (mul_dvd_mul_left _ hdiv)
  exact Ideal.ramificationIdx_eq_one_of_isUnramifiedAt (R := 𝓞 k) (S := 𝓞 Ω) (p := P.asIdeal)

end NK.NUV2.ARL.Gap
