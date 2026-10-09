/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The differentiation step of §5: a Kummer field with prescribed local degrees

Reference: the LaTeX sources of arXiv:2601.01251, §5, Lemma `lem:ell prime differentiation`
(the global form used in the Neukirch–Uchida reconstruction).

Let `K` be a number field containing the `ℓ`-th roots of unity (`ζ` a primitive `ℓ`-th root,
`ℓ` prime), let `K'` be a separable closure of `K` and let `T` be a finite set of finite primes
of `K` containing a distinguished prime `𝔭` and a finite set `S ⊆ T` with `𝔭 ∉ S`.

Assume

* `IsKummerSurjective K ℓ T` — the Kummer local surjection: every tuple of local `ℓ`-power
  classes at the primes of `T` is the diagonal image of a global unit class;
* `𝔭` has a unit which is not an `ℓ`-th power in the completion `K_𝔭` (this holds for every
  prime and every prime `ℓ`, by local Kummer theory);
* `IsKummerLocalDichotomy K K' ℓ` — the local Kummer dichotomy: for a Kummer field
  `L = K(a^{1/ℓ})`, a prime `𝔮` splits completely in `L` (all local degrees one) exactly when
  `a` is an `ℓ`-th power in `K_𝔮`.

Then there is `a ∈ Kˣ` whose Kummer field `L = K(a^{1/ℓ}) ⊆ K'` has local degree `ℓ` at `𝔭`
and local degree `1` at every `𝔮 ∈ S`.

The element `a` is produced by the local surjection: prescribe the class of a non-`ℓ`-th power at
`𝔭` and the trivial class at the primes of `S`.  The local degree at `𝔭` is then `ℓ` because
`L / K` is *Galois of prime degree* `ℓ`: the local degree of a prime above `𝔭` is the common value
`e_In · f_In`, and the fundamental identity `#(primes over 𝔭) · e_In · f_In = [L : K] = ℓ`
forces that common value to be `1` or `ℓ`; it is not `1` by the local dichotomy, hence it is `ℓ`.

## Main results

* `localDeg_eq_ramificationIdxIn_mul_inertiaDegIn` — the local degree of a prime above `𝔭` in a
  Galois extension is the common value `e_In · f_In`;
* `localDeg_eq_of_finrank_eq_prime_of_not_forall_eq_one` — in a Galois extension of prime degree
  `ℓ` in which not every prime above `𝔭` has local degree one, *every* prime above `𝔭` has local
  degree `ℓ`;
* `exists_kummerField_localDeg_eq_of_surjective` — the differentiation lemma.
-/
import Mathlib
import Submission.NK.UchidaKummer.Defs
import Submission.NK.LocalAnabelian.Kummer.Defs
import Submission.NK.LocalAnabelian.Kummer.isGalois_kummerField_and_finrank
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace NK.UchidaKummer.Differentiation

open IsDedekindDomain

set_option linter.style.haveILetI false

/-- **The local degree of a prime of a Galois extension is the common value `e_In · f_In`.**

For a finite Galois extension `L / K` of number fields, a finite prime `𝔭` of `K` and a prime `P`
of `𝓞 L` lying over `𝔭`, the product of the ramification index and the inertia degree of `P` over
`𝔭` agrees with the common value `𝔭.asIdeal.ramificationIdxIn (𝓞 L) · 𝔭.asIdeal.inertiaDegIn
(𝓞 L)`: over a Galois extension all primes above `𝔭` have the same `e` and the same `f`. -/
lemma localDeg_eq_ramificationIdxIn_mul_inertiaDegIn
    {K K' : Type*} [Field K] [NumberField K] [Field K'] [Algebra K K']
    (L : IntermediateField K K') [FiniteDimensional K L] [IsGalois K ↥L]
    (𝔭 : NK.Chebotarev.PrimeIdeal K) (P : NK.Chebotarev.PrimeIdeal ↥L)
    (hP : P.asIdeal.LiesOver 𝔭.asIdeal) :
    localDeg P 𝔭 =
      𝔭.asIdeal.ramificationIdxIn (NumberField.RingOfIntegers ↥L) *
        𝔭.asIdeal.inertiaDegIn (NumberField.RingOfIntegers ↥L) := by
  haveI := hP
  letI : MulSemiringAction Gal(↥L/K) (NumberField.RingOfIntegers ↥L) :=
    IsIntegralClosure.MulSemiringAction (NumberField.RingOfIntegers K) K ↥L
      (NumberField.RingOfIntegers ↥L)
  haveI hGal : IsGaloisGroup Gal(↥L/K) (NumberField.RingOfIntegers K)
      (NumberField.RingOfIntegers ↥L) :=
    IsGaloisGroup.of_isFractionRing Gal(↥L/K) (NumberField.RingOfIntegers K)
      (NumberField.RingOfIntegers ↥L) K ↥L
  haveI : Finite Gal(↥L/K) := inferInstance
  simp only [localDeg]
  rw [Ideal.ramificationIdxIn_eq_ramificationIdx 𝔭.asIdeal P.asIdeal Gal(↥L/K),
    Ideal.inertiaDegIn_eq_inertiaDeg 𝔭.asIdeal P.asIdeal Gal(↥L/K)]

/-- **Prime local degree `ℓ` in a Galois extension of degree `ℓ`.**

Let `L / K` be a finite Galois extension of number fields with `[L : K] = ℓ`, `ℓ` prime.  If not
every prime of `𝓞 L` above the finite prime `𝔭` of `K` has local degree one — equivalently, if `𝔭`
does not split completely in `L` — then *every* prime above `𝔭` has local degree `ℓ`.

Indeed, the common value `d = e_In · f_In` of the local degrees above `𝔭` satisfies
`#(primes over 𝔭) · d = [L : K] = ℓ` (the fundamental identity in Galois form), so `d ∣ ℓ`; and
`d ≠ 1`, since `d = 1` would mean that every prime above `𝔭` has local degree one. -/
lemma localDeg_eq_of_finrank_eq_prime_of_not_forall_eq_one
    {K K' : Type*} [Field K] [NumberField K] [Field K'] [Algebra K K']
    (L : IntermediateField K K') [FiniteDimensional K L] [IsGalois K ↥L]
    (ℓ : ℕ) (hℓ : ℓ.Prime) (hfin : Module.finrank K ↥L = ℓ)
    (𝔭 : NK.Chebotarev.PrimeIdeal K)
    (h : ¬ ∀ P : NK.Chebotarev.PrimeIdeal ↥L, P.asIdeal.LiesOver 𝔭.asIdeal →
      localDeg P 𝔭 = 1) :
    ∀ P : NK.Chebotarev.PrimeIdeal ↥L, P.asIdeal.LiesOver 𝔭.asIdeal →
      localDeg P 𝔭 = ℓ := by
  letI : MulSemiringAction Gal(↥L/K) (NumberField.RingOfIntegers ↥L) :=
    IsIntegralClosure.MulSemiringAction (NumberField.RingOfIntegers K) K ↥L
      (NumberField.RingOfIntegers ↥L)
  haveI hGal : IsGaloisGroup Gal(↥L/K) (NumberField.RingOfIntegers K)
      (NumberField.RingOfIntegers ↥L) :=
    IsGaloisGroup.of_isFractionRing Gal(↥L/K) (NumberField.RingOfIntegers K)
      (NumberField.RingOfIntegers ↥L) K ↥L
  haveI : Finite Gal(↥L/K) := inferInstance
  set d : ℕ := 𝔭.asIdeal.ramificationIdxIn (NumberField.RingOfIntegers ↥L) *
    𝔭.asIdeal.inertiaDegIn (NumberField.RingOfIntegers ↥L) with hd
  have hne : d ≠ 1 := by
    intro h1
    apply h
    intro P hP
    rw [localDeg_eq_ramificationIdxIn_mul_inertiaDegIn L 𝔭 P hP]
    exact h1
  have hmul : (𝔭.asIdeal.primesOver (NumberField.RingOfIntegers ↥L)).ncard * d =
      Module.finrank K ↥L := by
    rw [hd]
    rw [Ideal.ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn 𝔭.asIdeal
      (NumberField.RingOfIntegers ↥L) Gal(↥L/K)]
    exact IsGalois.card_aut_eq_finrank K ↥L
  have hdvd : d ∣ ℓ := ⟨_, by rw [mul_comm, hmul, hfin]⟩
  have hdℓ : d = ℓ := (hℓ.eq_one_or_self_of_dvd d hdvd).resolve_left hne
  intro P hP
  rw [localDeg_eq_ramificationIdxIn_mul_inertiaDegIn L 𝔭 P hP]
  exact hdℓ

/-- **The differentiation step of §5 of the Neukirch–Uchida reconstruction.**

For a number field `K` containing a primitive `ℓ`-th root of unity `ζ` (`ℓ` prime), a separable
closure `K'` of `K`, a finite prime `𝔭` at which some unit is not an `ℓ`-th power, a finite set of
primes `S` not containing `𝔭`, and a finite set `T ⊇ S ∪ {𝔭}` at which the Kummer local
surjection holds, there is `a ∈ Kˣ` whose Kummer field `L = K(a^{1/ℓ}) ⊆ K'` has local degree `ℓ`
at every prime above `𝔭` and local degree `1` at every prime above a prime of `S` — assuming the
local Kummer dichotomy at every prime of `K`.

*Proof.*  The local surjection at `T`, applied to the tuple which is the class of a non-`ℓ`-th
power at `𝔭` and trivial at the other primes, produces `a ∈ Kˣ` whose local `ℓ`-power class at `𝔭`
is that of a non-`ℓ`-th power, and which is a local `ℓ`-th power at every `𝔮 ∈ S`.  In
particular `a` is not an `ℓ`-th power in `K`, so by Kummer theory `L = K(a^{1/ℓ})` is Galois over
`K` of degree `ℓ`; and the local dichotomy gives the local degrees: `1` at the primes of `S`
(because `a` is a local `ℓ`-th power there) and `ℓ` at `𝔭` (because `a` is *not* a local `ℓ`-th
power there, so `𝔭` does not split completely, and the only other possibility for the common
local degree in a Galois extension of degree `ℓ` is `ℓ`). -/
theorem exists_kummerField_localDeg_eq_of_surjective
    {K K' : Type*} [Field K] [NumberField K] [Field K'] [Algebra K K'] [IsSepClosure K K']
    (ℓ : ℕ) (hℓ : ℓ.Prime) {ζ : K} (hζ : IsPrimitiveRoot ζ ℓ)
    (𝔭 : NK.Chebotarev.PrimeIdeal K) (S T : Finset (NK.Chebotarev.PrimeIdeal K))
    (h𝔭T : 𝔭 ∈ T) (hST : ∀ 𝔮 ∈ S, 𝔮 ∈ T) (h𝔭S : 𝔭 ∉ S)
    (hsurj : NK.UchidaKummer.IsKummerSurjective K ℓ T)
    (hnonpow : ∃ u : (𝔭.adicCompletion K)ˣ, ∀ b : (𝔭.adicCompletion K)ˣ, b ^ ℓ ≠ u)
    (hdich : NK.UchidaKummer.IsKummerLocalDichotomy K K' ℓ) :
    ∃ (a : Kˣ) (L : IntermediateField K K') (_ : FiniteDimensional K L) (_ : NumberField ↥L),
      L = NK.LocalAnabelian.kummerField (K' := K') ℓ a ∧
      (∀ P : NK.Chebotarev.PrimeIdeal ↥L, P.asIdeal.LiesOver 𝔭.asIdeal →
        NK.UchidaKummer.localDeg P 𝔭 = ℓ) ∧
      (∀ 𝔮 ∈ S, ∀ P : NK.Chebotarev.PrimeIdeal ↥L, P.asIdeal.LiesOver 𝔮.asIdeal →
        NK.UchidaKummer.localDeg P 𝔮 = 1) := by
  classical
  obtain ⟨u, hu⟩ := hnonpow
  -- The prescribed tuple of local `ℓ`-power classes: the class of `u` at `𝔭`, trivial elsewhere.
  let y : ∀ 𝔮 : T,
      (𝔮.1.adicCompletion K)ˣ ⧸ ellPowSubgroup (𝔮.1.adicCompletion K) ℓ :=
    fun 𝔮 => if h : 𝔮.1 = 𝔭 then
      h.symm ▸ ((u : (𝔭.adicCompletion K)ˣ ⧸ ellPowSubgroup (𝔭.adicCompletion K) ℓ))
      else 1
  obtain ⟨b, hb⟩ := hsurj y
  -- The class of `b` at `𝔭` is the class of `u`.
  have hb𝔭 : localPowClass K ℓ 𝔭 b =
      ((u : (𝔭.adicCompletion K)ˣ ⧸ ellPowSubgroup (𝔭.adicCompletion K) ℓ)) := by
    have h := hb ⟨𝔭, h𝔭T⟩
    simpa [y] using h
  -- The class of `b` at the primes of `S` is trivial.
  have hb𝔮 : ∀ (𝔮 : NK.Chebotarev.PrimeIdeal K) (_ : 𝔮 ∈ S),
      localPowClass K ℓ 𝔮 b = 1 := by
    intro 𝔮 h𝔮
    have hne : 𝔮 ≠ 𝔭 := fun h => h𝔭S (h ▸ h𝔮)
    have h := hb ⟨𝔮, hST 𝔮 h𝔮⟩
    simpa [y, hne] using h
  -- `b` is not an `ℓ`-th power in the completion at `𝔭`.
  have hmem : (Units.map (algebraMap K (𝔭.adicCompletion K)).toMonoidHom b)⁻¹ * u ∈
      ellPowSubgroup (𝔭.adicCompletion K) ℓ := by
    rw [← QuotientGroup.eq]
    simpa [localPowClass, MonoidHom.comp_apply] using hb𝔭
  obtain ⟨c, hc⟩ := MonoidHom.mem_range.mp hmem
  have hc' : c ^ ℓ = (Units.map (algebraMap K (𝔭.adicCompletion K)).toMonoidHom b)⁻¹ * u := hc
  have hbnotpow : ∀ d : (𝔭.adicCompletion K)ˣ,
      algebraMap K (𝔭.adicCompletion K) (b : K) ≠ (d : 𝔭.adicCompletion K) ^ ℓ := by
    intro d hd
    have hdu : Units.map (algebraMap K (𝔭.adicCompletion K)).toMonoidHom b = d ^ ℓ :=
      Units.ext (by simpa using hd)
    have hcu : u = (d * c) ^ ℓ := by
      rw [mul_pow, ← hdu, hc', ← mul_assoc, mul_inv_cancel, one_mul]
    exact hu (d * c) hcu.symm
  -- Hence `b` is not an `ℓ`-th power in `K` either.
  have hbglob : b ∉ NK.LocalAnabelian.powSubgroup ℓ K := by
    intro hmem2
    obtain ⟨e, he⟩ := MonoidHom.mem_range.mp hmem2
    have he' : e ^ ℓ = b := he
    have h2 : Units.map (algebraMap K (𝔭.adicCompletion K)).toMonoidHom b =
        (Units.map (algebraMap K (𝔭.adicCompletion K)).toMonoidHom e) ^ ℓ := by
      rw [← map_pow, he']
    exact hbnotpow (Units.map (algebraMap K (𝔭.adicCompletion K)).toMonoidHom e)
      (by simpa using congrArg (fun z : (𝔭.adicCompletion K)ˣ => (z : 𝔭.adicCompletion K)) h2)
  -- The Kummer field of `b` is Galois over `K` of degree `ℓ`.
  set L : IntermediateField K K' := NK.LocalAnabelian.kummerField (K' := K') ℓ b with hL
  have hKL := NK.LocalAnabelian.Kummer.isGalois_kummerField_and_finrank (k := K) (K' := K')
    ℓ hℓ hζ b hbglob
  haveI hgal : IsGalois K ↥L := hKL.1
  have hfinrank : Module.finrank K ↥L = ℓ := hKL.2
  haveI hfin : FiniteDimensional K L :=
    FiniteDimensional.of_finrank_pos (by rw [hfinrank]; exact hℓ.pos)
  haveI hNF : NumberField ↥L :=
    Commons.NumberTheory.NumberField.numberField_of_intermediateField L
  refine ⟨b, L, hfin, hNF, rfl, ?_, ?_⟩
  · -- The local degree at `𝔭` is `ℓ`.
    have hnotlocpow : ¬ ∃ c' : (𝔭.adicCompletion K)ˣ,
        algebraMap K (𝔭.adicCompletion K) (b : K) = (c' : 𝔭.adicCompletion K) ^ ℓ := by
      rintro ⟨c', hc''⟩
      exact hbnotpow c' hc''
    have hnotall : ¬ ∀ P : NK.Chebotarev.PrimeIdeal ↥L, P.asIdeal.LiesOver 𝔭.asIdeal →
        NK.UchidaKummer.localDeg P 𝔭 = 1 :=
      fun hall => hnotlocpow ((hdich b L hfin hNF rfl 𝔭).mp hall)
    exact localDeg_eq_of_finrank_eq_prime_of_not_forall_eq_one L ℓ hℓ hfinrank 𝔭 hnotall
  · -- The local degree at the primes of `S` is `1` (local Kummer dichotomy).
    intro 𝔮 h𝔮 P hP
    have hb𝔮' := hb𝔮 𝔮 h𝔮
    have hmem𝔮 : Units.map (algebraMap K (𝔮.adicCompletion K)).toMonoidHom b ∈
        ellPowSubgroup (𝔮.adicCompletion K) ℓ := by
      rw [← QuotientGroup.eq_one_iff]
      simpa [localPowClass, MonoidHom.comp_apply] using hb𝔮'
    obtain ⟨c₂, hc₂⟩ := MonoidHom.mem_range.mp hmem𝔮
    have hc₂' : c₂ ^ ℓ = Units.map (algebraMap K (𝔮.adicCompletion K)).toMonoidHom b := hc₂
    have hh : ∃ c' : (𝔮.adicCompletion K)ˣ,
        algebraMap K (𝔮.adicCompletion K) (b : K) = (c' : 𝔮.adicCompletion K) ^ ℓ :=
      ⟨c₂, by
        have h2 := congrArg (fun z : (𝔮.adicCompletion K)ˣ => (z : 𝔮.adicCompletion K)) hc₂'.symm
        simpa using h2⟩
    exact ((hdich b L hfin hNF rfl 𝔮).mpr hh) P hP

end NK.UchidaKummer.Differentiation
