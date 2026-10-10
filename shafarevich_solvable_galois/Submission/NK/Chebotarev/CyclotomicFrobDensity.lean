import Mathlib.RingTheory.Frobenius
import Mathlib.NumberTheory.NumberField.DirichletDensity
import Mathlib.NumberTheory.Padics.HeightOneSpectrum
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.NumberTheory.NumberField.Cyclotomic.Galois
import Submission.NK.Chebotarev.HasDirichletDensitySensitivity
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

open IsDedekindDomain
open scoped NumberField

namespace NK.Chebotarev

section Key

variable {n : ℕ} [NeZero n] {F : Type*} [Field F] [NumberField F] [IsCyclotomicExtension {n} ℚ F]

/-- **The Frobenius computes `p` modulo `n`.**  Let `F` be a cyclotomic extension of `ℚ` of
conductor `n`, let `P` be a maximal ideal of `𝓞 F` with `(n : 𝓞 F) ∉ P` (i.e. `P` is unramified
over the rational prime below it) and let `σ : Gal(F/ℚ)` satisfy the Frobenius congruence
`σ x ≡ x ^ q (mod P)` for all `x`, where `q = #(𝓞 ℚ / P ∩ 𝓞 ℚ)`.  Then the cyclotomic character of
`σ` is the residue class of `q` modulo `n`.

This is the cyclotomic reciprocity law `Frob_p(ζ) = ζ ^ p` in the language of
`IsCyclotomicExtension.Rat.galEquivZMod`. -/
theorem galEquivZMod_eq_of_isArithFrobAt {σ : Gal(F/ℚ)} {P : Ideal (𝓞 F)} [P.IsMaximal]
    (h : (galRestrict (𝓞 ℚ) ℚ F (𝓞 F) σ).toAlgHom.IsArithFrobAt P)
    (hnP : (n : 𝓞 F) ∉ P) :
    ((IsCyclotomicExtension.Rat.galEquivZMod n F σ : ZMod n)) =
      (Nat.card (𝓞 ℚ ⧸ P.under (𝓞 ℚ)) : ZMod n) := by
  have hζ : IsPrimitiveRoot (IsCyclotomicExtension.zeta n ℚ F) n :=
    IsCyclotomicExtension.zeta_spec n ℚ F
  have hzprim : IsPrimitiveRoot hζ.toInteger n := hζ.toInteger_isPrimitiveRoot
  have hcoe : algebraMap (𝓞 F) F hζ.toInteger = IsCyclotomicExtension.zeta n ℚ F := hζ.coe_toInteger
  -- The Frobenius congruence, transported to `F` through the primitive `n`-th root of unity.
  have h1F : σ (IsCyclotomicExtension.zeta n ℚ F)
      = (IsCyclotomicExtension.zeta n ℚ F) ^ Nat.card (𝓞 ℚ ⧸ P.under (𝓞 ℚ)) := by
    have h1 : galRestrict (𝓞 ℚ) ℚ F (𝓞 F) σ hζ.toInteger
        = hζ.toInteger ^ Nat.card (𝓞 ℚ ⧸ P.under (𝓞 ℚ)) :=
      AlgHom.IsArithFrobAt.apply_of_pow_eq_one h hzprim.pow_eq_one hnP
    have h2 := congrArg (algebraMap (𝓞 F) F) h1
    rw [map_pow] at h2
    rw [algebraMap_galRestrict_apply (𝓞 ℚ) (B := 𝓞 F) σ hζ.toInteger] at h2
    rw [hcoe] at h2
    exact h2
  -- The same action, read off from the cyclotomic character.
  have h2F : σ (IsCyclotomicExtension.zeta n ℚ F)
      = (IsCyclotomicExtension.zeta n ℚ F) ^
        ((IsCyclotomicExtension.Rat.galEquivZMod n F σ : ZMod n)).val :=
    IsCyclotomicExtension.Rat.galEquivZMod_apply_of_pow_eq n F σ hζ.pow_eq_one
  have h4F : (IsCyclotomicExtension.zeta n ℚ F) ^
        ((IsCyclotomicExtension.Rat.galEquivZMod n F σ : ZMod n)).val
      = (IsCyclotomicExtension.zeta n ℚ F) ^ Nat.card (𝓞 ℚ ⧸ P.under (𝓞 ℚ)) := h2F ▸ h1F
  -- Conclude modulo `n` by comparing the exponents of a primitive root of unity.
  have h5 : (((IsCyclotomicExtension.Rat.galEquivZMod n F σ : ZMod n)).val : ZMod n)
      = (Nat.card (𝓞 ℚ ⧸ P.under (𝓞 ℚ)) : ZMod n) := by
    have hcoe' : (((hζ.isUnit (NeZero.ne n)).unit : Fˣ) : F) =
        IsCyclotomicExtension.zeta n ℚ F := rfl
    have hpowu : ((hζ.isUnit (NeZero.ne n)).unit : Fˣ) ^
          ((IsCyclotomicExtension.Rat.galEquivZMod n F σ : ZMod n)).val
        = ((hζ.isUnit (NeZero.ne n)).unit : Fˣ) ^ Nat.card (𝓞 ℚ ⧸ P.under (𝓞 ℚ)) := by
      apply Units.ext
      simpa [hcoe'] using h4F
    have hmod := pow_eq_pow_iff_modEq.mp hpowu
    have hord : orderOf ((hζ.isUnit (NeZero.ne n)).unit : Fˣ) = n :=
      ((hζ.isUnit_unit (NeZero.ne n)).eq_orderOf).symm
    rw [hord] at hmod
    exact (ZMod.natCast_eq_natCast_iff _ _ n).mpr hmod
  rwa [← ZMod.natCast_zmod_val (IsCyclotomicExtension.Rat.galEquivZMod n F σ : ZMod n)]

end Key

/-! ## Elementary facts about the rational primes -/

section RatFacts

/-- The absolute norm of a finite place of `ℚ` is the rational prime generating it. -/
theorem absNorm_eq_natGenerator (p : PrimeIdeal ℚ) :
    Ideal.absNorm p.asIdeal = Rat.HeightOneSpectrum.natGenerator p :=
  Commons.NumberTheory.NumberField.Set.absNorm_eq_primesEquiv p

/-- The absolute norm of a finite place of `ℚ` is also the cardinality of the residue field. -/
theorem absNorm_eq_natCard (I : Ideal (𝓞 ℚ)) :
    Ideal.absNorm I = Nat.card (𝓞 ℚ ⧸ I) := by
  rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]

/-- A rational integer lies in a finite place of `ℚ` exactly when the generating prime divides
it. -/
theorem natGenerator_dvd_iff_mem (p : PrimeIdeal ℚ) (n : ℕ) :
    Rat.HeightOneSpectrum.natGenerator p ∣ n ↔ (n : 𝓞 ℚ) ∈ p.asIdeal := by
  have h1 := Rat.HeightOneSpectrum.natGenerator_dvd_iff p (n := n)
  have h2 : Rat.IsIntegralClosure.intEquiv (𝓞 ℚ) ((n : ℕ) : 𝓞 ℚ) = (n : ℤ) := by simp
  rw [← h2] at h1
  exact h1.trans (Ideal.apply_mem_of_equiv_iff (f := Rat.IsIntegralClosure.intEquiv (𝓞 ℚ))
    (I := p.asIdeal) (x := ((n : ℕ) : 𝓞 ℚ)))

/-- The "good" rational primes for the conductor `n`, i.e. those of residue characteristic
coprime to `n`, are exactly the primes not dividing `n`. -/
theorem absNorm_coprime_iff (p : PrimeIdeal ℚ) (n : ℕ) :
    (Ideal.absNorm p.asIdeal).Coprime n ↔ (n : 𝓞 ℚ) ∉ p.asIdeal := by
  rw [absNorm_eq_natGenerator, Nat.Prime.coprime_iff_not_dvd
    (Rat.HeightOneSpectrum.prime_natGenerator p), natGenerator_dvd_iff_mem]

end RatFacts

/-! ## Comparing `n` at a prime and at a prime above it -/

section Transfer

/-- A prime `P` of `𝓞 F` above `p` sees the integer `n` precisely when `p` does. -/
theorem mem_natCast_iff {F : Type*} [Field F] [NumberField F]
    (p : PrimeIdeal ℚ) (P : PrimeIdeal F) (hP : P.asIdeal.LiesOver p.asIdeal) (n : ℕ) :
    (n : 𝓞 F) ∈ P.asIdeal ↔ (n : 𝓞 ℚ) ∈ p.asIdeal := by
  rw [hP.over, Ideal.under_def, Ideal.mem_comap, map_natCast]

end Transfer

/-! ## The Frobenius set is the union of residue classes

Recall that for a cyclotomic extension `F/ℚ` of conductor `n`, the rational prime `p` is
unramified in `F` unless it divides `n`, and in that case the Frobenius at `p` corresponds, under
`IsCyclotomicExtension.Rat.galEquivZMod`, to the class of `p` in `(ℤ/nℤ)ˣ`.  The two statements
below make this precise, and show that the set of primes whose Frobenius is a given `σ` is, up to
the finitely many primes dividing `n`, the residue class of `galEquivZMod σ`. -/

section Directions

variable {n : ℕ} [NeZero n] {F : Type*} [Field F] [NumberField F] [IsCyclotomicExtension {n} ℚ F]

/-- If `σ` is a Frobenius at a prime `P` above the "good" rational prime `p`, then the cyclotomic
character of `σ` is the norm of `p` modulo `n`. -/
theorem zmod_eq_absNorm_of_isFrobAt (p : PrimeIdeal ℚ) (P : PrimeIdeal F)
    (hP : P.asIdeal.LiesOver p.asIdeal) (σ : Gal(F/ℚ)) (h : IsFrobAt P σ)
    (hgood : (n : 𝓞 ℚ) ∉ p.asIdeal) :
    ((IsCyclotomicExtension.Rat.galEquivZMod n F σ : ZMod n)) =
      (Ideal.absNorm p.asIdeal : ZMod n) := by
  have hnP : (n : 𝓞 F) ∉ P.asIdeal := fun hmem => hgood ((mem_natCast_iff p P hP n).mp hmem)
  rw [galEquivZMod_eq_of_isArithFrobAt (n := n) (σ := σ) (P := P.asIdeal) h hnP, hP.over,
    absNorm_eq_natCard]

/-- Conversely, at a good prime `p` the residue class of the norm of `p` modulo `n` determines
the Frobenius. -/
theorem isFrobAtPrime_of_eq_absNorm (p : PrimeIdeal ℚ) (σ : Gal(F/ℚ))
    (h : ((IsCyclotomicExtension.Rat.galEquivZMod n F σ : ZMod n)) =
      (Ideal.absNorm p.asIdeal : ZMod n)) :
    IsFrobAtPrime (K := ℚ) (L := F) p σ := by
  have : IsGalois ℚ F := IsCyclotomicExtension.isGalois {n} ℚ F
  obtain ⟨P, hP⟩ := exists_primeIdeal_liesOver (K := ℚ) (L := F) p
  obtain ⟨φ, hφ⟩ := exists_isFrobAt (K := ℚ) (L := F) p P hP
  -- The right-hand side of `h` is a unit, so `p` does not divide `n`.
  have hunit : IsUnit ((Ideal.absNorm p.asIdeal : ℕ) : ZMod n) := by
    rw [← h]
    exact (IsCyclotomicExtension.Rat.galEquivZMod n F σ).isUnit
  have hgood : (n : 𝓞 ℚ) ∉ p.asIdeal :=
    (absNorm_coprime_iff p n).mp ((ZMod.isUnit_iff_coprime _ n).mp hunit)
  have hp := zmod_eq_absNorm_of_isFrobAt (n := n) p P hP φ hφ hgood
  have hχ : IsCyclotomicExtension.Rat.galEquivZMod n F σ
      = IsCyclotomicExtension.Rat.galEquivZMod n F φ :=
    Units.ext (by rw [h, hp])
  have hσφ : σ = φ := (IsCyclotomicExtension.Rat.galEquivZMod n F).injective hχ
  exact ⟨P, hP, hσφ ▸ hφ⟩

end Directions

/-! ## The density statement -/

/-- **Čebotarev for cyclotomic extensions.**  In a cyclotomic extension `F/ℚ` of conductor `n`,
the primes whose Frobenius is a prescribed element `σ` of the Galois group have Dirichlet density
`1/φ(n)`. -/
theorem CyclotomicFrobDensity {n : ℕ} [NeZero n] {F : Type*} [Field F] [NumberField F]
    [IsCyclotomicExtension {n} ℚ F] (σ : Gal(F/ℚ)) :
    NumberField.Set.HasDirichletDensity
      {p : NK.Chebotarev.PrimeIdeal ℚ | NK.Chebotarev.IsFrobAtPrime (K := ℚ) (L := F) p σ}
      (1 / (Nat.totient n : ℝ)) := by
  set D : Set (PrimeIdeal ℚ) := {p | ((Ideal.absNorm p.asIdeal : ℕ) : ZMod n) =
        ((IsCyclotomicExtension.Rat.galEquivZMod n F σ : ZMod n))} with hDdef
  set Sfrob : Set (PrimeIdeal ℚ) := {p | IsFrobAtPrime (K := ℚ) (L := F) p σ} with hSdef
  -- Dirichlet's theorem: the residue class of `galEquivZMod σ` has density `1/φ(n)`.
  have hT : NumberField.Set.HasDirichletDensity D (1 / (Nat.totient n : ℝ)) := by
    rw [one_div]
    exact Commons.NumberTheory.NumberField.Set.hasDirichletDensity_residueClass n
      (IsCyclotomicExtension.Rat.galEquivZMod n F σ)
  -- Every prime in the residue class has the right Frobenius.
  have hDsub : D ⊆ Sfrob := fun p hp => isFrobAtPrime_of_eq_absNorm p σ hp.symm
  -- The two sets differ only at the primes dividing `n`.
  have hBfin : {p : PrimeIdeal ℚ | (n : 𝓞 ℚ) ∈ p.asIdeal}.Finite := by
    refine (Ideal.finite_factors (R := 𝓞 ℚ) (I := Ideal.span {((n : ℕ) : 𝓞 ℚ)}) ?_).subset ?_
    · intro h
      exact (by exact_mod_cast (NeZero.ne n : n ≠ 0) : ((n : ℕ) : 𝓞 ℚ) ≠ 0)
        (Ideal.span_singleton_eq_bot.mp h)
    · intro p hp
      simp only [Set.mem_ofPred_eq] at hp ⊢
      rw [Ideal.dvd_iff_le, Ideal.span_singleton_le_iff_mem]
      exact hp
  have hdiff : ((D \ Sfrob) ∪ (Sfrob \ D)).Finite := by
    refine hBfin.subset ?_
    rintro p (hp | hp)
    · exact (hp.2 (hDsub hp.1)).elim
    · by_contra hmem
      obtain ⟨P, hP, hFrob⟩ := hp.1
      exact hp.2 ((zmod_eq_absNorm_of_isFrobAt p P hP σ hFrob hmem).symm)
  exact HasDirichletDensitySensitivity hdiff hT

end NK.Chebotarev
