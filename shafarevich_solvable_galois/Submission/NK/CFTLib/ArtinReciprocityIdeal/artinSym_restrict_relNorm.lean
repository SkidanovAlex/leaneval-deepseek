import Mathlib.Order.CompletePartialOrder
import Mathlib.Algebra.CharZero.Infinite
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.RingTheory.Ideal.Norm.RelNorm
import Submission.NK.CFTLib.ARL.RelNormFI
import Submission.NK.CFTLib.Arl.isFrobAt_of_isFrobAt_any_primeOver
import Submission.NK.CFTLib.ArtinReciprocityIdeal.normRayLeKer
import Submission.NK.Chebotarev.ConjugacyOfFrobenius
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace NK.CFTLib.ArtinReciprocityIdeal

open NumberField IsDedekindDomain
open scoped NumberField nonZeroDivisors IsMulCommutative

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

/-! ## Auxiliary lemmas

The proof of the main theorem `artinSym_restrict_relNorm` proceeds as follows.

* `galRestrict_restrictScalars_apply`: the action of a `↥E`-automorphism of `M` on `𝓞 M` does not
  depend on which intermediate base field is used in `galRestrict`.
* `restrictNormalHom_frob_residue`: the residue of the restriction of a Frobenius element at a
  prime `𝔔` (in `M`) to the intermediate field `L`.
* `natCard_quotient_eq_pow_inertiaDeg_under`: `N𝔮 = N𝔭 ^ f(𝔮|𝔭)`.
* `sub_pow_iterate_mem_of`: iterating a congruence.
* `restrict_frobAtPrime_eq`: the restriction of the Frobenius at `𝔮` (in `M/↥E`) to `L` is the
  `f(𝔮|𝔭)`-th power of the Frobenius at `𝔭 = 𝔮 ∩ K` (in `L/K`).  This is the mathematical heart of
  the statement.
-/

section BaseChange

variable {K M : Type} [Field K] [NumberField K] [Field M] [NumberField M]
  [Algebra K M] [FiniteDimensional K M] [IsGalois K M]

/-- **The action on `𝓞 M` of an automorphism of `M` over an intermediate field `E` does not
depend on the choice of the base field `K ⊆ E`** used to define `galRestrict`. -/
lemma galRestrict_restrictScalars_apply (E : IntermediateField K M) [FiniteDimensional K ↥E]
    (σ : M ≃ₐ[↥E] M) (y : 𝓞 M) :
    galRestrict (𝓞 ↥E) (↥E) M (𝓞 M) σ y
      = galRestrict (𝓞 K) K M (𝓞 M) (σ.restrictScalars K) y := by
  apply IsIntegralClosure.algebraMap_injective (𝓞 M) (𝓞 K) M
  rw [algebraMap_galRestrict_apply, algebraMap_galRestrict_apply, AlgEquiv.restrictScalars_apply]

end BaseChange

section ResidueTransport

variable {K M : Type} [Field K] [NumberField K] [Field M] [NumberField M]
  [Algebra K M] [FiniteDimensional K M] [IsGalois K M]

/-- **The residue of the restriction of a Frobenius element.**  Let `σ ∈ Gal(M/↥E)` be a Frobenius
element at the prime `𝔔` of `𝓞 M`, lying over the prime `𝔮` of `𝓞 ↥E`.  Then the restriction of
`σ` to the intermediate field `L` acts on the residue field at `℘ = 𝔔 ∩ 𝓞 L` by
`x ↦ x ^ N𝔮`. -/
lemma restrictNormalHom_frob_residue (E L : IntermediateField K M)
    [FiniteDimensional K ↥E] [FiniteDimensional K ↥L] [IsGalois K ↥L]
    (σ : M ≃ₐ[↥E] M) (𝔮 : NK.Chebotarev.PrimeIdeal ↥E) (𝔔 : NK.Chebotarev.PrimeIdeal M)
    (h𝔔 : 𝔔.asIdeal.LiesOver 𝔮.asIdeal)
    (hfrob : NK.Chebotarev.IsFrobAt 𝔔 σ) (x : 𝓞 ↥L) :
    Ideal.Quotient.mk (𝔔.asIdeal.under (𝓞 ↥L))
        (galRestrict (𝓞 K) K ↥L (𝓞 ↥L)
          (AlgEquiv.restrictNormalHom (F := K) (K₁ := M) L (σ.restrictScalars K)) x)
      = (Ideal.Quotient.mk (𝔔.asIdeal.under (𝓞 ↥L)) x) ^ (Nat.card (𝓞 ↥E ⧸ 𝔮.asIdeal)) := by
  have h1 : galRestrict (𝓞 ↥E) (↥E) M (𝓞 M) σ (algebraMap (𝓞 ↥L) (𝓞 M) x)
      - algebraMap (𝓞 ↥L) (𝓞 M) (x ^ Nat.card (𝓞 ↥E ⧸ 𝔮.asIdeal)) ∈ 𝔔.asIdeal := by
    have h := hfrob (algebraMap (𝓞 ↥L) (𝓞 M) x)
    rw [← h𝔔.over] at h
    simpa only [AlgEquiv.coe_toAlgHom, ← map_pow] using h
  rw [galRestrict_restrictScalars_apply E σ (algebraMap (𝓞 ↥L) (𝓞 M) x)] at h1
  rw [← NK.Chebotarev.galRestrict_restrictNormalHom L (σ.restrictScalars K) x] at h1
  rw [← map_sub] at h1
  have hmem := (Ideal.mem_under (𝓞 ↥L) 𝔔.asIdeal).mpr h1
  rw [← map_pow, Ideal.Quotient.eq]
  exact hmem

end ResidueTransport

section Exponent

variable {K M : Type} [Field K] [NumberField K] [Field M] [NumberField M]
  [Algebra K M] [FiniteDimensional K M] [IsGalois K M]

/-- **The cardinality of the residue field is the inertia-degree-th power of that of the
subfield.**  For a prime `𝔮` of a finite extension `↥E/K` of number fields,
`N 𝔮 = (N (𝔮 ∩ K)) ^ f(𝔮 | 𝔮 ∩ K)`. -/
lemma natCard_quotient_eq_pow_inertiaDeg_under (E : IntermediateField K M) [FiniteDimensional K ↥E]
    (𝔮 : NK.Chebotarev.PrimeIdeal ↥E) :
    Nat.card (𝓞 ↥E ⧸ 𝔮.asIdeal)
      = (Nat.card (𝓞 K ⧸ (𝔮.under (𝓞 K)).asIdeal)) ^ (𝔮.asIdeal.inertiaDeg (𝓞 K)) := by
  haveI : 𝔮.asIdeal.LiesOver (𝔮.under (𝓞 K)).asIdeal :=
    ⟨HeightOneSpectrum.under_asIdeal (𝓞 K) 𝔮⟩
  have h := Ideal.absNorm_pow_inertiaDeg (p := (𝔮.under (𝓞 K)).asIdeal) (q := 𝔮.asIdeal)
  simp only [Ideal.absNorm_apply, Submodule.cardQuot_apply] at h
  exact h.symm

end Exponent

section Iterate

/-- Iterating the congruence `f x ≡ x ^ q (mod P)` gives `f^[n] x ≡ x ^ (q ^ n) (mod P)`. -/
theorem sub_pow_iterate_mem_of {S : Type*} [CommRing S] (P : Ideal S) (f : S → S) (q : ℕ)
    (hf : ∀ x : S, f x - x ^ q ∈ P) (n : ℕ) (x : S) :
    (f^[n]) x - x ^ (q ^ n) ∈ P := by
  induction n generalizing x with
  | zero => simp
  | succ n ih =>
      have h1 : f ((f^[n]) x) - ((f^[n]) x) ^ q ∈ P := hf _
      have h2 : ((f^[n]) x) ^ q - (x ^ (q ^ n)) ^ q ∈ P := by
        obtain ⟨c, hc⟩ := sub_dvd_pow_sub_pow ((f^[n]) x) (x ^ (q ^ n)) q
        rw [hc]
        exact Ideal.mul_mem_right _ P (ih x)
      have h3 : f ((f^[n]) x) - (x ^ (q ^ n)) ^ q ∈ P := by
        have h := add_mem h1 h2
        have heq : f ((f^[n]) x) - (x ^ (q ^ n)) ^ q
            = (f ((f^[n]) x) - ((f^[n]) x) ^ q)
              + (((f^[n]) x) ^ q - (x ^ (q ^ n)) ^ q) := by ring
        rwa [heq]
      rw [Function.iterate_succ_apply', Nat.pow_succ, pow_mul]
      exact h3

end Iterate

/-! ## The restriction of the Frobenius at a prime -/

section Prime

variable {K M : Type} [Field K] [NumberField K] [Field M] [NumberField M]
  [Algebra K M] [FiniteDimensional K M] [IsGalois K M]
  (E L : IntermediateField K M) [FiniteDimensional K ↥E] [FiniteDimensional K ↥L]
  [IsGalois K ↥L]

/-- **The restriction of the Frobenius at `𝔮` to `L`.**  Let `E, L ⊆ M` be intermediate fields of
a finite Galois extension `M/K`, `𝔮` a prime of `𝓞 ↥E` unramified in `M/↥E` whose trace
`𝔭 = 𝔮 ∩ K` is unramified in `L/K`.  Then the restriction of the Frobenius at `𝔮` of `M/↥E` to
`L` is the `f(𝔮|𝔭)`-th power of the Frobenius at `𝔭` of `L/K`:

  `Frob_𝔮(M/↥E)|_L = Frob_𝔭(L/K) ^ f(𝔮|𝔭)`.

Indeed, if `𝔔 | 𝔮` is the prime of `M` fixed by `Frob_𝔮` then for `x ∈ 𝓞 L` one has
`Frob_𝔮(M/↥E)|_L x ≡ x^{N𝔮} (mod 𝔔 ∩ 𝓞 L)` while `Frob_𝔭` acts as `x ↦ x^{N𝔭}`, and
`N𝔮 = (N𝔭)^{f(𝔮|𝔭)}`; the Frobenius at an unramified prime is determined by its residue action. -/
lemma restrict_frobAtPrime_eq
    (hcommE : ∀ a b : M ≃ₐ[↥E] M, a * b = b * a)
    (hcommL : ∀ a b : (↥L ≃ₐ[K] ↥L), a * b = b * a)
    (𝔮 : NK.Chebotarev.PrimeIdeal ↥E)
    (hunrE : IsUnramified (K := ↥E) (L := M) 𝔮)
    (hunrL : IsUnramified (K := K) (L := ↥L) (𝔮.under (𝓞 K))) :
    AlgEquiv.restrictNormalHom (F := K) (K₁ := M) L
        ((NK.Chebotarev.frobAtPrime (K := ↥E) (L := M) 𝔮).restrictScalars K)
      = (NK.Chebotarev.frobAtPrime (K := K) (L := ↥L) (𝔮.under (𝓞 K)))
          ^ (𝔮.asIdeal.inertiaDeg (𝓞 K)) := by
  classical
  set σ : M ≃ₐ[↥E] M := NK.Chebotarev.frobAtPrime (K := ↥E) (L := M) 𝔮 with hσdef
  set τ : ↥L ≃ₐ[K] ↥L :=
    AlgEquiv.restrictNormalHom (F := K) (K₁ := M) L (σ.restrictScalars K) with hτdef
  set τ₀ : ↥L ≃ₐ[K] ↥L := NK.Chebotarev.frobAtPrime (K := K) (L := ↥L) (𝔮.under (𝓞 K))
    with hτ₀def
  set f : ℕ := 𝔮.asIdeal.inertiaDeg (𝓞 K) with hfdef
  have hfrobσ : NK.Chebotarev.IsFrobAtPrime (K := ↥E) (L := M) 𝔮 σ := by
    rw [hσdef]
    exact NK.Chebotarev.isFrobAtPrime_frobAtPrime hcommE 𝔮 hunrE
  obtain ⟨𝔔, h𝔔, hfrob⟩ := hfrobσ
  set ℘ : NK.Chebotarev.PrimeIdeal ↥L := 𝔔.under (𝓞 ↥L) with h℘def
  have h℘as : ℘.asIdeal = 𝔔.asIdeal.under (𝓞 ↥L) := by
    rw [h℘def]; exact HeightOneSpectrum.under_asIdeal (𝓞 ↥L) 𝔔
  have h℘lies : ℘.asIdeal.LiesOver (𝔮.under (𝓞 K)).asIdeal :=
    ⟨by simp only [HeightOneSpectrum.under_asIdeal (𝓞 K) 𝔮, h𝔔.over, h℘as,
      Ideal.under_under]⟩
  -- The residue action of the restriction of `σ`
  have hres : ∀ x : 𝓞 ↥L,
      Ideal.Quotient.mk ℘.asIdeal (galRestrict (𝓞 K) K ↥L (𝓞 ↥L) τ x)
        = (Ideal.Quotient.mk ℘.asIdeal x) ^ (Nat.card (𝓞 ↥E ⧸ 𝔮.asIdeal)) := by
    intro x
    have h := restrictNormalHom_frob_residue E L σ 𝔮 𝔔 h𝔔 hfrob x
    rwa [← hτdef, ← h℘as] at h
  -- `Frob 𝔭` is a Frobenius at every prime over `𝔭`
  have hτ₀frob : NK.Chebotarev.IsFrobAt ℘ τ₀ := by
    obtain ⟨℘₀, h℘₀lies, h℘₀frob⟩ :=
      NK.Chebotarev.isFrobAtPrime_frobAtPrime (K := K) (L := ↥L) hcommL
        (𝔮.under (𝓞 K)) hunrL
    rw [hτ₀def]
    exact NK.CFTLib.Arl.isFrobAt_of_isFrobAt_any_primeOver hcommL h℘₀lies h℘lies h℘₀frob
  have hq : Nat.card (𝓞 K ⧸ ℘.asIdeal.under (𝓞 K))
      = Nat.card (𝓞 K ⧸ (𝔮.under (𝓞 K)).asIdeal) := by
    rw [← h℘lies.over]
  -- the residue action of `τ₀ ^ f`
  have hpw : ∀ x : 𝓞 ↥L, galRestrict (𝓞 K) K ↥L (𝓞 ↥L) (τ₀ ^ f) x
      - x ^ ((Nat.card (𝓞 K ⧸ (𝔮.under (𝓞 K)).asIdeal)) ^ f) ∈ ℘.asIdeal := by
    intro x
    have hφ : ∀ y : 𝓞 ↥L, galRestrict (𝓞 K) K ↥L (𝓞 ↥L) τ₀ y
        - y ^ (Nat.card (𝓞 K ⧸ (𝔮.under (𝓞 K)).asIdeal)) ∈ ℘.asIdeal := by
      intro y
      rw [← hq]
      exact hτ₀frob y
    have hcoe : ∀ n : ℕ, (⇑(galRestrict (𝓞 K) K ↥L (𝓞 ↥L) τ₀))^[n]
        = ⇑(galRestrict (𝓞 K) K ↥L (𝓞 ↥L) (τ₀ ^ n)) := by
      intro n
      rw [map_pow, AlgEquiv.coe_pow]
    have h := sub_pow_iterate_mem_of ℘.asIdeal
        (⇑(galRestrict (𝓞 K) K ↥L (𝓞 ↥L) τ₀))
        (Nat.card (𝓞 K ⧸ (𝔮.under (𝓞 K)).asIdeal)) hφ f x
    rw [hcoe] at h
    exact h
  have hNq : Nat.card (𝓞 ↥E ⧸ 𝔮.asIdeal)
      = (Nat.card (𝓞 K ⧸ (𝔮.under (𝓞 K)).asIdeal)) ^ f := by
    rw [hfdef]
    exact natCard_quotient_eq_pow_inertiaDeg_under E 𝔮
  refine Commons.NumberTheory.NumberField.FrobeniusEqOfCommute.eq_of_residue_mk_eq
    (𝔮.under (𝓞 K)) ℘ h℘lies (hunrL ℘ h℘lies) τ (τ₀ ^ f) ?_
  intro x
  have h2 : Ideal.Quotient.mk ℘.asIdeal (galRestrict (𝓞 K) K ↥L (𝓞 ↥L) (τ₀ ^ f) x)
      = (Ideal.Quotient.mk ℘.asIdeal x) ^ ((Nat.card (𝓞 K ⧸ (𝔮.under (𝓞 K)).asIdeal)) ^ f) := by
    rw [← map_pow, Ideal.Quotient.eq]
    exact hpw x
  rw [hres x, h2, hNq]

end Prime

/-! ## The main theorem -/

/-- **Functoriality of the Artin symbol under relative norms** (Lang, *Algebraic Number Theory*,
Ch. X §1; the guidance's item 1 for the ideal-theoretic reciprocity law).

Let `K ⊆ E, L ⊆ M` be intermediate fields of a finite Galois extension `M/K` with `E ⊓ L = ⊥`
and `E ⊔ L = ⊤` (so `M = E·L`, `Gal(M/E) ≅ Gal(L/K)` by restriction), and let `m` be a modulus
containing every prime ramified in `M/E` and every prime ramified in `L/K`.  Then for every
fractional ideal `𝔄` of `E` coprime to `(m)`,

  `ψ_{M/E}(𝔄)|_L = ψ_{L/K}(N_{E/K}(𝔄))`,

i.e. the restriction to `L` of the Artin symbol of `𝔄` in `M/E` is the Artin symbol in `L/K` of
the relative norm of `𝔄`.

The coprimality hypothesis is necessary: at a ramified prime `frobAtPrime` (`Classical.choose`)
is only a non-canonical representative of a coset of the inertia group, and the two sides use
independent choices.  For primes `𝔮 ∈ supp 𝔄` (resp. `𝔭 = 𝔮 ∩ K`) outside `(m)` the Frobenius is
the unique one, and the claim is the standard computation `N_{E/K}(𝔮) = 𝔭^{f(𝔮|𝔭)}` together with
the compatibility of Frobenius elements under restriction. -/
theorem artinSym_restrict_relNorm {K M : Type} [Field K] [NumberField K] [Field M] [NumberField M]
    [Algebra K M] [FiniteDimensional K M] [IsGalois K M]
    (E L : IntermediateField K M) [FiniteDimensional K ↥E] [FiniteDimensional K ↥L]
    [IsGalois K ↥E] [IsGalois K ↥L]
    (hsup : E ⊔ L = ⊤) (hinf : E ⊓ L = ⊥)
    (hcommE : ∀ a b : M ≃ₐ[↥E] M, a * b = b * a)
    (hcommL : ∀ a b : (↥L ≃ₐ[K] ↥L), a * b = b * a)
    (m : ℕ)
    (hramE : ∀ 𝔮 : NK.Chebotarev.PrimeIdeal ↥E,
      ¬ NK.CFTLib.ArtinReciprocityIdeal.IsUnramified (K := ↥E) (L := M) 𝔮 →
      (m : 𝓞 ↥E) ∈ 𝔮.asIdeal)
    (hram : ∀ p : NK.Chebotarev.PrimeIdeal K,
      ¬ NK.CFTLib.ArtinReciprocityIdeal.IsUnramified (K := K) (L := ↥L) p →
      (m : 𝓞 K) ∈ p.asIdeal)
    (𝔄 : (FractionalIdeal (𝓞 ↥E)⁰ ↥E)ˣ)
    (hcop : NK.CFTLib.ArtinReciprocityIdeal.FracCoprime (K := ↥E) m 𝔄) :
    AlgEquiv.restrictNormalHom (F := K) (K₁ := M) L
        ((NK.CFTLib.Arl.artinSym (K := ↥E) (L := M) hcommE
            (𝔄 : FractionalIdeal (𝓞 ↥E)⁰ ↥E)).restrictScalars K)
      = NK.CFTLib.Arl.artinSym (K := K) (L := ↥L) hcommL
          (NK.CFTLib.ARL.relNormUnit (K := K) (L := ↥E) 𝔄) := by
  classical
  letI hMC_E : IsMulCommutative (M ≃ₐ[↥E] M) := ⟨⟨hcommE⟩⟩
  letI hMC_L : IsMulCommutative (↥L ≃ₐ[K] ↥L) := ⟨⟨hcommL⟩⟩
  -- the two sides are monoid homomorphisms of the group of fractional ideals of `↥E`
  let Φ : (M ≃ₐ[↥E] M) →* (↥L ≃ₐ[K] ↥L) :=
    (AlgEquiv.restrictNormalHom (F := K) (K₁ := M) L).comp (AlgEquiv.restrictScalarsHom K)
  let F : Frac ↥E →* (↥L ≃ₐ[K] ↥L) := Φ.comp (artinSymFracHom (K := ↥E) (L := M) hcommE)
  let G : Frac ↥E →* (↥L ≃ₐ[K] ↥L) :=
    (artinSymFracHom (K := K) (L := ↥L) hcommL).comp
      (NK.CFTLib.ARL.relNormUnit (K := K) (L := ↥E))
  have hFG : F 𝔄 = G 𝔄 := by
    set S : Finset (NK.Chebotarev.PrimeIdeal ↥E) :=
      (Filter.eventually_cofinite.mp (FractionalIdeal.finite_factors (K := ↥E)
        (𝔄 : FractionalIdeal (𝓞 ↥E)⁰ ↥E))).toFinset with hS
    have hSmem : ∀ 𝔮 : NK.Chebotarev.PrimeIdeal ↥E,
        𝔮 ∈ S ↔ FractionalIdeal.count ↥E 𝔮 (𝔄 : FractionalIdeal (𝓞 ↥E)⁰ ↥E) ≠ 0 :=
      fun 𝔮 => Set.Finite.mem_toFinset _
    have hsupp : Function.mulSupport (fun 𝔮 : NK.Chebotarev.PrimeIdeal ↥E =>
        ((𝔮.asIdeal : Ideal (𝓞 ↥E)) : FractionalIdeal (𝓞 ↥E)⁰ ↥E) ^
          FractionalIdeal.count ↥E 𝔮 (𝔄 : FractionalIdeal (𝓞 ↥E)⁰ ↥E)) ⊆ ↑S := by
      intro 𝔮 h𝔮
      exact (hSmem 𝔮).mpr fun h0 => h𝔮 (by simp only [h0, zpow_zero])
    have hfac : (∏ 𝔮 ∈ S, (NK.CFTLib.ARL.primeUnit 𝔮) ^
        FractionalIdeal.count ↥E 𝔮 (𝔄 : FractionalIdeal (𝓞 ↥E)⁰ ↥E)) = 𝔄 := by
      apply Units.ext
      rw [Units.coe_prod]
      simp only [NK.CFTLib.ARL.primeUnit_val, Units.val_zpow_eq_zpow_val]
      rw [← finprod_eq_prod_of_mulSupport_subset _ hsupp]
      exact FractionalIdeal.finprod_heightOneSpectrum_factorization' ↥E 𝔄.ne_zero
    -- at a prime in the support both sides are computed by the prime case
    have hprime : ∀ 𝔮 ∈ S, F (NK.CFTLib.ARL.primeUnit 𝔮)
        = G (NK.CFTLib.ARL.primeUnit 𝔮) := by
      intro 𝔮 h𝔮
      have hcount : FractionalIdeal.count ↥E 𝔮 (𝔄 : FractionalIdeal (𝓞 ↥E)⁰ ↥E) ≠ 0 :=
        (hSmem 𝔮).mp h𝔮
      have hunrE : IsUnramified (K := ↥E) (L := M) 𝔮 := by
        by_contra h
        exact hcount (hcop 𝔮 (hramE 𝔮 h))
      have hunrL : IsUnramified (K := K) (L := ↥L) (𝔮.under (𝓞 K)) := by
        by_contra h
        have hm : (m : 𝓞 K) ∈ (𝔮.under (𝓞 K)).asIdeal := hram (𝔮.under (𝓞 K)) h
        rw [HeightOneSpectrum.under_asIdeal] at hm
        have hm' : (m : 𝓞 ↥E) ∈ 𝔮.asIdeal := by
          have h2 := (Ideal.mem_under (𝓞 K) 𝔮.asIdeal).mp hm
          simpa using h2
        exact hcount (hcop 𝔮 hm')
      have hF : F (NK.CFTLib.ARL.primeUnit 𝔮) = AlgEquiv.restrictNormalHom (F := K)
          (K₁ := M) L
          ((NK.Chebotarev.frobAtPrime (K := ↥E) (L := M) 𝔮).restrictScalars K) := by
        change Φ (artinSymFracHom (K := ↥E) (L := M) hcommE
          (NK.CFTLib.ARL.primeUnit 𝔮)) = _
        rw [artinSymFracHom_apply, NK.CFTLib.ARL.primeUnit_val,
          NK.CFTLib.Arl.artinSym_prime]
        rfl
      have hG : G (NK.CFTLib.ARL.primeUnit 𝔮) = (NK.Chebotarev.frobAtPrime (K := K)
          (L := ↥L) (𝔮.under (𝓞 K))) ^ (𝔮.asIdeal.inertiaDeg (𝓞 K)) := by
        haveI : 𝔮.asIdeal.IsMaximal :=
          Ring.DimensionLEOne.maximalOfPrime 𝔮.ne_bot 𝔮.isPrime
        have hqne : (𝔮.under (𝓞 K)).asIdeal ≠ ⊥ := by
          rw [HeightOneSpectrum.under_asIdeal]
          exact Ideal.under_ne_bot (𝓞 K) 𝔮.ne_bot
        haveI : ((𝔮.under (𝓞 K)).asIdeal).IsMaximal :=
          Ring.DimensionLEOne.maximalOfPrime hqne inferInstance
        haveI : 𝔮.asIdeal.LiesOver (𝔮.under (𝓞 K)).asIdeal :=
          ⟨HeightOneSpectrum.under_asIdeal (𝓞 K) 𝔮⟩
        change artinSymFracHom (K := K) (L := ↥L) hcommL
          (NK.CFTLib.ARL.relNormUnit (K := K) (L := ↥E)
            (NK.CFTLib.ARL.primeUnit 𝔮)) = _
        rw [NK.CFTLib.ARL.relNormUnit_primeUnit, artinSymFracHom_apply, Units.val_mk0,
          Ideal.relNorm_eq_pow_of_isMaximal 𝔮.asIdeal ((𝔮.under (𝓞 K)).asIdeal),
          FractionalIdeal.coeIdeal_pow,
          artinSymFrac_pow hcommL
            (FractionalIdeal.coeIdeal_ne_zero.mpr ((𝔮.under (𝓞 K)).ne_bot)),
          NK.CFTLib.Arl.artinSym_prime]
      rw [hF, hG]
      exact restrict_frobAtPrime_eq E L hcommE hcommL 𝔮 hunrE hunrL
    calc F 𝔄 = F (∏ 𝔮 ∈ S, (NK.CFTLib.ARL.primeUnit 𝔮) ^
            FractionalIdeal.count ↥E 𝔮 (𝔄 : FractionalIdeal (𝓞 ↥E)⁰ ↥E)) := by rw [hfac]
      _ = ∏ 𝔮 ∈ S, F (NK.CFTLib.ARL.primeUnit 𝔮) ^
            FractionalIdeal.count ↥E 𝔮 (𝔄 : FractionalIdeal (𝓞 ↥E)⁰ ↥E) := by
          rw [map_prod]
          exact Finset.prod_congr rfl fun 𝔮 _ => map_zpow _ _ _
      _ = ∏ 𝔮 ∈ S, G (NK.CFTLib.ARL.primeUnit 𝔮) ^
            FractionalIdeal.count ↥E 𝔮 (𝔄 : FractionalIdeal (𝓞 ↥E)⁰ ↥E) :=
          Finset.prod_congr rfl fun 𝔮 h𝔮 => by rw [hprime 𝔮 h𝔮]
      _ = G (∏ 𝔮 ∈ S, (NK.CFTLib.ARL.primeUnit 𝔮) ^
            FractionalIdeal.count ↥E 𝔮 (𝔄 : FractionalIdeal (𝓞 ↥E)⁰ ↥E)) := by
          rw [map_prod]
          exact Finset.prod_congr rfl fun 𝔮 _ => (map_zpow _ _ _).symm
      _ = G 𝔄 := by rw [hfac]
  simpa only [F, G, Φ, MonoidHom.comp_apply, artinSymFracHom_apply,
    AlgEquiv.restrictScalarsHom_apply] using hFG

end NK.CFTLib.ArtinReciprocityIdeal
