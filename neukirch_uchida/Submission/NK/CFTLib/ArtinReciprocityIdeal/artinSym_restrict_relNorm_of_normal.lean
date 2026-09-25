import Mathlib
import Submission.NK.CFTLib.ArtinReciprocityIdeal.artinSym_restrict_relNorm
import Submission.NK.CFTLib.ArtinReciprocityIdeal.frobAtPrime_prod_relNorm_eq_one
import Submission.NK.CFTLib.ARL.RelNormFI

/-!
# Functoriality of the Artin symbol under relative norms, without the disjointness hypotheses

The theorem `NK.CFTLib.ArtinReciprocityIdeal.artinSym_restrict_relNorm` proves the functoriality
of the Artin symbol under relative norms for intermediate fields `E, L` of a finite Galois
extension `M/K` with `E ⊔ L = ⊤` and `E ⊓ L = ⊥`.  Neither hypothesis is used in the proof: the
argument is prime-by-prime and only needs that `M/↥E` is abelian and `L/K` is Galois.  This file
therefore proves the same statement for arbitrary intermediate fields `E, L`, with the weaker
hypotheses `IsGalois ↥E M` and `IsGalois K ↥L` (in particular `M/K` need not be Galois).

The mathematical content is the compatibility of Frobenius elements with restriction: at a prime
`𝔮` of `𝓞 ↥E`, unramified in `M/↥E` and with `𝔭 = 𝔮 ∩ 𝓞 K` unramified in `L/K`,

  `Frob_𝔮(M/↥E)|_L = Frob_𝔭(L/K) ^ f(𝔮 | 𝔭)`,

and the multiplicativity of the Artin symbol on the group of fractional ideals.

The auxiliary lemmas `galRestrict_restrictNormalHom_relBase` and
`restrictNormalHom_frob_residue_relBase` redo the corresponding lemmas of
`artinSym_restrict_relNorm.lean` with the base field `↥E` (rather than `K`) on the side of the
Frobenius element; the statements in the two files differ only in the hypotheses, and the extra
hypotheses of the earlier file are never used.
-/

namespace NK.CFTLib.ArtinReciprocityIdeal

open NumberField IsDedekindDomain
open scoped NumberField nonZeroDivisors IsMulCommutative

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

section Compat

variable {K M : Type} [Field K] [NumberField K] [Field M] [NumberField M]
  [Algebra K M] [FiniteDimensional K M]

/-- **Compatibility of `galRestrict` with restriction to an intermediate field, over an arbitrary
base.**  Let `K ⊆ E, L ⊆ M` be intermediate fields of a finite extension `M/K`, with `L/K` normal.
For `σ ∈ Gal(M/↥E)` and `x ∈ 𝓞 ↥L`, the element of `𝓞 M` obtained by applying the action of the
restriction `σ|_L` of `σ` to `L` is the one obtained by applying `σ` itself to `x`. -/
lemma galRestrict_restrictNormalHom_relBase (E L : IntermediateField K M)
    [FiniteDimensional K ↥E] [FiniteDimensional K ↥L] [Normal K ↥L]
    (σ : M ≃ₐ[↥E] M) (x : 𝓞 ↥L) :
    algebraMap (𝓞 ↥L) (𝓞 M)
        (galRestrict (𝓞 K) K ↥L (𝓞 ↥L)
          (AlgEquiv.restrictNormalHom (F := K) (K₁ := M) L (σ.restrictScalars K)) x)
      = galRestrict (𝓞 ↥E) ↥E M (𝓞 M) σ (algebraMap (𝓞 ↥L) (𝓞 M) x) := by
  apply IsIntegralClosure.algebraMap_injective (𝓞 M) (𝓞 K) M
  conv_lhs => rw [← IsScalarTower.algebraMap_apply (𝓞 ↥L) (𝓞 M) M,
    IsScalarTower.algebraMap_apply (𝓞 ↥L) ↥L M, algebraMap_galRestrict_apply]
  conv_rhs => rw [algebraMap_galRestrict_apply,
    ← IsScalarTower.algebraMap_apply (𝓞 ↥L) (𝓞 M) M,
    IsScalarTower.algebraMap_apply (𝓞 ↥L) ↥L M]
  rw [show (AlgEquiv.restrictNormalHom (F := K) (K₁ := M) L (σ.restrictScalars K)) =
      (σ.restrictScalars K).restrictNormal ↥L from rfl, AlgEquiv.restrictNormal_commutes]
  rfl

/-- **The residue of the restriction of a Frobenius element, over an arbitrary base.**  Let
`σ ∈ Gal(M/↥E)` be a Frobenius element at a prime `𝔔` of `𝓞 M` over `𝔮`, and let `L/K` be normal.
Then the restriction of `σ` to `L` acts on the residue field at `𝔔 ∩ 𝓞 L` by `x ↦ x ^ N𝔮`. -/
lemma restrictNormalHom_frob_residue_relBase (E L : IntermediateField K M)
    [FiniteDimensional K ↥E] [FiniteDimensional K ↥L] [Normal K ↥L]
    (σ : M ≃ₐ[↥E] M) (𝔮 : NK.Chebotarev.PrimeIdeal ↥E) (𝔔 : NK.Chebotarev.PrimeIdeal M)
    (h𝔔 : 𝔔.asIdeal.LiesOver 𝔮.asIdeal)
    (hfrob : NK.Chebotarev.IsFrobAt 𝔔 σ) (x : 𝓞 ↥L) :
    Ideal.Quotient.mk (𝔔.asIdeal.under (𝓞 ↥L))
        (galRestrict (𝓞 K) K ↥L (𝓞 ↥L)
          (AlgEquiv.restrictNormalHom (F := K) (K₁ := M) L (σ.restrictScalars K)) x)
      = (Ideal.Quotient.mk (𝔔.asIdeal.under (𝓞 ↥L)) x) ^ (Nat.card (𝓞 ↥E ⧸ 𝔮.asIdeal)) := by
  have h1 : galRestrict (𝓞 ↥E) ↥E M (𝓞 M) σ (algebraMap (𝓞 ↥L) (𝓞 M) x)
      - algebraMap (𝓞 ↥L) (𝓞 M) (x ^ Nat.card (𝓞 ↥E ⧸ 𝔮.asIdeal)) ∈ 𝔔.asIdeal := by
    have h := hfrob (algebraMap (𝓞 ↥L) (𝓞 M) x)
    rw [← h𝔔.over] at h
    simpa only [AlgEquiv.coe_toAlgHom, ← map_pow] using h
  rw [← galRestrict_restrictNormalHom_relBase E L σ x] at h1
  rw [← map_sub] at h1
  have hmem := (Ideal.mem_under (𝓞 ↥L) 𝔔.asIdeal).mpr h1
  rw [← map_pow, Ideal.Quotient.eq]
  exact hmem

/-- **The cardinality of the residue field is the inertia-degree-th power of that of the
subfield.**  For a prime `𝔮` of an intermediate field `↥E` of `M/K`,
`N 𝔮 = (N (𝔮 ∩ K)) ^ f(𝔮 | 𝔮 ∩ K)`. -/
lemma natCard_quotient_eq_pow_inertiaDeg_under_relBase (E : IntermediateField K M)
    [FiniteDimensional K ↥E] (𝔮 : NK.Chebotarev.PrimeIdeal ↥E) :
    Nat.card (𝓞 ↥E ⧸ 𝔮.asIdeal)
      = (Nat.card (𝓞 K ⧸ (𝔮.under (𝓞 K)).asIdeal)) ^ (𝔮.asIdeal.inertiaDeg (𝓞 K)) := by
  haveI : 𝔮.asIdeal.LiesOver (𝔮.under (𝓞 K)).asIdeal :=
    ⟨HeightOneSpectrum.under_asIdeal (𝓞 K) 𝔮⟩
  have h := Ideal.absNorm_pow_inertiaDeg (p := (𝔮.under (𝓞 K)).asIdeal) (q := 𝔮.asIdeal)
  simp only [Ideal.absNorm_apply, Submodule.cardQuot_apply] at h
  exact h.symm

end Compat

section Prime

variable {K M : Type} [Field K] [NumberField K] [Field M] [NumberField M]
  [Algebra K M] [FiniteDimensional K M]
  (E L : IntermediateField K M) [FiniteDimensional K ↥E] [FiniteDimensional K ↥L]
  [IsGalois ↥E M] [IsGalois K ↥L]

/-- **The restriction of the Frobenius at `𝔮` to `L`, without disjointness hypotheses.**  Let
`E, L ⊆ M` be intermediate fields of a finite extension `M/K` with `M/↥E` abelian and `L/K`
Galois, and let `𝔮` be a prime of `𝓞 ↥E` unramified in `M/↥E` whose trace `𝔭 = 𝔮 ∩ 𝓞 K` is
unramified in `L/K`.  Then the restriction to `L` of the Frobenius at `𝔮` of `M/↥E` is the
`f(𝔮|𝔭)`-th power of the Frobenius at `𝔭` of `L/K`:

  `Frob_𝔮(M/↥E)|_L = Frob_𝔭(L/K) ^ f(𝔮|𝔭)`.

Indeed, if `𝔔 | 𝔮` is the prime of `M` fixed by `Frob_𝔮` then for `x ∈ 𝓞 L` one has
`Frob_𝔮(M/↥E)|_L x ≡ x^{N𝔮} (mod 𝔔 ∩ 𝓞 L)` while `Frob_𝔭` acts as `x ↦ x^{N𝔭}`, and
`N𝔮 = (N𝔭)^{f(𝔮|𝔭)}`; the Frobenius at an unramified prime is determined by its residue
action. -/
theorem restrict_frobAtPrime_eq_of_normal
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
  have hres : ∀ x : 𝓞 ↥L,
      Ideal.Quotient.mk ℘.asIdeal (galRestrict (𝓞 K) K ↥L (𝓞 ↥L) τ x)
        = (Ideal.Quotient.mk ℘.asIdeal x) ^ (Nat.card (𝓞 ↥E ⧸ 𝔮.asIdeal)) := by
    intro x
    have h := restrictNormalHom_frob_residue_relBase E L σ 𝔮 𝔔 h𝔔 hfrob x
    rwa [← hτdef, ← h℘as] at h
  have hτ₀frob : NK.Chebotarev.IsFrobAt ℘ τ₀ := by
    obtain ⟨℘₀, h℘₀lies, h℘₀frob⟩ :=
      NK.Chebotarev.isFrobAtPrime_frobAtPrime (K := K) (L := ↥L) hcommL
        (𝔮.under (𝓞 K)) hunrL
    rw [hτ₀def]
    exact NK.CFTLib.Arl.isFrobAt_of_isFrobAt_any_primeOver hcommL h℘₀lies h℘lies h℘₀frob
  have hq : Nat.card (𝓞 K ⧸ ℘.asIdeal.under (𝓞 K))
      = Nat.card (𝓞 K ⧸ (𝔮.under (𝓞 K)).asIdeal) := by
    rw [← h℘lies.over]
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
    exact natCard_quotient_eq_pow_inertiaDeg_under_relBase E 𝔮
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
Ch. X §1).

Let `K ⊆ E, L ⊆ M` be intermediate fields of a finite extension `M/K` of number fields with
`M/↥E` abelian and `L/K` Galois (the field `M/K` itself need not be Galois), and let `m` be a
modulus containing every prime ramified in `M/↥E` and every prime ramified in `L/K`.  Then for
every fractional ideal `𝔄` of `E` coprime to `(m)`,

  `ψ_{M/E}(𝔄)|_L = ψ_{L/K}(N_{E/K}(𝔄))`,

i.e. the restriction to `L` of the Artin symbol of `𝔄` in `M/E` is the Artin symbol in `L/K` of
the relative norm of `𝔄`.

The proof is prime-by-prime: for every prime `𝔮` in the support of `𝔄` (so `𝔮` is unramified in
`M/↥E` and `𝔮 ∩ K` unramified in `L/K` by the choice of `m`) the two sides agree on the prime
`𝔮`, by `restrict_frobAtPrime_eq_of_normal`; both sides are multiplicative, and `𝔄` is the
product of its prime factors. -/
theorem artinSym_restrict_relNorm_of_normal {K M : Type} [Field K] [NumberField K] [Field M]
    [NumberField M] [Algebra K M] [FiniteDimensional K M]
    (E L : IntermediateField K M) [FiniteDimensional K ↥E] [FiniteDimensional K ↥L]
    [IsGalois ↥E M] [IsGalois K ↥L]
    (hcommE : ∀ a b : M ≃ₐ[↥E] M, a * b = b * a)
    (hcommL : ∀ a b : (↥L ≃ₐ[K] ↥L), a * b = b * a)
    (m : ℕ)
    (hramE : ∀ 𝔮 : NK.Chebotarev.PrimeIdeal ↥E,
      ¬ NK.CFTLib.ArtinReciprocityIdeal.IsUnramified (K := ↥E) (L := M) 𝔮 →
      (m : NumberField.RingOfIntegers ↥E) ∈ 𝔮.asIdeal)
    (hram : ∀ p : NK.Chebotarev.PrimeIdeal K,
      ¬ NK.CFTLib.ArtinReciprocityIdeal.IsUnramified (K := K) (L := ↥L) p →
      (m : NumberField.RingOfIntegers K) ∈ p.asIdeal)
    (𝔄 : (FractionalIdeal (nonZeroDivisors (NumberField.RingOfIntegers ↥E)) ↥E)ˣ)
    (hcop : NK.CFTLib.ArtinReciprocityIdeal.FracCoprime (K := ↥E) m 𝔄) :
    AlgEquiv.restrictNormalHom (F := K) (K₁ := M) L
        ((NK.CFTLib.Arl.artinSym (K := ↥E) (L := M) hcommE
            (𝔄 : FractionalIdeal (nonZeroDivisors (NumberField.RingOfIntegers ↥E)) ↥E)).restrictScalars K)
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
      exact restrict_frobAtPrime_eq_of_normal E L hcommE hcommL 𝔮 hunrE hunrL
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
