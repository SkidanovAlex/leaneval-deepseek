import Mathlib.RingTheory.Ideal.Norm.RelNorm
import Submission.NK.CFTLib.ARL.RelNormFI
import Submission.NK.CFTLib.ArtinReciprocityIdeal.mem_idealCoprimeGroup_iff
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

open NumberField IsDedekindDomain
open scoped NumberField nonZeroDivisors

noncomputable section

namespace NK.Existence.ArtinLemma

open NK.CFTLib.ArtinReciprocityIdeal

/-- `(a ^ e) ^ n = (a ^ n) ^ e` for a group element `a`, `e : ℤ` and `n : ℕ`. -/
lemma zpow_pow_comm {G : Type*} [Group G] (a : G) (e : ℤ) (n : ℕ) :
    (a ^ e) ^ n = (a ^ n) ^ e := by
  rw [← zpow_natCast (a ^ e) n, ← zpow_natCast a n]
  rw [show (a ^ e) ^ (n : ℤ) = a ^ (e * (n : ℤ)) from (zpow_mul a e _).symm]
  rw [show (a ^ (n : ℤ)) ^ e = a ^ ((n : ℤ) * e) from (zpow_mul a _ e).symm]
  rw [mul_comm]

/-- **A fractional ideal is the product of its prime factors.**  For a nonzero fractional ideal
`A` of `K` and a finite set `s` of primes containing the support of `A`,
`A = ∏_{𝔭 ∈ s} 𝔭 ^ (count 𝔭 A)`. -/
lemma Frac_eq_prod_primeUnit {K : Type} [Field K] [NumberField K] (A : Frac K)
    (s : Finset (IsDedekindDomain.HeightOneSpectrum (𝓞 K)))
    (hs : ∀ 𝔭 : IsDedekindDomain.HeightOneSpectrum (𝓞 K),
      FractionalIdeal.count K 𝔭 (A : FractionalIdeal (𝓞 K)⁰ K) ≠ 0 → 𝔭 ∈ s) :
    A = ∏ 𝔭 ∈ s, (NK.CFTLib.ARL.primeUnit (L := K) 𝔭) ^
      (FractionalIdeal.count K 𝔭 (A : FractionalIdeal (𝓞 K)⁰ K)) := by
  classical
  have h1 : (A : FractionalIdeal (𝓞 K)⁰ K) =
      ∏ᶠ 𝔭 : IsDedekindDomain.HeightOneSpectrum (𝓞 K),
        ((𝔭.asIdeal : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K) ^
          (FractionalIdeal.count K 𝔭 (A : FractionalIdeal (𝓞 K)⁰ K)) :=
    (FractionalIdeal.finprod_heightOneSpectrum_factorization' (K := K) A.ne_zero).symm
  apply Units.ext
  rw [Units.coe_prod]
  simp only [NK.CFTLib.ARL.primeUnit_val, Units.val_zpow_eq_zpow_val]
  conv_lhs => rw [h1]
  exact finprod_eq_finsetProd_of_mulSupport_subset _ (fun 𝔭 h𝔭 => by
    by_contra hmem
    rw [Function.mem_mulSupport] at h𝔭
    have h0 : FractionalIdeal.count K 𝔭 (A : FractionalIdeal (𝓞 K)⁰ K) = 0 := by
      by_contra hne
      exact hmem (hs 𝔭 hne)
    exact h𝔭 (by rw [h0, zpow_zero]))

/-- **The `[L:K]`-th power of a fractional ideal coprime to `(m)` lies in the norm ray.**  It is
the relative norm of the base change `A·𝒪_L` of `A` to `L`
(`Ideal.relNorm_algebraMap`), which is integral and coprime to `(m)`. -/
theorem pow_finrank_mem_normRay {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] (m : ℕ) {A : Frac K} (hA : FracCoprime m A) :
    A ^ Module.finrank K L ∈ normRay K L m := by
  classical
  set s : Finset (IsDedekindDomain.HeightOneSpectrum (𝓞 K)) :=
    (Filter.eventually_cofinite.mp (FractionalIdeal.finite_factors (K := K)
      (A : FractionalIdeal (𝓞 K)⁰ K))).toFinset with hs
  have hsmem : ∀ 𝔭 : IsDedekindDomain.HeightOneSpectrum (𝓞 K),
      𝔭 ∈ s ↔ FractionalIdeal.count K 𝔭 (A : FractionalIdeal (𝓞 K)⁰ K) ≠ 0 :=
    fun 𝔭 => Set.Finite.mem_toFinset _
  have hfac : A = ∏ 𝔭 ∈ s, (NK.CFTLib.ARL.primeUnit (L := K) 𝔭) ^
      (FractionalIdeal.count K 𝔭 (A : FractionalIdeal (𝓞 K)⁰ K)) :=
    Frac_eq_prod_primeUnit A s (fun 𝔭 h => (hsmem 𝔭).mpr h)
  have hprime : ∀ 𝔭 ∈ s, (NK.CFTLib.ARL.primeUnit (L := K) 𝔭) ^ (Module.finrank K L)
      ∈ normRay K L m := by
    intro 𝔭 h𝔭
    have hcount : FractionalIdeal.count K 𝔭 (A : FractionalIdeal (𝓞 K)⁰ K) ≠ 0 :=
      (hsmem 𝔭).mp h𝔭
    have hpm : (m : 𝓞 K) ∉ 𝔭.asIdeal := fun hm => hcount (hA 𝔭 hm)
    set I : Ideal (𝓞 L) := Ideal.map (algebraMap (𝓞 K) (𝓞 L)) 𝔭.asIdeal with hI
    have hIne : I ≠ ⊥ := by
      rw [hI, Ne, Ideal.map_eq_bot_iff_of_injective
        (FaithfulSMul.algebraMap_injective (𝓞 K) (𝓞 L))]
      exact 𝔭.ne_bot
    have hrel : Ideal.relNorm (𝓞 K) I = 𝔭.asIdeal ^ Module.finrank K L := by
      rw [hI, Ideal.relNorm_algebraMap,
        show Module.finrank (𝓞 K) (𝓞 L) = Module.finrank K L from
          (IsFractionRing.finrank_eq (𝓞 K) K (𝓞 L) L).symm]
    have hcop : FracCoprime (K := L) m (idealUnit I hIne) := by
      intro 𝔮 h𝔮
      have hnotdvd : ¬ 𝔮.asIdeal ∣ I := by
        intro hdvd
        have hle : 𝔭.asIdeal ≤ 𝔮.asIdeal.under (𝓞 K) :=
          Ideal.map_le_iff_le_comap.mp (hI ▸ Ideal.dvd_iff_le.mp hdvd)
        have hne : 𝔮.asIdeal.under (𝓞 K) ≠ ⊤ := by
          intro htop
          have hone : (1 : 𝓞 L) ∈ 𝔮.asIdeal := by
            have h1 : (1 : 𝓞 K) ∈ 𝔮.asIdeal.under (𝓞 K) := htop ▸ Submodule.mem_top
            simpa using (Ideal.mem_under (𝓞 K) 𝔮.asIdeal).mp h1
          exact 𝔮.isPrime.ne_top (Ideal.eq_top_iff_one 𝔮.asIdeal |>.mpr hone)
        haveI : 𝔭.asIdeal.IsMaximal := Ideal.IsPrime.isMaximal 𝔭.isPrime 𝔭.ne_bot
        have heq : 𝔮.asIdeal.under (𝓞 K) = 𝔭.asIdeal :=
          (Ideal.IsMaximal.eq_of_le ‹𝔭.asIdeal.IsMaximal› hne hle).symm
        exact hpm (heq ▸ (Ideal.mem_under (𝓞 K) 𝔮.asIdeal).mpr (by simpa using h𝔮))
      have hc0 : (Associates.mk 𝔮.asIdeal).count (Associates.mk I).factors = 0 := by
        by_contra h
        exact hnotdvd
          ((Associates.count_ne_zero_iff_dvd (a := I) hIne 𝔮.irreducible).mp h)
      show FractionalIdeal.count L 𝔮
        (idealUnit (K := L) I hIne : FractionalIdeal (𝓞 L)⁰ L) = 0
      rw [show (idealUnit (K := L) I hIne : FractionalIdeal (𝓞 L)⁰ L)
          = (I : FractionalIdeal (𝓞 L)⁰ L) from rfl,
        FractionalIdeal.count_coe L 𝔮 hIne]
      simp [hc0]
    have hmem : idealUnit (K := K) (Ideal.relNorm (𝓞 K) I)
        (fun h => hIne ((Ideal.relNorm_eq_bot_iff).mp h)) ∈ normRay K L m :=
      Subgroup.subset_closure ⟨I, hIne, hcop, rfl⟩
    have hkey : idealUnit (K := K) (Ideal.relNorm (𝓞 K) I)
        (fun h => hIne ((Ideal.relNorm_eq_bot_iff).mp h))
        = (NK.CFTLib.ARL.primeUnit (L := K) 𝔭) ^ (Module.finrank K L) := by
      apply Units.ext
      show (((Ideal.relNorm (𝓞 K) I : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K))
        = (((𝔭.asIdeal : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K)) ^ (Module.finrank K L)
      rw [hrel, FractionalIdeal.coeIdeal_pow]
    rwa [hkey] at hmem
  rw [hfac]
  have hzpow : (∏ 𝔭 ∈ s, (NK.CFTLib.ARL.primeUnit (L := K) 𝔭) ^
        (FractionalIdeal.count K 𝔭 (A : FractionalIdeal (𝓞 K)⁰ K))) ^ (Module.finrank K L)
      = ∏ 𝔭 ∈ s, ((NK.CFTLib.ARL.primeUnit (L := K) 𝔭) ^ (Module.finrank K L)) ^
          (FractionalIdeal.count K 𝔭 (A : FractionalIdeal (𝓞 K)⁰ K)) := by
    rw [← Finset.prod_pow]
    exact Finset.prod_congr rfl fun 𝔭 _ =>
      zpow_pow_comm (NK.CFTLib.ARL.primeUnit (L := K) 𝔭)
        (FractionalIdeal.count K 𝔭 (A : FractionalIdeal (𝓞 K)⁰ K)) (Module.finrank K L)
  rw [hzpow]
  exact Subgroup.prod_mem _ fun 𝔭 h𝔭 => Subgroup.zpow_mem _ (hprime 𝔭 h𝔭) _

end NK.Existence.ArtinLemma
