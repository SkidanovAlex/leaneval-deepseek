import Mathlib
import Submission.Work.SSGRoute.ZDataMup.NKArtinUmbrella
import Submission.NK.CFTLib.Existence.artinKernel
import Submission.NK.NUV2.ARL.normAdjustment
import Submission.Work.SSGRoute.NKExistenceImport
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute.ZDataMup

set_option linter.style.haveILetI false
set_option linter.unusedVariables false

open scoped NumberField
open NumberField IsDedekindDomain

/-- **The idèlic Artin map of a congruence datum is a monoid homomorphism with the standard
properties.**

For a finite abelian extension `L/K` of number fields, a modulus `m > 0` whose primes `∤ (m)` are
unramified in `L`, the ideal-theoretic reciprocity law at `m`, a congruence subgroup `U` of modulus
`m` with an adjustment `𝕀 K = U · Kˣ`: the function `ideleArtin` is multiplicative, kills the
principal idèles, kills the idèlic norms `N_{L/K} 𝕀 L`, is surjective, and takes the value
`Frob_𝔭` at the idèle of a prime `𝔭 ∤ (m)`. -/
theorem exists_ideleHom_ideleArtin_of_congruence_data
    {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (hcomm : ∀ a b : Gal(L/K), a * b = b * a)
    (m : ℕ) (hm : 0 < m)
    (hram : ∀ p : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K),
      (m : NumberField.RingOfIntegers K) ∉ p.asIdeal →
      Ideal.ramificationIdxIn p.asIdeal (NumberField.RingOfIntegers L) = 1)
    (hprinc : NK.CFTLib.artinKillsPrincipal K L m)
    (U : Subgroup (NK.GlobalCFT.Idele K))
    (hU : NK.CFTLib.Arl.IsCongruenceSubgroup (K := K) m U)
    (hadj : ∀ x : NK.GlobalCFT.Idele K, ∃ b : Kˣ,
      x * NK.GlobalCFT.Idele.principalIdele K b ∈ U) :
    ∃ art : NK.GlobalCFT.Idele K →* Gal(L/K),
      (∀ x : NK.GlobalCFT.Idele K, art x = NK.CFTLib.Arl.ideleArtin hcomm U hadj x) ∧
      (∀ a : Kˣ, art (NK.GlobalCFT.Idele.principalIdele K a) = 1) ∧
      (∀ y : NK.GlobalCFT.Idele L, art (NK.GlobalCFT.Idele.normIdeleHom K L y) = 1) ∧
      Function.Surjective art ∧
      (∀ 𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K),
        (m : NumberField.RingOfIntegers K) ∉ 𝔭.asIdeal →
        art (NK.HeckeL.ideleOfPrime K 𝔭) = NK.Chebotarev.frobAtPrime (K := K) (L := L) 𝔭) := by
  obtain ⟨art, hart, hprincipal, hfrob, hsurj⟩ :=
    NK.CFTLib.Arl.exists_monoidHom_ideleArtin (K := K) (L := L) hcomm m hm hram hprinc U hU hadj
  have hnorm : ∀ y : NK.GlobalCFT.Idele L, art (NK.GlobalCFT.Idele.normIdeleHom K L y) = 1 := by
    intro y
    rw [hart (NK.GlobalCFT.Idele.normIdeleHom K L y)]
    exact NK.CFTLib.Arl.normIdeles_mem_ker_of_ideleArtin (K := K) (L := L) hcomm m hm hram hprinc
      U hU hadj (fun y' => NK.NUV2.ARL.normAdjustment (K := K) (L := L) m hm
        (fun p hp => hram p hp) U hU y') y
  exact ⟨art, hart, hprincipal, hnorm, hsurj, hfrob⟩

/-- **Two idèlic Artin maps with the same Frobenius values are equal.**

If `art₁`, `art₂ : 𝕀 K →* Gal(L/K)` are monoid homomorphisms which both kill the principal idèles
and the idèlic norms, are surjective, and agree with the Frobenius elements at all primes `𝔭 ∉ T`
of a finite set `T` (whose complement is unramified in `L`), then `art₁ = art₂`.

Mathematically: both factor through the reciprocity isomorphism
`C_K ⧸ N_{L/K} C_L ≃* Gal(L/K)`, and an endomorphism of `Gal(L/K)` fixing all Frobenius elements
outside `T` is the identity because those generate `Gal(L/K)` (Čebotarev). -/
theorem ideleHom_eq_of_frobAtPrime_of_notMem
    {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (hcomm : ∀ a b : Gal(L/K), a * b = b * a)
    (T : Finset (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)))
    (hunr : ∀ 𝔭, 𝔭 ∉ T →
      Ideal.ramificationIdxIn 𝔭.asIdeal (NumberField.RingOfIntegers L) = 1)
    (art₁ art₂ : NK.GlobalCFT.Idele K →* Gal(L/K))
    (hP₁ : ∀ a : Kˣ, art₁ (NK.GlobalCFT.Idele.principalIdele K a) = 1)
    (hN₁ : ∀ y : NK.GlobalCFT.Idele L, art₁ (NK.GlobalCFT.Idele.normIdeleHom K L y) = 1)
    (hS₁ : Function.Surjective art₁)
    (hF₁ : ∀ 𝔭, 𝔭 ∉ T → art₁ (NK.HeckeL.ideleOfPrime K 𝔭)
        = NK.Chebotarev.frobAtPrime (K := K) (L := L) 𝔭)
    (hP₂ : ∀ a : Kˣ, art₂ (NK.GlobalCFT.Idele.principalIdele K a) = 1)
    (hN₂ : ∀ y : NK.GlobalCFT.Idele L, art₂ (NK.GlobalCFT.Idele.normIdeleHom K L y) = 1)
    (hS₂ : Function.Surjective art₂)
    (hF₂ : ∀ 𝔭, 𝔭 ∉ T → art₂ (NK.HeckeL.ideleOfPrime K 𝔭)
        = NK.Chebotarev.frobAtPrime (K := K) (L := L) 𝔭) :
    art₁ = art₂ := by
  classical
  haveI : IsMulCommutative (L ≃ₐ[K] L) := IsMulCommutative.of_comm hcomm
  have hker₁ : NK.GlobalCFT.Idele.principalSubgroup K ≤ art₁.ker := by
    intro x hx
    obtain ⟨a, rfl⟩ := NK.GlobalCFT.Idele.mem_principalSubgroup.mp hx
    exact MonoidHom.mem_ker.mpr (hP₁ a)
  have hker₂ : NK.GlobalCFT.Idele.principalSubgroup K ≤ art₂.ker := by
    intro x hx
    obtain ⟨a, rfl⟩ := NK.GlobalCFT.Idele.mem_principalSubgroup.mp hx
    exact MonoidHom.mem_ker.mpr (hP₂ a)
  obtain ⟨e₁, he₁⟩ := NK.CFTLib.Existence.exists_artinIso_of_ideleArtin (K := K) (L := L)
    NK.CFTLib.fundamentalClassElement art₁ hker₁ hN₁ hS₁
  obtain ⟨e₂, he₂⟩ := NK.CFTLib.Existence.exists_artinIso_of_ideleArtin (K := K) (L := L)
    NK.CFTLib.fundamentalClassElement art₂ hker₂ hN₂ hS₂
  -- the idèle class group modulo the norm subgroup
  let Q := NK.GlobalCFT.IdeleClassGroup K ⧸ NK.GlobalCFT.Idele.normClassSubgroup K L
  let c : NK.GlobalCFT.Idele K → Q := fun x =>
    QuotientGroup.mk' (NK.GlobalCFT.Idele.normClassSubgroup K L)
      (NK.GlobalCFT.IdeleClassGroup.mk K x)
  -- the image of the prime idèles generates `Q`
  let S : Set Q := {q | ∃ 𝔭 : NK.Chebotarev.PrimeIdeal K, 𝔭 ∉ T ∧
    q = c (NK.HeckeL.ideleOfPrime K 𝔭)}
  have hgen : Subgroup.closure S = ⊤ := by
    have hmap : Subgroup.map (e₂ : Q →* Gal(L/K)) (Subgroup.closure S) = ⊤ := by
      rw [MonoidHom.map_closure]
      refine NK.CFTLib.Arl.eq_top_of_forall_isFrobAtPrime_of_notMem (K := K) (L := L) T _ ?_
      intro p hpT σ hσ
      have hunr' : ∀ P : NK.Chebotarev.PrimeIdeal L, P.asIdeal.LiesOver p.asIdeal →
          P.asIdeal.ramificationIdx (NumberField.RingOfIntegers K) = 1 := by
        intro P hP
        rw [← Ideal.ramificationIdxIn_eq_ramificationIdx (A := NumberField.RingOfIntegers K)
          (B := NumberField.RingOfIntegers L) p.asIdeal P.asIdeal (Gal(L/K))]
        exact hunr p hpT
      have hfrob : NK.Chebotarev.frobAtPrime (K := K) (L := L) p = σ :=
        (NK.Chebotarev.isFrobAtPrime_iff_frobAtPrime_eq (K := K) (L := L) hcomm p
          hunr' σ).mp hσ
      rw [← hfrob]
      refine Subgroup.subset_closure ⟨c (NK.HeckeL.ideleOfPrime K p), ⟨p, hpT, rfl⟩, ?_⟩
      exact (he₂ (NK.HeckeL.ideleOfPrime K p)).trans (hF₂ p hpT)
    rw [Subgroup.eq_top_iff']
    intro q
    obtain ⟨h, hh, hhq⟩ := Subgroup.mem_map.mp (by rw [hmap]; exact Subgroup.mem_top (e₂ q))
    have hhq' : h = q := e₂.injective hhq
    rw [← hhq']
    exact hh
  -- hence `e₁ = e₂`
  have heqOn : Set.EqOn (⇑e₁) (⇑e₂) (Subgroup.closure S : Set Q) :=
    MonoidHom.eqOn_closure (f := (e₁ : Q →* Gal(L/K))) (g := (e₂ : Q →* Gal(L/K))) (s := S)
      (fun x hx => by
        obtain ⟨𝔭, h𝔭T, rfl⟩ := hx
        dsimp only [c]
        exact ((he₁ (NK.HeckeL.ideleOfPrime K 𝔭)).trans (hF₁ 𝔭 h𝔭T)).trans
          (((he₂ (NK.HeckeL.ideleOfPrime K 𝔭)).trans (hF₂ 𝔭 h𝔭T)).symm))
  have heq : ∀ q : Q, e₁ q = e₂ q := by
    intro q
    exact heqOn (by rw [hgen]; exact Subgroup.mem_top q)
  refine MonoidHom.ext (fun x => ?_)
  rw [← he₁ x, ← he₂ x]
  exact heq (c x)

theorem ideleArtin_independent_of_congruence_data
    {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (hcomm : ∀ a b : Gal(L/K), a * b = b * a)
    (m₁ : ℕ) (hm₁ : 0 < m₁)
    (hram₁ : ∀ p : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K),
      (m₁ : NumberField.RingOfIntegers K) ∉ p.asIdeal →
      Ideal.ramificationIdxIn p.asIdeal (NumberField.RingOfIntegers L) = 1)
    (hprinc₁ : NK.CFTLib.artinKillsPrincipal K L m₁)
    (U₁ : Subgroup (NK.GlobalCFT.Idele K))
    (hU₁ : NK.CFTLib.Arl.IsCongruenceSubgroup (K := K) m₁ U₁)
    (hadj₁ : ∀ x : NK.GlobalCFT.Idele K, ∃ b : Kˣ,
      x * NK.GlobalCFT.Idele.principalIdele K b ∈ U₁)
    (m₂ : ℕ) (hm₂ : 0 < m₂)
    (hram₂ : ∀ p : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K),
      (m₂ : NumberField.RingOfIntegers K) ∉ p.asIdeal →
      Ideal.ramificationIdxIn p.asIdeal (NumberField.RingOfIntegers L) = 1)
    (hprinc₂ : NK.CFTLib.artinKillsPrincipal K L m₂)
    (U₂ : Subgroup (NK.GlobalCFT.Idele K))
    (hU₂ : NK.CFTLib.Arl.IsCongruenceSubgroup (K := K) m₂ U₂)
    (hadj₂ : ∀ x : NK.GlobalCFT.Idele K, ∃ b : Kˣ,
      x * NK.GlobalCFT.Idele.principalIdele K b ∈ U₂) :
    ∀ x : NK.GlobalCFT.Idele K,
      NK.CFTLib.Arl.ideleArtin hcomm U₁ hadj₁ x
        = NK.CFTLib.Arl.ideleArtin hcomm U₂ hadj₂ x := by
  classical
  obtain ⟨art₁, hA₁, hP₁, hN₁, hS₁, hF₁⟩ :=
    exists_ideleHom_ideleArtin_of_congruence_data (K := K) (L := L) hcomm m₁ hm₁ hram₁ hprinc₁
      U₁ hU₁ hadj₁
  obtain ⟨art₂, hA₂, hP₂, hN₂, hS₂, hF₂⟩ :=
    exists_ideleHom_ideleArtin_of_congruence_data (K := K) (L := L) hcomm m₂ hm₂ hram₂ hprinc₂
      U₂ hU₂ hadj₂
  -- the finitely many primes dividing `m₁ m₂`
  set T : Finset (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) :=
    NK.CFTLib.Arl.primesDividing (K := K) m₁ hm₁ ∪ NK.CFTLib.Arl.primesDividing (K := K) m₂ hm₂
    with hTdef
  have hnotMem₁ : ∀ 𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K),
      𝔭 ∉ T → (m₁ : NumberField.RingOfIntegers K) ∉ 𝔭.asIdeal := by
    intro 𝔭 h𝔭
    rw [hTdef, Finset.mem_union, not_or] at h𝔭
    exact fun h => h𝔭.1 ((NK.CFTLib.Arl.mem_primesDividing (K := K) m₁ hm₁ 𝔭).mpr h)
  have hnotMem₂ : ∀ 𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K),
      𝔭 ∉ T → (m₂ : NumberField.RingOfIntegers K) ∉ 𝔭.asIdeal := by
    intro 𝔭 h𝔭
    rw [hTdef, Finset.mem_union, not_or] at h𝔭
    exact fun h => h𝔭.2 ((NK.CFTLib.Arl.mem_primesDividing (K := K) m₂ hm₂ 𝔭).mpr h)
  have hunr : ∀ 𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K),
      𝔭 ∉ T → Ideal.ramificationIdxIn 𝔭.asIdeal (NumberField.RingOfIntegers L) = 1 :=
    fun 𝔭 h𝔭 => hram₁ 𝔭 (hnotMem₁ 𝔭 h𝔭)
  have hhom := ideleHom_eq_of_frobAtPrime_of_notMem (K := K) (L := L) hcomm T hunr art₁ art₂
    hP₁ hN₁ hS₁ (fun 𝔭 h𝔭 => hF₁ 𝔭 (hnotMem₁ 𝔭 h𝔭))
    hP₂ hN₂ hS₂ (fun 𝔭 h𝔭 => hF₂ 𝔭 (hnotMem₂ 𝔭 h𝔭))
  intro x
  exact (hA₁ x).symm.trans ((DFunLike.congr_fun hhom x).trans (hA₂ x))

end Work.SSGRoute.ZDataMup
