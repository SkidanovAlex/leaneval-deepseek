import Mathlib
import Submission.Work.SSGRoute.ZDataMup.NKArtinUmbrella
import Submission.NK.CFTLib.Existence.artinKernel
import Submission.NK.CFTLib.fundamentalClassElement
import Submission.Work.SSGRoute.ZDataMup.ZDataMupClean.CyclicCase
import Submission.Work.SSGRoute.ZDataMup.abelian_of_cyclicCase
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

open scoped NumberField RestrictedProduct
open NumberField IsDedekindDomain

noncomputable section

namespace Work.SSGRoute.ZDataMup

open NK.GlobalCFT

/-- **The idèlic Artin map of the reciprocity law, with its kernel.**

Given the ideal-theoretic reciprocity law at the modulus `m` (`hprinc`), a congruence subgroup `U`
of modulus `m` and an adjustment `𝕀 K = U · Kˣ`, the map `x ↦ artinSym (idealOf (x · bₓ))` is a
surjective homomorphism killing the principal idèles and the idèlic norms, Frobenius-normalised at
the primes `𝔭 ∤ (m)`, and its kernel is exactly `N_{L/K} 𝕀_L · Kˣ`.

This is the assembly of `NK.CFTLib.Arl.exists_monoidHom_ideleArtin` with the identification of the
kernel of the associated map `C_K →* Gal(L/K)` with the norm class subgroup
(`NK.CFTLib.Existence.ker_artinMapCK_eq_normClassSubgroup`), as in the cyclic case in
`Work.SSGRoute.ZDataMup.localGlobalArtinMap_killing_principalIdele`. -/
theorem exists_ideleArtinMap_with_kernel
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
      (∀ x, art x = NK.CFTLib.Arl.ideleArtin hcomm U hadj x) ∧
      art.ker = NK.GlobalCFT.Idele.normImage K L ⊔ NK.GlobalCFT.Idele.principalSubgroup K ∧
      (∀ a : Kˣ, art (NK.GlobalCFT.Idele.principalIdele K a) = 1) ∧
      (∀ 𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K),
        (m : NumberField.RingOfIntegers K) ∉ 𝔭.asIdeal →
        art (NK.HeckeL.ideleOfPrime K 𝔭) = NK.Chebotarev.frobAtPrime (K := K) (L := L) 𝔭) ∧
      Function.Surjective art := by
  classical
  haveI : IsMulCommutative (L ≃ₐ[K] L) := IsMulCommutative.of_comm hcomm
  obtain ⟨art, hagree, hprincipal, hgood, hsurj⟩ :=
    NK.CFTLib.Arl.exists_monoidHom_ideleArtin (K := K) (L := L) hcomm m hm hram hprinc U hU hadj
  have hUeq : U = NK.CFTLib.Arl.congruenceSubgroup K m :=
    SetLike.ext fun x => (hU.1 x).trans Iff.rfl
  have hnorm : ∀ y : NK.GlobalCFT.Idele L, art (NK.GlobalCFT.Idele.normIdeleHom K L y) = 1 := by
    intro y
    rw [hagree]
    refine NK.CFTLib.Arl.normIdeles_mem_ker_of_ideleArtin (K := K) (L := L) hcomm m hm hram hprinc
      U hU hadj ?_ y
    intro z
    obtain ⟨d, hd⟩ := NK.CFTLib.Arl.exists_norm_mul_mem_congruenceSubgroup K L m hm z
    exact ⟨d, hUeq ▸ hd⟩
  have hker : art.ker = NK.GlobalCFT.Idele.normImage K L
      ⊔ NK.GlobalCFT.Idele.principalSubgroup K := by
    have hPle : NK.GlobalCFT.Idele.principalSubgroup K ≤ art.ker := by
      intro x hx
      obtain ⟨a, rfl⟩ := NK.GlobalCFT.Idele.mem_principalSubgroup.mp hx
      exact MonoidHom.mem_ker.mpr (hprincipal a)
    have hFC := NK.CFTLib.fundamentalClassElement
    have h1 := NK.CFTLib.Existence.ker_artinMapCK_eq_normClassSubgroup (K := K) (L := L)
      hFC art hPle hnorm hsurj
    refine le_antisymm ?_ ?_
    · intro x hx
      have hmk : IdeleClassGroup.mk K x ∈ (NK.CFTLib.Existence.artinMapCK art hPle).ker := by
        rw [MonoidHom.mem_ker, NK.CFTLib.Existence.artinMapCK_mk]
        exact MonoidHom.mem_ker.mp hx
      rw [h1] at hmk
      obtain ⟨n, hn, hmn⟩ := Subgroup.mem_map.mp hmk
      have h2 : n⁻¹ * x ∈ NK.GlobalCFT.Idele.principalSubgroup K :=
        (IdeleClassGroup.mk_eq_mk_iff).mp hmn
      have h3 : n * (n⁻¹ * x) ∈ NK.GlobalCFT.Idele.normImage K L
          ⊔ NK.GlobalCFT.Idele.principalSubgroup K := Subgroup.mul_mem_sup hn h2
      rwa [mul_inv_cancel_left] at h3
    · refine sup_le ?_ hPle
      intro x hx
      obtain ⟨y, hy⟩ := NK.GlobalCFT.Idele.mem_normImage.mp hx
      rw [MonoidHom.mem_ker,
        show x = NK.GlobalCFT.Idele.normIdeleHom K L y from
          NK.GlobalCFT.Idele.ext (fun v => by rw [NK.GlobalCFT.Idele.normIdeleHom_apply]; exact hy v)]
      exact hnorm y
  exact ⟨art, hagree, hker, hprincipal, hgood, hsurj⟩

theorem ideleArtin_ideleOfPrime_of_unramified
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
      x * NK.GlobalCFT.Idele.principalIdele K b ∈ U)
    {Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)}
    (hunr : NK.HeckeL.IsUnramifiedIn (K := K) (L := L) Q) :
    NK.CFTLib.Arl.ideleArtin hcomm U hadj (NK.HeckeL.ideleOfPrime K Q)
      = NK.Chebotarev.frobAtPrime (K := K) (L := L) Q := by
  classical
  set b : Kˣ := NK.CFTLib.Arl.adjust U hadj (NK.HeckeL.ideleOfPrime K Q) with hbdef
  have hspec : NK.HeckeL.ideleOfPrime K Q * NK.GlobalCFT.Idele.principalIdele K b ∈ U :=
    NK.CFTLib.Arl.adjust_spec U hadj _
  -- the congruence datum, read off from `hU`
  have hcongU := (hU.1 (NK.HeckeL.ideleOfPrime K Q * NK.GlobalCFT.Idele.principalIdele K b)).mp hspec
  -- `Q` itself is unramified
  have hQunrIn : Ideal.ramificationIdxIn Q.asIdeal (NumberField.RingOfIntegers L) = 1 := by
    obtain ⟨P, hP⟩ := NK.Chebotarev.exists_primeIdeal_liesOver (K := K) (L := L) Q
    rw [Ideal.ramificationIdxIn_eq_ramificationIdx (A := NumberField.RingOfIntegers K)
      (B := NumberField.RingOfIntegers L) Q.asIdeal P.asIdeal (Gal(L/K))]
    exact hunr P hP
  -- the component of the adjusted prime idèle at a place `𝔮 ≠ Q`
  have hcomp : ∀ 𝔮 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K), 𝔮 ≠ Q →
      (NK.HeckeL.ideleOfPrime K Q * NK.GlobalCFT.Idele.principalIdele K b)
          (NK.GlobalCFT.Place.ofFinite 𝔮)
        = Units.map (algebraMap K (𝔮.adicCompletion K)).toMonoidHom b := by
    intro 𝔮 h𝔮
    rw [NK.GlobalCFT.Idele.mul_apply, NK.CFTLib.IdeleHasse.ideleOfPrime_apply_ofFinite_ne_exists h𝔮,
      one_mul, NK.GlobalCFT.Idele.principalIdele_apply]
    rfl
  -- the component at an infinite place
  have hcompInf : ∀ w : InfinitePlace K,
      (NK.HeckeL.ideleOfPrime K Q * NK.GlobalCFT.Idele.principalIdele K b)
          (NK.GlobalCFT.Place.ofInfinite w)
        = Units.map (algebraMap K w.Completion).toMonoidHom b := by
    intro w
    rw [NK.GlobalCFT.Idele.mul_apply, NK.CFTLib.IdeleHasse.ideleOfPrime_apply_ofInfinite, one_mul,
      NK.GlobalCFT.Idele.principalIdele_apply]
    rfl
  -- the coerced value of the component, as a ring element
  have hcoe : ∀ 𝔮 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K), 𝔮 ≠ Q →
      (↑((NK.HeckeL.ideleOfPrime K Q * NK.GlobalCFT.Idele.principalIdele K b)
          (NK.GlobalCFT.Place.ofFinite 𝔮)) : 𝔮.adicCompletion K)
        = algebraMap K (𝔮.adicCompletion K) ((b : Kˣ) : K) := by
    intro 𝔮 h𝔮
    rw [hcomp 𝔮 h𝔮, Units.coe_map]; rfl
  have hcoeInf : ∀ w : InfinitePlace K,
      (↑((NK.HeckeL.ideleOfPrime K Q * NK.GlobalCFT.Idele.principalIdele K b)
          (NK.GlobalCFT.Place.ofInfinite w)) : w.Completion)
        = algebraMap K w.Completion ((b : Kˣ) : K) := by
    intro w
    rw [hcompInf w, Units.coe_map]; rfl
  -- the congruence and positivity conditions of the conductor drop
  have hcong : ∀ 𝔮 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K),
      (m : NumberField.RingOfIntegers K) ∈ 𝔮.asIdeal →
      Ideal.ramificationIdxIn 𝔮.asIdeal (NumberField.RingOfIntegers L) ≠ 1 →
      Valued.v (algebraMap K (𝔮.adicCompletion K) ((b : Kˣ) : K) - 1)
        ≤ Valued.v ((m : ℕ) : 𝔮.adicCompletion K) := by
    intro 𝔮 h𝔮 hram𝔮
    have h𝔮Q : 𝔮 ≠ Q := by
      intro h; subst h; exact hram𝔮 hQunrIn
    have hval := (hcongU.1 𝔮 h𝔮)
    rw [hcoe 𝔮 h𝔮Q] at hval
    exact hval
  have hpos : ∀ (w : InfinitePlace K) (hw : w.IsReal),
      0 < (InfinitePlace.Completion.ringEquivRealOfIsReal hw)
            (algebraMap K w.Completion ((b : Kˣ) : K)) := by
    intro w hw
    have hval := (hcongU.2 w) hw
    rw [hcoeInf w] at hval
    exact hval
  -- the conductor drop at the ramified primes, in the form of the cyclic case
  have hb1 : NK.CFTLib.Arl.artinSym (K := K) (L := L) hcomm
      (FractionalIdeal.spanSingleton (nonZeroDivisors (NumberField.RingOfIntegers K))
        ((b : Kˣ) : K)) = 1 :=
    abelian_of_cyclicCase
      (Work.SSGRoute.ZDataMup.ArtinReciprocity.cyclicCaseStatement_ramifiedSupport_clean)
      (K := K) (L := L) hcomm m hm hram hprinc b hcong hpos
  -- the two factors of the Artin symbol of the adjusted prime idèle
  have hA : ((Q.asIdeal : Ideal (NumberField.RingOfIntegers K)) :
        FractionalIdeal (nonZeroDivisors (NumberField.RingOfIntegers K)) K) ≠ 0 :=
    FractionalIdeal.coeIdeal_ne_zero.mpr Q.ne_bot
  have hB : FractionalIdeal.spanSingleton (nonZeroDivisors (NumberField.RingOfIntegers K))
      ((b : Kˣ) : K) ≠ 0 :=
    FractionalIdeal.spanSingleton_ne_zero_iff.mpr (Units.ne_zero _)
  show NK.CFTLib.Arl.artinSym (K := K) (L := L) hcomm
      (Idele.idealOf (NK.HeckeL.ideleOfPrime K Q * NK.GlobalCFT.Idele.principalIdele K b))
    = NK.Chebotarev.frobAtPrime (K := K) (L := L) Q
  rw [Idele.idealOf_mul, NK.CFTLib.Arl.idealOf_ideleOfPrime, Idele.idealOf_principalIdele,
    NK.CFTLib.Arl.artinSym_mul (K := K) (L := L) hcomm hA hB, hb1, mul_one,
    NK.CFTLib.Arl.artinSym_prime]

end Work.SSGRoute.ZDataMup
