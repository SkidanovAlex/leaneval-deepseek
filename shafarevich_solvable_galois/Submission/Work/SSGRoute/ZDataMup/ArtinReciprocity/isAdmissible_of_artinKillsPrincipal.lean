import Mathlib
import Submission.Work.SSGRoute.ZDataMup.ArtinReciprocity.Imports
import Submission.Work.SSGRoute.ZDataMup.NKArtinUmbrella
import Submission.Work.SSGRoute.ZDataMup.weakApprox_pos_numberField
import Submission.Work.SSGRoute.ZDataMup.ArtinReciprocity.onePlace_congruenceUnit_eq_one_of_artinKillsPrincipal
import Submission.NK.CFTLib.Arl.exists_monoidHom_ideleArtin
import Submission.NK.CFTLib.Arl.normIdeles_mem_ker_of_ideleArtin
import Submission.NK.CFTLib.Arl.exists_isCongruenceSubgroup_and_adjust
import Submission.NK.CFTLib.Arl.exists_norm_mul_mem_congruenceSubgroup
import Submission.NK.CFTLib.Existence.artinKernel
import Submission.NK.CFTLib.fundamentalClassElement
import Submission.NK.CFTLib.IdeleHasse.range_localNormFinite_eq_of_liesOver
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Admissibility of a modulus satisfying the ideal-theoretic reciprocity law

For a finite **cyclic** Galois extension `L / K` of number fields, a modulus `M > 0` whose prime
divisors outside `(M)` are unramified in `L` (`hram`) and which satisfies the ideal-theoretic
reciprocity law `NK.CFTLib.artinKillsPrincipal K L M` (`hprinc`) is *admissible*
(`NK.CFTLib.ArtinReciprocityIdeal.IsAdmissible K L M`): every congruence unit `x ≡ 1 mod M` at a
prime `𝔭 | (M)` is a local norm at every prime of `L` above `𝔭`.

## Proof

Build the idèlic Artin map `art : 𝕀[K] →* Gal(L/K)` attached to the modulus `M`
(`NK.CFTLib.Arl.exists_monoidHom_ideleArtin`): it kills the principal idèles, kills the idèlic
norms, is Frobenius-normalised at the primes `∤ (M)`, and — via the class-field-theoretic
computation of its kernel as `N_{L/K} 𝕀[L] · Kˣ` — its one-place factors are faithful:
`art (onePlace v a) = 1 ↔ a ∈ N_v`.

The key arithmetic input is
`Work.SSGRoute.ZDataMup.ArtinReciprocity.onePlace_congruenceUnit_eq_one_of_artinKillsPrincipal`:
at a prime `𝔭 | (M)` the local factor `art ∘ onePlace_𝔭` kills the congruence units of level
`M` (the ramified case of the description of the idèlic Artin map by its local factors).  Hence a
congruence unit `x` at `𝔭` satisfies `art (onePlace 𝔭 x) = 1`, so `x` lies in the local norm
subgroup `N_𝔭`; transferring between the primes of `L` above `𝔭`
(`NK.CFTLib.IdeleHasse.range_localNormFinite_eq_of_liesOver`) gives membership in the norm group at
the required prime `𝔮 | 𝔭`.
-/

set_option maxHeartbeats 2000000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

open scoped NumberField nonZeroDivisors
open NumberField IsDedekindDomain

noncomputable section

namespace Work.SSGRoute.ZDataMup.ArtinReciprocity

open NK.GlobalCFT

theorem isAdmissible_of_artinKillsPrincipal
    {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] [IsCyclic (L ≃ₐ[K] L)]
    (hcomm : ∀ a b : L ≃ₐ[K] L, a * b = b * a)
    (M : ℕ) (hM : 0 < M)
    (hram : ∀ 𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K),
      (M : NumberField.RingOfIntegers K) ∉ 𝔭.asIdeal →
      Ideal.ramificationIdxIn 𝔭.asIdeal (NumberField.RingOfIntegers L) = 1)
    (hprinc : NK.CFTLib.artinKillsPrincipal K L M) :
    NK.CFTLib.ArtinReciprocityIdeal.IsAdmissible K L M := by
  classical
  haveI : IsMulCommutative (L ≃ₐ[K] L) := IsMulCommutative.of_comm hcomm
  -- ## the idèlic Artin map attached to the modulus `M`
  obtain ⟨U, hU, hadj⟩ := NK.CFTLib.Arl.exists_isCongruenceSubgroup_and_adjust K M hM
  obtain ⟨art, hagree, hprincipal, hfrob, hsurj⟩ :=
    NK.CFTLib.Arl.exists_monoidHom_ideleArtin (K := K) (L := L) hcomm M hM hram hprinc U hU hadj
  have hUeq : U = NK.CFTLib.Arl.congruenceSubgroup K M :=
    SetLike.ext fun x => (hU.1 x).trans Iff.rfl
  have hnorm : ∀ y : Idele L, art (Idele.normIdeleHom K L y) = 1 := by
    intro y
    rw [hagree]
    refine NK.CFTLib.Arl.normIdeles_mem_ker_of_ideleArtin (K := K) (L := L) hcomm M hM hram
      hprinc U hU hadj ?_ y
    intro z
    obtain ⟨d, hd⟩ := NK.CFTLib.Arl.exists_norm_mul_mem_congruenceSubgroup K L M hM z
    exact ⟨d, hUeq ▸ hd⟩
  have hPle : Idele.principalSubgroup K ≤ art.ker := by
    intro a ha
    obtain ⟨b, rfl⟩ := Idele.mem_principalSubgroup.mp ha
    exact MonoidHom.mem_ker.mpr (hprincipal b)
  -- ## the kernel of `art` is `N_{L/K} 𝕀[L] · Kˣ`
  have hker : art.ker = Idele.normImage K L ⊔ Idele.principalSubgroup K := by
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
      have h2 : n⁻¹ * x ∈ Idele.principalSubgroup K :=
        (IdeleClassGroup.mk_eq_mk_iff).mp hmn
      have h3 : n * (n⁻¹ * x) ∈ Idele.normImage K L ⊔ Idele.principalSubgroup K :=
        Subgroup.mul_mem_sup hn h2
      rwa [mul_inv_cancel_left] at h3
    · refine sup_le ?_ hPle
      intro x hx
      obtain ⟨y, hy⟩ := Idele.mem_normImage.mp hx
      rw [MonoidHom.mem_ker,
        show x = Idele.normIdeleHom K L y from
          Idele.ext (fun v => by rw [Idele.normIdeleHom_apply]; exact hy v)]
      exact hnorm y
  -- ## one-place faithfulness of the local factors
  have hloc : ∀ (v : Place K) (a : (Place.localField K v)ˣ),
      art (NK.HassePrinciple.onePlace v a) = 1 ↔
        a ∈ NK.CFTLib.IdeleHasse.localNormSubgroup (K := K) (L := L) v := by
    intro v a
    rw [← MonoidHom.mem_ker, hker]
    exact ⟨fun h => (NK.CFTLib.IdeleHasse.onePlace_mem_normImage_iff (K := K) (L := L) v a).mp
        (NK.CFTLib.IdeleHasse.localFaithful_onePlace (K := K) (L := L)
          (inferInstance : IsCyclic (L ≃ₐ[K] L)) h),
      fun h => Subgroup.mem_sup_left
        ((NK.CFTLib.IdeleHasse.onePlace_mem_normImage_iff (K := K) (L := L) v a).mpr h)⟩
  -- ## the criterion
  intro 𝔭 h𝔭mem 𝔮 h𝔮 x hx
  have hone : art (NK.HassePrinciple.onePlace (Place.ofFinite 𝔭) x) = 1 :=
    onePlace_congruenceUnit_eq_one_of_artinKillsPrincipal (K := K) (L := L) hcomm M hM hram hprinc
      hprincipal hnorm hfrob 𝔭 h𝔭mem x hx
  have hxN : x ∈ NK.CFTLib.IdeleHasse.localNormSubgroup (K := K) (L := L) (Place.ofFinite 𝔭) :=
    (hloc (Place.ofFinite 𝔭) x).mp hone
  rw [NK.CFTLib.IdeleHasse.range_localNormFinite_eq_localNormSubgroup (K := K) (L := L) 𝔭 𝔮 h𝔮]
  exact hxN

end Work.SSGRoute.ZDataMup.ArtinReciprocity
