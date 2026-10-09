import Mathlib
import Submission.NK.CFTLib.hilbertReciprocityCyclicAux
import Submission.NK.NUV2.ARL.unifUnit_pow_mem_localNormSubgroup
import Submission.NK.CFTLib.ARL.artinReciprocity_cyclotomic
import Submission.NK.CFTLib.Arl.exists_monoidHom_ideleArtin
import Submission.NK.CFTLib.Arl.exists_norm_mul_mem_congruenceSubgroup
import Submission.NK.CFTLib.IdeleHasse.mem_normImage_iff_localNorm_of_finiteDimensional
import Submission.NK.NUV2.ARL.Gap.isUnramified_cyclotomicExtension
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Hilbert reciprocity for a cyclotomic level at an unramified finite place, arbitrary modulus

`NK.NUV2.ARL.localImage_mem_localNormSubgroup_of_isCyclotomic_of_unramified` proves this for a
*prime* cyclotomic level `L = K(ζ_q)`.  The present file removes the primality hypothesis: for
**any** `m ≥ 1` with `L = K(ζ_m)` (so `Gal(L/K) ↪ (ℤ/m)ˣ` is still commutative) and a finite place
`Q` of `K` with `(m : 𝓞 K) ∉ Q.asIdeal`, a global element `b ∈ Kˣ` which is a local norm at every
place `v ≠ Q` is a local norm at `Q`.

Nothing in the argument uses primality of the modulus: the ramified primes of `K(ζ_m)/K` all divide
`(m)` (`NK.NUV2.ARL.Gap.isUnramified_cyclotomicExtension`, stated for arbitrary `n`), the
ideal-theoretic reciprocity law `NK.CFTLib.ARL.artinReciprocity_cyclotomic` is stated for arbitrary
`n`, and the local kernel computation
`NK.NUV2.ARL.mem_localNormSubgroup_of_onePlace_mem_ker` needs only the commutativity of the Galois
group.  Consequently the Frobenius normalisation `art (ideleOfPrime K 𝔭) = frobAtPrime 𝔭` is
available at every prime `𝔭 ∤ m`, in particular at `Q`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1600000

open scoped NumberField RestrictedProduct
open NumberField IsDedekindDomain

noncomputable section

namespace NK.CFTLib.HR

open NK.GlobalCFT

variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [FiniteDimensional K L] [IsGalois K L]

/-- The Galois group of a cyclotomic extension is commutative, for **any** modulus `m`: the
cyclotomic character `ζ ↦ ζ ^ _` embeds it into `(ZMod m)ˣ`. -/
theorem hcomm_of_isCyclotomic_neZero (m : ℕ) [NeZero m] [IsCyclotomicExtension {m} K L] :
    ∀ a b : Gal(L/K), a * b = b * a := by
  have hζ : IsPrimitiveRoot (IsCyclotomicExtension.zeta m K L) m :=
    IsCyclotomicExtension.zeta_spec m K L
  have hχinj : Function.Injective (hζ.autToPow K) := IsPrimitiveRoot.autToPow_injective K hζ
  intro a b
  exact hχinj (by rw [map_mul, map_mul, mul_comm])

/-- **The idèlic Artin map of a cyclotomic level, at the modulus `m`.**

For `L = K(ζ_m)` (`m ≥ 1`) there is an idèlic Artin map `𝕀 K →* Gal(L/K)` killing the principal
idèles `Kˣ` and the idèle norms `N_{L/K}𝕀_L`, carrying `ideleOfPrime K 𝔭` to `frobAtPrime 𝔭` for
**every** prime `𝔭` with `(m : 𝓞 K) ∉ 𝔭`, and surjective. -/
theorem exists_artin_of_cyclotomic_neZero (m : ℕ) [NeZero m] [IsCyclotomicExtension {m} K L] :
    ∃ art : Idele K →* Gal(L/K),
      (∀ a : Kˣ, art (Idele.principalIdele K a) = 1) ∧
      (∀ y : Idele L, art (Idele.normIdeleHom K L y) = 1) ∧
      (∀ 𝔭 : HeightOneSpectrum (𝓞 K), (m : 𝓞 K) ∉ 𝔭.asIdeal →
        art (NK.HeckeL.ideleOfPrime K 𝔭) = NK.Chebotarev.frobAtPrime (K := K) (L := L) 𝔭) ∧
      Function.Surjective art := by
  classical
  have hmpos : 0 < m := Nat.pos_of_ne_zero (NeZero.ne m)
  have hcomm : ∀ a b : Gal(L/K), a * b = b * a :=
    hcomm_of_isCyclotomic_neZero (K := K) (L := L) m
  have hram : ∀ 𝔭 : HeightOneSpectrum (𝓞 K), (m : 𝓞 K) ∉ 𝔭.asIdeal →
      Ideal.ramificationIdxIn 𝔭.asIdeal (𝓞 L) = 1 := by
    intro 𝔭 h𝔭
    obtain ⟨P, hP⟩ := NK.Chebotarev.exists_primeIdeal_liesOver (K := K) (L := L) 𝔭
    rw [Ideal.ramificationIdxIn_eq_ramificationIdx (A := 𝓞 K) (B := 𝓞 L) 𝔭.asIdeal P.asIdeal
      (Gal(L/K))]
    exact NK.NUV2.ARL.Gap.isUnramified_cyclotomicExtension (n := m) 𝔭 h𝔭 P hP
  have hprinc : NK.CFTLib.artinKillsPrincipal K L m :=
    fun a ha hpos s e σ hs hfac hfrob =>
      NK.CFTLib.ARL.artinReciprocity_cyclotomic K L m a ha hpos s e σ hs hfac hfrob
  obtain ⟨U, hU, hadj⟩ := NK.CFTLib.Arl.exists_isCongruenceSubgroup_and_adjust K m hmpos
  obtain ⟨art, hagree, hprin, hfrob, hsurj⟩ :=
    NK.CFTLib.Arl.exists_monoidHom_ideleArtin (K := K) (L := L) hcomm m hmpos hram hprinc
      U hU hadj
  have hUeq : U = NK.CFTLib.Arl.congruenceSubgroup K m :=
    SetLike.ext fun x => (hU.1 x).trans Iff.rfl
  have hnorm : ∀ y : Idele L, art (Idele.normIdeleHom K L y) = 1 := by
    intro y
    rw [hagree]
    refine NK.CFTLib.Arl.normIdeles_mem_ker_of_ideleArtin (K := K) (L := L) hcomm m hmpos hram
      hprinc U hU hadj ?_ y
    intro z
    obtain ⟨d, hd⟩ := NK.CFTLib.Arl.exists_norm_mul_mem_congruenceSubgroup K L m hmpos z
    exact ⟨d, hUeq ▸ hd⟩
  exact ⟨art, hprin, hnorm, hfrob, hsurj⟩

/-- **Hilbert reciprocity for a cyclotomic level at an unramified finite place (arbitrary modulus).**

For `L = K(ζ_m)` (`m ≥ 1`) and a finite place `Q` of `K` with `(m : 𝓞 K) ∉ Q.asIdeal`, a global
element `b ∈ Kˣ` which is a local norm at every place `v ≠ Q` is a local norm at `Q`. -/
theorem localImage_mem_localNormSubgroup_of_isCyclotomic_of_unramified_neZero
    (m : ℕ) [NeZero m] [IsCyclotomicExtension {m} K L]
    (Q : HeightOneSpectrum (𝓞 K)) (hmQ : (m : 𝓞 K) ∉ Q.asIdeal) (b : Kˣ)
    (h : ∀ v : Place K, v ≠ Place.ofFinite Q →
      NK.CFTLib.localImageHom v b ∈
        NK.CFTLib.IdeleHasse.localNormSubgroup (K := K) (L := L) v) :
    NK.CFTLib.localImageHom (Place.ofFinite Q) b ∈
      NK.CFTLib.IdeleHasse.localNormSubgroup (K := K) (L := L) (Place.ofFinite Q) := by
  classical
  have hmpos : 0 < m := Nat.pos_of_ne_zero (NeZero.ne m)
  haveI : IsMulCommutative (Gal(L/K)) :=
    IsMulCommutative.of_comm (hcomm_of_isCyclotomic_neZero (K := K) (L := L) m)
  have hunrHecke : NK.HeckeL.IsUnramifiedIn (K := K) (L := L) Q :=
    NK.NUV2.ARL.Gap.isUnramified_cyclotomicExtension (n := m) Q hmQ
  obtain ⟨art, hprin, hnorm, hfrob, -⟩ := exists_artin_of_cyclotomic_neZero (K := K) (L := L) m
  have hfrobQ : art (NK.HeckeL.ideleOfPrime K Q) =
      NK.Chebotarev.frobAtPrime (K := K) (L := L) Q :=
    hfrob Q hmQ
  set bQ : (Q.adicCompletion K)ˣ := NK.CFTLib.localImageHom (Place.ofFinite Q) b with hbQ
  set z : Idele K := Idele.principalIdele K b *
    (NK.HassePrinciple.onePlace (Place.ofFinite Q) bQ)⁻¹ with hz
  have hzmem : z ∈ Idele.normImage K L := by
    rw [NK.CFTLib.IdeleHasse.mem_normImage_iff_localNorm_of_finiteDimensional]
    intro v
    by_cases hv : v = Place.ofFinite Q
    · subst hv
      refine NK.CFTLib.exists_normIdeleFun_eq_of_mem_localNormSubgroup (K := K) (L := L) ?_
      have hbQeq : (Idele.principalIdele K b) (Place.ofFinite Q) = bQ := by
        rw [hbQ, NK.CFTLib.localImageHom_apply, Idele.principalIdele_apply]
        rfl
      rw [hz, Idele.mul_apply, Idele.inv_apply, NK.HassePrinciple.onePlace_apply_self,
        hbQeq, mul_inv_cancel]
      exact Subgroup.one_mem _
    · refine NK.CFTLib.exists_normIdeleFun_eq_of_mem_localNormSubgroup (K := K) (L := L) ?_
      rw [hz, Idele.mul_apply, Idele.inv_apply, NK.HassePrinciple.onePlace_apply_ne hv,
        inv_one, mul_one, Idele.principalIdele_apply]
      exact h v hv
  obtain ⟨y, hy⟩ := Idele.mem_normImage.mp hzmem
  have hzy : z = Idele.normIdeleHom K L y := by
    ext v
    rw [Idele.normIdeleHom_apply]
    exact congrArg Units.val (hy v)
  have hz1 : art z = 1 := by
    rw [hzy]
    exact hnorm y
  have hQ1 : art (NK.HassePrinciple.onePlace (Place.ofFinite Q) bQ) = 1 := by
    have h2 : art z = (art (NK.HassePrinciple.onePlace (Place.ofFinite Q) bQ))⁻¹ := by
      rw [hz, map_mul, map_inv, hprin b, one_mul]
    rw [hz1] at h2
    exact inv_eq_one.mp h2.symm
  exact NK.NUV2.ARL.mem_localNormSubgroup_of_onePlace_mem_ker (K := K) (L := L) Q hunrHecke
    art hnorm hfrobQ hQ1

end NK.CFTLib.HR
