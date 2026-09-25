import Mathlib
import Submission.NK.CFTLib.ArtinIdeal
import Submission.NK.CFTLib.ArtinReciprocityIdeal.Conductor
import Submission.NK.CFTLib.Arl.Defs
import Submission.NK.CFTLib.Arl.exists_isCongruenceSubgroup_and_adjust
import Submission.NK.CFTLib.Arl.exists_monoidHom_ideleArtin
import Submission.NK.CFTLib.Arl.normIdeles_mem_ker_of_ideleArtin
import Submission.NK.NUV2.ARL.normAdjustment

/-!
# The idèlic Artin map from the ideal-theoretic reciprocity law

For a finite abelian extension `L / K` of number fields, the ideal-theoretic reciprocity law
`NK.CFTLib.ArtinReciprocityIdeal` supplies a modulus `m` and the congruence subgroup `U` of
modulus `m`; the idèlic Artin map

  `art x = artinSym (idealOf (x · bₓ)),   x · bₓ ∈ U`

is then a surjective homomorphism `𝕀 K →* Gal(L/K)` which kills the principal idèles and the
idèlic norms `N_{L/K} 𝕀 L`, and which sends the idèle of a prime `𝔭 ∤ (m)` to its Frobenius.

This packages, for later use, the four properties in one statement with the modulus `m` carried
along; all the ingredients are the sorry-free files of `Submission/Work/CFTLib/Arl/` and
`Submission/Work/NUV2/ARL/`.
-/

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

open scoped NumberField RestrictedProduct IsMulCommutative
open NumberField IsDedekindDomain

noncomputable section

namespace NK.CFTLib.Existence

open NK.GlobalCFT

/-- **The idèlic Artin map attached to the ideal-theoretic reciprocity law.**

There is a modulus `m > 0`, a congruence subgroup `U` of modulus `m` (with an adjustment
`𝕀 K = U·Kˣ`), and a monoid homomorphism `art : 𝕀 K →* Gal(L/K)` such that

* every prime `𝔭 ∤ (m)` is unramified in `L/K`;
* `art` kills the principal idèles `Kˣ`;
* `art` kills the idèlic norms `N_{L/K} 𝕀 L`;
* `art (ideleOfPrime K 𝔭) = Frob_𝔭` for `𝔭 ∤ (m)`;
* `art` is surjective (the Frobenius elements generate `Gal(L/K)`). -/
theorem exists_ideleArtinMap_of_arl (h : NK.CFTLib.ArtinReciprocityIdeal)
    {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] [IsMulCommutative (L ≃ₐ[K] L)] :
    ∃ (m : ℕ) (_ : 0 < m) (art : Idele K →* Gal(L/K)),
      (∀ 𝔭 : NK.Chebotarev.PrimeIdeal K, (m : 𝓞 K) ∉ 𝔭.asIdeal →
        ∀ Q : NK.Chebotarev.PrimeIdeal L, Q.asIdeal.LiesOver 𝔭.asIdeal →
          Q.asIdeal.ramificationIdx (𝓞 K) = 1) ∧
      (∀ a : Kˣ, art (Idele.principalIdele K a) = 1) ∧
      (∀ y : Idele L, art (Idele.normIdeleHom K L y) = 1) ∧
      (∀ 𝔭 : NK.Chebotarev.PrimeIdeal K, (m : 𝓞 K) ∉ 𝔭.asIdeal →
        art (NK.HeckeL.ideleOfPrime K 𝔭) =
          NK.Chebotarev.frobAtPrime (K := K) (L := L) 𝔭) ∧
      Function.Surjective art := by
  classical
  have hcomm : ∀ a b : Gal(L/K), a * b = b * a := fun a b => mul_comm' a b
  obtain ⟨m, hm, hramIn, hprinc⟩ := h K L hcomm
  have hram : ∀ 𝔭 : NK.Chebotarev.PrimeIdeal K, (m : 𝓞 K) ∉ 𝔭.asIdeal →
      ∀ Q : NK.Chebotarev.PrimeIdeal L, Q.asIdeal.LiesOver 𝔭.asIdeal →
        Q.asIdeal.ramificationIdx (𝓞 K) = 1 := by
    intro 𝔭 h𝔭 Q hQ
    letI hMSA : MulSemiringAction (Gal(L/K)) (𝓞 L) :=
      IsIntegralClosure.MulSemiringAction (𝓞 K) K L (𝓞 L)
    haveI hGG : IsGaloisGroup (Gal(L/K)) (𝓞 K) (𝓞 L) :=
      IsGaloisGroup.of_isFractionRing (Gal(L/K)) (𝓞 K) (𝓞 L) K L
    rw [← Ideal.ramificationIdxIn_eq_ramificationIdx (A := 𝓞 K) (B := 𝓞 L) 𝔭.asIdeal Q.asIdeal
      (Gal(L/K))]
    exact hramIn 𝔭 h𝔭
  obtain ⟨U, hU, hadj⟩ := NK.CFTLib.Arl.exists_isCongruenceSubgroup_and_adjust K m hm
  obtain ⟨art, hart,
    hprincipal, hfrob, hsurj⟩ :=
    NK.CFTLib.Arl.exists_monoidHom_ideleArtin (K := K) (L := L) hcomm m hm hramIn hprinc U hU hadj
  have hnorm : ∀ y : Idele L, art (Idele.normIdeleHom K L y) = 1 := by
    intro y
    rw [hart (Idele.normIdeleHom K L y)]
    exact NK.CFTLib.Arl.normIdeles_mem_ker_of_ideleArtin (K := K) (L := L) hcomm m hm hramIn
      hprinc U hU hadj
      (NK.NUV2.ARL.normAdjustment (K := K) (L := L) m hm hramIn U hU) y
  exact ⟨m, hm, art, hram, hprincipal, hnorm, hfrob, hsurj⟩

end NK.CFTLib.Existence
