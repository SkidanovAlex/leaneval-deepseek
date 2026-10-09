import Mathlib
import Submission.Work.SSGRoute.ZDataMup.ArtinConductorImports
import Submission.Work.SSGRoute.NKExistenceImport
import Submission.NK.CFTLib.Existence.artinKernel
import Submission.NK.NUV2.ARL.normAdjustment
import Submission.Work.SSGRoute.ZDataMup.ideleArtin_frobAtPrime_unramifiedLane
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

/-- Commutativity of the Galois group of a cyclic extension. -/
theorem comm_of_isCyclic_zdata {G : Type*} [Group G] [IsCyclic G] :
    ∀ a b : G, a * b = b * a := by
  intro a b
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := G)
  obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp (hg a)
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp (hg b)
  rw [← zpow_add, ← zpow_add, add_comm m n]

/-- **The local–global Artin map of a cyclic extension kills the principal idèles** (Milne, *CFT*,
VII.8.1(a)).

For a finite cyclic extension `L/K` of number fields there is a monoid homomorphism
`Φ : 𝕀 K →* Gal(L/K)` which kills the principal idèles `Kˣ`, kills the idèlic norms `N_{L/K}𝕀_L`,
is surjective, and is Frobenius-normalised at **every** unramified finite prime:
`Φ (ideleOfPrime K Q) = frobAtPrime Q`.

Such a `Φ` is the product `∏_v λ_v` of the local Artin maps; the last three clauses are
`NK.CFTLib.IdeleHasse.exists_localGlobalArtinMap'`, so the content is the reciprocity clause
"`Φ` kills `Kˣ`".  Indeed a `Φ` obtained from `exists_localGlobalArtinMap'` also has kernel
`N_{L/K}𝕀_L ⊔ Kˣ` once `Φ` kills `Kˣ` (`NK.CFTLib.Existence.ker_artinMapCK_eq_normClassSubgroup`).

Here `Φ` is realised as the idèlic Artin map `NK.CFTLib.Arl.ideleArtin` attached to the
congruence datum supplied by the ideal-theoretic reciprocity law
(`NK.CFTLib.artinReciprocityIdeal_proved`), which kills the principal idèles by construction; the
Frobenius normalisation at the unramified primes dividing the modulus is the conductor drop
`conductorDrop_ramifiedCongrLane`. -/
theorem localGlobalArtinMap_kills_principal_cyclic
    {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] [IsCyclic (Gal(L/K))] :
    ∃ Φ : NK.GlobalCFT.Idele K →* Gal(L/K),
      (∀ a : Kˣ, Φ (NK.GlobalCFT.Idele.principalIdele K a) = 1) ∧
      (∀ y : NK.GlobalCFT.Idele L, Φ (NK.GlobalCFT.Idele.normIdeleHom K L y) = 1) ∧
      Function.Surjective Φ ∧
      (∀ Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K),
        NK.HeckeL.IsUnramifiedIn (K := K) (L := L) Q →
        Φ (NK.HeckeL.ideleOfPrime K Q) = NK.Chebotarev.frobAtPrime (K := K) (L := L) Q) := by
  classical
  have hcomm : ∀ a b : Gal(L/K), a * b = b * a := comm_of_isCyclic_zdata
  -- the ideal-theoretic reciprocity law
  obtain ⟨m, hm, hramIn, hprincIn⟩ := NK.CFTLib.artinReciprocityIdeal_proved K L hcomm
  -- the congruence subgroup of modulus `m`, with an adjustment
  obtain ⟨U, hU, hadj⟩ := NK.CFTLib.Arl.exists_isCongruenceSubgroup_and_adjust K m hm
  -- the idèlic Artin map
  obtain ⟨art, hagree, hprincipal, _hgood, hsurj⟩ :=
    NK.CFTLib.Arl.exists_monoidHom_ideleArtin (K := K) (L := L) hcomm m hm hramIn hprincIn
      U hU hadj
  have hUeq : U = NK.CFTLib.Arl.congruenceSubgroup K m :=
    SetLike.ext fun x => (hU.1 x).trans Iff.rfl
  -- the norm clause
  have hnorm : ∀ y : Idele L, art (Idele.normIdeleHom K L y) = 1 := by
    intro y
    rw [hagree]
    refine NK.CFTLib.Arl.normIdeles_mem_ker_of_ideleArtin (K := K) (L := L) hcomm m hm hramIn
      hprincIn U hU hadj ?_ y
    intro z
    obtain ⟨d, hd⟩ := NK.CFTLib.Arl.exists_norm_mul_mem_congruenceSubgroup K L m hm z
    exact ⟨d, hUeq ▸ hd⟩
  refine ⟨art, hprincipal, hnorm, hsurj, ?_⟩
  -- the Frobenius normalisation, at every unramified prime
  intro Q hunr
  rw [hagree]
  exact ideleArtin_frobAtPrime_unramifiedLane (K := K) (L := L) hcomm m hm hramIn hprincIn
    U hU hadj hunr

end Work.SSGRoute.ZDataMup
