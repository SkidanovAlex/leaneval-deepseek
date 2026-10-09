/-
# The local–global product formula for cyclic extensions (Milne, *CFT*, VII.8.1(a))

For a finite **cyclic** extension `L/K` of number fields, the *global Artin map* is the product
`∏_v θ_v` of the local Artin maps: there is a monoid homomorphism `Φ : 𝕀 K →* Gal(L/K)` which kills
the principal idèles `Kˣ`, kills the idèlic norms `N_{L/K}𝕀_L`, is surjective, and sends the idèle of
a prime to the Frobenius element at that prime for **every** unramified prime.

## Structure of this file

* `exists_artinMap_productFormula_cyclic_of_crux` — the assignment's statement from the **ideal
  modulus Lang crux** `ker ψ ∩ I(𝔪) ⊆ P(𝔪)·𝔑(𝔪)` (`kernelLeId`, Lang X.2 Thm 2; the one arithmetic
  input of the whole development).  The chain is:

  1. `NK.CFTLib.ArtinReciprocityIdeal.hprinc_idealModulus_ramifiedSupport` produces an ideal modulus
     `𝔪`, supported **exactly** on the ramified primes, together with the **`mod*` conductor drop**
     `∀ b : Kˣ, CongrOneId 𝔪 b → artinSym (spanSingleton b) = 1` (its inputs are the crux, the norm
     index inequality `IdealModulusIndexProved` and the containment
     `IdealModulusContainmentProved`);
  2. `Work.SSGRoute.ZDataMup.cycleOfIdealModulus` views `𝔪` as a `Cycle` whose support is exactly
     the ramified primes — this is where the ideal modulus is used: a natural-number modulus has
     its support saturated above the rational primes (`NOTE_conductorDrop_obstruction.md`,
     finding (B));
  3. `Cycle.localGlobalMap_productFormula_of_cycleDrop` builds `Φ : 𝕀 K →* Gal(L/K)` killing `Kˣ`
     and `N_{L/K}𝕀_L` and Frobenius-normalised at every prime **outside** `c.supp`, i.e. at every
     unramified prime;
  4. surjectivity follows from the Frobenius normalisation and Chebotarev
     (`NK.CFTLib.Arl.eq_top_of_forall_isFrobAtPrime_of_notMem`).

* `exists_artinMap_productFormula_cyclic` — the same, with the crux supplied by the team's
  `IdealModulusKernelLeProved` (swap that one line for any other proof of the crux).
* `canonicalArtinMap`, `canonicalArtinMap_spec`, `CanonicalKillsPrincipal`,
  `canonicalArtinMap_kills_principal`, `localGlobalProductFormula_cyclic_of_canonical`,
  `localGlobalProductFormula_cyclic`.
-/
import Mathlib
import Submission.Work.SSGRoute.ZDataMup.cycleOfIdealModulus
import Submission.Work.SSGRoute.ZDataMup.IdealModulusIndexProved
import Submission.Work.SSGRoute.ZDataMup.IdealModulusContainmentProved
import Submission.Work.SSGRoute.ZDataMup.ArtinReciprocity.IdealModulus.hprinc_idealModulus_ramifiedSupport
import Submission.Work.SSGRoute.ZDataMup.IdealModulusKernel.kernelLeId
import Submission.NK.CFTLib.Arl.eq_top_of_forall_isFrobAtPrime_of_notMem
import Submission.NK.Chebotarev.LFunctions
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute.ZDataMup

open scoped NumberField RestrictedProduct
open NumberField IsDedekindDomain

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1000000

noncomputable section

/-- Commutativity of the Galois group of a cyclic extension, as a plain hypothesis. -/
theorem comm_of_isCyclic_lgpfc {G : Type*} [Group G] [IsCyclic G] :
    ∀ a b : G, a * b = b * a := by
  intro a b
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := G)
  obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp (hg a)
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp (hg b)
  rw [← zpow_add, ← zpow_add, add_comm m n]

section Cyclic

variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [FiniteDimensional K L] [IsGalois K L] [IsCyclic (L ≃ₐ[K] L)]

/-- **The local–global product formula for a cyclic extension, from the ideal-modulus crux**
(Milne, *CFT*, VII.8.1(a)). -/
theorem exists_artinMap_productFormula_cyclic_of_crux
    (hkerId : ∀ (hcomm : ∀ a b : L ≃ₐ[K] L, a * b = b * a)
      (𝔪 : Ideal (𝓞 K)), 𝔪 ≠ ⊥ →
      NK.CFTLib.ArtinReciprocityIdeal.IsAdmissibleId (K := K) (L := L) 𝔪 →
      NK.CFTLib.ArtinReciprocityIdeal.ContainsRamified (K := K) (L := L) 𝔪 →
      ∀ A : NK.CFTLib.ArtinReciprocityIdeal.Frac K,
        NK.CFTLib.ArtinReciprocityIdeal.FracCoprimeId 𝔪 A →
        NK.CFTLib.Arl.artinSym (K := K) (L := L) hcomm A = 1 →
        A ∈ NK.CFTLib.ArtinReciprocityIdeal.principalRayId 𝔪 ⊔
            NK.CFTLib.ArtinReciprocityIdeal.normRayId (K := K) (L := L) 𝔪) :
    ∃ Φ : NK.GlobalCFT.Idele K →* (L ≃ₐ[K] L),
      (∀ a : Kˣ, Φ (NK.GlobalCFT.Idele.principalIdele K a) = 1) ∧
      (∀ y : NK.GlobalCFT.Idele L, Φ (NK.GlobalCFT.Idele.normIdeleHom K L y) = 1) ∧
      Function.Surjective Φ ∧
      (∀ Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K),
        NK.HeckeL.IsUnramifiedIn (K := K) (L := L) Q →
        Φ (NK.HeckeL.ideleOfPrime K Q) = NK.Chebotarev.frobAtPrime (K := K) (L := L) Q) := by
  classical
  have hcomm : ∀ a b : L ≃ₐ[K] L, a * b = b * a := comm_of_isCyclic_lgpfc
  -- 1. the ideal modulus supported exactly on the ramified primes, and the `mod*` conductor drop
  obtain ⟨𝔪, h𝔪, _hadmId, _hram, hsupp, hdrop⟩ :=
    NK.CFTLib.ArtinReciprocityIdeal.hprinc_idealModulus_ramifiedSupport (K := K) (L := L) hcomm
      (hkerId hcomm)
      (fun 𝔪 h𝔪 hram hadm =>
        ⟨sup_le (Work.SSGRoute.ZDataMup.principalRayId_le_idealCoprimeGroupId (K := K) 𝔪 h𝔪)
            (Work.SSGRoute.ZDataMup.normRayId_le_idealCoprimeGroupId (K := K) (L := L) 𝔪),
          Work.SSGRoute.ZDataMup.IdealModulusIndexProved (K := K) (L := L) 𝔪 h𝔪 hram hadm⟩)
  -- 2. the cycle whose support is exactly the ramified primes
  obtain ⟨c, hramC, hsuppC, hlevC, hdropC⟩ :=
    Work.SSGRoute.ZDataMup.cycleOfIdealModulus (K := K) (L := L) hcomm 𝔪 h𝔪 hsupp hdrop
  -- 3. the idèlic Artin map of that cycle
  obtain ⟨Φ, hprincipal, hnorm, hfrob⟩ :=
    Work.SSGRoute.ZDataMup.Cycle.localGlobalMap_productFormula_of_cycleDrop
      (K := K) (L := L) hcomm c hramC hsuppC hlevC hdropC
  refine ⟨Φ, hprincipal, hnorm, ?_, hfrob⟩
  -- 4. surjectivity: the range contains the Frobenius at every prime outside the finite set `c.supp`
  have hrange : Φ.range = ⊤ := by
    refine NK.CFTLib.Arl.eq_top_of_forall_isFrobAtPrime_of_notMem (K := K) (L := L) c.supp
      Φ.range ?_
    intro p hp σ hσ
    have hunr : NK.HeckeL.IsUnramifiedIn (K := K) (L := L) p := by
      by_contra h
      exact hp (hramC p h)
    have hσ' : NK.Chebotarev.frobAtPrime (K := K) (L := L) p = σ :=
      (NK.Chebotarev.isFrobAtPrime_iff_frobAtPrime_eq (K := K) (L := L) hcomm p hunr σ).mp hσ
    rw [← hσ']
    exact MonoidHom.mem_range.mpr ⟨NK.HeckeL.ideleOfPrime K p, hfrob p hunr⟩
  intro x
  exact MonoidHom.mem_range.mp (by rw [hrange]; exact Subgroup.mem_top x)

/-- **The local–global product formula for a cyclic extension** (Milne, *CFT*, VII.8.1(a)).

The arithmetic input `kernelLeId` (Lang X.2 Thm 2 for an ideal modulus) is supplied by the team's
`IdealModulusKernel.kernelLeId` (a file requested as part of this work); any other proof of the
same crux can be substituted here -- the only change needed is the one `fun` in the final line. -/
theorem exists_artinMap_productFormula_cyclic :
    ∃ Φ : NK.GlobalCFT.Idele K →* (L ≃ₐ[K] L),
      (∀ a : Kˣ, Φ (NK.GlobalCFT.Idele.principalIdele K a) = 1) ∧
      (∀ y : NK.GlobalCFT.Idele L, Φ (NK.GlobalCFT.Idele.normIdeleHom K L y) = 1) ∧
      Function.Surjective Φ ∧
      (∀ Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K),
        NK.HeckeL.IsUnramifiedIn (K := K) (L := L) Q →
        Φ (NK.HeckeL.ideleOfPrime K Q) = NK.Chebotarev.frobAtPrime (K := K) (L := L) Q) :=
  exists_artinMap_productFormula_cyclic_of_crux (K := K) (L := L)
    (fun hcomm 𝔪 h𝔪 hadm hram =>
      Work.SSGRoute.ZDataMup.IdealModulusKernel.kernelLeId (K := K) (L := L) hcomm 𝔪 h𝔪 hadm hram)

/-- **The canonical local–global Artin map of a cyclic extension**, as an explicit object: a map
`Φ : 𝕀 K →* Gal(L/K)` satisfying the four clauses of Milne, *CFT*, VII.8.1(a). -/
noncomputable def canonicalArtinMap : NK.GlobalCFT.Idele K →* (L ≃ₐ[K] L) :=
  Classical.choose (exists_artinMap_productFormula_cyclic (K := K) (L := L))

/-- The defining properties of `canonicalArtinMap`: it kills the principal idèles, kills the idèlic
norms, is surjective, and is Frobenius-normalised at every unramified prime. -/
theorem canonicalArtinMap_spec :
    (∀ a : Kˣ, canonicalArtinMap (K := K) (L := L) (NK.GlobalCFT.Idele.principalIdele K a) = 1) ∧
    (∀ y : NK.GlobalCFT.Idele L,
      canonicalArtinMap (K := K) (L := L) (NK.GlobalCFT.Idele.normIdeleHom K L y) = 1) ∧
    Function.Surjective (canonicalArtinMap (K := K) (L := L)) ∧
    (∀ Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K),
      NK.HeckeL.IsUnramifiedIn (K := K) (L := L) Q →
      canonicalArtinMap (K := K) (L := L) (NK.HeckeL.ideleOfPrime K Q)
        = NK.Chebotarev.frobAtPrime (K := K) (L := L) Q) :=
  Classical.choose_spec (exists_artinMap_productFormula_cyclic (K := K) (L := L))

/-- **The product form of Hilbert reciprocity for the canonical map** (Milne, *CFT*, VII.8.1(a)):
for every finite cyclic extension `L/K` of number fields the canonical local–global Artin map kills
the principal idèles. -/
def CanonicalKillsPrincipal : Prop :=
  ∀ {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] [IsCyclic (L ≃ₐ[K] L)],
    ∀ a : Kˣ,
      canonicalArtinMap (K := K) (L := L) (NK.GlobalCFT.Idele.principalIdele K a) = 1

/-- **The assignment's statement follows from the product form of Hilbert reciprocity**
(Milne, *CFT*, VII.8.1(a)). -/
theorem localGlobalProductFormula_cyclic_of_canonical
    {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] [IsCyclic (L ≃ₐ[K] L)]
    (hprod : CanonicalKillsPrincipal) :
    ∃ Φ : NK.GlobalCFT.Idele K →* (L ≃ₐ[K] L),
      (∀ a : Kˣ, Φ (NK.GlobalCFT.Idele.principalIdele K a) = 1) ∧
      (∀ y : NK.GlobalCFT.Idele L, Φ (NK.GlobalCFT.Idele.normIdeleHom K L y) = 1) ∧
      Function.Surjective Φ ∧
      (∀ Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K),
        NK.HeckeL.IsUnramifiedIn (K := K) (L := L) Q →
        Φ (NK.HeckeL.ideleOfPrime K Q) = NK.Chebotarev.frobAtPrime (K := K) (L := L) Q) := by
  obtain ⟨-, hnorm, hsurj, hfrob⟩ := canonicalArtinMap_spec (K := K) (L := L)
  exact ⟨canonicalArtinMap (K := K) (L := L), fun a => hprod a, hnorm, hsurj, hfrob⟩

end Cyclic

/-- **The canonical local–global Artin map of a cyclic extension kills the principal idèles**
(Milne, *CFT*, VII.8.1(a)) — the product form of Hilbert reciprocity. -/
theorem canonicalArtinMap_kills_principal : CanonicalKillsPrincipal := by
  intro K L _ _ _ _ _ _ _ _ a
  exact (canonicalArtinMap_spec (K := K) (L := L)).1 a

/-- **Shafarevich's local–global product formula for cyclic extensions** (Milne, *CFT*, VII.8.1(a)):
for a finite cyclic extension `L/K` of number fields there is a monoid homomorphism
`Φ : 𝕀 K →* Gal(L/K)` killing the principal idèles `Kˣ` and the idèlic norms, surjective, and
Frobenius-normalised at every unramified prime. -/
theorem localGlobalProductFormula_cyclic
    {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] [IsCyclic (L ≃ₐ[K] L)] :
    ∃ Φ : NK.GlobalCFT.Idele K →* (L ≃ₐ[K] L),
      (∀ a : Kˣ, Φ (NK.GlobalCFT.Idele.principalIdele K a) = 1) ∧
      (∀ y : NK.GlobalCFT.Idele L, Φ (NK.GlobalCFT.Idele.normIdeleHom K L y) = 1) ∧
      Function.Surjective Φ ∧
      (∀ Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K),
        NK.HeckeL.IsUnramifiedIn (K := K) (L := L) Q →
        Φ (NK.HeckeL.ideleOfPrime K Q) = NK.Chebotarev.frobAtPrime (K := K) (L := L) Q) :=
  localGlobalProductFormula_cyclic_of_canonical (K := K) (L := L)
    canonicalArtinMap_kills_principal

end

end Work.SSGRoute.ZDataMup
