import Mathlib
import Submission.Work.SSGRoute.ZDataMup.localFactorProductFormulaAux
import Submission.Work.SSGRoute.ZDataMup.LTRecFamCrux.ideleArtin_ideleOfPrime_of_unramified
import Submission.Work.SSGRoute.ZDataMup.NKArtinUmbrella
import Submission.NK.CFTLib.ArtinReciprocityIdealProved
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The abelian idèlic Artin map with its local factors, in a module that builds

`Submission/Work/SSGRoute/ZDataMup/localFactor_productFormula_abelian.lean` contains complete
proofs of the abelian idèlic Artin map (with the exact kernel `N_{L/K}𝕀_L ⊔ Kˣ` and the Frobenius
normalisation at every unramified prime) and of its local factors, but the file **does not parse**:
at line 111 a doc comment is left dangling (its declaration was deleted) so Lean reports an
`unexpected token` error on the section comment that follows it, and every module importing it is
therefore unbuildable
(among them `Work.SSGRoute.ZDataMup.mup_localArtin_productFormula`, `…gluedMap_kills_principalIdele`
and most of the `ZDataMup` Artin-reciprocity lane).  That file belongs to another agent and is not
edited here.

This module re-proves, in a buildable module, the single statement that the gate
`Work.SSGRoute.ZConstruction.auxPairingGate_odd` consumes: for a finite **abelian** extension
`L/K` of number fields there is `Φ : 𝕀_K →* Gal(L/K)` with

* `ker Φ = N_{L/K} 𝕀_L ⊔ Kˣ` (equivalently: `Φ` kills the idèlic norms and the principal idèles),
* `Φ (onePlace v a) = 1 ↔ a ∈ N_v` (one-place faithfulness, Milne *CFT* V.5.3(a)),
* `Φ (ideleOfPrime K Q) = Frob_Q` at every unramified `Q`,
* the product formula: for `x ∈ Kˣ` and every finite set of places `s` off which the local factors
  `θ_v := Φ ∘ onePlace_v` are trivial, `∏_{v ∈ s} θ_v(x_v) = 1`.

The proof is the (repaired) proof of the two theorems of the broken module: the surjectivity-free
kernel plus Frobenius clauses from `NK.CFTLib.artinReciprocityIdeal_proved` (the ideal-theoretic
reciprocity law) through `exists_ideleArtinMap_with_kernel` and
`ideleArtin_ideleOfPrime_of_unramified`, the one-place faithfulness from
`Work.SSGRoute.ZDataMup.localFaithful_abelian`, and the product formula from
`Work.SSGRoute.ZDataMup.cprod_localFactor_eq_one`.
-/

open scoped NumberField RestrictedProduct
open NumberField IsDedekindDomain

namespace Work.SSGRoute.ZConstruction

set_option maxHeartbeats 1000000

/-- **The abelian idèlic Artin map with its exact kernel, its one-place faithfulness and the
product formula for its local factors.** -/
theorem exists_abelianArtin_localFactors {K : Type} [Field K] [NumberField K] {L : Type} [Field L]
    [NumberField L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (hcomm : ∀ a b : L ≃ₐ[K] L, a * b = b * a) :
    ∃ Φ : NK.GlobalCFT.Idele K →* (L ≃ₐ[K] L),
      MonoidHom.ker Φ =
          NK.GlobalCFT.Idele.normImage K L ⊔ NK.GlobalCFT.Idele.principalSubgroup K ∧
      (∀ y : NK.GlobalCFT.Idele L, Φ (NK.GlobalCFT.Idele.normIdeleHom K L y) = 1) ∧
      (∀ a : Kˣ, Φ (NK.GlobalCFT.Idele.principalIdele K a) = 1) ∧
      (∀ (v : NK.GlobalCFT.Place K) (a : (NK.GlobalCFT.Place.localField K v)ˣ),
        Φ (NK.HassePrinciple.onePlace v a) = 1 ↔
          a ∈ NK.CFTLib.IdeleHasse.localNormSubgroup (K := K) (L := L) v) ∧
      (∀ (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)),
        NK.HeckeL.IsUnramifiedIn (K := K) (L := L) Q →
        Φ (NK.HeckeL.ideleOfPrime K Q) = NK.Chebotarev.frobAtPrime (K := K) (L := L) Q) ∧
      (∀ (x : Kˣ) (s : Finset (NK.GlobalCFT.Place K)),
        (∀ v, v ∉ s →
          Φ (NK.HassePrinciple.onePlace v (NK.CFTLib.IdeleHasse.localImageAt v x)) = 1) →
        NK.CFTLib.IdeleHasse.cprod hcomm s
          (fun v => Φ (NK.HassePrinciple.onePlace v (NK.CFTLib.IdeleHasse.localImageAt v x))) = 1) := by
  classical
  -- the ideal-theoretic reciprocity law at a modulus `m`, and a congruence subgroup of modulus `m`
  obtain ⟨m, hm, hram, hprinc⟩ := NK.CFTLib.artinReciprocityIdeal_proved K L hcomm
  obtain ⟨U, hU, hadj⟩ := NK.CFTLib.Arl.exists_isCongruenceSubgroup_and_adjust K m hm
  -- the idèlic Artin map with its kernel
  obtain ⟨Φ, hagree, hker, _hprincipal, _hgood, _hsurj⟩ :=
    Work.SSGRoute.ZDataMup.exists_ideleArtinMap_with_kernel (K := K) (L := L) hcomm m hm hram
      hprinc U hU hadj
  have hfrob : ∀ (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)),
      NK.HeckeL.IsUnramifiedIn (K := K) (L := L) Q →
      Φ (NK.HeckeL.ideleOfPrime K Q) = NK.Chebotarev.frobAtPrime (K := K) (L := L) Q := by
    intro Q hunr
    rw [hagree]
    exact Work.SSGRoute.ZDataMup.ideleArtin_ideleOfPrime_of_unramified (K := K) (L := L) hcomm m
      hm hram hprinc U hU hadj hunr
  have hnorm : ∀ y : NK.GlobalCFT.Idele L, Φ (NK.GlobalCFT.Idele.normIdeleHom K L y) = 1 := by
    intro y
    rw [← MonoidHom.mem_ker, hker]
    exact Subgroup.mem_sup_left
      (NK.GlobalCFT.Idele.mem_normImage.mpr ⟨y, fun v => by
        rw [NK.GlobalCFT.Idele.normIdeleHom_apply]⟩)
  have hprin : ∀ a : Kˣ, Φ (NK.GlobalCFT.Idele.principalIdele K a) = 1 := by
    intro a
    rw [← MonoidHom.mem_ker, hker]
    exact Subgroup.mem_sup_right (NK.GlobalCFT.Idele.mem_principalSubgroup.mpr ⟨a, rfl⟩)
  have hloc : ∀ (v : NK.GlobalCFT.Place K) (a : (NK.GlobalCFT.Place.localField K v)ˣ),
      Φ (NK.HassePrinciple.onePlace v a) = 1 ↔
        a ∈ NK.CFTLib.IdeleHasse.localNormSubgroup (K := K) (L := L) v := by
    intro v a
    rw [← MonoidHom.mem_ker, hker]
    exact ⟨fun h => (NK.CFTLib.IdeleHasse.onePlace_mem_normImage_iff (K := K) (L := L) v a).mp
        (Work.SSGRoute.ZDataMup.localFaithful_abelian (K := K) (L := L) hcomm h),
      fun h => Subgroup.mem_sup_left
        ((NK.CFTLib.IdeleHasse.onePlace_mem_normImage_iff (K := K) (L := L) v a).mpr h)⟩
  exact ⟨Φ, hker, hnorm, hprin, hloc, hfrob, fun x s hs =>
    Work.SSGRoute.ZDataMup.cprod_localFactor_eq_one (K := K) (L := L) hcomm Φ hprin hnorm x s
      (fun v hv => hs v hv)⟩

end Work.SSGRoute.ZConstruction
