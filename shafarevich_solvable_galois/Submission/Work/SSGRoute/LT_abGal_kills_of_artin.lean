import Mathlib
import Submission.Work.SSGRoute.LT_LocalCFTUmbrella
import Submission.Work.SSGRoute.localKummerReciprocity
import Submission.Work.SSGRoute.exists_finiteDimensional_normal_fixingSubgroup_le
import Submission.NK.LocalCFT.NormGroup.normGroup_eq_iff
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# A locally constant character of `G_F^{ab}` killing `artin` is trivial

Let `F' / F` be a Galois extension carrying a local Artin reciprocity datum
`D : NK.LocalCFT.ArtinReciprocity F F'`, i.e. a canonical Artin map

`D.artin : Fˣ →* Gal(F^{ab}/F)`,   `F^{ab} = NK.LocalReciprocity.maxAbelianSubext F F'`,

whose composite with the restriction `Gal(F^{ab}/F) →* Gal(L/F)` is surjective with kernel
`N_{L/F} Lˣ` at every finite abelian level `L ≤ F^{ab}`.

**The statement.**  Every *locally constant* (equivalently, continuous) character
`χ : Gal(F^{ab}/F) →* 𝔽_p^*` which kills the image of `D.artin` is trivial.

**Why it is true.**  The image of `D.artin` is *dense* in `Gal(F^{ab}/F)` for the Krull topology:
given an open normal subgroup `U` and a finite normal level `L ≤ F^{ab}` with
`Gal(F^{ab}/L) ≤ U`, the level isomorphism at `L` supplies for every `g` a unit `a` with
`artin a ≡ g  (mod Gal(F^{ab}/L))`, hence `g ∈ U · artin(Fˣ)`.  Since `Gal(F^{ab}/F)` is abelian
(`NK.LocalReciprocity.commutative_gal_maxAbelianSubext`), every level `L ≤ F^{ab}` is an *abelian*
level and the reciprocity isomorphism applies.  A continuous character killing a dense subgroup is
trivial; here it suffices to apply the density to the single open normal subgroup
`U = ker χ` (open because `χ` is locally constant, normal because it is a kernel).

**Route.**  `χ.ker` is open (`IsLocallyConstant.isOpen_fiber`), so by the Krull topology it
contains the fixing subgroup of a finite normal level `L` of `F^{ab}`
(`Work.SSGRoute.exists_finiteDimensional_normal_fixingSubgroup_le`).  At that level the Artin map
`levelRestrict L ∘ D.artin` is onto `Gal(L/F)` (`D.isLevelIso`; the required commutativity of
`Gal(L/F)` is `NK.LocalCFT.NormGroup.normGroup_eq_iff_commutative_gal`).  Given `g`, choose `a`
with `levelRestrict L (D.artin a) = levelRestrict L g`; then
`D.artin a * g⁻¹ ∈ Gal(F^{ab}/L) = L.fixingSubgroup ≤ ker χ`, and `χ (D.artin a) = 1` by
hypothesis, so `χ g = 1`.
-/

set_option linter.style.haveILetI false

namespace Work.SSGRoute

/-- **Any locally constant character of `Gal(F^{ab}/F)` that kills the image of the Artin map is
trivial.**  Equivalently, the image of `D.artin` is dense in `Gal(F^{ab}/F)` for the Krull
topology. -/
theorem LT_abGal_kills_of_artin {F F' : Type} [Field F] [Field F'] [Algebra F F']
    [IsGalois F F'] (D : NK.LocalCFT.ArtinReciprocity F F') (p : ℕ) [Fact p.Prime]
    (χbar : ↥(Work.SSGRoute.lcHoms p (NK.LocalCFT.AbGal F F')))
    (h : ∀ a : Fˣ, χbar.1 (D.artin a) = 1) : χbar.1 = 1 := by
  haveI : IsGalois F (NK.LocalReciprocity.maxAbelianSubext F F') :=
    IsGalois.of_fixedField_normal_subgroup (commutator (F' ≃ₐ[F] F'))
  -- the kernel of `χ` is an open subgroup of `Gal(F^{ab}/F)`
  have hkerOpen : IsOpen ((χbar.1.ker : Subgroup (NK.LocalCFT.AbGal F F')) :
      Set (NK.LocalCFT.AbGal F F')) := by
    have hset : ((χbar.1.ker : Subgroup (NK.LocalCFT.AbGal F F')) :
        Set (NK.LocalCFT.AbGal F F')) = {g | χbar.1 g = 1} :=
      Set.ext fun g => MonoidHom.mem_ker.symm
    rw [hset]
    exact χbar.2.isOpen_fiber 1
  -- Krull topology: it contains the fixing subgroup of a finite normal level `L ≤ F^{ab}`
  obtain ⟨L, hLfin, hLnorm, hLle⟩ :=
    Work.SSGRoute.exists_finiteDimensional_normal_fixingSubgroup_le χbar.1.ker hkerOpen
  haveI : FiniteDimensional F ↥L := hLfin
  haveI : Normal F ↥L := hLnorm
  -- every normal level of `F^{ab}` is abelian over `F`, so the reciprocity datum applies to it
  have hcomm := NK.LocalCFT.NormGroup.normGroup_eq_iff_commutative_gal (F := F) (F' := F') L
  have hsurj : Function.Surjective ((NK.LocalCFT.levelRestrict L).comp D.artin) :=
    (D.isLevelIso L hcomm).1
  refine MonoidHom.ext fun g => ?_
  -- `g` differs from an element of the image of `artin` by an element of `Gal(F^{ab}/L) ≤ ker χ`
  obtain ⟨a, ha⟩ := hsurj (NK.LocalCFT.levelRestrict L g)
  have hmem : D.artin a * g⁻¹ ∈ χbar.1.ker := by
    refine hLle ?_
    rw [← IntermediateField.restrictNormalHom_ker L, MonoidHom.mem_ker]
    show NK.LocalCFT.levelRestrict L (D.artin a * g⁻¹) = 1
    rw [map_mul, map_inv]
    rw [show NK.LocalCFT.levelRestrict L (D.artin a) = NK.LocalCFT.levelRestrict L g from ha,
      mul_inv_cancel]
  have h2 : χbar.1 g⁻¹ = 1 := by
    simpa [map_mul, h a] using MonoidHom.mem_ker.mp hmem
  have := congrArg Inv.inv h2
  simpa [map_inv] using this

end Work.SSGRoute
