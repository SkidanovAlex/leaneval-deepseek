import Mathlib.RingTheory.Henselian
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Topology.Algebra.RestrictedProduct.Basic
import Submission.NK.CFTLib.Existence.artinMapOfARL
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The kernel of the idèlic Artin map is the norm class subgroup

Let `L / K` be a finite abelian extension of number fields and let `art : 𝕀 K →* Gal(L/K)` be an
idèlic Artin map which kills the principal idèles and the idèlic norms and is surjective (as
produced, from the ideal-theoretic reciprocity law, by
`NK.CFTLib.Existence.exists_ideleArtinMap_of_arl`).  From the global fundamental class `hFC` we
know that the norm index is the degree, `[C_K : N_{L/K}C_L] = [L:K]`; since `art` kills the norms
and is surjective, the Artin map on `C_K` that it induces has kernel exactly `N_{L/K} C_L`.

The main output is `NK.CFTLib.Existence.artinReciprocity_of_arl`: the Artin reciprocity
isomorphism `C_K ⧸ N_{L/K}C_L ≃* Gal(L/K)` from the ideal-theoretic reciprocity law together with
the fundamental class — the same object that `NK.GlobalCFTdeep.artinReciprocity_of_fundamentalClassElement`
produces from `hFC` alone, but here *realised at the level of the idèlic Artin map*, which is what
makes it possible to compare the Artin maps of the two levels of a tower.
-/

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

open scoped NumberField RestrictedProduct IsMulCommutative
open NumberField IsDedekindDomain

noncomputable section

namespace NK.CFTLib.Existence

open NK.GlobalCFT

variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [FiniteDimensional K L] [IsGalois K L] [IsMulCommutative (L ≃ₐ[K] L)]

/-- **The Artin map on the idèle class group** induced by an idèlic Artin map which kills the
principal idèles. -/
noncomputable def artinMapCK (art : Idele K →* Gal(L/K))
    (h : Idele.principalSubgroup K ≤ art.ker) : IdeleClassGroup K →* Gal(L/K) :=
  QuotientGroup.lift (Idele.principalSubgroup K) art h

/-- The value of `artinMapCK` on the class of an idèle. -/
theorem artinMapCK_mk (art : Idele K →* Gal(L/K))
    (h : Idele.principalSubgroup K ≤ art.ker) (x : Idele K) :
    artinMapCK art h (IdeleClassGroup.mk K x) = art x := by
  rw [IdeleClassGroup.mk_apply]
  exact QuotientGroup.lift_mk' (Idele.principalSubgroup K) h x

/-- **The kernel of the Artin map on `C_K` is the norm class subgroup**, given the fundamental
class. -/
theorem ker_artinMapCK_eq_normClassSubgroup (hFC : NK.GlobalCFTdeep.FundamentalClassElement)
    (art : Idele K →* Gal(L/K)) (h : Idele.principalSubgroup K ≤ art.ker)
    (hnorm : ∀ y : Idele L, art (Idele.normIdeleHom K L y) = 1)
    (hsurj : Function.Surjective art) :
    (artinMapCK art h).ker = Idele.normClassSubgroup K L := by
  have hrec : NK.GlobalCFT.ArtinReciprocity K L :=
    NK.GlobalCFTdeep.artinReciprocity_of_fundamentalClassElement hFC
  have hidxN : (Idele.normClassSubgroup K L).index = Module.finrank K L :=
    NK.GlobalCFT.index_normClassSubgroup_eq_finrank hrec
  -- the inclusion `N_{L/K}C_L ≤ ker`
  have hle : Idele.normClassSubgroup K L ≤ (artinMapCK art h).ker := by
    intro z hz
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hz
    rw [MonoidHom.mem_ker, artinMapCK_mk]
    rw [Idele.normImage_eq_map, MonoidHom.mem_range] at hx
    obtain ⟨y, hy⟩ := hx
    rw [← hy]
    exact hnorm y
  -- the index of the kernel is the cardinality of the Galois group
  have hsurj' : Function.Surjective (artinMapCK art h) := by
    intro g
    obtain ⟨x, hx⟩ := hsurj g
    exact ⟨IdeleClassGroup.mk K x, by rw [artinMapCK_mk, hx]⟩
  have hidxker : (artinMapCK art h).ker.index = Nat.card (L ≃ₐ[K] L) := by
    rw [Subgroup.index_ker, MonoidHom.range_eq_top.mpr hsurj', Subgroup.card_top]
  have hcard : Nat.card (L ≃ₐ[K] L) = Module.finrank K L := IsGalois.card_aut_eq_finrank K L
  -- equal indices and the inclusion force equality
  have hidx : (Idele.normClassSubgroup K L).index = (artinMapCK art h).ker.index := by
    rw [hidxN, hidxker, hcard]
  have hne : (artinMapCK art h).ker.index ≠ 0 := by
    rw [hidxker, hcard]
    exact (Module.finrank_pos (R := K) (M := L)).ne'
  have hrel : (Idele.normClassSubgroup K L).relIndex (artinMapCK art h).ker = 1 := by
    have hmul := Subgroup.relIndex_mul_index hle
    rw [hidx] at hmul
    exact Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero hne) (by rw [hmul, one_mul])
  exact le_antisymm
    ((Subgroup.relIndex_eq_one (H := Idele.normClassSubgroup K L)
      (K := (artinMapCK art h).ker)).mp hrel) hle

/-- **The Artin isomorphism realised by an idèlic Artin map.**

Given the idèlic Artin map `art` of a finite abelian extension `L / K` (killing the principal idèles
and the norms, surjective) and the fundamental class, the isomorphism
`C_K ⧸ N_{L/K}C_L ≃* Gal(L/K)` sends the class of an idèle `x` to `art x`.  This is the sharp form
of Artin reciprocity at the level of idèles: it pins down the *value* of the isomorphism on idèles,
which is what makes it possible to compare the Artin maps of two levels of a tower. -/
theorem exists_artinIso_of_ideleArtin (hFC : NK.GlobalCFTdeep.FundamentalClassElement)
    (art : Idele K →* Gal(L/K)) (h : Idele.principalSubgroup K ≤ art.ker)
    (hnorm : ∀ y : Idele L, art (Idele.normIdeleHom K L y) = 1)
    (hsurj : Function.Surjective art) :
    ∃ e : IdeleClassGroup K ⧸ Idele.normClassSubgroup K L ≃* Gal(L/K),
      ∀ x : Idele K,
        e (QuotientGroup.mk' (Idele.normClassSubgroup K L) (IdeleClassGroup.mk K x)) = art x := by
  have hker := ker_artinMapCK_eq_normClassSubgroup (K := K) (L := L) hFC art h hnorm hsurj
  have hsurjCK : Function.Surjective (artinMapCK art h) := by
    intro g
    obtain ⟨x, hx⟩ := hsurj g
    exact ⟨IdeleClassGroup.mk K x, by rw [artinMapCK_mk, hx]⟩
  let g : IdeleClassGroup K ⧸ Idele.normClassSubgroup K L →* Gal(L/K) :=
    QuotientGroup.lift (Idele.normClassSubgroup K L) (artinMapCK art h)
      (le_of_eq hker.symm)
  have hg : ∀ z : IdeleClassGroup K,
      g (QuotientGroup.mk' (Idele.normClassSubgroup K L) z) = artinMapCK art h z :=
    fun z => QuotientGroup.lift_mk' _ _ z
  have hsurjg : Function.Surjective g := by
    intro y
    obtain ⟨z, hz⟩ := hsurjCK y
    exact ⟨QuotientGroup.mk' (Idele.normClassSubgroup K L) z, by rw [hg, hz]⟩
  have hkerg : g.ker = ⊥ := by
    rw [QuotientGroup.ker_lift, hker, Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk']
  have hinjg : Function.Injective g := (MonoidHom.ker_eq_bot_iff g).mp hkerg
  have hval : ∀ x : Idele K,
      g (QuotientGroup.mk' (Idele.normClassSubgroup K L) (IdeleClassGroup.mk K x)) = art x := by
    intro x
    rw [hg, artinMapCK_mk]
  exact ⟨MulEquiv.ofBijective g ⟨hinjg, hsurjg⟩, hval⟩

end NK.CFTLib.Existence
