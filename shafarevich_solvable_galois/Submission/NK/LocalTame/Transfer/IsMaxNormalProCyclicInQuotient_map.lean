import Mathlib.FieldTheory.Normal.Defs
import Submission.NK.LocalTame.Basic
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

set_option linter.style.haveILetI false

namespace NK.LocalTame.Transfer

open NK.LocalTame

/-! ## A universe-polymorphic form of pro-cyclicity invariance

`NK.LocalTame.isProCyclic_congr` compares two groups living in the *same* universe.  In the
transport below the two quotients are `G ⧸ V` and `H ⧸ V'` for `G` and `H` in a priori different
universes (the theorems are stated with `Type*`), so we need the general form.  The proof is
identical to `isProCyclic_congr`: pull back along `e` a normal finite index subgroup of the
target, and compare the corresponding quotients by `QuotientGroup.congr`. -/

/-- **Pro-cyclicity is invariant under a group isomorphism**, universe-polymorphically. -/
theorem isProCyclic_congr_uv {A : Type*} {B : Type*} [Group A] [Group B] (e : A ≃* B) :
    IsProCyclic A ↔ IsProCyclic B := by
  constructor
  · intro h N hN hfi
    haveI : (N.comap (e : A →* B)).Normal := Subgroup.Normal.comap hN _
    have hfin : (N.comap (e : A →* B)).FiniteIndex := by
      rw [Subgroup.finiteIndex_iff,
        Subgroup.index_comap_of_surjective (f := (e : A →* B)) N e.surjective]
      exact (Subgroup.finiteIndex_iff (H := N)).mp hfi
    exact (QuotientGroup.congr (N.comap (e : A →* B)) N e
      (Subgroup.map_comap_eq_self_of_surjective e.surjective N)).isCyclic.mp (h _ hfin)
  · intro h N hN hfi
    haveI : (N.map (e : A →* B)).Normal := hN.map _ e.surjective
    have hfin : (N.map (e : A →* B)).FiniteIndex := by
      rw [Subgroup.finiteIndex_iff, Subgroup.index_map_equiv N e]
      exact (Subgroup.finiteIndex_iff (H := N)).mp hfi
    exact (QuotientGroup.congr N (N.map (e : A →* B)) e rfl).isCyclic.mpr (h _ hfin)

/-! ## The transport -/

theorem IsMaxNormalProCyclicInQuotient_map {G H : Type*} [Group G] [Group H] {V I : Subgroup G}
    [V.Normal] (h : IsMaxNormalProCyclicInQuotient V I) (e : G ≃* H) {V' : Subgroup H}
    [V'.Normal] (hV : V.map (e : G →* H) = V') :
    IsMaxNormalProCyclicInQuotient V' (I.map (e : G →* H)) := by
  obtain ⟨hVI, hnorm, hcyc, hmax⟩ := h
  -- the induced isomorphism of the two quotients
  let φ : G ⧸ V ≃* H ⧸ V' := QuotientGroup.congr V V' e hV
  -- `φ` is induced by `e`: it carries `mk' V x` to `mk' V' (e x)`
  have hcomp : (φ : G ⧸ V →* H ⧸ V').comp (QuotientGroup.mk' V)
      = (QuotientGroup.mk' V').comp (e : G →* H) := by
    ext x
    rfl
  -- consequently it carries the quotient-image of `J` to the quotient-image of `J.map e`
  have key : ∀ J : Subgroup G, V ≤ J →
      (quotientImage V J).map (φ : G ⧸ V →* H ⧸ V') =
        quotientImage V' (J.map (e : G →* H)) := by
    intro J _
    rw [quotientImage, quotientImage, Subgroup.map_map, Subgroup.map_map, hcomp]
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- `V' ≤ I.map e`
    rw [← hV]
    exact Subgroup.map_mono hVI
  · -- normality of `I.map e / V'`
    rw [← key I hVI]
    exact hnorm.map (φ : G ⧸ V →* H ⧸ V') φ.surjective
  · -- pro-cyclicity of `I.map e / V'`
    rw [← key I hVI]
    exact (isProCyclic_congr_uv (Subgroup.equivMapOfInjective (quotientImage V I)
      (φ : G ⧸ V →* H ⧸ V') φ.injective)).mp hcyc
  · -- maximality: a normal pro-cyclic `J' ≥ V'` is contained in `I.map e`
    intro J' hV'J' hJn hJc
    -- pull `J'` back along `e`
    let J : Subgroup G := J'.comap (e : G →* H)
    have hVJ : V ≤ J := by
      rw [← Subgroup.map_le_iff_le_comap, hV]
      exact hV'J'
    have hJmap : J.map (e : G →* H) = J' :=
      Subgroup.map_comap_eq_self_of_surjective e.surjective J'
    have hkey := key J hVJ
    rw [hJmap] at hkey
    -- `J/V` inherits normality and pro-cyclicity from `J'/V'`
    have hJn' : (quotientImage V J).Normal := by
      apply Subgroup.Normal.of_map_injective (φ := (φ : G ⧸ V →* H ⧸ V')) φ.injective
      rwa [hkey]
    have hJc' : IsProCyclic ↥(quotientImage V J) :=
      (isProCyclic_congr_uv ((Subgroup.equivMapOfInjective (quotientImage V J)
        (φ : G ⧸ V →* H ⧸ V') φ.injective).trans
          (MulEquiv.subgroupCongr hkey))).mpr hJc
    have hJI : J ≤ I := hmax J hVJ hJn' hJc'
    rw [← hJmap]
    exact Subgroup.map_mono hJI

end NK.LocalTame.Transfer
