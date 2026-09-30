import Mathlib

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


set_option linter.style.haveILetI false

namespace Work.Normality

/-- The fixed points of a finite group acting on an integrally closed domain are again
integrally closed.

Proof sketch: put `R := FixedPoints.subring B G` and `L := FractionRing B`, with the action of
`G` on `L` given by `IsFractionRing.mulSemiringAction G B L` (compatible with `B → L`); let
`ψ : FractionRing R →+* L` be `IsFractionRing.lift` (with `R → L` injective), so that
`ψ (algebraMap R _ a) = algebraMap R L a`, and `ψ` is injective.  If `x : FractionRing R` is
integral over `R`, then `ψ x` is integral over `R`, hence over `B`, hence lies in `B`
(`IsIntegrallyClosed B`); writing `x = a / b` with `a b : R` (`IsFractionRing.div_surjective`)
and using that elements of `R = B^G` are fixed by `G`, one gets that `ψ x` is fixed by `G`;
hence `ψ x = algebraMap R L r` for some `r : R` (`Algebra.IsInvariant.isInvariant` for
`R = B^G` inside `B`), and injectivity of `ψ` gives
`x = algebraMap R (FractionRing R) r`. -/
theorem isIntegrallyClosed_invariants {B : Type*} [CommRing B] [IsDomain B] [IsIntegrallyClosed B]
    (G : Type*) [Group G] [Finite G] [MulSemiringAction G B] :
    IsIntegrallyClosed (FixedPoints.subring B G) := by
  -- `L` is the fraction field of `B`, and `G` acts on it compatibly with `B → L`.
  let L := FractionRing B
  letI : MulSemiringAction G L := IsFractionRing.mulSemiringAction G B L
  haveI : SMulDistribClass G B L := IsFractionRing.smulDistribClass G B L
  -- Elements of `R = B^G` are fixed by `G`.
  have hfix : ∀ (g : G) (r : FixedPoints.subring B G),
      g • (algebraMap (FixedPoints.subring B G) L r) = algebraMap (FixedPoints.subring B G) L r := by
    intro g r
    rw [IsScalarTower.algebraMap_apply (FixedPoints.subring B G) B L]
    rw [← algebraMap.coe_smul' g (algebraMap (FixedPoints.subring B G) B r) L]
    congr 1
    exact r.2 g
  -- The canonical map `R → L`.
  have hg : Function.Injective (algebraMap (FixedPoints.subring B G) L) := by
    rw [IsScalarTower.algebraMap_eq (FixedPoints.subring B G) B L]
    exact (IsFractionRing.injective B L).comp Subtype.val_injective
  let ψ : FractionRing (FixedPoints.subring B G) →+* L := IsFractionRing.lift hg
  have hψ : ∀ r, ψ (algebraMap (FixedPoints.subring B G) (FractionRing (FixedPoints.subring B G)) r)
      = algebraMap (FixedPoints.subring B G) L r :=
    fun r => IsFractionRing.lift_algebraMap hg r
  have hψinj : Function.Injective ψ := RingHom.injective ψ
  rw [isIntegrallyClosed_iff (K := FractionRing (FixedPoints.subring B G))]
  intro x hx
  -- `ψ x` is integral over `R`, hence over `B`.
  have hxψ : IsIntegral (FixedPoints.subring B G) (ψ x) :=
    IsIntegral.map_of_comp_eq (R := FixedPoints.subring B G)
      (S := FractionRing (FixedPoints.subring B G)) (T := FixedPoints.subring B G) (U := L)
      (RingHom.id _) ψ (by ext r; simp [hψ]) hx
  have hxψB : IsIntegral B (ψ x) := hxψ.tower_top
  -- `B` is integrally closed, so `ψ x` is (the image of) an element of `B`.
  obtain ⟨b, hb⟩ := IsIntegrallyClosed.algebraMap_eq_of_integral (R := B) (K := L) hxψB
  -- `ψ x` is fixed by `G`.
  have hψfix : ∀ g : G, g • ψ x = ψ x := by
    intro g
    have hρ : (MulSemiringAction.toRingEquiv G L g).toRingHom.comp ψ = ψ := by
      apply IsFractionRing.ringHom_ext (A := FixedPoints.subring B G)
      intro r
      simp only [RingHom.comp_apply]
      rw [hψ r]
      exact hfix g r
    have h2 := congr_fun (congr_arg DFunLike.coe hρ) x
    simpa [MulSemiringAction.toRingEquiv_apply_apply] using h2
  -- hence `b` is fixed by `G`, i.e. lies in `R`.
  have hbfix : ∀ g : G, g • b = b := by
    intro g
    apply IsFractionRing.injective B L
    calc (algebraMap B L) (g • b) = g • ((algebraMap B L) b) := algebraMap.coe_smul' g b L
      _ = g • ψ x := by rw [hb]
      _ = ψ x := hψfix g
      _ = (algebraMap B L) b := hb.symm
  refine ⟨⟨b, hbfix⟩, ?_⟩
  -- injectivity of `ψ` reduces the goal to `ψ (algebraMap R _ r) = ψ x`
  apply hψinj
  rw [hψ]
  rw [IsScalarTower.algebraMap_apply (FixedPoints.subring B G) B L]
  change algebraMap B L b = ψ x
  exact hb

end Work.Normality
