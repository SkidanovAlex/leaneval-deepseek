/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Area CH — route B of COV′: **POINT** (the VALUE direction of the graph of the residue map)

This file proves `Work.Charts.exists_V_of_landsIn_Wp`: a field point `p` of `Sym^{g+g} C`
landing in `W′ := dom ρ ∩ ρ⁻¹(V)` has a representative `y ∈ V` with
`divOf y ~ divOf p − g·P₀`.

The proof is the VALUE theorem of RESID (`Work.Domain.Resid.residMap_value`) applied to
`ρ = D.residMap a 𝟙 le_rfl`, together with the identification of the value of `ρ` at `p`
with the composite of the factorisation of `p` through `dom ρ` with `ρ.hom`
(`Work.Domain.Resid.valueOf_left_eq`).  The hypothesis that `p` lands in `W′` provides both
the fact that `p` lies in the domain of `ρ` and the fact that the value lies in the chart `V`.
-/
import Mathlib
import Submission.Work.Charts.Step3Defs
import Submission.Work.Domain.Resid.residMap_value

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.style.haveILetI false
set_option linter.unusedTactic false

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory AlgebraicGeometry
open scoped Classical AlgebraicGeometry MonoidalCategory
open scoped Work.GCBasics
open Work.GCBasics

universe u

namespace Work.Charts

noncomputable section

theorem exists_V_of_landsIn_Wp {K : Type u} [Field K] {C : Work.CurveBasics.Curve K}
    [Work.SpecLin.DivBase C] (R : Work.Charts.RochData C)
    (symGeom : ∀ n, Work.SpecLin.SymGeom C n)
    (D : Work.Domain.Resid.ResidData (K := K) symGeom R.g)
    (G : Work.Charts.Step3Geo R symGeom)
    (a : (symGeom (R.g + R.g)).S ⟶ (symGeom R.g).S) {P0Div : Work.GCBasics.Dv C K}
    (ha : ∀ {F : Type u} [Field F] [Algebra K F]
      (p : Work.GCBasics.FPt ((symGeom (R.g + R.g)).S) F),
      (symGeom R.g).divOf (Work.Charts.ptComp p a) =
        (R.g : ℤ) • Work.Charts.pullK C P0Div)
    (d : Work.Charts.BNDataAt R symGeom)
    {F : Type u} [Field F] [Algebra K F] (p : Work.GCBasics.FPt ((symGeom (R.g + R.g)).S) F)
    (hp : Work.GCBasics.RPt.LandsIn p (Work.Charts.Wp R symGeom D G a d)) :
    ∃ y : Work.GCBasics.FPt ((symGeom R.g).S) F, Work.GCBasics.RPt.LandsIn y d.V ∧
      Work.GCBasics.LinEquiv C ((symGeom R.g).divOf y)
        ((symGeom (R.g + R.g)).divOf p - (R.g : ℤ) • Work.Charts.pullK C P0Div) := by
  classical
  -- the instances carried by the geometric hypotheses
  haveI hInt : IsIntegral ((symGeom (R.g + R.g)).S).left := G.integral_gg
  haveI hRed : IsReduced ((symGeom (R.g + R.g)).S).left :=
    isReduced_of_isIntegral ((symGeom (R.g + R.g)).S).left
  haveI hLft : LocallyOfFiniteType ((symGeom (R.g + R.g)).S).hom := D.locallyOfFiniteType _
  haveI hLN : IsLocallyNoetherian ((symGeom (R.g + R.g)).S).left :=
    LocallyOfFiniteType.isLocallyNoetherian ((symGeom (R.g + R.g)).S).hom
  haveI hSep : IsSeparated ((symGeom R.g).S).hom := G.separated_g
  -- the point of `Spec F` underlying `p` lands in the image open `dom ρ` `''ᵁ` `ρ⁻¹V`
  have hmem : p.left (IsLocalRing.closedPoint F) ∈
      ((rho R symGeom D G a).domain.ι ''ᵁ
        ((rho R symGeom D G a).toPartialMap.hom ⁻¹ᵁ d.V) :
        ((symGeom (R.g + R.g)).S).left.Opens) := hp
  have hle : (rho R symGeom D G a).domain.ι ''ᵁ
      ((rho R symGeom D G a).toPartialMap.hom ⁻¹ᵁ d.V) ≤ (rho R symGeom D G a).domain :=
    Scheme.Opens.ι_image_le _ _
  -- hence `p` lands in the domain of `ρ`, and the corresponding point of the domain lies in `V`
  have hxdom : p.left (IsLocalRing.closedPoint F) ∈ (rho R symGeom D G a).domain :=
    hle hmem
  let x₀ : ↑(rho R symGeom D G a).domain := ⟨p.left (IsLocalRing.closedPoint F), hxdom⟩
  have hx₀Vmem : x₀ ∈ ((rho R symGeom D G a).toPartialMap.hom ⁻¹ᵁ d.V) :=
    (Scheme.Opens.mem_ι_image_iff (rho R symGeom D G a).domain).mp hmem
  have hx₀V : (rho R symGeom D G a).toPartialMap.hom x₀ ∈ d.V := hx₀Vmem
  have hx₀ι : (rho R symGeom D G a).domain.ι x₀ = p.left (IsLocalRing.closedPoint F) := rfl
  have hpdom : RPt.LandsIn p (rho R symGeom D G a).domain := hxdom
  have hσ : (rho R symGeom D G a).IsOver (Spec (CommRingCat.of K)) :=
    D.residMap_isOver a (𝟙 _) le_rfl
  -- factor `p` through the domain of `ρ`
  obtain ⟨q, hq, -⟩ := RPt.factor_of_closed_landsIn
    (rho R symGeom D G a).toPartialMap.domain p hpdom
  have hydef : (Work.Domain.Resid.valueOf hRed hSep (rho R symGeom D G a) hσ p hpdom).left
      = q.left ≫ (rho R symGeom D G a).toPartialMap.hom :=
    Work.Domain.Resid.valueOf_left_eq hRed hSep (rho R symGeom D G a) hσ p hpdom q hq
  -- the value of `ρ` at `p` is the required representative
  refine ⟨Work.Domain.Resid.valueOf hRed hSep (rho R symGeom D G a) hσ p hpdom, ?_, ?_⟩
  · -- it lands in the chart `V`
    rw [RPt.landsIn_iff]
    rw [hydef]
    rw [Scheme.Hom.comp_apply]
    have hqpt : (rho R symGeom D G a).domain.ι (q.left (IsLocalRing.closedPoint F))
        = p.left (IsLocalRing.closedPoint F) := by
      have h := congrArg Over.Hom.left hq
      rw [Over.comp_left, Opens.ιOver_left] at h
      exact congrArg (fun f => f (IsLocalRing.closedPoint F)) h
    have hqeq : q.left (IsLocalRing.closedPoint F) = x₀ := by
      apply Subtype.val_injective
      exact hqpt.trans hx₀ι.symm
    rw [hqeq]
    exact hx₀V
  · -- and VALUE of RESID gives the linear equivalence
    have hrel : Work.Domain.Resid.Rel symGeom a (𝟙 ((symGeom (R.g + R.g)).S)) p
        (Work.Domain.Resid.valueOf hRed hSep (rho R symGeom D G a) hσ p hpdom) :=
      Work.Domain.Resid.residMap_value D G.hstalk hRed hSep a (𝟙 _) le_rfl p hpdom
    rw [Work.Domain.Resid.rel_iff] at hrel
    rw [Work.Domain.Resid.divD] at hrel
    rw [Category.comp_id] at hrel
    rw [show (symGeom R.g).divOf (p ≫ a) = (R.g : ℤ) • Work.Charts.pullK C P0Div
      from ha p] at hrel
    exact hrel

end

end Work.Charts
