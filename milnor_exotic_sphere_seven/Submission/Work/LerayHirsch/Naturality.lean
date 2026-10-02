import Mathlib
import Submission.Work.LerayHirsch.TautLine
import Submission.Work.Thom.continuous_totalSpaceMap_field

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option linter.unusedSectionVars false

/-!
# Functoriality of the projectivisation

The projectivisation is functorial: a pullback of gluing data `f^*Z` over `B'` has projectivisation
`P(f^*Z)`, and there is a canonical continuous map

```lean
Work.LerayHirsch.projMapComap Z f : C(ProjSpace (bundleComap Z f), ProjSpace Z)
```

sending the class of a point `p = (b', v)` of the punctured total space of `f^*Z` to the class of
`(f b', v)` in `P(Z)`.  This is the map along which the tautological line bundle and the class
`ζ = c₁(ℓ)` are natural, and it is the map that the Mayer–Vietoris induction of
`Work.LerayHirsch.LerayHirschGlue` restricts along (for `f` the inclusion of an open set it is the
homeomorphism `Work.LerayHirsch.nonempty_homeo_projSpace_bundleComap_subtype`).
-/

namespace Work.LerayHirsch

open Work.TangentClasses Work.Thom

open scoped LinearAlgebra.Projectivization

noncomputable section

variable {B B' : Type} [TopologicalSpace B] [TopologicalSpace B'] {ι : Type} {m : ℕ}

/-- The total-space map `p ↦ ⟨f p.1, p.2⟩` of the pullback of gluing data, as an element of the
punctured total space of `Z`. -/
def punctComap (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι) (f : C(B', B))
    (p : ↥(zeroComplement (realification (bundleComap Z f)))) :
    ↥(zeroComplement (realification Z)) :=
  ⟨(⟨f p.1.proj, (show EuclideanSpace ℂ (Fin m) from p.1.2)⟩ : (realification Z).TotalSpace),
    by rw [mem_zeroComplement]; exact p.2⟩

theorem punctComap_smulPunct (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι)
    (f : C(B', B)) (c : ℂˣ)
    (p : ↥(zeroComplement (realification (bundleComap Z f)))) :
    punctComap Z f (smulPunct (bundleComap Z f) c p) = smulPunct Z c (punctComap Z f p) := by
  refine Subtype.ext (Bundle.TotalSpace.ext ?_ ?_)
  · show f ((smulPunct (bundleComap Z f) c p).1.proj) = f (p.1.proj)
    rw [smulPunct_proj]
  · refine heq_of_eq ?_
    show (show EuclideanSpace ℂ (Fin m) from
        (punctComap Z f (smulPunct (bundleComap Z f) c p)).1.2)
      = (show EuclideanSpace ℂ (Fin m) from (smulPunct Z c (punctComap Z f p)).1.2)
    rw [smulPunct_snd]
    rfl

/-- **Functoriality of the projectivisation**: the canonical map
`P(f^*E) → P(E)`, `[p] ↦ [⟨f p.1, p.2⟩]`. -/
def projMapComap (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι) (f : C(B', B)) :
    C(ProjSpace (bundleComap Z f), ProjSpace Z) where
  toFun := Quotient.lift (fun p => mkProj Z (punctComap Z f p)) (by
    intro p q h
    obtain ⟨c, hc⟩ := h
    rw [← hc, punctComap_smulPunct, mkProj_eq_iff]
    exact ⟨c, rfl⟩)
  continuous_toFun := by
    rw [isQuotientMap_quotient_mk'.continuous_iff]
    have htot : Continuous (fun p : (realification (bundleComap Z f)).TotalSpace =>
        (⟨f p.1, p.2⟩ : (realification Z).TotalSpace)) :=
      continuous_totalSpaceMap_field (realification (bundleComap Z f)) (realification Z) f
        (fun i => by rw [realification_bundleComap, bundleComap_baseSet])
        (fun x i => by
          rw [realification_bundleComap, bundleComap_coordChange, bundleComap_indexAt])
    refine (continuous_mkProj Z).comp ((htot.comp continuous_subtype_val).subtype_mk ?_)
    intro p
    rw [mem_zeroComplement]
    exact p.2

@[simp] theorem projMapComap_mkProj (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι)
    (f : C(B', B)) (p : ↥(zeroComplement (realification (bundleComap Z f)))) :
    projMapComap Z f (mkProj (bundleComap Z f) p)
      = mkProj Z ⟨(⟨f p.1.proj, (show EuclideanSpace ℂ (Fin m) from p.1.2)⟩ :
          (realification Z).TotalSpace), by rw [mem_zeroComplement]; exact p.2⟩ := rfl

/-- The computation rule of `Work.LerayHirsch.projMapComap`. -/
@[simp] theorem projMapComap_mkProj_apply (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι)
    (f : C(B', B)) (p : ↥(zeroComplement (realification (bundleComap Z f)))) :
    projMapComap Z f (mkProj (bundleComap Z f) p) = mkProj Z (punctComap Z f p) := rfl

/-- **The projections are compatible**: `π_{P(E)} ∘ P(f) = f ∘ π_{P(f^*E)}`. -/
theorem projMap_projMapComap (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι)
    (f : C(B', B)) (x : ProjSpace (bundleComap Z f)) :
    projMap Z (projMapComap Z f x) = f (projMap (bundleComap Z f) x) := by
  obtain ⟨p, rfl⟩ := surjective_mkProj (bundleComap Z f) x
  rfl

/-- **Functoriality**: `P``(g^*f^*E) → P(f^*E) → P(E)` is `P((f ∘ g)^*E) → P(E)`. -/
theorem projMapComap_comp {B'' : Type} [TopologicalSpace B'']
    (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι) (f : C(B', B)) (g : C(B'', B'))
    (x : ProjSpace (bundleComap (bundleComap Z f) g)) :
    projMapComap Z f (projMapComap (bundleComap Z f) g x)
      = projMapComap Z (f.comp g)
          (cast (congrArg (fun W => ProjSpace W) (bundleComap_comp Z f g).symm) x) := by
  obtain ⟨p, rfl⟩ := surjective_mkProj (bundleComap (bundleComap Z f) g) x
  rfl

end

end Work.LerayHirsch
