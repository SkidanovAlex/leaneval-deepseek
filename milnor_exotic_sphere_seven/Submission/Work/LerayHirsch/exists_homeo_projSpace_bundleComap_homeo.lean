import Mathlib
import Submission.Work.LerayHirsch.Punctum
import Submission.Work.LerayHirsch.Naturality
import Submission.Work.Thom.continuous_totalSpaceMap_field
import Submission.Work.LerayHirsch.nonempty_homeo_projSpace_bundleComap_subtype

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-!
# Functoriality of the projectivisation, II: a homeomorphism of the base

`Work.LerayHirsch.projMapComap Z f : P(f^*E) → P(E)` is the functoriality map of the
projectivisation.  For an *open embedding* `f` it is a homeomorphism onto the piece of `P(E)` over
the image (`Submission/Work/LerayHirsch/nonempty_homeo_projSpace_bundleComap_subtype.lean`), and
here we prove the same for a **homeomorphism** `e : B' ≃ₜ B` of the bases:

  `Work.LerayHirsch.exists_homeo_projSpace_bundleComap_homeo`:
  `projMapComap Z e : P(e^*E) ≃ₜ P(E)`.

This is what allows the whole Leray–Hirsch chapter to be transported along a change of the base
space (the tautological line bundle, `ζ`, the Leray–Hirsch property and the Chern class
computations all pull back along a homeomorphism of the base).

## The route

The `ℂˣ`-action on the punctured total space is natural, so the projectivisation is the quotient of
the punctured total space; the functoriality map is induced by the map `punctComap Z e` on punctured
total spaces.  For `e` a homeomorphism this map is a **homeomorphism**

  `Work.LerayHirsch.punctComapHomeo Z e : E∖0|_{e^*E} ≃ₜ E∖0`,

because its inverse is the evident map `⟨b, v⟩ ↦ ⟨e.symm b, v⟩`, which is continuous by the
general continuity criterion for total-space maps of bundle morphisms
(`Work.Thom.continuous_totalSpaceMap_field`, applied in both directions).  Passing to quotients by
the `ℂˣ`-action (continuous, `ℂˣ`-equivariant, bijective, and a quotient map as a homeomorphism)
gives the statement, exactly as in the open-embedding case.
-/

namespace Work.LerayHirsch

open Work.TangentClasses Work.Thom

noncomputable section

variable {B B' : Type} [TopologicalSpace B] [TopologicalSpace B'] {ι : Type} {m : ℕ}

/-! ## The inverse of `punctComap` along a homeomorphism of the base -/

/-- The transition functions of `realification Z` pulled back along `e.symm` are those of
`realification (e^*Z)`: this is the base-set form needed to apply the continuity criterion for
total-space maps to the inverse of `punctComap`. -/
theorem comap_symm_baseSet (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι)
    (e : B' ≃ₜ B) (i : ι) :
    (realification Z).baseSet i
      = (e.symm : C(B, B')) ⁻¹' (realification (bundleComap Z (e : C(B', B)))).baseSet i := by
  rw [realification_bundleComap, bundleComap_baseSet]
  ext b
  simp

/-- The same for the coordinate changes. -/
theorem comap_symm_coordChange (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι)
    (e : B' ≃ₜ B) (i : ι) (x : B) :
    (realification Z).coordChange ((realification Z).indexAt x) i x
      = (realification (bundleComap Z (e : C(B', B)))).coordChange
          ((realification (bundleComap Z (e : C(B', B)))).indexAt ((e.symm : C(B, B')) x)) i
          ((e.symm : C(B, B')) x) := by
  rw [realification_bundleComap, bundleComap_coordChange, bundleComap_indexAt]
  simp

/-- The map `⟨b, v⟩ ↦ ⟨e.symm b, v⟩` on the punctured total spaces; the inverse of
`punctComap Z e`. -/
def punctComapInv (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι) (e : B' ≃ₜ B) :
    ↥(zeroComplement (realification Z)) →
      ↥(zeroComplement (realification (bundleComap Z (e : C(B', B))))) :=
  fun p => ⟨⟨(e.symm) p.1.proj, (show EuclideanSpace ℂ (Fin m) from p.1.2)⟩, by
    rw [mem_zeroComplement]; exact p.2⟩

theorem continuous_punctComapInv (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι)
    (e : B' ≃ₜ B) : Continuous (punctComapInv Z e) := by
  have htot : Continuous (fun p : (realification Z).TotalSpace =>
      (⟨(e.symm) p.1, p.2⟩ : (realification (bundleComap Z (e : C(B', B)))).TotalSpace)) :=
    continuous_totalSpaceMap_field (realification Z)
      (realification (bundleComap Z (e : C(B', B)))) (e.symm : C(B, B'))
      (fun i => comap_symm_baseSet Z e i) (fun x i => comap_symm_coordChange Z e i x)
  exact Continuous.subtype_mk (htot.comp continuous_subtype_val) _

/-! ## `punctComap` is continuous -/

/-- `punctComap Z f`, the map on punctured total spaces underlying the functoriality map of the
projectivisation, is continuous. -/
theorem continuous_punctComap (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι)
    (f : C(B', B)) : Continuous (punctComap Z f) := by
  have htot : Continuous (fun p : (realification (bundleComap Z f)).TotalSpace =>
      (⟨f p.1, p.2⟩ : (realification Z).TotalSpace)) :=
    continuous_totalSpaceMap_field (realification (bundleComap Z f)) (realification Z) f
      (fun i => by rw [realification_bundleComap, bundleComap_baseSet])
      (fun x i => by rw [realification_bundleComap, bundleComap_coordChange, bundleComap_indexAt])
  exact Continuous.subtype_mk (htot.comp continuous_subtype_val) _

/-! ## The punctured total space of a pullback along a homeomorphism -/

/-- **The punctured total space of the pullback along a homeomorphism of the base is the
punctured total space**: `punctComap Z e` is a homeomorphism, its inverse being
`⟨b, v⟩ ↦ ⟨e.symm b, v⟩`. -/
def punctComapHomeo (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι) (e : B' ≃ₜ B) :
    ↥(zeroComplement (realification (bundleComap Z (e : C(B', B))))) ≃ₜ
      ↥(zeroComplement (realification Z)) where
  toFun := punctComap Z (e : C(B', B))
  invFun := punctComapInv Z e
  left_inv := fun p => by
    refine Subtype.ext (Bundle.TotalSpace.ext ?_ ?_)
    · exact e.symm_apply_apply p.1.proj
    · rfl
  right_inv := fun p => by
    refine Subtype.ext (Bundle.TotalSpace.ext ?_ ?_)
    · exact e.apply_symm_apply p.1.proj
    · rfl
  continuous_toFun := continuous_punctComap Z (e : C(B', B))
  continuous_invFun := continuous_punctComapInv Z e

@[simp] theorem punctComapHomeo_apply (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι)
    (e : B' ≃ₜ B) (p : ↥(zeroComplement (realification (bundleComap Z (e : C(B', B)))))) :
    punctComapHomeo Z e p = punctComap Z (e : C(B', B)) p := rfl

/-- The homeomorphism is `ℂˣ`-equivariant, so it descends to the projectivisations. -/
theorem punctComapHomeo_smulPunct (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι)
    (e : B' ≃ₜ B) (c : ℂˣ)
    (x : ↥(zeroComplement (realification (bundleComap Z (e : C(B', B)))))) :
    punctComapHomeo Z e (smulPunct (bundleComap Z (e : C(B', B))) c x)
      = smulPunct Z c (punctComapHomeo Z e x) :=
  punctComap_smulPunct Z (e : C(B', B)) c x

/-! ## The main statement -/

/-- **The projectivisation of a pullback along a homeomorphism of the base**: for `e : B' ≃ₜ B` the
functoriality map `projMapComap Z e : P(e^*E) → P(E)` is a homeomorphism. -/
theorem exists_homeo_projSpace_bundleComap_homeo {B B' : Type} [TopologicalSpace B]
    [TopologicalSpace B'] {ι : Type} {m : ℕ}
    (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι) (e : B' ≃ₜ B) :
    ∃ φ : Work.LerayHirsch.ProjSpace (Work.Thom.bundleComap Z (e : C(B', B))) ≃ₜ
        Work.LerayHirsch.ProjSpace Z,
      ⇑φ = ⇑(Work.LerayHirsch.projMapComap Z (e : C(B', B))) := by
  -- The composite `P(e^*E) → P(E)` is induced by the homeomorphism on punctured total spaces.
  have hkey : ∀ a : ↥(zeroComplement (realification (bundleComap Z (e : C(B', B))))),
      (projMapComap Z (e : C(B', B))) (mkProj (bundleComap Z (e : C(B', B))) a)
        = mkProj Z (punctComapHomeo Z e a) := by
    intro a
    rw [projMapComap_mkProj_apply, punctComapHomeo_apply]
  have hcomp : Topology.IsQuotientMap
      ((projMapComap Z (e : C(B', B))) ∘ (mkProj (bundleComap Z (e : C(B', B))))) := by
    have heq : ((projMapComap Z (e : C(B', B))) ∘ (mkProj (bundleComap Z (e : C(B', B)))))
        = ((mkProj Z) ∘ (punctComapHomeo Z e)) := funext hkey
    rw [heq]
    exact (isQuotientMap_quotient_mk' (s := projSetoid Z)).comp (punctComapHomeo Z e).isQuotientMap
  have hinj : Function.Injective (projMapComap Z (e : C(B', B))) := by
    intro p q hpq
    obtain ⟨a, rfl⟩ := surjective_mkProj (bundleComap Z (e : C(B', B))) p
    obtain ⟨b, rfl⟩ := surjective_mkProj (bundleComap Z (e : C(B', B))) q
    rw [hkey a, hkey b] at hpq
    obtain ⟨c, hc⟩ := (mkProj_eq_iff Z).mp hpq
    refine (mkProj_eq_iff (bundleComap Z (e : C(B', B)))).mpr ⟨c, ?_⟩
    apply (punctComapHomeo Z e).injective
    rw [punctComapHomeo_smulPunct]
    exact hc
  have hsurj : Function.Surjective (projMapComap Z (e : C(B', B))) := by
    intro y
    obtain ⟨x, hx⟩ := surjective_mkProj Z y
    refine ⟨mkProj (bundleComap Z (e : C(B', B))) ((punctComapHomeo Z e).symm x), ?_⟩
    rw [hkey, Homeomorph.apply_symm_apply, hx]
  have hq : Topology.IsQuotientMap (projMapComap Z (e : C(B', B))) :=
    Topology.IsQuotientMap.of_comp_isQuotientMap
      (isQuotientMap_quotient_mk' (s := projSetoid (bundleComap Z (e : C(B', B))))) hcomp
  exact ⟨(Equiv.ofBijective (projMapComap Z (e : C(B', B))) ⟨hinj, hsurj⟩).toHomeomorph
    (fun _ => hq.isCoinducing.isOpen_preimage), rfl⟩

end

end Work.LerayHirsch
