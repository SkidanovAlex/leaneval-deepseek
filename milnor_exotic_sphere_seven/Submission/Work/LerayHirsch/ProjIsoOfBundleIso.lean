import Mathlib
import Submission.Work.LerayHirsch.Naturality
import Submission.Work.Thom.IsoPunct
import Submission.Work.Thom.realification_homeo

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
-- set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

/-!
# Functoriality of the projectivisation under an isomorphism of bundles

* `Work.LerayHirsch.punctIsoMap` / `punctIsoHomeo` — the homeomorphism of the punctured total
  spaces of the realifications induced by a `Work.Thom.BundleIso Z Z'`;
* `Work.LerayHirsch.projIsoMap` — the induced *continuous map* `P(Z) → P(Z')` on the
  projectivisations, `[p] ↦ [e.punctMap p]`;
* `Work.LerayHirsch.exists_homeo_projSpace_of_bundleIso` — `projIsoMap Z Z' e` is a homeomorphism;
* `Work.LerayHirsch.projMap_projIsoMap` — `π_{P(Z')} ∘ P(e) = π_{P(Z)}`.

This is the analogue for an isomorphism of bundles of
`Work.LerayHirsch.projMapComap` / `exists_homeo_projSpace_bundleComap_homeo` (the base-change case).
-/

namespace Work.LerayHirsch

open Work.TangentClasses Work.Thom

open scoped LinearAlgebra.Projectivization

noncomputable section

variable {B : Type} [TopologicalSpace B] {ι ι' : Type} {m : ℕ}

/-! ## The punctured total spaces -/

/-- **The map of punctured total spaces induced by a bundle isomorphism** (on the realifications). -/
def punctIsoMap (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι)
    (Z' : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι') (e : BundleIso Z Z') :
    ↥(zeroComplement (realification Z)) → ↥(zeroComplement (realification Z')) :=
  fun p => ⟨⟨p.1.proj, e.hom p.1.proj (show EuclideanSpace ℂ (Fin m) from p.1.2)⟩, by
    rw [mem_zeroComplement]
    exact e.hom_ne_zero p.2⟩

@[simp] theorem punctIsoMap_proj (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι)
    (Z' : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι') (e : BundleIso Z Z')
    (p : ↥(zeroComplement (realification Z))) :
    (punctIsoMap Z Z' e p).1.proj = p.1.proj := rfl

@[simp] theorem punctIsoMap_snd (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι)
    (Z' : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι') (e : BundleIso Z Z')
    (p : ↥(zeroComplement (realification Z))) :
    (show EuclideanSpace ℂ (Fin m) from (punctIsoMap Z Z' e p).1.2)
      = e.hom p.1.proj (show EuclideanSpace ℂ (Fin m) from p.1.2) := rfl

/-- **The map of punctured total spaces**, as a homeomorphism: it is the composite of the two
realification identifications with the homeomorphism `Work.Thom.BundleIso.punctHomeomorph`. -/
def punctIsoHomeo (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι)
    (Z' : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι') (e : BundleIso Z Z') :
    ↥(zeroComplement (realification Z)) ≃ₜ ↥(zeroComplement (realification Z')) :=
  (zeroComplementHomeomorph Z).trans
    (e.punctHomeomorph.trans (zeroComplementHomeomorph Z').symm)

@[simp] theorem punctIsoHomeo_apply (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι)
    (Z' : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι') (e : BundleIso Z Z')
    (p : ↥(zeroComplement (realification Z))) :
    punctIsoHomeo Z Z' e p = punctIsoMap Z Z' e p := rfl

/-- **The induced map is `ℂˣ`-equivariant**, so that it descends to the projectivisations. -/
theorem punctIsoMap_smulPunct (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι)
    (Z' : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι') (e : BundleIso Z Z')
    (c : ℂˣ) (p : ↥(zeroComplement (realification Z))) :
    punctIsoMap Z Z' e (smulPunct Z c p) = smulPunct Z' c (punctIsoMap Z Z' e p) := by
  refine Subtype.ext (Bundle.TotalSpace.ext ?_ ?_)
  · show (punctIsoMap Z Z' e (smulPunct Z c p)).1.proj
        = (smulPunct Z' c (punctIsoMap Z Z' e p)).1.proj
    rw [smulPunct_proj]
    rfl
  · refine heq_of_eq ?_
    show (show EuclideanSpace ℂ (Fin m) from (punctIsoMap Z Z' e (smulPunct Z c p)).1.2)
      = (show EuclideanSpace ℂ (Fin m) from
          (smulPunct Z' c (punctIsoMap Z Z' e p)).1.2)
    rw [punctIsoMap_snd, smulPunct_snd, smulPunct_snd, punctIsoMap_snd, smulPunct_proj]
    exact map_smul (e.hom p.1.proj) (c : ℂ) (show EuclideanSpace ℂ (Fin m) from p.1.2)

/-- The `ℂˣ`-equivariance in the form of the homeomorphism `punctIsoHomeo`. -/
theorem punctIsoHomeo_smulPunct (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι)
    (Z' : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι') (e : BundleIso Z Z')
    (c : ℂˣ) (p : ↥(zeroComplement (realification Z))) :
    punctIsoHomeo Z Z' e (smulPunct Z c p) = smulPunct Z' c (punctIsoHomeo Z Z' e p) :=
  punctIsoMap_smulPunct Z Z' e c p

/-! ## The projectivisation -/

/-- The defining function of `Work.LerayHirsch.projIsoMap`, on representatives. -/
def projIsoFun (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι)
    (Z' : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι') (e : BundleIso Z Z') :
    ↥(zeroComplement (realification Z)) → ProjSpace Z' :=
  fun p => mkProj Z' (punctIsoMap Z Z' e p)

/-- `projIsoFun` is constant on the classes of the `ℂˣ`-action, so it descends to `P(Z)`. -/
theorem projIsoFun_eq_of_rel (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι)
    (Z' : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι') (e : BundleIso Z Z')
    {a b : ↥(zeroComplement (realification Z))} (h : projRel Z a b) :
    projIsoFun Z Z' e a = projIsoFun Z Z' e b := by
  obtain ⟨c, hc⟩ := h
  rw [projIsoFun, projIsoFun, ← hc, punctIsoMap_smulPunct, mkProj_eq_iff]
  exact ⟨c, rfl⟩

/-- **Functoriality of the projectivisation under a bundle isomorphism**: the induced continuous
map `P(Z) → P(Z')`, `[p] ↦ [e.punctMap p]`. -/
def projIsoMap (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι)
    (Z' : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι') (e : BundleIso Z Z') :
    C(ProjSpace Z, ProjSpace Z') where
  toFun := Quotient.lift (projIsoFun Z Z' e) (fun _ _ h => projIsoFun_eq_of_rel Z Z' e h)
  continuous_toFun := by
    refine Continuous.quotient_lift ?_ (fun _ _ h => projIsoFun_eq_of_rel Z Z' e h)
    exact (continuous_mkProj Z').comp (punctIsoHomeo Z Z' e).continuous

@[simp] theorem projIsoMap_mkProj (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι)
    (Z' : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι') (e : BundleIso Z Z')
    (p : ↥(zeroComplement (realification Z))) :
    projIsoMap Z Z' e (mkProj Z p) = mkProj Z' (punctIsoMap Z Z' e p) := rfl

/-- **The projection to the base is compatible**: `π' ∘ P(e) = π`. -/
theorem projMap_projIsoMap (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι)
    (Z' : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι') (e : BundleIso Z Z')
    (x : ProjSpace Z) :
    projMap Z' (projIsoMap Z Z' e x) = projMap Z x := by
  obtain ⟨p, rfl⟩ := surjective_mkProj Z x
  rfl

/-- **The induced map of projectivisations is a homeomorphism.** -/
theorem exists_homeo_projSpace_of_bundleIso
    (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι)
    (Z' : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι') (e : BundleIso Z Z') :
    ∃ Φ : ProjSpace Z ≃ₜ ProjSpace Z', ⇑Φ = ⇑(projIsoMap Z Z' e) := by
  have hkey : ∀ a : ↥(zeroComplement (realification Z)),
      (projIsoMap Z Z' e) (mkProj Z a) = mkProj Z' (punctIsoHomeo Z Z' e a) := fun a => rfl
  have hcomp : Topology.IsQuotientMap
      ((projIsoMap Z Z' e) ∘ (mkProj Z)) := by
    have heq : ((projIsoMap Z Z' e) ∘ (mkProj Z))
        = ((mkProj Z') ∘ (punctIsoHomeo Z Z' e)) := funext hkey
    rw [heq]
    exact (isQuotientMap_quotient_mk' (s := projSetoid Z')).comp
      (punctIsoHomeo Z Z' e).isQuotientMap
  have hinj : Function.Injective (projIsoMap Z Z' e) := by
    intro p q hpq
    obtain ⟨a, rfl⟩ := surjective_mkProj Z p
    obtain ⟨b, rfl⟩ := surjective_mkProj Z q
    rw [hkey a, hkey b] at hpq
    obtain ⟨c, hc⟩ := (mkProj_eq_iff Z').mp hpq
    refine (mkProj_eq_iff Z).mpr ⟨c, ?_⟩
    apply (punctIsoHomeo Z Z' e).injective
    rw [punctIsoHomeo_smulPunct]
    exact hc
  have hsurj : Function.Surjective (projIsoMap Z Z' e) := by
    intro y
    obtain ⟨x, hx⟩ := surjective_mkProj Z' y
    refine ⟨mkProj Z ((punctIsoHomeo Z Z' e).symm x), ?_⟩
    rw [hkey, Homeomorph.apply_symm_apply, hx]
  have hq : Topology.IsQuotientMap (projIsoMap Z Z' e) :=
    Topology.IsQuotientMap.of_comp_isQuotientMap
      (isQuotientMap_quotient_mk' (s := projSetoid Z)) hcomp
  exact ⟨(Equiv.ofBijective (projIsoMap Z Z' e) ⟨hinj, hsurj⟩).toHomeomorph
    (fun _ => hq.isCoinducing.isOpen_preimage), rfl⟩

end

end Work.LerayHirsch
