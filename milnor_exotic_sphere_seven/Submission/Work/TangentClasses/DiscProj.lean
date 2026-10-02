import Mathlib
import Submission.Work.TangentClasses.Capped
import Submission.Work.Milnor.ZeroSectionProj

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

/-!
# The bundle projection of the disc bundle, and the geometric input

`Submission/Work/TangentClasses/Capped.lean` encodes the geometric input at the heart of the
identification `p₁(TX) = Work.Milnor.cappedPontryaginClass F hF` as a `DiscTangentSplitting`: a
bundle projection `proj : C(D(ξ), S⁴)` together with a class `G ∈ H⁴(S⁴;ℤ)` whose pullback along
`proj` is the chapter's generator `τ ∈ H⁴(D(ξ);ℤ) ≅ ℤ` of the disc bundle, up to sign.

This module relates that data to the honest bundle projection and the zero section of the disc
bundle:

* `discProj` is `vBaseMap : Vk (-2) → S⁴` (`Submission/Work/Milnor/exists_proj`) as a continuous
  map, and `discSection` is the zero section `S⁴ → Vk (-2)`;
* `discProj_comp_discSection : π ∘ s = id` (`Work.Milnor.vBaseMap_zeroSection`);
* `injective_HMap_discProj`: **the pullback along the bundle projection is injective** in every
  degree — the zero section splits `π^*` on the other side — so the class `G` of a
  `DiscTangentSplitting` is *unique* when it exists (for each choice of sign);
* `nonempty_discTangentSplitting_of_surjective`: the data exists as soon as `π^*` is surjective; and
  since `π : D(ξ) → S⁴` is a homotopy equivalence (the open disc bundle deformation retracts onto
  the zero section — a geometric fact not formalized in this workspace), this always holds.

So nothing about `DiscTangentSplitting` is an extra mathematical hypothesis: it records the
*normalisation of the chosen generators* of `H⁴(S⁴;ℤ) ≅ ℤ` and `H⁴(D(ξ);ℤ) ≅ ℤ`, together with
the geometric identification `TX|_{D(ξ)} ≅ π^*(TS⁴ ⊕ ξ)` which is its interpretation.
-/

namespace Work.TangentClasses

open CategoryTheory
open Work.CharacteristicClasses

noncomputable section

/-- **The bundle projection `π : D(ξ) → S⁴`** of the disc bundle, as a continuous map (the
`vBaseMap` of `Submission/Work/Milnor/exists_proj`). -/
def discProj : C(DiscSpace, S4) :=
  ⟨Work.Milnor.vBaseMap (-2), Work.Milnor.continuous_vBaseMap (-2)⟩

/-- **The zero section `s : S⁴ → D(ξ)`** of the disc bundle, as a continuous map. -/
def discSection : C(S4, DiscSpace) :=
  ⟨Work.Milnor.zeroSection (-2), Work.Milnor.continuous_zeroSection (-2)⟩

@[simp] theorem discProj_apply (p : DiscSpace) : discProj p = Work.Milnor.vBaseMap (-2) p := rfl

@[simp] theorem discSection_apply (x : S4) : discSection x = Work.Milnor.zeroSection (-2) x := rfl

/-- The zero section is a section of the bundle projection: `π ∘ s = id`. -/
theorem discProj_comp_discSection : discProj.comp discSection = ContinuousMap.id S4 := by
  ext x
  exact Work.Milnor.vBaseMap_zeroSection (-2) x

/-- The composition `s^* ∘ π^*` is the identity on `H^n(S⁴;ℤ)`. -/
theorem HMap_discSection_comp_HMap_discProj (n : ℕ) :
    (HMap discSection n).hom.comp (HMap discProj n).hom =
      (LinearMap.id : H n S4 →ₗ[ℤ] H n S4) := by
  have h := HMap_comp discSection discProj n
  rw [discProj_comp_discSection, HMap_id] at h
  have h2 := congrArg (fun f : H n S4 ⟶ H n S4 => f.hom) h
  simpa using h2.symm

/-- The map `s^* ∘ π^*` is the identity, pointwise. -/
theorem HMap_discSection_HMap_discProj_apply (n : ℕ) (z : H n S4) :
    (HMap discSection n).hom ((HMap discProj n).hom z) = z := by
  have h := congrArg (fun f : H n S4 →ₗ[ℤ] H n S4 => f z)
    (HMap_discSection_comp_HMap_discProj n)
  simpa using h

/-- **The pullback along the bundle projection is injective** (in every degree): the zero section
splits it, `s^* ∘ π^* = id`.  In particular the class `G` of a `DiscTangentSplitting` is unique
(for each choice of sign). -/
theorem injective_HMap_discProj (n : ℕ) : Function.Injective (HMap discProj n).hom := by
  intro x y hxy
  calc x = (HMap discSection n).hom ((HMap discProj n).hom x) :=
        (HMap_discSection_HMap_discProj_apply n x).symm
    _ = (HMap discSection n).hom ((HMap discProj n).hom y) := by rw [hxy]
    _ = y := HMap_discSection_HMap_discProj_apply n y

/-- **The geometric input exists as soon as `π^*` is surjective.**  Taking a preimage of the
generator `τ` under `π^*` gives the second component of a `DiscTangentSplitting` (with the honest
bundle projection).  Since `π` is a homotopy equivalence (the open disc bundle deformation retracts
onto the zero section), surjectivity always holds. -/
theorem nonempty_discTangentSplitting_of_surjective
    (h : Function.Surjective (HMap discProj 4).hom) : Nonempty DiscTangentSplitting := by
  obtain ⟨G, hG⟩ := h Work.Milnor.tauD
  exact ⟨⟨discProj, G, Or.inl hG⟩⟩

end

end Work.TangentClasses
