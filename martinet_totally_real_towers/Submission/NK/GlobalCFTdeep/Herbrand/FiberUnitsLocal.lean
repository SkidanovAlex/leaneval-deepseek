/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import Submission.NK.GlobalCFTdeep.Herbrand.FiberUnitsDefs

/-!
# The short exact sequence `0 ⟶ 𝒪_wˣ ⟶ L_wˣ ⟶ ℤ ⟶ 0`

For a finite place `q` of `L` lying over the finite place `Q` of `K`, the valuation logarithm
`NK.GlobalCFTdeep.localValLinear` exhibits `L_qˣ` as an extension of `ℤ` (with the trivial
`D_q`-action, by `NK.GlobalCFTdeep.valLog_localAction`) by the local units `𝒪_qˣ`.  This file
records the resulting short exact sequence of `ℤ[D_q]`-modules

`NK.GlobalCFTdeep.sesLocalUnits`: `0 ⟶ 𝒪_qˣ ⟶ L_qˣ ⟶ ℤ ⟶ 0`,

with short exactness `NK.GlobalCFTdeep.sesLocalUnits_shortExact`.

## What this sequence is for

The middle term has Herbrand quotient `|D_q|` for cyclic `L/K`
(`NK.GlobalCFTdeep.herbrandEq_localUnitsRep_ofFinite`), and the third term is the trivial module
`ℤ`, with `hZero = |D_q|` and `hOne = 1` (`NK.GlobalCFTdeep.Herbrand.hZero_trivial`,
`...hOne_trivial`).  Since local automorphisms preserve the valuation, the first term is the local
units `𝒪_qˣ = NK.GlobalCFTdeep.localUnitSubRep (Place.ofFinite q)`, and the Euler-characteristic
identity `NK.GlobalCFTdeep.Herbrand.tateCohomology_mul_eq_of_shortExact_noFin` attached to the
sequence reads

  `|Ĥ⁰(L_qˣ)| · |Ĥ¹(𝒪_qˣ)| · |Ĥ¹(ℤ)| = |Ĥ⁰(𝒪_qˣ)| · |Ĥ⁰(ℤ)| · |Ĥ¹(L_qˣ)|`,

i.e. `|D_q| · |Ĥ¹(𝒪_qˣ)| = |Ĥ⁰(𝒪_qˣ)| · |D_q|`: cancelling `|D_q|` gives **Herbrand's theorem for
the local units**, `HerbrandEq (localUnitSubRep (Place.ofFinite q)) 1`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option maxHeartbeats 800000

open scoped NumberField RestrictedProduct
open NumberField IsDedekindDomain
open CategoryTheory

noncomputable section

namespace NK.GlobalCFTdeep

open NK.GlobalCFT

variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [FiniteDimensional K L] [IsGalois K L]

/-- The inclusion `𝒪_qˣ ↪ L_qˣ` of the local units at a finite place, as a morphism of
`ℤ[D_q]`-modules. -/
noncomputable def localUnitIncl (q : HeightOneSpectrum (𝓞 L)) :
    localUnitSubRep (K := K) (L := L) (Place.ofFinite q) ⟶
      localUnitsRep (K := K) (L := L) (Place.ofFinite q) :=
  Rep.ofHom
    { toFun := fun u => Additive.ofMul
        ((Additive.toMul u : ↥(Place.localUnits L (Place.ofFinite q))) :
          (Place.localField L (Place.ofFinite q))ˣ)
      map_add' := fun x y => by
        show Additive.ofMul ((↑(Additive.toMul (x + y)) :
            (Place.localField L (Place.ofFinite q))ˣ))
          = Additive.ofMul ((↑(Additive.toMul x) : (Place.localField L (Place.ofFinite q))ˣ)) +
            Additive.ofMul ((↑(Additive.toMul y) : (Place.localField L (Place.ofFinite q))ˣ))
        rw [toMul_add, Subgroup.coe_mul, ofMul_mul]
      map_smul' := fun n x => by
        show Additive.ofMul ((↑(Additive.toMul (n • x)) :
            (Place.localField L (Place.ofFinite q))ˣ))
          = n • Additive.ofMul ((↑(Additive.toMul x) :
            (Place.localField L (Place.ofFinite q))ˣ))
        rw [toMul_zsmul, Subgroup.coe_zpow, ofMul_zpow]
      isIntertwining' := fun σ => by
        apply LinearMap.ext
        intro x
        rfl }

/-- The valuation logarithm `L_qˣ ⟶ ℤ` at a finite place, as a morphism of `ℤ[D_q]`-modules
(the target carrying the trivial action, by `valLog_localAction`). -/
noncomputable def localValLogHom (Q : HeightOneSpectrum (𝓞 K)) (q : HeightOneSpectrum (𝓞 L))
    (hq : q.asIdeal.LiesOver Q.asIdeal) :
    localUnitsRep (K := K) (L := L) (Place.ofFinite q) ⟶
      Rep.trivial ℤ ↥(decompositionSubgroup (K := K) (L := L) (Place.ofFinite q)) ℤ :=
  Rep.ofHom
    { localValLinear q with
      isIntertwining' := fun σ => by
        apply LinearMap.ext
        intro a
        show localValLinear q (Additive.ofMul
            (Units.map (NK.GlobalCFT.Inclusion.Place.localAction σ.1 (Place.ofFinite q)
              σ.2).toMonoidHom (Additive.toMul a)))
          = (Rep.trivial ℤ ↥(decompositionSubgroup (K := K) (L := L) (Place.ofFinite q))
              ℤ).ρ σ (localValLinear q a)
        rw [show (Rep.trivial ℤ ↥(decompositionSubgroup (K := K) (L := L) (Place.ofFinite q))
              ℤ).ρ σ (localValLinear q a) = localValLinear q a from rfl]
        show Multiplicative.toAdd (valLog (HeightOneSpectrum.adicCompletion L q)
            (Units.map (NK.GlobalCFT.Inclusion.Place.localAction σ.1 (Place.ofFinite q)
              σ.2).toMonoidHom (Additive.toMul a))) = localValLinear q a
        rw [valLog_localAction (K := K) (L := L) Q q hq σ.1 σ.2 (Additive.toMul a)]
        rfl }

/-- **The short complex `0 ⟶ 𝒪_qˣ ⟶ L_qˣ ⟶ ℤ ⟶ 0`** of `ℤ[D_q]`-modules at a finite place `q`
of `L` above the finite place `Q` of `K`. -/
noncomputable def sesLocalUnits (Q : HeightOneSpectrum (𝓞 K)) (q : HeightOneSpectrum (𝓞 L))
    (hq : q.asIdeal.LiesOver Q.asIdeal) :
    ShortComplex (Rep ℤ ↥(decompositionSubgroup (K := K) (L := L) (Place.ofFinite q))) where
  X₁ := localUnitSubRep (K := K) (L := L) (Place.ofFinite q)
  X₂ := localUnitsRep (K := K) (L := L) (Place.ofFinite q)
  X₃ := Rep.trivial ℤ ↥(decompositionSubgroup (K := K) (L := L) (Place.ofFinite q)) ℤ
  f := localUnitIncl (K := K) q
  g := localValLogHom (K := K) Q q hq
  zero := by
    apply Rep.hom_ext
    apply Representation.IntertwiningMap.ext
    apply LinearMap.ext
    intro x
    show localValLinear q (Additive.ofMul
      ((Additive.toMul x : ↥(Place.localUnits L (Place.ofFinite q))) :
        (Place.localField L (Place.ofFinite q))ˣ)) = 0
    rw [localValLinear_eq_zero_iff]
    exact (Additive.toMul x).2

/-- **The short complex of local units is short exact.** -/
theorem sesLocalUnits_shortExact (Q : HeightOneSpectrum (𝓞 K)) (q : HeightOneSpectrum (𝓞 L))
    (hq : q.asIdeal.LiesOver Q.asIdeal) :
    (sesLocalUnits (K := K) (L := L) Q q hq).ShortExact := by
  refine Commons.RepresentationTheory.GroupCohomology.shortExact_of_mono_epi_elementwise _
    ((Rep.mono_iff_injective _).2 ?_) ((Rep.epi_iff_surjective _).2 ?_) ?_
  · intro x y h
    exact Additive.toMul.injective
      (Subtype.ext (Additive.ofMul.injective h))
  · intro z
    obtain ⟨a, ha⟩ := localValLinear_surjective q z
    exact ⟨a, ha⟩
  · intro x hx
    have hx' : localValLinear q x = 0 := hx
    refine ⟨Additive.ofMul ⟨Additive.toMul x, ?_⟩, rfl⟩
    rw [← localValLinear_eq_zero_iff]
    change localValLinear q x = 0
    exact hx'

end NK.GlobalCFTdeep
