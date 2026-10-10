import Mathlib.FieldTheory.KrullTopology
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.PicardGroup
import Mathlib.Combinatorics.Quiver.ReflQuiver
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RepresentationTheory.Rep.Res
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.Valuation.ValuationSubring
import Submission.Work.SSGRoute.E1aClean.decompField_hensel_groupIso
import Submission.Work.SSGRoute.E1aClean.e1cMap_hensel_cocycle_formula
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# **(BC)**, piece (C): the level-change transport of the cocycle-lift relation

This file proves the one piece of mathematics of **(BC)** `dict_baseChange_decomp`
(`E1aClean/NOTE_BC_dict_baseChange_decomp_design_2026-10-06.md` §3, and the design resolution
`E1aClean/PING_BC_design_settled_by_freeCoverCompat_2026-10-06.md`): the lift relation
`iotaH (c γ) = d0 ñ γ` of a level-`1` cocycle **transports** to the henselian (level-`2`) datum
along the canonical comparison map of the two canonical covers.

The datum is the henselian one of `E1aClean.e1cMap_hensel_cocycle_formula`:

* `k^h := decompField k Ω A`, `K^h := henselOverDecomp k Ω K A`, `φ : Gal(K^h/k^h) →* Gal(K/k)`
  the restriction along `K ≤ K^h`, `R : Rep Coeff Gal(K/k)` a `ℤ`-finite coefficient;
* the comparison map of the covers is `Work.SSGRoute.PT.freeCoverCompat φ R`
  (`PT/freeCoverCompat.lean`, with its two rules `E1cGeneric.freeCoverCompat_single` and
  `E1cGeneric.freeCoverCompat_comp`), taken here as the additive map
  `levelChangeIota A R φ : E1cF (Rep.res φ R) →+ E1cF R`.  Its target is the level-`1` free module,
  which is exactly the domain of a level-`1` lift `ñ : E1cN R`, so `ñ ∘ levelChangeIota` **is** a
  level-`2` element `E1cN (Rep.res φ R)` (the carriers agree definitionally).

The two bookkeeping lemmas are

* `levelChangeIota_equivariant` — `ι` is `Gal(K^h/k^h)`-equivariant for `φ` (from
  `Rep.hom_comm_apply`; `levelChangeIota` is the underlying additive map of a morphism of
  representations).  It is used with the *inverse* group element, i.e. it says that
  `ι (F₂.ρ τ x) = F₁.ρ (φ τ) (ι x)`, which is what the conjugation actions
  (`Work.SSGRoute.homCoind.smul_apply`) consume;
* `levelChange_coverMap_iota` — the two canonical covers commute with `ι`
  (`coverMap^{(k^h)} x = coverMap^{(k)} (ι x)`), which is `freeCoverCompat_comp` evaluated at `x`.

Together they give `levelChange_lift_transport`: for every `g : Gal(Ω/k^h)`,

    iotaH^{(k^h)} (c.1 (ψ g)) = d0^{(k^h)} (ñ ∘ ι) g        (ψ := inclusion  Gal(Ω/k^h) ↪ Gal(Ω/k)),

proved pointwise: `iotaH` is precomposition with `coverMap`, `coverMap` commutes with `ι`,
`d0` is `cnj − id` in the *explicit* form `E1cGeneric.d0_cnj` (which avoids the `•`-instance
ambiguity of the free-based coefficient, cf. `PT/NOTE_e1aChainC_localComparison.md` §14), the
level-`1` hypothesis `hñ` computes `iotaH^{(k)} (c.1 (ψ g)) ∘ ι`, and the two remaining
comparisons are the `Gal`-level compatibility `hφres`
(`φ ∘ res_{K^h/k^h} = res_{K/k} ∘ ψ`, an `AlgEquiv.ext`-level identity of the canonical
restrictions) and the `•`-comparison on `Ωˣ`, which is `rfl` (`AlgEquiv.restrictScalars` is the
same function, so the two `Units.map` actions agree definitionally).

Nothing is assumed about `(PUSH)`, and no choice principle beyond `Classical.choice` is used.
-/

open CategoryTheory SSGRoute.PTExt

namespace Work.SSGRoute.E1aClean

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 2000000
set_option linter.unusedSectionVars false

noncomputable section

variable {k : Type} [Field k] [NumberField k] {Ω : Type} [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]
  {K : IntermediateField k Ω} [FiniteDimensional k K] [IsGalois k K]
  (A : ValuationSubring Ω)
  (R : Rep.{0} SSGRoute.PTExt.Coeff (K ≃ₐ[k] K)) [Module.Finite ℤ R.V]
  (φ : (↥(henselOverDecomp k Ω K A) ≃ₐ[↥(decompField k Ω A)] ↥(henselOverDecomp k Ω K A)) →*
    (K ≃ₐ[k] K))
  [CharZero ↥(decompField k Ω A)] [IsAlgClosure ↥(decompField k Ω A) Ω]
  [FiniteDimensional ↥(decompField k Ω A) ↥(henselOverDecomp k Ω K A)]
  [IsGalois ↥(decompField k Ω A) ↥(henselOverDecomp k Ω K A)]

/-- **The comparison map of the two canonical covers**, as an additive map:
`freeCoverCompat φ R : ℤ[Gal(K^h/k^h)]⊗R → ℤ[Gal(K/k)]⊗R`. -/
def levelChangeIota : (Rep.free SSGRoute.PTExt.Coeff
      (↥(henselOverDecomp k Ω K A) ≃ₐ[↥(decompField k Ω A)] ↥(henselOverDecomp k Ω K A)) R.V).V →+
    (Rep.free SSGRoute.PTExt.Coeff (K ≃ₐ[k] K) R.V).V :=
  (Work.SSGRoute.PT.freeCoverCompat φ R).hom.toLinearMap.toAddMonoidHom

/-- **`ι` is equivariant for the restriction `φ`** (it is the underlying additive map of a morphism
of representations). -/
theorem levelChangeIota_equivariant
    (τ : ↥(henselOverDecomp k Ω K A) ≃ₐ[↥(decompField k Ω A)] ↥(henselOverDecomp k Ω K A))
    (x : (Rep.free SSGRoute.PTExt.Coeff
      (↥(henselOverDecomp k Ω K A) ≃ₐ[↥(decompField k Ω A)] ↥(henselOverDecomp k Ω K A)) R.V).V) :
    levelChangeIota A R φ ((Rep.free SSGRoute.PTExt.Coeff
      (↥(henselOverDecomp k Ω K A) ≃ₐ[↥(decompField k Ω A)] ↥(henselOverDecomp k Ω K A)) R.V).ρ τ x)
      = (Rep.free SSGRoute.PTExt.Coeff (K ≃ₐ[k] K) R.V).ρ (φ τ)
          (levelChangeIota A R φ x) := by
  simpa [levelChangeIota] using Rep.hom_comm_apply (Work.SSGRoute.PT.freeCoverCompat φ R) τ x

/-- **The two canonical covers commute with `ι`**: the level-`2` cover of `Rep.res φ R` is the
level-`1` cover of `R` precomposed with `ι` (this is `E1cGeneric.freeCoverCompat_comp`). -/
theorem levelChange_coverMap_iota (x : (Rep.free SSGRoute.PTExt.Coeff
      (↥(henselOverDecomp k Ω K A) ≃ₐ[↥(decompField k Ω A)] ↥(henselOverDecomp k Ω K A)) R.V).V) :
    Work.SSGRoute.ExtChain.E1cGeneric.coverMap (k := ↥(decompField k Ω A))
        (Ω := Ω) (K := henselOverDecomp k Ω K A) (Rep.res φ R) x
      = Work.SSGRoute.ExtChain.E1cGeneric.coverMap (k := k) (Ω := Ω) (K := K) R
          (levelChangeIota A R φ x) := by
  have h := congrArg
    (fun (f : Rep.free SSGRoute.PTExt.Coeff
          (↥(henselOverDecomp k Ω K A) ≃ₐ[↥(decompField k Ω A)]
            ↥(henselOverDecomp k Ω K A)) R.V ⟶ Rep.res φ R) =>
        (Rep.Hom.hom f) x)
    (Work.SSGRoute.E1cGeneric.freeCoverCompat_comp φ R)
  rw [Rep.comp_apply, Rep.resMap_hom_apply] at h
  exact h.symm

/-- **The transport of the cocycle-lift relation along the level change** (piece (C) of (BC)).

Let `c` be a level-`1` `1`-cocycle with values in `homCoind k Ω K R` and `ñ : E1cN R` a lift of its
values to the middle term of the canonical cover (`iotaH (c γ) = d0 ñ γ` for all `γ`).  Then for
`ψ := AlgEquiv.restrictScalars k : Gal(Ω/k^h) → Gal(Ω/k)` and `ι := levelChangeIota`,
`ñ ∘ ι` is a lift at the henselian level: for every `g : Gal(Ω/k^h)`,

    iotaH^{(k^h)} (c.1 (ψ g)) = d0^{(k^h)} (ñ ∘ ι) g .

The hypothesis `hφres` is the `Gal`-level compatibility of the two restrictions
(`φ (g|_{K^h}) = (ψ g)|_K`); it is an `AlgEquiv.ext`-level identity of the canonical restriction maps
and holds for the canonical `φ`. -/
theorem levelChange_lift_transport
    (hφres : ∀ g : Ω ≃ₐ[↥(decompField k Ω A)] Ω,
      φ (SSGRoute.res ↥(decompField k Ω A) (henselOverDecomp k Ω K A) g)
        = SSGRoute.res k K (AlgEquiv.restrictScalars k g))
    (c : ↥(Work.AbsoluteKummer.Z1 (Ω ≃ₐ[k] Ω) (Work.SSGRoute.homCoind k Ω K R)))
    (ñ : Work.SSGRoute.ExtChain.E1cGeneric.E1cN (k := k) (Ω := Ω) (K := K) R)
    (hñ : ∀ γ : Ω ≃ₐ[k] Ω,
      Work.SSGRoute.ExtChain.E1cGeneric.iotaH (k := k) (Ω := Ω) (K := K) R (c.1 γ)
        = Work.GroupCohomology.d0 (Ω ≃ₐ[k] Ω)
            (Work.SSGRoute.ExtChain.E1cGeneric.E1cN (k := k) (Ω := Ω) (K := K) R) ñ γ)
    (g : Ω ≃ₐ[↥(decompField k Ω A)] Ω) :
    Work.SSGRoute.ExtChain.E1cGeneric.iotaH (k := ↥(decompField k Ω A))
        (Ω := Ω) (K := henselOverDecomp k Ω K A) (Rep.res φ R)
        (c.1 (AlgEquiv.restrictScalars k g))
      = Work.GroupCohomology.d0 (Ω ≃ₐ[↥(decompField k Ω A)] Ω)
          (Work.SSGRoute.ExtChain.E1cGeneric.E1cN (k := ↥(decompField k Ω A))
            (Ω := Ω) (K := henselOverDecomp k Ω K A) (Rep.res φ R))
          (ñ.comp (levelChangeIota A R φ)) g := by
  apply AddMonoidHom.ext; intro x
  rw [Work.SSGRoute.ExtChain.E1cGeneric.iotaH_apply, AddMonoidHom.comp_apply,
    levelChange_coverMap_iota A R φ x, ← AddMonoidHom.comp_apply,
    ← Work.SSGRoute.ExtChain.E1cGeneric.iotaH_apply,
    hñ (AlgEquiv.restrictScalars k g)]
  rw [Work.SSGRoute.ExtChain.E1cGeneric.d0_cnj (k := k) (Ω := Ω) (K := K) R,
    Work.SSGRoute.ExtChain.E1cGeneric.d0_cnj (k := ↥(decompField k Ω A))
      (Ω := Ω) (K := henselOverDecomp k Ω K A) (Rep.res φ R)]
  rw [AddMonoidHom.sub_apply, AddMonoidHom.sub_apply, AddMonoidHom.comp_apply]
  congr 1
  show (Work.SSGRoute.homCoind.smulHom (k := k) (Ω := Ω) (AlgEquiv.restrictScalars k g))
      (ñ ((Rep.free SSGRoute.PTExt.Coeff (K ≃ₐ[k] K) R.V).ρ
        ((SSGRoute.res k K) (AlgEquiv.restrictScalars k g))⁻¹ (levelChangeIota A R φ x)))
    = (Work.SSGRoute.homCoind.smulHom (k := ↥(decompField k Ω A)) (Ω := Ω) g)
      ((ñ.comp (levelChangeIota A R φ)) ((Rep.free SSGRoute.PTExt.Coeff
        (↥(henselOverDecomp k Ω K A) ≃ₐ[↥(decompField k Ω A)]
          ↥(henselOverDecomp k Ω K A)) R.V).ρ
        ((SSGRoute.res ↥(decompField k Ω A) (henselOverDecomp k Ω K A)) g)⁻¹ x))
  rw [Work.SSGRoute.homCoind.smulHom_apply, Work.SSGRoute.homCoind.smulHom_apply,
    AddMonoidHom.comp_apply, ← hφres g]
  have heq : levelChangeIota A R φ ((Rep.free SSGRoute.PTExt.Coeff
        (↥(henselOverDecomp k Ω K A) ≃ₐ[↥(decompField k Ω A)]
          ↥(henselOverDecomp k Ω K A)) R.V).ρ
        ((SSGRoute.res ↥(decompField k Ω A) (henselOverDecomp k Ω K A)) g)⁻¹ x)
      = (Rep.free SSGRoute.PTExt.Coeff (K ≃ₐ[k] K) R.V).ρ
          (φ ((SSGRoute.res ↥(decompField k Ω A) (henselOverDecomp k Ω K A)) g)⁻¹)
            (levelChangeIota A R φ x) :=
    levelChangeIota_equivariant A R φ _ x
  have hminv : (φ ((SSGRoute.res ↥(decompField k Ω A) (henselOverDecomp k Ω K A)) g))⁻¹
      = φ (((SSGRoute.res ↥(decompField k Ω A) (henselOverDecomp k Ω K A)) g)⁻¹) :=
    (map_inv φ _).symm
  rw [hminv, ← heq]
  rfl

/-- **The two conjugation actions commute with the level change** (the *general* form of the step
proved inside `levelChange_lift_transport`, with `ñ` replaced by an arbitrary level-`1` element):

    cnj^{(k^h)} g (m ∘ ι) = (cnj^{(k)} (restrictScalars k g) m) ∘ ι .

This is what transfers the **cocycle condition** (not only the lift relation) along the level change:
if `c` is a level-`1` `1`-cocycle then `g ↦ c.1 (ψ g) ∘ ι` is a level-`2` `1`-cocycle; the same
identity, read at `m := ` the level-`1` `d0`-terms, is the lift transport. -/
theorem levelChange_cnj
    (hφres : ∀ g : Ω ≃ₐ[↥(decompField k Ω A)] Ω,
      φ (SSGRoute.res ↥(decompField k Ω A) (henselOverDecomp k Ω K A) g)
        = SSGRoute.res k K (AlgEquiv.restrictScalars k g))
    (m : Work.SSGRoute.ExtChain.E1cGeneric.E1cN (k := k) (Ω := Ω) (K := K) R)
    (g : Ω ≃ₐ[↥(decompField k Ω A)] Ω) :
    Work.SSGRoute.ExtChain.E1cGeneric.cnj (k := ↥(decompField k Ω A)) (Ω := Ω)
        (K := henselOverDecomp k Ω K A) (Rep.res φ R) g
        (m.comp (levelChangeIota A R φ))
      = (Work.SSGRoute.ExtChain.E1cGeneric.cnj (k := k) (Ω := Ω) (K := K) R
            (AlgEquiv.restrictScalars k g) m).comp (levelChangeIota A R φ) := by
  apply AddMonoidHom.ext; intro x
  show (Work.SSGRoute.homCoind.smulHom (k := ↥(decompField k Ω A)) (Ω := Ω) g)
      (m (levelChangeIota A R φ ((Rep.free SSGRoute.PTExt.Coeff
        (↥(henselOverDecomp k Ω K A) ≃ₐ[↥(decompField k Ω A)]
          ↥(henselOverDecomp k Ω K A)) R.V).ρ
        ((SSGRoute.res ↥(decompField k Ω A) (henselOverDecomp k Ω K A)) g)⁻¹ x)))
    = (Work.SSGRoute.homCoind.smulHom (k := k) (Ω := Ω) (AlgEquiv.restrictScalars k g))
      (m ((Rep.free SSGRoute.PTExt.Coeff (K ≃ₐ[k] K) R.V).ρ
        ((SSGRoute.res k K) (AlgEquiv.restrictScalars k g))⁻¹ (levelChangeIota A R φ x)))
  rw [Work.SSGRoute.homCoind.smulHom_apply, Work.SSGRoute.homCoind.smulHom_apply, ← hφres g]
  have heq : levelChangeIota A R φ ((Rep.free SSGRoute.PTExt.Coeff
        (↥(henselOverDecomp k Ω K A) ≃ₐ[↥(decompField k Ω A)]
          ↥(henselOverDecomp k Ω K A)) R.V).ρ
        ((SSGRoute.res ↥(decompField k Ω A) (henselOverDecomp k Ω K A)) g)⁻¹ x)
      = (Rep.free SSGRoute.PTExt.Coeff (K ≃ₐ[k] K) R.V).ρ
          (φ ((SSGRoute.res ↥(decompField k Ω A) (henselOverDecomp k Ω K A)) g)⁻¹)
            (levelChangeIota A R φ x) :=
    levelChangeIota_equivariant A R φ _ x
  have hminv : (φ ((SSGRoute.res ↥(decompField k Ω A) (henselOverDecomp k Ω K A)) g))⁻¹
      = φ (((SSGRoute.res ↥(decompField k Ω A) (henselOverDecomp k Ω K A)) g)⁻¹) :=
    (map_inv φ _).symm
  rw [hminv, ← heq]
  rfl

/-- **The action comparison on the small coind coefficient**: the level-`2` action at `g`
(`homCoind ↥k^h Ω K^h (Rep.res φ R)`) is the level-`1` action at `AlgEquiv.restrictScalars k g`
(`homCoind k Ω K R`).  The two coefficients have the *same* underlying type `R.V →+ Ωˣ` and their
actions are given by the same formula, with `R.ρ (res_{K/k} (g|_Ω))` on the one side and
`R.ρ (φ (g|_{K^h}))` on the other; `hφres` identifies these.  This is the key to transferring the
*cocycle condition* across the level change. -/
theorem homCoind_levelChange_smul
    (hφres : ∀ g : Ω ≃ₐ[↥(decompField k Ω A)] Ω,
      φ (SSGRoute.res ↥(decompField k Ω A) (henselOverDecomp k Ω K A) g)
        = SSGRoute.res k K (AlgEquiv.restrictScalars k g))
    (g : Ω ≃ₐ[↥(decompField k Ω A)] Ω)
    (m : R.V →+ Additive Ωˣ) :
    (Work.SSGRoute.homCoind.instDistribMulActionAlgEquiv
        (k := ↥(decompField k Ω A)) (Ω := Ω)
        (K := henselOverDecomp k Ω K A) (Rep.res φ R)).smul g m
      = (Work.SSGRoute.homCoind.instDistribMulActionAlgEquiv (k := k) (Ω := Ω) (K := K)
          R).smul (AlgEquiv.restrictScalars k g) m := by
  apply AddMonoidHom.ext; intro x
  show (Work.SSGRoute.homCoind.smulHom (k := ↥(decompField k Ω A)) (Ω := Ω) g)
      (m (((Rep.res φ R).ρ ((SSGRoute.res ↥(decompField k Ω A)
        (henselOverDecomp k Ω K A)) g)⁻¹) x))
    = (Work.SSGRoute.homCoind.smulHom (k := k) (Ω := Ω) (AlgEquiv.restrictScalars k g))
      (m ((R.ρ ((SSGRoute.res k K) (AlgEquiv.restrictScalars k g))⁻¹) x))
  rw [← hφres g,
    Work.SSGRoute.homCoind.smulHom_apply, Work.SSGRoute.homCoind.smulHom_apply]
  rw [Rep.coe_res_obj_ρ', map_inv]
  rfl

/-- **(BC)**: the level-`1` `1`-cocycle, read with the *same values* in the level-`2` coefficient
(the two coefficients `homCoind k Ω K R` and `homCoind ↥k^h Ω K^h (Rep.res φ R)` have the same
underlying type, and their actions agree by `homCoind_levelChange_smul`), is a level-`2`
`1`-cocycle.  This is exactly the cocycle needed by the level-`2` instance of
`E1aClean.e1cMap_hensel_cocycle_formula`. -/
theorem levelChange_mem_Z1
    (hφres : ∀ g : Ω ≃ₐ[↥(decompField k Ω A)] Ω,
      φ (SSGRoute.res ↥(decompField k Ω A) (henselOverDecomp k Ω K A) g)
        = SSGRoute.res k K (AlgEquiv.restrictScalars k g))
    (hψc : Continuous (fun g : Ω ≃ₐ[↥(decompField k Ω A)] Ω =>
      AlgEquiv.restrictScalars k g))
    (c : ↥(Work.AbsoluteKummer.Z1 (Ω ≃ₐ[k] Ω) (Work.SSGRoute.homCoind k Ω K R))) :
    (fun g : Ω ≃ₐ[↥(decompField k Ω A)] Ω => c.1 (AlgEquiv.restrictScalars k g))
      ∈ Work.AbsoluteKummer.Z1 (Ω ≃ₐ[↥(decompField k Ω A)] Ω)
          (Work.SSGRoute.homCoind ↥(decompField k Ω A) Ω
            (henselOverDecomp k Ω K A) (Rep.res φ R)) := by
  rw [Work.AbsoluteKummer.mem_Z1_iff]
  refine ⟨?_, ?_⟩
  · intro g h
    have h1 : Work.GroupCohomology.IsCrossedHom (Ω ≃ₐ[k] Ω)
        (Work.SSGRoute.homCoind k Ω K R) c.1 :=
      ((Work.AbsoluteKummer.mem_Z1_iff c.1).mp c.2).1
    have h2 := h1 (AlgEquiv.restrictScalars k g) (AlgEquiv.restrictScalars k h)
    have hmap : AlgEquiv.restrictScalars k (g * h)
        = AlgEquiv.restrictScalars k g * AlgEquiv.restrictScalars k h := by
      ext x; rfl
    dsimp only
    rw [hmap, h2]
    congr 1
    exact (homCoind_levelChange_smul A R φ hφres g
      (c.1 (AlgEquiv.restrictScalars k h))).symm
  · rw [Work.AbsoluteKummer.isLocallyConstant_iff]
    intro g
    obtain ⟨U₁, hU₁open, hg₁, hU₁⟩ :=
      (Work.AbsoluteKummer.isLocallyConstant_iff.mp
        ((Work.AbsoluteKummer.mem_Z1_iff c.1).mp c.2).2) (AlgEquiv.restrictScalars k g)
    refine ⟨(fun g : Ω ≃ₐ[↥(decompField k Ω A)] Ω => AlgEquiv.restrictScalars k g) ⁻¹' U₁,
      hU₁open.preimage hψc, hg₁, ?_⟩
    intro y hy
    exact hU₁ (AlgEquiv.restrictScalars k y) hy

end

end Work.SSGRoute.E1aClean
