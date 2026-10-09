import Mathlib
import Submission.Work.SSGRoute.E1aClean.finPlaceDict
import Submission.Work.SSGRoute.E1aClean.phiCanDefs
import Submission.Work.SSGRoute.E1aClean.henselUnits_push_iso
import Submission.Work.SSGRoute.ArchDictionary.archCruxLinkedGen
import Submission.Work.SSGRoute.E1aClean.LeadNatWit
import Submission.Work.SSGRoute.E1aClean.transferNatCoeff
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Obligation 2 of `finPlaceDict_holds`: the comparison **square**

Target (the second conjunct of `Work.SSGRoute.LeadNatWit.FinPlaceDict`, at
`Φ := Work.SSGRoute.E1aClean.phiCan …`): for every `E` and every global locally constant cocycle
`b : (Ω ≃ₐ[k] Ω) → E`,

```
SSGRoute.PTExt.extLoc (k := k) (NK.GlobalCFT.Place.ofFinite q)
    (SSGRoute.PTExt.extToIdeles (k := k)
      (Work.SSGRoute.E1aClean.globalDictionaryCanon p k Ω K ζ hζ hζK T hT E b))
  = phiCan … E (Work.SSGRoute.toClass p k Ω K E (SSGRoute.decomp k A) b)
```

## The reduction (route of `E1aClean/NOTE_localDict_finite_route_sessionN5.md` §10, steps (1)–(6))

Unfold `phiCan` (`E1aClean/phiCanDefs.lean`) — its eight factors, outermost last, are

1. `h1locSubgroupEqEquiv p E hfix.symm`  (`H1loc` along `D_A = (k^h).fixingSubgroup`),
2. `H1locEquivH1 p k Ω K E H'`,
3. `H1Equiv.h1AddEquiv Φd hΦ hΨ`  with `Φd = e1aCoeffNat` — the *same* coefficient transport that
   `globalDictionaryCanon` uses (this is what makes the square possible: it cancels),
4. `levelChangeTransferD p k Ω K A X (levelTwoGroupHom …) hφres`,
5. `(ExtChain.E1cGeneric.e1cEquiv (k := ↥k^h) … R₂).symm`,
6. the `Eq.mp`-transport along `Rep.res e.symm (Rep.res e (unitsK …)) = unitsK …` and
   `AddEquiv.refl`,
7. `extResEquivExplicit e XD (Rep.res e.toMonoidHom (unitsK …))`,
8. `AddEquiv.ofBijective ((mk₀ θ).postcomp XD (add_zero 1)) (hpush E)`  — **the push**,

and the left-hand side, after `PT.e1a_localComparison_bricks.extLoc_extToIdeles_eq`, is the
`resH1_{D_A}` of the level-one `e1cMap` of `globalDictionaryCanon … b`.  Steps (1)–(6) of §10
therefore have to compare the two `E1c` dictionaries (level one versus the henselian level two)
through (BC) `E1aClean.levelTwo_cocycle_agrees` and `E1aClean.levelChangeTransfer_H1π`, and the last
step is the push `E1aClean.henselUnits_push_iso`.

## Content of this file

The **outer end** of the square: once the inner six factors have been matched, both sides are
`(mk₀ θ).postcomp XD`-images, and matching them needs the coefficient bookkeeping of the push —
carried here by `ext_mk₀_comp_postcomp` (the push commutes with premultiplication by a degree-zero
class).  `θ` is pinned by `θ u = Units.map φ u` and does *not* depend on `E`, so this is pure `Ext`
associativity.  Further pieces are added to this module in later stretches; nothing here is
`sorry`-ed.
-/

namespace Work.SSGRoute.E1aClean

open CategoryTheory

set_option maxHeartbeats 4000000

noncomputable section

/-- **The push commutes with premultiplication by a degree-zero class.**

For a degree-zero class `θ : Ext Z₁ Z₂ 0` and a morphism `f : X₂ ⟶ X₁`, the `Ext`-composition with
`mk₀ f` on the left commutes with post-composition by `θ`:

`(mk₀ f).comp ((mk₀ θ).postcomp X₁ y) = (mk₀ θ).postcomp X₂ ((mk₀ f).comp y)`.

This is the coefficient-bookkeeping of the push factor `(mk₀ θ).postcomp XD (add_zero 1)` of `phiCan`
(the last factor of the chain, `E1aClean/henselUnits_push_iso.lean`): in the naturality square of
`PhiCan`, the coefficient change on the source side is `mk₀ (Rep.resMap (decompK w).subtype F')`,
which must slide past the push. -/
theorem ext_mk₀_comp_postcomp {C : Type*} [CategoryTheory.Category C]
    [CategoryTheory.Abelian C] [CategoryTheory.HasExt C]
    {X₁ X₂ Z₁ Z₂ : C} (f : X₂ ⟶ X₁) (θ : Z₁ ⟶ Z₂)
    (y : CategoryTheory.Abelian.Ext X₁ Z₁ 1) :
    (CategoryTheory.Abelian.Ext.mk₀ f).comp
        ((CategoryTheory.Abelian.Ext.mk₀ θ).postcomp X₁ (add_zero 1) y) (zero_add 1)
      = (CategoryTheory.Abelian.Ext.mk₀ θ).postcomp X₂ (add_zero 1)
          ((CategoryTheory.Abelian.Ext.mk₀ f).comp y (zero_add 1)) := by
  change (CategoryTheory.Abelian.Ext.mk₀ f).comp
      (y.comp (CategoryTheory.Abelian.Ext.mk₀ θ) (add_zero 1)) (zero_add 1)
    = ((CategoryTheory.Abelian.Ext.mk₀ f).comp y (zero_add 1)).comp
        (CategoryTheory.Abelian.Ext.mk₀ θ) (add_zero 1)
  exact (CategoryTheory.Abelian.Ext.comp_assoc_of_third_deg_zero
    (CategoryTheory.Abelian.Ext.mk₀ f) y (CategoryTheory.Abelian.Ext.mk₀ θ) (zero_add 1)).symm

end

end Work.SSGRoute.E1aClean

namespace Work.SSGRoute.E1aClean

open CategoryTheory

/-- **The `Eq.mp`/`AddEquiv.refl` transport of a type family is the canonical cast.**

This is the sixth factor of `phiCan`'s chain: the `Eq.mp`-transport of `AddEquiv.refl` along the
`congrArg` of an equality of the *index* of a type family applied to nothing but the identity.
Written at the level of a general family `F : C → Type*` (in `phiCan`:
`C := (↥(henselOverDecomp k Ω K A) ≃ₐ[↥(decompField k Ω A)] ↥(henselOverDecomp k Ω K A))`,
`F := fun S => CategoryTheory.Abelian.Ext R₂ S 1`, `u₁ := unitsK ↥(decompField k Ω A)
↥(henselOverDecomp k Ω K A)`, `u₂ := Rep.res e.symm (Rep.res e (unitsK …))` and
`h := (res_comp_symm_self e _).symm`), it says that the transported identity acts as the canonical
cast `h ▸ ·` — i.e. that factor 6 can be *read off* rather than computed indirectly, which is what
lets the square and the naturality chase pass through it.

Instantiate with `F := fun S => CategoryTheory.Abelian.Ext R₂ S 1` (pass `F` explicitly: the
family in the chain is syntactically `fun S => Ext R₂ A 1 ≃+ Ext R₂ S 1`). -/
theorem eq_mp_congrArg_refl_apply {C : Type*} {F : C → Type*} [∀ S, Add (F S)] {u₁ u₂ : C}
    (h : u₁ = u₂) (x : F u₁) :
    (Eq.mp (congrArg (fun S => F u₁ ≃+ F S) h) (AddEquiv.refl (F u₁))) x = h ▸ x := by
  cases h
  rfl

section InstantiationCheck

/-- **Instantiation check** at the shape in which factor 6 of `phiCan` occurs: over a
category with `Ext`, with the family `fun S => Ext R₂ S 1` (only the *second* argument of `Ext`
varies), the general transport lemma applies with `F := fun S => CategoryTheory.Abelian.Ext R₂ S 1`. -/
example {C : Type*} [CategoryTheory.Category C] [CategoryTheory.Abelian C]
    [CategoryTheory.HasExt C] (R₂ : C) {u₁ u₂ : C} (h : u₁ = u₂)
    (x : CategoryTheory.Abelian.Ext R₂ u₁ 1) :
    (Eq.mp (congrArg (fun S => CategoryTheory.Abelian.Ext R₂ u₁ 1 ≃+
      CategoryTheory.Abelian.Ext R₂ S 1) h)
      (AddEquiv.refl (CategoryTheory.Abelian.Ext R₂ u₁ 1))) x = h ▸ x :=
  eq_mp_congrArg_refl_apply (F := fun S => CategoryTheory.Abelian.Ext R₂ S 1) h x

end InstantiationCheck

end Work.SSGRoute.E1aClean

namespace Work.SSGRoute.E1aClean

open CategoryTheory

/-- **The cancellation of the shared `h1AddEquiv Φd`.**

Both `globalDictionaryCanon` and `phiCan` carry the *same* named coefficient transport
`Work.SSGRoute.H1Equiv.h1AddEquiv Φd hΦ hΨ` for `Φd = e1aCoeffNat … E`
(`E1aClean/globalDictionaryCanonDefs.lean` uses it at the global group `G_k = Ω ≃ₐ[k] Ω`, `phiCan`
at the decomposition subgroup `H' = (k^h).fixingSubgroup`).  The two instances are *related by
restriction*: for every `x : H¹(Γ, M)`,

  `resH1 Nsub N (h1AddEquiv_{Γ} Φ hΦ hΨ x) = h1AddEquiv_{↥Nsub} Φ hΦ' hΨ' (resH1 Nsub M x)`.

Since `(h1AddEquiv Φ hΦ hΨ).toFun` *is* `mapH1 Φ.toAddMonoidHom hΦ` (`h1_equiv_of_equiv.lean:65`),
this is `Work.SSGRoute.ArchDictionary.resH1_mapH1` read through that definitional identity.  With it,
the square's left-hand side — which reaches `Φd` through the *global* dictionary, restricted to
`D_A` — can be put in exactly the form `h1AddEquiv Φd` applied at `H'`, i.e. the same term as
`phiCan`'s third factor (note that the equivariance proofs are the *same* term at the two groups:
`IsEquivariant G φ` is `∀ g m, φ (g • m) = g • φ m`, and `↥H'` coerces into `G_k`). -/
theorem resH1_h1AddEquiv {Γ : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    {M N : Type} [AddCommGroup M] [DistribMulAction Γ M] [AddCommGroup N] [DistribMulAction Γ N]
    (Nsub : Subgroup Γ) (Φ : M ≃+ N)
    (hΦ : Work.GroupCohomology.IsEquivariant Γ Φ.toAddMonoidHom)
    (hΦ' : Work.GroupCohomology.IsEquivariant ↥Nsub Φ.toAddMonoidHom)
    (hΨ : Work.GroupCohomology.IsEquivariant Γ Φ.symm.toAddMonoidHom)
    (hΨ' : Work.GroupCohomology.IsEquivariant ↥Nsub Φ.symm.toAddMonoidHom)
    (x : Work.AbsoluteKummer.H1 Γ M) :
    Work.SSGRoute.PT.H2Fin.resH1 Nsub N
        ((Work.SSGRoute.H1Equiv.h1AddEquiv (G := Γ) Φ hΦ hΨ) x)
      = (Work.SSGRoute.H1Equiv.h1AddEquiv (G := ↥Nsub) Φ hΦ' hΨ')
          (Work.SSGRoute.PT.H2Fin.resH1 Nsub M x) :=
  Work.SSGRoute.ArchDictionary.resH1_mapH1 Nsub Φ.toAddMonoidHom hΦ hΦ' x

/-- **The cancellation of the shared `h1AddEquiv Φd`, inverse form.**  The same statement with the
transports read in the other direction: the transport of the *restriction* is the restriction of the
transported inverse. -/
theorem resH1_h1AddEquiv_symm {Γ : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    {M N : Type} [AddCommGroup M] [DistribMulAction Γ M] [AddCommGroup N] [DistribMulAction Γ N]
    (Nsub : Subgroup Γ) (Φ : M ≃+ N)
    (hΦ : Work.GroupCohomology.IsEquivariant Γ Φ.toAddMonoidHom)
    (hΦ' : Work.GroupCohomology.IsEquivariant ↥Nsub Φ.toAddMonoidHom)
    (hΨ : Work.GroupCohomology.IsEquivariant Γ Φ.symm.toAddMonoidHom)
    (hΨ' : Work.GroupCohomology.IsEquivariant ↥Nsub Φ.symm.toAddMonoidHom)
    (y : Work.AbsoluteKummer.H1 Γ N) :
    Work.SSGRoute.PT.H2Fin.resH1 Nsub M
        ((Work.SSGRoute.H1Equiv.h1AddEquiv (G := Γ) Φ hΦ hΨ).symm y)
      = (Work.SSGRoute.H1Equiv.h1AddEquiv (G := ↥Nsub) Φ hΦ' hΨ').symm
          (Work.SSGRoute.PT.H2Fin.resH1 Nsub N y) := by
  refine (Work.SSGRoute.H1Equiv.h1AddEquiv (G := ↥Nsub) Φ hΦ' hΨ').injective ?_
  rw [AddEquiv.apply_symm_apply]
  have h := resH1_h1AddEquiv Nsub Φ hΦ hΦ' hΨ hΨ'
    ((Work.SSGRoute.H1Equiv.h1AddEquiv (G := Γ) Φ hΦ hΨ).symm y)
  rw [AddEquiv.apply_symm_apply] at h
  exact h.symm

end Work.SSGRoute.E1aClean

namespace Work.SSGRoute.E1aClean

open CategoryTheory

variable {k : Type} [Field k] {Ω : Type} [Field Ω] [Algebra k Ω] {K : IntermediateField k Ω}

/-- **The interface between the two shapes of (BC).**

The two on-disk shapes of the base-change comparison address the restriction of a level-one cocycle
to `D_A` through *different* names for the same element of `Ω ≃ₐ[k] Ω`:

* `E1aClean.LevelTwoCocycleTarget` (`E1aClean/levelTwoDatum.lean:164`) compares `c₂.1 g` with
  `c₁.1 ↑((fixingSubgroupEquiv (decompField k Ω A)).symm g)`;
* `E1aClean.levelChangeTransfer_H1π` (`E1aClean/resH1LevelChange.lean:129`) produces the cocycle
  `fun g => c.1 (AlgEquiv.restrictScalars k g)`.

They are the same map: the coercion of `(fixingSubgroupEquiv _).symm g` into `Ω ≃ₐ[k] Ω` *is*
`AlgEquiv.restrictScalars k g`, by `AlgEquiv.ext (fun x => rfl)` — the same identification that the
definition of `levelChangeTransfer` uses (`resH1LevelChange.lean`, the `convert` step).  This lemma
is what lets the glue chain step (BC) into step `levelChangeTransfer_H1π` without a coercion detour.

Assembler: rewrite with `fixingSubgroupEquiv_symm_coe_eq_restrictScalars` under the `fun g =>`
binder (or `funext g` then the lemma) before feeding (BC) into `levelChangeTransfer_H1π`. -/
theorem fixingSubgroupEquiv_symm_coe_eq_restrictScalars (A : ValuationSubring Ω)
    (g : Ω ≃ₐ[↥(decompField k Ω A)] Ω) :
    ((↑((IntermediateField.fixingSubgroupEquiv (decompField k Ω A)).symm g) : Ω ≃ₐ[k] Ω))
      = AlgEquiv.restrictScalars k g :=
  AlgEquiv.ext (fun _ => rfl)

end Work.SSGRoute.E1aClean
namespace Work.SSGRoute.E1aClean

open CategoryTheory

variable {k : Type} [Field k] [NumberField k] {Ω : Type} [Field Ω] [Algebra k Ω]
  [IsAlgClosure k Ω] {K : IntermediateField k Ω} [FiniteDimensional k K] [IsGalois k K]
  [NumberField ↥K]

/-- **Interface (β) of the glue: `levelTwoCoeff` *is* `Rep.res` of the level-two group hom.**

`E1aClean.levelTwoDatum` defines the level-two coefficient of (BC) by
`noncomputable abbrev levelTwoCoeff … e X := Rep.res (levelTwoGroupHom k Ω K A hA q hAq e) X`
(`levelTwoDatum.lean:88`), while the level-two dictionary formula
`E1aClean.e1cMap_hensel_cocycle_formula` (`e1cMap_hensel_cocycle_formula.lean:36`) is stated for a
coefficient written `Rep.res φ X`.  The two names denote the *same* representation by definition —
so those two vocabulary layers can be used interchangeably — and this `rfl`-lemma banks the
identification as a name, so that the glue can `rw` it instead of relying on `abbrev` unfolding
(which `rw` will not always perform).

Compare interface (α) — `fixingSubgroupEquiv_symm_coe_eq_restrictScalars` — which is the same kind of
identification one level down, on the *elements* (`Ω ≃ₐ[k] Ω`) rather than on the coefficients. -/
theorem levelTwoCoeff_eq_rep_res (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A)
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ↥K))
    (hAq : ∀ x : NumberField.RingOfIntegers ↥K,
      x ∈ q.asIdeal ↔ A.valuation (((x : ↥K) : Ω)) < 1)
    (e : ↥(SSGRoute.PTExt.decompK (k := k) (NK.GlobalCFT.Place.ofFinite q)) ≃*
        (henselOverDecomp k Ω K A ≃ₐ[decompField k Ω A] henselOverDecomp k Ω K A))
    (X : Rep.{0} SSGRoute.PTExt.Coeff (K ≃ₐ[k] K)) :
    levelTwoCoeff k Ω K A hA q hAq e X
      = Rep.res (levelTwoGroupHom k Ω K A hA q hAq e) X :=
  rfl

end Work.SSGRoute.E1aClean