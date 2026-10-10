import Mathlib.RingTheory.Henselian
import Mathlib.Algebra.Field.ZMod
import Mathlib.RepresentationTheory.Rep.Res
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
import Submission.Work.SSGRoute.ArchDictionary.extOneDictNaturalH1
import Submission.Work.SSGRoute.ArchDictionary.localCoeffP2IsEquivariant
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The canonical archimedean local dictionary at a complex place, `p = 2`

## The composite to assemble

The `E`-indexed family of additive equivalences

```
  Phi E : Ac c E  ≃+  Ext¹_{D_w}(E'|, K_wˣ)
```

(the `Phi` of `LeadNatWit.ArchPlaceDict`) is the composite of four canonical, coefficient-natural
factors:

* `acH1Equiv : Ac c E ≃+ H¹(⟨c⟩,E)` — `ArchDictionary/archAcH1Natural.lean`;
* `cycTransfer : H¹(⟨c⟩,E) ≃+ H¹(D_w,E)` — `ArchDictionary/p2Link.lean`;
* the coefficient change along `localCoeffP2 : E ≃+ Hom_ℤ(E'|, K_wˣ)`, using the forward
  equivariance `localCoeffP2_fwd_isEquivariant` (this file) and the inverse one
  `localCoeffP2IsEquivariant` (`ArchDictionary/localCoeffP2IsEquivariant.lean`);
* `(extOneDictNaturalH1 D_w (K_wˣ) hdiv E'|)⁻¹ : H¹(D_w, Hom_ℤ(E'|,K_wˣ)) ≃+ Ext¹_{D_w}(E'|,K_wˣ)`
  — `ArchDictionary/extOneDictNaturalH1.lean`; use the *named* family `NatH1.eOf`, whose values do
  not depend on the auxiliary `X`/`hX`, so that it stays transparent for later computations
  (`Classical.choose` of `extOneDictNaturalH1` would destroy that transparency and hence make the
  comparison square unprovable).

The divisibility hypothesis for the dictionary is `localUnitsK_divisible_of_decompK_ne_bot`.

## Two Lean-level obstacles met while assembling it (do not rediscover them)

1. `Work.SSGRoute.H1Equiv.h1AddEquiv` is stated for `Work.AbsoluteKummer.H1`, **not** for
   `Work.GroupCohomology.H1` (which is what `homH1`, `cycTransfer` and `acH1Equiv` use), so it
   cannot be used for the coefficient change here.  The replacement is
   `AddEquiv.ofBijective (mapH1 Ψ hΦ) ⟨·,·⟩` with inverse `mapH1 Ψ⁻¹ hΨ`, using
   `Work.GroupCohomology.mapH1_comp` and `mapH1_id`.  Note that after
   `rw [← Work.GroupCohomology.mapH1_comp]` the step
   `hcoe : Ψ⁻¹.comp Ψ = AddMonoidHom.id E` must be performed by
   `simp only [hcoe, mapH1_id, AddMonoidHom.id_apply]` — a plain `rw [hcoe]` fails with
   "motive is not type correct" because the equivariance-proof argument depends on it.
2. The instance telescopes of `Work.GroupCohomology.mapH1` / `IsEquivariant` interleave the
   carriers with their instances; under `@` the order for `mapH1` is
   `G A B [Group G] [AddCommGroup A] [AddCommGroup B] [DistribMulAction G A] [DistribMulAction G B]`
   (cf. `#check @Work.GroupCohomology.mapH1_comp`), and for `IsEquivariant` it is
   `G A B [Group G] [AddCommGroup A] [AddCommGroup B] [DistribMulAction G A] [DistribMulAction G B]`.
   Every instance must be supplied by hand, because `↑(homRep X N)` is opaque (type-class search
   does not unfold `def homRep`, so it never finds `homRepDistribMulAction` by itself).
3. In a term, `show T from x` is elaborated as a `let`, which `rw`/`simp` then refuse to match
   against a pattern; either write `(x : T)` or `dsimp only` the `let` away first.

## What this file contains

Only the two self-contained pieces: the divisibility of the local units in the shape the
dictionary needs, and the *forward* equivariance of `localCoeffP2`.
-/

namespace Work.SSGRoute.ArchDictionary

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000

open CategoryTheory SSGRoute.PTExt
open scoped TensorProduct

variable {k Ω : Type} [Field k] [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]
  {K : IntermediateField k Ω} [FiniteDimensional k K] [IsGalois k K] [NumberField ↥K]

/-- **The local units at a complex place are divisible**, in the shape
`extOneDictNaturalH1`/`NatH1.eOf` need. -/
theorem localUnitsK_divisible_of_decompK_ne_bot
    (φ : Ω →+* ℂ) (w : NK.GlobalCFT.Place ↥K)
    (hw : w = NK.GlobalCFT.Place.ofInfinite
      (NumberField.InfinitePlace.mk (φ.comp (algebraMap ↥K Ω))))
    (hne : SSGRoute.PTExt.decompK (k := k) w ≠ ⊥) :
    ∀ (n : ℕ), 0 < n → ∀ y : (SSGRoute.PTExt.localUnitsK (k := k) w).V,
      ∃ x : (SSGRoute.PTExt.localUnitsK (k := k) w).V, n • x = y := by
  have hwC : (NumberField.InfinitePlace.mk (φ.comp (algebraMap ↥K Ω))).IsComplex :=
    SSGRoute.SSGStage.isComplex_of_decompK_ofInfinite_ne_bot (k := k) (K := ↥K) (hw ▸ hne)
  rw [hw]
  exact SSGRoute.SSGStage.localUnitsK_divisible_of_isComplex (k := k) (K := ↥K) hwC

/-- **Forward equivariance of `localCoeffP2`** for the `D_w`-action, deduced from the `.symm` form
`localCoeffP2IsEquivariant`. -/
theorem localCoeffP2_fwd_isEquivariant (T : Type) [AddCommGroup T] [Module (ZMod 2) T]
    [DistribMulAction (K ≃ₐ[k] K) T] [SMulCommClass (K ≃ₐ[k] K) (ZMod 2) T]
    (hT : SSGRoute.IsCyclotomicDual 2 (T := T) (SSGRoute.res k K) (-1 : Ω))
    (w : NK.GlobalCFT.Place ↥K)
    (E : Type) [AddCommGroup E] [Module (ZMod 2) E] [DistribMulAction (K ≃ₐ[k] K) E]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod 2) E] [Finite E] :
    @Work.GroupCohomology.IsEquivariant ↥(SSGRoute.PTExt.decompK (k := k) w) E
      ((Eprime 2 k Ω K T E).V →ₗ[SSGRoute.PTExt.Coeff]
        (SSGRoute.PTExt.localUnitsK (k := k) w).V) _ _ _
      (dcAct K E w)
      (Work.SSGRoute.homRepDistribMulAction
        (Rep.res (SSGRoute.PTExt.decompK (k := k) w).subtype (Eprime 2 k Ω K T E))
        (SSGRoute.PTExt.localUnitsK (k := k) w))
      ((localCoeffP2 (T := T) hT E w).toAddMonoidHom) := by
  have hΨ := localCoeffP2IsEquivariant (k := k) (Ω := Ω) (K := K) T hT w E
  letI hinst : DistribMulAction ↥(SSGRoute.PTExt.decompK (k := k) w)
      ((Eprime 2 k Ω K T E).V →ₗ[SSGRoute.PTExt.Coeff]
        (SSGRoute.PTExt.localUnitsK (k := k) w).V) :=
    Work.SSGRoute.homRepDistribMulAction
      (Rep.res (SSGRoute.PTExt.decompK (k := k) w).subtype (Eprime 2 k Ω K T E))
      (SSGRoute.PTExt.localUnitsK (k := k) w)
  intro d g
  have h := hΨ d ((localCoeffP2 (T := T) hT E w) g)
  change (localCoeffP2 (T := T) hT E w).symm
      (d • (localCoeffP2 (T := T) hT E w) g)
    = d • (localCoeffP2 (T := T) hT E w).symm
        ((localCoeffP2 (T := T) hT E w) g) at h
  rw [AddEquiv.symm_apply_apply] at h
  show (localCoeffP2 (T := T) hT E w) (d • g) = d • (localCoeffP2 (T := T) hT E w) g
  rw [← h, AddEquiv.apply_symm_apply]

end Work.SSGRoute.ArchDictionary
