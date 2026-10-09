import Mathlib
import Submission.Work.SSGRoute.PTDefs
import Submission.Work.SSGRoute.phi1_level_naturality
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Z8, step 2: composite-datum bookkeeping, coefficient level

In `SSGRoute.PTExt.VanishesAbove` the level data at `L ⊇ L₀` is `(f₀ ∘ g, Rep.resMap g ι₀ ≫ ι₁)`,
where `ι₁` is the local embedding climbing from `L₀` to `L`.  For the composite `k`-level datum at a
closure `L̃` of a `k'`-level `L`, the coefficient map is therefore a *composite*
`Rep.resMap f₂ ι₀ ≫ ι₁` of two canonical embeddings, and it must be identified with the canonical map
at the top level.

The pointwise half is the transitivity of `NK.GlobalCFT.Place.localAlgebraMapUnits`, **already proved
(sorry-free)** as `Work.SSGRoute.localAlgebraMapUnits_comp` (`phi1_level_naturality.lean`, via
`completionMap_comp_infinite` and `adicCompletionMap_comp`).  This file supplies the second half: the
upgrade of a pointwise identity on the units `Additive.ofMul u` to an identity of `Rep`-morphisms, in
the form needed here — where the source is `Rep.res f (localUnitsK k w)` for a *non-identity* `f`, so
the existing `Work.SSGRoute.localUnits_hom_ext` (stated for `f = 𝟙`) does not apply verbatim.
-/

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

namespace Work.SSGRoute

open SSGRoute.PTExt CategoryTheory

/-- **`localUnits_hom_ext`, generalised to a source `Rep.res f (localUnitsK k w)`.**  Two morphisms
out of the restriction of the local units along an arbitrary `f` which agree on `Additive.ofMul u`
for every unit `u` are equal.  (The case `f = 𝟙` is `Work.SSGRoute.localUnits_hom_ext`; the proof is
the same, `Additive.ofMul` being surjective onto the carrier.) -/
theorem localUnits_res_hom_ext {H : Type} [Group H] (k K : Type) [Field k] [NumberField k]
    [Field K] [NumberField K] [Algebra k K] [FiniteDimensional k K] [IsGalois k K]
    (w : NK.GlobalCFT.Place K) (f : H →* decompK (k := k) w)
    {B : Rep.{0} Coeff H}
    (ι ι' : Rep.res f (localUnitsK (k := k) w) ⟶ B)
    (h : ∀ u : (NK.GlobalCFT.Place.localField K w)ˣ,
      ι.hom (Additive.ofMul u) = ι'.hom (Additive.ofMul u)) :
    ι = ι' := by
  letI := (Rep.res f (localUnitsK (k := k) w)).hV2
  letI := B.hV2
  refine Rep.hom_ext ?_
  refine Representation.IntertwiningMap.ext ?_
  ext x
  obtain ⟨u, rfl⟩ := Additive.ofMul.surjective x
  exact h u

/-- **The composite-datum coefficient map, at the level of `Rep`-morphisms.**  For a tower
`K ⊆ L ⊆ L'` with places `w ∣ w' ∣ w''` and compatible group data `f₁`, `f₂`, the composite of the
two canonical coefficient maps `ι₀` (`K_wˣ → L_{w'}ˣ`) and `ι₁` (`L_{w'}ˣ → L'_{w''}ˣ`) is the
canonical map `ι` (`K_wˣ → L'_{w''}ˣ`) — the identification needed to feed the composite level datum
of `VanishesAbove` to the pairing transfer (Y3/Z1/Z2).

Proof: `localUnits_res_hom_ext` reduces to the values on `Additive.ofMul u`; the composite's value is
computed from `Rep.hom_comp`/`Rep.resMap_hom_toLinearMap`, then `hι₀ u`, then `hι₁` at the *explicit*
argument `localAlgebraMapUnits w' w h₁ u`, and finally the composite is re-formed by
`← MonoidHom.comp_apply` so that the proved transitivity `localAlgebraMapUnits_comp` can fire. -/
theorem localAlgebraMapUnits_comp_rep (k K L L' : Type) [Field k] [NumberField k] [Field K]
    [NumberField K] [Field L] [NumberField L] [Field L'] [NumberField L']
    [Algebra k K] [FiniteDimensional k K] [IsGalois k K]
    [Algebra k L] [Algebra K L] [IsScalarTower k K L] [FiniteDimensional k L] [IsGalois k L]
    [Algebra k L'] [Algebra K L'] [Algebra L L'] [IsScalarTower k L L'] [IsScalarTower K L L']
    [IsScalarTower k K L'] [FiniteDimensional k L'] [IsGalois k L']
    (w : NK.GlobalCFT.Place K) (w' : NK.GlobalCFT.Place L) (w'' : NK.GlobalCFT.Place L')
    (h₁ : NK.GlobalCFT.Place.LiesOver w' w) (h₂ : NK.GlobalCFT.Place.LiesOver w'' w')
    (h₃ : NK.GlobalCFT.Place.LiesOver w'' w)
    (f₁ : MulAction.stabilizer (L ≃ₐ[k] L) w' →* decompK (k := k) w)
    (f₂ : MulAction.stabilizer (L' ≃ₐ[k] L') w'' →* MulAction.stabilizer (L ≃ₐ[k] L) w')
    (ι₀ : Rep.res f₁ (localUnitsK (k := k) w) ⟶ NK.HassePrinciple.localUnitsRep k L w')
    (hι₀ : ∀ u : (NK.GlobalCFT.Place.localField K w)ˣ,
      ι₀.hom (Additive.ofMul u) =
        Additive.ofMul (NK.GlobalCFT.Place.localAlgebraMapUnits w' w h₁ u))
    (ι₁ : Rep.res f₂ (NK.HassePrinciple.localUnitsRep k L w') ⟶
      NK.HassePrinciple.localUnitsRep k L' w'')
    (hι₁ : ∀ v : (NK.GlobalCFT.Place.localField L w')ˣ,
      ι₁.hom (Additive.ofMul v) =
        Additive.ofMul (NK.GlobalCFT.Place.localAlgebraMapUnits w'' w' h₂ v))
    (ι : Rep.res (f₁.comp f₂) (localUnitsK (k := k) w) ⟶ NK.HassePrinciple.localUnitsRep k L' w'')
    (hι : ∀ u : (NK.GlobalCFT.Place.localField K w)ˣ,
      ι.hom (Additive.ofMul u) =
        Additive.ofMul (NK.GlobalCFT.Place.localAlgebraMapUnits w'' w h₃ u)) :
    Rep.resMap f₂ ι₀ ≫ ι₁ = ι := by
  refine localUnits_res_hom_ext k K w (f₁.comp f₂) (Rep.resMap f₂ ι₀ ≫ ι₁) ι ?_
  intro u
  have hcomp := localAlgebraMapUnits_comp (K := K) (L := L) (M := L')
    (v := w) (w := w') (w' := w'') h₂ h₁ h₃
  simp only [Rep.hom_comp, Representation.IntertwiningMap.comp_toLinearMap,
    LinearMap.comp_apply, Rep.resMap_hom_toLinearMap]
  refine (congrArg ι₁.hom (hι₀ u)).trans ?_
  refine (hι₁ (NK.GlobalCFT.Place.localAlgebraMapUnits w' w h₁ u)).trans ?_
  refine (congrArg Additive.ofMul ?_).trans (hι u).symm
  simpa only [MonoidHom.comp_apply] using congrArg (fun f => f u) hcomp

end Work.SSGRoute
