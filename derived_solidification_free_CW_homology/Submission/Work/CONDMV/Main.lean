/-
# AREA CONDMV — Mayer–Vietoris for `ℤ[−]` on open covers

This file proves `Submission.Blueprint.CondMVProp`: for a topological space `X` covered by two
open subsets `U`, `V`, the square

```
  ℤ[U ∩ V]  ⟶  ℤ[V]
      |             |
      v             v
   ℤ[U]     ⟶   ℤ[X]
```

of free light condensed abelian groups is a pushout with injective legs (`ℤ[−]` denotes
`freeLightCondAbOfTopFunctor`, the free light condensed abelian group on a topological space).

The pushout statement in light condensed sets is `Work.CONDMV.isPushout_condOf` (proved in
`Submission/Work/CONDMV/Pushout.lean`) and it is transported to light condensed abelian groups by
`Work.CONDMV.isPushout_free`.  The injectivity of the legs is `Work.CONDMV.injective_app_incl`
(the map on sections induced by an inclusion of subspaces is injective) together with
`Work.CONDMV.FreeMono.mono_free_map` (the free light condensed abelian group functor preserves
monomorphisms, by sectionwise freeness and exactness of sheafification).

We also record the analogous statement for an open exhaustion `X = ⋃ₙ Aₙ` of `X` (the second half
of `REFS/01` F11).
-/
import Submission.Work.CONDMV.Pushout
import Submission.Work.CONDMV.FreeMono.mono_free_map
import Submission.Work.CONDMV.Exhaust.isColimit_exhaustCocone

open CategoryTheory Limits LightProfinite LightCondensed LightCondensed.Solid
open MonoidalCategory MonoidalClosed
open Opposite

noncomputable section

namespace Work.CONDMV

/-- The free light condensed abelian group functor sends the inclusion of a subspace to a
monomorphism. -/
theorem mono_free_map_incl {X : TopCat.{0}} {A B : Set X} (h : A ⊆ B) :
    Mono (freeLightCondAbOfTopFunctor.map (Submission.Blueprint.incl h)) :=
  FreeMono.mono_free_map _ (mono_hom_of_pointwise_injective _
    (fun S => injective_app_incl h S))

/-- **AREA CONDMV.** Mayer–Vietoris for `ℤ[−]` on an open cover: the square of free light
condensed abelian groups on `U ∩ V`, `U`, `V` and `X` is a pushout with injective legs. -/
theorem condMV_prop : Submission.Blueprint.CondMVProp := by
  intro X U V hU hV hUV
  constructor
  · exact mono_free_map_incl (Set.inter_subset_left : U ∩ V ⊆ U)
  · exact isPushout_free U V hU hV hUV

/-- For an exhaustion `X = ⋃ₙ Aₙ` by an increasing sequence of subsets such that every compact
subset of `X` is contained in some `Aₙ`, the free light condensed abelian groups `ℤ[Aₙ]` form a
colimit diagram with colimit `ℤ[X]`. -/
theorem isColimit_exhaustCocone_free {X : TopCat.{0}} (A : ℕ → Set X) (hmono : Monotone A)
    (hex : ∀ K : Set X, IsCompact K → ∃ n, K ⊆ A n) :
    Nonempty
      (IsColimit ((LightCondensed.free ℤ).mapCocone (exhaustCocone A hmono))) := by
  obtain ⟨h⟩ := Exhaust.isColimit_exhaustCocone A hmono hex
  exact ⟨isColimitOfPreserves (LightCondensed.free ℤ) h⟩

end Work.CONDMV
