import Submission.Work.DSG4c.Basic
import Submission.Work.DSG4c.ChartPushout.chart_pushout
import Submission.Work.DSG4c.ProjBaseChange.isPullback_baseChangeMap_of_chartPushout
import Submission.Work.DSG4c.ClosedImmersionBaseChange.isClosedImmersion_pullback_of_isPullback

/-!
# Area DSG4c: base change of `ℙᴺ` preserves properness, surjectivity and projectivity

Main theorem: `DSMap.area_G4c_baseChange_proved`, whose type is identical to the frozen
`DSMap.area_G4c_baseChange` of `Submission/Work/DSMap/Map.lean`.

The chapter consists of

* `Work.DSG4c.Basic` — the coefficient-extension graded ring hom `coeffExt`, the induced
  morphism `Work.DSG4c.baseChangeMap : ℙᴺ_{A'} ⟶ ℙᴺ_A`, the standard charts `Work.DSG4c.chartι`
  of `ℙᴺ_A` and their structure maps;
* `Work.DSG4c.ChartPushout.chart_pushout` — base change of a standard chart is a pushout of
  rings (the crux);
* `Work.DSG4c.ProjBaseChange.isPullback_baseChangeMap_of_chartPushout` — `ℙᴺ_{A'}` is the base
  change of `ℙᴺ_A`;
* `Work.DSG4c.ClosedImmersionBaseChange.isClosedImmersion_pullback_of_isPullback` — closed
  immersions pull back along a base change square;
* `Work.DSG4c.Cover` — the chart cover of `ℙᴺ_A` and a second (local-to-global) proof of the
  base change square from the local statements on the charts.

The projective part of the main theorem is obtained by exhibiting `ℙᴺ_{A'}` as the base change of
`ℙᴺ_A` and pulling back the closed immersion `X ⟶ ℙᴺ_A`; properness and surjectivity are the
Mathlib base-change instances.
-/

open CategoryTheory AlgebraicGeometry Limits MvPolynomial

attribute [local instance] MvPolynomial.gradedAlgebra

set_option linter.style.haveILetI false

namespace Work.DSG4c

universe u

/-- **Base change of `ℙᴺ`**: `ℙᴺ_{A'}` is the fibre product of `ℙᴺ_A` over `Spec A` with
`Spec A'`, i.e. the square

```
ℙᴺ_{A'} --baseChangeMap--> ℙᴺ_A
   |                          |
   v                          v
 Spec A' -----Spec ψ------> Spec A
```
is cartesian. -/
theorem isPullback_baseChangeMap (A A' : Type u) [CommRing A] [CommRing A'] (ψ : A →+* A')
    (N : ℕ) :
    IsPullback (baseChangeMap A A' ψ N) (DSMap.PSpace.toSpec A' N) (DSMap.PSpace.toSpec A N)
      (Spec.map (CommRingCat.ofHom ψ)) :=
  ProjBaseChange.isPullback_baseChangeMap_of_chartPushout A A' ψ N fun i =>
    ChartPushout.chart_pushout A A' ψ N i

/-- **Base change preserves projectivity over `Spec`**: if `X` is a closed subscheme of
`ℙᴺ_A` over `A`, then its base change is a closed subscheme of `ℙᴺ_{A'}` over `A'`. -/
theorem isProjOver_pullback_snd (A A' : Type u) [CommRing A] [CommRing A'] (ψ : A →+* A')
    {X : Scheme.{u}} {f : X ⟶ Spec (.of A)} (hp : DSMap.IsProjOver A f) :
    DSMap.IsProjOver A' (pullback.snd f (Spec.map (CommRingCat.ofHom ψ))) := by
  obtain ⟨N, i, hi, hif⟩ := hp
  obtain ⟨j, hjc, hjs⟩ :=
    ClosedImmersionBaseChange.isClosedImmersion_pullback_of_isPullback
      (X := X) (P := DSMap.PSpace A N) (P' := DSMap.PSpace A' N) (S := Spec (.of A))
      (S' := Spec (.of A')) i (DSMap.PSpace.toSpec A N) (baseChangeMap A A' ψ N)
      (DSMap.PSpace.toSpec A' N) (Spec.map (CommRingCat.ofHom ψ))
      (isPullback_baseChangeMap A A' ψ N)
  rw [← hif]
  exact ⟨N, j, hjc, hjs⟩

end Work.DSG4c

namespace DSMap

universe a

/-- **G4c**: base change along `Spec A' ⟶ Spec A` keeps proper, surjective and projective. -/
theorem area_G4c_baseChange_proved (A A' : Type a) [CommRing A] [CommRing A'] (ψ : A →+* A')
    (X : Scheme.{a}) (f : X ⟶ Spec (.of A)) [IsProper f] (hs : Function.Surjective f)
    (hp : IsProjOver A f) :
    IsProper (pullback.snd f (Spec.map (CommRingCat.ofHom ψ))) ∧
      Function.Surjective (pullback.snd f (Spec.map (CommRingCat.ofHom ψ))) ∧
      IsProjOver A' (pullback.snd f (Spec.map (CommRingCat.ofHom ψ))) := by
  haveI : Surjective f := (surjective_iff f).mpr hs
  exact ⟨inferInstance, (surjective_iff _).mp inferInstance,
    Work.DSG4c.isProjOver_pullback_snd A A' ψ hp⟩

end DSMap
