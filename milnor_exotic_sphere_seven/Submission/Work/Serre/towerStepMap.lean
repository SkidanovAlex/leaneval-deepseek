import Mathlib
import Submission.Work.Serre.genStep_extension
import Submission.Work.Serre.killStepExtension

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

namespace Work.Serre

/-!
# The tower step for the `famSpace` route to `serreC3FiniteOne`

`Work.Serre.CWModel.genStep`/`killStep` extend a based map *out of a stage of the model tower*:
`genStep` attaches `(n+2)`-cells along **constant** maps, `killStep` attaches `(n+3)`-cells along
sphere maps representing the kernel of `π_{n+2}(g)`.

The claim below extends an *arbitrary* based map `h : s.Y → L` (NOT the structure map `s.g`) over
both steps, keeping it a bijection on `π₁`, given only `π_{n+2}(L, l₀) = 0`.

Ingredients that are already proved in this workspace:
* `Work.Serre.genStep_extension s h` — an extension `h₁` over `genStep s` with `h₁ ∘ attachIncl = h`;
* `Work.Serre.killStepExtension (genStep s) l₀ h₁ hb₁ hsub` — an extension `h₂` over the killing
  step with `h₂ ∘ attachIncl = h₁`;
* `Work.Serre.CWModel.piMapN_comp` and `Work.Serre.CWModel.bijective_of_comp_of_surjective` (a
  function is bijective if it is composed with a *surjection* and the composite is bijective);
* surjectivity of `π₁` of the inclusion of a cell attachment:
  `Work.RatHurewicz.surjective_πmap_attachIncl n Y ι f y₀` (degree `n+1`; for `n = 0` this is
  exactly `π₁`) and `Work.Serre.attachIncl_piMap_bijective_of_compress m Y ι f y₀ 1` (which needs
  `1 ≤ m`, i.e. cells of dimension `m+2 ≥ 3`; use it for the killing step and for the generator
  step when `n ≥ 1`).  `Work.StemsB.πmap f 0` and `Work.Serre.piMapN f 1` are the same map.
-/

/-- **A map `π_j` of a two-step composite is bijective when the intermediate inclusion is
surjective and the composite of the two is bijective.**  The point of the formulation is that the
equality `f ∘ i = h` is only *propositional*, so the base-point transport
`Work.StemsB.homotopyGroupCast` has to be inserted; `Work.StemsB.πmap_congr` supplies it. -/
theorem πmap_comp_bijective_of_eq {X Y Z : Type} [TopologicalSpace X] [TopologicalSpace Y]
    [TopologicalSpace Z] (i : C(X, Y)) {f : C(Y, Z)} {h : C(X, Z)} (heq : f.comp i = h)
    (j : ℕ) (x : X)
    (hsurj : Function.Surjective (Work.StemsB.πmap i j x))
    (hbij : Function.Bijective (Work.StemsB.πmap h j x)) :
    Function.Bijective (Work.StemsB.πmap f j (i x)) := by
  have hbij2 : Function.Bijective (⇑(Work.StemsB.πmap (f.comp i) j x)) := by
    refine ⟨?_, ?_⟩
    · intro a b hab
      apply hbij.1
      rw [← Work.StemsB.πmap_congr heq j x a, ← Work.StemsB.πmap_congr heq j x b, hab]
    · intro z
      obtain ⟨a, ha⟩ := hbij.2 ((Work.StemsB.homotopyGroupCast
        (congrArg (fun k : C(X, Z) => k x) heq) j) z)
      refine ⟨a, ?_⟩
      have h1 := Work.StemsB.πmap_congr heq j x a
      rw [ha] at h1
      exact (Work.StemsB.homotopyGroupCast (congrArg (fun k : C(X, Z) => k x) heq) j).injective h1
  have hcomp : ⇑(Work.StemsB.πmap (f.comp i) j x)
      = fun a => Work.StemsB.πmap f j (i x) (Work.StemsB.πmap i j x a) :=
    funext fun a => Work.StemsB.πmap_comp_apply i f j x a
  rw [hcomp] at hbij2
  exact Work.Serre.CWModel.bijective_of_comp_of_surjective hbij2 hsurj

/-- The `π₁` form of `Work.Serre.πmap_comp_bijective_of_eq`: `Work.StemsB.πmap f 0` is
`Work.Serre.piMapN f 1`. -/
theorem piMapN_comp_bijective_of_eq {X Y Z : Type} [TopologicalSpace X] [TopologicalSpace Y]
    [TopologicalSpace Z] (i : C(X, Y)) {f : C(Y, Z)} {h : C(X, Z)} (heq : f.comp i = h)
    (x : X)
    (hsurj : Function.Surjective (Work.Serre.piMapN i 1 x))
    (hbij : Function.Bijective (Work.Serre.piMapN h 1 x)) :
    Function.Bijective (Work.Serre.piMapN f 1 (i x)) :=
  πmap_comp_bijective_of_eq i heq 0 x hsurj hbij

theorem towerStepMap {B : Type} [TopologicalSpace B] {b₀ : B} {n : ℕ}
    (s : Work.Serre.CWModel.StA B b₀ n) {L : Type} [TopologicalSpace L] (l₀ : L)
    (h : C(s.Y, L)) (hb : h s.y₀ = l₀)
    (hbij : Function.Bijective (Work.Serre.piMapN h 1 s.y₀))
    (hsub : Subsingleton (HomotopyGroup (Fin (n + 2)) L l₀)) :
    ∃ h' : C((Work.Serre.CWModel.killStep (Work.Serre.CWModel.genStep s)).Y, L),
      h' (Work.Serre.CWModel.killStep (Work.Serre.CWModel.genStep s)).y₀ = l₀ ∧
      Function.Bijective (Work.Serre.piMapN h' 1
        (Work.Serre.CWModel.killStep (Work.Serre.CWModel.genStep s)).y₀) := by
  classical
  -- the generator step, and the index/family of its attaching maps
  let gs : Work.Serre.CWModel.StG B b₀ n := Work.Serre.CWModel.genStep s
  let ι₁ := HomotopyGroup (Fin (n + 2)) B (s.g s.y₀)
  let f₁ : ι₁ → C(Work.RatHurewicz.cellSphere n, s.Y) :=
    fun _ => ContinuousMap.const (Work.RatHurewicz.cellSphere n) s.y₀
  obtain ⟨h₁, hh₁⟩ := Work.Serre.genStep_extension s h
  have heq₁ : h₁.comp (Work.RatHurewicz.attachIncl n s.Y ι₁ f₁) = h :=
    ContinuousMap.ext hh₁
  have hb₁ : h₁ gs.y₀ = l₀ := (hh₁ s.y₀).trans hb
  -- the inclusion of `s.Y` into the generator step is onto on `π₁`
  have hsurj₁ : Function.Surjective
      (Work.Serre.piMapN (Work.RatHurewicz.attachIncl n s.Y ι₁ f₁) 1 s.y₀) := by
    rcases Nat.eq_zero_or_pos n with hn0 | hnpos
    · subst hn0
      exact Work.RatHurewicz.surjective_πmap_attachIncl 0 s.Y ι₁ f₁ s.y₀
    · exact (Work.Serre.attachIncl_piMap_bijective_of_compress n s.Y ι₁ f₁ s.y₀ 1 le_rfl
        (by omega)).2
  have hbij₁ : Function.Bijective (Work.Serre.piMapN h₁ 1 gs.y₀) :=
    piMapN_comp_bijective_of_eq (Work.RatHurewicz.attachIncl n s.Y ι₁ f₁) heq₁ s.y₀ hsurj₁ hbij
  -- the killing step, and the index/family of its attaching maps
  let ι₂ := {α : HomotopyGroup (Fin (n + 2)) gs.Y gs.y₀ //
    Work.Serre.piMapN gs.g (n + 2) gs.y₀ α = 1}
  let f₂ : ι₂ → C(Work.RatHurewicz.cellSphere (n + 1), gs.Y) :=
    fun k => Work.RatHurewicz.killFamily (n + 1) gs.Y gs.y₀ k.1
  obtain ⟨h₂, hh₂⟩ := Work.Serre.killStepExtension gs l₀ h₁ hb₁ hsub
  have heq₂ : h₂.comp (Work.RatHurewicz.attachIncl (n + 1) gs.Y ι₂ f₂) = h₁ :=
    ContinuousMap.ext hh₂
  have hb₂ : h₂ (Work.Serre.CWModel.killStep gs).y₀ = l₀ := (hh₂ gs.y₀).trans hb₁
  -- the inclusion of the generator step into the killing step is onto on `π₁`
  have hsurj₂ : Function.Surjective
      (Work.Serre.piMapN (Work.RatHurewicz.attachIncl (n + 1) gs.Y ι₂ f₂) 1 gs.y₀) :=
    (Work.Serre.attachIncl_piMap_bijective_of_compress (n + 1) gs.Y ι₂ f₂ gs.y₀ 1 le_rfl
      (by omega)).2
  have hbij₂ : Function.Bijective (Work.Serre.piMapN h₂ 1 (Work.Serre.CWModel.killStep gs).y₀) :=
    piMapN_comp_bijective_of_eq (Work.RatHurewicz.attachIncl (n + 1) gs.Y ι₂ f₂) heq₂ gs.y₀
      hsurj₂ hbij₁
  exact ⟨h₂, hb₂, hbij₂⟩

end Work.Serre
