import Mathlib
import Submission.Work.PTGeometric.HOFXfer
import Submission.Work.ThomBordism.boundarySign_transfer

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory
open Work.PTGeometric.HOF

namespace Work.ThomBordism

noncomputable section

variable {X Y : TopCat} {n : ℕ}

/-- **The restriction of `f` to `N`, corestricted to its image `f '' N`.** -/
def localRestr (f : X ⟶ Y) (N : Set X) : TopCat.of ↥N ⟶ TopCat.of ↥(f '' N) :=
  TopCat.ofHom ⟨fun z => ⟨f z.1, ⟨z.1, z.2, rfl⟩⟩, by
    exact Continuous.subtype_mk (f.hom.continuous.comp continuous_subtype_val)
      (fun z => ⟨z.1, z.2, rfl⟩)⟩

@[simp] theorem localRestr_apply (f : X ⟶ Y) (N : Set X) (z : ↥N) :
    (localRestr f N) z = (⟨f z.1, ⟨z.1, z.2, rfl⟩⟩ : ↥(f '' N)) := rfl

/-- **Naturality of the localisation `excM` with respect to a map of pairs.**  The square

`H_n(N, N∖{y}) --exc--> H_n(X, X∖{y}) --f_*--> H_n(Y, Y∖{f y})`

`H_n(N, N∖{y}) --(f|_N)_*--> H_n(f''N, f''N∖{f y}) --exc--> H_n(Y, Y∖{f y})`

commutes. -/
theorem excM_comp_RelHmapOf (f : X ⟶ Y) {N : Set X} {y : X}
    (hf : ∀ x, x ∉ ({y} : Set X) → f x ∉ ({f y} : Set Y))
    (h1 : ∀ z : ↥N, z ∉ trace N ({y} : Set X) →
      (localRestr f N) z ∉ trace (f '' N) ({f y} : Set Y)) :
    (RelHmapOf n f ({y} : Set X) ({f y} : Set Y) hf).comp (excM X n N ({y} : Set X))
      = (excM Y n (f '' N) ({f y} : Set Y)).comp
          (RelHmapOf n (localRestr f N) (trace N ({y} : Set X))
            (trace (f '' N) ({f y} : Set Y)) h1) := by
  have hA : ∀ z : ↥N, z ∉ trace N ({y} : Set X) →
      (Work.Cohomology.subtypeIncl X N ≫ f) z ∉ ({f y} : Set Y) :=
    fun z hz => hf z.1 hz
  have hB : ∀ z : ↥N, z ∉ trace N ({y} : Set X) →
      (localRestr f N ≫ Work.Cohomology.subtypeIncl Y (f '' N)) z ∉ ({f y} : Set Y) :=
    fun z hz => hf z.1 hz
  have hmap : Work.Cohomology.subtypeIncl X N ≫ f
      = localRestr f N ≫ Work.Cohomology.subtypeIncl Y (f '' N) := by
    apply TopCat.ext
    intro z
    rfl
  show (RelHmapOf n f ({y} : Set X) ({f y} : Set Y) hf).comp
        (RelHmapOf n (Work.Cohomology.subtypeIncl X N) (trace N ({y} : Set X)) ({y} : Set X)
          (fun z hz => hz))
      = (RelHmapOf n (Work.Cohomology.subtypeIncl Y (f '' N)) (trace (f '' N) ({f y} : Set Y))
          ({f y} : Set Y) (fun z hz => hz)).comp
        (RelHmapOf n (localRestr f N) (trace N ({y} : Set X))
          (trace (f '' N) ({f y} : Set Y)) h1)
  calc (RelHmapOf n f ({y} : Set X) ({f y} : Set Y) hf).comp
        (RelHmapOf n (Work.Cohomology.subtypeIncl X N) (trace N ({y} : Set X)) ({y} : Set X)
          (fun z hz => hz))
      = RelHmapOf n (Work.Cohomology.subtypeIncl X N ≫ f) (trace N ({y} : Set X))
          ({f y} : Set Y) hA :=
        RelHmapOf_comp (Work.Cohomology.subtypeIncl X N) f (K := trace N ({y} : Set X))
          (K' := ({y} : Set X)) (K'' := ({f y} : Set Y)) (fun z hz => hz) hf hA
    _ = RelHmapOf n (localRestr f N ≫ Work.Cohomology.subtypeIncl Y (f '' N))
          (trace N ({y} : Set X)) ({f y} : Set Y) hB :=
        RelHmapOf_congr hmap hA hB
    _ = (RelHmapOf n (Work.Cohomology.subtypeIncl Y (f '' N)) (trace (f '' N) ({f y} : Set Y))
          ({f y} : Set Y) (fun z hz => hz)).comp
        (RelHmapOf n (localRestr f N) (trace N ({y} : Set X))
          (trace (f '' N) ({f y} : Set Y)) h1) :=
        (RelHmapOf_comp (localRestr f N) (Work.Cohomology.subtypeIncl Y (f '' N))
          (K := trace N ({y} : Set X)) (K' := trace (f '' N) ({f y} : Set Y))
          (K'' := ({f y} : Set Y)) h1 (fun w hw => hw) hB).symm

/-- The applied form of `excM_comp_RelHmapOf`. -/
theorem excM_comp_RelHmapOf_apply (f : X ⟶ Y) {N : Set X} {y : X}
    (hf : ∀ x, x ∉ ({y} : Set X) → f x ∉ ({f y} : Set Y))
    (h1 : ∀ z : ↥N, z ∉ trace N ({y} : Set X) →
      (localRestr f N) z ∉ trace (f '' N) ({f y} : Set Y))
    (v : Work.Orient.RelH (TopCat.of ↥N) n (trace N ({y} : Set X))) :
    RelHmapOf n f ({y} : Set X) ({f y} : Set Y) hf (excM X n N ({y} : Set X) v)
      = excM Y n (f '' N) ({f y} : Set Y)
          (RelHmapOf n (localRestr f N) (trace N ({y} : Set X))
            (trace (f '' N) ({f y} : Set Y)) h1 v) :=
  LinearMap.congr_fun (excM_comp_RelHmapOf f hf h1) v

theorem relHmapOf_injective_of_localHomeo {n : ℕ} {X Y : TopCat} [T1Space X] (f : X ⟶ Y)
    {N : Set X} (hN : IsOpen N) {y : X} (hy : y ∈ N) (hIm : IsOpen (f '' N))
    (hyY : IsClosed ({f y} : Set Y))
    (g : ↥(f '' N) → ↥N) (hgcont : Continuous g)
    (hgf : ∀ z : ↥N, g ⟨f z.1, ⟨z.1, z.2, rfl⟩⟩ = z)
    (hfg : ∀ w : ↥(f '' N), f (g w).1 = w.1)
    (hf : ∀ x : X, x ∉ ({y} : Set X) → f x ∉ ({f y} : Set Y)) :
    Function.Injective (Work.PTGeometric.HOF.RelHmapOf n f ({y} : Set X) ({f y} : Set Y) hf) := by
  let e : TopCat.of ↥(f '' N) ⟶ TopCat.of ↥N := TopCat.ofHom ⟨g, hgcont⟩
  -- the pair conditions for the restricted map `N → f '' N` and for `g`
  have h1 : ∀ z : ↥N, z ∉ trace N ({y} : Set X) →
      (localRestr f N) z ∉ trace (f '' N) ({f y} : Set Y) := by
    intro z hz hcon
    exact hf z.1 hz hcon
  have h2 : ∀ w : ↥(f '' N), w ∉ trace (f '' N) ({f y} : Set Y) →
      e w ∉ trace N ({y} : Set X) := by
    intro w hw hcon
    refine hw ?_
    have h5 : ((g w : ↥N) : X) = y := hcon
    have h6 : ((w : ↥(f '' N)) : Y) = f ((g w : ↥N) : X) := (hfg w).symm
    show ((w : ↥(f '' N)) : Y) = f y
    rw [h6, h5]
  have h3 : ∀ z : ↥N, e ((localRestr f N) z) = z := fun z => hgf z
  have hinj : Function.Injective (RelHmapOf n (localRestr f N) (trace N ({y} : Set X))
      (trace (f '' N) ({f y} : Set Y)) h1) :=
    relHmapOf_injective_of_leftInverse (n := n) (localRestr f N) e
      (K := trace N ({y} : Set X)) (K' := trace (f '' N) ({f y} : Set Y)) h1 h2 h3
  intro a b hab
  have ha : excM X n N ({y} : Set X)
      ((punctIso X n N hN y hy isClosed_singleton).symm a) = a :=
    punctIso_excM_symm X n N hN y hy isClosed_singleton a
  have hb : excM X n N ({y} : Set X)
      ((punctIso X n N hN y hy isClosed_singleton).symm b) = b :=
    punctIso_excM_symm X n N hN y hy isClosed_singleton b
  rw [← ha, ← hb] at hab
  rw [excM_comp_RelHmapOf_apply f hf h1, excM_comp_RelHmapOf_apply f hf h1] at hab
  have hKU : ({f y} : Set Y) ⊆ f '' N := Set.singleton_subset_iff.mpr ⟨y, hy, rfl⟩
  have hEq : RelHmapOf n (localRestr f N) (trace N ({y} : Set X))
        (trace (f '' N) ({f y} : Set Y)) h1
        ((punctIso X n N hN y hy isClosed_singleton).symm a)
      = RelHmapOf n (localRestr f N) (trace N ({y} : Set X))
        (trace (f '' N) ({f y} : Set Y)) h1
        ((punctIso X n N hN y hy isClosed_singleton).symm b) :=
    (excM_injective Y n (f '' N) hIm ({f y} : Set Y) hKU hyY) hab
  have hpab := hinj hEq
  rw [← ha, ← hb, hpab]

end

end Work.ThomBordism
