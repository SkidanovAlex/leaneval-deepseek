import Mathlib
import Submission.Work.Pi6.Interfaces
set_option backward.isDefEq.respectTransparency false  -- v435port
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

/-!
# AREA SQASM (`Work.Pi6.SqCyclic`) — the objects of the argument

This file only fixes the vocabulary of the SQASM argument (the lead's §8 of
`REFS/NOTES_LEAD_PI6.md`); the mathematics lives in the sibling modules.

Given Postnikov data `g₃ : S³ → P₃`, `g₄ : E → P₄`, `g₅ : Y → P₅` of the killing tower, the
argument needs the fibre of the fibration `homotopyFibreFst g₄ : Y → E` over the base point
`e₀ ∈ E` — this is (the fibre of `homotopyFibreFst g₄` is the base change of the path–loop
fibration of `P₄`, so) a model of `K(ℤ/2,3)` in the range.  Here

* `Kfib g₃ g₄` is that fibre,
* `kfibPt g₃ g₄` its base point (the base point of `Y`), and
* `kfibIncl g₃ g₄ : Kfib → Y` the inclusion.

The composite `g₅ ∘ kfibIncl : Kfib → P₅` is the map to which `Work.Pi6.SqCyclicCore` (the
Steenrod-squared input `Sq²Sq²ι₃ ≠ 0`) is applied.
-/

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000

open CategoryTheory CategoryTheory.Limits

namespace Work.Pi6.SQASM

noncomputable section

open Work.Pi6

/-- The fibre of the fibration `Work.RatHurewicz.homotopyFibreFst g₄ : Y → E` over `e₀ ∈ E`.
Since `homotopyFibreFst g₄` is the base change of the path–loop fibration of `P₄` along `g₄`,
this is a model of `Ω P₄ = K(ℤ/2,3)` in the range. -/
abbrev Kfib {P3 : Type} [TopologicalSpace P3] {P4 : Type} [TopologicalSpace P4]
    (g3 : C(S3, P3)) (g4 : C(Ecov g3, P4)) : Type :=
  Work.StemsB.fibre (Work.RatHurewicz.homotopyFibreFst g4 (e0 g3)) (e0 g3)

/-- The base point of `Kfib`: the base point `y₀` of `Y`, which does lie over `e₀`. -/
abbrev kfibPt {P3 : Type} [TopologicalSpace P3] {P4 : Type} [TopologicalSpace P4]
    (g3 : C(S3, P3)) (g4 : C(Ecov g3, P4)) : Kfib g3 g4 :=
  ⟨y0 g3 g4, rfl⟩

/-- The inclusion of the fibre `Kfib` into `Y`. -/
abbrev kfibIncl {P3 : Type} [TopologicalSpace P3] {P4 : Type} [TopologicalSpace P4]
    (g3 : C(S3, P3)) (g4 : C(Ecov g3, P4)) : C(Kfib g3 g4, Ycov g3 g4) :=
  Work.StemsB.fibreIncl (Work.RatHurewicz.homotopyFibreFst g4 (e0 g3)) (e0 g3)

/-- The composite `Kfib → Y → P₅`, the map to which `SqCyclicCore` is applied. -/
abbrev hcomp {P3 : Type} [TopologicalSpace P3] {P4 : Type} [TopologicalSpace P4]
    {P5 : Type} [TopologicalSpace P5] (g3 : C(S3, P3)) (g4 : C(Ecov g3, P4))
    (g5 : C(Ycov g3 g4, P5)) : C(Kfib g3 g4, P5) :=
  g5.comp (kfibIncl g3 g4)

@[simp]
theorem kfibIncl_pt {P3 : Type} [TopologicalSpace P3] {P4 : Type} [TopologicalSpace P4]
    (g3 : C(S3, P3)) (g4 : C(Ecov g3, P4)) : kfibIncl g3 g4 (kfibPt g3 g4) = y0 g3 g4 := rfl

/-- **A map whose source is trivial and which sits in an exact pair is injective.** -/
theorem exact_injective_of_subsingleton {M N P : Type} [AddCommGroup M] [AddCommGroup N]
    [AddCommGroup P] (f : M →+ N) (g : N →+ P) (h : Function.Exact f g)
    (hM : Subsingleton M) : Function.Injective g := by
  have hf0 : ∀ x : M, f x = 0 := by
    intro x
    rw [Subsingleton.elim x 0, map_zero]
  have hker : ∀ y : N, g y = 0 → y = 0 := by
    intro y hy
    obtain ⟨x, hx⟩ := Set.mem_range.mp ((h y).mp hy)
    rw [← hx]
    exact hf0 x
  intro a b hab
  have h0 : g (a - b) = 0 := by rw [map_sub, hab, sub_self]
  exact sub_eq_zero.mp (hker (a - b) h0)

end

end Work.Pi6.SQASM

namespace Work.Pi6.SQASM

open CategoryTheory CategoryTheory.Limits

noncomputable section

/-- Functoriality of `hmap` on composites. -/
theorem hmap_comp (R : Type) [CommRing R] {X Y Z : Type} [TopologicalSpace X]
    [TopologicalSpace Y] [TopologicalSpace Z] (f : C(X, Y)) (g : C(Y, Z)) (i : ℕ) :
    Work.Pi6.hmap R (g.comp f) i = Work.Pi6.hmap R f i ≫ Work.Pi6.hmap R g i := by
  simp only [Work.Pi6.hmap, Work.Cohomology.chainMap]
  rw [show (TopCat.ofHom (g.comp f) : TopCat.of X ⟶ TopCat.of Z) =
      (TopCat.ofHom f ≫ TopCat.ofHom g) from rfl, Functor.map_comp,
      HomologicalComplex.homologyMap_comp]

/-- Functoriality of `cmap` on composites (contravariance). -/
theorem cmap_comp (R : Type) [CommRing R] {X Y Z : Type} [TopologicalSpace X]
    [TopologicalSpace Y] [TopologicalSpace Z] (f : C(X, Y)) (g : C(Y, Z)) (i : ℕ) :
    Work.Pi6.cmap R (g.comp f) i = Work.Pi6.cmap R g i ≫ Work.Pi6.cmap R f i := by
  simp only [Work.Pi6.cmap]
  rw [show (TopCat.ofHom (g.comp f) : TopCat.of X ⟶ TopCat.of Z) =
      (TopCat.ofHom f ≫ TopCat.ofHom g) from rfl]
  exact Work.Cohomology.singularCohomologyMap_comp R (TopCat.ofHom f) (TopCat.ofHom g) i

/-- A morphism of `ModuleCat R` is non-zero as soon as it is non-zero at one element. -/
theorem ne_zero_iff_exists_apply_ne_zero {R : Type} [Ring R] {M N : ModuleCat R}
    (f : M ⟶ N) : f ≠ 0 ↔ ∃ x : M, f.hom x ≠ 0 := by
  constructor
  · intro h
    by_contra hc
    simp only [not_exists, not_not] at hc
    exact h (ModuleCat.hom_ext (LinearMap.ext fun x => by rw [hc x]; simp))
  · rintro ⟨x, hx⟩ rfl
    exact hx (by simp)

end

end Work.Pi6.SQASM

namespace Work.Pi6.SQASM

open CategoryTheory CategoryTheory.Limits

noncomputable section

/-- **`IsEMSpaceUpTo` is monotone in the range.** -/
theorem isEMSpaceUpTo_mono {A : Type} [AddCommGroup A] {m : ℕ} (hm : 0 < m) {N N' : ℕ}
    (hN : N ≤ N') {X : Type} [TopologicalSpace X] (pt : X)
    (h : Work.Serre.IsEMSpaceUpTo A m hm N' X pt) :
    Work.Serre.IsEMSpaceUpTo A m hm N X pt :=
  ⟨h.1, fun i hi hc =>
    h.2 i hi (hc.elim (fun h1 => Or.inl h1) (fun h2 => Or.inr (le_trans h2 hN)))⟩

end

end Work.Pi6.SQASM
