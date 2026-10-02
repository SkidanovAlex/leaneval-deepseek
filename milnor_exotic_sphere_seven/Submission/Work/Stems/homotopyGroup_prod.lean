import Mathlib
import Submission.Work.Stems.Pi
import Submission.Work.Stems.HomotopyGroupMap

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Homotopy groups of a product

We prove that the `N`-th homotopy group of a product is the product of the homotopy groups of the
factors:

  `πₙ(X × Y, (x, y)) ≃* πₙ(X, x) × πₙ(Y, y)`.

The isomorphism is the projection `πₙ(X × Y) → πₙ X × πₙ Y` induced by the two projections of the
product; it is a monoid homomorphism because each component is the monoid homomorphism
`HomotopyGroup.mapHom` of `Submission.Work.Stems.HomotopyGroupMap`, and it is bijective with
inverse the pairing `(⟦p⟧, ⟦q⟧) ↦ ⟦t ↦ (p t, q t)⟧`, which is manifestly inverse on loop classes.
-/

open scoped Topology Topology.Homotopy unitInterval
open ContinuousMap

namespace Work.Stems
namespace HGProd

variable {N X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

/-- The generalized loop in `X × Y` assembled from generalized loops in `X` and in `Y`. -/
def combineLoop {x : X} {y : Y} (p : ↑(Ω^ N X x)) (q : ↑(Ω^ N Y y)) :
    ↑(Ω^ N (X × Y) (x, y)) :=
  ⟨p.1.prodMk q.1, fun t ht => by
    rw [ContinuousMap.prod_eval]
    exact Prod.ext (p.2 t ht) (q.2 t ht)⟩

theorem combineLoop_homotopic {x : X} {y : Y} {p p' : ↑(Ω^ N X x)} {q q' : ↑(Ω^ N Y y)}
    (hp : GenLoop.Homotopic p p') (hq : GenLoop.Homotopic q q') :
    GenLoop.Homotopic (combineLoop p q) (combineLoop p' q') :=
  Nonempty.map2 ContinuousMap.HomotopyRel.prod hp hq

/-- Pairing of loop classes: `πₙ X × πₙ Y → πₙ (X × Y)`. -/
def combine {x : X} {y : Y} [DecidableEq N] :
    HomotopyGroup N X x → HomotopyGroup N Y y → HomotopyGroup N (X × Y) (x, y) :=
  Quotient.map₂ combineLoop (fun _ _ hp _ _ hq => combineLoop_homotopic hp hq)

theorem combine_mk {x : X} {y : Y} [DecidableEq N]
    (p : ↑(Ω^ N X x)) (q : ↑(Ω^ N Y y)) :
    combine ⟦p⟧ ⟦q⟧ = ⟦combineLoop p q⟧ := rfl

/-- `combine` as a plain function on the product. -/
def combineHom {x : X} {y : Y} [DecidableEq N] :
    HomotopyGroup N X x × HomotopyGroup N Y y → HomotopyGroup N (X × Y) (x, y) :=
  fun z => combine z.1 z.2

/-- The projection `πₙ(X × Y) → πₙ X × πₙ Y` induced by the two projections of the product. -/
noncomputable def splitHom {x : X} {y : Y} [DecidableEq N] [Nonempty N] :
    HomotopyGroup N (X × Y) (x, y) →* HomotopyGroup N X x × HomotopyGroup N Y y :=
  (HomotopyGroup.mapHom (ContinuousMap.fst : C(X × Y, X))).prod
    (HomotopyGroup.mapHom (ContinuousMap.snd : C(X × Y, Y)))

theorem combineHom_splitHom {x : X} {y : Y} [DecidableEq N] [Nonempty N]
    (c : HomotopyGroup N (X × Y) (x, y)) :
    combineHom (splitHom c) = c := by
  induction c using Quotient.inductionOn with
  | h p =>
    have h1 : combineHom (splitHom (⟦p⟧ : HomotopyGroup N (X × Y) (x, y)))
        = combine (HomotopyGroup.map (ContinuousMap.fst : C(X × Y, X)) ⟦p⟧)
                  (HomotopyGroup.map (ContinuousMap.snd : C(X × Y, Y)) ⟦p⟧) := rfl
    rw [h1, HomotopyGroup.map_mk_mapLoop, HomotopyGroup.map_mk_mapLoop, combine_mk]
    apply Quotient.sound
    have h : combineLoop (HomotopyGroup.mapLoop (ContinuousMap.fst : C(X × Y, X)) p)
        (HomotopyGroup.mapLoop (ContinuousMap.snd : C(X × Y, Y)) p) = p := by
      apply GenLoop.ext; intro t; rfl
    exact h ▸ GenLoop.Homotopic.refl _

theorem splitHom_combineHom {x : X} {y : Y} [DecidableEq N] [Nonempty N]
    (z : HomotopyGroup N X x × HomotopyGroup N Y y) :
    splitHom (combineHom z) = z := by
  obtain ⟨a, b⟩ := z
  induction a using Quotient.inductionOn with
  | h p =>
    induction b using Quotient.inductionOn with
    | h q =>
      have h2 : combineHom ((⟦p⟧, ⟦q⟧) : HomotopyGroup N X x × HomotopyGroup N Y y)
          = ⟦combineLoop p q⟧ := rfl
      have h1 : splitHom (⟦combineLoop p q⟧ : HomotopyGroup N (X × Y) (x, y))
          = (HomotopyGroup.map (ContinuousMap.fst : C(X × Y, X)) ⟦combineLoop p q⟧,
             HomotopyGroup.map (ContinuousMap.snd : C(X × Y, Y)) ⟦combineLoop p q⟧) := rfl
      rw [h2, h1, HomotopyGroup.map_mk_mapLoop, HomotopyGroup.map_mk_mapLoop]
      refine Prod.ext ?_ ?_
      · apply Quotient.sound
        have h : HomotopyGroup.mapLoop (ContinuousMap.fst : C(X × Y, X)) (combineLoop p q) = p := by
          apply GenLoop.ext; intro t; rfl
        exact h ▸ GenLoop.Homotopic.refl _
      · apply Quotient.sound
        have h : HomotopyGroup.mapLoop (ContinuousMap.snd : C(X × Y, Y)) (combineLoop p q) = q := by
          apply GenLoop.ext; intro t; rfl
        exact h ▸ GenLoop.Homotopic.refl _

/-- The projection homomorphism `πₙ(X × Y) → πₙ X × πₙ Y` is a bijection, with inverse the
pairing `combineHom`. -/
theorem splitHom_bijective {x : X} {y : Y} [DecidableEq N] [Nonempty N] :
    Function.Bijective (splitHom (N := N) (x := x) (y := y)) :=
  ⟨Function.LeftInverse.injective (g := combineHom (x := x) (y := y)) combineHom_splitHom,
   fun z => ⟨combineHom z, splitHom_combineHom z⟩⟩

end HGProd

/-- The `N`-th homotopy group of a product `X × Y` is the product of the homotopy groups of the
factors. -/
theorem homotopyGroup_prod {N X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [DecidableEq N] [Nonempty N] (x : X) (y : Y) :
    Nonempty (HomotopyGroup N (X × Y) (x, y) ≃* HomotopyGroup N X x × HomotopyGroup N Y y) :=
  ⟨MulEquiv.ofBijective (HGProd.splitHom (N := N) (x := x) (y := y)) HGProd.splitHom_bijective⟩

end Work.Stems
