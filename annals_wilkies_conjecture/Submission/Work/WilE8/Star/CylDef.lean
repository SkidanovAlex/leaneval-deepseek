/-
  WilE8 / Star — the coordinate-forgetting projection `cylProj` underlying the cylindrical
  lift of `*`-pieces along `skipInj`.

  `Work.WilE8.skipInj n m : Fin (n+m) → Fin (n+1+m)` inserts the new coordinate at position
  `n`; `Work.WilE8.Star.insCoord n m w t` inserts a *value* at that position.  This file
  collects the two maps

  * `cylProj n m : (Fin (n+1+m) → ℝ) → (Fin (n+m) → ℝ)`, `x ↦ x ∘ skipInj` — the projection
    onto the coordinates that survive, i.e. the map whose fibres are the cylinders;
  * `newCoord n m x = x (Fin.castAdd m (Fin.last n))` — the coordinate that is inserted.

  They are mutually inverse in the appropriate sense:
  * `cylProj_insCoord` : `cylProj n m (insCoord n m w t) = w` (so `insCoord` is a section);
  * `insCoord_cylProj` : `insCoord n m (cylProj n m x) (newCoord n m x) = x` (so
    `x ↦ (cylProj n m x, newCoord n m x)` is injective, with `insCoord` as inverse);
  * `continuous_cylProj`, and the cube estimates `newCoord_mem_Icc`, `insCoord_cube`.

  Everything below is elementary; the lemmas that use this vocabulary (`cyl_image`,
  `cyl_preconnected`, `cylProj_image_cyl`, `image_connectedComponentIn_subset`) are in the
  sibling modules.
-/
import Mathlib
import Submission.Work.WilE8.Star.LiftDef
import Submission.Work.WilE8.Extend
import Submission.Work.WilE8.Basic

set_option autoImplicit false
noncomputable section
open Classical Topology
namespace Work.WilE8.Star

open WilkiesDesign WilkiesDesign.E

/-- Forget the coordinate inserted by `skipInj`. -/
def cylProj (n m : ℕ) : (Fin (n + 1 + m) → ℝ) → (Fin (n + m) → ℝ) :=
  fun x i => x (Work.WilE8.skipInj n m i)

/-- The coordinate inserted by `skipInj` (the one that `cylProj` forgets). -/
def newCoord (n m : ℕ) (x : Fin (n + 1 + m) → ℝ) : ℝ := x (Fin.castAdd m (Fin.last n))

lemma cylProj_apply (n m : ℕ) (x : Fin (n + 1 + m) → ℝ) :
    cylProj n m x = fun i => x (Work.WilE8.skipInj n m i) := rfl

lemma newCoord_apply (n m : ℕ) (x : Fin (n + 1 + m) → ℝ) :
    newCoord n m x = x (Fin.castAdd m (Fin.last n)) := rfl

lemma continuous_cylProj (n m : ℕ) : Continuous (cylProj n m) :=
  continuous_pi fun i => continuous_apply (Work.WilE8.skipInj n m i)

/-- `cylProj` is a left inverse of `insCoord`. -/
lemma cylProj_insCoord (n m : ℕ) (w : Fin (n + m) → ℝ) (t : ℝ) :
    cylProj n m (insCoord n m w t) = w :=
  funext fun i => insCoord_skipInj n m w t i

/-- Every tuple is the insertion of its new value into its `cylProj`-projection. -/
lemma insCoord_cylProj (n m : ℕ) (x : Fin (n + 1 + m) → ℝ) :
    insCoord n m (cylProj n m x) (newCoord n m x) = x :=
  insCoord_self n m x

/-- The inserted coordinate of a cube point is in `[-1,1]`. -/
lemma newCoord_mem_Icc {n m : ℕ} {x : Fin (n + 1 + m) → ℝ}
    (hx : x ∈ WilkiesDesign.E.cubeC (n + 1 + m)) : newCoord n m x ∈ Set.Icc (-1 : ℝ) 1 :=
  abs_le.mp (hx (Fin.castAdd m (Fin.last n)))

/-- Inserting a cube point and a value of modulus at most one stays in the cube. -/
lemma insCoord_cube' {n m : ℕ} {w : Fin (n + m) → ℝ} {t : ℝ}
    (hw : w ∈ WilkiesDesign.E.cubeC (n + m)) (ht : |t| ≤ 1) :
    insCoord n m w t ∈ WilkiesDesign.E.cubeC (n + 1 + m) :=
  insCoord_cube n m hw ht

/-- The cylinder over `C`, cut by the cube, is exactly the set of points whose `cylProj` lies
in `C` — with the cube condition. -/
lemma cyl_eq_preimage (n m : ℕ) (C : Set (Fin (n + m) → ℝ)) :
    ({x : Fin (n + 1 + m) → ℝ | cylProj n m x ∈ C} ∩ WilkiesDesign.E.cubeC (n + 1 + m))
      = {x : Fin (n + 1 + m) → ℝ |
          x ∈ WilkiesDesign.E.cubeC (n + 1 + m) ∧ cylProj n m x ∈ C} := by
  ext x
  exact ⟨fun h => ⟨h.2, h.1⟩, fun h => ⟨h.2, h.1⟩⟩

end Work.WilE8.Star
