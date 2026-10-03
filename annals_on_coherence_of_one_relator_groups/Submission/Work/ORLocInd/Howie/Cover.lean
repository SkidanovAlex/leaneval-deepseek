/-
# The cyclic cover of a graph (Howie 2000, Case 1 of Theorem 3.1)

A *labelling* of the graph `Γ` by `ℤ` is a function `θ` on the arrows with `θ (e⁻¹) = - θ e`.  It
gives

* the *level* `pathSum θ p` of a path: the sum of the labels of its arrows (well defined modulo
  cancellation of backtracks, since `θ e + θ e⁻¹ = 0`);
* the homomorphism `pathIntegral θ hθ v : F(Γ)_v →* Multiplicative ℤ`;
* the **cyclic cover** `Γ̃` (defined in `Cover/Graph.lean`), with vertex set `V × ℤ` and an arrow
  `(e, n) : (i(e), n) → (t(e), n + θ e)` for every arrow `e` of `Γ` and every level `n`, together
  with the *lift* of a path.

When `θ` vanishes on the relators of a presentation `P`, the relators lift to closed paths, and the
vertex group of the lifted presentation at `(v, 0)` is the subgroup of `π₁(⟨Γ|R⟩, v)` on which `θ`
vanishes.
-/
import Mathlib
import Submission.Work.ORLocInd.Howie.Relator
import Submission.Work.ORLocInd.Howie.Datum

set_option autoImplicit false
set_option linter.unusedVariables false

universe u

namespace Work.ORLocInd.Howie

open Quiver

variable {V : Type u} [Quiver V] [Quiver.HasInvolutiveReverse V]

namespace Quiver.Path

variable {a b c : V}

/-- The arrow list of a singleton path. -/
theorem arrowList_toPath' (e : a ⟶ b) : e.toPath.arrowList = [Quiver.Total.mk a b e] := rfl

theorem arrowList_comp' (p : Quiver.Path a b) (q : Quiver.Path b c) :
    (p.comp q).arrowList = p.arrowList ++ q.arrowList := by
  induction q with
  | nil => simp [Quiver.Path.arrowList]
  | cons q e ih => simp [Quiver.Path.arrowList_cons, ih, List.append_assoc]

theorem arrowList_reverse' (p : Quiver.Path a b) :
    p.reverse.arrowList = (p.arrowList.map Quiver.totalReverse).reverse := by
  induction p with
  | nil => simp [Quiver.Path.arrowList]
  | cons p e ih =>
    have h2 : (p.cons e).reverse = (Quiver.reverse e).toPath.comp p.reverse := rfl
    rw [h2, Quiver.Path.arrowList_comp', Quiver.Path.arrowList_toPath', ih]
    simp [Quiver.Path.arrowList_cons]

end Quiver.Path

/-- The sum of the labels of the arrows of a path (its "level"). -/
noncomputable def pathSum (θ : Quiver.Total V → ℤ) {a b : V} (p : Quiver.Path a b) : ℤ :=
  (p.arrowList.map θ).sum

theorem pathSum_nil (θ : Quiver.Total V → ℤ) (a : V) :
    pathSum θ (Quiver.Path.nil : Quiver.Path a a) = 0 := rfl

theorem pathSum_cons (θ : Quiver.Total V → ℤ) {a b c : V} (p : Quiver.Path a b) (e : b ⟶ c) :
    pathSum θ (p.cons e) = pathSum θ p + θ (Quiver.Total.mk b c e) := by
  simp [pathSum, Quiver.Path.arrowList_cons, List.sum_append]

/-- A labelling is *balanced* if it is additive under reversal of arrows. -/
def IsBalanced (θ : Quiver.Total V → ℤ) : Prop :=
  ∀ e : Quiver.Total V, θ (Quiver.totalReverse e) = - θ e

theorem pathSum_comp (θ : Quiver.Total V → ℤ) {a b c : V} (p : Quiver.Path a b)
    (q : Quiver.Path b c) : pathSum θ (p.comp q) = pathSum θ p + pathSum θ q := by
  rw [pathSum, Quiver.Path.arrowList_comp', List.map_append, List.sum_append, pathSum, pathSum]

theorem pathSum_toPath (θ : Quiver.Total V → ℤ) {a b : V} (e : a ⟶ b) :
    pathSum θ e.toPath = θ (Quiver.Total.mk a b e) := by
  simp [pathSum, Quiver.Path.arrowList_toPath']

theorem pathSum_reverse (θ : Quiver.Total V → ℤ) (hθ : IsBalanced θ) {a b : V}
    (p : Quiver.Path a b) : pathSum θ p.reverse = - pathSum θ p := by
  rw [pathSum, Quiver.Path.arrowList_reverse', List.map_reverse, List.sum_reverse, pathSum]
  have h : List.map θ (List.map Quiver.totalReverse p.arrowList)
      = List.map (fun x => - θ x) p.arrowList := by
    rw [List.map_map]
    apply List.map_congr_left
    intro x _
    exact hθ x
  rw [h]
  induction p.arrowList with
  | nil => simp
  | cons x xs ih => simp [ih]; ring

theorem pathSum_of_reducesTo (θ : Quiver.Total V → ℤ) (hθ : IsBalanced θ) {a b : V}
    {p q : Quiver.Path a b} (h : p.ReducesTo q) : pathSum θ p = pathSum θ q := by
  induction h with
  | refl => rfl
  | tail _ hstep ih =>
    obtain ⟨p₁, e, p₂⟩ := hstep
    have h1 : pathSum θ (e.toPath.comp ((Quiver.reverse e).toPath.comp p₂))
        = pathSum θ p₂ := by
      rw [pathSum_comp, pathSum_comp, pathSum_toPath, pathSum_toPath, ← Quiver.totalReverse_mk, hθ]
      ring
    have h2 : pathSum θ (p₁.comp (e.toPath.comp ((Quiver.reverse e).toPath.comp p₂)))
        = pathSum θ (p₁.comp p₂) := by
      rw [pathSum_comp, h1, pathSum_comp]
    exact ih.trans h2

end Work.ORLocInd.Howie
