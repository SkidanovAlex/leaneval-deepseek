import Mathlib
import Submission.Work.Core.Defs

namespace Work.Translate

open LeanEval.Geometry.NewlanderNirenberg
open Submission
open Set
open scoped ContDiff

/-- The Lie bracket is invariant under translating the two vector fields: the Lie bracket of the
translated fields at `y` is the translate of the Lie bracket at `x + y`.

This is a computation from the definition `[F,G] = DG(F) - DF(G)`: the derivative of a translated
field is the translated derivative (`fderiv_comp_add_left`). -/
lemma lieBracket_translate {n : ℕ} (F G : E n → E n) (x y : E n) :
    VectorField.lieBracket ℝ (fun z => F (x + z)) (fun z => G (x + z)) y
      = VectorField.lieBracket ℝ F G (x + y) := by
  have h1 : fderiv ℝ (fun z : E n => G (x + z)) y = fderiv ℝ G (x + y) :=
    fderiv_comp_add_left (a := x)
  have h2 : fderiv ℝ (fun z : E n => F (x + z)) y = fderiv ℝ F (x + y) :=
    fderiv_comp_add_left (a := x)
  rw [VectorField.lieBracket, VectorField.lieBracket, h1, h2]

/-- **The Nijenhuis tensor of a translated structure.**  Translating the almost complex structure
by `x` and evaluating on `V`, `W` at `y` is the same as evaluating the original tensor on the
translated fields `z ↦ V (z - x)`, `z ↦ W (z - x)` at `x + y`. -/
lemma nijenhuis_translate {n : ℕ} (J : E n → E n →L[ℝ] E n) (V W : E n → E n) (x y : E n) :
    nijenhuis (fun y => J (x + y)) V W y
      = nijenhuis J (fun z => V (z - x)) (fun z => W (z - x)) (x + y) := by
  have hVx : ∀ z : E n, x + z - x = z := fun z => by abel
  set V' : E n → E n := fun z => V (z - x) with hV'def
  set W' : E n → E n := fun z => W (z - x) with hW'def
  have hVshift : ∀ z : E n, V' (x + z) = V z := by
    intro z; simp only [hV'def, hVx z]
  have hWshift : ∀ z : E n, W' (x + z) = W z := by
    intro z; simp only [hW'def, hVx z]
  have eFV : (fun z : E n => J (x + z) (V z))
      = fun z => (fun w => J w (V' w)) (x + z) := by
    funext z; simp only [hVshift z]
  have eFW : (fun z : E n => J (x + z) (W z))
      = fun z => (fun w => J w (W' w)) (x + z) := by
    funext z; simp only [hWshift z]
  have eV : V = fun z => V' (x + z) := by funext z; rw [hVshift z]
  have eW : W = fun z => W' (x + z) := by funext z; rw [hWshift z]
  have k1 : VectorField.lieBracket ℝ (fun z => J (x + z) (V z)) (fun z => J (x + z) (W z)) y
      = VectorField.lieBracket ℝ (fun w => J w (V' w)) (fun w => J w (W' w)) (x + y) := by
    rw [eFV, eFW]
    exact lieBracket_translate (fun w => J w (V' w)) (fun w => J w (W' w)) x y
  have k2 : VectorField.lieBracket ℝ (fun z => J (x + z) (V z)) W y
      = VectorField.lieBracket ℝ (fun w => J w (V' w)) W' (x + y) := by
    rw [eFV, eW]
    exact lieBracket_translate (fun w => J w (V' w)) W' x y
  have k3 : VectorField.lieBracket ℝ V (fun z => J (x + z) (W z)) y
      = VectorField.lieBracket ℝ V' (fun w => J w (W' w)) (x + y) := by
    rw [eV, eFW]
    exact lieBracket_translate V' (fun w => J w (W' w)) x y
  have k4 : VectorField.lieBracket ℝ V W y
      = VectorField.lieBracket ℝ V' W' (x + y) := by
    rw [eV, eW]
    exact lieBracket_translate V' W' x y
  simp only [nijenhuis]
  rw [k1, k2, k3, k4]

/-- **The vanishing of the Nijenhuis tensor is invariant under translations.**  If `J` has
vanishing Nijenhuis tensor on the open set `U`, then the translated structure
`y ↦ J (x + y)` has vanishing Nijenhuis tensor on `{y | x + y ∈ U}`.

This is the hypothesis transfer needed to run the analytic input (`Submission.DbarSolvable` at the
origin) at an arbitrary point `x` of `U`: see `Work.Translate.ofTranslate`. -/
theorem nijenhuisTranslate {n : ℕ} {U : Set (E n)} (hU : IsOpen U)
    {J : E n → E n →L[ℝ] E n} (hN : NijenhuisVanishesOn J U) (x : E n) :
    NijenhuisVanishesOn (fun y => J (x + y)) {y | x + y ∈ U} := by
  intro V W hV hW y hy
  have hV' : ContDiff ℝ ∞ (fun z : E n => V (z - x)) :=
    hV.comp (contDiff_id.sub contDiff_const)
  have hW' : ContDiff ℝ ∞ (fun z : E n => W (z - x)) :=
    hW.comp (contDiff_id.sub contDiff_const)
  have h := hN (fun z : E n => V (z - x)) (fun z : E n => W (z - x)) hV' hW' (x + y) hy
  rw [nijenhuis_translate J V W x y]
  exact h

end Work.Translate
