import Mathlib.Analysis.Convex.Body
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.LinearAlgebra.FiniteDimensional.Defs

namespace Commons.Geometry.Convex.Hadwiger

open Filter
open scoped Topology Pointwise

/-- The functional `x ↦ inner ℝ u x` maps the Minkowski sum of the two bodies
to the pointwise sum of their images. -/
private lemma image_add_image {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (K L : ConvexBody V) (u : V) :
    (fun x : V => inner ℝ u x) '' ((K : Set V) + (L : Set V)) =
      (fun x : V => inner ℝ u x) '' (K : Set V) +
        (fun x : V => inner ℝ u x) '' (L : Set V) := by
  let f : V → ℝ := fun x : V => inner ℝ u x
  have hf : ∀ a b : V, f (a + b) = f a + f b := by
    intro a b
    simp [f, inner_add_right]
  calc
    f '' ((K : Set V) + (L : Set V))
        = f '' (Set.image2 (· + ·) (K : Set V) (L : Set V)) := by rfl
    _ = Set.image2 (fun a b : V => f (a + b)) (K : Set V) (L : Set V) := by
        simpa using (Set.image_image2 (s := (K : Set V)) (t := (L : Set V)) (f := (· + ·)) (g := f))
    _ = Set.image2 (fun a b : V => f a + f b) (K : Set V) (L : Set V) := by
        apply Set.image2_congr'
        intro a b
        exact hf a b
    _ = Set.image2 (· + ·) (f '' (K : Set V)) (f '' (L : Set V)) := by
        rw [Set.image2_image_left, Set.image2_image_right]
    _ = (f '' (K : Set V)) + (f '' (L : Set V)) := by rfl

private lemma bddAbove_image {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (K : ConvexBody V) (u : V) :
    BddAbove ((fun x : V => inner ℝ u x) '' (K : Set V)) := by
  refine IsCompact.bddAbove_image K.isCompact ?_
  exact ((innerSL ℝ u).continuous).continuousOn

private lemma nonempty_image {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (K : ConvexBody V) (u : V) :
    ((fun x : V => inner ℝ u x) '' (K : Set V)).Nonempty := by
  exact (K.nonempty.image (fun x : V => inner ℝ u x))

theorem support_add
    (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [CompleteSpace V] [FiniteDimensional ℝ V]
    (K L : ConvexBody V) (u : V) :
    sSup ((fun x : V => inner ℝ u x) '' ((K + L : ConvexBody V) : Set V)) =
      sSup ((fun x : V => inner ℝ u x) '' (K : Set V)) +
        sSup ((fun x : V => inner ℝ u x) '' (L : Set V)) := by
  rw [ConvexBody.coe_add]
  rw [image_add_image]
  rw [csSup_add (nonempty_image K u) (bddAbove_image K u) (nonempty_image L u) (bddAbove_image L u)]

end Commons.Geometry.Convex.Hadwiger