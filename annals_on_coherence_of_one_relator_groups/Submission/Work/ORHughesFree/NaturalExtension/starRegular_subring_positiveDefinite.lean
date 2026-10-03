import Mathlib
import Submission.Work.ORHughesFree.StarRegular
import Submission.Work.ORHughesFree.StarRegular.vonNeumannRegularRing_matrix

namespace Work.ORHughesFree.NaturalExtension

/-- Positive definiteness passes to a `∗`-subring: if `V` embeds into a positive definite
`∗`-regular ring `P` through an injective, `star`-preserving ring homomorphism `f`, and `V` is
already `∗`-regular, then `V` is positive definite.

Indeed `Mat_n(V)` embeds into `Mat_n(P)` entrywise via `f`.  The only non-formal input is von
Neumann regularity of `Mat_n(V)`, which holds because `V` is von Neumann regular and matrix rings
of von Neumann regular rings are von Neumann regular (`vonNeumannRegularRing_matrix`); the
properness of the involution on `Mat_n(V)` follows from that of `Mat_n(P)` (an hypothesis, since
`P` is positive definite) because `f` is injective and commutes with `star`. -/
theorem starRegular_subring_positiveDefinite {V P : Type} [Ring V] [StarRing V] [Ring P] [StarRing P]
    (f : V →+* P) (hf : Function.Injective f) (hstar : ∀ v : V, f (star v) = star (f v))
    [IsStarRegular V] (hpos : IsPositiveDefiniteStarRegular P) : IsPositiveDefiniteStarRegular V := by
  intro n
  refine ⟨Work.ORHughesFree.StarRegular.vonNeumannRegularRing_matrix n, ?_⟩
  intro A hA
  -- `star` commutes with the entrywise extension of `f` to matrices.
  have hstar_map : star (A.map f) = (star A).map f := by
    ext i j
    rw [Matrix.star_apply, Matrix.map_apply, Matrix.map_apply, Matrix.star_apply, hstar]
  -- hence `star (A.map f) * (A.map f) = 0`, so `A.map f = 0` by properness over `P`
  have hB : star (A.map f) * A.map f = 0 := by
    rw [hstar_map, ← Matrix.map_mul, hA]
    ext i j
    simp
  have hB0 : A.map f = 0 := (hpos n).proper _ hB
  -- and `f` injective then forces `A = 0`
  ext i j
  have h3 : f (A i j) = 0 := by
    have := congr_fun (congr_fun hB0 i) j
    simpa [Matrix.map_apply] using this
  have h4 : f (A i j) = f (0 : V) := by rw [h3, map_zero]
  exact hf h4

end Work.ORHughesFree.NaturalExtension
