import Mathlib
import Submission.Commons.LinearAlgebra.Matrix.Cartan.E8_dominant_unique
import Submission.Commons.LinearAlgebra.Matrix.Cartan.E8_weyl_height_bound
import Submission.Commons.LinearAlgebra.Matrix.Cartan.E8_weyl_height_eq

/-!
# Dominant weights dominate their `E₈`-Weyl orbit in the root cone

The main statement (`E8_coords_sub_weyl_mem_cone`) says: if `μ : Fin 8 → ℤ` is dominant (all its
`ω`-coordinates are nonnegative) and `L` is any word of simple reflections
`(sᵢ w)ⱼ = wⱼ - wᵢ A_{ij}` (`A = CartanMatrix.E₈`), then `μ - (wact L μ)` lies in the positive
cone of the root lattice, i.e. all its coordinates in the simple-root basis (`A⁻¹` of the vector)
are nonnegative.

This is the "fundamental-chamber" input for the representation theory of `E₈`: it implies that the
closed dominant chamber is a fundamental domain for the Weyl group
(`Commons.LinearAlgebra.Matrix.Cartan.E8_dominant_unique`), i.e. that the dominant representative
of a Weyl orbit is unique.

The proof assembles the (already formalized) classical argument:

* the height `e8htZ v = ∑ᵢ (A⁻¹ v)ᵢ = ⟪ρ, v⟫` of every Weyl conjugate of the Weyl vector `ρ` is at
  most `620 = e8htZ ρ` (`E8_weyl_height_bound`), because `⟪wρ, wρ⟫ = ⟪ρ, ρ⟫ = 620` and
  Cauchy–Schwarz bounds `⟪ρ, wρ⟫`;
* the bound `620` is attained only at `ρ` itself (`E8_weyl_height_eq`), by positive definiteness of
  the Cartan form;
* these two facts make the quantity `620 - e8htZ (wact L ρ)` a decreasing measure along the
  "reflect at a descent" algorithm, which proves `μ - wact L μ` lies in the positive cone for every
  dominant `μ` (`weyl_acts_cone_aux`).
-/

open scoped BigOperators

namespace Commons.LinearAlgebra.Matrix.Cartan

/-- **Dominant weights dominate their Weyl orbit in the cone order.**

For a dominant weight `μ : Fin 8 → ℤ` (all `ω`-coordinates nonnegative) and any word `L` of simple
reflections `(sᵢ w)ⱼ = wⱼ - wᵢ A_{ij}` with `A = CartanMatrix.E₈`, the difference `μ - wact L μ`
lies in the positive cone: all its `α`-coordinates (`A⁻¹` applied to it) are nonnegative. -/
theorem E8_coords_sub_weyl_mem_cone (μ : Fin 8 → ℤ) (hμ : ∀ i, 0 ≤ μ i) (L : List (Fin 8)) :
    ∀ j, 0 ≤ ∑ k, Commons.LinearAlgebra.Matrix.Cartan.E8NormTwo.E8inv j k *
      (μ - L.foldl (fun w (i : Fin 8) => fun j => w j - w i * CartanMatrix.E₈ i j) μ) k := by
  have hb : ∀ L : List (Fin 8), e8htZ (wact L rhoZ) ≤ 620 :=
    fun L => E8_weyl_height_bound L
  have heq : ∀ L : List (Fin 8), e8htZ (wact L rhoZ) = 620 → wact L rhoZ = rhoZ :=
    fun L h => E8_weyl_height_eq L h
  intro j
  have key := weyl_acts_cone_aux hb heq L μ hμ j
  rw [show wact L μ
      = L.foldl (fun w (i : Fin 8) => fun j => w j - w i * CartanMatrix.E₈ i j) μ from rfl] at key
  simpa only [coords, Matrix.mulVec, dotProduct] using key

end Commons.LinearAlgebra.Matrix.Cartan
