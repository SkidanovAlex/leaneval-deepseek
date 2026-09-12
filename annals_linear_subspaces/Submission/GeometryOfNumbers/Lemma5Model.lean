import Mathlib
import Submission.GeometryOfNumbers.WedgeContract
import Submission.GeometryOfNumbers.WedgeExpanding
import Submission.GeometryOfNumbers.LargeBlockCovering
import Submission.Commons.Analysis.InnerProductSpace.norm_iMulti_orthonormal

/-!
# Lemma 5 in the model: π+-orthonormal directions inside the blocks

Paper §3 Lemma 5: for a `j`-plane `V ≤ ℝᵈ` whose wedge `v ∈ ∧^j ℝᵈ` has a comparable
component in the block `∧^i L ⊗ ∧^{j−i} Lᗮ` (`‖π_{j−i}(v)‖ ≽ ‖v‖`, `L = x₀` the
contracting plane), there exists an orthonormal family `u₁,…,u_i ⊆ V` with
`‖π+(u₁∧…∧u_i)‖ ≽ 1` (π+ = projection onto `∧^i L`); and orthonormal extensions preserve
this control.

In the model the planes §3 quantifies over are the Harder–Narasimhan block spans — in the
coordinate model either inside `x₀` (contracting block) or inside `x₀ᗮ` (expanding block).
For families inside a block the π-condition of Lemma 5 holds *automatically* and exactly:
the block projection acts as the identity on their wedges, and orthonormal families of any
size `i` (prefixes of an orthonormal basis of the block-plane) have `π`-norm exactly `1`:

* `norm_blockElem_le` — every block component of a `k`-vector has norm at most the vector's
  norm (`‖blockElem w r‖ ≤ ‖w‖` for `r ≤ k`), the elementary inequality behind
  `‖π(v)‖ ≽ ‖v‖ ⇒ v has a big block component`;
* **`lemma5_contracting_first`** — the model Lemma-5 first assertion on the contracting
  side: for an orthonormal basis `u : Fin j → ℝᵈ` of a coordinate `j`-plane inside `x₀`
  (`u t ∈ blockSpan ℓ`, `i ≤ j`), the first-`i` prefix is an orthonormal family inside the
  plane with `‖π₀(ιMulti (prefix i))‖ = 1` (`π₀` = projection onto `∧^i x₀`);
* **`lemma5_expanding_first`** — the mirror on the expanding side: an orthonormal family
  inside `largeSpan ℓ ⊆ x₀ᗮ` has `‖π₁(ιMulti u)‖ = 1` (`π₁` = projection onto
  `∧^i x₀ᗮ`).

All results are Mathlib-only (besides the Submission geometry modules).
-/

noncomputable section

open Module exteriorPower InnerProductGeometry Real
open scoped BigOperators
set_option autoImplicit false
set_option linter.unusedSectionVars false

open Submission.ExteriorCoordinates
open Submission.DiagonalFlow
open Submission.WedgeBlocks

namespace Submission.Lemma5Model

variable {d : ℕ}
local notation "ℝᵈ" => EuclideanSpace ℝ (Fin d)

/-- **Block components do not increase the norm**: for `r ≤ k`, the `r`-th block component
of a `k`-vector has norm at most the vector's norm (`‖blockElem w r‖²` is one term of the
Pythagorean sum over all blocks). -/
lemma norm_blockElem_le {k ℓ : ℕ} (w : WK d k) (r : ℕ) (hr : r ≤ k) :
    ‖blockElem (d := d) (k := k) (ℓ := ℓ) w r‖ ≤ ‖w‖ := by
  have hle0 : ‖blockElem (d := d) (k := k) (ℓ := ℓ) w r‖ ^ 2 ≤
      (Finset.range (k + 1)).sum (fun s : ℕ =>
        ‖blockElem (d := d) (k := k) (ℓ := ℓ) w s‖ ^ 2) := by
    exact Finset.single_le_sum (s := Finset.range (k + 1))
      (f := fun s : ℕ => ‖blockElem (d := d) (k := k) (ℓ := ℓ) w s‖ ^ 2)
      (by intro s hs; exact sq_nonneg _) (a := r) (Finset.mem_range.mpr (by omega))
  have hle : ‖blockElem (d := d) (k := k) (ℓ := ℓ) w r‖ ^ 2 ≤ ‖w‖ ^ 2 := by
    rw [← sum_normSq_blockElem (d := d) (k := k) (ℓ := ℓ) w]
    exact hle0
  have habs : |‖blockElem (d := d) (k := k) (ℓ := ℓ) w r‖| ≤ |‖w‖| := sq_le_sq.mp hle
  have hb : 0 ≤ ‖blockElem (d := d) (k := k) (ℓ := ℓ) w r‖ := norm_nonneg _
  have hw : 0 ≤ ‖w‖ := norm_nonneg _
  simpa [abs_of_nonneg hb, abs_of_nonneg hw] using habs

/-- **Lemma 5 (first assertion), model form — contracting block**: for an orthonormal basis
`u : Fin j → ℝᵈ` of a coordinate `j`-plane inside the contracting block's real span
(`u t ∈ blockSpan ℓ ⊆ x₀`) and any `0 < i ≤ j`, the first-`i` prefix `w t := u t` is an
orthonormal family inside the plane whose `π₀`-wedge (projection onto `∧^i x₀`) has norm
exactly `1`. -/
theorem lemma5_contracting_first {i j ℓ : ℕ} (hi0 : 0 < i) (hij : i ≤ j)
    (u : Fin j → ℝᵈ) (huON : Orthonormal ℝ u)
    (hu : ∀ t : Fin j, u t ∈ Submission.BlockCovering.blockSpan (d := d) ℓ) :
    ∃ w : Fin i → ℝᵈ,
      Orthonormal ℝ w ∧ (∀ t : Fin i, w t ∈ Submission.BlockCovering.blockSpan (d := d) ℓ) ∧
        ‖Submission.WedgeContract.pi0 (d := d) (k := i) ℓ
          (exteriorPower.ιMulti ℝ i w)‖ = 1 := by
  let w : Fin i → ℝᵈ := fun t => u (Fin.castLE hij t)
  have hwON : Orthonormal ℝ w := by
    dsimp [w]
    exact Orthonormal.comp huON (Fin.castLE hij) (Fin.castLE_injective hij)
  have hwmem : ∀ t : Fin i, w t ∈ Submission.BlockCovering.blockSpan (d := d) ℓ := by
    intro t
    dsimp [w]
    exact hu (Fin.castLE hij t)
  refine ⟨w, hwON, hwmem, ?_⟩
  have hfix := Submission.WedgeContract.pi0_ιMulti_of_mem_blockSpan (d := d) (k := i) ℓ w hwmem
  rw [hfix]
  exact Commons.Analysis.InnerProductSpace.norm_iMulti_orthonormal (E := ℝᵈ) w hwON hi0

/-- **Lemma 5 (first assertion), model form — expanding block**: an orthonormal family
`u : Fin i → ℝᵈ` of directions inside the expanding block's real span
(`u t ∈ largeSpan ℓ ⊆ x₀ᗮ`) has `π₁`-wedge (projection onto `∧^i x₀ᗮ`) of norm exactly
`1`. -/
theorem lemma5_expanding_first {i ℓ : ℕ} (hi0 : 0 < i)
    (u : Fin i → ℝᵈ) (huON : Orthonormal ℝ u)
    (hu : ∀ t : Fin i, u t ∈ Submission.LargeBlockCovering.largeSpan (d := d) ℓ) :
    ‖Submission.WedgeExpanding.pi1 (d := d) (k := i) ℓ
        (exteriorPower.ιMulti ℝ i u)‖ = 1 := by
  have hfix := Submission.WedgeExpanding.pi1_ιMulti_of_mem_largeSpan (d := d) (k := i) ℓ u hu
  rw [hfix]
  exact Commons.Analysis.InnerProductSpace.norm_iMulti_orthonormal (E := ℝᵈ) u huON hi0

end Submission.Lemma5Model
