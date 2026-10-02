import Mathlib
import Submission.Work.Escape.Basic
import Submission.Work.Escape.tendsto_greenIter
import Submission.Work.Escape.mem_escapeRegion_iterate
import Submission.Work.Escape.geom_le_norm_iterate
import Submission.Work.Escape.norm_le_norm_iterate
import Submission.Work.Escape.tendsto_norm_iterate_atTop

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# The Green function is equivariant under the dynamics

For a `MonicGrowth f d A` map with `d ≥ 2`, the Green function `G_f` satisfies the
functional equation

`G_f (f z) = d * G_f z`,

which is the defining property of the Böttcher coordinate: the Green function is harmonic
and multiplies by the degree under the dynamics.

The proof is a one-line manipulation of the partial Green functions `greenIter f d z n =
d^{-n} log⁺ ‖f^[n] z‖`.  Since `(f^[n]) (f z) = (f^[n+1]) z` and `d * d^{-(n+1)} = d^{-n}`,

`greenIter f d (f z) n = d * greenIter f d z (n+1)`,

so the sequence `greenIter f d (f z) ·` is the shift of `greenIter f d z ·` scaled by `d`.
Both sequences have honest limits (`tendsto_greenIter`), and passing to the limit in the
shifted sequence gives the claim.
-/

open Filter Function Metric Set
open scoped Topology

noncomputable section

namespace Work.Escape

/-- The shift identity for the partial Green functions: the partial Green functions of `f z` are
the `d`-scaled shift of those of `z`. -/
theorem greenIter_comp (f : ℂ → ℂ) (d : ℕ) (z : ℂ) (n : ℕ) (_hd : 2 ≤ d) :
    greenIter f d (f z) n = (d : ℝ) * greenIter f d z (n + 1) := by
  have hd0 : (d : ℝ) ≠ 0 := by
    have : (2 : ℝ) ≤ (d : ℝ) := by exact_mod_cast _hd
    linarith
  rw [greenIter_def, greenIter_def, ← Function.iterate_succ_apply]
  have halg : ((d : ℝ) ^ n)⁻¹ = (d : ℝ) * ((d : ℝ) ^ (n + 1))⁻¹ := by
    rw [pow_succ, mul_inv]
    field_simp
  rw [halg]
  ring

theorem green_comp (f : ℂ → ℂ) (d : ℕ) (A : ℝ) (h : MonicGrowth f d A) (hd : 2 ≤ d) (z : ℂ) :
    green f d (f z) = (d : ℝ) * green f d z := by
  have h1 : Filter.Tendsto (greenIter f d (f z)) Filter.atTop (nhds (green f d (f z))) :=
    tendsto_greenIter f d A h hd (f z)
  have h2 : Filter.Tendsto (fun n : ℕ => (d : ℝ) * greenIter f d z (n + 1)) Filter.atTop
      (nhds ((d : ℝ) * green f d z)) :=
    ((tendsto_greenIter f d A h hd z).comp (tendsto_add_atTop_nat 1)).const_mul (d : ℝ)
  have h2' : Filter.Tendsto (greenIter f d (f z)) Filter.atTop
      (nhds ((d : ℝ) * green f d z)) := by
    convert h2 using 1
    funext n
    exact greenIter_comp f d z n hd
  exact tendsto_nhds_unique h1 h2'

end Work.Escape
