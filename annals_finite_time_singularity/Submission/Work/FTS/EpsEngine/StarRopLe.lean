/-
Copyright: work module for the Elgina finite-time singularity project.

# `Submission/Work/FTS/EpsEngine/StarRopLe.lean` — the star piece of the `Rop` slot

The `Rop` slot of `EpsDecay` decomposes as
`Rop α (PhiTil α f (Φs + E f)) = Rop α (PhiTil α f (E f)) + Rop α (PhiTil α F_* Φs) + Rop α (Theta α F_*)`
(`Rop_Uop_Vop_add` + the affineness of `PhiTil`).  This module produces the pointwise bound for the
*star* piece from `Work.FTS.VocabO2.StarPkgo2`:

    |Rop α (PhiTil α F_* Φs) z θ| ≤ Cs α · z/(1+z)      (z > 0, 0 < θ < π/2),

which is the `hS` input of `Work.FTS.EpsEngine.Rop_block_abs_le_one` (`Work.FTS.OpenPkg.WDp 4` is a
sum of the sup norms of the mixed slots, so its bound `≤ Cs α` yields the pointwise bound for the
slot `(0,0)` through `Work.FTS.OpenPkg.WDMem_of_WDp_le`).

Everything here is `sorry`-free.
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS.VocabO2
import Submission.Work.FTS.OpenPkg.Basic

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology ENNReal
open MeasureTheory Set Filter
open Work.FTS.Galerkin (Fn Fam slice)

namespace Work.FTS.EpsEngine

set_option autoImplicit false

/-- **The star piece of the `Rop` slot.** -/
theorem star_Rop_le {α Cs : ℝ} {Φs : Fn}
    (hstar : Work.FTS.VocabO2.StarPkgo2 α Cs Φs) :
    ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      |Work.Construction.Rop α (Work.Construction.PhiTil α (Work.Construction.Fstar α) Φs) z θ|
        ≤ Cs * α * z / (1 + z) := by
  obtain ⟨hmem, hbd⟩ := hstar.R
  intro z θ hz hθ0 hθ1
  have hpt := Work.FTS.OpenPkg.WDMem_of_WDp_le (l := 4)
    (f := fun z θ => (z + 1) / z
      * Work.Construction.Rop α (Work.Construction.PhiTil α (Work.Construction.Fstar α) Φs) z θ)
    hmem hbd 0 0 (by norm_num) z θ hz hθ0 hθ1
  simp only [Work.Spaces.mixed_zero_left, Work.Spaces.mixed_zero_right,
    Work.Spaces.DthIter_zero, Work.Spaces.DzIter_zero] at hpt
  -- `hpt : |(z+1)/z * X| ≤ Cs * α`, conclude `|X| ≤ Cs α · z/(1+z)`
  have hz1 : 0 < (z + 1) / z := div_pos (by linarith) hz
  have hfac : z / (1 + z) * ((z + 1) / z) = 1 := by
    field_simp
    ring
  calc |Work.Construction.Rop α (Work.Construction.PhiTil α (Work.Construction.Fstar α) Φs) z θ|
      = z / (1 + z)
          * |(z + 1) / z
              * Work.Construction.Rop α (Work.Construction.PhiTil α
                  (Work.Construction.Fstar α) Φs) z θ| := by
        rw [abs_mul, abs_of_pos hz1, ← mul_assoc, hfac, one_mul]
    _ ≤ z / (1 + z) * (Cs * α) := by
        refine mul_le_mul_of_nonneg_left hpt (by positivity)
    _ = Cs * α * z / (1 + z) := by ring

end Work.FTS.EpsEngine
