/-
# `Work.FTS.GalBasis.cc.Subcut.MajDefs` — the majorant of the final assembly

The pointwise product bound (`Subcut.HkIntegrand_sub_psiCut_le_sharp`) localises
`HkIntegrand α 4 (χ_N f)` to the set `UN N` (where the cutoff is not `1`) plus the wrong-weight slots
on the two angular layers `LN N`.  The two functions below package the two forms of that majorant:

* `Maj α C κN N f` — the **sharp** majorant, exactly the right-hand side of the pointwise bound; its
  iterated integral splits into the shrinking-mass term (`Upart_tendsto`) and the layer terms
  (`LN_layer_tendsto`), both of which tend to `0`;
* `MajRed α C κN N f` — the **reduced** majorant, in which the wrong-weight layer slots are bounded by
  the pure `D_z`-slots of `HkIntegrand α 4 f` (via `Subcut.LN_indicator_wrongWeight_le`).  It is
  pointwise larger than `Maj`, hence every integrability/measurability property of `MajRed` transfers
  to `Maj`, while the magnitude of `MajRed` is controlled by `HkIntegrand α 4 f` and `HkMem α 4 f`.
-/
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Basic.Real.Basic
import Mathlib.Order.Filter.Defs
import Submission.Work.FTS.GalBasis.cc.Subcut.Defs
import Submission.Work.FTS.GalBasis.cc.SlotDefs
import Submission.Work.Spaces.HkSq_terms

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.GalBasis.cc

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false

/-- The sharp majorant of the pointwise product bound for `χ_N f = f - ψ N · f`. -/
def Maj (α : ℝ) (C κN : ℝ) (N : ℕ) (f : Fn) : ℝ → ℝ → ℝ := fun z θ =>
  C * ((UN N).indicator (fun _ => (1 : ℝ)) (z, θ) * Work.Spaces.HkIntegrand α 4 f z θ
    + (LN N).indicator (fun _ => (1 : ℝ)) θ *
        ∑ b ∈ Finset.range 4, (zslotW α b f z θ) ^ 2)

/-- The reduced majorant: the wrong-weight slots on the layer are replaced by the pure `D_z`-slots. -/
def MajRed (α : ℝ) (C κN : ℝ) (N : ℕ) (f : Fn) : ℝ → ℝ → ℝ := fun z θ =>
  C * ((UN N).indicator (fun _ => (1 : ℝ)) (z, θ) * Work.Spaces.HkIntegrand α 4 f z θ
    + κN * ((LN N).indicator (fun _ => (1 : ℝ)) θ * Work.Spaces.HkIntegrand α 4 f z θ))

@[simp] theorem Maj_apply (α : ℝ) (C κN : ℝ) (N : ℕ) (f : Fn) (z θ : ℝ) :
    Maj α C κN N f z θ =
      C * ((UN N).indicator (fun _ => (1 : ℝ)) (z, θ) * Work.Spaces.HkIntegrand α 4 f z θ
        + (LN N).indicator (fun _ => (1 : ℝ)) θ *
            ∑ b ∈ Finset.range 4, (zslotW α b f z θ) ^ 2) := rfl

@[simp] theorem MajRed_apply (α : ℝ) (C κN : ℝ) (N : ℕ) (f : Fn) (z θ : ℝ) :
    MajRed α C κN N f z θ =
      C * ((UN N).indicator (fun _ => (1 : ℝ)) (z, θ) * Work.Spaces.HkIntegrand α 4 f z θ
        + κN * ((LN N).indicator (fun _ => (1 : ℝ)) θ * Work.Spaces.HkIntegrand α 4 f z θ)) := rfl

/-- The layer indicator distributes over the finite sum of wrong-weight slots. -/
theorem Maj_eq_sum_form (α : ℝ) (C κN : ℝ) (N : ℕ) (f : Fn) (z θ : ℝ) :
    Maj α C κN N f z θ =
      C * ((UN N).indicator (fun _ => (1 : ℝ)) (z, θ) * Work.Spaces.HkIntegrand α 4 f z θ
        + ∑ b ∈ Finset.range 4, (LN N).indicator (fun _ => (1 : ℝ)) θ *
            (zslotW α b f z θ) ^ 2) := by
  rw [Maj_apply]
  congr 1
  rw [Finset.mul_sum]

end Work.FTS.GalBasis.cc
