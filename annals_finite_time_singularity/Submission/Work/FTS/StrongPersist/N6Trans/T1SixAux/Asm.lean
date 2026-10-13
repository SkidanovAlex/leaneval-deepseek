/-
Copyright: work module for the Elgindi finite-time singularity project.

# Assembly helpers for `slotT1Six`

The elementary analytic ingredients of the level-six per-slot `D_θ`-transport bound
`Work.FTS.StrongPersist.N6Trans.slotT1Six`:

* `SmoothOpenMul` — `SmoothOpen` is closed under products;
* `slotSliceIntegrable` — the `θ`-slice of the `canonW q`-weighted square of the slot
  `mixed b a g` is integrable for `q ∈ [0,γ]` (`q ≤ η` when `a = 0`);
* `slotEnergyZOuter` — its `z`-marginal is integrable and the `z`-outer iterated integral is at
  most `HkSq α 6 g` (from `SixAux.slotEnergy6`, which is stated in the `θ`-outer order, via
  Fubini).

All declarations here are `sorry`-free.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.MeasureTheory.Integral.Prod
import Submission.Work.FTS.TransportS.Slots
import Submission.Work.FTS.TransportS.SlotT2.Basic
import Submission.Work.FTS.StrongPersist.N6Trans.T1SixAux.Basic
import Submission.Work.FTS.StrongPersist.N6Trans.SixAux.slotEnergy6

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.N6Trans.T1SixAux

open Work.FTS.TransportS.SlotT2 (canonW canonW_nonneg canonW_zero_z)

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

/-- `SmoothOpen` is closed under pointwise products. -/
theorem SmoothOpenMul {F G : ℝ → ℝ → ℝ} (hF : Work.FTS.EllipticEst.SmoothOpen F)
    (hG : Work.FTS.EllipticEst.SmoothOpen G) :
    Work.FTS.EllipticEst.SmoothOpen (fun z θ => F z θ * G z θ) := by
  unfold Work.FTS.EllipticEst.SmoothOpen at *
  convert hF.mul hG using 1
  ext p
  rfl

/-- The `θ`-slice of the `canonW q`-weighted square of the slot `mixed b a g` is integrable,
for `q ∈ [0,γ]` (`q ≤ η` when `a = 0`). -/
theorem slotSliceIntegrable (α q : ℝ) {g : ℝ → ℝ → ℝ}
    (hG : Work.FTS.EllipticEst.SmoothOpen g) (hmg : Work.Spaces.HkMem α 6 g)
    {a b : ℕ} (hqγ : q ≤ Work.Spaces.gam α) (hqη : a = 0 → q ≤ Work.Spaces.eta)
    (hab : a + b ≤ 6) {z : ℝ} (hz : z ∈ Work.Spaces.Iz) :
    MeasureTheory.IntegrableOn (fun θ : ℝ =>
      canonW q z θ * (Work.Spaces.mixed b a g z θ) ^ 2) Work.Spaces.Iθ := by
  rcases eq_or_lt_of_le (show (0 : ℝ) ≤ z from hz) with h0 | hz0
  · subst h0
    rw [show (fun θ : ℝ => canonW q 0 θ * (Work.Spaces.mixed b a g 0 θ) ^ 2)
        = fun _ => (0 : ℝ) from by
      funext θ; rw [canonW_zero_z, zero_mul]]
    exact integrableOn_zero
  · refine MeasureTheory.Integrable.mono' (hmg.1 z hz)
      (Work.FTS.TransportS.SlotT2.mslot_slice_aesm (q := q) hG b a hz0) ?_
    filter_upwards [Work.FTS.TransportS.ae_mem_Ioo_Iθ] with θ hθ
    rw [Real.norm_of_nonneg (mul_nonneg (canonW_nonneg ⟨hθ.1.le, hθ.2.le⟩) (sq_nonneg _))]
    exact Work.FTS.StrongPersist.N6Trans.SixAux.canonW_mixed_le6_open α q g a b hqγ hqη hab hθ

/-- The `z`-marginal of the `canonW q`-weighted square of the slot `mixed b a g` is
integrable, and the `z`-outer iterated integral is at most `HkSq α 6 g`. -/
theorem slotEnergyZOuter (α q : ℝ) {g : ℝ → ℝ → ℝ}
    (hG : Work.FTS.EllipticEst.SmoothOpen g) (hmg : Work.Spaces.HkMem α 6 g)
    {a b : ℕ} (hq0 : 0 ≤ q) (hqγ : q ≤ Work.Spaces.gam α) (hqη : a = 0 → q ≤ Work.Spaces.eta)
    (hab : a + b ≤ 6) :
    MeasureTheory.IntegrableOn (fun z : ℝ => ∫ θ in Work.Spaces.Iθ,
        canonW q z θ * (Work.Spaces.mixed b a g z θ) ^ 2) Work.Spaces.Iz ∧
      (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
        canonW q z θ * (Work.Spaces.mixed b a g z θ) ^ 2) ≤ Work.Spaces.HkSq α 6 g := by
  obtain ⟨hint, _, hbound⟩ :=
    Work.FTS.StrongPersist.N6Trans.SixAux.slotEnergy6 α q g a b hq0 hqγ hqη hab hG hmg
  refine ⟨hint.integral_prod_left, ?_⟩
  rw [MeasureTheory.integral_integral_swap
    (μ := MeasureTheory.volume.restrict Work.Spaces.Iz)
    (ν := MeasureTheory.volume.restrict Work.Spaces.Iθ)
    (f := fun z θ => canonW q z θ * (Work.Spaces.mixed b a g z θ) ^ 2) hint]
  exact hbound

end Work.FTS.StrongPersist.N6Trans.T1SixAux
