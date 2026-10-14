import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS_EllLimOK.Closed
import Submission.Work.FTS_RegExport.RXT.jc3_aux
import Submission.Work.Spaces.bt_integral_weight_id
import Submission.Work.Spaces.factor_bound
import Submission.Work.Spaces.uncurry_partial_c1

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS_EllLimOK

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false

/-! ## Order-3 jet convergence -/

/-- Convergence of the `C³`-jets on the open quadrant. -/
def JConv3 (Ψn : ℕ → Fn) (Ψ : Fn) : Prop :=
  ∀ j i : ℕ, j + i ≤ 3 → ∀ z θ, (z, θ) ∈ Work.Construction.Qd →
    Tendsto (fun n => Work.Spaces.mixed j i (Ψn n) z θ) atTop
      (𝓝 (Work.Spaces.mixed j i Ψ z θ))


/-! ## The Fatou package -/

/-- **The Fatou package of a pair (source, solution)**: the ellipticity law, `C³`-regularity on
`Qd`, and the honest `ℋ⁰`-memberships, `L²`-memberships and decay that the tree's uniqueness
theorem consumes.  These are exactly the non-smoothness fields of `EllipticEst.EllHyp 0` /
`EllHypN 0`, and they are what pins the limit down to the correct solution (they exclude the
homogeneous mode `z^{-5/α} sin 2θ`). -/
def FatouPkg (α : ℝ) (f Ψ : Fn) : Prop :=
  Work.FTS.StrongGlobal.IsBslSolPos α f Ψ ∧
  ContDiffOn ℝ 3 (Function.uncurry Ψ) Work.Construction.Qd ∧
  Work.Spaces.HkMem α 0 Ψ ∧
  Work.Spaces.HkMem α 0 (Work.Spaces.pth Ψ) ∧
  Work.Spaces.HkMem α 0 (Work.Spaces.pthIter 2 Ψ) ∧
  Work.Spaces.HkMem α 0 (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) ∧
  Work.Spaces.HkMem α 0 (fun z θ => Ψ z θ / Real.cos θ) ∧
  Work.Spaces.L2Mem (Work.Spaces.pthIter 2 Ψ) ∧
  Work.Spaces.L2Mem (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) ∧
  Work.Spaces.L2Mem (fun z θ => Ψ z θ / Real.cos θ) ∧
  Work.FTS.EllipticEst.ZDecay Ψ ∧
  BoxReg Ψ

theorem FatouPkg.sol {α : ℝ} {f Ψ : Fn} (h : FatouPkg α f Ψ) :
    Work.FTS.StrongGlobal.IsBslSolPos α f Ψ := h.1

theorem FatouPkg.contDiffOn {α : ℝ} {f Ψ : Fn} (h : FatouPkg α f Ψ) :
    ContDiffOn ℝ 3 (Function.uncurry Ψ) Work.Construction.Qd := h.2.1

/-! ## The order-3 limit vocabulary -/







/-! ## The order-3 limit closure (a verbatim copy of the lead's `FinalV2.EllLimOK3`) -/

/-- **The order-`3` limit closure** (ruling §G5): as `EllLimOK`, but the limit `E f` is `C³` on
`Qd` and the jets of order `≤ 3` converge.  *Verbatim copy* of `Work.FTS.FinalV2.EllLimOK3` (same
body ⇒ definitionally equal; `FinalCore.Lead_EllLimOK3_iff` is the bridge). -/
def EllLimOK3 (α : ℝ) (E : Fn → Fn) : Prop :=
  ∀ (fn : ℕ → Fn) (f : Fn) (B : ℝ),
    (∀ n, Work.FTS.ClassC.ClassC α (fn n)) →
    (∀ n, Work.FTS.StrongGlobal.Xn6 α (fn n) ≤ B) →
    ContDiffOn ℝ 4 (Function.uncurry f) Work.Construction.Qd →
    (∀ j i : ℕ, j + i ≤ 4 → ∀ z θ, (z, θ) ∈ Work.Construction.Qd →
      Tendsto (fun n => Work.Spaces.mixed j i (fn n) z θ) atTop
        (𝓝 (Work.Spaces.mixed j i f z θ))) →
    Work.FTS.StrongGlobal.IsBslSolPos α f (E f) ∧
    ContDiffOn ℝ 3 (Function.uncurry (E f)) Work.Construction.Qd ∧
    ∀ j i : ℕ, j + i ≤ 3 → ∀ z θ, (z, θ) ∈ Work.Construction.Qd →
      Tendsto (fun n => Work.Spaces.mixed j i (E (fn n)) z θ) atTop
        (𝓝 (Work.Spaces.mixed j i (E f) z θ))

/-- `EllLimOK3` implies `EllLimOK` (a stronger conclusion on a smaller jet range). -/
theorem EllLimOK3.toEllLimOK {α : ℝ} {E : Fn → Fn} (h : EllLimOK3 α E) :
    EllLimOK α E := by
  intro fn f B hC hB h4 hj
  obtain ⟨hlaw, -, hconv⟩ := h fn f B hC hB h4 hj
  exact ⟨hlaw, fun j i hji z θ hzθ => hconv j i (by omega) z θ hzθ⟩

/-! ## The small-α obligation shapes (the ruling's `∃ α₁ > 0, ∀ α ∈ (0, α₁], ∀ Ce, …`) -/








/-- **The box data of obligation 1** (the boundary/trace half of `FatouData`): on every closed box
`[a,b] × [0,π/2]` with `0 < a ≤ b` the sequence along a `LimSeq4` converges to a limit `G` which
is jointly `C²` on the box and which vanishes on the two angular boundary lines.

This is the sequence-level form of the closed-quadrant regularity on boxes away from `z = 0`
that elliptic regularity supplies for the paper's solutions (`FTS_EllLimOK.BoxReg`); it is the
hypothesis that makes the `θ`-boundary terms of the uniqueness argument (`Lzero_self_form`,
`Lzero_orthogonal`, `angQ_ge`) vanish, and it is *not* a consequence of the integral memberships
of `FatouData`, which are stated with weights integrable at the angular endpoints.  The bridge
from primitive uniform estimates to this predicate is `FTS_EllLimOK.BoxReg_of_uniform`. -/
def BoxData (α Ce : ℝ) : Prop :=
  ∀ E : Fn →ₗ[ℝ] Fn, HasPkg α Ce E → ∀ (fn : ℕ → Fn) (f : Fn), LimSeq4 α fn f →
    ∀ a b : ℝ, 0 < a → a ≤ b → ∃ G : Fn,
      ContDiffOn ℝ 2 (Function.uncurry G) (cbox a b) ∧
      (∀ z ∈ Set.Icc a b, ∀ θ ∈ Set.Icc 0 (π / 2),
        Tendsto (fun n => E (fn n) z θ) atTop (𝓝 (G z θ))) ∧
      (∀ z ∈ Set.Icc a b, G z 0 = 0 ∧ G z (π / 2) = 0)




end Work.FTS_EllLimOK
