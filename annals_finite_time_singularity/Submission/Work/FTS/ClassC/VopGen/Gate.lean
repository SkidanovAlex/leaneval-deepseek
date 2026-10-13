import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.EllipticEst.Cores.levelTwo_fts
import Submission.Work.FTS.EllipticEst.Cores.TSCAssembly
import Submission.Work.FTS.EllipticEst.Cores.ShiftedTwoL2Clean
import Submission.Work.FTS.EllipticEst.EllGap.ellWeak0Clean
import Submission.Work.FTS.EllipticEst.HonGaps.estStepWeak
import Submission.Work.FTS.EllipticEst.TT.WeakDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.FTS.ClassC.VopGen.Gate` — the gate chain of the level-parametric `V`-slot

The `V`-slot at level `k ≥ 2` needs the elliptic estimate `TT.EllEstUnif k`, which is the paper's
`prop:Hk`.  That estimate is assembled in the tree from the level-`0` estimate
(`TT.EllWeak0`, proved: `EllGap.level0ReHome`), the level-`2` estimate (`prop:H2`) and the clean
induction step (`HonGaps.estStepWeak`).  The level-`2` estimate in turn is assembled
(`Cores.levelTwo_of_pieces`) from the shifted level-`0` estimate (`Cores.ShiftedTwoL2Clean`,
proved) and the *six level-`2` `Tk`-slots* (`Cores.topSlotsTwo`), which are themselves assembled
(`Cores.TopSlotsTwoClean_of`) from the *single* `(1,1)`-slot bound `A11Hyp` below.

So the whole gate is the single statement `A11Hyp` (`= Cores.ASlot11Bound`, the "T2 wall"), and
the latter is the shadow of the level-`2` light-weight core inequality `CoreASlot11Hyp`
(`= Cores.Aux.coreASlot11`): the slicewise angular Agmon inequality `Prop.sliceAgmonMu` applied
to `X = D_z(z²∂_z²Ψ)` plus the radial integration by parts `Prop.radialIbpWild` with a
logarithmic cutoff in `z`, Cauchy–Schwarz, and AM–GM.

The chain proved here is `A11Hyp → TT.EllEstUnif 2 → TT.EllEstUnif k` (`k ≥ 2`); the reduction
`CoreASlot11Hyp → A11Hyp` is the sibling `VopGen.a11_of_coreASlot11`.

Everything in this file is `sorry`-free.
-/
noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.ClassC.VopGen

set_option autoImplicit false

/-- **The level-`2` light-weight core inequality** (the tree's `Cores.Aux.coreASlot11`, the
"T2 wall"): the `(1,1)`-slot of `A = z²∂_z²Ψ` against the *light* angular weight
`μ = sin(2θ)^{2-γ}` is bounded by the three light-weighted *pure* slots of `A`. -/
def CoreASlot11Hyp : Prop :=
  ∃ K : ℝ, 0 < K ∧ ∀ (α : ℝ) (F Ψ : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 / 4 →
    Work.FTS.EllipticEst.TT.EllWeakPos α 2 F Ψ →
    (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
        (Work.Spaces.pth (Work.Spaces.Dz (Work.FTS.EllipticEst.H2W.Aof Ψ)) z θ) ^ 2
          * (Work.Spaces.w z) ^ 2
          * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α))
      ≤ K * ((∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
            (Work.Spaces.Dz (Work.Spaces.Dz (Work.FTS.EllipticEst.H2W.Aof Ψ)) z θ) ^ 2
              * (Work.Spaces.w z) ^ 2
              * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α))
          + (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
            (Work.Spaces.Dz (Work.FTS.EllipticEst.H2W.Aof Ψ) z θ) ^ 2
              * (Work.Spaces.w z) ^ 2
              * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α))
          + (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
            (Work.Spaces.pthIter 2 (Work.FTS.EllipticEst.H2W.Aof Ψ) z θ) ^ 2
              * (Work.Spaces.w z) ^ 2
              * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α)))

/-- **The `(1,1)`-slot bound** (the tree's `Cores.ASlot11Bound`): the level-`2` light-weight
`(1,1)`-slot of `A = z²∂_z²Ψ`, weighted by `α⁴`, is bounded by the level-`2` energy of the
source `F`.  This is the single input of `Cores.TopSlotsTwoClean_of`. -/
def A11Hyp : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ) (F Ψ : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 / 4 →
    Work.FTS.EllipticEst.TT.EllWeakPos α 2 F Ψ →
    α ^ 4 * Work.FTS.EllipticEst.remov.Step.Tk α 1
        (Work.Spaces.DzIter 1 (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ))
      ≤ C * Work.Spaces.HkSq α 2 F

/-- **The six level-`2` `Tk`-slots from `A11Hyp`** (the tree's `Cores.TopSlotsTwoClean`). -/
theorem topSlotsTwo_of_A11 (h : A11Hyp) : ∃ C : ℝ, 0 < C ∧
    ∀ (α : ℝ) (F Ψ : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 / 4 →
      Work.FTS.EllipticEst.TT.EllWeakPos α 2 F Ψ →
      (α ^ 4 * (Work.FTS.EllipticEst.remov.Step.Tk α 1
            (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)
          + 3 * Work.FTS.EllipticEst.remov.Step.Tk α 1
            (Work.Spaces.DzIter 1 (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ))
          + Work.FTS.EllipticEst.remov.Step.Tk α 2
            (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)))
        + (Work.FTS.EllipticEst.remov.Step.Tk α 1 (Work.Spaces.pthIter 2 Ψ)
          + 3 * Work.FTS.EllipticEst.remov.Step.Tk α 1
            (Work.Spaces.DzIter 1 (Work.Spaces.pthIter 2 Ψ))
          + Work.FTS.EllipticEst.remov.Step.Tk α 2 (Work.Spaces.pthIter 2 Ψ))
        ≤ C * Work.Spaces.HkSq α 2 F := by
  obtain ⟨C0, hC0pos, h0⟩ := Work.FTS.EllipticEst.EllGap.ellWeak0Clean
  exact Work.FTS.EllipticEst.Cores.TopSlotsTwoClean_of h ⟨C0, hC0pos, h0⟩

/-- **`prop:H2` from `A11Hyp`** (Elgindi's level-`2` elliptic estimate). -/
theorem EllEstUnif_two_of_A11 (h : A11Hyp) :
    ∃ C : ℝ, 0 < C ∧ Work.FTS.EllipticEst.TT.EllEstUnif 2 C := by
  obtain ⟨C0, hC0pos, h0⟩ := Work.FTS.EllipticEst.EllGap.ellWeak0Clean
  exact Work.FTS.EllipticEst.Cores.levelTwo_of_pieces
    (Work.FTS.EllipticEst.Cores.ShiftedTwoL2Clean ⟨C0, hC0pos, h0⟩)
    (topSlotsTwo_of_A11 h)
    ⟨C0, hC0pos, h0⟩

/-- **`prop:Hk` at level `k` from `A11Hyp`**, for every `k ≥ 2`: the level-`2` estimate plus the
clean induction step (`HonGaps.estStepWeak`, the paper's §"General `ℋ^k` Case"). -/
theorem EllEstUnif_of_A11 (h : A11Hyp) (k : ℕ) (hk : 2 ≤ k) :
    ∃ C : ℝ, 0 < C ∧ Work.FTS.EllipticEst.TT.EllEstUnif k C := by
  obtain ⟨C0, hC0pos, h0⟩ := Work.FTS.EllipticEst.EllGap.ellWeak0Clean
  have hstep : ∀ k : ℕ, 3 ≤ k →
      (∃ C : ℝ, 0 < C ∧ Work.FTS.EllipticEst.TT.EllEstUnif (k - 1) C) →
      ∃ C : ℝ, 0 < C ∧ Work.FTS.EllipticEst.TT.EllEstUnif k C :=
    fun k hk3 => Work.FTS.EllipticEst.HonGaps.estStepWeak k hk3 ⟨C0, hC0pos, h0⟩
  exact Work.FTS.EllipticEst.TT.propHk_core_of ⟨C0, hC0pos, h0⟩
    (EllEstUnif_two_of_A11 h) hstep k hk

end Work.FTS.ClassC.VopGen
