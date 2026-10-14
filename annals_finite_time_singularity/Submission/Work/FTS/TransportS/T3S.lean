import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.H2.T3Q.HardTheta
import Submission.Work.FTS.H2.T3Q.T3Q
import Submission.Work.FTS.TransportS.Defs
import Submission.Work.FTS.TransportS.GalSide

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.TransportS

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false

/-! ## The hypothesis bundles -/

/-- The frozen `f`-side hypotheses of `T3S_Dz`. -/
def T3SF (α : ℝ) (f : Fn) : Prop :=
  Work.FTS.EllipticEst.SmoothOpen f ∧ Work.Spaces.WlInfMem α 4 f
    ∧ Work.FTS.VocabO.CoefThMem 3 f

/-- The frozen `g`-side hypotheses of `T3S_Dz`. -/
def T3SG (α : ℝ) (g : Fn) : Prop :=
  Work.FTS.Nonlin.RegQ α 4 g ∧ Work.Spaces.HkMem α 5 g ∧ Work.Spaces.DecayAll 4 g

theorem T3SF.smoothOpen {α : ℝ} {f : Fn} (h : T3SF α f) :
    Work.FTS.EllipticEst.SmoothOpen f := h.1
theorem T3SF.coef {α : ℝ} {f : Fn} (h : T3SF α f) : Work.FTS.VocabO.CoefThMem 3 f := h.2.2
theorem T3SG.reg {α : ℝ} {g : Fn} (h : T3SG α g) : Work.FTS.Nonlin.RegQ α 4 g := h.1
theorem T3SG.hk4 {α : ℝ} {g : Fn} (h : T3SG α g) : Work.Spaces.HkMem α 4 g := h.1.2.1
theorem T3SG.hk5 {α : ℝ} {g : Fn} (h : T3SG α g) : Work.Spaces.HkMem α 5 g := h.2.1


/-! ## The three inputs of the `D_z` half -/




/-! ## The frozen statement as a `Prop` (no proof obligations here) -/


end Work.FTS.TransportS
