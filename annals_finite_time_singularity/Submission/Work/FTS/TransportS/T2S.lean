import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.TransportS.Defs
import Submission.Work.FTS.TransportS.GalSide
import Submission.Work.FTS.TransportS.sup_dz_le_hk
import Submission.Work.Spaces.factor_bound

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

/-- The frozen `f`-side hypotheses of `T2S`: interior `C^∞`, honesty of `ℋ⁴`, and the flat
angular coefficient norm.  (No decay of `f`: the pointwise bounds come from `T2SupF`.) -/
def T2SF (α : ℝ) (f : Fn) : Prop :=
  Work.FTS.EllipticEst.SmoothOpen f ∧ Work.Spaces.HkMem α 4 f ∧ Work.FTS.VocabO.CoefThMem 1 f

/-- The frozen `g`-side hypotheses of `T2S`. -/
def T2SG (α : ℝ) (g : Fn) : Prop :=
  Work.FTS.Nonlin.RegQ α 4 g ∧ Work.Spaces.HkMem α 5 g ∧ Work.Spaces.DecayAll 4 g

theorem T2SF.smoothOpen {α : ℝ} {f : Fn} (h : T2SF α f) :
    Work.FTS.EllipticEst.SmoothOpen f := h.1
theorem T2SF.hk {α : ℝ} {f : Fn} (h : T2SF α f) : Work.Spaces.HkMem α 4 f := h.2.1
theorem T2SF.coef {α : ℝ} {f : Fn} (h : T2SF α f) : Work.FTS.VocabO.CoefThMem 1 f := h.2.2
theorem T2SG.reg {α : ℝ} {g : Fn} (h : T2SG α g) : Work.FTS.Nonlin.RegQ α 4 g := h.1
theorem T2SG.hk4 {α : ℝ} {g : Fn} (h : T2SG α g) : Work.Spaces.HkMem α 4 g := h.1.2.1
theorem T2SG.hk5 {α : ℝ} {g : Fn} (h : T2SG α g) : Work.Spaces.HkMem α 5 g := h.2.1
theorem T2SG.decay {α : ℝ} {g : Fn} (h : T2SG α g) : Work.Spaces.DecayAll 4 g := h.2.2

/-! ## The five inputs -/




/-- **Input 4**: the bound on the easy part of the pairing, with the pointwise data `Mf`, `Mg`
as parameters (exactly the shape of `Work.FTS.H2.EasyQ_T2Q`). -/
def T2Easy : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ) (f g : Fn) (Mf Mg : ℝ),
    0 < α → α ≤ 1 → 0 ≤ Mf → 0 ≤ Mg → T2SF α f → T2SG α g →
    (∀ (b a : ℕ), a + b ≤ 2 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < π / 2 →
      |Work.Spaces.mixed b a f z θ| ≤ Mf) →
    (∀ (b a : ℕ), a + b ≤ 2 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < π / 2 →
      |Work.Spaces.mixed b a g z θ| ≤ Mg) →
    MeasureTheory.IntegrableOn
        (fun z => ∫ θ in Work.Spaces.Iθ, Work.FTS.H2.Heasy α f g z θ) Work.Spaces.Iz ∧
      (∫ z in Work.Spaces.Iz,
          |∫ θ in Work.Spaces.Iθ, Work.FTS.H2.Heasy α f g z θ|)
        ≤ C * (Mf * Work.Spaces.HkNorm α 4 g ^ 2
            + Mg * Work.Spaces.HkNorm α 4 f * Work.Spaces.HkNorm α 4 g)



/-! ## `T2SupG` is proved (from the proved `SecondDerivativesBounded` of `T2Qaux`) -/


/-! ## The assembly -/


end Work.FTS.TransportS
