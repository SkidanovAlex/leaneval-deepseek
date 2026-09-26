import Mathlib
import Submission.Work.SphereJordan.annulusTargetCurves

/-!
# The configuration of `annulusTargetSpansCore`: the two target curves and the slit annulus

This module fixes the objects of the target statement `Work.SphereJordan.annulusTargetSpansCore`:

* the two `4`-arc curves `tgtUpB`, `tgtDnB` of the cut-and-paste, regarded as `PlaneCurve`s
  (`tgtUpPC`, `tgtDnPC`);
* the two cuts `cut₁`, `cut₂` and the annulus `annulus S` (already defined in `plainAnnulusSetup`);
* the slit annulus `annulusCut` and the two "pieces" as connected components;
* the test points `upPt`, `dnPt` of the annulus lying on the two sides of the outer circle.

The mathematical content of `annulusTargetSpansCore` is that the two pieces are the images of the
two spanning discs of `tgtUpPC b` and `tgtDnPC b`, for the correct choice of the sign `b`.
-/

open Set

namespace Work.SphereJordan

noncomputable section

variable {γ : Work.Smooth.Jordan.PlaneCurve}

/-- The upper target curve `tgtUpB`, as a plane curve.  The continuity and periodicity are the
content of `Work.SphereJordan.continuous_periodic_tgtUpB`. -/
def tgtUpPC (S : Work.Smooth.Jordan.PlaneSchoenflies γ) (t₁ s₁ t₂ s₂ : ℝ) (b : Bool)
    (θ₁ θ₂ : ℝ)
    (hout₁ : (Work.Smooth.SphereJordan.base S : ℂ) + (s₁ : ℂ) *
      Work.Smooth.SphereJordan.cutDir S = Work.Smooth.SphereJordan.cutDir S)
    (hout₂ : (Work.Smooth.SphereJordan.base S : ℂ) - (s₂ : ℂ) *
      Work.Smooth.SphereJordan.cutDir S = -Work.Smooth.SphereJordan.cutDir S)
    (hθ₁ : γ.γ θ₁ = (Work.Smooth.SphereJordan.base S : ℂ) +
      (t₁ : ℂ) * Work.Smooth.SphereJordan.cutDir S)
    (hθ₂ : γ.γ θ₂ = (Work.Smooth.SphereJordan.base S : ℂ) -
      (t₂ : ℂ) * Work.Smooth.SphereJordan.cutDir S) :
    Work.Smooth.Jordan.PlaneCurve where
  γ := Work.Smooth.SphereJordan.tgtUpB S t₁ s₁ t₂ s₂ b θ₁ θ₂
  cont := (Work.SphereJordan.continuous_periodic_tgtUpB (γ := γ) S t₁ s₁ t₂ s₂ b θ₁ θ₂
    hout₁ hout₂ hθ₁ hθ₂).1
  periodic := (Work.SphereJordan.continuous_periodic_tgtUpB (γ := γ) S t₁ s₁ t₂ s₂ b θ₁ θ₂
    hout₁ hout₂ hθ₁ hθ₂).2

/-- The lower target curve `tgtDnB`, as a plane curve. -/
def tgtDnPC (S : Work.Smooth.Jordan.PlaneSchoenflies γ) (t₁ s₁ t₂ s₂ : ℝ) (b : Bool)
    (θ₁ θ₂ : ℝ)
    (hout₁ : (Work.Smooth.SphereJordan.base S : ℂ) + (s₁ : ℂ) *
      Work.Smooth.SphereJordan.cutDir S = Work.Smooth.SphereJordan.cutDir S)
    (hout₂ : (Work.Smooth.SphereJordan.base S : ℂ) - (s₂ : ℂ) *
      Work.Smooth.SphereJordan.cutDir S = -Work.Smooth.SphereJordan.cutDir S)
    (hθ₁ : γ.γ θ₁ = (Work.Smooth.SphereJordan.base S : ℂ) +
      (t₁ : ℂ) * Work.Smooth.SphereJordan.cutDir S)
    (hθ₂ : γ.γ θ₂ = (Work.Smooth.SphereJordan.base S : ℂ) -
      (t₂ : ℂ) * Work.Smooth.SphereJordan.cutDir S) :
    Work.Smooth.Jordan.PlaneCurve where
  γ := Work.Smooth.SphereJordan.tgtDnB S t₁ s₁ t₂ s₂ b θ₁ θ₂
  cont := (Work.SphereJordan.continuous_periodic_tgtDnB (γ := γ) S t₁ s₁ t₂ s₂ b θ₁ θ₂
    hout₁ hout₂ hθ₁ hθ₂).1
  periodic := (Work.SphereJordan.continuous_periodic_tgtDnB (γ := γ) S t₁ s₁ t₂ s₂ b θ₁ θ₂
    hout₁ hout₂ hθ₁ hθ₂).2

@[simp] theorem tgtUpPC_apply (S : Work.Smooth.Jordan.PlaneSchoenflies γ) (t₁ s₁ t₂ s₂ : ℝ)
    (b : Bool) (θ₁ θ₂ : ℝ)
    (hout₁ : (Work.Smooth.SphereJordan.base S : ℂ) + (s₁ : ℂ) *
      Work.Smooth.SphereJordan.cutDir S = Work.Smooth.SphereJordan.cutDir S)
    (hout₂ : (Work.Smooth.SphereJordan.base S : ℂ) - (s₂ : ℂ) *
      Work.Smooth.SphereJordan.cutDir S = -Work.Smooth.SphereJordan.cutDir S)
    (hθ₁ : γ.γ θ₁ = (Work.Smooth.SphereJordan.base S : ℂ) +
      (t₁ : ℂ) * Work.Smooth.SphereJordan.cutDir S)
    (hθ₂ : γ.γ θ₂ = (Work.Smooth.SphereJordan.base S : ℂ) -
      (t₂ : ℂ) * Work.Smooth.SphereJordan.cutDir S) (τ : ℝ) :
    (tgtUpPC S t₁ s₁ t₂ s₂ b θ₁ θ₂ hout₁ hout₂ hθ₁ hθ₂).γ τ =
      Work.Smooth.SphereJordan.tgtUpB S t₁ s₁ t₂ s₂ b θ₁ θ₂ τ := rfl

@[simp] theorem tgtDnPC_apply (S : Work.Smooth.Jordan.PlaneSchoenflies γ) (t₁ s₁ t₂ s₂ : ℝ)
    (b : Bool) (θ₁ θ₂ : ℝ)
    (hout₁ : (Work.Smooth.SphereJordan.base S : ℂ) + (s₁ : ℂ) *
      Work.Smooth.SphereJordan.cutDir S = Work.Smooth.SphereJordan.cutDir S)
    (hout₂ : (Work.Smooth.SphereJordan.base S : ℂ) - (s₂ : ℂ) *
      Work.Smooth.SphereJordan.cutDir S = -Work.Smooth.SphereJordan.cutDir S)
    (hθ₁ : γ.γ θ₁ = (Work.Smooth.SphereJordan.base S : ℂ) +
      (t₁ : ℂ) * Work.Smooth.SphereJordan.cutDir S)
    (hθ₂ : γ.γ θ₂ = (Work.Smooth.SphereJordan.base S : ℂ) -
      (t₂ : ℂ) * Work.Smooth.SphereJordan.cutDir S) (τ : ℝ) :
    (tgtDnPC S t₁ s₁ t₂ s₂ b θ₁ θ₂ hout₁ hout₂ hθ₁ hθ₂).γ τ =
      Work.Smooth.SphereJordan.tgtDnB S t₁ s₁ t₂ s₂ b θ₁ θ₂ τ := rfl

/-- The union of the two cuts. -/
def cuts (S : Work.Smooth.Jordan.PlaneSchoenflies γ) (t₁ s₁ t₂ s₂ : ℝ) : Set ℂ :=
  Work.Smooth.SphereJordan.cut₁ S t₁ s₁ ∪ Work.Smooth.SphereJordan.cut₂ S t₂ s₂

/-- The slit annulus: the closed annulus `annulus S` with the two cuts removed. -/
def slitAnnulus (S : Work.Smooth.Jordan.PlaneSchoenflies γ) (t₁ s₁ t₂ s₂ : ℝ) : Set ℂ :=
  Work.Smooth.SphereJordan.annulus S \ cuts S t₁ s₁ t₂ s₂

end

end Work.SphereJordan
