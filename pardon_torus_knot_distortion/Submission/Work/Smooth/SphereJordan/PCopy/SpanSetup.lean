import Mathlib
import Submission.Work.Smooth.SphereJordan.PCopy.annulusTargetCurves

/-!
# The configuration of `annulusTargetSpansCore`: the two target curves and the slit pcannulus

This module fixes the objects of the target statement `Work.SphereJordan.annulusTargetSpansCore`:

* the two `4`-arc curves `pctgtUpB`, `pctgtDnB` of the cut-and-paste, regarded as `PlaneCurve`s
  (`pctgtUpPC`, `pctgtDnPC`);
* the two pccuts `pccut₁`, `pccut₂` and the pcannulus `pcannulus S` (already defined in `plainAnnulusSetup`);
* the slit pcannulus `pcannulusCut` and the two "pieces" as connected components;
* the test points `upPt`, `dnPt` of the pcannulus lying on the two sides of the outer circle.

The mathematical content of `annulusTargetSpansCore` is that the two pieces are the images of the
two spanning discs of `pctgtUpPC b` and `pctgtDnPC b`, for the correct choice of the sign `b`.
-/

open Set

namespace Work.SphereJordan

noncomputable section

variable {γ : Work.Smooth.Jordan.PlaneCurve}

/-- The upper target curve `pctgtUpB`, as a plane curve.  The continuity and periodicity are the
content of `Work.SphereJordan.pccontinuous_periodic_tgtUpB`. -/
def pctgtUpPC (S : Work.Smooth.Jordan.PlaneSchoenflies γ) (t₁ s₁ t₂ s₂ : ℝ) (b : Bool)
    (θ₁ θ₂ : ℝ)
    (hout₁ : (Work.Smooth.SphereJordan.pcbase S : ℂ) + (s₁ : ℂ) *
      Work.Smooth.SphereJordan.pccutDir S = Work.Smooth.SphereJordan.pccutDir S)
    (hout₂ : (Work.Smooth.SphereJordan.pcbase S : ℂ) - (s₂ : ℂ) *
      Work.Smooth.SphereJordan.pccutDir S = -Work.Smooth.SphereJordan.pccutDir S)
    (hθ₁ : γ.γ θ₁ = (Work.Smooth.SphereJordan.pcbase S : ℂ) +
      (t₁ : ℂ) * Work.Smooth.SphereJordan.pccutDir S)
    (hθ₂ : γ.γ θ₂ = (Work.Smooth.SphereJordan.pcbase S : ℂ) -
      (t₂ : ℂ) * Work.Smooth.SphereJordan.pccutDir S) :
    Work.Smooth.Jordan.PlaneCurve where
  γ := Work.Smooth.SphereJordan.pctgtUpB S t₁ s₁ t₂ s₂ b θ₁ θ₂
  cont := (Work.SphereJordan.pccontinuous_periodic_tgtUpB (γ := γ) S t₁ s₁ t₂ s₂ b θ₁ θ₂
    hout₁ hout₂ hθ₁ hθ₂).1
  periodic := (Work.SphereJordan.pccontinuous_periodic_tgtUpB (γ := γ) S t₁ s₁ t₂ s₂ b θ₁ θ₂
    hout₁ hout₂ hθ₁ hθ₂).2

/-- The lower target curve `pctgtDnB`, as a plane curve. -/
def pctgtDnPC (S : Work.Smooth.Jordan.PlaneSchoenflies γ) (t₁ s₁ t₂ s₂ : ℝ) (b : Bool)
    (θ₁ θ₂ : ℝ)
    (hout₁ : (Work.Smooth.SphereJordan.pcbase S : ℂ) + (s₁ : ℂ) *
      Work.Smooth.SphereJordan.pccutDir S = Work.Smooth.SphereJordan.pccutDir S)
    (hout₂ : (Work.Smooth.SphereJordan.pcbase S : ℂ) - (s₂ : ℂ) *
      Work.Smooth.SphereJordan.pccutDir S = -Work.Smooth.SphereJordan.pccutDir S)
    (hθ₁ : γ.γ θ₁ = (Work.Smooth.SphereJordan.pcbase S : ℂ) +
      (t₁ : ℂ) * Work.Smooth.SphereJordan.pccutDir S)
    (hθ₂ : γ.γ θ₂ = (Work.Smooth.SphereJordan.pcbase S : ℂ) -
      (t₂ : ℂ) * Work.Smooth.SphereJordan.pccutDir S) :
    Work.Smooth.Jordan.PlaneCurve where
  γ := Work.Smooth.SphereJordan.pctgtDnB S t₁ s₁ t₂ s₂ b θ₁ θ₂
  cont := (Work.SphereJordan.pccontinuous_periodic_tgtDnB (γ := γ) S t₁ s₁ t₂ s₂ b θ₁ θ₂
    hout₁ hout₂ hθ₁ hθ₂).1
  periodic := (Work.SphereJordan.pccontinuous_periodic_tgtDnB (γ := γ) S t₁ s₁ t₂ s₂ b θ₁ θ₂
    hout₁ hout₂ hθ₁ hθ₂).2

@[simp] theorem pctgtUpPC_apply (S : Work.Smooth.Jordan.PlaneSchoenflies γ) (t₁ s₁ t₂ s₂ : ℝ)
    (b : Bool) (θ₁ θ₂ : ℝ)
    (hout₁ : (Work.Smooth.SphereJordan.pcbase S : ℂ) + (s₁ : ℂ) *
      Work.Smooth.SphereJordan.pccutDir S = Work.Smooth.SphereJordan.pccutDir S)
    (hout₂ : (Work.Smooth.SphereJordan.pcbase S : ℂ) - (s₂ : ℂ) *
      Work.Smooth.SphereJordan.pccutDir S = -Work.Smooth.SphereJordan.pccutDir S)
    (hθ₁ : γ.γ θ₁ = (Work.Smooth.SphereJordan.pcbase S : ℂ) +
      (t₁ : ℂ) * Work.Smooth.SphereJordan.pccutDir S)
    (hθ₂ : γ.γ θ₂ = (Work.Smooth.SphereJordan.pcbase S : ℂ) -
      (t₂ : ℂ) * Work.Smooth.SphereJordan.pccutDir S) (τ : ℝ) :
    (pctgtUpPC S t₁ s₁ t₂ s₂ b θ₁ θ₂ hout₁ hout₂ hθ₁ hθ₂).γ τ =
      Work.Smooth.SphereJordan.pctgtUpB S t₁ s₁ t₂ s₂ b θ₁ θ₂ τ := rfl

@[simp] theorem pctgtDnPC_apply (S : Work.Smooth.Jordan.PlaneSchoenflies γ) (t₁ s₁ t₂ s₂ : ℝ)
    (b : Bool) (θ₁ θ₂ : ℝ)
    (hout₁ : (Work.Smooth.SphereJordan.pcbase S : ℂ) + (s₁ : ℂ) *
      Work.Smooth.SphereJordan.pccutDir S = Work.Smooth.SphereJordan.pccutDir S)
    (hout₂ : (Work.Smooth.SphereJordan.pcbase S : ℂ) - (s₂ : ℂ) *
      Work.Smooth.SphereJordan.pccutDir S = -Work.Smooth.SphereJordan.pccutDir S)
    (hθ₁ : γ.γ θ₁ = (Work.Smooth.SphereJordan.pcbase S : ℂ) +
      (t₁ : ℂ) * Work.Smooth.SphereJordan.pccutDir S)
    (hθ₂ : γ.γ θ₂ = (Work.Smooth.SphereJordan.pcbase S : ℂ) -
      (t₂ : ℂ) * Work.Smooth.SphereJordan.pccutDir S) (τ : ℝ) :
    (pctgtDnPC S t₁ s₁ t₂ s₂ b θ₁ θ₂ hout₁ hout₂ hθ₁ hθ₂).γ τ =
      Work.Smooth.SphereJordan.pctgtDnB S t₁ s₁ t₂ s₂ b θ₁ θ₂ τ := rfl

/-- The union of the two pccuts. -/
def pccuts (S : Work.Smooth.Jordan.PlaneSchoenflies γ) (t₁ s₁ t₂ s₂ : ℝ) : Set ℂ :=
  Work.Smooth.SphereJordan.pccut₁ S t₁ s₁ ∪ Work.Smooth.SphereJordan.pccut₂ S t₂ s₂

/-- The slit pcannulus: the closed pcannulus `pcannulus S` with the two pccuts removed. -/
def pcslitAnnulus (S : Work.Smooth.Jordan.PlaneSchoenflies γ) (t₁ s₁ t₂ s₂ : ℝ) : Set ℂ :=
  Work.Smooth.SphereJordan.pcannulus S \ pccuts S t₁ s₁ t₂ s₂

end

end Work.SphereJordan
