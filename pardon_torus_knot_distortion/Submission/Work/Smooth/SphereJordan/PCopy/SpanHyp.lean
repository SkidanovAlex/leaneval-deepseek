import Mathlib
import Submission.Work.Smooth.SphereJordan.PCopy.SpanSetup
import Submission.Work.Smooth.SphereJordan.PCopy.Setup

/-!
# The bundled hypotheses of `annulusTargetSpansCore`

The hypotheses of the target statement `Work.SphereJordan.annulusTargetSpansCore` are numerous; this
module bundles them into a single structure `pcSpanHyp`, so that the auxiliary lemmas about the two
target curves and the slit pcannulus can be stated with a single hypothesis.

The fields are exactly the hypotheses of the target statement (the data `t₁ s₁ t₂ s₂ θ₁ θ₂` together
with the configuration facts `ht₁`, `ht₁s₁`, `ht₂`, `ht₂s₂`, `ha₁`, `hseg₁`, `hout₁`, `ha₂`,
`hseg₂`, `hout₂`, `hθ₁`, `hθ₂`, `hθ`, `hθ'`, `hmax₁`, `hmax₂`).
-/

open Set

namespace Work.SphereJordan

noncomputable section

variable {γ : Work.Smooth.Jordan.PlaneCurve}

/-- The bundled configuration hypotheses of the target statement. -/
structure pcSpanHyp (h : Work.Smooth.SphereJordan.PlaneHypothesis) (hs : γ.IsSimple)
    (hball : ∀ θ : ℝ, ‖γ.γ θ‖ < 1) (S : Work.Smooth.Jordan.PlaneSchoenflies γ) where
  t₁ : ℝ
  s₁ : ℝ
  t₂ : ℝ
  s₂ : ℝ
  θ₁ : ℝ
  θ₂ : ℝ
  ht₁ : 0 < t₁
  ht₁s₁ : t₁ < s₁
  ht₂ : 0 < t₂
  ht₂s₂ : t₂ < s₂
  ha₁ : (Work.Smooth.SphereJordan.pcbase S : ℂ) + (t₁ : ℂ) *
    Work.Smooth.SphereJordan.pccutDir S ∈ γ.trace
  hseg₁ : ∀ σ : ℝ, t₁ < σ → σ < s₁ →
    (Work.Smooth.SphereJordan.pcbase S : ℂ) + (σ : ℂ) * Work.Smooth.SphereJordan.pccutDir S ∈
      Metric.ball (0 : ℂ) 1 \ S.V
  hout₁ : (Work.Smooth.SphereJordan.pcbase S : ℂ) + (s₁ : ℂ) *
    Work.Smooth.SphereJordan.pccutDir S = Work.Smooth.SphereJordan.pccutDir S
  ha₂ : (Work.Smooth.SphereJordan.pcbase S : ℂ) - (t₂ : ℂ) *
    Work.Smooth.SphereJordan.pccutDir S ∈ γ.trace
  hseg₂ : ∀ σ : ℝ, t₂ < σ → σ < s₂ →
    (Work.Smooth.SphereJordan.pcbase S : ℂ) - (σ : ℂ) * Work.Smooth.SphereJordan.pccutDir S ∈
      Metric.ball (0 : ℂ) 1 \ S.V
  hout₂ : (Work.Smooth.SphereJordan.pcbase S : ℂ) - (s₂ : ℂ) *
    Work.Smooth.SphereJordan.pccutDir S = -Work.Smooth.SphereJordan.pccutDir S
  hθ₁ : γ.γ θ₁ = (Work.Smooth.SphereJordan.pcbase S : ℂ) +
    (t₁ : ℂ) * Work.Smooth.SphereJordan.pccutDir S
  hθ₂ : γ.γ θ₂ = (Work.Smooth.SphereJordan.pcbase S : ℂ) -
    (t₂ : ℂ) * Work.Smooth.SphereJordan.pccutDir S
  hθ : θ₂ < θ₁
  hθ' : θ₁ < θ₂ + 2 * Real.pi
  hmax₁ : ∀ σ : ℝ, t₁ < σ →
    (Work.Smooth.SphereJordan.pcbase S : ℂ) + (σ : ℂ) * Work.Smooth.SphereJordan.pccutDir S ∉
      closure S.V
  hmax₂ : ∀ σ : ℝ, t₂ < σ →
    (Work.Smooth.SphereJordan.pcbase S : ℂ) - (σ : ℂ) * Work.Smooth.SphereJordan.pccutDir S ∉
      closure S.V

namespace pcSpanHyp

variable {h : Work.Smooth.SphereJordan.PlaneHypothesis} {hs : γ.IsSimple}
  {hball : ∀ θ : ℝ, ‖γ.γ θ‖ < 1} {S : Work.Smooth.Jordan.PlaneSchoenflies γ}

/-- The upper target curve, as a plane curve. -/
def pcupPC (H : pcSpanHyp h hs hball S) (b : Bool) : Work.Smooth.Jordan.PlaneCurve :=
  pctgtUpPC S H.t₁ H.s₁ H.t₂ H.s₂ b H.θ₁ H.θ₂ H.hout₁ H.hout₂ H.hθ₁ H.hθ₂

/-- The lower target curve, as a plane curve. -/
def pcdnPC (H : pcSpanHyp h hs hball S) (b : Bool) : Work.Smooth.Jordan.PlaneCurve :=
  pctgtDnPC S H.t₁ H.s₁ H.t₂ H.s₂ b H.θ₁ H.θ₂ H.hout₁ H.hout₂ H.hθ₁ H.hθ₂

@[simp] theorem pcupPC_apply (H : pcSpanHyp h hs hball S) (b : Bool) (τ : ℝ) :
    (H.pcupPC b).γ τ = Work.Smooth.SphereJordan.pctgtUpB S H.t₁ H.s₁ H.t₂ H.s₂ b H.θ₁ H.θ₂ τ := rfl

@[simp] theorem pcdnPC_apply (H : pcSpanHyp h hs hball S) (b : Bool) (τ : ℝ) :
    (H.pcdnPC b).γ τ = Work.Smooth.SphereJordan.pctgtDnB S H.t₁ H.s₁ H.t₂ H.s₂ b H.θ₁ H.θ₂ τ := rfl

/-- The union of the two pccuts. -/
def pccuts' (H : pcSpanHyp h hs hball S) : Set ℂ := pccuts S H.t₁ H.s₁ H.t₂ H.s₂

/-- The slit pcannulus. -/
def pcslit' (H : pcSpanHyp h hs hball S) : Set ℂ := pcslitAnnulus S H.t₁ H.s₁ H.t₂ H.s₂

theorem pcbase_eq (H : pcSpanHyp h hs hball S) :
    (Work.Smooth.SphereJordan.pcbase S : ℂ) =
      ((‖(Work.Smooth.SphereJordan.pcbase S : ℂ)‖ : ℂ)) * Work.Smooth.SphereJordan.pccutDir S :=
  Work.Smooth.SphereJordan.pcbase_eq_smul_cutDir S

theorem pcnorm_base_lt_one (H : pcSpanHyp h hs hball S) :
    ‖(Work.Smooth.SphereJordan.pcbase S : ℂ)‖ < 1 :=
  Work.Smooth.SphereJordan.pcnorm_base_lt_one S hball

/-- The complex number `w := pcbase + σ • u` lies on the line of the pccuts. -/
theorem pcbase_add_eq (H : pcSpanHyp h hs hball S) (σ : ℝ) :
    (Work.Smooth.SphereJordan.pcbase S : ℂ) + (σ : ℂ) * Work.Smooth.SphereJordan.pccutDir S =
      (((‖(Work.Smooth.SphereJordan.pcbase S : ℂ)‖ + σ : ℝ)) : ℂ) *
        Work.Smooth.SphereJordan.pccutDir S := by
  rw [Complex.ofReal_add, add_mul]
  congr 1
  exact H.pcbase_eq

theorem pcbase_sub_eq (H : pcSpanHyp h hs hball S) (σ : ℝ) :
    (Work.Smooth.SphereJordan.pcbase S : ℂ) - (σ : ℂ) * Work.Smooth.SphereJordan.pccutDir S =
      (((‖(Work.Smooth.SphereJordan.pcbase S : ℂ)‖ - σ : ℝ)) : ℂ) *
        Work.Smooth.SphereJordan.pccutDir S := by
  rw [Complex.ofReal_sub, sub_mul]
  congr 1
  exact H.pcbase_eq

/-- The outer parameter `s₁` is `1 - ‖pcbase‖`. -/
theorem pcs₁_eq (H : pcSpanHyp h hs hball S) :
    H.s₁ = 1 - ‖(Work.Smooth.SphereJordan.pcbase S : ℂ)‖ := by
  have hu : Work.Smooth.SphereJordan.pccutDir S ≠ 0 :=
    Work.Smooth.SphereJordan.pccutDir_ne_zero S
  have h := H.hout₁
  rw [H.pcbase_add_eq H.s₁] at h
  have h' : ((‖(Work.Smooth.SphereJordan.pcbase S : ℂ)‖ + H.s₁ : ℝ) : ℂ) *
      Work.Smooth.SphereJordan.pccutDir S = (1 : ℂ) * Work.Smooth.SphereJordan.pccutDir S := by
    rw [h]; ring
  have h2 := mul_right_cancel₀ hu h'
  have h3 : ‖(Work.Smooth.SphereJordan.pcbase S : ℂ)‖ + H.s₁ = 1 := by
    simpa using congrArg Complex.re h2
  linarith

/-- The outer parameter `s₂` is `1 + ‖pcbase‖`. -/
theorem pcs₂_eq (H : pcSpanHyp h hs hball S) :
    H.s₂ = 1 + ‖(Work.Smooth.SphereJordan.pcbase S : ℂ)‖ := by
  have hu : Work.Smooth.SphereJordan.pccutDir S ≠ 0 :=
    Work.Smooth.SphereJordan.pccutDir_ne_zero S
  have h := H.hout₂
  rw [H.pcbase_sub_eq H.s₂] at h
  have h' : ((‖(Work.Smooth.SphereJordan.pcbase S : ℂ)‖ - H.s₂ : ℝ) : ℂ) *
      Work.Smooth.SphereJordan.pccutDir S = (-1 : ℂ) * Work.Smooth.SphereJordan.pccutDir S := by
    rw [h]; ring
  have h2 := mul_right_cancel₀ hu h'
  have h3 : ‖(Work.Smooth.SphereJordan.pcbase S : ℂ)‖ - H.s₂ = -1 := by
    simpa using congrArg Complex.re h2
  linarith

end pcSpanHyp

end

end Work.SphereJordan
