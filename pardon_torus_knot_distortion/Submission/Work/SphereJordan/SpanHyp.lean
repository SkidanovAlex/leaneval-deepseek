import Mathlib
import Submission.Work.SphereJordan.SpanSetup
import Submission.Work.Smooth.SphereJordan.annulus_of_planeHypothesis

/-!
# The bundled hypotheses of `annulusTargetSpansCore`

The hypotheses of the target statement `Work.SphereJordan.annulusTargetSpansCore` are numerous; this
module bundles them into a single structure `SpanHyp`, so that the auxiliary lemmas about the two
target curves and the slit annulus can be stated with a single hypothesis.

The fields are exactly the hypotheses of the target statement (the data `t₁ s₁ t₂ s₂ θ₁ θ₂` together
with the configuration facts `ht₁`, `ht₁s₁`, `ht₂`, `ht₂s₂`, `ha₁`, `hseg₁`, `hout₁`, `ha₂`,
`hseg₂`, `hout₂`, `hθ₁`, `hθ₂`, `hθ`, `hθ'`, `hmax₁`, `hmax₂`).
-/

open Set

namespace Work.SphereJordan

noncomputable section

variable {γ : Work.Smooth.Jordan.PlaneCurve}

/-- The bundled configuration hypotheses of the target statement. -/
structure SpanHyp (h : Work.Smooth.SphereJordan.PlaneHypothesis) (hs : γ.IsSimple)
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
  ha₁ : (Work.Smooth.SphereJordan.base S : ℂ) + (t₁ : ℂ) *
    Work.Smooth.SphereJordan.cutDir S ∈ γ.trace
  hseg₁ : ∀ σ : ℝ, t₁ < σ → σ < s₁ →
    (Work.Smooth.SphereJordan.base S : ℂ) + (σ : ℂ) * Work.Smooth.SphereJordan.cutDir S ∈
      Metric.ball (0 : ℂ) 1 \ S.V
  hout₁ : (Work.Smooth.SphereJordan.base S : ℂ) + (s₁ : ℂ) *
    Work.Smooth.SphereJordan.cutDir S = Work.Smooth.SphereJordan.cutDir S
  ha₂ : (Work.Smooth.SphereJordan.base S : ℂ) - (t₂ : ℂ) *
    Work.Smooth.SphereJordan.cutDir S ∈ γ.trace
  hseg₂ : ∀ σ : ℝ, t₂ < σ → σ < s₂ →
    (Work.Smooth.SphereJordan.base S : ℂ) - (σ : ℂ) * Work.Smooth.SphereJordan.cutDir S ∈
      Metric.ball (0 : ℂ) 1 \ S.V
  hout₂ : (Work.Smooth.SphereJordan.base S : ℂ) - (s₂ : ℂ) *
    Work.Smooth.SphereJordan.cutDir S = -Work.Smooth.SphereJordan.cutDir S
  hθ₁ : γ.γ θ₁ = (Work.Smooth.SphereJordan.base S : ℂ) +
    (t₁ : ℂ) * Work.Smooth.SphereJordan.cutDir S
  hθ₂ : γ.γ θ₂ = (Work.Smooth.SphereJordan.base S : ℂ) -
    (t₂ : ℂ) * Work.Smooth.SphereJordan.cutDir S
  hθ : θ₂ < θ₁
  hθ' : θ₁ < θ₂ + 2 * Real.pi
  hmax₁ : ∀ σ : ℝ, t₁ < σ →
    (Work.Smooth.SphereJordan.base S : ℂ) + (σ : ℂ) * Work.Smooth.SphereJordan.cutDir S ∉
      closure S.V
  hmax₂ : ∀ σ : ℝ, t₂ < σ →
    (Work.Smooth.SphereJordan.base S : ℂ) - (σ : ℂ) * Work.Smooth.SphereJordan.cutDir S ∉
      closure S.V

namespace SpanHyp

variable {h : Work.Smooth.SphereJordan.PlaneHypothesis} {hs : γ.IsSimple}
  {hball : ∀ θ : ℝ, ‖γ.γ θ‖ < 1} {S : Work.Smooth.Jordan.PlaneSchoenflies γ}

/-- The upper target curve, as a plane curve. -/
def upPC (H : SpanHyp h hs hball S) (b : Bool) : Work.Smooth.Jordan.PlaneCurve :=
  tgtUpPC S H.t₁ H.s₁ H.t₂ H.s₂ b H.θ₁ H.θ₂ H.hout₁ H.hout₂ H.hθ₁ H.hθ₂

/-- The lower target curve, as a plane curve. -/
def dnPC (H : SpanHyp h hs hball S) (b : Bool) : Work.Smooth.Jordan.PlaneCurve :=
  tgtDnPC S H.t₁ H.s₁ H.t₂ H.s₂ b H.θ₁ H.θ₂ H.hout₁ H.hout₂ H.hθ₁ H.hθ₂

@[simp] theorem upPC_apply (H : SpanHyp h hs hball S) (b : Bool) (τ : ℝ) :
    (H.upPC b).γ τ = Work.Smooth.SphereJordan.tgtUpB S H.t₁ H.s₁ H.t₂ H.s₂ b H.θ₁ H.θ₂ τ := rfl

@[simp] theorem dnPC_apply (H : SpanHyp h hs hball S) (b : Bool) (τ : ℝ) :
    (H.dnPC b).γ τ = Work.Smooth.SphereJordan.tgtDnB S H.t₁ H.s₁ H.t₂ H.s₂ b H.θ₁ H.θ₂ τ := rfl

/-- The union of the two cuts. -/
def cuts' (H : SpanHyp h hs hball S) : Set ℂ := cuts S H.t₁ H.s₁ H.t₂ H.s₂

/-- The slit annulus. -/
def slit' (H : SpanHyp h hs hball S) : Set ℂ := slitAnnulus S H.t₁ H.s₁ H.t₂ H.s₂

theorem base_eq (H : SpanHyp h hs hball S) :
    (Work.Smooth.SphereJordan.base S : ℂ) =
      ((‖(Work.Smooth.SphereJordan.base S : ℂ)‖ : ℂ)) * Work.Smooth.SphereJordan.cutDir S :=
  Work.Smooth.SphereJordan.base_eq_smul_cutDir S

theorem norm_base_lt_one (H : SpanHyp h hs hball S) :
    ‖(Work.Smooth.SphereJordan.base S : ℂ)‖ < 1 :=
  Work.Smooth.SphereJordan.norm_base_lt_one S hball

/-- The complex number `w := base + σ • u` lies on the line of the cuts. -/
theorem base_add_eq (H : SpanHyp h hs hball S) (σ : ℝ) :
    (Work.Smooth.SphereJordan.base S : ℂ) + (σ : ℂ) * Work.Smooth.SphereJordan.cutDir S =
      (((‖(Work.Smooth.SphereJordan.base S : ℂ)‖ + σ : ℝ)) : ℂ) *
        Work.Smooth.SphereJordan.cutDir S := by
  rw [Complex.ofReal_add, add_mul]
  congr 1
  exact H.base_eq

theorem base_sub_eq (H : SpanHyp h hs hball S) (σ : ℝ) :
    (Work.Smooth.SphereJordan.base S : ℂ) - (σ : ℂ) * Work.Smooth.SphereJordan.cutDir S =
      (((‖(Work.Smooth.SphereJordan.base S : ℂ)‖ - σ : ℝ)) : ℂ) *
        Work.Smooth.SphereJordan.cutDir S := by
  rw [Complex.ofReal_sub, sub_mul]
  congr 1
  exact H.base_eq

/-- The outer parameter `s₁` is `1 - ‖base‖`. -/
theorem s₁_eq (H : SpanHyp h hs hball S) :
    H.s₁ = 1 - ‖(Work.Smooth.SphereJordan.base S : ℂ)‖ := by
  have hu : Work.Smooth.SphereJordan.cutDir S ≠ 0 :=
    Work.Smooth.SphereJordan.cutDir_ne_zero S
  have h := H.hout₁
  rw [H.base_add_eq H.s₁] at h
  have h' : ((‖(Work.Smooth.SphereJordan.base S : ℂ)‖ + H.s₁ : ℝ) : ℂ) *
      Work.Smooth.SphereJordan.cutDir S = (1 : ℂ) * Work.Smooth.SphereJordan.cutDir S := by
    rw [h]; ring
  have h2 := mul_right_cancel₀ hu h'
  have h3 : ‖(Work.Smooth.SphereJordan.base S : ℂ)‖ + H.s₁ = 1 := by
    simpa using congrArg Complex.re h2
  linarith

/-- The outer parameter `s₂` is `1 + ‖base‖`. -/
theorem s₂_eq (H : SpanHyp h hs hball S) :
    H.s₂ = 1 + ‖(Work.Smooth.SphereJordan.base S : ℂ)‖ := by
  have hu : Work.Smooth.SphereJordan.cutDir S ≠ 0 :=
    Work.Smooth.SphereJordan.cutDir_ne_zero S
  have h := H.hout₂
  rw [H.base_sub_eq H.s₂] at h
  have h' : ((‖(Work.Smooth.SphereJordan.base S : ℂ)‖ - H.s₂ : ℝ) : ℂ) *
      Work.Smooth.SphereJordan.cutDir S = (-1 : ℂ) * Work.Smooth.SphereJordan.cutDir S := by
    rw [h]; ring
  have h2 := mul_right_cancel₀ hu h'
  have h3 : ‖(Work.Smooth.SphereJordan.base S : ℂ)‖ - H.s₂ = -1 := by
    simpa using congrArg Complex.re h2
  linarith

end SpanHyp

end

end Work.SphereJordan
