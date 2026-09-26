import Mathlib
import Submission.Work.Smooth.SphereJordan.Pasting
import Submission.Work.Smooth.SphereJordan.Defs
import Submission.Work.Smooth.Jordan.All
import Submission.Work.Smooth.SphereJordan.annulus_of_planeHypothesis
import Submission.Work.Smooth.SphereJordan.injOn_circlePoint

/-!
# The configuration of the two-cuts proof of the planar annulus theorem

The planar annulus theorem (`Work.Smooth.SphereJordan.PlainAnnulusSchoenflies`) is proved from the
planar Jordan--Schoenflies theorem by the classical "two cuts" construction: the annulus
`A = 𝔻 ∖ int K` between the Schoenflies disc `K` of a Jordan curve `γ ⊆ int 𝔻` and the boundary
circle is cut along two straight crosscuts joining `γ` to `∂𝔻`, and each of the two pieces is
identified with a standard half-annulus by the Schoenflies theorem (applied to its four-arc
boundary curve).

This module fixes the configuration: the unit direction `cutDir S` of the *diameter* through the
base point `p = S.e 0` (so that the two outer endpoints of the crosscuts are the two points
`± cutDir` where the diameter meets the circle), the four endpoints `a₁, b₁, a₂, b₂` of the
crosscuts (`exists_cuts`), the crosscuts as point sets (`cut₁`, `cut₂`), the annulus `A`
(`annulus`) and the two pieces (`pieceUp`, `pieceDown`) cut out by the crosscuts.
-/

open Set
open LeanEval.KnotTheory.PardonDistortion

namespace Work.Smooth.SphereJordan

noncomputable section

/-! ## Elementary facts about the boundary circle of the model disc -/

/-- The standard parametrisation `θ ↦ e^{iθ}` of the boundary circle is continuous. -/
theorem continuous_circlePoint_disc : Continuous (circlePoint : ℝ → Disc) :=
  Continuous.subtype_mk (by fun_prop : Continuous fun θ : ℝ => Complex.exp (θ * Complex.I))
    (fun θ => by rw [Metric.mem_closedBall, dist_zero_right,
      Complex.norm_exp_ofReal_mul_I])

/-- The standard parametrisation of the boundary circle is `2π`-periodic. -/
theorem circlePoint_add_two_pi_local (θ : ℝ) : circlePoint (θ + 2 * Real.pi) = circlePoint θ := by
  apply Subtype.ext
  rw [Work.Smooth.Jordan.circlePoint_coe, Work.Smooth.Jordan.circlePoint_coe]
  rw [show (((θ + 2 * Real.pi : ℝ)) : ℂ) * Complex.I =
      (θ : ℂ) * Complex.I + (2 * (Real.pi : ℂ) * Complex.I) by push_cast; ring]
  rw [Complex.exp_add, Complex.exp_two_pi_mul_I, mul_one]

/-- The norm of a point of the model disc is at most one. -/
theorem norm_coe_disc_le_one (z : Disc) : ‖((z : Disc) : ℂ)‖ ≤ 1 := by
  have h := z.2
  rwa [Metric.mem_closedBall, dist_eq_norm, sub_zero] at h

variable {γ : Work.Smooth.Jordan.PlaneCurve}

/-! ## The diameter through the base point -/

/-- The unit direction of the diameter through the base point `S.e 0`. -/
def cutDir (S : Work.Smooth.Jordan.PlaneSchoenflies γ) : ℂ :=
  if (Work.Smooth.SphereJordan.base S : ℂ) = 0 then 1
  else ((‖(Work.Smooth.SphereJordan.base S : ℂ)‖ : ℂ))⁻¹ * (Work.Smooth.SphereJordan.base S : ℂ)

theorem cutDir_ne_zero (S : Work.Smooth.Jordan.PlaneSchoenflies γ) : cutDir S ≠ 0 := by
  rw [cutDir]
  split_ifs with h
  · exact one_ne_zero
  · exact mul_ne_zero (inv_ne_zero (by exact_mod_cast (norm_ne_zero_iff.mpr h))) h

theorem norm_cutDir (S : Work.Smooth.Jordan.PlaneSchoenflies γ) : ‖cutDir S‖ = 1 := by
  rw [cutDir]
  split_ifs with h
  · norm_num
  · rw [norm_mul, norm_inv, Complex.norm_def, Complex.normSq_ofReal, Real.sqrt_mul_self]
    · rw [inv_mul_cancel₀]
      exact norm_ne_zero_iff.mpr h
    · positivity

/-- The base point is a positive multiple of the cut direction. -/
theorem base_eq_smul_cutDir (S : Work.Smooth.Jordan.PlaneSchoenflies γ) :
    (Work.Smooth.SphereJordan.base S : ℂ) =
      ((‖(Work.Smooth.SphereJordan.base S : ℂ)‖ : ℂ)) * cutDir S := by
  rw [cutDir]
  by_cases h : (Work.Smooth.SphereJordan.base S : ℂ) = 0
  · rw [if_pos h, h]; simp
  · rw [if_neg h]
    have hne : ((‖(Work.Smooth.SphereJordan.base S : ℂ)‖ : ℝ) : ℂ) ≠ 0 := by
      exact_mod_cast (norm_ne_zero_iff.mpr h)
    field_simp

theorem norm_base_lt_one (S : Work.Smooth.Jordan.PlaneSchoenflies γ)
    (hball : ∀ θ : ℝ, ‖γ.γ θ‖ < 1) : ‖(Work.Smooth.SphereJordan.base S : ℂ)‖ < 1 :=
  Work.Smooth.SphereJordan.closure_V_subset_openBall S hball
    (Work.Smooth.SphereJordan.base_mem_K S)

/-! ## The two crosscuts -/

/-- **The two crosscuts.**  There are parameters `0 < t₁ < s₁` and `0 < t₂ < s₂` such that the
points `aᵢ = p ± tᵢ•u` lie on `γ`, the points `bᵢ = p ± sᵢ•u` lie on `∂𝔻`, and the open segments
between them lie in the annulus `A = 𝔻 ∖ int K`. -/
theorem exists_cuts (S : Work.Smooth.Jordan.PlaneSchoenflies γ)
    (hball : ∀ θ : ℝ, ‖γ.γ θ‖ < 1) :
    ∃ t₁ s₁ t₂ s₂ : ℝ, 0 < t₁ ∧ t₁ < s₁ ∧ 0 < t₂ ∧ t₂ < s₂ ∧
      (Work.Smooth.SphereJordan.base S : ℂ) + (t₁ : ℂ) * cutDir S ∈ γ.trace ∧
      (Work.Smooth.SphereJordan.base S : ℂ) + (s₁ : ℂ) * cutDir S ∈ Metric.sphere (0 : ℂ) 1 ∧
      (Work.Smooth.SphereJordan.base S : ℂ) - (t₂ : ℂ) * cutDir S ∈ γ.trace ∧
      (Work.Smooth.SphereJordan.base S : ℂ) - (s₂ : ℂ) * cutDir S ∈ Metric.sphere (0 : ℂ) 1 ∧
      (∀ σ : ℝ, t₁ < σ → σ < s₁ →
        (Work.Smooth.SphereJordan.base S : ℂ) + (σ : ℂ) * cutDir S ∈
          Metric.ball (0 : ℂ) 1 \ S.V) ∧
      (∀ σ : ℝ, t₂ < σ → σ < s₂ →
        (Work.Smooth.SphereJordan.base S : ℂ) - (σ : ℂ) * cutDir S ∈
          Metric.ball (0 : ℂ) 1 \ S.V) := by
  have hu : cutDir S ≠ 0 := cutDir_ne_zero S
  have hgen : ∀ σ : ℝ, (Work.Smooth.SphereJordan.base S : ℂ) + σ • cutDir S =
      (Work.Smooth.SphereJordan.base S : ℂ) + (σ : ℂ) * cutDir S := by
    intro σ; rw [Complex.real_smul]
  have hgen' : ∀ σ : ℝ, (Work.Smooth.SphereJordan.base S : ℂ) + σ • (-cutDir S) =
      (Work.Smooth.SphereJordan.base S : ℂ) - (σ : ℂ) * cutDir S := by
    intro σ; rw [smul_neg, Complex.real_smul]; ring
  obtain ⟨t₁, s₁, ht₁, hts₁, ha₁, hb₁, hseg₁, -⟩ :=
    Work.Smooth.SphereJordan.crosscut_mem_annulus S hball (cutDir S) hu
  obtain ⟨t₂, s₂, ht₂, hts₂, ha₂, hb₂, hseg₂, -⟩ :=
    Work.Smooth.SphereJordan.crosscut_mem_annulus S hball (-cutDir S) (neg_ne_zero.mpr hu)
  refine ⟨t₁, s₁, t₂, s₂, ht₁, hts₁, ht₂, hts₂, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← hgen t₁]; exact ha₁
  · rw [← hgen s₁]; exact hb₁
  · rw [← hgen' t₂]; exact ha₂
  · rw [← hgen' s₂]; exact hb₂
  · intro σ h1 h2; rw [← hgen σ]; exact hseg₁ σ h1 h2
  · intro σ h1 h2; rw [← hgen' σ]; exact hseg₂ σ h1 h2

/-! ## The cuts, the annulus and its two pieces -/

/-- The first crosscut, as a point set: the segment from `a₁` to `b₁`. -/
def cut₁ (S : Work.Smooth.Jordan.PlaneSchoenflies γ) (t₁ s₁ : ℝ) : Set ℂ :=
  {z : ℂ | ∃ σ : ℝ, σ ∈ Set.Icc t₁ s₁ ∧ z = (Work.Smooth.SphereJordan.base S : ℂ) + (σ : ℂ) * cutDir S}

/-- The second crosscut, as a point set: the segment from `a₂` to `b₂`. -/
def cut₂ (S : Work.Smooth.Jordan.PlaneSchoenflies γ) (t₂ s₂ : ℝ) : Set ℂ :=
  {z : ℂ | ∃ σ : ℝ, σ ∈ Set.Icc t₂ s₂ ∧ z = (Work.Smooth.SphereJordan.base S : ℂ) - (σ : ℂ) * cutDir S}

/-- The closed annulus between the Schoenflies disc `K = closure S.V` and the boundary circle. -/
def annulus (S : Work.Smooth.Jordan.PlaneSchoenflies γ) : Set ℂ :=
  Metric.closedBall (0 : ℂ) 1 \ S.V

/-- The annulus with the two crosscuts removed. -/
def annulusCut (S : Work.Smooth.Jordan.PlaneSchoenflies γ) (t₁ s₁ t₂ s₂ : ℝ) : Set ℂ :=
  annulus S \ (cut₁ S t₁ s₁ ∪ cut₂ S t₂ s₂)

/-- The **upper piece**: the connected component of the cut annulus containing the point `i·u`. -/
def pieceUp (S : Work.Smooth.Jordan.PlaneSchoenflies γ) (t₁ s₁ t₂ s₂ : ℝ) : Set ℂ :=
  connectedComponentIn (annulusCut S t₁ s₁ t₂ s₂) (Complex.I * cutDir S)

/-- The **lower piece**: the connected component of the cut annulus containing the point `-i·u`. -/
def pieceDown (S : Work.Smooth.Jordan.PlaneSchoenflies γ) (t₁ s₁ t₂ s₂ : ℝ) : Set ℂ :=
  connectedComponentIn (annulusCut S t₁ s₁ t₂ s₂) (-Complex.I * cutDir S)

/-- The "up" semicircle of the boundary circle: the outer boundary arc of the upper piece.  It is
the set of points of the circle on the left of the diameter through the base point. -/
def upArc (S : Work.Smooth.Jordan.PlaneSchoenflies γ) : Set ℂ :=
  {z : ℂ | ‖z‖ = 1 ∧ 0 ≤ (z / cutDir S).im}

/-- The "down" semicircle: the outer boundary arc of the lower piece. -/
def downArc (S : Work.Smooth.Jordan.PlaneSchoenflies γ) : Set ℂ :=
  {z : ℂ | ‖z‖ = 1 ∧ (z / cutDir S).im ≤ 0}

/-- The "up" semicircle of the boundary circle, in the cut coordinates, parametrised by `θ ∈ [0,π]`
as `u·e^{iθ}`. -/
def upArcPoint (S : Work.Smooth.Jordan.PlaneSchoenflies γ) (θ : ℝ) : ℂ :=
  cutDir S * Complex.exp (θ * Complex.I)

/-- The "down" semicircle, parametrised by `θ ∈ [0,π]` as `-u·e^{iθ}` (so that it runs from `-u`
to `u` through `-i·u`). -/
def downArcPoint (S : Work.Smooth.Jordan.PlaneSchoenflies γ) (θ : ℝ) : ℂ :=
  -(cutDir S * Complex.exp (θ * Complex.I))

end

end Work.Smooth.SphereJordan
