import Mathlib
import Submission.Work.Smooth.SphereJordan.Defs
import Submission.Work.Smooth.Jordan.All
import Submission.Work.Smooth.SphereJordan.annulus_of_planeHypothesis
import Submission.Work.Smooth.SphereJordan.thetaTwoHalvesSphereOfPlane
import Submission.Work.SphereJordan.odd_windNumber_of_mem_V

/-!
# The two crosscuts of the planar annulus theorem

This module fixes the configuration on which the planar annulus theorem is proved: the two
crosscuts of the open annulus between a simple closed curve `γ` inside the unit disc and the
boundary circle, along the horizontal line through the base point `base S`.

Nothing here is classical.  The three geometric inputs of the construction live in companion
modules and are stated in this module's vocabulary.
-/

open Set

namespace Work.Smooth.SphereJordan

noncomputable section

variable {γ : Work.Smooth.Jordan.PlaneCurve}

/-! ## The two crosscuts through the base point, and the upper half of the annulus -/

variable {γ : Work.Smooth.Jordan.PlaneCurve}

/-- The **open annulus** between `γ` and the boundary circle: the open unit disc with the closed
disc bounded by `γ` removed.  Its closure is `annulusRegion S`. -/
def annulusOpen (S : Work.Smooth.Jordan.PlaneSchoenflies γ) : Set ℂ :=
  Metric.ball (0 : ℂ) 1 \ closure S.V

theorem isOpen_annulusOpen (S : Work.Smooth.Jordan.PlaneSchoenflies γ) :
    IsOpen (annulusOpen S) :=
  Metric.isOpen_ball.sdiff isClosed_closure

/-- The **upper half-plane** of the horizontal line through the base point. -/
def upperHalfPlane (S : Work.Smooth.Jordan.PlaneSchoenflies γ) : Set ℂ :=
  {z : ℂ | 0 < (z - Work.Smooth.SphereJordan.base S).im}

/-- The **lower half-plane** of the horizontal line through the base point. -/
def lowerHalfPlane (S : Work.Smooth.Jordan.PlaneSchoenflies γ) : Set ℂ :=
  {z : ℂ | (z - Work.Smooth.SphereJordan.base S).im < 0}

/-- The **horizontal line** through the base point. -/
def baseLine (S : Work.Smooth.Jordan.PlaneSchoenflies γ) : Set ℂ :=
  {z : ℂ | (z - Work.Smooth.SphereJordan.base S).im = 0}

theorem isOpen_upperHalfPlane (S : Work.Smooth.Jordan.PlaneSchoenflies γ) :
    IsOpen (upperHalfPlane S) := by
  have h : Continuous fun z : ℂ => (z - Work.Smooth.SphereJordan.base S).im :=
    Complex.continuous_im.comp (continuous_id.sub continuous_const)
  exact isOpen_lt continuous_const h

theorem isOpen_lowerHalfPlane (S : Work.Smooth.Jordan.PlaneSchoenflies γ) :
    IsOpen (lowerHalfPlane S) := by
  have h : Continuous fun z : ℂ => (z - Work.Smooth.SphereJordan.base S).im :=
    Complex.continuous_im.comp (continuous_id.sub continuous_const)
  exact isOpen_lt h continuous_const

/-- **The configuration of the two crosscuts** of the open annulus through the base point, along the
horizontal line: the inner endpoints `x₁`, `x₂` on `γ`, the outer endpoints `y₁`, `y₂` on the
boundary circle, and the four incidence properties. -/
structure CutSetup (S : Work.Smooth.Jordan.PlaneSchoenflies γ)
    (hball : ∀ θ : ℝ, ‖γ.γ θ‖ < 1) where
  /-- inner parameter of the first crosscut -/
  t₁ : ℝ
  /-- outer parameter of the first crosscut -/
  s₁ : ℝ
  /-- inner parameter of the second crosscut -/
  t₂ : ℝ
  /-- outer parameter of the second crosscut -/
  s₂ : ℝ
  ht₁ : 0 < t₁
  ht₁s₁ : t₁ < s₁
  ht₂ : 0 < t₂
  ht₂s₂ : t₂ < s₂
  /-- the first inner endpoint lies on the curve -/
  hx₁ : Work.Smooth.SphereJordan.base S + t₁ ∈ γ.trace
  /-- the first outer endpoint lies on the boundary circle -/
  hy₁ : Work.Smooth.SphereJordan.base S + s₁ ∈ Metric.sphere (0 : ℂ) 1
  /-- the second inner endpoint lies on the curve -/
  hx₂ : Work.Smooth.SphereJordan.base S - t₂ ∈ γ.trace
  /-- the second outer endpoint lies on the boundary circle -/
  hy₂ : Work.Smooth.SphereJordan.base S - s₂ ∈ Metric.sphere (0 : ℂ) 1
  /-- the open part of the first crosscut lies in the open annulus -/
  hseg₁ : ∀ σ : ℝ, t₁ < σ → σ < s₁ →
    Work.Smooth.SphereJordan.base S + σ ∈ Metric.ball (0 : ℂ) 1 \ S.V
  /-- the open part of the second crosscut lies in the open annulus -/
  hseg₂ : ∀ σ : ℝ, t₂ < σ → σ < s₂ →
    Work.Smooth.SphereJordan.base S - σ ∈ Metric.ball (0 : ℂ) 1 \ S.V
  /-- beyond the first inner endpoint the ray misses the closed disc -/
  hmax₁ : ∀ σ : ℝ, t₁ < σ → Work.Smooth.SphereJordan.base S + σ ∉ closure S.V
  /-- beyond the second inner endpoint the ray misses the closed disc -/
  hmax₂ : ∀ σ : ℝ, t₂ < σ → Work.Smooth.SphereJordan.base S - σ ∉ closure S.V

/-- `t • (1 : ℂ) = (t : ℂ)`. -/
theorem real_smul_one (t : ℝ) : t • (1 : ℂ) = (t : ℂ) := by
  rw [Complex.real_smul, mul_one]

/-- `t • (-1 : ℂ) = -(t : ℂ)`. -/
theorem real_smul_neg_one (t : ℝ) : t • (-1 : ℂ) = -(t : ℂ) := by
  rw [Complex.real_smul]
  ring

/-- **The two crosscuts exist.** -/
theorem exists_cutSetup (S : Work.Smooth.Jordan.PlaneSchoenflies γ)
    (hball : ∀ θ : ℝ, ‖γ.γ θ‖ < 1) : Nonempty (CutSetup S hball) := by
  obtain ⟨t₁, ht₁, hx₁, hmax₁⟩ :=
    Work.Smooth.SphereJordan.exists_crosscut_inner S hball (1 : ℂ) one_ne_zero
  have htK₁ : Work.Smooth.SphereJordan.base S + t₁ • (1 : ℂ) ∈ closure S.V := by
    rw [Work.Smooth.SphereJordan.closure_V_eq S]; exact Or.inr hx₁
  obtain ⟨s₁, hts₁, hy₁, hs₁⟩ :=
    Work.Smooth.SphereJordan.exists_crosscut_outer S hball (1 : ℂ) one_ne_zero ht₁.le htK₁
  obtain ⟨t₂, ht₂, hx₂, hmax₂⟩ :=
    Work.Smooth.SphereJordan.exists_crosscut_inner S hball (-1 : ℂ) (by norm_num)
  have htK₂ : Work.Smooth.SphereJordan.base S + t₂ • (-1 : ℂ) ∈ closure S.V := by
    rw [Work.Smooth.SphereJordan.closure_V_eq S]; exact Or.inr hx₂
  obtain ⟨s₂, hts₂, hy₂, hs₂⟩ :=
    Work.Smooth.SphereJordan.exists_crosscut_outer S hball (-1 : ℂ) (by norm_num) ht₂.le htK₂
  have htv₁ : t₁ < s₁ := by
    rcases lt_or_eq_of_le hts₁ with h | h
    · exact h
    · exfalso
      have h1 : ‖Work.Smooth.SphereJordan.base S + t₁ • (1 : ℂ)‖ = 1 := by
        rw [h]; exact Work.Smooth.SphereJordan.mem_sphere_one_iff _ |>.mp hy₁
      exact absurd h1 (ne_of_lt (Work.Smooth.SphereJordan.closure_V_subset_openBall S hball htK₁))
  have htv₂ : t₂ < s₂ := by
    rcases lt_or_eq_of_le hts₂ with h | h
    · exact h
    · exfalso
      have h1 : ‖Work.Smooth.SphereJordan.base S + t₂ • (-1 : ℂ)‖ = 1 := by
        rw [h]; exact Work.Smooth.SphereJordan.mem_sphere_one_iff _ |>.mp hy₂
      exact absurd h1 (ne_of_lt (Work.Smooth.SphereJordan.closure_V_subset_openBall S hball htK₂))
  refine ⟨t₁, s₁, t₂, s₂, ht₁, htv₁, ht₂, htv₂, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [real_smul_one] using hx₁
  · simpa [real_smul_one] using hy₁
  · have h : Work.Smooth.SphereJordan.base S + t₂ • (-1 : ℂ) ∈ γ.trace := hx₂
    simpa [real_smul_neg_one, sub_eq_add_neg] using h
  · have h : Work.Smooth.SphereJordan.base S + s₂ • (-1 : ℂ) ∈ Metric.sphere (0 : ℂ) 1 := hy₂
    simpa [real_smul_neg_one, sub_eq_add_neg] using h
  · intro σ h1 h2
    refine ⟨?_, ?_⟩
    · have h := hs₁ σ h1.le h2
      rw [Metric.mem_ball, dist_eq_norm] at h ⊢
      simpa [real_smul_one] using h
    · intro hV
      exact hmax₁ σ h1 (subset_closure (by simpa [real_smul_one] using hV))
  · intro σ h1 h2
    refine ⟨?_, ?_⟩
    · have h := hs₂ σ h1.le h2
      rw [Metric.mem_ball, dist_eq_norm] at h ⊢
      simpa [real_smul_neg_one, sub_eq_add_neg] using h
    · intro hV
      have hV' : Work.Smooth.SphereJordan.base S + σ • (-1 : ℂ) ∈ S.V := by
        simpa [real_smul_neg_one, sub_eq_add_neg] using hV
      exact hmax₂ σ h1 (subset_closure hV')
  · intro σ h1
    have h := hmax₁ σ h1
    simpa [real_smul_one] using h
  · intro σ h1
    have h := hmax₂ σ h1
    simpa [real_smul_neg_one, sub_eq_add_neg] using h


/-! ## The pieces cut out by the two crosscuts

**WARNING (recorded after a failed attempt).**  The "half-plane" subdivision below does *not*
behave as one would like.  `upperPiece S` is **not** preconnected in general: if `γ` has a "fjord"
(the unbounded side `S.U` reaching across the base line), the part of the fjord above the base line
is a separate component of `upperPiece S`.  Two independent reviewers produced explicit
counterexamples.  Likewise `innerArcUp S = γ.trace ∩ closure (upperHalfPlane S)` need not be a
single arc, and `annulusOpen S ∩ baseLine S` need not be the two crosscuts.  The correct
side-determination is the *winding-number parity* argument recorded in
`Submission/Work/SphereJordan/span_pairing_plan.lean` (dictionary + oddness + pairing identities),
for which `mem_V_iff_windNumber_ne_zero` and `odd_windNumber_of_mem_V'` below are the dictionary.
The definitions in this section are kept only as vocabulary; the lemmas above are the sound part.

-/

/-- The **upper piece** of the open annulus: its intersection with the upper half-plane.

**Not preconnected in general** -- see the warning above. -/
def upperPiece (S : Work.Smooth.Jordan.PlaneSchoenflies γ) : Set ℂ :=
  upperHalfPlane S ∩ annulusOpen S

/-- The **lower piece** of the open annulus: its intersection with the lower half-plane. -/
def lowerPiece (S : Work.Smooth.Jordan.PlaneSchoenflies γ) : Set ℂ :=
  lowerHalfPlane S ∩ annulusOpen S

/-- The **upper inner arc**: the part of the curve in the closed upper half-plane. -/
def innerArcUp (S : Work.Smooth.Jordan.PlaneSchoenflies γ) : Set ℂ :=
  γ.trace ∩ closure (upperHalfPlane S)

/-- The **upper outer arc**: the part of the boundary circle in the closed upper half-plane. -/
def outerArcUp (S : Work.Smooth.Jordan.PlaneSchoenflies γ) : Set ℂ :=
  Metric.sphere (0 : ℂ) 1 ∩ closure (upperHalfPlane S)

/-- The **first crosscut** (closed segment from the curve out to the boundary circle). -/
def cutUp (S : Work.Smooth.Jordan.PlaneSchoenflies γ) {hball : ∀ θ : ℝ, ‖γ.γ θ‖ < 1}
    (D : CutSetup S hball) : Set ℂ :=
  {z : ℂ | ∃ σ : ℝ, σ ∈ Set.Icc D.t₁ D.s₁ ∧ z = Work.Smooth.SphereJordan.base S + σ}

/-- The **second crosscut** (closed segment from the curve out to the boundary circle). -/
def cutDn (S : Work.Smooth.Jordan.PlaneSchoenflies γ) {hball : ∀ θ : ℝ, ‖γ.γ θ‖ < 1}
    (D : CutSetup S hball) : Set ℂ :=
  {z : ℂ | ∃ σ : ℝ, σ ∈ Set.Icc D.t₂ D.s₂ ∧ z = Work.Smooth.SphereJordan.base S - σ}


/-! ## The dictionary between the bounded side and the winding number -/

/-- **A point off the trace lies in the bounded side exactly when its winding number is
nonzero.** -/
theorem mem_V_iff_windNumber_ne_zero {γ : Work.Smooth.Jordan.PlaneCurve}
    (S : Work.Smooth.Jordan.PlaneSchoenflies γ) {z : ℂ} (hz : z ∉ γ.trace) :
    z ∈ S.V ↔ Work.Smooth.SphereJordan.windNumber γ.γ γ.cont z ≠ 0 := by
  constructor
  · intro hzV
    exact Work.Smooth.SphereJordan.windNumber_ne_zero_of_mem_V S hzV
  · intro hne
    by_contra hzV
    have hU : z ∈ S.U := by
      have hmem : z ∈ S.U ∪ S.V := by
        rw [S.toPlaneSeparation.union_eq]
        exact hz
      exact hmem.resolve_right hzV
    exact hne (Work.Smooth.SphereJordan.windNumber_eq_zero_of_mem_U
      S.toPlaneSeparation hU)

/-- **The winding number of a simple closed plane curve on its bounded side is odd.** -/
theorem odd_windNumber_of_mem_V' {γ : Work.Smooth.Jordan.PlaneCurve}
    (S : Work.Smooth.Jordan.PlaneSchoenflies γ) {z : ℂ} (hz : z ∈ S.V) :
    Odd (Work.Smooth.SphereJordan.windNumber γ.γ γ.cont z) :=
  Work.SphereJordan.odd_windNumber_of_mem_V S hz


/-! ## The arithmetic of the pairing argument -/

/-- **The arithmetic of the pairing lemma.**  If `a + b = 1 + e` with `e` odd and `a`, `b` odd
whenever nonzero, then `a` and `b` vanish together.  (Concretely `a` and `b` are the winding
numbers of two four-arc curves sharing their outer path and differing in their inner arc, and `e`
is the winding number of the original curve at a point of its bounded side.) -/
theorem pair_zero_iff {a b e : ℤ} (ha : a ≠ 0 → Odd a) (hb : b ≠ 0 → Odd b) (he : Odd e)
    (h : a + b = 1 + e) : (a = 0 ↔ b = 0) := by
  obtain ⟨k, hk⟩ := he
  constructor
  · intro hz
    by_contra hb0
    obtain ⟨l, hl⟩ := hb hb0
    rw [hz, zero_add, hk, hl] at h
    omega
  · intro hz
    by_contra ha0
    obtain ⟨l, hl⟩ := ha ha0
    rw [hz, add_zero, hk, hl] at h
    omega


/-! ## The unit circle as a plane curve -/

/-- The unit circle, as a plane curve (the standard parametrisation `θ ↦ e^{iθ}`). -/
def circleCurve : Work.Smooth.Jordan.PlaneCurve where
  γ := fun θ : ℝ => ((Work.Smooth.Jordan.circlePoint θ : Work.Smooth.SphereJordan.Disc) : ℂ)
  cont := by
    have h1 : Continuous (fun θ : ℝ => Complex.exp ((θ : ℂ) * Complex.I)) := by fun_prop
    have h2 : Continuous (fun θ : ℝ =>
        (⟨Complex.exp ((θ : ℂ) * Complex.I), by
          rw [Metric.mem_closedBall, dist_zero_right, Complex.norm_exp_ofReal_mul_I]⟩ :
          Work.Smooth.SphereJordan.Disc)) :=
      Continuous.subtype_mk h1 _
    exact continuous_subtype_val.comp h2
  periodic := by
    intro θ
    apply congrArg (fun z : Work.Smooth.SphereJordan.Disc => ((z : ℂ)))
    apply Subtype.ext
    rw [Work.Smooth.Jordan.circlePoint_coe, Work.Smooth.Jordan.circlePoint_coe]
    rw [show (((θ + 2 * Real.pi : ℝ)) : ℂ) * Complex.I =
        (θ : ℂ) * Complex.I + (2 * (Real.pi : ℂ)) * Complex.I by push_cast; ring]
    rw [Complex.exp_add, Complex.exp_two_pi_mul_I, mul_one]

@[simp] theorem circleCurve_apply (θ : ℝ) :
    circleCurve.γ θ = ((Work.Smooth.Jordan.circlePoint θ : Work.Smooth.SphereJordan.Disc) : ℂ) := rfl



end

end Work.Smooth.SphereJordan
