import Mathlib
import Submission.Work.Geometry.Ulam.arc_second_deriv_sign
import Mathlib.Analysis.Calculus.FDeriv.Pow
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.Real.Pi.Bounds
import Submission.Work.Geometry.Ulam.radial_C2_bounds



namespace Commons.Geometry.Ulam

open Filter
open scoped Topology ContDiff

noncomputable section

/-! ## From radial functions to the profile

This is the next brick after
`spherical_radon_radial_reconstruction_general`.  Given the radial
functions `R,r` close to `1` with vanishing first derivatives at `0`, the
right-hand boundary arc is the parametric curve

`α ↦ (R α * cos α, R α * sin α)`,  `α ∈ [0, π/2]`,

and similarly on the left with `r`.  The profile `f` is obtained by solving
the first coordinate for `α` and reading off the second coordinate:

`f (R α * cos α) = R α * sin α`,  `f (-(r α * cos α)) = r α * sin α`.

The lemma below is the next target: it packages the geometric facts (smoothness,
concavity, positivity, support) that the rest of the odd-dimensional
construction consumes. -/

/-- Right-hand boundary arc of a body of revolution with radial function `R`. -/
def rightArc (R : ℝ → ℝ) (α : ℝ) : ℝ × ℝ :=
  (R α * Real.cos α, R α * Real.sin α)

/-- Left-hand boundary arc of a body of revolution with radial function `r`. -/
def leftArc (r : ℝ → ℝ) (α : ℝ) : ℝ × ℝ :=
  (-(r α * Real.cos α), r α * Real.sin α)

lemma rightArc_at_pi_div_two (R : ℝ → ℝ) :
    (rightArc R (Real.pi / 2)).1 = 0 := by
  simp [rightArc]

lemma leftArc_at_pi_div_two (r : ℝ → ℝ) :
    (leftArc r (Real.pi / 2)).1 = 0 := by
  simp [leftArc]

lemma rightArc_radius_at_pi_div_two (R : ℝ → ℝ) :
    (rightArc R (Real.pi / 2)).2 = R (Real.pi / 2) := by
  simp [rightArc]

lemma leftArc_radius_at_pi_div_two (r : ℝ → ℝ) :
    (leftArc r (Real.pi / 2)).2 = r (Real.pi / 2) := by
  simp [leftArc]

/-- The first coordinate of the right arc is strictly decreasing on `[0, π/2]`
under the quantitative bounds that the radial reconstruction will supply:
`R` stays above `1-η`, and `deriv R` is controlled by `η * α`. -/
lemma rightArc_fst_strictAntiOn
    (R : ℝ → ℝ) {η : ℝ} (hη : 0 < η) (hηsmall : η < 1 / 8)
    (hR_cont : ContDiffOn ℝ (⊤ : ℕ∞) R (Set.Icc 0 (Real.pi / 2)))
    (hR_pos : ∀ α ∈ Set.Icc 0 (Real.pi / 2), 0 < R α)
    (hR_lower : ∀ α ∈ Set.Icc 0 (Real.pi / 2), 1 - η ≤ R α)
    (hR_deriv_bound : ∀ α ∈ Set.Icc 0 (Real.pi / 2), |deriv R α| ≤ η * α) :
    StrictAntiOn (fun α => R α * Real.cos α) (Set.Icc 0 (Real.pi / 2)) := by
  apply strictAntiOn_of_deriv_neg (convex_Icc _ _)
  · exact hR_cont.continuousOn.mul Real.continuous_cos.continuousOn
  · intro α hα
    rw [interior_Icc] at hα
    have hα0 : 0 < α := hα.1
    have hαπ : α < Real.pi / 2 := hα.2
    have hαmem : α ∈ Set.Icc 0 (Real.pi / 2) := ⟨le_of_lt hα0, le_of_lt hαπ⟩
    have hR_diff : DifferentiableAt ℝ R α :=
      (hR_cont.differentiableOn (by simp : ((⊤ : ℕ∞) : WithTop ℕ∞) ≠ 0) α hαmem).differentiableAt
        (Icc_mem_nhds hα0 hαπ)
    have hderiv : deriv (fun α => R α * Real.cos α) α =
        deriv R α * Real.cos α - R α * Real.sin α := by
      have h := deriv_mul hR_diff Real.differentiableAt_cos
      change deriv (R * Real.cos) α = deriv R α * Real.cos α - R α * Real.sin α
      simpa [Real.deriv_cos, sub_eq_add_neg] using h
    rw [hderiv]
    have hR_gt : 1 - η ≤ R α := hR_lower α hαmem
    have hderivR_le : |deriv R α| ≤ η * α := hR_deriv_bound α hαmem
    have hsin : (2 / Real.pi) * α ≤ Real.sin α :=
      Real.mul_le_sin (le_of_lt hα0) (le_of_lt hαπ)
    have hcos_le : Real.cos α ≤ 1 := Real.cos_le_one α
    have h1 : deriv R α * Real.cos α ≤ η * α := by
      have hle := (abs_le.mp hderivR_le).2
      have hcos_nonneg : 0 ≤ Real.cos α :=
        Real.cos_nonneg_of_mem_Icc ⟨by linarith [Real.pi_pos], hαπ.le⟩
      have hηα_nonneg : 0 ≤ η * α := mul_nonneg (le_of_lt hη) (le_of_lt hα0)
      calc
        deriv R α * Real.cos α ≤ (η * α) * Real.cos α :=
          mul_le_mul_of_nonneg_right hle hcos_nonneg
        _ ≤ (η * α) * 1 := mul_le_mul_of_nonneg_left hcos_le hηα_nonneg
        _ = η * α := by ring
    have h2 : (1 - η) * ((2 / Real.pi) * α) ≤ R α * Real.sin α := by
      have hsin_pos : 0 < Real.sin α :=
        Real.sin_pos_of_pos_of_lt_pi hα0 (by linarith [Real.pi_pos])
      have hle := mul_le_mul_of_nonneg_right hR_gt (le_of_lt hsin_pos)
      nlinarith [hsin, hle]
    have hcoef : η < (1 - η) * (2 / Real.pi) := by
      have hpi4 : Real.pi < 4 := Real.pi_lt_four
      have hhalf : (1 / 2 : ℝ) < 2 / Real.pi := by
        field_simp
        nlinarith [Real.pi_pos, hpi4]
      have h1 : (1 - η) * (1 / 2 : ℝ) < (1 - η) * (2 / Real.pi) :=
        mul_lt_mul_of_pos_left hhalf (by linarith : 0 < 1 - η)
      have h2 : η < (1 - η) * (1 / 2 : ℝ) := by nlinarith [hηsmall, hη]
      linarith
    have hcoefα : η * α < (1 - η) * (2 / Real.pi) * α :=
      mul_lt_mul_of_pos_right hcoef hα0
    have hlt : deriv R α * Real.cos α < R α * Real.sin α := by
      calc
        deriv R α * Real.cos α ≤ η * α := h1
        _ < (1 - η) * (2 / Real.pi) * α := hcoefα
        _ = (1 - η) * (2 / Real.pi * α) := by ring
        _ ≤ R α * Real.sin α := h2
    linarith

lemma rightArc_deriv_neg
    (R : ℝ → ℝ) {η : ℝ} (hη : 0 < η) (hηsmall : η < 1 / 8)
    (hR_cont : ContDiffOn ℝ (⊤ : ℕ∞) R (Set.Icc 0 (Real.pi / 2)))
    (hR_pos : ∀ α ∈ Set.Icc 0 (Real.pi / 2), 0 < R α)
    (hR_lower : ∀ α ∈ Set.Icc 0 (Real.pi / 2), 1 - η ≤ R α)
    (hR_deriv_bound : ∀ α ∈ Set.Icc 0 (Real.pi / 2), |deriv R α| ≤ η * α)
    {α : ℝ} (hα : α ∈ Set.Ioo 0 (Real.pi / 2)) :
    deriv R α * Real.cos α - R α * Real.sin α < 0 := by
  have hα0 : 0 < α := hα.1
  have hαπ : α < Real.pi / 2 := hα.2
  have hαmem : α ∈ Set.Icc 0 (Real.pi / 2) := ⟨le_of_lt hα0, le_of_lt hαπ⟩
  have hR_gt : 1 - η ≤ R α := hR_lower α hαmem
  have hderivR_le : |deriv R α| ≤ η * α := hR_deriv_bound α hαmem
  have hsin : (2 / Real.pi) * α ≤ Real.sin α :=
    Real.mul_le_sin (le_of_lt hα0) (le_of_lt hαπ)
  have hcos_le : Real.cos α ≤ 1 := Real.cos_le_one α
  have h1 : deriv R α * Real.cos α ≤ η * α := by
    have hle := (abs_le.mp hderivR_le).2
    have hcos_nonneg : 0 ≤ Real.cos α :=
      Real.cos_nonneg_of_mem_Icc ⟨by linarith [Real.pi_pos], hαπ.le⟩
    have hηα_nonneg : 0 ≤ η * α := mul_nonneg (le_of_lt hη) (le_of_lt hα0)
    calc
      deriv R α * Real.cos α ≤ (η * α) * Real.cos α :=
        mul_le_mul_of_nonneg_right hle hcos_nonneg
      _ ≤ (η * α) * 1 := mul_le_mul_of_nonneg_left hcos_le hηα_nonneg
      _ = η * α := by ring
  have h2 : (1 - η) * ((2 / Real.pi) * α) ≤ R α * Real.sin α := by
    have hsin_pos : 0 < Real.sin α :=
      Real.sin_pos_of_pos_of_lt_pi hα0 (by linarith [Real.pi_pos])
    have hle := mul_le_mul_of_nonneg_right hR_gt (le_of_lt hsin_pos)
    nlinarith [hsin, hle]
  have hcoef : η < (1 - η) * (2 / Real.pi) := by
    have hpi4 : Real.pi < 4 := Real.pi_lt_four
    have hhalf : (1 / 2 : ℝ) < 2 / Real.pi := by
      field_simp
      nlinarith [Real.pi_pos, hpi4]
    have h1 : (1 - η) * (1 / 2 : ℝ) < (1 - η) * (2 / Real.pi) :=
      mul_lt_mul_of_pos_left hhalf (by linarith : 0 < 1 - η)
    have h2 : η < (1 - η) * (1 / 2 : ℝ) := by nlinarith [hηsmall, hη]
    linarith
  have hcoefα : η * α < (1 - η) * (2 / Real.pi) * α :=
    mul_lt_mul_of_pos_right hcoef hα0
  have hlt : deriv R α * Real.cos α < R α * Real.sin α := by
    calc
      deriv R α * Real.cos α ≤ η * α := h1
      _ < (1 - η) * (2 / Real.pi) * α := hcoefα
      _ = (1 - η) * (2 / Real.pi * α) := by ring
      _ ≤ R α * Real.sin α := h2
  linarith

/-- The first coordinate of the right arc maps `[0, π/2]` onto `[0, R 0]`. -/
lemma rightArc_fst_image_eq
    (R : ℝ → ℝ) {η : ℝ} (hη : 0 < η) (hηsmall : η < 1 / 8)
    (hR_cont : ContDiffOn ℝ (⊤ : ℕ∞) R (Set.Icc 0 (Real.pi / 2)))
    (hR_pos : ∀ α ∈ Set.Icc 0 (Real.pi / 2), 0 < R α)
    (hR_lower : ∀ α ∈ Set.Icc 0 (Real.pi / 2), 1 - η ≤ R α)
    (hR_deriv_bound : ∀ α ∈ Set.Icc 0 (Real.pi / 2), |deriv R α| ≤ η * α) :
    (fun α => R α * Real.cos α) '' Set.Icc 0 (Real.pi / 2) = Set.Icc 0 (R 0) := by
  have hanti := (rightArc_fst_strictAntiOn R hη hηsmall hR_cont hR_pos hR_lower hR_deriv_bound).antitoneOn
  have hcont : ContinuousOn (fun α => R α * Real.cos α) (Set.Icc 0 (Real.pi / 2)) :=
    hR_cont.continuousOn.mul Real.continuous_cos.continuousOn
  have h := ContinuousOn.image_Icc_of_antitoneOn (a := 0) (b := Real.pi / 2)
    (by positivity) hcont hanti
  simpa [Real.cos_pi_div_two, Real.cos_zero, mul_one, mul_zero] using h

/-- The first coordinate of the left arc is strictly increasing on `[0, π/2]`
(mirror of the right arc). -/
lemma leftArc_fst_strictMonoOn
    (r : ℝ → ℝ) {η : ℝ} (hη : 0 < η) (hηsmall : η < 1 / 8)
    (hr_cont : ContDiffOn ℝ (⊤ : ℕ∞) r (Set.Icc 0 (Real.pi / 2)))
    (hr_pos : ∀ α ∈ Set.Icc 0 (Real.pi / 2), 0 < r α)
    (hr_lower : ∀ α ∈ Set.Icc 0 (Real.pi / 2), 1 - η ≤ r α)
    (hr_deriv_bound : ∀ α ∈ Set.Icc 0 (Real.pi / 2), |deriv r α| ≤ η * α) :
    StrictMonoOn (fun α => -(r α * Real.cos α)) (Set.Icc 0 (Real.pi / 2)) := by
  intro a ha b hb hab
  have h := rightArc_fst_strictAntiOn r hη hηsmall hr_cont hr_pos hr_lower hr_deriv_bound ha hb hab
  linarith

/-- The first coordinate of the left arc maps `[0, π/2]` onto `[-r 0, 0]`. -/
lemma leftArc_fst_image_eq
    (r : ℝ → ℝ) {η : ℝ} (hη : 0 < η) (hηsmall : η < 1 / 8)
    (hr_cont : ContDiffOn ℝ (⊤ : ℕ∞) r (Set.Icc 0 (Real.pi / 2)))
    (hr_pos : ∀ α ∈ Set.Icc 0 (Real.pi / 2), 0 < r α)
    (hr_lower : ∀ α ∈ Set.Icc 0 (Real.pi / 2), 1 - η ≤ r α)
    (hr_deriv_bound : ∀ α ∈ Set.Icc 0 (Real.pi / 2), |deriv r α| ≤ η * α) :
    (fun α => -(r α * Real.cos α)) '' Set.Icc 0 (Real.pi / 2) = Set.Icc (-(r 0)) 0 := by
  have hmono := leftArc_fst_strictMonoOn r hη hηsmall hr_cont hr_pos hr_lower hr_deriv_bound
  have hcont : ContinuousOn (fun α => -(r α * Real.cos α)) (Set.Icc 0 (Real.pi / 2)) :=
    (hr_cont.continuousOn.mul Real.continuous_cos.continuousOn).neg
  have h := ContinuousOn.image_Icc_of_monotoneOn (a := 0) (b := Real.pi / 2)
    (by positivity) hcont hmono.monotoneOn
  simpa [Real.cos_pi_div_two, Real.cos_zero, mul_one, mul_zero] using h

lemma right_zero_pos
    (R : ℝ → ℝ)
    (hR_pos : ∀ α ∈ Set.Icc 0 (Real.pi / 2), 0 < R α) :
    0 < R 0 :=
  hR_pos 0 ⟨le_rfl, by linarith [Real.pi_pos]⟩

lemma left_zero_pos
    (r : ℝ → ℝ)
    (hr_pos : ∀ α ∈ Set.Icc 0 (Real.pi / 2), 0 < r α) :
    0 < r 0 :=
  hr_pos 0 ⟨le_rfl, by linarith [Real.pi_pos]⟩

/-- The angle on the right arc corresponding to first coordinate `t`. -/
noncomputable def rightAlpha (R : ℝ → ℝ) (t : ℝ) : ℝ :=
  Function.invFunOn (fun α => R α * Real.cos α) (Set.Icc 0 (Real.pi / 2)) t

/-- The angle on the left arc corresponding to first coordinate `t`. -/
noncomputable def leftAlpha (r : ℝ → ℝ) (t : ℝ) : ℝ :=
  Function.invFunOn (fun α => -(r α * Real.cos α)) (Set.Icc 0 (Real.pi / 2)) t

/-- The profile obtained by gluing the two arcs at `0`.
Outside the interval `[-r 0, R 0]` it is defined to be zero. -/
noncomputable def profileGlue (R r : ℝ → ℝ) (t : ℝ) : ℝ :=
  if t ∈ Set.Icc 0 (R 0) then R (rightAlpha R t) * Real.sin (rightAlpha R t)
  else if t ∈ Set.Icc (-(r 0)) 0 then r (leftAlpha r t) * Real.sin (leftAlpha r t)
  else 0

lemma rightAlpha_spec
    (R : ℝ → ℝ) {η : ℝ} (hη : 0 < η) (hηsmall : η < 1 / 8)
    (hR_cont : ContDiffOn ℝ (⊤ : ℕ∞) R (Set.Icc 0 (Real.pi / 2)))
    (hR_pos : ∀ α ∈ Set.Icc 0 (Real.pi / 2), 0 < R α)
    (hR_lower : ∀ α ∈ Set.Icc 0 (Real.pi / 2), 1 - η ≤ R α)
    (hR_deriv_bound : ∀ α ∈ Set.Icc 0 (Real.pi / 2), |deriv R α| ≤ η * α)
    {t : ℝ} (ht : t ∈ Set.Icc 0 (R 0)) :
    rightAlpha R t ∈ Set.Icc 0 (Real.pi / 2) ∧
      R (rightAlpha R t) * Real.cos (rightAlpha R t) = t := by
  have himage := rightArc_fst_image_eq R hη hηsmall hR_cont hR_pos hR_lower hR_deriv_bound
  have ht' : t ∈ (fun α => R α * Real.cos α) '' Set.Icc 0 (Real.pi / 2) := by
    rw [himage]
    exact ht
  rcases ht' with ⟨α, hα, hαt⟩
  have h_exists : ∃ a, a ∈ Set.Icc 0 (Real.pi / 2) ∧
      (fun α => R α * Real.cos α) a = t := ⟨α, hα, hαt⟩
  have h := Function.invFunOn_pos h_exists
  simpa [rightAlpha] using h

lemma leftAlpha_spec
    (r : ℝ → ℝ) {η : ℝ} (hη : 0 < η) (hηsmall : η < 1 / 8)
    (hr_cont : ContDiffOn ℝ (⊤ : ℕ∞) r (Set.Icc 0 (Real.pi / 2)))
    (hr_pos : ∀ α ∈ Set.Icc 0 (Real.pi / 2), 0 < r α)
    (hr_lower : ∀ α ∈ Set.Icc 0 (Real.pi / 2), 1 - η ≤ r α)
    (hr_deriv_bound : ∀ α ∈ Set.Icc 0 (Real.pi / 2), |deriv r α| ≤ η * α)
    {t : ℝ} (ht : t ∈ Set.Icc (-(r 0)) 0) :
    leftAlpha r t ∈ Set.Icc 0 (Real.pi / 2) ∧
      -(r (leftAlpha r t) * Real.cos (leftAlpha r t)) = t := by
  have himage := leftArc_fst_image_eq r hη hηsmall hr_cont hr_pos hr_lower hr_deriv_bound
  have ht' : t ∈ (fun α => -(r α * Real.cos α)) '' Set.Icc 0 (Real.pi / 2) := by
    rw [himage]
    exact ht
  rcases ht' with ⟨α, hα, hαt⟩
  have h_exists : ∃ a, a ∈ Set.Icc 0 (Real.pi / 2) ∧
      (fun α => -(r α * Real.cos α)) a = t := ⟨α, hα, hαt⟩
  have h := Function.invFunOn_pos h_exists
  simpa [leftAlpha] using h

lemma rightAlpha_zero
    (R : ℝ → ℝ) {η : ℝ} (hη : 0 < η) (hηsmall : η < 1 / 8)
    (hR_cont : ContDiffOn ℝ (⊤ : ℕ∞) R (Set.Icc 0 (Real.pi / 2)))
    (hR_pos : ∀ α ∈ Set.Icc 0 (Real.pi / 2), 0 < R α)
    (hR_lower : ∀ α ∈ Set.Icc 0 (Real.pi / 2), 1 - η ≤ R α)
    (hR_deriv_bound : ∀ α ∈ Set.Icc 0 (Real.pi / 2), |deriv R α| ≤ η * α) :
    rightAlpha R 0 = Real.pi / 2 := by
  have hinj : Set.InjOn (fun α => R α * Real.cos α) (Set.Icc 0 (Real.pi / 2)) :=
    (rightArc_fst_strictAntiOn R hη hηsmall hR_cont hR_pos hR_lower hR_deriv_bound).injOn
  have hmem : (Real.pi / 2) ∈ Set.Icc 0 (Real.pi / 2) := by
    constructor <;> linarith [Real.pi_pos]
  have hleft := hinj.leftInvOn_invFunOn hmem
  have hf : R (Real.pi / 2) * Real.cos (Real.pi / 2) = 0 := by simp
  rw [rightAlpha]
  simpa [hf] using hleft

lemma leftAlpha_zero
    (r : ℝ → ℝ) {η : ℝ} (hη : 0 < η) (hηsmall : η < 1 / 8)
    (hr_cont : ContDiffOn ℝ (⊤ : ℕ∞) r (Set.Icc 0 (Real.pi / 2)))
    (hr_pos : ∀ α ∈ Set.Icc 0 (Real.pi / 2), 0 < r α)
    (hr_lower : ∀ α ∈ Set.Icc 0 (Real.pi / 2), 1 - η ≤ r α)
    (hr_deriv_bound : ∀ α ∈ Set.Icc 0 (Real.pi / 2), |deriv r α| ≤ η * α) :
    leftAlpha r 0 = Real.pi / 2 := by
  have hinj : Set.InjOn (fun α => -(r α * Real.cos α)) (Set.Icc 0 (Real.pi / 2)) :=
    (leftArc_fst_strictMonoOn r hη hηsmall hr_cont hr_pos hr_lower hr_deriv_bound).injOn
  have hmem : (Real.pi / 2) ∈ Set.Icc 0 (Real.pi / 2) := by
    constructor <;> linarith [Real.pi_pos]
  have hleft := hinj.leftInvOn_invFunOn hmem
  have hf : -(r (Real.pi / 2) * Real.cos (Real.pi / 2)) = 0 := by simp
  rw [leftAlpha]
  simpa [hf] using hleft

lemma profileGlue_zero_right
    (R r : ℝ → ℝ) {η : ℝ} (hη : 0 < η) (hηsmall : η < 1 / 8)
    (hR_cont : ContDiffOn ℝ (⊤ : ℕ∞) R (Set.Icc 0 (Real.pi / 2)))
    (hR_pos : ∀ α ∈ Set.Icc 0 (Real.pi / 2), 0 < R α)
    (hR_lower : ∀ α ∈ Set.Icc 0 (Real.pi / 2), 1 - η ≤ R α)
    (hR_deriv_bound : ∀ α ∈ Set.Icc 0 (Real.pi / 2), |deriv R α| ≤ η * α) :
    profileGlue R r 0 = R (Real.pi / 2) := by
  have hR0 := rightAlpha_zero R hη hηsmall hR_cont hR_pos hR_lower hR_deriv_bound
  have h0mem : (0 : ℝ) ∈ Set.Icc 0 (R 0) := by
    constructor <;> [rfl; exact le_of_lt (hR_pos 0 (by constructor <;> linarith [Real.pi_pos]))]
  simp [profileGlue, h0mem, hR0, Real.sin_pi_div_two]

lemma profileGlue_zero_left
    (R r : ℝ → ℝ) {η : ℝ} (hη : 0 < η) (hηsmall : η < 1 / 8)
    (hr_cont : ContDiffOn ℝ (⊤ : ℕ∞) r (Set.Icc 0 (Real.pi / 2)))
    (hr_pos : ∀ α ∈ Set.Icc 0 (Real.pi / 2), 0 < r α)
    (hr_lower : ∀ α ∈ Set.Icc 0 (Real.pi / 2), 1 - η ≤ r α)
    (hr_deriv_bound : ∀ α ∈ Set.Icc 0 (Real.pi / 2), |deriv r α| ≤ η * α)
    (hRr_end : R (Real.pi / 2) = r (Real.pi / 2)) :
    r (leftAlpha r 0) * Real.sin (leftAlpha r 0) = R (Real.pi / 2) := by
  have hl0 := leftAlpha_zero r hη hηsmall hr_cont hr_pos hr_lower hr_deriv_bound
  simp [hl0, Real.sin_pi_div_two, hRr_end]

lemma profileGlue_support_subset
    (R r : ℝ → ℝ) {η : ℝ} (hη : 0 < η) (hηsmall : η < 1 / 8)
    (hR_cont : ContDiffOn ℝ (⊤ : ℕ∞) R (Set.Icc 0 (Real.pi / 2)))
    (hr_cont : ContDiffOn ℝ (⊤ : ℕ∞) r (Set.Icc 0 (Real.pi / 2)))
    (hR_pos : ∀ α ∈ Set.Icc 0 (Real.pi / 2), 0 < R α)
    (hr_pos : ∀ α ∈ Set.Icc 0 (Real.pi / 2), 0 < r α)
    (hR_lower : ∀ α ∈ Set.Icc 0 (Real.pi / 2), 1 - η ≤ R α)
    (hr_lower : ∀ α ∈ Set.Icc 0 (Real.pi / 2), 1 - η ≤ r α)
    (hR_deriv_bound : ∀ α ∈ Set.Icc 0 (Real.pi / 2), |deriv R α| ≤ η * α)
    (hr_deriv_bound : ∀ α ∈ Set.Icc 0 (Real.pi / 2), |deriv r α| ≤ η * α)
    (hRr_end : R (Real.pi / 2) = r (Real.pi / 2)) :
    Function.support (profileGlue R r) ⊆ Set.Icc (-(r 0)) (R 0) := by
  intro t ht
  by_contra hnot
  have hzero : profileGlue R r t = 0 := by
    simp only [profileGlue]
    split_ifs with ht1 ht2
    · have hr0 : 0 ≤ r 0 := le_of_lt (hr_pos 0 (by constructor <;> linarith [Real.pi_pos]))
      exact False.elim (hnot ⟨le_trans (neg_nonpos.mpr hr0) ht1.1, ht1.2⟩)
    · have hR0 : 0 ≤ R 0 := le_of_lt (hR_pos 0 (by constructor <;> linarith [Real.pi_pos]))
      exact False.elim (hnot ⟨ht2.1, le_trans ht2.2 hR0⟩)
    · rfl
  exact ht (by simpa [Function.mem_support] using hzero)

lemma profileGlue_pos
    (R r : ℝ → ℝ) {η : ℝ} (hη : 0 < η) (hηsmall : η < 1 / 8)
    (hR_cont : ContDiffOn ℝ (⊤ : ℕ∞) R (Set.Icc 0 (Real.pi / 2)))
    (hr_cont : ContDiffOn ℝ (⊤ : ℕ∞) r (Set.Icc 0 (Real.pi / 2)))
    (hR_pos : ∀ α ∈ Set.Icc 0 (Real.pi / 2), 0 < R α)
    (hr_pos : ∀ α ∈ Set.Icc 0 (Real.pi / 2), 0 < r α)
    (hR_lower : ∀ α ∈ Set.Icc 0 (Real.pi / 2), 1 - η ≤ R α)
    (hr_lower : ∀ α ∈ Set.Icc 0 (Real.pi / 2), 1 - η ≤ r α)
    (hR_deriv_bound : ∀ α ∈ Set.Icc 0 (Real.pi / 2), |deriv R α| ≤ η * α)
    (hr_deriv_bound : ∀ α ∈ Set.Icc 0 (Real.pi / 2), |deriv r α| ≤ η * α)
    (hRr_end : R (Real.pi / 2) = r (Real.pi / 2)) :
    ∀ t ∈ Set.Ioo (-(r 0)) (R 0), 0 < profileGlue R r t := by
  intro t ht
  rcases lt_trichotomy t 0 with htneg | ht0 | htpos
  · -- left branch
    have ht_mem : t ∈ Set.Icc (-(r 0)) 0 := ⟨le_of_lt ht.1, le_of_lt htneg⟩
    have ht_not_mem : t ∉ Set.Icc 0 (R 0) := by
      intro h
      linarith [h.1, htneg]
    have hspec := leftAlpha_spec r hη hηsmall hr_cont hr_pos hr_lower hr_deriv_bound ht_mem
    set α := leftAlpha r t with hα
    have hα_mem : α ∈ Set.Icc 0 (Real.pi / 2) := hspec.1
    have hαeq : -(r α * Real.cos α) = t := hspec.2
    have hsin_pos : 0 < Real.sin α := by
      have hprod : 0 < r α * Real.cos α := by nlinarith [hαeq, htneg]
      have hcos_pos : 0 < Real.cos α :=
        pos_of_mul_pos_right hprod (le_of_lt (hr_pos α hα_mem))
      have hα_lt : α < Real.pi / 2 := by
        have hne : α ≠ Real.pi / 2 := by
          intro h
          rw [h, Real.cos_pi_div_two] at hcos_pos
          linarith
        exact lt_of_le_of_ne hα_mem.2 hne
      have hα_gt : 0 < α := by
        have hne : α ≠ 0 := by
          intro h
          rw [h] at hαeq
          simp at hαeq
          nlinarith [left_zero_pos r hr_pos, ht.1]
        exact lt_of_le_of_ne hα_mem.1 (Ne.symm hne)
      exact Real.sin_pos_of_pos_of_lt_pi hα_gt (by linarith [Real.pi_pos, hα_mem.2])
    have hval : profileGlue R r t = r α * Real.sin α := by
      simp [profileGlue, ht_not_mem, ht_mem, hα]
    rw [hval]
    exact mul_pos (hr_pos α hα_mem) hsin_pos
  · -- t = 0
    subst ht0
    have hval : profileGlue R r 0 = R (Real.pi / 2) :=
      profileGlue_zero_right R r hη hηsmall hR_cont hR_pos hR_lower hR_deriv_bound
    rw [hval]
    exact hR_pos (Real.pi / 2) ⟨by linarith [Real.pi_pos], le_rfl⟩
  · -- right branch
    have ht_mem : t ∈ Set.Icc 0 (R 0) := ⟨le_of_lt htpos, le_of_lt ht.2⟩
    have hspec := rightAlpha_spec R hη hηsmall hR_cont hR_pos hR_lower hR_deriv_bound ht_mem
    set α := rightAlpha R t with hα
    have hα_mem : α ∈ Set.Icc 0 (Real.pi / 2) := hspec.1
    have hαeq : R α * Real.cos α = t := hspec.2
    have hsin_pos : 0 < Real.sin α := by
      have hprod : 0 < R α * Real.cos α := by nlinarith [hαeq, htpos]
      have hcos_pos : 0 < Real.cos α :=
        pos_of_mul_pos_right hprod (le_of_lt (hR_pos α hα_mem))
      have hα_lt : α < Real.pi / 2 := by
        have hne : α ≠ Real.pi / 2 := by
          intro h
          rw [h, Real.cos_pi_div_two] at hcos_pos
          linarith
        exact lt_of_le_of_ne hα_mem.2 hne
      have hα_gt : 0 < α := by
        have hne : α ≠ 0 := by
          intro h
          rw [h] at hαeq
          simp at hαeq
          nlinarith [hαeq, ht.2]
        exact lt_of_le_of_ne hα_mem.1 (Ne.symm hne)
      exact Real.sin_pos_of_pos_of_lt_pi hα_gt (by linarith [Real.pi_pos, hα_mem.2])
    have hval : profileGlue R r t = R α * Real.sin α := by
      simp [profileGlue, ht_mem, hα]
    rw [hval]
    exact mul_pos (hR_pos α hα_mem) hsin_pos

/-- The right-branch profile as a function of the first coordinate. -/
noncomputable def rightProfile (R : ℝ → ℝ) (t : ℝ) : ℝ :=
  R (rightAlpha R t) * Real.sin (rightAlpha R t)

/-- Continuity of the right inverse branch at interior points of its interval. -/
lemma rightAlpha_continuousAt
    (R : ℝ → ℝ) {η : ℝ} (hη : 0 < η) (hηsmall : η < 1 / 8)
    (hR_cont : ContDiffOn ℝ (⊤ : ℕ∞) R (Set.Icc 0 (Real.pi / 2)))
    (hR_pos : ∀ α ∈ Set.Icc 0 (Real.pi / 2), 0 < R α)
    (hR_lower : ∀ α ∈ Set.Icc 0 (Real.pi / 2), 1 - η ≤ R α)
    (hR_deriv_bound : ∀ α ∈ Set.Icc 0 (Real.pi / 2), |deriv R α| ≤ η * α)
    {t : ℝ} (ht : t ∈ Set.Ioo 0 (R 0)) :
    ContinuousAt (rightAlpha R) t := by
  rw [Metric.continuousAt_iff]
  intro ε hε
  let f : ℝ → ℝ := fun α => R α * Real.cos α
  have hf_anti : StrictAntiOn f (Set.Icc 0 (Real.pi / 2)) :=
    rightArc_fst_strictAntiOn R hη hηsmall hR_cont hR_pos hR_lower hR_deriv_bound
  have hf_cont : ContinuousOn f (Set.Icc 0 (Real.pi / 2)) :=
    hR_cont.continuousOn.mul Real.continuous_cos.continuousOn
  have ht_mem : t ∈ Set.Icc 0 (R 0) := ⟨le_of_lt ht.1, le_of_lt ht.2⟩
  have hα_spec := rightAlpha_spec R hη hηsmall hR_cont hR_pos hR_lower hR_deriv_bound ht_mem
  set α := rightAlpha R t with hα
  have hα_mem : α ∈ Set.Icc 0 (Real.pi / 2) := hα_spec.1
  have hαeq : f α = t := hα_spec.2
  have hα_pos : 0 < α := by
    by_contra h
    have hα0 : α = 0 := le_antisymm (le_of_not_gt h) hα_mem.1
    have : t = R 0 := by
      rw [← hαeq, hα0]
      simp [f, Real.cos_zero, mul_one]
    linarith [ht.2]
  have hα_lt_pi_div_two : α < Real.pi / 2 := by
    by_contra h
    have hαpi : α = Real.pi / 2 := le_antisymm hα_mem.2 (le_of_not_gt h)
    have : t = 0 := by
      rw [← hαeq, hαpi]
      simp [f, Real.cos_pi_div_two]
    linarith [ht.1]
  let β : ℝ := max 0 (α - ε / 2)
  let γ : ℝ := min (Real.pi / 2) (α + ε / 2)
  have hβ_mem : β ∈ Set.Icc 0 (Real.pi / 2) := by
    constructor
    · exact le_max_left _ _
    · exact le_trans (max_le hα_mem.1 (by linarith)) hα_mem.2
  have hγ_mem : γ ∈ Set.Icc 0 (Real.pi / 2) := by
    constructor
    · exact le_trans hα_mem.1 (le_min (by linarith [Real.pi_pos]) (by linarith [hα_mem.1, hε]))
    · exact min_le_left _ _
  have hβ_lt_α : β < α := by
    dsimp [β]
    exact max_lt hα_pos (by linarith)
  have hα_lt_γ : α < γ := by
    dsimp [γ]
    exact lt_min hα_lt_pi_div_two (by linarith)
  have hfβ_gt : t < f β := by
    have h := hf_anti hβ_mem hα_mem hβ_lt_α
    simpa [hαeq] using h
  have hfγ_lt : f γ < t := by
    have h := hf_anti hα_mem hγ_mem hα_lt_γ
    simpa [hαeq] using h
  let δ : ℝ := min (t - f γ) (f β - t)
  have hδ_pos : 0 < δ := by
    dsimp [δ]
    exact lt_min (sub_pos.mpr hfγ_lt) (sub_pos.mpr hfβ_gt)
  refine ⟨δ, hδ_pos, ?_⟩
  intro y hy
  have hy_lt : |y - t| < δ := by simpa [Real.dist_eq] using hy
  have hy_lower : f γ < y := by
    have h1 : t - δ < y := by linarith [(abs_lt.mp hy_lt).1]
    have h2 : f γ ≤ t - δ := by
      dsimp [δ]
      linarith [min_le_left (t - f γ) (f β - t)]
    exact lt_of_le_of_lt h2 h1
  have hy_upper : y < f β := by
    have h1 : y < t + δ := by linarith [(abs_lt.mp hy_lt).2]
    have h2 : t + δ ≤ f β := by
      dsimp [δ]
      linarith [min_le_right (t - f γ) (f β - t)]
    exact lt_of_lt_of_le h1 h2
  have hy_image : y ∈ f '' Set.Ioo β γ := by
    have hf_anti_sub : StrictAntiOn f (Set.Icc β γ) :=
      hf_anti.mono (Set.Icc_subset_Icc hβ_mem.1 hγ_mem.2)
    have hf_cont_sub : ContinuousOn f (Set.Icc β γ) :=
      hf_cont.mono (Set.Icc_subset_Icc hβ_mem.1 hγ_mem.2)
    have himage := ContinuousOn.image_Ioo_of_strictAntiOn (a := β) (b := γ)
      (le_of_lt (lt_trans hβ_lt_α hα_lt_γ)) hf_cont_sub hf_anti_sub
    rw [himage]
    exact ⟨hy_lower, hy_upper⟩
  rcases hy_image with ⟨d, hd_mem, hd_eq⟩
  have hy_Icc : y ∈ Set.Icc 0 (R 0) := by
    constructor
    · have : 0 ≤ f γ := by
        have hcos : 0 ≤ Real.cos γ :=
          Real.cos_nonneg_of_mem_Icc ⟨by linarith [hγ_mem.1, Real.pi_pos], hγ_mem.2⟩
        exact mul_nonneg (le_of_lt (hR_pos γ hγ_mem)) hcos
      linarith
    · have h0 : (0:ℝ) ∈ Set.Icc 0 (Real.pi / 2) := ⟨le_rfl, by linarith [Real.pi_pos]⟩
      have h := hf_anti.antitoneOn h0 hβ_mem hβ_mem.1
      have : f β ≤ R 0 := by simpa [f, Real.cos_zero, mul_one] using h
      linarith
  have hy_spec := rightAlpha_spec R hη hηsmall hR_cont hR_pos hR_lower hR_deriv_bound hy_Icc
  have h_eq : rightAlpha R y = d := by
    apply hf_anti.injOn
    · exact hy_spec.1
    · exact ⟨le_trans hβ_mem.1 (le_of_lt hd_mem.1),
        le_trans (le_of_lt hd_mem.2) hγ_mem.2⟩
    · simpa [hd_eq] using hy_spec.2
  have hdist : |rightAlpha R y - α| < ε := by
    rw [h_eq]
    have h1 : α - ε / 2 ≤ d := by
      have : α - ε / 2 ≤ β := le_max_right _ _
      linarith [hd_mem.1]
    have h2 : d ≤ α + ε / 2 := by
      have : γ ≤ α + ε / 2 := min_le_right _ _
      linarith [hd_mem.2]
    rw [abs_lt]
    exact ⟨by linarith, by linarith⟩
  simpa [Real.dist_eq, hα] using hdist

/-- Derivative of the right inverse branch, extracted for the second-derivative
computation. -/
lemma rightAlpha_deriv
    (R : ℝ → ℝ) {η : ℝ} (hη : 0 < η) (hηsmall : η < 1 / 8)
    (hR_cont : ContDiffOn ℝ (⊤ : ℕ∞) R (Set.Icc 0 (Real.pi / 2)))
    (hR_pos : ∀ α ∈ Set.Icc 0 (Real.pi / 2), 0 < R α)
    (hR_lower : ∀ α ∈ Set.Icc 0 (Real.pi / 2), 1 - η ≤ R α)
    (hR_deriv_bound : ∀ α ∈ Set.Icc 0 (Real.pi / 2), |deriv R α| ≤ η * α)
    {t : ℝ} (ht : t ∈ Set.Ioo 0 (R 0)) :
    deriv (rightAlpha R) t =
      (deriv R (rightAlpha R t) * Real.cos (rightAlpha R t) -
        R (rightAlpha R t) * Real.sin (rightAlpha R t))⁻¹ := by
  let α := rightAlpha R t
  have ht_mem : t ∈ Set.Icc 0 (R 0) := ⟨le_of_lt ht.1, le_of_lt ht.2⟩
  have hα_spec := rightAlpha_spec R hη hηsmall hR_cont hR_pos hR_lower hR_deriv_bound ht_mem
  have hα_mem : α ∈ Set.Icc 0 (Real.pi / 2) := hα_spec.1
  have hαeq : R α * Real.cos α = t := hα_spec.2
  have hα_pos : 0 < α := by
    by_contra h
    have hα0 : α = 0 := le_antisymm (le_of_not_gt h) hα_mem.1
    have : t = R 0 := by
      rw [← hαeq, hα0]
      simp [Real.cos_zero, mul_one]
    linarith [ht.2]
  have hα_lt_pi_div_two : α < Real.pi / 2 := by
    by_contra h
    have hαpi : α = Real.pi / 2 := le_antisymm hα_mem.2 (le_of_not_gt h)
    have : t = 0 := by
      rw [← hαeq, hαpi]
      simp [Real.cos_pi_div_two]
    linarith [ht.1]
  have hR_diff : DifferentiableAt ℝ R α :=
    (hR_cont.differentiableOn (by simp : ((⊤ : ℕ∞) : WithTop ℕ∞) ≠ 0) α hα_mem).differentiableAt
      (Icc_mem_nhds hα_pos hα_lt_pi_div_two)
  have hf_deriv : HasDerivAt (fun α => R α * Real.cos α)
      (deriv R α * Real.cos α - R α * Real.sin α) α := by
    have h := hR_diff.hasDerivAt.mul (Real.hasDerivAt_cos α)
    change HasDerivAt (R * Real.cos) (deriv R α * Real.cos α - R α * Real.sin α) α
    simpa [mul_neg, sub_eq_add_neg] using h
  have hf'_ne : deriv R α * Real.cos α - R α * Real.sin α ≠ 0 := by
    exact ne_of_lt (rightArc_deriv_neg R hη hηsmall hR_cont hR_pos hR_lower hR_deriv_bound
      ⟨hα_pos, hα_lt_pi_div_two⟩)
  have hg_cont : ContinuousAt (rightAlpha R) t :=
    rightAlpha_continuousAt R hη hηsmall hR_cont hR_pos hR_lower hR_deriv_bound ht
  have hfg : ∀ᶠ y in 𝓝 t, (fun α => R α * Real.cos α) (rightAlpha R y) = y := by
    filter_upwards [Icc_mem_nhds ht.1 ht.2] with y hy
    exact (rightAlpha_spec R hη hηsmall hR_cont hR_pos hR_lower hR_deriv_bound hy).2
  have hg_deriv : HasDerivAt (rightAlpha R)
      ((deriv R α * Real.cos α - R α * Real.sin α)⁻¹) t :=
    HasDerivAt.of_local_left_inverse hg_cont hf_deriv hf'_ne hfg
  simpa [α] using hg_deriv.deriv

/-- First derivative of the right-branch profile, by the inverse-graph chain rule. -/
lemma rightProfile_deriv
    (R : ℝ → ℝ) {η : ℝ} (hη : 0 < η) (hηsmall : η < 1 / 8)
    (hR_cont : ContDiffOn ℝ (⊤ : ℕ∞) R (Set.Icc 0 (Real.pi / 2)))
    (hR_pos : ∀ α ∈ Set.Icc 0 (Real.pi / 2), 0 < R α)
    (hR_lower : ∀ α ∈ Set.Icc 0 (Real.pi / 2), 1 - η ≤ R α)
    (hR_deriv_bound : ∀ α ∈ Set.Icc 0 (Real.pi / 2), |deriv R α| ≤ η * α) :
    ∀ t ∈ Set.Ioo 0 (R 0),
      deriv (rightProfile R) t =
        (deriv R (rightAlpha R t) * Real.sin (rightAlpha R t) +
            R (rightAlpha R t) * Real.cos (rightAlpha R t)) /
          (deriv R (rightAlpha R t) * Real.cos (rightAlpha R t) -
            R (rightAlpha R t) * Real.sin (rightAlpha R t)) := by
  intro t ht
  let α := rightAlpha R t
  have ht_mem : t ∈ Set.Icc 0 (R 0) := ⟨le_of_lt ht.1, le_of_lt ht.2⟩
  have hα_spec := rightAlpha_spec R hη hηsmall hR_cont hR_pos hR_lower hR_deriv_bound ht_mem
  have hα_mem : α ∈ Set.Icc 0 (Real.pi / 2) := hα_spec.1
  have hαeq : R α * Real.cos α = t := hα_spec.2
  have hα_pos : 0 < α := by
    by_contra h
    have hα0 : α = 0 := le_antisymm (le_of_not_gt h) hα_mem.1
    have : t = R 0 := by
      rw [← hαeq, hα0]
      simp [Real.cos_zero, mul_one]
    linarith [ht.2]
  have hα_lt_pi_div_two : α < Real.pi / 2 := by
    by_contra h
    have hαpi : α = Real.pi / 2 := le_antisymm hα_mem.2 (le_of_not_gt h)
    have : t = 0 := by
      rw [← hαeq, hαpi]
      simp [Real.cos_pi_div_two]
    linarith [ht.1]
  have hR_diff : DifferentiableAt ℝ R α :=
    (hR_cont.differentiableOn (by simp : ((⊤ : ℕ∞) : WithTop ℕ∞) ≠ 0) α hα_mem).differentiableAt
      (Icc_mem_nhds hα_pos hα_lt_pi_div_two)
  have hf_deriv : HasDerivAt (fun α => R α * Real.cos α)
      (deriv R α * Real.cos α - R α * Real.sin α) α := by
    have h := hR_diff.hasDerivAt.mul (Real.hasDerivAt_cos α)
    change HasDerivAt (R * Real.cos) (deriv R α * Real.cos α - R α * Real.sin α) α
    simpa [mul_neg, sub_eq_add_neg] using h
  have hf'_ne : deriv R α * Real.cos α - R α * Real.sin α ≠ 0 := by
    exact ne_of_lt (rightArc_deriv_neg R hη hηsmall hR_cont hR_pos hR_lower hR_deriv_bound
      ⟨hα_pos, hα_lt_pi_div_two⟩)
  have hg_cont : ContinuousAt (rightAlpha R) t :=
    rightAlpha_continuousAt R hη hηsmall hR_cont hR_pos hR_lower hR_deriv_bound ht
  have hfg : ∀ᶠ y in 𝓝 t, (fun α => R α * Real.cos α) (rightAlpha R y) = y := by
    filter_upwards [Icc_mem_nhds ht.1 ht.2] with y hy
    exact (rightAlpha_spec R hη hηsmall hR_cont hR_pos hR_lower hR_deriv_bound hy).2
  have hg_deriv : HasDerivAt (rightAlpha R)
      ((deriv R α * Real.cos α - R α * Real.sin α)⁻¹) t :=
    HasDerivAt.of_local_left_inverse hg_cont hf_deriv hf'_ne hfg
  have hR_chain : HasDerivAt (fun t => R (rightAlpha R t))
      (deriv R α * (deriv R α * Real.cos α - R α * Real.sin α)⁻¹) t :=
    hR_diff.hasDerivAt.comp t hg_deriv
  have hsin_chain : HasDerivAt (fun t => Real.sin (rightAlpha R t))
      (Real.cos α * (deriv R α * Real.cos α - R α * Real.sin α)⁻¹) t := by
    change HasDerivAt (Real.sin ∘ rightAlpha R)
      (Real.cos α * (deriv R α * Real.cos α - R α * Real.sin α)⁻¹) t
    simpa using (Real.hasDerivAt_sin α).comp t hg_deriv
  have hprod := hR_chain.mul hsin_chain
  have hprod' : HasDerivAt (fun t => R (rightAlpha R t) * Real.sin (rightAlpha R t))
      (deriv R α * (deriv R α * Real.cos α - R α * Real.sin α)⁻¹ * Real.sin α +
        R α * (Real.cos α * (deriv R α * Real.cos α - R α * Real.sin α)⁻¹)) t := by
    change HasDerivAt ((fun t => R (rightAlpha R t)) * fun t => Real.sin (rightAlpha R t))
      (deriv R α * (deriv R α * Real.cos α - R α * Real.sin α)⁻¹ * Real.sin α +
        R α * (Real.cos α * (deriv R α * Real.cos α - R α * Real.sin α)⁻¹)) t
    exact hprod
  have hmain : HasDerivAt (rightProfile R)
      ((deriv R α * Real.sin α + R α * Real.cos α) /
        (deriv R α * Real.cos α - R α * Real.sin α)) t := by
    convert hprod' using 1
    · ext t; rfl
    · rw [div_eq_mul_inv]; ring
  simpa [α] using hmain.deriv

lemma hasDerivAt_deriv_of_contDiffOn
    (R : ℝ → ℝ)
    (hR_cont : ContDiffOn ℝ (⊤ : ℕ∞) R (Set.Icc 0 (Real.pi / 2)))
    {α : ℝ} (hα : α ∈ Set.Ioo 0 (Real.pi / 2)) :
    HasDerivAt (deriv R) (deriv (deriv R) α) α := by
  have hderiv_cont : ContDiffOn ℝ (⊤ : ℕ∞) (deriv R) (Set.Ioo 0 (Real.pi / 2)) :=
    (hR_cont.mono (Set.Ioo_subset_Icc_self)).deriv_of_isOpen isOpen_Ioo (by simp)
  have hderiv_at : ContDiffAt ℝ (⊤ : ℕ∞) (deriv R) α :=
    (contDiffWithinAt_iff_contDiffAt (Ioo_mem_nhds hα.1 hα.2)).1 (hderiv_cont α hα)
  exact (hderiv_at.differentiableAt (by simp : ((⊤ : ℕ∞) : WithTop ℕ∞) ≠ 0)).hasDerivAt

lemma rightArc_N_deriv
    (R : ℝ → ℝ)
    (hR_cont : ContDiffOn ℝ (⊤ : ℕ∞) R (Set.Icc 0 (Real.pi / 2)))
    {α : ℝ} (hα : α ∈ Set.Ioo 0 (Real.pi / 2)) :
    deriv (fun α => deriv R α * Real.sin α + R α * Real.cos α) α =
      deriv (deriv R) α * Real.sin α + 2 * deriv R α * Real.cos α - R α * Real.sin α := by
  have hαIcc : α ∈ Set.Icc 0 (Real.pi / 2) := ⟨le_of_lt hα.1, le_of_lt hα.2⟩
  have hR_diff : DifferentiableAt ℝ R α :=
    (hR_cont.differentiableOn (by simp : ((⊤ : ℕ∞) : WithTop ℕ∞) ≠ 0) α hαIcc).differentiableAt
      (Icc_mem_nhds hα.1 hα.2)
  have hR'_diff : DifferentiableAt ℝ (deriv R) α :=
    (hasDerivAt_deriv_of_contDiffOn R hR_cont hα).differentiableAt
  have h1 : HasDerivAt (fun α => deriv R α * Real.sin α)
      (deriv (deriv R) α * Real.sin α + deriv R α * Real.cos α) α :=
    hR'_diff.hasDerivAt.mul (Real.hasDerivAt_sin α)
  have h2 : HasDerivAt (fun α => R α * Real.cos α)
      (deriv R α * Real.cos α - R α * Real.sin α) α := by
    have h := hR_diff.hasDerivAt.mul (Real.hasDerivAt_cos α)
    change HasDerivAt (R * Real.cos) (deriv R α * Real.cos α - R α * Real.sin α) α
    simpa [mul_neg, sub_eq_add_neg] using h
  have hsum := h1.add h2
  have hsum' : HasDerivAt (fun α => deriv R α * Real.sin α + R α * Real.cos α)
      (deriv (deriv R) α * Real.sin α + deriv R α * Real.cos α +
        (deriv R α * Real.cos α - R α * Real.sin α)) α := by
    change HasDerivAt ((fun α => deriv R α * Real.sin α) + fun α => R α * Real.cos α)
      (deriv (deriv R) α * Real.sin α + deriv R α * Real.cos α +
        (deriv R α * Real.cos α - R α * Real.sin α)) α
    exact hsum
  have hmain : HasDerivAt (fun α => deriv R α * Real.sin α + R α * Real.cos α)
      (deriv (deriv R) α * Real.sin α + 2 * deriv R α * Real.cos α - R α * Real.sin α) α := by
    convert hsum' using 1
    ring
  exact hmain.deriv

lemma rightArc_D_deriv
    (R : ℝ → ℝ)
    (hR_cont : ContDiffOn ℝ (⊤ : ℕ∞) R (Set.Icc 0 (Real.pi / 2)))
    {α : ℝ} (hα : α ∈ Set.Ioo 0 (Real.pi / 2)) :
    deriv (fun α => deriv R α * Real.cos α - R α * Real.sin α) α =
      deriv (deriv R) α * Real.cos α - 2 * deriv R α * Real.sin α - R α * Real.cos α := by
  have hαIcc : α ∈ Set.Icc 0 (Real.pi / 2) := ⟨le_of_lt hα.1, le_of_lt hα.2⟩
  have hR_diff : DifferentiableAt ℝ R α :=
    (hR_cont.differentiableOn (by simp : ((⊤ : ℕ∞) : WithTop ℕ∞) ≠ 0) α hαIcc).differentiableAt
      (Icc_mem_nhds hα.1 hα.2)
  have hR'_diff : DifferentiableAt ℝ (deriv R) α :=
    (hasDerivAt_deriv_of_contDiffOn R hR_cont hα).differentiableAt
  have h1 : HasDerivAt (fun α => deriv R α * Real.cos α)
      (deriv (deriv R) α * Real.cos α - deriv R α * Real.sin α) α := by
    have h := hR'_diff.hasDerivAt.mul (Real.hasDerivAt_cos α)
    change HasDerivAt ((deriv R) * Real.cos)
      (deriv (deriv R) α * Real.cos α - deriv R α * Real.sin α) α
    simpa [mul_neg, sub_eq_add_neg] using h
  have h2 : HasDerivAt (fun α => R α * Real.sin α)
      (deriv R α * Real.sin α + R α * Real.cos α) α :=
    hR_diff.hasDerivAt.mul (Real.hasDerivAt_sin α)
  have hsub := h1.sub h2
  have hsub' : HasDerivAt (fun α => deriv R α * Real.cos α - R α * Real.sin α)
      (deriv (deriv R) α * Real.cos α - deriv R α * Real.sin α -
        (deriv R α * Real.sin α + R α * Real.cos α)) α := by
    change HasDerivAt ((fun α => deriv R α * Real.cos α) - fun α => R α * Real.sin α)
      (deriv (deriv R) α * Real.cos α - deriv R α * Real.sin α -
        (deriv R α * Real.sin α + R α * Real.cos α)) α
    exact hsub
  have hmain : HasDerivAt (fun α => deriv R α * Real.cos α - R α * Real.sin α)
      (deriv (deriv R) α * Real.cos α - 2 * deriv R α * Real.sin α - R α * Real.cos α) α := by
    convert hsub' using 1
    ring
  exact hmain.deriv

lemma rightAlpha_hasDerivAt
    (R : ℝ → ℝ) {η : ℝ} (hη : 0 < η) (hηsmall : η < 1 / 8)
    (hR_cont : ContDiffOn ℝ (⊤ : ℕ∞) R (Set.Icc 0 (Real.pi / 2)))
    (hR_pos : ∀ α ∈ Set.Icc 0 (Real.pi / 2), 0 < R α)
    (hR_lower : ∀ α ∈ Set.Icc 0 (Real.pi / 2), 1 - η ≤ R α)
    (hR_deriv_bound : ∀ α ∈ Set.Icc 0 (Real.pi / 2), |deriv R α| ≤ η * α)
    {t : ℝ} (ht : t ∈ Set.Ioo 0 (R 0)) :
    HasDerivAt (rightAlpha R)
      ((deriv R (rightAlpha R t) * Real.cos (rightAlpha R t) -
        R (rightAlpha R t) * Real.sin (rightAlpha R t))⁻¹) t := by
  let α := rightAlpha R t
  have ht_mem : t ∈ Set.Icc 0 (R 0) := ⟨le_of_lt ht.1, le_of_lt ht.2⟩
  have hα_spec := rightAlpha_spec R hη hηsmall hR_cont hR_pos hR_lower hR_deriv_bound ht_mem
  have hα_mem : α ∈ Set.Icc 0 (Real.pi / 2) := hα_spec.1
  have hαeq : R α * Real.cos α = t := hα_spec.2
  have hα_pos : 0 < α := by
    by_contra h
    have hα0 : α = 0 := le_antisymm (le_of_not_gt h) hα_mem.1
    have : t = R 0 := by
      rw [← hαeq, hα0]
      simp [α, Real.cos_zero, mul_one]
    linarith [ht.2]
  have hα_lt_pi_div_two : α < Real.pi / 2 := by
    by_contra h
    have hαpi : α = Real.pi / 2 := le_antisymm hα_mem.2 (le_of_not_gt h)
    have : t = 0 := by
      rw [← hαeq, hαpi]
      simp [α, Real.cos_pi_div_two]
    linarith [ht.1]
  have hR_diff : DifferentiableAt ℝ R α :=
    (hR_cont.differentiableOn (by simp : ((⊤ : ℕ∞) : WithTop ℕ∞) ≠ 0) α hα_mem).differentiableAt
      (Icc_mem_nhds hα_pos hα_lt_pi_div_two)
  have hf_deriv : HasDerivAt (fun α => R α * Real.cos α)
      (deriv R α * Real.cos α - R α * Real.sin α) α := by
    have h := hR_diff.hasDerivAt.mul (Real.hasDerivAt_cos α)
    change HasDerivAt (R * Real.cos) (deriv R α * Real.cos α - R α * Real.sin α) α
    simpa [mul_neg, sub_eq_add_neg] using h
  have hf'_ne : deriv R α * Real.cos α - R α * Real.sin α ≠ 0 := by
    exact ne_of_lt (rightArc_deriv_neg R hη hηsmall hR_cont hR_pos hR_lower hR_deriv_bound
      ⟨hα_pos, hα_lt_pi_div_two⟩)
  have hg_cont : ContinuousAt (rightAlpha R) t :=
    rightAlpha_continuousAt R hη hηsmall hR_cont hR_pos hR_lower hR_deriv_bound ht
  have hfg : ∀ᶠ y in 𝓝 t, (fun α => R α * Real.cos α) (rightAlpha R y) = y := by
    filter_upwards [Icc_mem_nhds ht.1 ht.2] with y hy
    exact (rightAlpha_spec R hη hηsmall hR_cont hR_pos hR_lower hR_deriv_bound hy).2
  have hg_deriv : HasDerivAt (rightAlpha R)
      ((deriv R α * Real.cos α - R α * Real.sin α)⁻¹) t :=
    HasDerivAt.of_local_left_inverse hg_cont hf_deriv hf'_ne hfg
  simpa [α] using hg_deriv

-- Second derivative of the right-branch profile in terms of `R`, `R'`, `R''`. -/
lemma rightProfile_deriv2
    (R : ℝ → ℝ) {η : ℝ} (hη : 0 < η) (hηsmall : η < 1 / 8)
    (hR_cont : ContDiffOn ℝ (⊤ : ℕ∞) R (Set.Icc 0 (Real.pi / 2)))
    (hR_pos : ∀ α ∈ Set.Icc 0 (Real.pi / 2), 0 < R α)
    (hR_lower : ∀ α ∈ Set.Icc 0 (Real.pi / 2), 1 - η ≤ R α)
    (hR_deriv_bound : ∀ α ∈ Set.Icc 0 (Real.pi / 2), |deriv R α| ≤ η * α) :
    ∀ t ∈ Set.Ioo 0 (R 0),
      deriv (deriv (rightProfile R)) t =
        (R (rightAlpha R t) ^ 2 -
            R (rightAlpha R t) * deriv (deriv R) (rightAlpha R t) +
            2 * (deriv R (rightAlpha R t)) ^ 2) /
          ((deriv R (rightAlpha R t) * Real.cos (rightAlpha R t) -
              R (rightAlpha R t) * Real.sin (rightAlpha R t)) ^ 3) := by
  intro t ht
  let α := rightAlpha R t
  let N : ℝ → ℝ := fun α => deriv R α * Real.sin α + R α * Real.cos α
  let D : ℝ → ℝ := fun α => deriv R α * Real.cos α - R α * Real.sin α
  have ht_mem : t ∈ Set.Icc 0 (R 0) := ⟨le_of_lt ht.1, le_of_lt ht.2⟩
  have hα_spec := rightAlpha_spec R hη hηsmall hR_cont hR_pos hR_lower hR_deriv_bound ht_mem
  have hα_mem : α ∈ Set.Icc 0 (Real.pi / 2) := hα_spec.1
  have hαeq : R α * Real.cos α = t := hα_spec.2
  have hα_pos : 0 < α := by
    by_contra h
    have hα0 : α = 0 := le_antisymm (le_of_not_gt h) hα_mem.1
    have : t = R 0 := by
      rw [← hαeq, hα0]
      simp [α, Real.cos_zero, mul_one]
    linarith [ht.2]
  have hα_lt_pi_div_two : α < Real.pi / 2 := by
    by_contra h
    have hαpi : α = Real.pi / 2 := le_antisymm hα_mem.2 (le_of_not_gt h)
    have : t = 0 := by
      rw [← hαeq, hαpi]
      simp [α, Real.cos_pi_div_two]
    linarith [ht.1]
  have hα_ioo : α ∈ Set.Ioo 0 (Real.pi / 2) := ⟨hα_pos, hα_lt_pi_div_two⟩
  -- differentiability of R and R' at α
  have hR_diff : DifferentiableAt ℝ R α :=
    (hR_cont.differentiableOn (by simp : ((⊤ : ℕ∞) : WithTop ℕ∞) ≠ 0) α hα_mem).differentiableAt
      (Icc_mem_nhds hα_pos hα_lt_pi_div_two)
  have hR'_diff : DifferentiableAt ℝ (deriv R) α :=
    (hasDerivAt_deriv_of_contDiffOn R hR_cont hα_ioo).differentiableAt
  -- derivative of the denominator
  have hD_diff : DifferentiableAt ℝ D α := by
    dsimp [D]
    exact (hR'_diff.mul Real.differentiableAt_cos).sub (hR_diff.mul Real.differentiableAt_sin)
  have hD_has : HasDerivAt D
      (deriv (deriv R) α * Real.cos α - 2 * deriv R α * Real.sin α - R α * Real.cos α) α := by
    have h := hD_diff.hasDerivAt
    change HasDerivAt (fun α => deriv R α * Real.cos α - R α * Real.sin α)
      (deriv (fun α => deriv R α * Real.cos α - R α * Real.sin α) α) α at h
    rw [rightArc_D_deriv R hR_cont hα_ioo] at h
    simpa [D] using h
  have hD_ne : D α ≠ 0 := by
    dsimp [D]
    exact ne_of_lt (rightArc_deriv_neg R hη hηsmall hR_cont hR_pos hR_lower hR_deriv_bound hα_ioo)
  -- derivative of the numerator
  have hN_diff : DifferentiableAt ℝ N α := by
    dsimp [N]
    exact (hR'_diff.mul Real.differentiableAt_sin).add (hR_diff.mul Real.differentiableAt_cos)
  have hN_has : HasDerivAt N
      (deriv (deriv R) α * Real.sin α + 2 * deriv R α * Real.cos α - R α * Real.sin α) α := by
    have h := hN_diff.hasDerivAt
    change HasDerivAt (fun α => deriv R α * Real.sin α + R α * Real.cos α)
      (deriv (fun α => deriv R α * Real.sin α + R α * Real.cos α) α) α at h
    rw [rightArc_N_deriv R hR_cont hα_ioo] at h
    simpa [N] using h
  -- derivative of α at t
  have hα_deriv : HasDerivAt (rightAlpha R) (D α)⁻¹ t := by
    simpa [D] using rightAlpha_hasDerivAt R hη hηsmall hR_cont hR_pos hR_lower hR_deriv_bound ht
  have hN_has' : HasDerivAt N
      (deriv (deriv R) α * Real.sin α + 2 * deriv R α * Real.cos α - R α * Real.sin α)
      (rightAlpha R t) := by simpa [α] using hN_has
  have hD_has' : HasDerivAt D
      (deriv (deriv R) α * Real.cos α - 2 * deriv R α * Real.sin α - R α * Real.cos α)
      (rightAlpha R t) := by simpa [α] using hD_has
  have hN_chain : HasDerivAt (fun t' => N (rightAlpha R t'))
      ((deriv (deriv R) α * Real.sin α + 2 * deriv R α * Real.cos α - R α * Real.sin α) * (D α)⁻¹) t :=
    hN_has'.comp t hα_deriv
  have hD_chain : HasDerivAt (fun t' => D (rightAlpha R t'))
      ((deriv (deriv R) α * Real.cos α - 2 * deriv R α * Real.sin α - R α * Real.cos α) * (D α)⁻¹) t :=
    hD_has'.comp t hα_deriv
  -- derivative of the quotient
  have hquot : HasDerivAt (fun t' => N (rightAlpha R t') / D (rightAlpha R t'))
      ((((deriv (deriv R) α * Real.sin α + 2 * deriv R α * Real.cos α - R α * Real.sin α) * (D α)⁻¹) * D α -
          N α * ((deriv (deriv R) α * Real.cos α - 2 * deriv R α * Real.sin α - R α * Real.cos α) * (D α)⁻¹)) /
        (D α) ^ 2) t :=
    hN_chain.div hD_chain (by simpa [D] using hD_ne)
  -- identify the function with `deriv (rightProfile R)` near t
  have hev : (fun t' => deriv (rightProfile R) t') =ᶠ[𝓝 t]
      (fun t' => N (rightAlpha R t') / D (rightAlpha R t')) := by
    filter_upwards [Ioo_mem_nhds ht.1 ht.2] with t' ht'
    have h := rightProfile_deriv R hη hηsmall hR_cont hR_pos hR_lower hR_deriv_bound t' ht'
    simpa [N, D] using h
  have hderiv_eq : deriv (deriv (rightProfile R)) t =
      deriv (fun t' => N (rightAlpha R t') / D (rightAlpha R t')) t := by
    -- use `Filter.EventuallyEq.deriv_eq`
    have h := hev.deriv_eq
    simpa using h
  -- compute the derivative value
  have hmain : deriv (deriv (rightProfile R)) t =
      (R α ^ 2 - R α * deriv (deriv R) α + 2 * (deriv R α) ^ 2) / (D α) ^ 3 := by
    rw [hderiv_eq]
    -- the derivative of the quotient is `hquot.deriv`
    have hval := hquot.deriv
    -- simplify the quotient derivative expression
    rw [hval]
    field_simp [hD_ne]
    simp only [N, D]
    ring_nf
    linear_combination (-(deriv (deriv R) α * R α) + 2 * deriv R α ^ 2 + R α ^ 2) *
      (Real.sin_sq_add_cos_sq α)
  -- rewrite `D α` and `α` back
  simpa [α, D] using hmain

/-- **Concavity target.**  The glued profile is concave on the full interval.
This is the remaining analytic obligation; it splits at `0` and matches the
one-sided derivatives at the seam using `hRr_end`.  The `C²`-closeness
hypotheses on `R,r` are the quantitative input. -/
lemma profileGlue_concaveOn
    (R r : ℝ → ℝ)
    (hR_cont : ContDiffOn ℝ (⊤ : ℕ∞) R (Set.Icc 0 (Real.pi / 2)))
    (hr_cont : ContDiffOn ℝ (⊤ : ℕ∞) r (Set.Icc 0 (Real.pi / 2)))
    (hR_pos : ∀ α ∈ Set.Icc 0 (Real.pi / 2), 0 < R α)
    (hr_pos : ∀ α ∈ Set.Icc 0 (Real.pi / 2), 0 < r α)
    (hR_closeC2 : ∃ η > 0, ∀ α ∈ Set.Icc 0 (Real.pi / 2),
      |R α - 1| < η ∧ |deriv R α| < η ∧ |deriv (deriv R) α| < η)
    (hr_closeC2 : ∃ η > 0, ∀ α ∈ Set.Icc 0 (Real.pi / 2),
      |r α - 1| < η ∧ |deriv r α| < η ∧ |deriv (deriv r) α| < η)
    (hR_deriv0 : deriv R 0 = 0)
    (hr_deriv0 : deriv r 0 = 0)
    (hRr_end : R (Real.pi / 2) = r (Real.pi / 2)) :
    ConcaveOn ℝ (Set.Icc (-(r 0)) (R 0)) (profileGlue R r) := by
  rcases hR_closeC2 with ⟨ηR, hηR_pos, hηR_bounds⟩
  rcases hr_closeC2 with ⟨ηr, hηr_pos, hηr_bounds⟩
  have hR_lower : ∀ α ∈ Set.Icc 0 (Real.pi / 2), 1 - ηR ≤ R α :=
    radial_lower_bound_C2 hηR_pos (fun α hα => (hηR_bounds α hα).1)
  have hr_lower : ∀ α ∈ Set.Icc 0 (Real.pi / 2), 1 - ηr ≤ r α :=
    radial_lower_bound_C2 hηr_pos (fun α hα => (hηr_bounds α hα).1)
  -- The remaining assembly uses the arc-sign lemmas and the seam glue.
  sorry

/-- **Next target.**  Given radial functions `R,r` close to `1` in `C²`, with
vanishing first derivatives at `0`, the two arcs define a smooth concave
profile on `[-r 0, R 0]`. -/
lemma profile_from_radial_functions
    (R r : ℝ → ℝ)
    (hR_cont : ContDiffOn ℝ (⊤ : ℕ∞) R (Set.Icc 0 (Real.pi / 2)))
    (hr_cont : ContDiffOn ℝ (⊤ : ℕ∞) r (Set.Icc 0 (Real.pi / 2)))
    (hR_pos : ∀ α ∈ Set.Icc 0 (Real.pi / 2), 0 < R α)
    (hr_pos : ∀ α ∈ Set.Icc 0 (Real.pi / 2), 0 < r α)
    (hR_closeC2 : ∃ η > 0, ∀ α ∈ Set.Icc 0 (Real.pi / 2),
      |R α - 1| < η ∧ |deriv R α| < η ∧ |deriv (deriv R) α| < η)
    (hr_closeC2 : ∃ η > 0, ∀ α ∈ Set.Icc 0 (Real.pi / 2),
      |r α - 1| < η ∧ |deriv r α| < η ∧ |deriv (deriv r) α| < η)
    (hR_deriv0 : deriv R 0 = 0)
    (hr_deriv0 : deriv r 0 = 0)
    (hRr_end : R (Real.pi / 2) = r (Real.pi / 2)) :
    ∃ f : ℝ → ℝ,
      Function.support f ⊆ Set.Icc (-(r 0)) (R 0) ∧
      ContDiffOn ℝ (⊤ : ℕ∞) f (Set.Ioo (-(r 0)) (R 0)) ∧
      ConcaveOn ℝ (Set.Icc (-(r 0)) (R 0)) f ∧
      f (-(r 0)) = 0 ∧ f (R 0) = 0 ∧
      (∀ t ∈ Set.Ioo (-(r 0)) (R 0), 0 < f t) ∧
      (∀ α ∈ Set.Icc 0 (Real.pi / 2),
        f (R α * Real.cos α) = R α * Real.sin α) ∧
      (∀ α ∈ Set.Icc 0 (Real.pi / 2),
        f (-(r α * Real.cos α)) = r α * Real.sin α) := by
  sorry

end

end Commons.Geometry.Ulam
