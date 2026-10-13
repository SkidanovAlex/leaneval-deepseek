import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Submission.Work.FTS.EllipticEst.ThetaPoincareDefs
import Submission.Work.Spaces.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.H2W.AeW

/-!
# The angular cot-flux identity for the weight `sin(2θ)^{-η}`

For `f : ℝ → ℝ` of class `C¹` on the open interval `(0, π/2)` and `0 < a < b < π/2`,

  `∫_a^b sin(2θ)^{-(η+2)} f²
    = (1/(4η)) ∫_a^b sin(2θ)^{-η} (f')²
      - (1/2) [ cos(2θ) sin(2θ)^{-(η+1)} f² ]_a^b
      - (1/(4η)) ∫_a^b sin(2θ)^{-η} (f' - 2η cot(2θ) f)²,  η = 99/100.

The identity is the fundamental theorem of calculus for the primitive

  `G θ = -(1/2) cos(2θ) sin(2θ)^{-(η+1)} f(θ)²`

whose derivative is `sin(2θ)^{-(η+2)} f² - K θ`, where

  `K θ = cos(2θ) sin(2θ)^{-(η+1)} f f' - η cos²(2θ) sin(2θ)^{-(η+2)} f²`

is the "flux" integrand; the *difference* of the two integrands of the right-hand side is
the pointwise identity `sin(2θ)^{-η}(f')² - sin(2θ)^{-η}(f' - 2η cot(2θ) f)² = 4η K`
(a difference of two squares), which is why no second derivative of `f` is needed.
-/

/-- `sin (2θ) > 0` for `θ ∈ (0, π/2)`. -/
private theorem sin_two_pos_of_Ioo' {θ : ℝ} (hθ : θ ∈ Set.Ioo (0:ℝ) (Real.pi / 2)) :
    0 < Real.sin (2 * θ) :=
  Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2])

/-- The boundary flux `cos(2θ)·sin(2θ)^{-(η+1)}·f(θ)²`. -/
private def fluxBdry (η : ℝ) (f : ℝ → ℝ) (θ : ℝ) : ℝ :=
  Real.cos (2 * θ) * (Real.sin (2 * θ)) ^ (-(η + 1)) * (f θ) ^ 2

/-- The primitive of the cot-flux identity: `-(1/2) cos(2θ) sin(2θ)^{-(η+1)} f²`. -/
private def fluxPrim (η : ℝ) (f : ℝ → ℝ) : ℝ → ℝ :=
  fun θ => -(1 / 2) * fluxBdry η f θ

/-- The left-hand integrand `sin(2θ)^{-(η+2)} f²`. -/
private def fluxL (η : ℝ) (f : ℝ → ℝ) : ℝ → ℝ :=
  fun θ => (Real.sin (2 * θ)) ^ (-(η + 2)) * (f θ) ^ 2

/-- The first right-hand integrand `sin(2θ)^{-η} (f')²`. -/
private def fluxX (η : ℝ) (f : ℝ → ℝ) : ℝ → ℝ :=
  fun θ => (Real.sin (2 * θ)) ^ (-η) * (deriv f θ) ^ 2

/-- The third right-hand integrand `sin(2θ)^{-η} (f' - 2η cot(2θ) f)²`. -/
private def fluxY (η : ℝ) (f : ℝ → ℝ) : ℝ → ℝ :=
  fun θ => (Real.sin (2 * θ)) ^ (-η) * (deriv f θ - 2 * η * Real.cot (2 * θ) * f θ) ^ 2

/-- The flux integrand `K = cos(2θ) sin(2θ)^{-(η+1)} f f' - η cos²(2θ) sin(2θ)^{-(η+2)} f²`. -/
private def fluxK (η : ℝ) (f : ℝ → ℝ) : ℝ → ℝ :=
  fun θ => Real.cos (2 * θ) * (Real.sin (2 * θ)) ^ (-(η + 1)) * f θ * deriv f θ
    - η * (Real.cos (2 * θ)) ^ 2 * (Real.sin (2 * θ)) ^ (-(η + 2)) * (f θ) ^ 2

/-- Derivative of `cos(2θ)·sin(2θ)^{-(η+1)}` at an interior point. -/
private theorem hasDerivAt_cos_mul_sin_rpow (η : ℝ) {θ : ℝ}
    (hθ : θ ∈ Set.Ioo (0:ℝ) (Real.pi / 2)) :
    HasDerivAt (fun t : ℝ => Real.cos (2 * t) * (Real.sin (2 * t)) ^ (-(η + 1)))
      (-2 * (Real.sin (2 * θ)) ^ (-η)
        - 2 * (η + 1) * (Real.cos (2 * θ)) ^ 2 * (Real.sin (2 * θ)) ^ (-(η + 2))) θ := by
  have hsp : 0 < Real.sin (2 * θ) := sin_two_pos_of_Ioo' hθ
  have h2 : HasDerivAt (fun t : ℝ => 2 * t) 2 θ := by
    simpa using (hasDerivAt_id θ).const_mul (2 : ℝ)
  have hsin : HasDerivAt (fun t : ℝ => Real.sin (2 * t)) (2 * Real.cos (2 * θ)) θ := by
    have hh := (Real.hasDerivAt_sin (2 * θ)).comp θ h2
    have heq : Real.cos (2 * θ) * 2 = 2 * Real.cos (2 * θ) := by ring
    rwa [heq] at hh
  have hcos : HasDerivAt (fun t : ℝ => Real.cos (2 * t)) (-2 * Real.sin (2 * θ)) θ := by
    have hh := (Real.hasDerivAt_cos (2 * θ)).comp θ h2
    have heq : -Real.sin (2 * θ) * 2 = -2 * Real.sin (2 * θ) := by ring
    rwa [heq] at hh
  have hrpow : HasDerivAt (fun t : ℝ => (Real.sin (2 * t)) ^ (-(η + 1)))
      ((2 * Real.cos (2 * θ)) * (-(η + 1)) * (Real.sin (2 * θ)) ^ (-(η + 1) - 1)) θ :=
    hsin.rpow_const (Or.inl (ne_of_gt hsp))
  have hmul := hcos.mul hrpow
  have hval : (-2 * Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (-(η + 1))
      + Real.cos (2 * θ)
          * ((2 * Real.cos (2 * θ)) * (-(η + 1)) * (Real.sin (2 * θ)) ^ (-(η + 1) - 1))
      = -2 * (Real.sin (2 * θ)) ^ (-η)
        - 2 * (η + 1) * (Real.cos (2 * θ)) ^ 2 * (Real.sin (2 * θ)) ^ (-(η + 2)) := by
    have h1 : Real.sin (2 * θ) * (Real.sin (2 * θ)) ^ (-(η + 1))
        = (Real.sin (2 * θ)) ^ (-η) := by
      have h := Real.rpow_add hsp (1:ℝ) (-(η + 1))
      rw [show (1:ℝ) + -(η + 1) = -η by ring, Real.rpow_one] at h
      exact h.symm
    rw [show -(η + 1) - 1 = -(η + 2) by ring]
    linear_combination (-2) * h1
  rw [hval] at hmul
  exact hmul

/-- The derivative of the primitive `fluxPrim`, written as `fluxL - fluxK`. -/
private theorem hasDerivAt_fluxPrim (η : ℝ) {f : ℝ → ℝ} {θ : ℝ}
    (hθ : θ ∈ Set.Ioo (0:ℝ) (Real.pi / 2)) (hd : HasDerivAt f (deriv f θ) θ) :
    HasDerivAt (fluxPrim η f) (fluxL η f θ - fluxK η f θ) θ := by
  have hsp : 0 < Real.sin (2 * θ) := sin_two_pos_of_Ioo' hθ
  have hP := hasDerivAt_cos_mul_sin_rpow η hθ
  have hsq : HasDerivAt (fun t : ℝ => (f t) ^ 2) (2 * f θ ^ (2 - 1) * deriv f θ) θ := hd.pow 2
  have hmul : HasDerivAt (fun t : ℝ => (Real.cos (2 * t) * (Real.sin (2 * t)) ^ (-(η + 1))) * (f t) ^ 2)
      ((-2 * (Real.sin (2 * θ)) ^ (-η)
          - 2 * (η + 1) * (Real.cos (2 * θ)) ^ 2 * (Real.sin (2 * θ)) ^ (-(η + 2))) * (f θ) ^ 2
        + (Real.cos (2 * θ) * (Real.sin (2 * θ)) ^ (-(η + 1))) * (2 * f θ ^ (2 - 1) * deriv f θ)) θ :=
    hP.mul hsq
  have hkey : -(1 / 2) * ((-2 * (Real.sin (2 * θ)) ^ (-η)
        - 2 * (η + 1) * (Real.cos (2 * θ)) ^ 2 * (Real.sin (2 * θ)) ^ (-(η + 2))) * (f θ) ^ 2
      + (Real.cos (2 * θ) * (Real.sin (2 * θ)) ^ (-(η + 1))) * (2 * f θ ^ (2 - 1) * deriv f θ))
      = fluxL η f θ - fluxK η f θ := by
    have hS1 : (Real.sin (2 * θ)) ^ (-(η + 2)) * (Real.sin (2 * θ)) ^ 2
        = (Real.sin (2 * θ)) ^ (-η) := by
      have h := Real.rpow_add hsp (-(η + 2)) (2:ℝ)
      rw [show -(η + 2) + 2 = -η by ring, Real.rpow_two] at h
      exact h.symm
    simp only [fluxL, fluxK]
    rw [show (2:ℕ) - 1 = 1 from rfl, pow_one]
    rw [← hS1]
    linear_combination ((Real.sin (2 * θ)) ^ (-(η + 2)) * (f θ) ^ 2) * Real.sin_sq_add_cos_sq (2 * θ)
  have hmain : HasDerivAt (fun t : ℝ => -(1 / 2) * ((Real.cos (2 * t) * (Real.sin (2 * t)) ^ (-(η + 1))) * (f t) ^ 2))
      (-(1 / 2) * ((-2 * (Real.sin (2 * θ)) ^ (-η)
        - 2 * (η + 1) * (Real.cos (2 * θ)) ^ 2 * (Real.sin (2 * θ)) ^ (-(η + 2))) * (f θ) ^ 2
      + (Real.cos (2 * θ) * (Real.sin (2 * θ)) ^ (-(η + 1))) * (2 * f θ ^ (2 - 1) * deriv f θ))) θ :=
    hmul.const_mul (-(1 / 2))
  rw [hkey] at hmain
  exact hmain

/-- The difference of squares identity: `fluxX - fluxY = 4η · fluxK`. -/
private theorem diff_squares_eq (η : ℝ) {f : ℝ → ℝ} {θ : ℝ}
    (hθ : θ ∈ Set.Ioo (0:ℝ) (Real.pi / 2)) :
    fluxX η f θ - fluxY η f θ = 4 * η * fluxK η f θ := by
  have hsp : 0 < Real.sin (2 * θ) := sin_two_pos_of_Ioo' hθ
  have hS1 : (Real.sin (2 * θ)) ^ (-η)
      = (Real.sin (2 * θ)) ^ (-(η + 2)) * (Real.sin (2 * θ)) ^ 2 := by
    have h := Real.rpow_add hsp (-(η + 2)) (2:ℝ)
    rw [show -(η + 2) + 2 = -η by ring, Real.rpow_two] at h
    exact h
  have hS2 : (Real.sin (2 * θ)) ^ (-(η + 1))
      = (Real.sin (2 * θ)) ^ (-(η + 2)) * Real.sin (2 * θ) := by
    have h := Real.rpow_add hsp (-(η + 2)) (1:ℝ)
    rw [show -(η + 2) + 1 = -(η + 1) by ring, Real.rpow_one] at h
    exact h
  simp only [fluxX, fluxY, fluxK]
  rw [Real.cot_eq_cos_div_sin, hS1, hS2]
  field_simp
  ring

/-- Continuity of the flux integrand on the closed interval. -/
private theorem continuousOn_fluxK (f : ℝ → ℝ) {a b : ℝ}
    (hcf : ContinuousOn f (Set.uIcc a b)) (hcd : ContinuousOn (deriv f) (Set.uIcc a b))
    (hcsin : ContinuousOn (fun x : ℝ => Real.sin (2 * x)) (Set.uIcc a b))
    (hccos : ContinuousOn (fun x : ℝ => Real.cos (2 * x)) (Set.uIcc a b))
    (hsp : ∀ x ∈ Set.uIcc a b, 0 < Real.sin (2 * x)) :
    ContinuousOn (fluxK Work.Spaces.eta f) (Set.uIcc a b) := by
  have hpw1 : ContinuousOn (fun x : ℝ => (Real.sin (2 * x)) ^ (-(Work.Spaces.eta + 1))) (Set.uIcc a b) :=
    hcsin.rpow_const (fun x hx => Or.inl (ne_of_gt (hsp x hx)))
  have hpw2 : ContinuousOn (fun x : ℝ => (Real.sin (2 * x)) ^ (-(Work.Spaces.eta + 2))) (Set.uIcc a b) :=
    hcsin.rpow_const (fun x hx => Or.inl (ne_of_gt (hsp x hx)))
  have h1K : ContinuousOn (fun x : ℝ => Real.cos (2 * x) * (Real.sin (2 * x)) ^ (-(Work.Spaces.eta + 1)) * f x * deriv f x) (Set.uIcc a b) :=
    ((hccos.mul hpw1).mul hcf).mul hcd
  have h2K : ContinuousOn (fun x : ℝ => Work.Spaces.eta * (Real.cos (2 * x)) ^ 2 * (Real.sin (2 * x)) ^ (-(Work.Spaces.eta + 2)) * (f x) ^ 2) (Set.uIcc a b) :=
    (((continuous_const.continuousOn.mul (hccos.pow 2)).mul hpw2).mul (hcf.pow 2))
  unfold fluxK
  exact h1K.sub h2K

/-- **The cot-flux identity.** For `f` of class `C¹` on `(0, π/2)` and `0 < a < b < π/2`,
`∫_a^b sin(2θ)^{-(η+2)} f² = (1/(4η)) ∫_a^b sin(2θ)^{-η}(f')²
  - (1/2)[cos(2θ) sin(2θ)^{-(η+1)} f²]_a^b
  - (1/(4η)) ∫_a^b sin(2θ)^{-η}(f' - 2η cot(2θ) f)²`, where `η = 99/100`. -/
theorem cotFluxIdentity {f : ℝ → ℝ} (hf : ContDiffOn ℝ 1 f (Set.Ioo 0 (Real.pi / 2)))
    {a b : ℝ} (ha : 0 < a) (hab : a < b) (hb : b < Real.pi / 2) :
    (∫ θ in a..b, (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta + 2)) * (f θ) ^ 2)
      = (1 / (4 * Work.Spaces.eta)) * (∫ θ in a..b, Work.FTS.EllipticEst.thEta θ * (deriv f θ) ^ 2)
        - (1 / 2) * (Real.cos (2 * b) * (Real.sin (2 * b)) ^ (-(Work.Spaces.eta + 1)) * (f b) ^ 2
            - Real.cos (2 * a) * (Real.sin (2 * a)) ^ (-(Work.Spaces.eta + 1)) * (f a) ^ 2)
        - (1 / (4 * Work.Spaces.eta)) * (∫ θ in a..b, Work.FTS.EllipticEst.thEta θ
            * (deriv f θ - 2 * Work.Spaces.eta * Real.cot (2 * θ) * f θ) ^ 2) := by
  show (∫ θ in a..b, fluxL Work.Spaces.eta f θ)
      = (1 / (4 * Work.Spaces.eta)) * (∫ θ in a..b, fluxX Work.Spaces.eta f θ)
        - (1 / 2) * (fluxBdry Work.Spaces.eta f b - fluxBdry Work.Spaces.eta f a)
        - (1 / (4 * Work.Spaces.eta)) * (∫ θ in a..b, fluxY Work.Spaces.eta f θ)
  have hηpos : (0:ℝ) < Work.Spaces.eta := Work.Spaces.eta_pos
  have hmem : ∀ x ∈ Set.uIcc a b, x ∈ Set.Ioo (0:ℝ) (Real.pi / 2) := by
    intro x hx
    have hx' : a ≤ x ∧ x ≤ b := by
      rw [Set.uIcc_of_le hab.le] at hx
      exact hx
    exact ⟨by linarith [hx'.1], by linarith [hx'.2]⟩
  have hsp : ∀ x ∈ Set.uIcc a b, 0 < Real.sin (2 * x) := fun x hx => sin_two_pos_of_Ioo' (hmem x hx)
  have hcf : ContinuousOn f (Set.uIcc a b) := hf.continuousOn.mono hmem
  have hcd : ContinuousOn (deriv f) (Set.uIcc a b) :=
    (hf.continuousOn_deriv_of_isOpen isOpen_Ioo le_rfl).mono hmem
  have hcsin : ContinuousOn (fun x : ℝ => Real.sin (2 * x)) (Set.uIcc a b) := by fun_prop
  have hccos : ContinuousOn (fun x : ℝ => Real.cos (2 * x)) (Set.uIcc a b) := by fun_prop
  have hpw0 : ContinuousOn (fun x : ℝ => (Real.sin (2 * x)) ^ (-(Work.Spaces.eta))) (Set.uIcc a b) :=
    hcsin.rpow_const (fun x hx => Or.inl (ne_of_gt (hsp x hx)))
  have hpw1 : ContinuousOn (fun x : ℝ => (Real.sin (2 * x)) ^ (-(Work.Spaces.eta + 1))) (Set.uIcc a b) :=
    hcsin.rpow_const (fun x hx => Or.inl (ne_of_gt (hsp x hx)))
  have hpw2 : ContinuousOn (fun x : ℝ => (Real.sin (2 * x)) ^ (-(Work.Spaces.eta + 2))) (Set.uIcc a b) :=
    hcsin.rpow_const (fun x hx => Or.inl (ne_of_gt (hsp x hx)))
  have hXcont : ContinuousOn (fluxX Work.Spaces.eta f) (Set.uIcc a b) := by
    unfold fluxX
    exact hpw0.mul (hcd.pow 2)
  have hcoth : ContinuousOn (fun x : ℝ => Real.cot (2 * x)) (Set.uIcc a b) := by
    have h := hccos.div hcsin (fun x hx => ne_of_gt (hsp x hx))
    have heq : (fun x : ℝ => Real.cot (2 * x))
        = ((fun x : ℝ => Real.cos (2 * x)) / fun x => Real.sin (2 * x)) := by
      funext x
      exact Real.cot_eq_cos_div_sin (2 * x)
    rw [heq]
    exact h
  have hsub : ContinuousOn (fun x : ℝ => deriv f x - 2 * Work.Spaces.eta * Real.cot (2 * x) * f x) (Set.uIcc a b) := by
    refine hcd.sub ?_
    have h0 := (hcoth.mul hcf).const_mul (2 * Work.Spaces.eta)
    simpa only [Pi.mul_apply, mul_assoc] using h0
  have hYcont : ContinuousOn (fluxY Work.Spaces.eta f) (Set.uIcc a b) := by
    unfold fluxY
    exact hpw0.mul (hsub.pow 2)
  have hKcont : ContinuousOn (fluxK Work.Spaces.eta f) (Set.uIcc a b) :=
    continuousOn_fluxK f hcf hcd hcsin hccos hsp
  have hLcont : ContinuousOn (fluxL Work.Spaces.eta f) (Set.uIcc a b) := by
    unfold fluxL
    exact hpw2.mul (hcf.pow 2)
  have hXint : IntervalIntegrable (fluxX Work.Spaces.eta f) volume a b :=
    ContinuousOn.intervalIntegrable hXcont
  have hYint : IntervalIntegrable (fluxY Work.Spaces.eta f) volume a b :=
    ContinuousOn.intervalIntegrable hYcont
  have hKint : IntervalIntegrable (fluxK Work.Spaces.eta f) volume a b :=
    ContinuousOn.intervalIntegrable hKcont
  have hLKcont : ContinuousOn (fun x => fluxL Work.Spaces.eta f x - fluxK Work.Spaces.eta f x) (Set.uIcc a b) :=
    hLcont.sub hKcont
  have hLKint : IntervalIntegrable (fun x => fluxL Work.Spaces.eta f x - fluxK Work.Spaces.eta f x) volume a b :=
    ContinuousOn.intervalIntegrable hLKcont
  have hder : ∀ x ∈ Set.uIcc a b, HasDerivAt (fluxPrim Work.Spaces.eta f)
      ((fun x => fluxL Work.Spaces.eta f x - fluxK Work.Spaces.eta f x) x) x := by
    intro x hx
    have hd : HasDerivAt f (deriv f x) x :=
      ((hf.differentiableOn (by norm_num)).differentiableAt
        (isOpen_Ioo.mem_nhds (hmem x hx))).hasDerivAt
    exact hasDerivAt_fluxPrim Work.Spaces.eta (hmem x hx) hd
  have hftc : ∫ x in a..b, (fluxL Work.Spaces.eta f x - fluxK Work.Spaces.eta f x)
      = fluxPrim Work.Spaces.eta f b - fluxPrim Work.Spaces.eta f a :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt hder hLKint
  have hLdecomp : ∫ x in a..b, fluxL Work.Spaces.eta f x
      = (∫ x in a..b, fluxK Work.Spaces.eta f x)
        + ∫ x in a..b, (fluxL Work.Spaces.eta f x - fluxK Work.Spaces.eta f x) := by
    rw [← intervalIntegral.integral_add hKint hLKint]
    exact intervalIntegral.integral_congr (fun x hx => by ring)
  have hXYsplit : (∫ x in a..b, fluxX Work.Spaces.eta f x) - (∫ x in a..b, fluxY Work.Spaces.eta f x)
      = ∫ x in a..b, fluxX Work.Spaces.eta f x - fluxY Work.Spaces.eta f x :=
    (intervalIntegral.integral_sub hXint hYint).symm
  have hXYcongr : (∫ x in a..b, fluxX Work.Spaces.eta f x - fluxY Work.Spaces.eta f x)
      = ∫ x in a..b, 4 * Work.Spaces.eta * fluxK Work.Spaces.eta f x :=
    intervalIntegral.integral_congr (fun x hx => diff_squares_eq Work.Spaces.eta (hmem x hx))
  have h4 : (∫ x in a..b, 4 * Work.Spaces.eta * fluxK Work.Spaces.eta f x)
      = 4 * Work.Spaces.eta * (∫ x in a..b, fluxK Work.Spaces.eta f x) :=
    intervalIntegral.integral_const_mul _ _
  have hXY : (∫ x in a..b, fluxX Work.Spaces.eta f x) - (∫ x in a..b, fluxY Work.Spaces.eta f x)
      = 4 * Work.Spaces.eta * (∫ x in a..b, fluxK Work.Spaces.eta f x) :=
    hXYsplit.trans (hXYcongr.trans h4)
  have hGval : fluxPrim Work.Spaces.eta f b - fluxPrim Work.Spaces.eta f a
      = -(1 / 2) * (fluxBdry Work.Spaces.eta f b - fluxBdry Work.Spaces.eta f a) := by
    simp only [fluxPrim, fluxBdry]; ring
  have hkey : (1 / (4 * Work.Spaces.eta)) * (∫ x in a..b, fluxX Work.Spaces.eta f x)
        - (1 / 2) * (fluxBdry Work.Spaces.eta f b - fluxBdry Work.Spaces.eta f a)
        - (1 / (4 * Work.Spaces.eta)) * (∫ x in a..b, fluxY Work.Spaces.eta f x)
      = (∫ x in a..b, fluxK Work.Spaces.eta f x)
        + (fluxPrim Work.Spaces.eta f b - fluxPrim Work.Spaces.eta f a) := by
    have h4η : (1 / (4 * Work.Spaces.eta)) * (4 * Work.Spaces.eta * (∫ x in a..b, fluxK Work.Spaces.eta f x))
        = ∫ x in a..b, fluxK Work.Spaces.eta f x := by
      have hne : (4 * Work.Spaces.eta) ≠ 0 := by positivity
      rw [one_div, inv_mul_eq_iff_eq_mul₀ hne, mul_assoc]
    rw [show (1 / (4 * Work.Spaces.eta)) * (∫ x in a..b, fluxX Work.Spaces.eta f x)
          - (1 / 2) * (fluxBdry Work.Spaces.eta f b - fluxBdry Work.Spaces.eta f a)
          - (1 / (4 * Work.Spaces.eta)) * (∫ x in a..b, fluxY Work.Spaces.eta f x)
        = (1 / (4 * Work.Spaces.eta)) * ((∫ x in a..b, fluxX Work.Spaces.eta f x)
            - (∫ x in a..b, fluxY Work.Spaces.eta f x))
          - (1 / 2) * (fluxBdry Work.Spaces.eta f b - fluxBdry Work.Spaces.eta f a) by ring,
      hXY, h4η, hGval]
    ring
  rw [hkey, ← hftc, ← hLdecomp]

end Work.FTS.EllipticEst.H2W.AeW
