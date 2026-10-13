import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Order.CompletePartialOrder

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.EllipticEst.ModalSolution

noncomputable section

/-!
# The angular integration by parts identity, zero form

For the angular operator `L u = -u'' + ∂_θ(tan θ · u) - 6u` (the `α = 0` angular part of the
Biot–Savart operator in Elgindi's coordinates, written against the weight `cos θ`), the pairing
`∫ (f · Lg - Lf · g) cos θ` vanishes whenever `g` is supported away from the two endpoints
`0, π/2`.  Indeed the integrand is exactly the derivative of `-((f g' - f' g) cos θ)`, whose
endpoint values vanish because `g` and `g'` do.

Note: this file carries `open scoped Real` (the workspace sets `autoImplicit = false`), so the
`π` in the statement is the notation for `Real.pi` -- without it the bare `π` is an unknown
identifier and the statement does not even elaborate.

The statement itself is untouched; all the auxiliary material is `private`. -/

/-- The angular integrand `f · (L g) · cos θ - (L f) · g · cos θ`. -/
private def angInt (f g : ℝ → ℝ) (θ : ℝ) : ℝ :=
  (f θ * (-deriv (deriv g) θ + deriv (fun θ' => Real.tan θ' * g θ') θ - 6 * g θ)
    - (-deriv (deriv f) θ + deriv (fun θ' => Real.tan θ' * f θ') θ - 6 * f θ) * g θ)
    * Real.cos θ

/-- The algebraic core: the integrand is `-(d/dθ)((A·P - Q·B) cos θ)` written with the
derivatives of `tan · u` expanded. -/
private theorem key_alg {θ A B P Q R S : ℝ} (hcos : Real.cos θ ≠ 0) :
    -((A * R - S * B) * Real.cos θ + (A * P - Q * B) * (-Real.sin θ))
      = (A * (-R + (1 / Real.cos θ ^ 2 * B + Real.tan θ * P) - 6 * B)
          - (-S + (1 / Real.cos θ ^ 2 * A + Real.tan θ * Q) - 6 * A) * B) * Real.cos θ := by
  rw [Real.tan_eq_sin_div_cos]
  field_simp
  ring

/-- A `C²` function on the open angular interval has continuous second derivative there. -/
private theorem cont_deriv_deriv {u : ℝ → ℝ} (hu : ContDiffOn ℝ 2 u (Set.Ioo 0 (π / 2))) :
    ContinuousOn (deriv (deriv u)) (Set.Ioo 0 (π / 2)) := by
  have hU : UniqueDiffOn ℝ (Set.Ioo (0 : ℝ) (π / 2)) := isOpen_Ioo.uniqueDiffOn
  have h1 : ContDiffOn ℝ 1 (derivWithin u (Set.Ioo (0 : ℝ) (π / 2))) (Set.Ioo (0 : ℝ) (π / 2)) :=
    hu.derivWithin hU (by norm_num)
  have h2 : ContDiffOn ℝ 0 (derivWithin (derivWithin u (Set.Ioo (0 : ℝ) (π / 2)))
      (Set.Ioo (0 : ℝ) (π / 2))) (Set.Ioo (0 : ℝ) (π / 2)) := h1.derivWithin hU (by norm_num)
  refine h2.continuousOn.congr ?_
  intro θ hθ
  rw [derivWithin_of_mem_nhds (isOpen_Ioo.mem_nhds hθ)]
  exact Filter.EventuallyEq.deriv_eq (by
    filter_upwards [isOpen_Ioo.mem_nhds hθ] with y hy
    exact (derivWithin_of_mem_nhds (isOpen_Ioo.mem_nhds hy)).symm)

/-- On the open angular interval, `θ ↦ ∂_θ(tan θ · u θ)` is continuous for `u` of class `C¹`. -/
private theorem cont_deriv_tan_mul {u : ℝ → ℝ} (hu : ContDiffOn ℝ 1 u (Set.Ioo 0 (π / 2))) :
    ContinuousOn (fun θ => deriv (fun θ' => Real.tan θ' * u θ') θ) (Set.Ioo 0 (π / 2)) := by
  have hs : ∀ θ ∈ Set.Ioo (0 : ℝ) (π / 2), Real.cos θ ≠ 0 := fun θ hθ =>
    ne_of_gt (Real.cos_pos_of_mem_Ioo ⟨by linarith [hθ.1, Real.pi_pos],
      by linarith [hθ.2, Real.pi_pos]⟩)
  have htan : ContinuousOn Real.tan (Set.Ioo (0 : ℝ) (π / 2)) :=
    (Real.continuous_sin.continuousOn.div Real.continuous_cos.continuousOn
      (fun θ hθ => hs θ hθ)).congr (fun θ hθ => by
        simp only [Pi.div_apply]; exact Real.tan_eq_sin_div_cos θ)
  have hK : ContinuousOn (fun θ => 1 / Real.cos θ ^ 2 * u θ + Real.tan θ * deriv u θ)
      (Set.Ioo (0 : ℝ) (π / 2)) := by
    apply ContinuousOn.add
    · apply ContinuousOn.mul
      · exact continuousOn_const.div (Real.continuous_cos.continuousOn.pow 2)
          (fun θ hθ => pow_ne_zero 2 (hs θ hθ))
      · exact hu.continuousOn
    · exact htan.mul (hu.continuousOn_deriv_of_isOpen isOpen_Ioo (by norm_num))
  refine hK.congr (fun θ hθ => ?_)
  exact (((Real.hasDerivAt_tan (hs θ hθ)).mul
    (((hu.contDiffAt (isOpen_Ioo.mem_nhds hθ)).differentiableAt one_ne_zero).hasDerivAt))).deriv

/-- The pointwise derivative: the antiderivative `θ ↦ -((f θ · g' θ - f' θ · g θ) cos θ)` has
derivative `angInt f g θ` at every interior point. -/
private theorem hasDerivAt_angInt {f g : ℝ → ℝ}
    (hf : ContDiffOn ℝ 2 f (Set.Ioo 0 (π / 2)))
    (hg : ContDiffOn ℝ 2 g (Set.Ioo 0 (π / 2)))
    {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    HasDerivAt (fun θ : ℝ => -((f θ * deriv g θ - deriv f θ * g θ) * Real.cos θ))
      (angInt f g θ) θ := by
  change HasDerivAt (fun θ : ℝ => -((f θ * deriv g θ - deriv f θ * g θ) * Real.cos θ))
    ((f θ * (-deriv (deriv g) θ + deriv (fun θ' => Real.tan θ' * g θ') θ - 6 * g θ)
      - (-deriv (deriv f) θ + deriv (fun θ' => Real.tan θ' * f θ') θ - 6 * f θ) * g θ)
      * Real.cos θ) θ
  have hcos : Real.cos θ ≠ 0 := ne_of_gt (Real.cos_pos_of_mem_Ioo
    ⟨by linarith [hθ.1, Real.pi_pos], by linarith [hθ.2, Real.pi_pos]⟩)
  have hdf : HasDerivAt f (deriv f θ) θ :=
    ((hf.contDiffAt (isOpen_Ioo.mem_nhds hθ)).differentiableAt two_ne_zero).hasDerivAt
  have hddg : HasDerivAt (deriv g) (deriv (deriv g) θ) θ :=
    (((hg.contDiffAt (isOpen_Ioo.mem_nhds hθ)).derivWithin (m := 1) (by norm_num)).differentiableAt
      one_ne_zero).hasDerivAt
  have hdg : HasDerivAt g (deriv g θ) θ :=
    ((hg.contDiffAt (isOpen_Ioo.mem_nhds hθ)).differentiableAt two_ne_zero).hasDerivAt
  have hddf : HasDerivAt (deriv f) (deriv (deriv f) θ) θ :=
    (((hf.contDiffAt (isOpen_Ioo.mem_nhds hθ)).derivWithin (m := 1) (by norm_num)).differentiableAt
      one_ne_zero).hasDerivAt
  have ht_g : HasDerivAt (fun θ' => Real.tan θ' * g θ')
      (1 / Real.cos θ ^ 2 * g θ + Real.tan θ * deriv g θ) θ :=
    (Real.hasDerivAt_tan hcos).mul hdg
  have ht_f : HasDerivAt (fun θ' => Real.tan θ' * f θ')
      (1 / Real.cos θ ^ 2 * f θ + Real.tan θ * deriv f θ) θ :=
    (Real.hasDerivAt_tan hcos).mul hdf
  have hu : HasDerivAt (fun θ' => f θ' * deriv g θ' - deriv f θ' * g θ')
      (f θ * deriv (deriv g) θ - deriv (deriv f) θ * g θ) θ := by
    refine ((hdf.mul hddg).sub (hddf.mul hdg)).congr_deriv ?_
    ring
  have hF := (hu.mul (Real.hasDerivAt_cos θ)).neg
  rw [ht_g.deriv, ht_f.deriv]
  refine hF.congr_deriv ?_
  exact key_alg hcos

/-- A continuous function which vanishes to the right of `a` vanishes at `a`. -/
private theorem eq_zero_of_cont_of_eventually_gt {u : ℝ → ℝ} {a : ℝ}
    (hcont : ContinuousAt u a) (h : ∀ᶠ x in 𝓝[>] a, u x = 0) : u a = 0 := by
  have h1 : Tendsto u (𝓝[>] a) (𝓝 (u a)) := hcont.tendsto.mono_left nhdsWithin_le_nhds
  have h2 : Tendsto u (𝓝[>] a) (𝓝 0) := tendsto_const_nhds.congr' (h.mono fun x hx => hx.symm)
  exact tendsto_nhds_unique h1 h2

/-- A continuous function which vanishes to the left of `a` vanishes at `a`. -/
private theorem eq_zero_of_cont_of_eventually_lt {u : ℝ → ℝ} {a : ℝ}
    (hcont : ContinuousAt u a) (h : ∀ᶠ x in 𝓝[<] a, u x = 0) : u a = 0 := by
  have h1 : Tendsto u (𝓝[<] a) (𝓝 (u a)) := hcont.tendsto.mono_left nhdsWithin_le_nhds
  have h2 : Tendsto u (𝓝[<] a) (𝓝 0) := tendsto_const_nhds.congr' (h.mono fun x hx => hx.symm)
  exact tendsto_nhds_unique h1 h2

/-- A function differentiable at `a` and vanishing on `(a, ∞)` has vanishing derivative at `a`. -/
private theorem deriv_eq_zero_of_forall_gt {u : ℝ → ℝ} {a : ℝ}
    (hd : HasDerivAt u (deriv u a) a) (h0 : u a = 0) (h : ∀ x, a < x → u x = 0) :
    deriv u a = 0 := by
  have h1 : derivWithin u (Set.Ioi a) a = deriv u a :=
    hd.hasDerivWithinAt.derivWithin (uniqueDiffWithinAt_Ioi a)
  have h2 : derivWithin u (Set.Ioi a) a = 0 := by
    have haux := derivWithin_congr (s := Set.Ioi a) (x := a) (f₁ := u)
      (f := Function.const ℝ (0 : ℝ)) (fun x hx => h x hx) h0
    rw [haux]
    simp
  exact h1.symm.trans h2

/-- A function differentiable at `a` and vanishing on `(-∞, a)` has vanishing derivative at `a`. -/
private theorem deriv_eq_zero_of_forall_lt {u : ℝ → ℝ} {a : ℝ}
    (hd : HasDerivAt u (deriv u a) a) (h0 : u a = 0) (h : ∀ x, x < a → u x = 0) :
    deriv u a = 0 := by
  have h1 : derivWithin u (Set.Iio a) a = deriv u a :=
    hd.hasDerivWithinAt.derivWithin (uniqueDiffWithinAt_Iio a)
  have h2 : derivWithin u (Set.Iio a) a = 0 := by
    have haux := derivWithin_congr (s := Set.Iio a) (x := a) (f₁ := u)
      (f := Function.const ℝ (0 : ℝ)) (fun x hx => h x hx) h0
    rw [haux]
    simp
  exact h1.symm.trans h2

theorem angular_ibp_zero {f g : ℝ → ℝ} {c d : ℝ} (hc : 0 < c) (hcd : c < d) (hd : d < π / 2)
    (hf : ContDiffOn ℝ 2 f (Set.Ioo 0 (π / 2)))
    (hg : ContDiffOn ℝ 2 g (Set.Ioo 0 (π / 2)))
    (hg0 : ∀ θ, θ ∉ Set.Icc c d → g θ = 0) :
    ∫ θ in Set.Icc c d, (f θ * (-deriv (deriv g) θ + deriv (fun θ' => Real.tan θ' * g θ') θ
        - 6 * g θ) - (-deriv (deriv f) θ + deriv (fun θ' => Real.tan θ' * f θ') θ - 6 * f θ) * g θ)
        * Real.cos θ = 0 := by
  change ∫ θ in Set.Icc c d, angInt f g θ = 0
  have hcd' : c ≤ d := hcd.le
  have hsub : Set.Icc c d ⊆ Set.Ioo (0 : ℝ) (π / 2) :=
    fun θ hθ => ⟨lt_of_lt_of_le hc hθ.1, lt_of_le_of_lt hθ.2 hd⟩
  have hsub' : Set.uIcc c d ⊆ Set.Ioo (0 : ℝ) (π / 2) := by
    rw [Set.uIcc_of_le hcd']; exact hsub
  -- the antiderivative `F` of the integrand
  let F : ℝ → ℝ := fun θ => -((f θ * deriv g θ - deriv f θ * g θ) * Real.cos θ)
  have hderiv : ∀ θ ∈ Set.uIcc c d, HasDerivAt F (angInt f g θ) θ :=
    fun θ hθ => hasDerivAt_angInt hf hg (hsub' hθ)
  -- the integrand is continuous on the interval, hence interval integrable
  have hfm : ContinuousOn f (Set.uIcc c d) := hf.continuousOn.mono hsub'
  have hgm : ContinuousOn g (Set.uIcc c d) := hg.continuousOn.mono hsub'
  have hddfm : ContinuousOn (fun θ => deriv (deriv f) θ) (Set.uIcc c d) :=
    (cont_deriv_deriv hf).mono hsub'
  have hddgm : ContinuousOn (fun θ => deriv (deriv g) θ) (Set.uIcc c d) :=
    (cont_deriv_deriv hg).mono hsub'
  have htfm : ContinuousOn (fun θ => deriv (fun θ' => Real.tan θ' * f θ') θ) (Set.uIcc c d) :=
    (cont_deriv_tan_mul (hf.of_le (by norm_num))).mono hsub'
  have htgm : ContinuousOn (fun θ => deriv (fun θ' => Real.tan θ' * g θ') θ) (Set.uIcc c d) :=
    (cont_deriv_tan_mul (hg.of_le (by norm_num))).mono hsub'
  have hcosm : ContinuousOn Real.cos (Set.uIcc c d) := Real.continuous_cos.continuousOn
  have hcont : ContinuousOn (angInt f g) (Set.uIcc c d) := by
    unfold angInt
    fun_prop
  have hint : IntervalIntegrable (angInt f g) volume c d := hcont.intervalIntegrable
  have hFTC : ∫ θ in c..d, angInt f g θ = F d - F c :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
  -- boundary values: `g` and `g'` vanish at both endpoints
  have hc_mem : c ∈ Set.Ioo (0 : ℝ) (π / 2) := ⟨hc, lt_trans hcd hd⟩
  have hd_mem : d ∈ Set.Ioo (0 : ℝ) (π / 2) := ⟨lt_trans hc hcd, hd⟩
  have hg_d : g d = 0 := eq_zero_of_cont_of_eventually_gt
    ((hg.contDiffAt (isOpen_Ioo.mem_nhds hd_mem)).continuousAt) (by
      filter_upwards [self_mem_nhdsWithin] with x hx
      exact hg0 x (fun h => absurd h.2 (not_le.mpr hx)))
  have hdg_d : deriv g d = 0 := deriv_eq_zero_of_forall_gt
    (((hg.contDiffAt (isOpen_Ioo.mem_nhds hd_mem)).differentiableAt two_ne_zero).hasDerivAt) hg_d
    (fun x hx => hg0 x (fun h => absurd h.2 (not_le.mpr hx)))
  have hg_c : g c = 0 := eq_zero_of_cont_of_eventually_lt
    ((hg.contDiffAt (isOpen_Ioo.mem_nhds hc_mem)).continuousAt) (by
      filter_upwards [self_mem_nhdsWithin] with x hx
      exact hg0 x (fun h => absurd h.1 (not_le.mpr hx)))
  have hdg_c : deriv g c = 0 := deriv_eq_zero_of_forall_lt
    (((hg.contDiffAt (isOpen_Ioo.mem_nhds hc_mem)).differentiableAt two_ne_zero).hasDerivAt) hg_c
    (fun x hx => hg0 x (fun h => absurd h.1 (not_le.mpr hx)))
  have hFd : F d = 0 := by
    show -((f d * deriv g d - deriv f d * g d) * Real.cos d) = 0
    rw [hg_d, hdg_d]; ring
  have hFc : F c = 0 := by
    show -((f c * deriv g c - deriv f c * g c) * Real.cos c) = 0
    rw [hg_c, hdg_c]; ring
  have hconv : (∫ θ in Set.Icc c d, angInt f g θ) = ∫ θ in c..d, angInt f g θ := by
    rw [MeasureTheory.integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hcd']
  rw [hconv, hFTC, hFd, hFc]
  ring

end

end Work.EllipticEst.ModalSolution
