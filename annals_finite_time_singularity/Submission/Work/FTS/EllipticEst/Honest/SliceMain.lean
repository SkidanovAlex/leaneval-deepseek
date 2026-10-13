/-
Copyright: work module for the Elgindi finite-time singularity project.

# The `I₄`/`Ψ̄`-bound of Step 2 of `prop:H2` (honest class)

`Work.FTS.EllipticEst.Honest.step3PsiBar`: under the honest slice hypotheses
(`Ψ` smooth on the *open* quadrant, `Ψ z 0 = Ψ z (π/2) = 0`, and `HkMem 0 0` of `Ψ`,
of `∂_θθΨ` and of `sin θ · ∂_θ(Ψ/cos θ)`), the `σ`-weighted `L²`-norm of
`sin θ · ∂_θ(Ψ/cos θ)` is bounded by the norms of `Ψ` and `∂_θθΨ`
(`σ θ = sin(2θ)^{-η}`, `η = 99/100`; Elgindi, Annals **194** (2021), Step 2 of `prop:H2`,
tex 890--905, the positivity `I_{4,2}`).

## The route

Everything is slicewise: for a fixed `z` put `u θ = Ψ z θ`, `ψ = u / cos θ`,
`σ = sin(2θ)^{-η}`, and let

* `Y = ∫ (sin θ)² (ψ')² σ`,  `X = ∫ (u'')² σ`,  `B = ∫ u² σ`,
* `E = ∫ A(θ) (ψ')² σ` with `A(θ) = ((1-η)/2) cos 2θ + 2 sin²θ = (1-η)/2 + (1+η) sin²θ`,
* `M = ∫ sin θ ψ' u'' σ`,  `C = ∫ cos 2θ ψ² σ`.

The `I₄`-identity (`Work.FTS.EllipticEst.Honest.slice_ident_honest`) reads
`M = ((1-η)/2) · C - E`.  Since `A ≥ sin²θ` we get `Y ≤ E`, and
`C ≤ 2 ∫ u² σ` pointwise (`cos 2θ (a/cos θ)² ≤ 2a²`) together with Cauchy--Schwarz
`-M ≤ √Y √X` gives `Y ≤ (1-η) B + √Y √X`, whence `Y ≤ X + 2B` by `2√Y√X ≤ Y + X`.

Integrating in `z` against `w(z)²` identifies the three terms with
`HkSq 0 0 (sin θ · ∂_θ(Ψ/cos θ))`, `HkSq 0 0 (∂_θθΨ)` and `HkSq 0 0 Ψ`, and
`√(a+2b) ≤ √a + √2 √b ≤ 2(√a + √b)` gives the statement with `C = 2`.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Order.CompletePartialOrder
import Submission.Work.FTS.EllipticEst.Honest.Basic
import Submission.Work.FTS.EllipticEst.Honest.SliceSetup
import Submission.Work.FTS.EllipticEst.AngSecond.abs_setIntegral_le_sqrt_mul_sqrt

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.Honest

set_option autoImplicit false
set_option linter.unusedSimpArgs false

/-- Local abbreviation for the angular weight `σ θ = sin(2θ)^{-η}`
(`Work.FTS.EllipticEst.AngSecond.sig`). -/
local notation "sg" => Work.FTS.EllipticEst.AngSecond.sig

/-- Local abbreviation for the coefficient `A(θ) = ((1-η)/2) cos 2θ + 2 sin²θ`
(`Work.FTS.EllipticEst.AngSecond.acoef`). -/
local notation "acf" => Work.FTS.EllipticEst.AngSecond.acoef

/-! ## Elementary pointwise facts -/

/-- `2 |a b| ≤ a² + b²`. -/
theorem two_mul_abs_mul_le (a b : ℝ) : 2 * |a * b| ≤ a ^ 2 + b ^ 2 := by
  rw [abs_mul]
  nlinarith [sq_nonneg (|a| - |b|), sq_abs a, sq_abs b]

/-- `√(a² σ) = |a| √σ` for `σ ≥ 0`. -/
theorem sqrt_sq_mul_sqrt (a σ : ℝ) (hσ : 0 ≤ σ) :
    Real.sqrt (a ^ 2 * σ) = |a| * Real.sqrt σ := by
  rw [Real.sqrt_mul (sq_nonneg a), Real.sqrt_sq_eq_abs]

/-- `√σ · √σ = σ` for `σ ≥ 0`. -/
theorem sqrt_mul_sqrt_eq (σ : ℝ) (hσ : 0 ≤ σ) : Real.sqrt σ * Real.sqrt σ = σ := by
  rw [← pow_two, Real.sq_sqrt hσ]

/-- `(sin(2θ))^{-η} = (sin(θ * 2))^{-η}`. -/
theorem sin_two_rpow_comm (θ : ℝ) :
    (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
      = (Real.sin (θ * 2)) ^ (-(Work.Spaces.eta)) := by
  rw [mul_comm]

/-- The coefficient `A` dominates `sin²θ`. -/
theorem sin_sq_le_acoef (θ : ℝ) : (Real.sin θ) ^ 2 ≤ acf θ := by
  rw [Work.FTS.EllipticEst.AngSecond.acoef_eq]
  have h1 := Work.Spaces.eta_nonneg
  have h2 := Work.FTS.EllipticEst.AngSecond.one_sub_eta_pos
  nlinarith [sq_nonneg (Real.sin θ)]

/-- On the open quadrant, `cos 2θ · (a / cos θ)² ≤ 2a²`.  (Where `cos 2θ > 0` one has
`cos 2θ ≤ 2 cos²θ`; where `cos 2θ < 0` the left-hand side is negative.) -/
theorem cos2_mul_div_cos_sq_le {a θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    Real.cos (2 * θ) * (a / Real.cos θ) ^ 2 ≤ 2 * a ^ 2 := by
  have hcpos : 0 < Real.cos θ :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [hθ.1, Real.pi_pos], hθ.2⟩
  have hc2 : 0 < Real.cos θ ^ 2 := sq_pos_of_pos hcpos
  have hkey : (2 * Real.cos θ ^ 2 - 1) * (a ^ 2 / Real.cos θ ^ 2)
      = 2 * a ^ 2 - a ^ 2 / Real.cos θ ^ 2 := by
    field_simp
  rw [div_pow, Real.cos_two_mul, hkey]
  have hnn : 0 ≤ a ^ 2 / Real.cos θ ^ 2 := div_nonneg (sq_nonneg a) (le_of_lt hc2)
  linarith

/-! ## Continuity of the slice integrands on the open quadrant -/

/-- `σ` is continuous on the open quadrant. -/
theorem continuousOn_sig : ContinuousOn sg (Set.Ioo 0 (Real.pi / 2)) := by
  show ContinuousOn (fun θ : ℝ => (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
    (Set.Ioo 0 (Real.pi / 2))
  refine ContinuousOn.rpow_const ?_ ?_
  · exact Real.continuous_sin.comp_continuousOn (continuousOn_id.const_mul 2)
  · intro θ hθ
    exact Or.inl (ne_of_gt (Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1])
      (by linarith [hθ.2, Real.pi_pos])))

/-- `(u/cos)'` is continuous on the open quadrant for `u ∈ C²` there. -/
theorem continuousOn_deriv_div_cos {u : ℝ → ℝ}
    (hu : ContDiffOn ℝ 2 u (Set.Ioo 0 (Real.pi / 2))) :
    ContinuousOn (deriv (fun θ => u θ / Real.cos θ)) (Set.Ioo 0 (Real.pi / 2)) := by
  have hcd : ContDiffOn ℝ 2 (fun θ => u θ / Real.cos θ) (Set.Ioo 0 (Real.pi / 2)) :=
    hu.div Real.contDiff_cos.contDiffOn fun θ hθ =>
      ne_of_gt (Real.cos_pos_of_mem_Ioo ⟨by linarith [hθ.1, Real.pi_pos], hθ.2⟩)
  exact hcd.continuousOn_deriv_of_isOpen isOpen_Ioo (by norm_num)

/-- `u''` is continuous on the open quadrant for `u ∈ C²` there. -/
theorem continuousOn_deriv_deriv {u : ℝ → ℝ}
    (hu : ContDiffOn ℝ 2 u (Set.Ioo 0 (Real.pi / 2))) :
    ContinuousOn (deriv (deriv u)) (Set.Ioo 0 (Real.pi / 2)) := by
  have hcd : ContDiffOn ℝ 1 (deriv u) (Set.Ioo 0 (Real.pi / 2)) :=
    hu.deriv_of_isOpen isOpen_Ioo (m := 1) (by norm_num)
  exact hcd.continuousOn_deriv_of_isOpen isOpen_Ioo (by norm_num)

/-! ## From `HkMem` to the slicewise `σ`-weighted integrability -/

/-- **The slicewise integrability of `g² σ` for an honest `g`.**  `Work.Spaces.HkMem 0 0 g`
says that for every `z ∈ Iz` the function `θ ↦ (g z θ · w z / σ θ ^{η/2})²` is integrable on
`Iθ`; since that function equals `(g z θ)² · (w z)² · σ θ` and `w z ≠ 0` for `z > 0`, the
slice `θ ↦ (g z θ)² σ θ` is integrable. -/
theorem integrableOn_sq_mul_sig_of_hkMem {g : ℝ → ℝ → ℝ} (hg : Work.Spaces.HkMem 0 0 g)
    {z : ℝ} (hz : 0 < z) :
    IntegrableOn (fun θ => (g z θ) ^ 2 * sg θ) Work.Spaces.Iθ := by
  have hzI : z ∈ Work.Spaces.Iz := le_of_lt hz
  have h1 : IntegrableOn (fun θ => Work.Spaces.HkIntegrand 0 0 g z θ) Work.Spaces.Iθ :=
    hg.1 z hzI
  have hw : Work.Spaces.w z ^ 2 ≠ 0 := by
    have hpos : 0 < Work.Spaces.w z := by rw [Work.Spaces.w]; positivity
    positivity
  have heq : EqOn (fun θ => Work.Spaces.HkIntegrand 0 0 g z θ)
      (fun θ => Work.Spaces.w z ^ 2 * ((g z θ) ^ 2 * sg θ)) Work.Spaces.Iθ := by
    intro θ hθ
    show Work.Spaces.HkIntegrand 0 0 g z θ = Work.Spaces.w z ^ 2 * ((g z θ) ^ 2 * sg θ)
    rw [HkIntegrand_zero_eq, sq_profile_eq g z θ (sin_two_nonneg_of_mem_Iθ hθ)]
    simp only [Work.FTS.EllipticEst.AngSecond.sig, sin_two_rpow_comm]
    ring
  have h2 : IntegrableOn (fun θ => Work.Spaces.w z ^ 2 * ((g z θ) ^ 2 * sg θ))
      Work.Spaces.Iθ := h1.congr_fun heq measurableSet_Icc
  have h3 : Integrable (fun θ => (g z θ) ^ 2 * sg θ)
      ((volume : Measure ℝ).restrict Work.Spaces.Iθ) :=
    (integrable_const_mul_iff (IsUnit.mk0 (Work.Spaces.w z ^ 2) hw)
      (fun θ => (g z θ) ^ 2 * sg θ)).mp h2
  exact h3

/-! ## The level-`0` `HkSq` as the `z`-integral of the slice integrals -/

/-- At a fixed `z ∈ Iz`, the `θ`-integral of the level-`0` `HkIntegrand` is `w z²` times the
`σ`-weighted `L²`-mass of the slice. -/
theorem hkIntegrand_zero_integral_eq {g : ℝ → ℝ → ℝ} (hg : Work.Spaces.HkMem 0 0 g)
    {z : ℝ} (hz : z ∈ Work.Spaces.Iz) :
    (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand 0 0 g z θ)
      = (Work.Spaces.w z) ^ 2
        * (∫ θ in Set.Ioo 0 (Real.pi / 2), (g z θ) ^ 2 * sg θ) := by
  have hz' : (0 : ℝ) ≤ z := hz
  rcases eq_or_lt_of_le hz' with h | h
  · subst h
    have hw0 : Work.Spaces.w 0 = 0 := by rw [Work.Spaces.w]; norm_num
    have hz0 : (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand 0 0 g 0 θ) = 0 := by
      have hpt : ∀ θ : ℝ, Work.Spaces.HkIntegrand 0 0 g 0 θ = 0 := by
        intro θ
        rw [HkIntegrand_zero_eq, hw0]
        simp
      rw [show (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand 0 0 g 0 θ)
          = ∫ θ in Work.Spaces.Iθ, (0 : ℝ) from
        MeasureTheory.setIntegral_congr_fun measurableSet_Icc (fun θ _ => hpt θ)]
      simp
    rw [hw0, hz0]
    ring
  · have h1 : (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand 0 0 g z θ)
        = ∫ θ in Work.Spaces.Iθ, (g z θ) ^ 2 * (Work.Spaces.w z) ^ 2 * sg θ := by
      refine MeasureTheory.setIntegral_congr_fun measurableSet_Icc fun θ hθ => ?_
      rw [HkIntegrand_zero_eq, sq_profile_eq g z θ (sin_two_nonneg_of_mem_Iθ hθ)]
      simp only [Work.FTS.EllipticEst.AngSecond.sig, sin_two_rpow_comm]
    rw [h1]
    rw [show (fun θ => (g z θ) ^ 2 * (Work.Spaces.w z) ^ 2 * sg θ)
        = (fun θ => (Work.Spaces.w z) ^ 2 * ((g z θ) ^ 2 * sg θ)) from by
      funext θ; ring]
    rw [MeasureTheory.integral_const_mul]
    congr 1
    rw [Work.Spaces.Iθ]
    exact (MeasureTheory.setIntegral_congr_set
      (MeasureTheory.Ioo_ae_eq_Icc (μ := volume) (a := 0) (b := Real.pi / 2))).symm

/-- **`HkSq 0 0 g` as the `w²`-weighted integral of the slicewise `σ`-weighted `L²`-masses.** -/
theorem hkSq_zero_eq_sliceW {g : ℝ → ℝ → ℝ} (hg : Work.Spaces.HkMem 0 0 g) :
    Work.Spaces.HkSq 0 0 g
      = ∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2
          * (∫ θ in Set.Ioo 0 (Real.pi / 2), (g z θ) ^ 2 * sg θ) := by
  rw [Work.Spaces.HkSq]
  exact MeasureTheory.setIntegral_congr_fun measurableSet_Ici fun z hz =>
    hkIntegrand_zero_integral_eq hg hz

/-! ## Slices of a function smooth on the open quadrant -/

/-- The `θ`-slice of a function smooth on the open quadrant is smooth on `(0, π/2)`. -/
theorem contDiffOn_slice_of_hsm {Ψ : ℝ → ℝ → ℝ}
    (hsm : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry Ψ)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)))
    {z : ℝ} (hz : 0 < z) (n : ℕ) :
    ContDiffOn ℝ n (fun θ => Ψ z θ) (Set.Ioo 0 (Real.pi / 2)) := by
  have hcomp : ContDiffOn ℝ n (fun θ : ℝ => (z, θ)) (Set.Ioo 0 (Real.pi / 2)) :=
    contDiffOn_const.prodMk contDiffOn_id
  have h := (hsm n).comp hcomp (fun θ hθ => ⟨hz, hθ⟩)
  simpa [Function.comp_def, Function.uncurry] using h

/-- The iterated angular derivative `∂_θ²` of a fixed slice is the second derivative of the
slice. -/
theorem pthIter_two_apply (Ψ : ℝ → ℝ → ℝ) (z θ : ℝ) :
    Work.Spaces.pthIter 2 Ψ z θ = deriv (deriv (fun θ' => Ψ z θ')) θ := rfl

/-- The `θ`-derivative of `Ψ/cos θ` at `(z,θ)` is the derivative of the slice. -/
theorem pth_div_apply (Ψ : ℝ → ℝ → ℝ) (z θ : ℝ) :
    Work.Spaces.pth (fun z θ => Ψ z θ / Real.cos θ) z θ
      = deriv (fun θ' => Ψ z θ' / Real.cos θ') θ := rfl

/-! ## The quadratic solve: the `I₄`-identity implies the slice estimate -/

/-- **The slicewise estimate, from the `I₄`-identity.**

Given the honest integrability facts on a slice `u` (with `ψ = u/cos`), the identity
`∫ sin θ ψ' u'' σ = ((1-η)/2) ∫ cos 2θ ψ² σ - ∫ A (ψ')² σ` yields
`∫ sin²θ (ψ')² σ ≤ ∫ (u'')² σ + 2 ∫ u² σ`
on that slice, by `A ≥ sin²θ`, the pointwise bound `cos 2θ (u/cos θ)² ≤ 2 u²`, and
Cauchy--Schwarz `-∫ sin θ ψ' u'' σ ≤ √(∫ sin²θ (ψ')² σ) √(∫ (u'')² σ)`. -/
theorem slice_sq_le_of_ident (u : ℝ → ℝ)
    (hu : ContDiffOn ℝ 2 u (Set.Ioo 0 (Real.pi / 2)))
    (hA : IntegrableOn (fun θ => (u θ / Real.cos θ) ^ 2 * sg θ) (Set.Ioo 0 (Real.pi / 2)))
    (hA' : IntegrableOn (fun θ => (deriv (fun θ => u θ / Real.cos θ) θ) ^ 2 * sg θ)
      (Set.Ioo 0 (Real.pi / 2)))
    (hB : IntegrableOn (fun θ => (u θ) ^ 2 * sg θ) (Set.Ioo 0 (Real.pi / 2)))
    (hX : IntegrableOn (fun θ => (deriv (deriv u) θ) ^ 2 * sg θ)
      (Set.Ioo 0 (Real.pi / 2)))
    (hY : IntegrableOn (fun θ => (Real.sin θ) ^ 2
      * (deriv (fun θ => u θ / Real.cos θ) θ) ^ 2 * sg θ) (Set.Ioo 0 (Real.pi / 2)))
    (hident : (∫ θ in Set.Ioo 0 (Real.pi / 2), Real.sin θ
          * deriv (fun θ => u θ / Real.cos θ) θ * deriv (deriv u) θ * sg θ)
      = ((1 - Work.Spaces.eta) / 2) * (∫ θ in Set.Ioo 0 (Real.pi / 2),
            Real.cos (2 * θ) * (u θ / Real.cos θ) ^ 2 * sg θ)
        - ∫ θ in Set.Ioo 0 (Real.pi / 2), acf θ
            * (deriv (fun θ => u θ / Real.cos θ) θ) ^ 2 * sg θ) :
    (∫ θ in Set.Ioo 0 (Real.pi / 2), (Real.sin θ) ^ 2
        * (deriv (fun θ => u θ / Real.cos θ) θ) ^ 2 * sg θ)
      ≤ (∫ θ in Set.Ioo 0 (Real.pi / 2), (deriv (deriv u) θ) ^ 2 * sg θ)
        + 2 * (∫ θ in Set.Ioo 0 (Real.pi / 2), (u θ) ^ 2 * sg θ) := by
  set ys : ℝ := ∫ θ in Set.Ioo 0 (Real.pi / 2), (Real.sin θ) ^ 2
      * (deriv (fun θ => u θ / Real.cos θ) θ) ^ 2 * sg θ with hys
  set xs : ℝ := ∫ θ in Set.Ioo 0 (Real.pi / 2), (deriv (deriv u) θ) ^ 2 * sg θ with hxs
  set bs : ℝ := ∫ θ in Set.Ioo 0 (Real.pi / 2), (u θ) ^ 2 * sg θ with hbs
  set em : ℝ := ∫ θ in Set.Ioo 0 (Real.pi / 2), acf θ
      * (deriv (fun θ => u θ / Real.cos θ) θ) ^ 2 * sg θ with hem
  set c2 : ℝ := ∫ θ in Set.Ioo 0 (Real.pi / 2), Real.cos (2 * θ)
      * (u θ / Real.cos θ) ^ 2 * sg θ with hc2
  set mm : ℝ := ∫ θ in Set.Ioo 0 (Real.pi / 2), Real.sin θ
      * deriv (fun θ => u θ / Real.cos θ) θ * deriv (deriv u) θ * sg θ with hmm
  have hs : MeasurableSet (Set.Ioo 0 (Real.pi / 2)) := measurableSet_Ioo
  have hsub : Set.Ioo 0 (Real.pi / 2) ⊆ Set.Icc 0 (Real.pi / 2) :=
    fun _ hθ => ⟨hθ.1.le, hθ.2.le⟩
  have hsig_nn : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2), 0 ≤ sg θ := fun θ hθ =>
    Work.FTS.EllipticEst.AngSecond.sig_nonneg ⟨hθ.1.le, hθ.2.le⟩
  have hψ'c : ContinuousOn (deriv (fun θ => u θ / Real.cos θ))
      (Set.Ioo 0 (Real.pi / 2)) := continuousOn_deriv_div_cos hu
  have hu''c : ContinuousOn (deriv (deriv u)) (Set.Ioo 0 (Real.pi / 2)) :=
    continuousOn_deriv_deriv hu
  have hsg_c : ContinuousOn sg (Set.Ioo 0 (Real.pi / 2)) := continuousOn_sig
  have hCcont : ContinuousOn (fun θ => Real.sin θ
      * deriv (fun θ => u θ / Real.cos θ) θ * deriv (deriv u) θ * sg θ)
      (Set.Ioo 0 (Real.pi / 2)) := by
    have h1 : ContinuousOn (fun θ : ℝ => Real.sin θ) (Set.Ioo 0 (Real.pi / 2)) := by
      fun_prop
    exact ((h1.mul hψ'c).mul hu''c).mul hsg_c
  -- nonnegativity of the three integrals
  have hys_nn : 0 ≤ ys := by
    rw [hys]
    exact MeasureTheory.setIntegral_nonneg hs fun θ hθ =>
      mul_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _)) (hsig_nn θ hθ)
  have hxs_nn : 0 ≤ xs := by
    rw [hxs]
    exact MeasureTheory.setIntegral_nonneg hs fun θ hθ =>
      mul_nonneg (sq_nonneg _) (hsig_nn θ hθ)
  have hbs_nn : 0 ≤ bs := by
    rw [hbs]
    exact MeasureTheory.setIntegral_nonneg hs fun θ hθ =>
      mul_nonneg (sq_nonneg _) (hsig_nn θ hθ)
  -- (a) `Y ≤ E`
  have hEY : ys ≤ em := by
    rw [hys, hem]
    refine MeasureTheory.setIntegral_mono_on hY ?_ hs fun θ hθ => ?_
    · have hc : ContinuousOn acf (Set.Icc 0 (Real.pi / 2)) := by
        change ContinuousOn (fun θ : ℝ => ((1 - Work.Spaces.eta) / 2) * Real.cos (2 * θ)
          + 2 * (Real.sin θ) ^ 2) (Set.Icc 0 (Real.pi / 2))
        fun_prop
      have h := hA'.mul_continuousOn_of_subset hc hs isCompact_Icc hsub
      refine h.congr_fun (fun θ _ => ?_) hs
      ring
    · have hcoef : (Real.sin θ) ^ 2 ≤ acf θ := sin_sq_le_acoef θ
      calc (Real.sin θ) ^ 2 * (deriv (fun θ => u θ / Real.cos θ) θ) ^ 2 * sg θ
          = (Real.sin θ) ^ 2 * ((deriv (fun θ => u θ / Real.cos θ) θ) ^ 2 * sg θ) := by
            ring
        _ ≤ acf θ * ((deriv (fun θ => u θ / Real.cos θ) θ) ^ 2 * sg θ) :=
            mul_le_mul_of_nonneg_right hcoef (mul_nonneg (sq_nonneg _) (hsig_nn θ hθ))
        _ = acf θ * (deriv (fun θ => u θ / Real.cos θ) θ) ^ 2 * sg θ := by ring
  -- (b) `-M ≤ √Y √X`
  have hMY : -mm ≤ Real.sqrt ys * Real.sqrt xs := by
    have hCint : IntegrableOn (fun θ => Real.sin θ
        * deriv (fun θ => u θ / Real.cos θ) θ * deriv (deriv u) θ * sg θ)
        (Set.Ioo 0 (Real.pi / 2)) := by
      refine MeasureTheory.Integrable.mono'
        (μ := (volume : Measure ℝ).restrict (Set.Ioo 0 (Real.pi / 2))) (hY.add hX)
        (hCcont.aestronglyMeasurable hs) ?_
      filter_upwards [MeasureTheory.ae_restrict_mem hs] with θ hθ
      have hsig : 0 ≤ sg θ := hsig_nn θ hθ
      have h2 := two_mul_abs_mul_le (Real.sin θ * deriv (fun θ => u θ / Real.cos θ) θ)
        (deriv (deriv u) θ)
      rw [mul_pow] at h2
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hsig]
      calc |Real.sin θ * deriv (fun θ => u θ / Real.cos θ) θ * deriv (deriv u) θ| * sg θ
          ≤ ((Real.sin θ) ^ 2 * (deriv (fun θ => u θ / Real.cos θ) θ) ^ 2
              + (deriv (deriv u) θ) ^ 2) * sg θ := by
            have hle : |Real.sin θ * deriv (fun θ => u θ / Real.cos θ) θ
                * deriv (deriv u) θ|
                ≤ (Real.sin θ) ^ 2 * (deriv (fun θ => u θ / Real.cos θ) θ) ^ 2
                  + (deriv (deriv u) θ) ^ 2 := by
              linarith [abs_nonneg (Real.sin θ * deriv (fun θ => u θ / Real.cos θ) θ
                * deriv (deriv u) θ)]
            exact mul_le_mul_of_nonneg_right hle hsig
        _ = (Real.sin θ) ^ 2 * (deriv (fun θ => u θ / Real.cos θ) θ) ^ 2 * sg θ
              + (deriv (deriv u) θ) ^ 2 * sg θ := by ring
    have hdom : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2), |Real.sin θ
        * deriv (fun θ => u θ / Real.cos θ) θ * deriv (deriv u) θ * sg θ|
        ≤ Real.sqrt ((Real.sin θ) ^ 2 * (deriv (fun θ => u θ / Real.cos θ) θ) ^ 2 * sg θ)
          * Real.sqrt ((deriv (deriv u) θ) ^ 2 * sg θ) := by
      intro θ hθ
      have hsig : 0 ≤ sg θ := hsig_nn θ hθ
      have h1 : Real.sqrt ((Real.sin θ) ^ 2
            * (deriv (fun θ => u θ / Real.cos θ) θ) ^ 2 * sg θ)
          = |Real.sin θ * deriv (fun θ => u θ / Real.cos θ) θ| * Real.sqrt (sg θ) := by
        rw [show (Real.sin θ) ^ 2 * (deriv (fun θ => u θ / Real.cos θ) θ) ^ 2 * sg θ
            = (Real.sin θ * deriv (fun θ => u θ / Real.cos θ) θ) ^ 2 * sg θ by ring]
        exact sqrt_sq_mul_sqrt _ _ hsig
      have h2 : Real.sqrt ((deriv (deriv u) θ) ^ 2 * sg θ)
          = |deriv (deriv u) θ| * Real.sqrt (sg θ) := sqrt_sq_mul_sqrt _ _ hsig
      have h3 : |Real.sin θ * deriv (fun θ => u θ / Real.cos θ) θ
            * deriv (deriv u) θ * sg θ|
          = (|Real.sin θ * deriv (fun θ => u θ / Real.cos θ) θ| * |deriv (deriv u) θ|)
            * sg θ := by
        rw [abs_mul, abs_of_nonneg hsig, abs_mul]
      rw [h1, h2, h3]
      have key : (|Real.sin θ * deriv (fun θ => u θ / Real.cos θ) θ| * Real.sqrt (sg θ))
            * (|deriv (deriv u) θ| * Real.sqrt (sg θ))
          = (|Real.sin θ * deriv (fun θ => u θ / Real.cos θ) θ| * |deriv (deriv u) θ|)
            * sg θ := by
        conv_rhs => rw [← sqrt_mul_sqrt_eq (sg θ) hsig]
        ring
      rw [key]
    have hCS := Work.FTS.EllipticEst.AngSecond.abs_setIntegral_le_sqrt_mul_sqrt
      (s := Set.Ioo 0 (Real.pi / 2))
      (A := fun θ => (Real.sin θ) ^ 2 * (deriv (fun θ => u θ / Real.cos θ) θ) ^ 2 * sg θ)
      (B := fun θ => (deriv (deriv u) θ) ^ 2 * sg θ)
      (C := fun θ => Real.sin θ * deriv (fun θ => u θ / Real.cos θ) θ
        * deriv (deriv u) θ * sg θ)
      hY hX hCint
      (fun θ hθ => mul_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _)) (hsig_nn θ hθ))
      (fun θ hθ => mul_nonneg (sq_nonneg _) (hsig_nn θ hθ))
      hdom
    rw [← hmm, ← hys, ← hxs] at hCS
    exact le_trans (neg_le_abs _) hCS
  -- (c) `C ≤ 2 B`
  have hCB : c2 ≤ 2 * bs := by
    rw [hc2, hbs, ← MeasureTheory.integral_const_mul]
    refine MeasureTheory.setIntegral_mono_on ?_ ?_ hs fun θ hθ => ?_
    · have hc : ContinuousOn (fun θ : ℝ => Real.cos (2 * θ)) (Set.Icc 0 (Real.pi / 2)) := by
        fun_prop
      have h := hA.mul_continuousOn_of_subset hc hs isCompact_Icc hsub
      refine h.congr_fun (fun θ _ => ?_) hs
      ring
    · exact hB.const_mul 2
    · have h1 := cos2_mul_div_cos_sq_le (a := u θ) hθ
      have h2 := mul_le_mul_of_nonneg_right h1 (hsig_nn θ hθ)
      calc Real.cos (2 * θ) * (u θ / Real.cos θ) ^ 2 * sg θ ≤ 2 * (u θ) ^ 2 * sg θ := h2
        _ = 2 * ((u θ) ^ 2 * sg θ) := by ring
  -- the identity, in the abbreviations
  have hident' : mm = ((1 - Work.Spaces.eta) / 2) * c2 - em := by
    first
      | exact hident
      | (rw [← hmm, ← hc2, ← hem] at hident; exact hident)
  -- combine
  have hstep : ys ≤ ((1 - Work.Spaces.eta) / 2) * (2 * bs)
      + Real.sqrt ys * Real.sqrt xs := by
    have hcoef : ((1 - Work.Spaces.eta) / 2) * c2 ≤ ((1 - Work.Spaces.eta) / 2) * (2 * bs) :=
      mul_le_mul_of_nonneg_left hCB (by linarith [Work.Spaces.eta_lt_one])
    have hEM : ys ≤ ((1 - Work.Spaces.eta) / 2) * c2 - mm := by linarith [hEY, hident']
    linarith [hEM, hcoef, hMY]
  -- arithmetic
  have hamgm : 2 * (Real.sqrt ys * Real.sqrt xs) ≤ ys + xs := by
    have h1 := Real.sq_sqrt hys_nn
    have h2 := Real.sq_sqrt hxs_nn
    nlinarith [sq_nonneg (Real.sqrt ys - Real.sqrt xs)]
  have hcoef2 : ((1 - Work.Spaces.eta) / 2) * (2 * bs) ≤ bs := by
    have h1 : (1 : ℝ) - Work.Spaces.eta ≤ 1 := by linarith [Work.Spaces.eta_nonneg]
    have h2 : ((1 - Work.Spaces.eta) / 2) * (2 * bs) = (1 - Work.Spaces.eta) * bs := by ring
    rw [h2]
    exact mul_le_of_le_one_left hbs_nn h1
  linarith [hstep, hamgm, hcoef2]

end Work.FTS.EllipticEst.Honest
