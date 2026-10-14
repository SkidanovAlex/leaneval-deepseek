import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.EllipticEst.OpenFTC.absFtcLeIntegralAbsDeriv
import Submission.Work.FTS.EllipticEst.Tools.aesm_Fpair_fts
import Submission.Work.FTS.EllipticEst.integrableOn_Bmom_div
import Submission.Work.FTS.EllipticEst.integrableOn_HkIntegrand_terms
import Submission.Work.FTS.EllipticEst.remov.SmoothOpen_bslOp_of_smoothOpen
import Submission.Work.FTS.LocDataExt.oneSubChi_jet_le5
import Submission.Work.FTS.StrongEps.EComparison.L12_sub_HkMem
import Submission.Work.FTS_EllLimOK.Decay.DecayTools
import Submission.Work.FTS_EllLimOK.LimTower_identify3
import Submission.Work.FTS_RegExport.RXT.Sys.L12FKaux.hasDerivAt_integral_Itheta_K
import Submission.Work.FTS_StreamBdry.Inputs.theta_part_alt_l12fstar
import Submission.Work.GalerkinFix.RegQ.HkMem_mono_Q
import Submission.Work.SolutionDelivery.DatumOdd
import Submission.Work.SolutionDelivery.Scaling.Main
import Submission.Work.Spaces.HProductRule_bad_term
import Submission.Work.Spaces.SmoothCompact_HkMem
import Submission.Work.Spaces.pz_DthIter_mul_eq
-- ===== merged: Submission.Work.FTS.EllipticEst.Final.Step3Helpers =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.Honest

open scoped Real Topology
open MeasureTheory Set Filter


/-- The level-`0` `HkIntegrand` vanishes at `z = 0` (where `w 0 = 0`) and at the two angles
`θ = 0`, `θ = π/2` (where `sin(2θ) = 0`).  Consequently the level-`0` `HkSq` of a function
depends only on its values on the *open* quadrant. -/
theorem HkIntegrand_zero_boundary (α : ℝ) (g : ℝ → ℝ → ℝ) {z θ : ℝ}
    (h : z = 0 ∨ θ = 0 ∨ θ = Real.pi / 2) : Work.Spaces.HkIntegrand α 0 g z θ = 0 := by
  rcases h with h | h | h
  · subst h
    rw [HkIntegrand_zero_eq]
    have hw : Work.Spaces.w 0 = 0 := by norm_num [Work.Spaces.w]
    rw [hw, zero_div, mul_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0)]
  · subst h
    rw [HkIntegrand_zero_eq]
    have h2 : 2 * (0 : ℝ) = 0 := by norm_num
    rw [h2, Real.sin_zero]
    have hz : (0 : ℝ) ^ (Work.Spaces.eta / 2) = 0 := by
      rw [Real.zero_rpow]
      norm_num [Work.Spaces.eta]
    rw [hz, div_zero, mul_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0)]
  · subst h
    rw [HkIntegrand_zero_eq]
    have h2 : 2 * (Real.pi / 2) = Real.pi := by ring
    rw [h2, Real.sin_pi]
    have hz : (0 : ℝ) ^ (Work.Spaces.eta / 2) = 0 := by
      rw [Real.zero_rpow]
      norm_num [Work.Spaces.eta]
    rw [hz, div_zero, mul_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0)]

/-! ## The pointwise identity transported to the integrands -/

/-- The level-`0` integrands of `uOf Ψ` and of `fun z θ => Ψ z θ + POf Ψ z θ` agree on the
domain: at `z = 0` and at `θ ∈ {0, π/2}` both vanish, and on the open quadrant the two
functions are equal by `pth_tan_mul_eq_open`. -/
theorem HkIntegrand_uOf_eq {α : ℝ} {Ψ : ℝ → ℝ → ℝ}
    (hsm : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry Ψ) (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)))
    {z θ : ℝ} (hz : z ∈ Work.Spaces.Iz) (hθ : θ ∈ Work.Spaces.Iθ) :
    Work.Spaces.HkIntegrand α 0 (uOf Ψ) z θ
      = Work.Spaces.HkIntegrand α 0 (fun z θ => Ψ z θ + POf Ψ z θ) z θ := by
  rcases eq_or_lt_of_le (Set.mem_Ici.mp hz) with hz0 | hzpos
  · rw [HkIntegrand_zero_boundary α _ (Or.inl hz0.symm),
      HkIntegrand_zero_boundary α _ (Or.inl hz0.symm)]
  · rcases eq_or_lt_of_le (Set.mem_Icc.mp hθ).1 with hθ0 | hθ0pos
    · rw [HkIntegrand_zero_boundary α _ (Or.inr (Or.inl hθ0.symm)),
        HkIntegrand_zero_boundary α _ (Or.inr (Or.inl hθ0.symm))]
    · rcases eq_or_lt_of_le (Set.mem_Icc.mp hθ).2 with hθπ | hθlt
      · rw [HkIntegrand_zero_boundary α _ (Or.inr (Or.inr hθπ)),
          HkIntegrand_zero_boundary α _ (Or.inr (Or.inr hθπ))]
      · simp only [uOf, POf]
        rw [HkIntegrand_zero_eq, HkIntegrand_zero_eq, pth_tan_mul_eq_open hsm hzpos hθ0pos hθlt]

/-- **`HkSq` of the angular term does not see the difference between `uOf Ψ` and
`Ψ + POf Ψ`.** -/
theorem HkSq_uOf_eq {α : ℝ} {Ψ : ℝ → ℝ → ℝ}
    (hsm : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry Ψ) (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2))) :
    Work.Spaces.HkSq α 0 (uOf Ψ)
      = Work.Spaces.HkSq α 0 (fun z θ => Ψ z θ + POf Ψ z θ) := by
  rw [Work.Spaces.HkSq, Work.Spaces.HkSq]
  refine MeasureTheory.setIntegral_congr_fun measurableSet_Ici fun z hz => ?_
  refine MeasureTheory.setIntegral_congr_fun measurableSet_Icc fun θ hθ => ?_
  exact HkIntegrand_uOf_eq hsm hz hθ

/-- **The `HkSq`-level triangle inequality for the angular term.**  With `HkMem` of `Ψ` and of
`POf Ψ`, the pointwise identity `u = Ψ + P` and `(a + b)² ≤ 2a² + 2b²` give

  `HkSq α 0 (uOf Ψ) ≤ 2 HkSq α 0 Ψ + 2 HkSq α 0 (POf Ψ)`. -/
theorem HkSq_uOf_le {α : ℝ} {Ψ : ℝ → ℝ → ℝ}
    (hsm : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry Ψ) (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)))
    (hΨ : Work.Spaces.HkMem α 0 Ψ) (hP : Work.Spaces.HkMem α 0 (POf Ψ)) :
    Work.Spaces.HkSq α 0 (uOf Ψ)
      ≤ 2 * Work.Spaces.HkSq α 0 Ψ + 2 * Work.Spaces.HkSq α 0 (POf Ψ) := by
  have hpt : ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
      Work.Spaces.HkIntegrand α 0 (fun z θ => Ψ z θ + POf Ψ z θ) z θ
        ≤ 2 * Work.Spaces.HkIntegrand α 0 Ψ z θ
          + 2 * Work.Spaces.HkIntegrand α 0 (POf Ψ) z θ := by
    intro z _ θ _
    rw [HkIntegrand_zero_eq, HkIntegrand_zero_eq, HkIntegrand_zero_eq]
    set W : ℝ := Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)
    have hW : (Ψ z θ + POf Ψ z θ) * W = Ψ z θ * W + POf Ψ z θ * W := by ring
    rw [hW]
    nlinarith [sq_nonneg (Ψ z θ * W - POf Ψ z θ * W)]
  have hle := Work.FTS.EllipticEst.HkSq_add_le_of_pointwise α 0 hΨ hP hpt
  rwa [← HkSq_uOf_eq hsm] at hle

/-- **The square-root triangle inequality for the angular term.** -/
theorem sqrt_HkSq_uOf_le {α : ℝ} {Ψ : ℝ → ℝ → ℝ}
    (hsm : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry Ψ) (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)))
    (hΨ : Work.Spaces.HkMem α 0 Ψ) (hP : Work.Spaces.HkMem α 0 (POf Ψ)) :
    Real.sqrt (Work.Spaces.HkSq α 0 (uOf Ψ))
      ≤ Real.sqrt 2 * (Real.sqrt (Work.Spaces.HkSq α 0 Ψ)
        + Real.sqrt (Work.Spaces.HkSq α 0 (POf Ψ))) := by
  have hle := HkSq_uOf_le hsm hΨ hP
  have hx : 0 ≤ Work.Spaces.HkSq α 0 Ψ := HkSq_zero_nonneg α Ψ
  have hy : 0 ≤ Work.Spaces.HkSq α 0 (POf Ψ) := HkSq_zero_nonneg α _
  have h2 : 0 ≤ Real.sqrt 2 * (Real.sqrt (Work.Spaces.HkSq α 0 Ψ)
      + Real.sqrt (Work.Spaces.HkSq α 0 (POf Ψ))) := by positivity
  rw [Real.sqrt_le_left h2]
  have hsq : (Real.sqrt 2 * (Real.sqrt (Work.Spaces.HkSq α 0 Ψ)
        + Real.sqrt (Work.Spaces.HkSq α 0 (POf Ψ)))) ^ 2
      = 2 * (Real.sqrt (Work.Spaces.HkSq α 0 Ψ)
          + Real.sqrt (Work.Spaces.HkSq α 0 (POf Ψ))) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  rw [hsq]
  have hx1 : Real.sqrt (Work.Spaces.HkSq α 0 Ψ) * Real.sqrt (Work.Spaces.HkSq α 0 Ψ)
      = Work.Spaces.HkSq α 0 Ψ := by rw [← sq, Real.sq_sqrt hx]
  have hy1 : Real.sqrt (Work.Spaces.HkSq α 0 (POf Ψ)) * Real.sqrt (Work.Spaces.HkSq α 0 (POf Ψ))
      = Work.Spaces.HkSq α 0 (POf Ψ) := by rw [← sq, Real.sq_sqrt hy]
  have hxy : 0 ≤ Real.sqrt (Work.Spaces.HkSq α 0 Ψ)
      * Real.sqrt (Work.Spaces.HkSq α 0 (POf Ψ)) :=
    mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  nlinarith [sq_nonneg (Real.sqrt (Work.Spaces.HkSq α 0 Ψ)
      - Real.sqrt (Work.Spaces.HkSq α 0 (POf Ψ))), hx1, hy1, hxy, hle]

/-! ## Honesty of the `I₄`-quantity `P = sin θ · ∂_θ(Ψ/cos θ)`

`Hon α F Ψ` gives `HkMem` only for `F`, `A = z²∂_zzΨ` and `B = ∂_θθΨ`.  The equation
`Hon.eq_solve` together with the pointwise identity `u = Ψ + P` (`POf_eq_of_hon` below)
expresses `P` on the open quadrant as the sum of five honest quantities, so `HkMem α 0 P`
follows from a majorant argument. -/

/-- **`HkMem` is closed under multiplication by a constant** (the level-`0` integrand of
`c · f` is `c²` times the level-`0` integrand of `f`). -/
theorem HkMem_const_mul' {α : ℝ} (c : ℝ) {f : ℝ → ℝ → ℝ} (h : Work.Spaces.HkMem α 0 f) :
    Work.Spaces.HkMem α 0 (fun z θ => c * f z θ) := by
  have hpt : ∀ z θ, Work.Spaces.HkIntegrand α 0 (fun z θ => c * f z θ) z θ
      = c ^ 2 * Work.Spaces.HkIntegrand α 0 f z θ := by
    intro z θ
    rw [HkIntegrand_zero_eq, HkIntegrand_zero_eq]
    ring
  constructor
  · intro z hz
    exact MeasureTheory.IntegrableOn.congr_fun ((h.1 z hz).const_mul (c ^ 2))
      (fun θ _ => (hpt z θ).symm) measurableSet_Icc
  · have h2 : MeasureTheory.IntegrableOn
        (fun z => c ^ 2 * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0 f z θ))
        Work.Spaces.Iz := h.2.const_mul (c ^ 2)
    refine MeasureTheory.IntegrableOn.congr_fun h2 (fun z _ => ?_) measurableSet_Ici
    show c ^ 2 * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0 f z θ)
      = ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0 (fun z θ => c * f z θ) z θ
    rw [← MeasureTheory.integral_const_mul]
    exact (MeasureTheory.setIntegral_congr_fun measurableSet_Icc (fun θ _ => hpt z θ)).symm

/-- **The pointwise decomposition of `P = sin θ · ψ'`, `ψ = Ψ/cos θ`**, on the open quadrant:
`P = α²(z²∂_zzΨ) + α(5+α)(z∂_zΨ) + ∂_θθΨ + F + 5Ψ`. -/
theorem POf_eq_of_hon {α : ℝ} {F Ψ : ℝ → ℝ → ℝ} (h : Hon α F Ψ) {z θ : ℝ}
    (hz : 0 < z) (hθ0 : 0 < θ) (hθ1 : θ < π / 2) :
    POf Ψ z θ = α ^ 2 * AOf Ψ z θ + α * (5 + α) * GOf Ψ z θ
      + Work.Spaces.pthIter 2 Ψ z θ + F z θ + 5 * Ψ z θ := by
  have hsol := h.eq_solve hz hθ0 hθ1
  have hid := pth_tan_mul_eq_open h.sm hz hθ0 hθ1
  simp only [POf, uOf, AOf, GOf] at hid ⊢
  linarith [hsol, hid]

/-- **The five-term Cauchy–Schwarz bound** `(Σ xᵢ)² ≤ 5 Σ xᵢ²`. -/
theorem sum_five_sq_le (x1 x2 x3 x4 x5 : ℝ) :
    (x1 + x2 + x3 + x4 + x5) ^ 2 ≤ 5 * (x1 ^ 2 + x2 ^ 2 + x3 ^ 2 + x4 ^ 2 + x5 ^ 2) := by
  nlinarith [sq_nonneg (x1 - x2), sq_nonneg (x1 - x3), sq_nonneg (x1 - x4), sq_nonneg (x1 - x5),
    sq_nonneg (x2 - x3), sq_nonneg (x2 - x4), sq_nonneg (x2 - x5), sq_nonneg (x3 - x4),
    sq_nonneg (x3 - x5), sq_nonneg (x4 - x5)]

/-- `POf Ψ` is `C^∞` on the open quadrant: it equals `uOf Ψ - Ψ` there by
`pth_tan_mul_eq_open`, and `uOf Ψ = ∂_θ(tan θ · Ψ)` is the `θ`-derivative of a product of
`C^∞` functions. -/
theorem smoothOpen_POf {Ψ : ℝ → ℝ → ℝ}
    (hsm : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry Ψ) (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2))) :
    SmoothOpen (POf Ψ) := by
  have hΨ : SmoothOpen Ψ := Work.FTS.EllipticEst.smoothOpen_of_forall hsm
  have htan : SmoothOpen (fun z θ => Real.tan θ * Ψ z θ) :=
    Work.FTS.EllipticEst.Cert.smoothOpen_mul_bsl (f := fun _ : ℝ => Real.tan) (g := Ψ)
      Work.FTS.EllipticEst.Cert.smoothOpen_tan_bsl hΨ
  have hU : SmoothOpen (uOf Ψ) :=
    show SmoothOpen (Work.Spaces.pth (fun z θ => Real.tan θ * Ψ z θ)) from htan.pth
  refine Work.FTS.EllipticEst.Cert.smoothOpen_congr_bsl
    (Work.FTS.EllipticEst.Cert.smoothOpen_sub_bsl hU hΨ) ?_
  intro z θ hz hθ0 hθ1
  have hid := pth_tan_mul_eq_open hsm hz hθ0 hθ1
  simp only [Pi.sub_apply, uOf, POf]
  linarith [hid]

/-- **The pointwise majorant of the `H⁰`-integrand of `P`** by the sum of the five integrands
coming from the equation.  It holds on the whole domain: at `z = 0` and at the two angles both
sides vanish, and on the open quadrant it is the five-term Cauchy–Schwarz bound applied to
`POf_eq_of_hon`. -/
theorem HkIntegrand_POf_le (α : ℝ) (F Ψ : ℝ → ℝ → ℝ) (h : Hon α F Ψ) (z θ : ℝ)
    (hz : z ∈ Work.Spaces.Iz) (hθ : θ ∈ Work.Spaces.Iθ) :
    Work.Spaces.HkIntegrand α 0 (POf Ψ) z θ
      ≤ 5 * (Work.Spaces.HkIntegrand α 0 (fun z θ => α ^ 2 * AOf Ψ z θ) z θ
        + Work.Spaces.HkIntegrand α 0 (fun z θ => α * (5 + α) * GOf Ψ z θ) z θ
        + Work.Spaces.HkIntegrand α 0 (Work.Spaces.pthIter 2 Ψ) z θ
        + Work.Spaces.HkIntegrand α 0 F z θ
        + Work.Spaces.HkIntegrand α 0 (fun z θ => 5 * Ψ z θ) z θ) := by
  have hnn1 := Work.Spaces.HkIntegrand_nonneg α 0 (fun z θ => α ^ 2 * AOf Ψ z θ) z θ
  have hnn2 := Work.Spaces.HkIntegrand_nonneg α 0 (fun z θ => α * (5 + α) * GOf Ψ z θ) z θ
  have hnn3 := Work.Spaces.HkIntegrand_nonneg α 0 (Work.Spaces.pthIter 2 Ψ) z θ
  have hnn4 := Work.Spaces.HkIntegrand_nonneg α 0 F z θ
  have hnn5 := Work.Spaces.HkIntegrand_nonneg α 0 (fun z θ => 5 * Ψ z θ) z θ
  rcases eq_or_lt_of_le (Set.mem_Ici.mp hz) with hz0 | hzpos
  · rw [HkIntegrand_zero_boundary α _ (Or.inl hz0.symm)]
    nlinarith [hnn1, hnn2, hnn3, hnn4, hnn5]
  · rcases eq_or_lt_of_le (Set.mem_Icc.mp hθ).1 with hθ0 | hθ0pos
    · rw [HkIntegrand_zero_boundary α _ (Or.inr (Or.inl hθ0.symm))]
      nlinarith [hnn1, hnn2, hnn3, hnn4, hnn5]
    · rcases eq_or_lt_of_le (Set.mem_Icc.mp hθ).2 with hθπ | hθlt
      · rw [HkIntegrand_zero_boundary α _ (Or.inr (Or.inr hθπ))]
        nlinarith [hnn1, hnn2, hnn3, hnn4, hnn5]
      · rw [HkIntegrand_zero_eq, HkIntegrand_zero_eq, HkIntegrand_zero_eq, HkIntegrand_zero_eq,
          HkIntegrand_zero_eq, HkIntegrand_zero_eq, POf_eq_of_hon h hzpos hθ0pos hθlt]
        set W : ℝ := Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)
        have hkey := sum_five_sq_le (α ^ 2 * AOf Ψ z θ * W) (α * (5 + α) * GOf Ψ z θ * W)
          (Work.Spaces.pthIter 2 Ψ z θ * W) (F z θ * W) (5 * Ψ z θ * W)
        have hsplit : (α ^ 2 * AOf Ψ z θ + α * (5 + α) * GOf Ψ z θ
              + Work.Spaces.pthIter 2 Ψ z θ + F z θ + 5 * Ψ z θ) * W
            = α ^ 2 * AOf Ψ z θ * W + α * (5 + α) * GOf Ψ z θ * W
              + Work.Spaces.pthIter 2 Ψ z θ * W + F z θ * W + 5 * Ψ z θ * W := by ring
        rw [hsplit]
        linarith [hkey]


end Work.FTS.EllipticEst.Honest
end
-- ===== merged: Submission.Work.FTS.EllipticEst.Honest.step3PsiBoundFree =====
section

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
set_option linter.unusedVariables false

/-- Local abbreviation for the angular weight `σ θ = sin(2θ)^{-η}`
(`Work.FTS.EllipticEst.AngSecond.sig`). -/
local notation "sg" => Work.FTS.EllipticEst.AngSecond.sig

/-! ## The level-`0` objects are independent of `α` -/




/-! ## The `α = 0` slice bound (Elgindi's `I_{4,2}` positivity) -/




/-! ## The target -/


end Work.FTS.EllipticEst.Honest
end
end
-- ===== merged: Submission.Work.FTS.PhiStar.Honesty.CptApp.momentDzZero =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.PhiStar.Honesty.CptApp

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false

/-- **Interval integrability of the divided angular moment.**  For `F` smooth on the open
quadrant with `F ∈ ℋ^k` and `a ≤ k`, the function `r ↦ F_*(D_z^a F)(r)/r` is interval
integrable on `[s,t]` for `0 < s < t`.

This is the local-integrability input of the moment chain
(`H2W.PsiSlices.ae_eq_zero_of_moment_chain`).  It follows from the majorant
`r ↦ ((π/2) ∫_θ HkIntegrand α k F(r,θ) + 1)/2`, which dominates the *undivided* moment and is
integrable on `(0,t)` by `HkMem`; the factor `1/r ≤ 1/s` is bounded on `[s,t]`. -/
private theorem intervalIntegrable_Fstar_DzIter_div {α : ℝ} {k : ℕ} {F : ℝ → ℝ → ℝ}
    (hF : Work.FTS.EllipticEst.SmoothOpen F) (hmem : Work.Spaces.HkMem α k F)
    {a : ℕ} (ha : a ≤ k) {s t : ℝ} (hs : 0 < s) (hst : s < t) :
    IntervalIntegrable (fun r : ℝ => Work.Elliptic.Fstar (Work.Spaces.DzIter a F) r / r)
      MeasureTheory.volume s t := by
  have ht : 0 < t := lt_trans hs hst
  -- ## The majorant is integrable on `(0,z)`, hence the divided moment is
  have hIoo : ∀ z : ℝ, 0 < z → MeasureTheory.IntegrableOn
      (fun r : ℝ => Work.Elliptic.Fstar (Work.Spaces.DzIter a F) r / r) (Set.Ioo 0 z) := by
    intro z hz
    have hmaj : MeasureTheory.IntegrableOn (fun r : ℝ => ((Real.pi / 2) * (∫ θ in Work.Spaces.Iθ,
        Work.Spaces.HkIntegrand α k F r θ) + 1) / 2) (Set.Ioo 0 z) :=
      Work.FTS.EllipticEst.GbarSin.majorant_integrableOn α k F hmem
        (fun r hr => by rw [Work.Spaces.Iz]; exact le_of_lt hr.1)
        (by rw [Real.volume_Ioo]; exact ENNReal.ofReal_ne_top)
    refine hmaj.mono' (Work.FTS.EllipticEst.GbarSin.Fstar_div_aesm F hF a) ?_
    rw [ae_restrict_iff' measurableSet_Ioo]
    refine Eventually.of_forall fun r hr => ?_
    have hr0 : 0 < r := hr.1
    rw [Real.norm_eq_abs, abs_div, abs_of_pos hr0]
    exact Work.FTS.EllipticEst.GbarSin.Fstar_div_le_majorant α k F hF hmem a ha hr0
  -- ## restrict to the interval `(s,t]` and convert to interval integrability
  have hIoc : MeasureTheory.IntegrableOn
      (fun r : ℝ => Work.Elliptic.Fstar (Work.Spaces.DzIter a F) r / r) (Set.Ioc s t) :=
    (hIoo (t + 1) (by linarith)).mono_set
      (fun r hr => ⟨lt_trans hs hr.1, by linarith [hr.2]⟩)
  rw [intervalIntegrable_iff, Set.uIoc_of_le hst.le]
  exact hIoc

/-- **The angular moment of every radial iterate vanishes a.e.**  If `F` is smooth on the open
quadrant, `F ∈ ℋ^k`, and `F_*(F) = 0` on `(0,∞)`, then `F_*(D_z^m F) = 0` a.e. on `(0,∞)` for
every `m ≤ k`. -/
theorem momentDzZero {α : ℝ} {k : ℕ} {F : ℝ → ℝ → ℝ}
    (hsm : Work.FTS.EllipticEst.SmoothOpen F) (hF : Work.Spaces.HkMem α k F)
    (hFs : ∀ z : ℝ, 0 < z → Work.Elliptic.Fstar F z = 0) :
    ∀ m : ℕ, m ≤ k → ∀ᵐ z ∂(MeasureTheory.Measure.restrict MeasureTheory.volume (Set.Ioi 0)),
      MeasureTheory.integral
        (MeasureTheory.Measure.restrict MeasureTheory.volume Work.Spaces.Iθ)
        (fun θ => Work.Spaces.DzIter m F z θ * Work.Elliptic.sinCos2 θ) = 0 := by
  -- ## a.e. vanishing of `F_*(D_z^j F)` for every `j ≤ k`, by induction on `j`
  have hmain : ∀ j : ℕ, j ≤ k →
      ∀ᵐ z ∂(MeasureTheory.Measure.restrict MeasureTheory.volume (Set.Ioi (0 : ℝ))),
        Work.Elliptic.Fstar (Work.Spaces.DzIter j F) z = 0 := by
    intro j
    induction j with
    | zero =>
        intro _
        simpa using (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioi hFs)
    | succ j ih =>
        intro hj
        have hj' : j ≤ k := Nat.le_of_succ_le hj
        -- the integrated chain rule for the angular moment along `D_z`
        have hchain : ∀ s z : ℝ, 0 < s → s ≤ z →
            Work.Elliptic.Fstar (Work.Spaces.DzIter j F) z
              - Work.Elliptic.Fstar (Work.Spaces.DzIter j F) s
            = ∫ r in s..z, Work.Elliptic.Fstar (Work.Spaces.DzIter (j + 1) F) r / r :=
          fun s z hs hsz => Work.FTS.EllipticEst.GbarSin.FstarDzIter_chain_open
            α k F hsm hF j hj hs hsz
        -- the divided moment is interval integrable
        have hInt : ∀ a b : ℝ, 0 < a → a < b →
            IntervalIntegrable
              (fun r : ℝ => Work.Elliptic.Fstar (Work.Spaces.DzIter (j + 1) F) r / r)
              MeasureTheory.volume a b :=
          fun a b ha hab => intervalIntegrable_Fstar_DzIter_div hsm hF hj ha hab
        have hV :=
          Work.FTS.EllipticEst.H2W.PsiSlices.ae_eq_zero_of_moment_chain hchain (ih hj') hInt
        filter_upwards [hV, MeasureTheory.self_mem_ae_restrict measurableSet_Ioi]
          with z hz hzpos
        rw [div_eq_zero_iff] at hz
        rcases hz with h | h
        · exact h
        · exact absurd h (ne_of_gt hzpos)
  intro m hm
  exact hmain m hm

end Work.FTS.PhiStar.Honesty.CptApp
end
