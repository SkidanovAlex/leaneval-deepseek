/-
Copyright: work module for the Elgindi finite-time singularity project.

# `Final.Step3Helpers` — the slice helpers of the honest Step-3 angular estimate

The declarations collected here are the *helper* part of
`Submission/Work/FTS/EllipticEst/Honest/step3Angle.lean` (everything in that file up to, but not
including, `step3Angle_of_pieces`).  They are consumed by the `I₄`-estimate
`H2W/AngBW/Step3/Ang1Bound.lean` (and hence by `Dispatch.step3AeD`), while the file's *target*
`Honest.step3Angle` — the Step-3 angular estimate itself, a different statement — is still a
`sorry` there.

Splitting the helpers out (verbatim, under the same names and the same namespace) is what makes
the level-`0` route `Final/Level0.lean` independent of `Honest.step3Angle`.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Prod
import Submission.Work.FTS.EllipticEst.Honest.Basic
import Submission.Work.FTS.EllipticEst.Honest.step3Defs
import Submission.Work.FTS.EllipticEst.HkNorm_add_le
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS.EllipticEst.Cert.SmoothOpen_bslOp
import Submission.Work.Spaces.aesm_of_continuousOn_Qd
import Submission.Work.Blocks.HkMem_of_majorant_aesm
import Submission.Work.FTS.EllipticEst.HkSq_congr_open
import Submission.Work.FTS.EllipticEst.AngClean.HkMem_zero_IPMem
import Submission.Work.FTS.EllipticEst.AngClean.IPMem_F_Phi
import Submission.Work.FTS.EllipticEst.Honest.AesmCross.aesmSliceCross
import Submission.Work.FTS.EllipticEst.Honest.AesmCross.aesmProdCross
import Submission.Work.FTS.EllipticEst.Honest.HonMemU.honMemPthTan
import Submission.Work.FTS.EllipticEst.remov.SmoothOpen_bslOp_of_smoothOpen

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

/-- **Honesty of `P`**, given the two honesty fields of Step 1. -/
theorem hkMem_POf {α : ℝ} {F Ψ : ℝ → ℝ → ℝ} (h : Hon α F Ψ)
    (hΨ : Work.Spaces.HkMem α 0 Ψ) (hG : Work.Spaces.HkMem α 0 (GOf Ψ)) :
    Work.Spaces.HkMem α 0 (POf Ψ) := by
  have hmp : SmoothOpen (POf Ψ) := smoothOpen_POf h.sm
  have hm1 : Work.Spaces.HkMem α 0 (fun z θ => α ^ 2 * AOf Ψ z θ) :=
    HkMem_const_mul' (α ^ 2) (f := AOf Ψ) h.memA
  have hm2 : Work.Spaces.HkMem α 0 (fun z θ => α * (5 + α) * GOf Ψ z θ) :=
    HkMem_const_mul' (α * (5 + α)) (f := GOf Ψ) hG
  have hm3 : Work.Spaces.HkMem α 0 (Work.Spaces.pthIter 2 Ψ) := h.memB
  have hm4 : Work.Spaces.HkMem α 0 F := h.memF
  have hm5 : Work.Spaces.HkMem α 0 (fun z θ => 5 * Ψ z θ) := HkMem_const_mul' 5 (f := Ψ) hΨ
  -- the five level-`0` integrands and their majorant
  set g1 : ℝ → ℝ → ℝ := fun z θ =>
    Work.Spaces.HkIntegrand α 0 (fun z θ => α ^ 2 * AOf Ψ z θ) z θ with hg1
  set g2 : ℝ → ℝ → ℝ := fun z θ =>
    Work.Spaces.HkIntegrand α 0 (fun z θ => α * (5 + α) * GOf Ψ z θ) z θ with hg2
  set g3 : ℝ → ℝ → ℝ := fun z θ =>
    Work.Spaces.HkIntegrand α 0 (Work.Spaces.pthIter 2 Ψ) z θ with hg3
  set g4 : ℝ → ℝ → ℝ := fun z θ => Work.Spaces.HkIntegrand α 0 F z θ with hg4
  set g5 : ℝ → ℝ → ℝ := fun z θ =>
    Work.Spaces.HkIntegrand α 0 (fun z θ => 5 * Ψ z θ) z θ with hg5
  set M : ℝ → ℝ → ℝ := fun z θ => 5 * (g1 z θ + g2 z θ + g3 z θ + g4 z θ + g5 z θ) with hM
  refine Work.Blocks.HkMem_of_majorant_aesm α 0 (f := POf Ψ) (M := M) ?_ ?_ ?_ ?_ ?_
  · -- a.e. strong measurability of the angular slices of `HkIntegrand (POf Ψ)`
    intro z hz
    rcases eq_or_lt_of_le (Set.mem_Ici.mp hz) with hz0 | hzpos
    · rw [show (fun θ => Work.Spaces.HkIntegrand α 0 (POf Ψ) z θ) = fun _ : ℝ => (0 : ℝ) from by
        funext θ
        rw [← hz0]
        exact HkIntegrand_zero_boundary α _ (Or.inl rfl)]
      exact aestronglyMeasurable_const
    · exact Work.Spaces.aesm_slice_of_continuousOn_Qd
        (fun p : ℝ × ℝ => Work.Spaces.HkIntegrand α 0 (POf Ψ) p.1 p.2)
        (hmp.continuousOn_HkIntegrand α 0) hzpos
  · -- a.e. strong measurability of the partial `θ`-integral
    have hprod : MeasureTheory.AEStronglyMeasurable
        (fun p : ℝ × ℝ => Work.Spaces.HkIntegrand α 0 (POf Ψ) p.1 p.2)
        ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
          (MeasureTheory.volume.restrict Work.Spaces.Iθ)) :=
      Work.Spaces.aesm_of_continuousOn_Qd _ (hmp.continuousOn_HkIntegrand α 0)
    exact hprod.integral_prod_right'
  · -- integrability of the majorant on every angular slice
    intro z hz
    have hb1 : MeasureTheory.IntegrableOn (fun θ => g1 z θ) Work.Spaces.Iθ := hm1.1 z hz
    have hb2 : MeasureTheory.IntegrableOn (fun θ => g2 z θ) Work.Spaces.Iθ := hm2.1 z hz
    have hb3 : MeasureTheory.IntegrableOn (fun θ => g3 z θ) Work.Spaces.Iθ := hm3.1 z hz
    have hb4 : MeasureTheory.IntegrableOn (fun θ => g4 z θ) Work.Spaces.Iθ := hm4.1 z hz
    have hb5 : MeasureTheory.IntegrableOn (fun θ => g5 z θ) Work.Spaces.Iθ := hm5.1 z hz
    have h12 := hb1.add hb2
    have h123 := h12.add hb3
    have h1234 := h123.add hb4
    rw [hM]
    exact (h1234.add hb5).const_mul 5
  · -- integrability of the `z`-integral of the majorant
    set I1 : ℝ → ℝ := fun z => ∫ θ in Work.Spaces.Iθ, g1 z θ with hI1
    set I2 : ℝ → ℝ := fun z => ∫ θ in Work.Spaces.Iθ, g2 z θ with hI2
    set I3 : ℝ → ℝ := fun z => ∫ θ in Work.Spaces.Iθ, g3 z θ with hI3
    set I4 : ℝ → ℝ := fun z => ∫ θ in Work.Spaces.Iθ, g4 z θ with hI4
    set I5 : ℝ → ℝ := fun z => ∫ θ in Work.Spaces.Iθ, g5 z θ with hI5
    have hint1 : MeasureTheory.IntegrableOn I1 Work.Spaces.Iz := hm1.2
    have hint2 : MeasureTheory.IntegrableOn I2 Work.Spaces.Iz := hm2.2
    have hint3 : MeasureTheory.IntegrableOn I3 Work.Spaces.Iz := hm3.2
    have hint4 : MeasureTheory.IntegrableOn I4 Work.Spaces.Iz := hm4.2
    have hint5 : MeasureTheory.IntegrableOn I5 Work.Spaces.Iz := hm5.2
    have hSum : MeasureTheory.IntegrableOn
        (fun z => 5 * (I1 z + I2 z + I3 z + I4 z + I5 z)) Work.Spaces.Iz :=
      ((((hint1.add hint2).add hint3).add hint4).add hint5).const_mul 5
    refine MeasureTheory.IntegrableOn.congr_fun hSum (fun z hz => ?_) measurableSet_Ici
    have hb1 : MeasureTheory.IntegrableOn (fun θ => g1 z θ) Work.Spaces.Iθ := hm1.1 z hz
    have hb2 : MeasureTheory.IntegrableOn (fun θ => g2 z θ) Work.Spaces.Iθ := hm2.1 z hz
    have hb3 : MeasureTheory.IntegrableOn (fun θ => g3 z θ) Work.Spaces.Iθ := hm3.1 z hz
    have hb4 : MeasureTheory.IntegrableOn (fun θ => g4 z θ) Work.Spaces.Iθ := hm4.1 z hz
    have hb5 : MeasureTheory.IntegrableOn (fun θ => g5 z θ) Work.Spaces.Iθ := hm5.1 z hz
    have h12 := hb1.add hb2
    have h123 := h12.add hb3
    have h1234 := h123.add hb4
    have s5 : (∫ θ in Work.Spaces.Iθ, ((g1 z θ + g2 z θ + g3 z θ + g4 z θ) + g5 z θ))
        = (∫ θ in Work.Spaces.Iθ, (g1 z θ + g2 z θ + g3 z θ + g4 z θ))
          + (∫ θ in Work.Spaces.Iθ, g5 z θ) :=
      MeasureTheory.integral_add h1234 hb5
    have s4 : (∫ θ in Work.Spaces.Iθ, (g1 z θ + g2 z θ + g3 z θ + g4 z θ))
        = (∫ θ in Work.Spaces.Iθ, (g1 z θ + g2 z θ + g3 z θ))
          + (∫ θ in Work.Spaces.Iθ, g4 z θ) :=
      MeasureTheory.integral_add h123 hb4
    have s3 : (∫ θ in Work.Spaces.Iθ, (g1 z θ + g2 z θ + g3 z θ))
        = (∫ θ in Work.Spaces.Iθ, (g1 z θ + g2 z θ)) + (∫ θ in Work.Spaces.Iθ, g3 z θ) :=
      MeasureTheory.integral_add h12 hb3
    have s2 : (∫ θ in Work.Spaces.Iθ, (g1 z θ + g2 z θ))
        = (∫ θ in Work.Spaces.Iθ, g1 z θ) + (∫ θ in Work.Spaces.Iθ, g2 z θ) :=
      MeasureTheory.integral_add hb1 hb2
    show 5 * (I1 z + I2 z + I3 z + I4 z + I5 z) = ∫ θ in Work.Spaces.Iθ, M z θ
    rw [hM]
    simp only [MeasureTheory.integral_const_mul]
    congr 1
    simp only [hI1, hI2, hI3, hI4, hI5]
    rw [s5, s4, s3, s2]
  · -- the pointwise domination
    intro z hz θ hθ
    have hle := HkIntegrand_POf_le α F Ψ h z θ hz hθ
    rw [hM]
    simp only [hg1, hg2, hg3, hg4, hg5] at hle ⊢
    exact hle

end Work.FTS.EllipticEst.Honest
