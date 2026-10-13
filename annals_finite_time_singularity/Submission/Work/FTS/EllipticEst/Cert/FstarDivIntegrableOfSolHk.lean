import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Submission.Work.FTS.EllipticEst.Cert.FstarSmooth.Defs
import Submission.Work.FTS.EllipticEst.Cert.SmoothOpen_bslOp
import Submission.Work.FTS.EllipticEst.FstarDzIter_sq_mul_w_le_open
import Submission.Work.FTS.EllipticEst.aestronglyMeasurable_integral_Itheta_Q0

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology ENNReal
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.Cert

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-! ## Toolbox: smoothness of the source, measurability, Cauchy–Schwarz

The hypotheses of the certificate are `SmoothNbhd Ψ` (`Ψ` is smooth on a neighbourhood of
the closed quadrant) and `IsBslSol α F Ψ` (the elliptic law `F = bslOp α Ψ` on the open
quadrant `Q0 = (0,∞) × (0,π/2)`).  Together they give `SmoothOpen F`, i.e. `F` is `C^∞` on
the *open* quadrant: the certificate `Cert.SmoothOpen_bslOp` shows that `bslOp α Ψ` is
`C^∞` there, and `F` agrees with it on `Q0`.  Consequently

* `r ↦ F_*(F)(r)/r` is a.e. strongly measurable on `(0,∞)`
  (`aestronglyMeasurable_integral_Itheta_Q0`, a Fubini argument over the product measure);
* the Cauchy–Schwarz estimate `FstarDzIter_sq_mul_w_le_open` at `j = 0` reads
  `F_*(F)(r)²·w(r)² ≤ (π/2)·∫_θ (F(r,θ)·w(r)/sin(2θ)^{η/2})² dθ`. -/

/-- `F` is `C^∞` on the open quadrant, because there it coincides with `bslOp α Ψ`. -/
theorem SmoothOpen_of_bslSol (α : ℝ) (F Ψ : ℝ → ℝ → ℝ)
    (hsm : Work.Spaces.SmoothNbhd Ψ) (hsol : Work.Elliptic.IsBslSol α F Ψ) :
    Work.FTS.EllipticEst.SmoothOpen F :=
  smoothOpen_congr_bsl (SmoothOpen_bslOp α Ψ hsm)
    (fun z θ hz hθ0 hθ1 => hsol.1 z hz θ hθ0 hθ1)

/-- **Measurability of the angular-moment quotient.**  For the source `F` of a solution of
(PolarBSL), `r ↦ F_*(F)(r)/r` is a.e. strongly measurable on `(0,∞)`. -/
theorem aesm_Fstar_div_of_bslSol (α : ℝ) (F Ψ : ℝ → ℝ → ℝ)
    (hsm : Work.Spaces.SmoothNbhd Ψ) (hsol : Work.Elliptic.IsBslSol α F Ψ) :
    MeasureTheory.AEStronglyMeasurable (fun r : ℝ => Work.Elliptic.Fstar F r / r)
      (MeasureTheory.volume.restrict (Set.Ioi 0)) := by
  have hF : Work.FTS.EllipticEst.SmoothOpen F := SmoothOpen_of_bslSol α F Ψ hsm hsol
  have hφ : ContinuousOn Work.Elliptic.sinCos2 Work.Spaces.Iθ := by
    show ContinuousOn (fun θ : ℝ => Real.sin θ * Real.cos θ ^ 2) Work.Spaces.Iθ
    exact (Real.continuous_sin.mul (Real.continuous_cos.pow 2)).continuousOn
  have hmom := Work.FTS.EllipticEst.aestronglyMeasurable_integral_Itheta_Q0 F hF.continuousOn
    Work.Elliptic.sinCos2 hφ
  have hinv : MeasureTheory.AEStronglyMeasurable (fun r : ℝ => r⁻¹)
      (MeasureTheory.volume.restrict (Set.Ioi 0)) := by
    refine (continuousOn_id.inv₀ ?_).aestronglyMeasurable measurableSet_Ioi
    intro r hr
    exact ne_of_gt hr
  have hmul := hmom.mul hinv
  rw [show (fun r : ℝ => Work.Elliptic.Fstar F r / r)
      = (fun r : ℝ => (∫ θ in Work.Spaces.Iθ, F r θ * Work.Elliptic.sinCos2 θ) * r⁻¹)
      from by funext r; rw [Work.Elliptic.Fstar, div_eq_mul_inv]]
  exact hmul

/-! ## The two elementary pointwise estimates -/

/-- Young's inequality `√X·Y ≤ (X + Y²)/2` (valid for every `Y : ℝ`). -/
theorem sqrt_mul_le_half (X Y : ℝ) (hX : 0 ≤ X) : Real.sqrt X * Y ≤ (X + Y ^ 2) / 2 := by
  nlinarith [Real.sq_sqrt hX, sq_nonneg (Real.sqrt X - Y)]

/-- The radial weight is nonnegative. -/
theorem w_nonneg (r : ℝ) : 0 ≤ Work.Spaces.w r := by
  rw [Work.Spaces.w]; positivity

/-- **Cauchy–Schwarz for the angular moment, in the form used below**: for `r > 0`,

  `|F_*(F)(r)|·w(r) ≤ √((π/2)·∫_θ (F(r,θ)·w(r)/sin(2θ)^{η/2})² dθ)`. -/
theorem Fstar_mul_w_le_sqrt (α : ℝ) (k : ℕ) (F : ℝ → ℝ → ℝ)
    (hF : Work.FTS.EllipticEst.SmoothOpen F) (hmem : Work.Spaces.HkMem α k F)
    {r : ℝ} (hr : 0 < r) :
    |Work.Elliptic.Fstar F r| * Work.Spaces.w r
      ≤ Real.sqrt ((Real.pi / 2) * ∫ θ in Work.Spaces.Iθ,
          (F r θ * (Work.Spaces.w r / Real.sin (2 * θ) ^ (Work.Spaces.eta / 2))) ^ 2) := by
  set X : ℝ := (Real.pi / 2) * ∫ θ in Work.Spaces.Iθ,
      (F r θ * (Work.Spaces.w r / Real.sin (2 * θ) ^ (Work.Spaces.eta / 2))) ^ 2 with hX
  have hXnn : 0 ≤ X := by
    rw [hX]
    exact mul_nonneg (by positivity) (integral_nonneg fun θ => sq_nonneg _)
  have hsq : (Work.Elliptic.Fstar F r * Work.Spaces.w r) ^ 2 ≤ X := by
    rw [hX]
    have h := Work.FTS.EllipticEst.FstarDzIter_sq_mul_w_le_open α k F hF hmem 0 (Nat.zero_le k) hr
    simpa only [Work.Spaces.DzIter_zero, mul_pow] using h
  have h := Real.sqrt_le_sqrt hsq
  rw [Real.sqrt_sq_eq_abs] at h
  rwa [abs_mul, abs_of_nonneg (w_nonneg r)] at h

/-- **The angular slice of the weighted square of `F` is dominated by the `ℋ^k`-integrand**:
this is the `i = 0` term of the first sum of `Work.Spaces.HkIntegrand`. -/
theorem slice_le_HkIntegrand (α : ℝ) (k : ℕ) (F : ℝ → ℝ → ℝ)
    (hmem : Work.Spaces.HkMem α k F) {r : ℝ} (hr : r ∈ Work.Spaces.Iz) :
    (∫ θ in Work.Spaces.Iθ,
        (F r θ * (Work.Spaces.w r / Real.sin (2 * θ) ^ (Work.Spaces.eta / 2))) ^ 2)
      ≤ ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k F r θ :=
  integral_mono_of_nonneg (Eventually.of_forall fun θ => sq_nonneg _) (hmem.1 r hr)
    (Eventually.of_forall fun θ => by
      simpa only [Work.Spaces.DzIter_zero] using
        Work.Spaces.sq_le_HkIntegrand_z α k F r θ 0 (Nat.zero_le k))

/-! ## The majorants on `(0,1]` and on `(1,∞)`

Both use `|F_*(F)(r)|·w(r) ≤ √X(r)` with `X(r) = (π/2)∫_θ (…)²`, and then trade the weight
`w` against the radial factor `r`:

* on `(0,1]` one has `r²·w(r) = (1+r)² ≥ 1`, so `|F_*(F)(r)| ≤ √X(r)·r²` and hence
  `|F_*(F)(r)|/r ≤ √X(r)·r ≤ √X(r) ≤ (X(r)+1)/2`;
* on `(1,∞)` one has `w(r) ≥ 1`, so `|F_*(F)(r)|/r ≤ √X(r)/r ≤ (X(r) + r^{-2})/2`. -/

/-- **Majorant on `(0,1]`.** -/
theorem Fstar_div_le_majorant_Ioc (α : ℝ) (k : ℕ) (F : ℝ → ℝ → ℝ)
    (hF : Work.FTS.EllipticEst.SmoothOpen F) (hmem : Work.Spaces.HkMem α k F)
    {r : ℝ} (hr : r ∈ Set.Ioc 0 1) :
    |Work.Elliptic.Fstar F r| / r
      ≤ ((Real.pi / 2) * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k F r θ) + 1) / 2 := by
  have hr0 : 0 < r := hr.1
  have hrI : r ∈ Work.Spaces.Iz := by rw [Work.Spaces.Iz]; exact le_of_lt hr0
  set G : ℝ := ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k F r θ with hG
  set X : ℝ := (Real.pi / 2) * ∫ θ in Work.Spaces.Iθ,
      (F r θ * (Work.Spaces.w r / Real.sin (2 * θ) ^ (Work.Spaces.eta / 2))) ^ 2 with hX
  have hXnn : 0 ≤ X := by
    rw [hX]; exact mul_nonneg (by positivity) (integral_nonneg fun θ => sq_nonneg _)
  have hXG : X ≤ (Real.pi / 2) * G := by
    rw [hX, hG]
    exact mul_le_mul_of_nonneg_left (slice_le_HkIntegrand α k F hmem hrI) (by positivity)
  have hAw : |Work.Elliptic.Fstar F r| * Work.Spaces.w r ≤ Real.sqrt X := by
    rw [hX]; exact Fstar_mul_w_le_sqrt α k F hF hmem hr0
  have hone : 1 ≤ r ^ 2 * Work.Spaces.w r := by
    rw [Work.Spaces.w]
    field_simp
    nlinarith [hr0]
  have hstep1 : |Work.Elliptic.Fstar F r| ≤ Real.sqrt X * r ^ 2 := by
    calc |Work.Elliptic.Fstar F r| = |Work.Elliptic.Fstar F r| * 1 := by ring
      _ ≤ |Work.Elliptic.Fstar F r| * (r ^ 2 * Work.Spaces.w r) :=
          mul_le_mul_of_nonneg_left hone (abs_nonneg _)
      _ = (|Work.Elliptic.Fstar F r| * Work.Spaces.w r) * r ^ 2 := by ring
      _ ≤ Real.sqrt X * r ^ 2 := mul_le_mul_of_nonneg_right hAw (by positivity)
  have hstep2 : |Work.Elliptic.Fstar F r| / r ≤ Real.sqrt X * r := by
    rw [div_eq_mul_inv]
    calc |Work.Elliptic.Fstar F r| * r⁻¹ ≤ (Real.sqrt X * r ^ 2) * r⁻¹ :=
          mul_le_mul_of_nonneg_right hstep1 (by positivity)
      _ = Real.sqrt X * r := by
          rw [mul_assoc, sq, mul_assoc, mul_inv_cancel₀ hr0.ne', mul_one]
  have hstep3 : Real.sqrt X * r ≤ Real.sqrt X := by
    nth_rewrite 2 [← mul_one (Real.sqrt X)]
    exact mul_le_mul_of_nonneg_left hr.2 (Real.sqrt_nonneg _)
  have hstep4 : Real.sqrt X ≤ (X + 1) / 2 := by
    simpa using sqrt_mul_le_half X 1 hXnn
  calc |Work.Elliptic.Fstar F r| / r ≤ Real.sqrt X * r := hstep2
    _ ≤ Real.sqrt X := hstep3
    _ ≤ (X + 1) / 2 := hstep4
    _ ≤ ((Real.pi / 2) * G + 1) / 2 := by linarith [hXG]

/-- **Majorant on `(1,∞)`.** -/
theorem Fstar_div_le_majorant_Ioi (α : ℝ) (k : ℕ) (F : ℝ → ℝ → ℝ)
    (hF : Work.FTS.EllipticEst.SmoothOpen F) (hmem : Work.Spaces.HkMem α k F)
    {r : ℝ} (hr : 1 < r) :
    |Work.Elliptic.Fstar F r| / r
      ≤ ((Real.pi / 2) * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k F r θ)
          + (r⁻¹) ^ 2) / 2 := by
  have hr0 : 0 < r := by linarith
  have hrI : r ∈ Work.Spaces.Iz := by rw [Work.Spaces.Iz]; exact le_of_lt hr0
  set G : ℝ := ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k F r θ with hG
  set X : ℝ := (Real.pi / 2) * ∫ θ in Work.Spaces.Iθ,
      (F r θ * (Work.Spaces.w r / Real.sin (2 * θ) ^ (Work.Spaces.eta / 2))) ^ 2 with hX
  have hXnn : 0 ≤ X := by
    rw [hX]; exact mul_nonneg (by positivity) (integral_nonneg fun θ => sq_nonneg _)
  have hXG : X ≤ (Real.pi / 2) * G := by
    rw [hX, hG]
    exact mul_le_mul_of_nonneg_left (slice_le_HkIntegrand α k F hmem hrI) (by positivity)
  have hAw : |Work.Elliptic.Fstar F r| * Work.Spaces.w r ≤ Real.sqrt X := by
    rw [hX]; exact Fstar_mul_w_le_sqrt α k F hF hmem hr0
  have hone : 1 ≤ Work.Spaces.w r := by
    rw [Work.Spaces.w, le_div_iff₀ (by positivity : (0:ℝ) < r ^ 2)]
    nlinarith [hr]
  have hstep1 : |Work.Elliptic.Fstar F r| ≤ Real.sqrt X := by
    calc |Work.Elliptic.Fstar F r| = |Work.Elliptic.Fstar F r| * 1 := by ring
      _ ≤ |Work.Elliptic.Fstar F r| * Work.Spaces.w r :=
          mul_le_mul_of_nonneg_left hone (abs_nonneg _)
      _ ≤ Real.sqrt X := hAw
  have hstep2 : |Work.Elliptic.Fstar F r| / r ≤ Real.sqrt X * r⁻¹ := by
    rw [div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_right hstep1 (by positivity)
  have hstep3 : Real.sqrt X * r⁻¹ ≤ (X + (r⁻¹) ^ 2) / 2 := sqrt_mul_le_half X r⁻¹ hXnn
  calc |Work.Elliptic.Fstar F r| / r ≤ Real.sqrt X * r⁻¹ := hstep2
    _ ≤ (X + (r⁻¹) ^ 2) / 2 := hstep3
    _ ≤ ((Real.pi / 2) * G + (r⁻¹) ^ 2) / 2 := by linarith [hXG]

/-! ## The certificate -/

/-- **`r ↦ F_*(F)(r)/r` is integrable on `(0,∞)`** for the source `F` of a solution of
(PolarBSL) whose weighted `ℋ^k`-norm is honest.

Route (elementary Cauchy–Schwarz; measurability of `r ↦ F_*(F)(r)/r` comes from `hsol`, which
gives `F = bslOp α Ψ` a.e. on the open quadrant, hence a.e.-strong measurability via
`AEStronglyMeasurable.integral_prod_right'`):
`|F_*(F)(r)| ≤ √(π/2)·(∫_θ F(r,θ)² dθ)^{1/2}`; then
* on `(1,∞)`: `∫_1^∞ |F_*|/r ≤ √(π/2)·√(∫_1^∞ r^{-2})·√(∫_1^∞∫_θ F²) < ∞`;
* on `(0,1)`: `(∫_θF²)^{1/2} = r²·(r^{-4}∫_θF²)^{1/2}` and Cauchy–Schwarz give
  `∫_0^1 |F_*|/r ≤ √(π/2)·√(∫_0^1 r²)·√(∫_0^1 r^{-4}∫_θ F²) < ∞`.
In both cases `w(r)² ≥ r^{-4}` on `(0,1)` and `w(r)² ≥ 1` on `(1,∞)`, so the bounds are
dominated by the `i = 0` summand of `Work.Spaces.HkIntegrand α k F`, integrable by `hmem`.
(The `HkMem`-only version of the statement is false — see
`Submission/Work/FTS/EllipticEst/IntegrableOn_Fstar_div_of_HkMem.lean` — which is why `hsol`
is needed.) -/
theorem FstarDivIntegrableOfSolHk (α : ℝ) (k : ℕ) (F Ψ : ℝ → ℝ → ℝ)
    (hα : 0 < α) (hsm : Work.Spaces.SmoothNbhd Ψ) (hsol : Work.Elliptic.IsBslSol α F Ψ)
    (hmem : Work.Spaces.HkMem α k F) :
    MeasureTheory.IntegrableOn (fun r : ℝ => Work.Elliptic.Fstar F r / r) (Set.Ioi 0) := by
  have hF : Work.FTS.EllipticEst.SmoothOpen F := SmoothOpen_of_bslSol α F Ψ hsm hsol
  have haesm : MeasureTheory.AEStronglyMeasurable (fun r : ℝ => Work.Elliptic.Fstar F r / r)
      (MeasureTheory.volume.restrict (Set.Ioi 0)) := aesm_Fstar_div_of_bslSol α F Ψ hsm hsol
  have hIoc_aesm : MeasureTheory.AEStronglyMeasurable (fun r : ℝ => Work.Elliptic.Fstar F r / r)
      (MeasureTheory.volume.restrict (Set.Ioc 0 1)) :=
    haesm.mono_measure (Measure.restrict_mono (fun r hr => by
      simp only [Set.mem_Ioc] at hr; simp only [Set.mem_Ioi]; exact hr.1) le_rfl)
  have hIoi_aesm : MeasureTheory.AEStronglyMeasurable (fun r : ℝ => Work.Elliptic.Fstar F r / r)
      (MeasureTheory.volume.restrict (Set.Ioi 1)) :=
    haesm.mono_measure (Measure.restrict_mono (fun r hr => by
      simp only [Set.mem_Ioi] at hr ⊢; linarith) le_rfl)
  have hGIoc : MeasureTheory.IntegrableOn
      (fun r : ℝ => ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k F r θ) (Set.Ioc 0 1) :=
    hmem.2.mono_set (fun r hr => by rw [Work.Spaces.Iz]; exact le_of_lt hr.1)
  have hGIoi : MeasureTheory.IntegrableOn
      (fun r : ℝ => ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k F r θ) (Set.Ioi 1) :=
    hmem.2.mono_set (fun r hr => by
      rw [Work.Spaces.Iz]
      exact le_of_lt (lt_trans zero_lt_one (Set.mem_Ioi.mp hr)))
  have hc1 : MeasureTheory.IntegrableOn (fun _ : ℝ => (1 : ℝ)) (Set.Ioc 0 1) :=
    integrableOn_const (s := Set.Ioc 0 1) (C := (1 : ℝ))
      (by rw [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top)
  have hM1 : MeasureTheory.IntegrableOn (fun r : ℝ =>
      ((Real.pi / 2) * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k F r θ) + 1) / 2)
      (Set.Ioc 0 1) :=
    ((hGIoc.const_mul (Real.pi / 2)).add hc1).div_const 2
  have hrpow : MeasureTheory.IntegrableOn (fun r : ℝ => r ^ (-2 : ℝ)) (Set.Ioi 1) :=
    integrableOn_Ioi_rpow_of_lt (a := -2) (c := 1) (by norm_num) (by norm_num)
  have hInvSq : MeasureTheory.IntegrableOn (fun r : ℝ => (r⁻¹) ^ 2) (Set.Ioi 1) :=
    hrpow.congr_fun (fun r hr => by
      show r ^ (-2 : ℝ) = (r⁻¹) ^ 2
      rw [Real.rpow_neg (le_of_lt (lt_trans zero_lt_one (Set.mem_Ioi.mp hr)))]
      rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) from by norm_num, Real.rpow_natCast, inv_pow])
      measurableSet_Ioi
  have hM2 : MeasureTheory.IntegrableOn (fun r : ℝ =>
      ((Real.pi / 2) * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k F r θ)
        + (r⁻¹) ^ 2) / 2) (Set.Ioi 1) :=
    ((hGIoi.const_mul (Real.pi / 2)).add hInvSq).div_const 2
  have h1 : MeasureTheory.IntegrableOn (fun r : ℝ => Work.Elliptic.Fstar F r / r)
      (Set.Ioc 0 1) :=
    hM1.mono' hIoc_aesm (by
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
      rw [Real.norm_eq_abs, abs_div, abs_of_pos hr.1]
      exact Fstar_div_le_majorant_Ioc α k F hF hmem hr)
  have h2 : MeasureTheory.IntegrableOn (fun r : ℝ => Work.Elliptic.Fstar F r / r)
      (Set.Ioi 1) := by
    have hr0 : ∀ r : ℝ, r ∈ Set.Ioi 1 → (0 : ℝ) < r := fun r hr =>
      lt_trans zero_lt_one (Set.mem_Ioi.mp hr)
    refine hM2.mono' hIoi_aesm ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
    rw [Real.norm_eq_abs, abs_div, abs_of_pos (hr0 r hr)]
    exact Fstar_div_le_majorant_Ioi α k F hF hmem (Set.mem_Ioi.mp hr)
  have hset : Set.Ioc (0 : ℝ) 1 ∪ Set.Ioi 1 = Set.Ioi 0 := by
    ext r
    simp only [Set.mem_union, Set.mem_Ioc, Set.mem_Ioi]
    constructor
    · rintro (⟨h1, _⟩ | h1) <;> linarith
    · intro hr
      rcases lt_or_ge r 1 with h | h
      · exact Or.inl ⟨hr, le_of_lt h⟩
      · rcases eq_or_lt_of_le h with h' | h'
        · exact Or.inl ⟨hr, le_of_eq h'.symm⟩
        · exact Or.inr h'
  have hU := h1.union h2
  rw [hset] at hU
  exact hU

end Work.FTS.EllipticEst.Cert
