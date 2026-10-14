import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.FTS.EllipticEst.OpenFTC.absFtcLeIntegralAbsDeriv
import Submission.Work.Spaces.HkSq_terms
import Submission.Work.Spaces.sin_two_rpow
import Submission.Work.Spaces.sq_mul_div_rpow
-- ===== merged: Submission.Work.FTS.EllipticEst.abs_mul_sinCos2_le_weighted =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst

open scoped Real

/-- On `[0,π/2]` the angular profile `sin θ cos²θ` lies in `[0,1]`. -/
lemma abs_sinCos2_le_one {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    |Work.Elliptic.sinCos2 θ| ≤ 1 := by
  have hθ0 : 0 ≤ θ := hθ.1
  have hθ1 : θ ≤ Real.pi / 2 := hθ.2
  have hpi := Real.pi_pos
  have hsin0 : 0 ≤ Real.sin θ := Real.sin_nonneg_of_nonneg_of_le_pi hθ0 (by linarith)
  have hsin1 : Real.sin θ ≤ 1 := Real.sin_le_one θ
  have hcos0 : 0 ≤ Real.cos θ :=
    Real.cos_nonneg_of_neg_pi_div_two_le_of_le (by linarith) hθ1
  have hcos1 : Real.cos θ ≤ 1 := Real.cos_le_one θ
  have hcos2 : Real.cos θ ^ 2 ≤ 1 := by nlinarith
  have hc1 : Work.Elliptic.sinCos2 θ ≤ 1 := by
    rw [Work.Elliptic.sinCos2]
    calc Real.sin θ * Real.cos θ ^ 2 ≤ 1 * 1 :=
          mul_le_mul hsin1 hcos2 (by positivity) (by norm_num)
      _ = 1 := by norm_num
  have hc0 : 0 ≤ Work.Elliptic.sinCos2 θ := by
    rw [Work.Elliptic.sinCos2]; positivity
  rw [abs_of_nonneg hc0]; exact hc1

/-- The radial weight `w(z) = (1+z)²/z²` is at least `1` for `z > 0`. -/
lemma one_le_w {z : ℝ} (hz : 0 < z) : 1 ≤ Work.Spaces.w z := by
  rw [Work.Spaces.w, one_le_div (by positivity)]
  nlinarith

/-- The requested estimate: on the angular domain, `|f θ · sinθcos²θ|` is absorbed by the
square of `f θ` times the weight `w(z)/sin(2θ)^{η/2}`, plus the constant `1`. -/
theorem abs_mul_sinCos2_le_weighted {f : ℝ → ℝ} {z : ℝ} (hz : 0 < z) {θ : ℝ}
    (hθ : θ ∈ Work.Spaces.Iθ) :
    |f θ * Work.Elliptic.sinCos2 θ|
      ≤ (f θ * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 + 1 := by
  have hθ0 : 0 ≤ θ := hθ.1
  have hθ1 : θ ≤ Real.pi / 2 := hθ.2
  have hcabs : |Work.Elliptic.sinCos2 θ| ≤ 1 := abs_sinCos2_le_one hθ
  have hsin2_nonneg : 0 ≤ Real.sin (2 * θ) := by
    apply Real.sin_nonneg_of_nonneg_of_le_pi <;> linarith
  have hw : 1 ≤ Work.Spaces.w z := one_le_w hz
  have heta2 : 0 ≤ Work.Spaces.eta / 2 := by norm_num [Work.Spaces.eta]
  have heta2' : Work.Spaces.eta / 2 ≠ 0 := by norm_num [Work.Spaces.eta]
  by_cases h0 : Real.sin (2 * θ) = 0
  · -- degenerate angles: `sin(2θ) = 0` forces `sinθcos²θ = 0`, and the weight is `0`
    have hs0 : Real.sin (2 * θ) ^ (Work.Spaces.eta / 2) = 0 := by
      rw [h0]; exact Real.zero_rpow heta2'
    have hcz : Work.Elliptic.sinCos2 θ = 0 := by
      have h1 : Real.sin θ * Real.cos θ = 0 := by
        have h2 := Real.sin_two_mul θ
        rw [h0] at h2
        linarith
      rw [Work.Elliptic.sinCos2]
      calc Real.sin θ * Real.cos θ ^ 2 = (Real.sin θ * Real.cos θ) * Real.cos θ := by ring
        _ = 0 := by rw [h1, zero_mul]
    rw [hcz, mul_zero, abs_zero, hs0, div_zero, mul_zero,
      zero_pow (by norm_num : (2 : ℕ) ≠ 0)]
    norm_num
  · -- non-degenerate angles: the weight is at least `1`
    have hs_pos : 0 < Real.sin (2 * θ) ^ (Work.Spaces.eta / 2) :=
      Real.rpow_pos_of_pos (lt_of_le_of_ne hsin2_nonneg (Ne.symm h0)) _
    have hs_le : Real.sin (2 * θ) ^ (Work.Spaces.eta / 2) ≤ 1 :=
      Real.rpow_le_one hsin2_nonneg (Real.sin_le_one _) heta2
    have hW : 1 ≤ Work.Spaces.w z / Real.sin (2 * θ) ^ (Work.Spaces.eta / 2) := by
      rw [one_le_div hs_pos]
      exact le_trans hs_le hw
    have hW2 : 1 ≤ (Work.Spaces.w z / Real.sin (2 * θ) ^ (Work.Spaces.eta / 2)) ^ 2 :=
      one_le_pow₀ hW
    -- `|f θ · sinθcos²θ| ≤ |f θ|`
    have hLHS : |f θ * Work.Elliptic.sinCos2 θ| ≤ |f θ| := by
      rw [abs_mul]
      exact mul_le_of_le_one_right (abs_nonneg _) hcabs
    -- `|f θ| ≤ (f θ · W)² + 1`
    have hstep : |f θ|
        ≤ (f θ * (Work.Spaces.w z / Real.sin (2 * θ) ^ (Work.Spaces.eta / 2))) ^ 2 + 1 := by
      have h1 : (f θ) ^ 2
          ≤ (f θ * (Work.Spaces.w z / Real.sin (2 * θ) ^ (Work.Spaces.eta / 2))) ^ 2 := by
        rw [mul_pow]
        nlinarith [sq_nonneg (f θ), hW2]
      nlinarith [sq_abs (f θ), sq_nonneg (|f θ| - 1 / 2), h1]
    linarith

end Work.FTS.EllipticEst
end
-- ===== merged: Submission.Work.FTS.EllipticEst.pz_DzIter_sq_mul_sin_le_term =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst

/-- The radial weight beats the reciprocal of `z`: `1 ≤ z · w(z)` for `z > 0`, because
`z·w(z) = (1+z)²/z = z + 2 + 1/z ≥ 1`. -/
private lemma one_le_mul_w {z : ℝ} (hz : 0 < z) : 1 ≤ z * Work.Spaces.w z := by
  have hzw : z * Work.Spaces.w z = (1 + z) ^ 2 / z := by
    rw [Work.Spaces.w]
    field_simp
  rw [hzw, le_div_iff₀ hz]
  nlinarith [sq_nonneg z]

theorem pz_DzIter_sq_mul_sin_le_term (j : ℕ) {F : ℝ → ℝ → ℝ} {z θ : ℝ} (hz : 0 < z)
    (hθ : θ ∈ Work.Spaces.Iθ) :
    (Work.Spaces.pz (Work.Spaces.DzIter j F) z θ) ^ 2
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
      ≤ (Work.Spaces.DzIter (j + 1) F z θ
        * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 := by
  -- Unfold the outermost `D_z` and abbreviate `a = ∂_z D_z^j F (z,θ)`.
  rw [Work.Spaces.DzIter_succ]
  simp only [Work.Spaces.Dz]
  set a : ℝ := Work.Spaces.pz (Work.Spaces.DzIter j F) z θ with ha
  -- `sin (2θ) ≥ 0` on the angular interval.
  have hS : 0 ≤ Real.sin (2 * θ) :=
    Real.sin_nonneg_of_mem_Icc ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩
  have hnn : 0 ≤ a ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) :=
    mul_nonneg (sq_nonneg a) (Real.rpow_nonneg hS _)
  -- `D_z^{j+1} F = z·a`, so the right hand side is `(z·a·(w z / s^{η/2}))²`; the `rpow` algebra
  -- of `T1HardWeightAlg` rewrites it as `w(z)²·((z·a)²·s^{-η})`.
  have hkey := (Work.FTS.H2.T1HardWeightAlg 0 z θ (z * a) 0 (le_of_lt hz) hθ).1
  rw [← hkey]
  have h2 : (Work.Spaces.w z) ^ 2 * ((z * a) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
      = (z * Work.Spaces.w z) ^ 2
        * (a ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) := by
    ring
  rw [h2]
  exact le_mul_of_one_le_left hnn (one_le_pow₀ (one_le_mul_w hz))

end Work.FTS.EllipticEst
end
-- ===== merged: Submission.Work.FTS.H2.L12Q.phiWeight_slice_le =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.H2.L12Q

open scoped Real Topology
open MeasureTheory Set Filter

/-- **Pointwise form of the Hardy-weight comparison.**  For `r > 0` and `θ ∈ (0,π/2)`
the single weighted `D_z`-term `i = 0` of `HkIntegrand` dominates `(f r θ)² · w r`:
`sin(2θ)^{η/2} ≤ 1 ≤ w r` makes the weight factor in the squared derivative at least `w r`. -/
private lemma slice_pointwise (α : ℝ) (f : ℝ → ℝ → ℝ) (r θ : ℝ) (hr : 0 < r)
    (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    (f r θ) ^ 2 * ((1 + r) / r) ^ 2 ≤ Work.Spaces.HkIntegrand α 4 f r θ := by
  have hs0 : 0 < Real.sin (2 * θ) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])
  have hs1 : Real.sin (2 * θ) ≤ 1 := Real.sin_le_one _
  have hsle : (Real.sin (2 * θ)) ^ Work.Spaces.eta ≤ 1 :=
    Real.rpow_le_one (le_of_lt hs0) hs1 (le_of_lt Work.Spaces.eta_pos)
  have hsinpow : 1 ≤ (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) := by
    rw [Real.rpow_neg (le_of_lt hs0), one_le_inv₀ (Real.rpow_pos_of_pos hs0 _)]
    exact hsle
  have hwr : Work.Spaces.w r = ((1 + r) / r) ^ 2 := by rw [Work.Spaces.w, div_pow]
  rw [← hwr]
  have hw1 : 1 ≤ Work.Spaces.w r := by
    rw [Work.Spaces.w, one_le_div (by positivity)]
    nlinarith [hr]
  have hkey : Work.Spaces.w r
      ≤ (Work.Spaces.w r) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) := by
    have h2 : Work.Spaces.w r ≤ (Work.Spaces.w r) ^ 2 := by nlinarith
    have h3 : (Work.Spaces.w r) ^ 2
        ≤ (Work.Spaces.w r) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) := by
      simpa using mul_le_mul_of_nonneg_left hsinpow (sq_nonneg (Work.Spaces.w r))
    linarith
  refine le_trans ?_ (Work.Spaces.sq_le_HkIntegrand_z α 4 f r θ 0 (by norm_num))
  simp only [Work.Spaces.DzIter_zero]
  rw [Work.Spaces.sq_mul_div_rpow (f r θ) (Work.Spaces.w r) (Real.sin (2 * θ))
        Work.Spaces.eta (le_of_lt hs0) (ne_of_gt Work.Spaces.eta_pos)]
  nlinarith [mul_le_mul_of_nonneg_left hkey (sq_nonneg (f r θ))]

/-- **The Hardy-weight comparison of a single radial slice, with no smoothness hypothesis.**
For `f ∈ ℋ⁴` (i.e. `HkMem α 4 f`) and `r > 0`:
`(∫_θ f(r,θ)²) · ((1+r)/r)² ≤ ∫_θ HkIntegrand α 4 f r θ`.

This is the first step of `|L₁₂(f)(0)| ≤ C |f|_{ℋ⁴}` (Elgindi, Proposition `muestimate`,
tex 1516), in the interior class where `Work.Spaces.SmoothNbhd` is unavailable.

Read `Submission/Work/Spaces/Defs.lean` and `Submission/Work/Spaces/HkSq_terms.lean` first.
Declare the result in `namespace Work.FTS.H2.L12Q` inside the module
`Submission/Work/FTS/H2/L12Q/phiWeight_slice_le.lean`, so that its full name is
`Work.FTS.H2.L12Q.phiWeight_slice_le`.

ROUTE (no smoothness needed).  For `θ ∈ Ioo 0 (π/2)` one has `0 < sin(2θ) ≤ 1`, so
`sin(2θ)^η ≤ 1`, and `w r = ((1+r)/r)^2 ≥ 1` for `r > 0`; hence
`(f r θ)^2 * w r ≤ (f r θ * (w r / sin(2θ)^(η/2)))^2 ≤ Work.Spaces.HkIntegrand α 4 f r θ`,
the last step being `Work.Spaces.sq_le_HkIntegrand_z α 4 f r θ 0 (by norm_num)` and the middle
identity `(w/s^(η/2))^2 = w^2/s^η` (`Real.rpow_mul`, `η = (η/2)*2`).  Rewrite
`(∫_θ f²) * w r = ∫_θ f² * w r` (`MeasureTheory.integral_mul_const`) and apply
`MeasureTheory.integral_mono_of_nonneg` with the (integrable) majorant
`θ ↦ HkIntegrand α 4 f r θ` obtained from `hmem.1 r (le_of_lt hr)`; only the a.e. bound is
needed, the two endpoints being null (`MeasureTheory.Ioo_ae_eq_Icc`). -/
theorem phiWeight_slice_le (α : ℝ) (f : ℝ → ℝ → ℝ) (hmem : Work.Spaces.HkMem α 4 f) :
    ∀ r : ℝ, 0 < r →
      (∫ θ in Work.Spaces.Iθ, (f r θ) ^ 2) * ((1 + r) / r) ^ 2
        ≤ ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 f r θ := by
  intro r hr
  -- The pointwise bound only holds off the two endpoints, which are null sets.
  have hae : (fun θ => (f r θ) ^ 2 * ((1 + r) / r) ^ 2)
      ≤ᵐ[volume.restrict Work.Spaces.Iθ]
        (fun θ => Work.Spaces.HkIntegrand α 4 f r θ) := by
    have hcongr : volume.restrict Work.Spaces.Iθ
        = volume.restrict (Set.Ioo (0 : ℝ) (π / 2)) := by
      rw [Work.Spaces.Iθ]
      exact MeasureTheory.Measure.restrict_congr_set
        (MeasureTheory.Ioo_ae_eq_Icc (μ := volume) (a := (0 : ℝ)) (b := (π / 2))).symm
    rw [hcongr]
    exact MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioo
      (fun θ hθ => slice_pointwise α f r θ hr hθ)
  have hmono := MeasureTheory.integral_mono_of_nonneg
    (μ := volume.restrict Work.Spaces.Iθ)
    (f := fun θ => (f r θ) ^ 2 * ((1 + r) / r) ^ 2)
    (g := fun θ => Work.Spaces.HkIntegrand α 4 f r θ)
    (Eventually.of_forall (fun θ => mul_nonneg (sq_nonneg _) (sq_nonneg _)))
    (hmem.1 r (le_of_lt hr)) hae
  rwa [MeasureTheory.integral_mul_const] at hmono

end Work.FTS.H2.L12Q
end
-- ===== merged: Submission.Work.FTS.H2.OscSqLe =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.H2

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-! ## Elementary `rpow` bookkeeping -/

/-- `(x ^ a) ^ 2 = x ^ (2 * a)` for `x > 0`. -/
private lemma rpow_sq (x a : ℝ) (hx : 0 < x) : (x ^ a) ^ 2 = x ^ (2 * a) := by
  rw [pow_two, ← Real.rpow_add hx, show a + a = 2 * a by ring]

/-- `x ^ ((2 - γ)/2) * x ^ ((γ - 2)/2) = 1` for `x > 0`. -/
private lemma rpow_half_mul_half (x γ : ℝ) (hx : 0 < x) :
    x ^ ((2 - γ) / 2) * x ^ ((γ - 2) / 2) = 1 := by
  rw [← Real.rpow_add hx, show (2 - γ) / 2 + (γ - 2) / 2 = 0 by ring, Real.rpow_zero]

/-! ## The Cauchy–Schwarz step on a subinterval of `Iθ` -/

/-- Cauchy–Schwarz / Hardy oscillation bound on a subinterval of `Iθ = [0, π/2]`:
for `0 < α ≤ 1`, `a ≤ b` both in `Iθ` and `h` continuous on `[a,b]`,

  `(∫_a^b h)² ≤ (100/(γ-1)) · ∫_{Iθ} h² sin(2σ)^{2-γ}`.

This is a verbatim generalisation of the private lemma `core` of
`Submission/Work/Spaces/HardyTheta.lean` (the case `a = 0`, `b = θ`) from `Ioo 0 θ` to
`Ioo a b`. -/
private theorem coreInterval (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) (h : ℝ → ℝ) {a b : ℝ}
    (ha : a ∈ Work.Spaces.Iθ) (hb : b ∈ Work.Spaces.Iθ) (hab : a ≤ b)
    (hcont : ContinuousOn h (Set.Icc a b))
    (hint : MeasureTheory.IntegrableOn
      (fun s => (h s) ^ 2 * (Real.sin (2 * s)) ^ (2 - Work.Spaces.gam α))
      Work.Spaces.Iθ) :
    (∫ s in a..b, h s) ^ 2 ≤
      (100 / (Work.Spaces.gam α - 1)) *
        ∫ s in Work.Spaces.Iθ,
          (h s) ^ 2 * (Real.sin (2 * s)) ^ (2 - Work.Spaces.gam α) := by
  have hγ1 : 1 < Work.Spaces.gam α := Work.Spaces.one_lt_gam hα
  have hγ2 : Work.Spaces.gam α ≤ 11 / 10 := by rw [Work.Spaces.gam]; linarith
  have hp1 : -1 < Work.Spaces.gam α - 2 := by linarith
  have hp0 : Work.Spaces.gam α - 2 ≤ 0 := by linarith
  have ha0 : 0 ≤ a := ha.1
  have hb1 : b ≤ π / 2 := hb.2
  -- positivity of `sin (2 ·)` on `(a,b)`, nonnegativity on `Iθ`
  have hsinpos : ∀ s ∈ Set.Ioo a b, 0 < Real.sin (2 * s) := by
    intro s hs
    exact Real.sin_pos_of_pos_of_lt_pi (by linarith [hs.1, ha0])
      (by linarith [hs.2, hb1, Real.pi_pos])
  have hsinIθ : ∀ x ∈ Work.Spaces.Iθ, 0 ≤ Real.sin (2 * x) := by
    intro x hx
    exact Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hx.1])
      (by linarith [hx.2, Real.pi_pos])
  have hsub : Set.Ioo a b ⊆ Work.Spaces.Iθ := fun x hx =>
    ⟨le_trans ha0 hx.1.le, le_trans hx.2.le hb1⟩
  have hae_sub : Set.Ioo a b ≤ᵐ[volume] Work.Spaces.Iθ :=
    Filter.Eventually.of_forall (fun x hx => hsub hx)
  have hmIθ : MeasurableSet Work.Spaces.Iθ := by
    simp only [Work.Spaces.Iθ]
    exact measurableSet_Icc
  have hFnn : 0 ≤ᵐ[volume.restrict Work.Spaces.Iθ]
      (fun s => (h s) ^ 2 * (Real.sin (2 * s)) ^ (2 - Work.Spaces.gam α)) :=
    (MeasureTheory.ae_restrict_iff' hmIθ).2
      (Filter.Eventually.of_forall fun x hx =>
        mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (hsinIθ x hx) _))
  have hSnn : 0 ≤ᵐ[volume.restrict Work.Spaces.Iθ]
      (fun s => (Real.sin (2 * s)) ^ (Work.Spaces.gam α - 2)) :=
    (MeasureTheory.ae_restrict_iff' hmIθ).2
      (Filter.Eventually.of_forall fun x hx => Real.rpow_nonneg (hsinIθ x hx) _)
  -- integrability of the weighted square over the open interval
  have hIntF : MeasureTheory.IntegrableOn
      (fun s => (h s) ^ 2 * (Real.sin (2 * s)) ^ (2 - Work.Spaces.gam α)) (Set.Ioo a b) :=
    hint.mono_set hsub
  -- measurability of the two Cauchy–Schwarz factors
  have hcont_sin : ContinuousOn (fun s : ℝ => Real.sin (2 * s)) (Set.Ioo a b) :=
    Real.continuous_sin.comp_continuousOn ((continuous_const.mul continuous_id).continuousOn)
  have hsm_h : AEMeasurable h (volume.restrict (Set.Ioo a b)) :=
    (hcont.mono Set.Ioo_subset_Icc_self).aemeasurable measurableSet_Ioo
  have hsm_s : AEMeasurable (fun s : ℝ => (Real.sin (2 * s)) ^ ((2 - Work.Spaces.gam α) / 2))
      (volume.restrict (Set.Ioo a b)) :=
    (hcont_sin.rpow_const fun x hx => Or.inl (ne_of_gt (hsinpos x hx))).aemeasurable
      measurableSet_Ioo
  have hsm_s2 : AEMeasurable (fun s : ℝ => (Real.sin (2 * s)) ^ ((Work.Spaces.gam α - 2) / 2))
      (volume.restrict (Set.Ioo a b)) :=
    (hcont_sin.rpow_const fun x hx => Or.inl (ne_of_gt (hsinpos x hx))).aemeasurable
      measurableSet_Ioo
  -- the two squared integrands
  have eq_v2 : Set.EqOn
      (fun x => ((Real.sin (2 * x)) ^ ((Work.Spaces.gam α - 2) / 2)) ^ 2)
      (fun x => (Real.sin (2 * x)) ^ (Work.Spaces.gam α - 2)) (Set.Ioo a b) := by
    intro x hx
    dsimp only
    rw [rpow_sq _ _ (hsinpos x hx),
      show 2 * ((Work.Spaces.gam α - 2) / 2) = Work.Spaces.gam α - 2 by ring]
  have eq_u2 : Set.EqOn
      (fun x => (h x * (Real.sin (2 * x)) ^ ((2 - Work.Spaces.gam α) / 2)) ^ 2)
      (fun x => (h x) ^ 2 * (Real.sin (2 * x)) ^ (2 - Work.Spaces.gam α)) (Set.Ioo a b) := by
    intro x hx
    dsimp only
    rw [mul_pow, rpow_sq _ _ (hsinpos x hx),
      show 2 * ((2 - Work.Spaces.gam α) / 2) = 2 - Work.Spaces.gam α by ring]
  have hInt_v2 : MeasureTheory.IntegrableOn
      (fun x => ((Real.sin (2 * x)) ^ ((Work.Spaces.gam α - 2) / 2)) ^ 2) (Set.Ioo a b) :=
    ((Work.Spaces.sin_two_rpow (Work.Spaces.gam α - 2) hp1 hp0).1.mono_set hsub).congr_fun
      eq_v2.symm measurableSet_Ioo
  have hInt_u2 : MeasureTheory.IntegrableOn
      (fun x => (h x * (Real.sin (2 * x)) ^ ((2 - Work.Spaces.gam α) / 2)) ^ 2)
      (Set.Ioo a b) :=
    hIntF.congr_fun eq_u2.symm measurableSet_Ioo
  have hu_mem : MeasureTheory.MemLp
      (fun x => h x * (Real.sin (2 * x)) ^ ((2 - Work.Spaces.gam α) / 2)) 2
      (volume.restrict (Set.Ioo a b)) :=
    (MeasureTheory.memLp_two_iff_integrable_sq (hsm_h.mul hsm_s).aestronglyMeasurable).2 hInt_u2
  have hv_mem : MeasureTheory.MemLp
      (fun x => (Real.sin (2 * x)) ^ ((Work.Spaces.gam α - 2) / 2)) 2
      (volume.restrict (Set.Ioo a b)) :=
    (MeasureTheory.memLp_two_iff_integrable_sq hsm_s2.aestronglyMeasurable).2 hInt_v2
  have hcs := Work.Spaces.cs_integral hu_mem hv_mem
  -- identify the three integrals
  have e1 : (∫ x in Set.Ioo a b,
        (h x * (Real.sin (2 * x)) ^ ((2 - Work.Spaces.gam α) / 2))
          * (Real.sin (2 * x)) ^ ((Work.Spaces.gam α - 2) / 2))
      = ∫ x in Set.Ioo a b, h x := by
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioo fun x hx => ?_
    rw [mul_assoc, rpow_half_mul_half _ _ (hsinpos x hx), mul_one]
  have e2 : (∫ x in Set.Ioo a b,
        (h x * (Real.sin (2 * x)) ^ ((2 - Work.Spaces.gam α) / 2)) ^ 2)
      = ∫ x in Set.Ioo a b,
          (h x) ^ 2 * (Real.sin (2 * x)) ^ (2 - Work.Spaces.gam α) := by
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioo fun x hx => ?_
    rw [mul_pow, rpow_sq _ _ (hsinpos x hx),
      show 2 * ((2 - Work.Spaces.gam α) / 2) = 2 - Work.Spaces.gam α by ring]
  have e3 : (∫ x in Set.Ioo a b,
        ((Real.sin (2 * x)) ^ ((Work.Spaces.gam α - 2) / 2)) ^ 2)
      = ∫ x in Set.Ioo a b, (Real.sin (2 * x)) ^ (Work.Spaces.gam α - 2) := by
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioo fun x hx => ?_
    rw [rpow_sq _ _ (hsinpos x hx),
      show 2 * ((Work.Spaces.gam α - 2) / 2) = Work.Spaces.gam α - 2 by ring]
  have key : (∫ x in Set.Ioo a b, h x) ^ 2 ≤
      (∫ x in Set.Ioo a b, (h x) ^ 2 * (Real.sin (2 * x)) ^ (2 - Work.Spaces.gam α))
        * (∫ x in Set.Ioo a b, (Real.sin (2 * x)) ^ (Work.Spaces.gam α - 2)) := by
    calc (∫ x in Set.Ioo a b, h x) ^ 2
        = (∫ x in Set.Ioo a b,
            (h x * (Real.sin (2 * x)) ^ ((2 - Work.Spaces.gam α) / 2))
              * (Real.sin (2 * x)) ^ ((Work.Spaces.gam α - 2) / 2)) ^ 2 := by rw [e1]
      _ ≤ (∫ x in Set.Ioo a b,
              (h x * (Real.sin (2 * x)) ^ ((2 - Work.Spaces.gam α) / 2)) ^ 2)
            * (∫ x in Set.Ioo a b,
                ((Real.sin (2 * x)) ^ ((Work.Spaces.gam α - 2) / 2)) ^ 2) := hcs
      _ = (∫ x in Set.Ioo a b, (h x) ^ 2 * (Real.sin (2 * x)) ^ (2 - Work.Spaces.gam α))
            * (∫ x in Set.Ioo a b, (Real.sin (2 * x)) ^ (Work.Spaces.gam α - 2)) := by
            rw [e2, e3]
  -- monotonicity and the explicit bound for the singular weight
  have hA : (∫ x in Set.Ioo a b, (h x) ^ 2 * (Real.sin (2 * x)) ^ (2 - Work.Spaces.gam α))
      ≤ ∫ s in Work.Spaces.Iθ,
          (h s) ^ 2 * (Real.sin (2 * s)) ^ (2 - Work.Spaces.gam α) :=
    MeasureTheory.setIntegral_mono_set hint hFnn hae_sub
  have hB : (∫ x in Set.Ioo a b, (Real.sin (2 * x)) ^ (Work.Spaces.gam α - 2))
      ≤ 100 / (Work.Spaces.gam α - 1) := by
    have h1 : (∫ x in Set.Ioo a b, (Real.sin (2 * x)) ^ (Work.Spaces.gam α - 2))
        ≤ ∫ s in Work.Spaces.Iθ, (Real.sin (2 * s)) ^ (Work.Spaces.gam α - 2) :=
      MeasureTheory.setIntegral_mono_set (Work.Spaces.sin_two_rpow (Work.Spaces.gam α - 2)
        hp1 hp0).1 hSnn hae_sub
    have h2 : (∫ s in Work.Spaces.Iθ, (Real.sin (2 * s)) ^ (Work.Spaces.gam α - 2))
        ≤ 100 / ((Work.Spaces.gam α - 2) + 1) :=
      (Work.Spaces.sin_two_rpow (Work.Spaces.gam α - 2) hp1 hp0).2
    have h3 : 100 / ((Work.Spaces.gam α - 2) + 1) = 100 / (Work.Spaces.gam α - 1) := by
      ring_nf
    exact h1.trans (h2.trans (le_of_eq h3))
  have hA0 : 0 ≤ ∫ s in Work.Spaces.Iθ,
      (h s) ^ 2 * (Real.sin (2 * s)) ^ (2 - Work.Spaces.gam α) :=
    MeasureTheory.setIntegral_nonneg hmIθ
      (fun x hx => mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (hsinIθ x hx) _))
  have hB0 : 0 ≤ ∫ x in Set.Ioo a b, (Real.sin (2 * x)) ^ (Work.Spaces.gam α - 2) :=
    MeasureTheory.setIntegral_nonneg measurableSet_Ioo
      (fun x hx => Real.rpow_nonneg (hsinIθ x (hsub hx)) _)
  have hIoo : (∫ s in a..b, h s) = ∫ x in Set.Ioo a b, h x := by
    rw [intervalIntegral.integral_of_le hab, MeasureTheory.integral_Ioc_eq_integral_Ioo]
  calc (∫ s in a..b, h s) ^ 2
      = (∫ x in Set.Ioo a b, h x) ^ 2 := by rw [hIoo]
    _ ≤ (∫ x in Set.Ioo a b, (h x) ^ 2 * (Real.sin (2 * x)) ^ (2 - Work.Spaces.gam α))
          * (∫ x in Set.Ioo a b, (Real.sin (2 * x)) ^ (Work.Spaces.gam α - 2)) := key
    _ ≤ (∫ s in Work.Spaces.Iθ,
            (h s) ^ 2 * (Real.sin (2 * s)) ^ (2 - Work.Spaces.gam α))
          * (100 / (Work.Spaces.gam α - 1)) := mul_le_mul hA hB hB0 hA0
    _ = (100 / (Work.Spaces.gam α - 1)) *
          ∫ s in Work.Spaces.Iθ,
            (h s) ^ 2 * (Real.sin (2 * s)) ^ (2 - Work.Spaces.gam α) := by ring

/-! ## The oscillation bound -/

theorem OscSqLe (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) (h : ℝ → ℝ) {θ θ₀ : ℝ}
    (hθ : θ ∈ Work.Spaces.Iθ) (hθ₀ : θ₀ ∈ Work.Spaces.Iθ)
    (hderiv : ∀ x ∈ Set.uIcc θ θ₀, HasDerivAt h (deriv h x) x)
    (hcont : ContinuousOn (deriv h) (Set.uIcc θ θ₀))
    (hint : MeasureTheory.IntegrableOn
      (fun σ => (deriv h σ) ^ 2 * (Real.sin (2 * σ)) ^ (2 - Work.Spaces.gam α))
      Work.Spaces.Iθ) :
    (h θ - h θ₀) ^ 2 ≤ (100 / (Work.Spaces.gam α - 1)) *
      ∫ σ in Work.Spaces.Iθ,
        (deriv h σ) ^ 2 * (Real.sin (2 * σ)) ^ (2 - Work.Spaces.gam α) := by
  have hcont' : ContinuousOn (deriv h) (Set.uIcc θ₀ θ) := by
    rw [Set.uIcc_comm]
    exact hcont
  have hFTC : ∫ σ in θ₀..θ, deriv h σ = h θ - h θ₀ := by
    refine intervalIntegral.integral_eq_sub_of_hasDerivAt ?_ hcont'.intervalIntegrable
    intro x hx
    refine hderiv x ?_
    rw [Set.uIcc_comm] at hx
    exact hx
  rcases le_total θ₀ θ with hle | hle
  · -- `θ₀ ≤ θ`: apply the core on `[θ₀, θ]`; the fundamental theorem gives the difference.
    have hcc : ContinuousOn (deriv h) (Set.Icc θ₀ θ) := by
      rw [← Set.uIcc_of_le hle, Set.uIcc_comm]
      exact hcont
    have hcore := coreInterval α hα hα1 (deriv h) hθ₀ hθ hle hcc hint
    rw [hFTC] at hcore
    exact hcore
  · -- `θ ≤ θ₀`: the core on `[θ, θ₀]`; the reversed interval integral has the same square.
    have hcc : ContinuousOn (deriv h) (Set.Icc θ θ₀) := by
      rw [← Set.uIcc_of_le hle]
      exact hcont
    have hcore := coreInterval α hα hα1 (deriv h) hθ hθ₀ hle hcc hint
    have hsym : (∫ σ in θ₀..θ, deriv h σ) = -(∫ σ in θ..θ₀, deriv h σ) :=
      intervalIntegral.integral_symm θ θ₀
    have hsq : (h θ - h θ₀) ^ 2 = (∫ σ in θ..θ₀, deriv h σ) ^ 2 := by
      rw [← hFTC, hsym]
      ring
    rw [hsq]
    exact hcore

end Work.FTS.H2
end
end
-- ===== merged: Submission.Work.FTS.H2.Transport1Aux =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.H2

set_option autoImplicit false

/-! ## The angular slice supremum -/







/-! ## Regularity closure -/

/-- The pointwise product of two functions smooth on a neighbourhood of the closed quadrant
is again smooth on a neighbourhood of the closed quadrant. -/
theorem smoothNbhd_mul {f g : ℝ → ℝ → ℝ} (hf : Spaces.SmoothNbhd f)
    (hg : Spaces.SmoothNbhd g) : Spaces.SmoothNbhd (fun z θ => f z θ * g z θ) := by
  show ContDiffOn ℝ ⊤ (Function.uncurry (fun z θ : ℝ => f z θ * g z θ)) _
  have h : Function.uncurry (fun z θ : ℝ => f z θ * g z θ)
      = Function.uncurry f * Function.uncurry g := rfl
  rw [h]
  exact hf.mul hg


/-! ## Iterated `D_θ` against an extra `D_θ` -/

/-- `D_θ^n (D_θ g) = D_θ^{n+1} g`. -/
theorem DthIter_Dth (n : ℕ) (g : ℝ → ℝ → ℝ) :
    Spaces.DthIter n (Spaces.Dth g) = Spaces.DthIter (n + 1) g := by
  induction n with
  | zero => rfl
  | succ k ih =>
      rw [Spaces.DthIter_succ k (Spaces.Dth g), ih]
      exact (Spaces.DthIter_succ (k + 1) g).symm

/-- `D_z^j D_θ^i (D_θ g) = D_z^j D_θ^{i+1} g`, i.e. `mixed j i (D_θ g) = mixed j (i+1) g`. -/
theorem mixed_Dth (j i : ℕ) (g : ℝ → ℝ → ℝ) :
    Spaces.mixed j i (Spaces.Dth g) = Spaces.mixed j (i + 1) g := by
  rw [Spaces.mixed, Spaces.mixed, DthIter_Dth]


end Work.FTS.H2
end
end
