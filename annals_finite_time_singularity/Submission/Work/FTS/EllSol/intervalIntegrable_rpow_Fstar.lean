import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Submission.Work.Spaces.HkSq_terms
import Submission.Work.FTS.EllipticEst.Fstar_Hk_le_open
import Submission.Work.FTS.EllipticEst.Cert.FstarDivIntegrableOfSolHk
import Submission.Work.FTS.H2.QangAux

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllSol

open MeasureTheory Set Filter
open scoped Real Topology

/-! ## Interval integrability of `s^{(5-α)/α} F_*(g)(s)`

The singular radial piece `Ḡ(α,g)(z) = -(3/(4α)) z^{-5/α} ∫_0^z s^{(5-α)/α} F_*(g)(s) ds`
of §'The singular term' is only a genuine integral if the integrand
`s ↦ s^{(5-α)/α} · F_*(g)(s)` is interval integrable on `[0,z]`; this is what is proved here
for every datum `g` that is `C^∞` on the open half-strip and lies honestly in `ℋ⁴`.

The mathematics is a two-step domination, valid for *every* `α > 0` (no `α ≤ 1` is needed):

* **Cauchy–Schwarz against the weight.**  `Cert.Fstar_mul_w_le_sqrt` gives
  `|F_*(g)(s)| · w(s) ≤ √((π/2) ∫_θ (g(s,θ) w(s)/sin(2θ)^{η/2})² dθ)`, and the angular
  integral is at most the `θ`-slice `G(s) = ∫_θ HkIntegrand α 4 g s θ` of the `ℋ⁴`-integrand
  (`Cert.slice_le_HkIntegrand`).  Since `1/w(s) = s²/(1+s)² ≤ s²`, this yields
  `|F_*(g)(s)| ≤ √(π/2)·√(G(s))·s²`.
* **The radial exponents.**  Multiplying by `s^c`, `c = (5-α)/α`,
  `|s^c F_*(g)(s)| ≤ √(π/2)·s^{c+2}·√(G(s))`; here `c + 2 = (5+α)/α > 0`, so on `(0,z]` the
  factor `s^{c+2}` is bounded by `z^{c+2}` (this is exactly what makes the argument work also
  for `α > 5`, where `c < 0` and `s^c` alone is unbounded at `0`).  Finally `√X ≤ 1 + X`, and
  `s ↦ 1 + G(s)` is integrable on the *finite* interval `(0,z]` by `HkMem`, so the majorant
  `√(π/2)·z^{c+2}·(1 + G(s))` is integrable.

The only remaining input is measurability: `F_*(g) = B_0` is the zeroth radial moment, hence
continuous on `(0,∞)` by `continuousOn_Bmom`. -/

theorem intervalIntegrable_rpow_Fstar (α : ℝ) (hα : 0 < α) (g : ℝ → ℝ → ℝ)
    (hsm : Work.FTS.LocData.SmoothQuad g) (hmem : Work.Spaces.HkMem α 4 g)
    {z : ℝ} (hz : 0 < z) :
    IntervalIntegrable (fun s : ℝ => s ^ ((5 - α) / α) * Work.Elliptic.Fstar g s)
      MeasureTheory.volume 0 z := by
  set c : ℝ := (5 - α) / α with hc
  have hcgt : -1 < c := by
    rw [hc, lt_div_iff₀ hα]; linarith
  have hc2 : 0 < c + 2 := by linarith
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hz.le]
  have hO : Work.FTS.EllipticEst.SmoothOpen g := Work.FTS.H2.SmoothQuad.toSmoothOpen hsm
  -- `F_*(g) = Bmom g 0` is continuous on `(0,∞)`
  have hcont : ContinuousOn (fun s : ℝ => Work.Elliptic.Fstar g s) (Set.Ioi 0) := by
    have h := Work.FTS.EllipticEst.continuousOn_Bmom α 4 hO hmem 0 (by norm_num)
    refine h.congr ?_
    intro s _
    exact (Work.FTS.EllipticEst.Bmom_zero g s).symm
  have haesm : AEStronglyMeasurable (fun s : ℝ => s ^ c * Work.Elliptic.Fstar g s)
      (volume.restrict (Set.Ioc 0 z)) := by
    have hrpow_cont : ContinuousOn (fun s : ℝ => s ^ c) (Set.Ioi 0) :=
      continuousOn_id.rpow_const (fun s hs => Or.inl (ne_of_gt hs))
    exact ((hrpow_cont.mul hcont).mono (fun s hs => hs.1)).aestronglyMeasurable measurableSet_Ioc
  -- the `θ`-slice of the `ℋ⁴`-integrand is integrable on `(0,z]`
  have hGint : IntegrableOn (fun s : ℝ => ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 g s θ)
      (Set.Ioc 0 z) :=
    hmem.2.mono_set (fun s hs => by rw [Work.Spaces.Iz]; exact le_of_lt hs.1)
  have hone : IntegrableOn (fun _ : ℝ => (1 : ℝ)) (Set.Ioc 0 z) :=
    integrableOn_const (by rw [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top)
  have hdom : Integrable (fun s : ℝ => Real.sqrt (π / 2) * z ^ (c + 2) *
      (1 + ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 g s θ))
      (volume.restrict (Set.Ioc 0 z)) :=
    (hone.add hGint).const_mul (Real.sqrt (π / 2) * z ^ (c + 2))
  -- the pointwise domination
  have hpt : ∀ s ∈ Set.Ioc 0 z,
      ‖s ^ c * Work.Elliptic.Fstar g s‖
        ≤ Real.sqrt (π / 2) * z ^ (c + 2)
            * (1 + ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 g s θ) := by
    intro s hs
    have hs0 : 0 < s := hs.1
    have hsz : s ≤ z := hs.2
    have hsI : s ∈ Work.Spaces.Iz := le_of_lt hs0
    set G : ℝ := ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 g s θ with hG
    have hGnn : 0 ≤ G := by
      rw [hG]; exact integral_nonneg fun θ => Work.Spaces.HkIntegrand_nonneg α 4 g s θ
    have hslice : (∫ θ in Work.Spaces.Iθ,
        (g s θ * (Work.Spaces.w s / Real.sin (2 * θ) ^ (Work.Spaces.eta / 2))) ^ 2) ≤ G := by
      rw [hG]; exact Work.FTS.EllipticEst.Cert.slice_le_HkIntegrand α 4 g hmem hsI
    have hXG : (π / 2) * (∫ θ in Work.Spaces.Iθ,
        (g s θ * (Work.Spaces.w s / Real.sin (2 * θ) ^ (Work.Spaces.eta / 2))) ^ 2)
        ≤ (π / 2) * G :=
      mul_le_mul_of_nonneg_left hslice (by positivity)
    have hAw := Work.FTS.EllipticEst.Cert.Fstar_mul_w_le_sqrt α 4 g hO hmem hs0
    have hAb : |Work.Elliptic.Fstar g s| * Work.Spaces.w s ≤ Real.sqrt ((π / 2) * G) :=
      le_trans hAw (Real.sqrt_le_sqrt hXG)
    have hwpos : 0 < Work.Spaces.w s := by
      rw [Work.Spaces.w]; positivity
    -- `1 / w s ≤ s²`
    have hwinv : 1 / Work.Spaces.w s ≤ s ^ 2 := by
      have h1 : (1 : ℝ) ≤ (1 + s) ^ 2 := by nlinarith [hs0.le]
      rw [Work.Spaces.w, one_div, inv_div]
      rw [div_le_iff₀ (by positivity : (0 : ℝ) < (1 + s) ^ 2)]
      simpa using mul_le_mul_of_nonneg_left h1 (sq_nonneg s)
    have hb1 : |Work.Elliptic.Fstar g s| ≤ Real.sqrt ((π / 2) * G) * s ^ 2 := by
      have h1 : |Work.Elliptic.Fstar g s| * Work.Spaces.w s / Work.Spaces.w s
          ≤ Real.sqrt ((π / 2) * G) / Work.Spaces.w s :=
        div_le_div_of_nonneg_right hAb hwpos.le
      have h2 : Real.sqrt ((π / 2) * G) / Work.Spaces.w s ≤ Real.sqrt ((π / 2) * G) * s ^ 2 := by
        rw [div_eq_mul_one_div]
        exact mul_le_mul_of_nonneg_left hwinv (Real.sqrt_nonneg _)
      have h3 : |Work.Elliptic.Fstar g s| * Work.Spaces.w s / Work.Spaces.w s
          = |Work.Elliptic.Fstar g s| := by
        rw [mul_div_assoc, div_self (ne_of_gt hwpos), mul_one]
      calc |Work.Elliptic.Fstar g s|
          = |Work.Elliptic.Fstar g s| * Work.Spaces.w s / Work.Spaces.w s := h3.symm
        _ ≤ Real.sqrt ((π / 2) * G) / Work.Spaces.w s := h1
        _ ≤ Real.sqrt ((π / 2) * G) * s ^ 2 := h2
    have hsq : Real.sqrt ((π / 2) * G) = Real.sqrt (π / 2) * Real.sqrt G :=
      Real.sqrt_mul (by positivity) G
    have hb1' : |Work.Elliptic.Fstar g s| ≤ Real.sqrt (π / 2) * Real.sqrt G * s ^ 2 := by
      rw [hsq] at hb1; exact hb1
    have hb2 : s ^ c * |Work.Elliptic.Fstar g s| ≤ Real.sqrt (π / 2) * z ^ (c + 2) * Real.sqrt G := by
      have h1 : s ^ c * |Work.Elliptic.Fstar g s|
          ≤ s ^ c * (Real.sqrt (π / 2) * Real.sqrt G * s ^ 2) :=
        mul_le_mul_of_nonneg_left hb1' (Real.rpow_nonneg hs0.le c)
      have h2 : s ^ c * (Real.sqrt (π / 2) * Real.sqrt G * s ^ 2)
          = Real.sqrt (π / 2) * s ^ (c + 2) * Real.sqrt G := by
        rw [Real.rpow_add hs0 c 2]
        have htwo : s ^ (2 : ℝ) = s ^ 2 := by norm_num
        rw [htwo]
        ring
      have h3 : Real.sqrt (π / 2) * s ^ (c + 2) * Real.sqrt G
          ≤ Real.sqrt (π / 2) * z ^ (c + 2) * Real.sqrt G := by
        have hsz' : s ^ (c + 2) ≤ z ^ (c + 2) := Real.rpow_le_rpow hs0.le hsz hc2.le
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hsz' (Real.sqrt_nonneg _))
          (Real.sqrt_nonneg _)
      calc s ^ c * |Work.Elliptic.Fstar g s|
            ≤ s ^ c * (Real.sqrt (π / 2) * Real.sqrt G * s ^ 2) := h1
        _ = Real.sqrt (π / 2) * s ^ (c + 2) * Real.sqrt G := h2
        _ ≤ Real.sqrt (π / 2) * z ^ (c + 2) * Real.sqrt G := h3
    have hb3 : Real.sqrt G ≤ 1 + G := by
      rw [Real.sqrt_le_iff]
      exact ⟨by linarith, by nlinarith⟩
    have hfinal : Real.sqrt (π / 2) * z ^ (c + 2) * Real.sqrt G
        ≤ Real.sqrt (π / 2) * z ^ (c + 2) * (1 + G) :=
      mul_le_mul_of_nonneg_left hb3
        (mul_nonneg (Real.sqrt_nonneg _) (Real.rpow_nonneg (le_trans hs0.le hsz) _))
    have hnorm : ‖s ^ c * Work.Elliptic.Fstar g s‖ = s ^ c * |Work.Elliptic.Fstar g s| := by
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (Real.rpow_nonneg hs0.le c)]
    rw [hnorm]
    exact le_trans hb2 hfinal
  exact Integrable.mono' hdom haesm (ae_restrict_of_forall_mem measurableSet_Ioc hpt)

end Work.FTS.EllSol
