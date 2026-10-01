import Mathlib
import Submission.Work.LinnikAreas.P3Rect.Work_LinnikAreas_DhExplicit_XiStrip
import Submission.Work.LinnikAreas.P3Rect.Work_LinnikAreas_DhK_ZSBase

open scoped Classical BigOperators Topology
open Filter

noncomputable section

namespace Work.LinnikAreas.DhExplicit

open Work.LinnikAreas.DhK

/-- Near a point `u` of the critical strip, `Ξ` agrees with `(1/2) · s · Γ_ℝ(s) · ζ₁(s)`,
where `ζ₁ = (s-1)ζ`.  The factor `(1/2) · s · Γ_ℝ(s)` is analytic and non-vanishing at `u`. -/
lemma Xi_eventuallyEq_half_mul_zeta1 {u : ℂ} (h0 : 0 < u.re) (h1 : u.re < 1) :
    Xi =ᶠ[𝓝 u] fun s : ℂ => ((1 / 2 : ℂ) * s * Complex.Gammaℝ s) * riemannZeta₁ s := by
  have hu0 : u ≠ 0 := by intro h; rw [h] at h0; simp at h0
  have hu1 : u ≠ 1 := by intro h; rw [h] at h1; norm_num at h1
  filter_upwards [isOpen_lt continuous_const Complex.continuous_re |>.mem_nhds h0,
    eventually_ne_nhds hu0, eventually_ne_nhds hu1] with s hsre hs0 hs1
  have hs1' : s - 1 ≠ 0 := sub_ne_zero.mpr hs1
  have hGs : Complex.Gammaℝ s ≠ 0 := Complex.Gammaℝ_ne_zero_of_re_pos hsre
  have hΛζ : completedRiemannZeta s = Complex.Gammaℝ s * riemannZeta s := by
    rw [riemannZeta_def_of_ne_zero hs0]; field_simp
  have hζ : riemannZeta s = (s - 1)⁻¹ * riemannZeta₁ s := riemannZeta_eq_inv_sub_mul hs1
  rw [Xi_eq_half_mul s hs0 hs1, hΛζ, hζ]
  field_simp [hs1']

/-- In the critical strip the vanishing order of `Ξ` equals that of `ζ₁ = (s-1)ζ`. -/
lemma ordNat_Xi_eq_zeta1 {u : ℂ} (h0 : 0 < u.re) (h1 : u.re < 1) :
    analyticOrderNatAt Xi u = analyticOrderNatAt riemannZeta₁ u := by
  have hu0 : u ≠ 0 := by intro h; rw [h] at h0; simp at h0
  have hu1 : u ≠ 1 := by intro h; rw [h] at h1; norm_num at h1
  have hGan : AnalyticAt ℂ Complex.Gammaℝ u := by
    have hinv : Differentiable ℂ (fun s : ℂ => (Complex.Gammaℝ s)⁻¹) :=
      Complex.differentiable_Gammaℝ_inv
    have hinvz : (fun s : ℂ => (Complex.Gammaℝ s)⁻¹) u ≠ 0 :=
      inv_ne_zero (Complex.Gammaℝ_ne_zero_of_re_pos h0)
    have han0 : AnalyticAt ℂ (fun s : ℂ => ((Complex.Gammaℝ s)⁻¹)⁻¹) u :=
      (hinv.analyticAt u).inv hinvz
    have heq : (fun s : ℂ => ((Complex.Gammaℝ s)⁻¹)⁻¹) = Complex.Gammaℝ := by
      funext s; rw [inv_inv]
    rwa [heq] at han0
  have hgan : AnalyticAt ℂ (fun s : ℂ => (1 / 2 : ℂ) * s * Complex.Gammaℝ s) u :=
    (analyticAt_const.mul analyticAt_id).mul hGan
  have hganne : (fun s : ℂ => (1 / 2 : ℂ) * s * Complex.Gammaℝ s) u ≠ 0 := by
    have hGne : Complex.Gammaℝ u ≠ 0 := Complex.Gammaℝ_ne_zero_of_re_pos h0
    show (1 / 2 : ℂ) * u * Complex.Gammaℝ u ≠ 0
    exact mul_ne_zero (mul_ne_zero (by norm_num) hu0) hGne
  have hz1an : AnalyticAt ℂ riemannZeta₁ u := differentiable_riemannZeta₁.analyticAt u
  have hEq := Xi_eventuallyEq_half_mul_zeta1 h0 h1
  have h1' : analyticOrderNatAt Xi u
      = analyticOrderNatAt
          (fun s : ℂ => ((1 / 2 : ℂ) * s * Complex.Gammaℝ s) * riemannZeta₁ s) u := by
    simp only [analyticOrderNatAt]
    rw [analyticOrderAt_congr hEq]
  have h_or : analyticOrderAt
        (fun s : ℂ => ((1 / 2 : ℂ) * s * Complex.Gammaℝ s) * riemannZeta₁ s) u
      = analyticOrderAt (fun s : ℂ => (1 / 2 : ℂ) * s * Complex.Gammaℝ s) u
        + analyticOrderAt riemannZeta₁ u := by
    rw [show (fun s : ℂ => ((1 / 2 : ℂ) * s * Complex.Gammaℝ s) * riemannZeta₁ s)
        = (fun s : ℂ => (1 / 2 : ℂ) * s * Complex.Gammaℝ s) * riemannZeta₁ from rfl]
    exact analyticOrderAt_mul hgan hz1an
  have hzero : analyticOrderAt (fun s : ℂ => (1 / 2 : ℂ) * s * Complex.Gammaℝ s) u = 0 :=
    analyticOrderAt_eq_zero.mpr (Or.inr hganne)
  have h1'' : analyticOrderNatAt
        (fun s : ℂ => ((1 / 2 : ℂ) * s * Complex.Gammaℝ s) * riemannZeta₁ s) u
      = analyticOrderNatAt riemannZeta₁ u := by
    simp only [analyticOrderNatAt]
    rw [h_or, hzero, zero_add]
  rw [h1', h1'']

/-- Pointwise domination of the vanishing order of `Ξ` by that of `ζ₁ = (s-1)ζ`.

`Ξ = Work.LinnikAreas.DhK.Xi` is the entire completion `Ξ(s) = 1/2 + (1/2)s(s-1)Λ₀(s)` of the
Riemann zeta function; its zeros are the non-trivial zeros of `ζ` and lie in `0 < Re < 1`
(`Work.LinnikAreas.DhExplicit.Xi_zero_strip` in
`Submission/Work/LinnikAreas/DhExplicit/XiStrip.lean`, which you may import).  For a zero `u` of
`Ξ` with `0 < Re u < 1`, one has near `u` the factorisation `Ξ = (1/2) · s · Γ_ℝ(s) · ζ₁(s)`
(`Xi_eq_half_mul`, `riemannZeta_def_of_ne_zero`, `riemannZeta_eq_inv_sub_mul`) with both factors
analytic at `u` and the first non-vanishing, hence
`analyticOrderNatAt Ξ u = analyticOrderNatAt ζ₁ u`; if `Ξ u ≠ 0` the left hand order is `0`.
This is the exact analogue of `Work.LinnikAreas.FarRepel.multZeta_le_order_zeta1` (read-only file
`Submission/Work/LinnikAreas/FarRepel/zeroSumInvSqBound.lean`, which cannot be imported because of
a name clash) — its proof can be copied with `completedRiemannZeta` replaced by `Xi`.  You may add
helper lemmas above the statement. -/
theorem XiOrdLeZeta1 (u : ℂ) :
    analyticOrderNatAt Work.LinnikAreas.DhK.Xi u ≤ analyticOrderNatAt riemannZeta₁ u := by
  by_cases h : Xi u = 0
  · obtain ⟨h0, h1⟩ := Xi_zero_strip h
    rw [ordNat_Xi_eq_zeta1 h0 h1]
  · have hz : analyticOrderNatAt Xi u = 0 := by
      have h0 : analyticOrderAt Xi u = 0 := analyticOrderAt_eq_zero.mpr (Or.inr h)
      simp [analyticOrderNatAt, h0]
    rw [hz]; exact Nat.zero_le _

end Work.LinnikAreas.DhExplicit
