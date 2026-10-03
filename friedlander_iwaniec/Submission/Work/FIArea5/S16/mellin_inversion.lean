/-
# `Submission.Work.FIArea5.S16.mellin_inversion`

**The Mellin inversion of the radius mollifier** (*FI* (16.28)): for `p : ℝ → ℝ` of class `C²`,
valued in `[0,1]`, supported in the segment `(N, (1+θ)N]` of (4.12), with the (4.14) second
derivative bound, and for `1/2 ≤ σ ≤ 2`, `n > 0`,

  `p(n) = (1/2π) ∫_ℝ p̂(σ+iτ) n^{-(σ+iτ)} dτ`,   `p̂(s) = ∫_0^∞ p(u) u^{s-1} du`.

Mathlib's `mellinInv_mellin_eq` gives the inversion for a Mellin transform with a convergent
defining integral and a vertically integrable transform; the content here is to *discharge* those
two hypotheses for the mollifier of (4.12): convergence from the compact support, and vertical
integrability from the decay `mellin_decay` (which in turn comes from the two integrations by parts
`mellin_ibp` at the vanishing endpoints `p(N) = p((1+θ)N) = p'(N) = p'((1+θ)N) = 0`).
This is the step that produces the contour representation `p(n) = (1/2πi)∫ p̂(s)n^{-s}ds` of §16.
-/
import Mathlib
import Submission.Work.FIArea5.S16.mellin_decay
import Submission.Work.FIArea5.S16.p_endpoint_zero

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace Work.FIArea5.S16

open MeasureTheory intervalIntegral
open scoped BigOperators Topology

noncomputable section

/-- The canonical `ℂ`-scalar multiplication on `ℂ` is multiplication (used to convert the `•`'s
of Mathlib's `mellinInv` into `*`). -/
lemma smul_eq_mul_complex (a b : ℂ) : a • b = a * b := rfl

/-- The Mellin transform of the mollifier, written with the integrand in the order
`p(u)·u^{s-1}`. -/
lemma mellin_mollifier_eq (p : ℝ → ℝ) (s : ℂ) :
    mellin (fun u : ℝ => (p u : ℂ)) s
      = ∫ u in Set.Ioi (0 : ℝ), (p u : ℂ) * (u : ℂ) ^ (s - 1) := by
  rw [mellin]
  refine setIntegral_congr_fun measurableSet_Ioi fun u _ => ?_
  rw [smul_eq_mul, mul_comm]

/-- **Support reduction**: for a mollifier supported in `(N, (1+θ)N]`, the Mellin integral over
`(0,∞)` is the interval integral over `[N, (1+θ)N]`. -/
lemma mellin_mollifier_eq_interval {p : ℝ → ℝ} {N θ : ℝ} (hN : 0 < N) (hθ : 0 < θ)
    (hsupp : ∀ u, p u ≠ 0 → N < u ∧ u ≤ (1 + θ) * N) (s : ℂ) :
    mellin (fun u : ℝ => (p u : ℂ)) s
      = ∫ u in N..((1 + θ) * N), (p u : ℂ) * (u : ℂ) ^ (s - 1) := by
  have hNle : N ≤ (1 + θ) * N := by nlinarith
  have hzero_out : ∀ u : ℝ, u ∉ Set.Ioc N ((1 + θ) * N) →
      (u : ℂ) ^ (s - 1) • (p u : ℂ) = 0 := by
    intro u hu
    by_cases h1 : u ≤ N
    · have hp : p u = 0 := by
        by_contra h
        exact absurd (hsupp u h).1 (not_lt.mpr h1)
      simp [hp]
    · push_neg at h1
      have h2 : (1 + θ) * N < u := by
        by_contra h2
        exact hu ⟨h1, not_lt.mp h2⟩
      have hp : p u = 0 := by
        by_contra h
        exact absurd (hsupp u h).2 (not_le.mpr h2)
      simp [hp]
  have hzero_out0 : ∀ u : ℝ, u ∉ Set.Ioi (0 : ℝ) →
      (u : ℂ) ^ (s - 1) • (p u : ℂ) = 0 := by
    intro u hu
    have hp : p u = 0 := by
      by_contra h
      exact hu (lt_of_le_of_lt hN.le (hsupp u h).1)
    simp [hp]
  calc mellin (fun u : ℝ => (p u : ℂ)) s
      = ∫ u in Set.Ioi (0 : ℝ), (u : ℂ) ^ (s - 1) • (p u : ℂ) := rfl
    _ = ∫ u : ℝ, (u : ℂ) ^ (s - 1) • (p u : ℂ) :=
        setIntegral_eq_integral_of_forall_compl_eq_zero hzero_out0
    _ = ∫ u in Set.Ioc N ((1 + θ) * N), (u : ℂ) ^ (s - 1) • (p u : ℂ) :=
        (setIntegral_eq_integral_of_forall_compl_eq_zero hzero_out).symm
    _ = ∫ u in N..((1 + θ) * N), (u : ℂ) ^ (s - 1) • (p u : ℂ) :=
        (intervalIntegral.integral_of_le hNle).symm
    _ = ∫ u in N..((1 + θ) * N), (p u : ℂ) * (u : ℂ) ^ (s - 1) := by
        refine intervalIntegral.integral_congr fun u _ => ?_
        rw [smul_eq_mul, mul_comm]

/-- The Mellin transform of the mollifier converges in the whole half-plane `re s > 0`. -/
lemma mellinConvergent_mollifier {p : ℝ → ℝ} {N θ : ℝ} (hN : 0 < N) (hθ : 0 < θ)
    (hpC : ContDiff ℝ 2 p) (hsupp : ∀ u, p u ≠ 0 → N < u ∧ u ≤ (1 + θ) * N)
    {σ : ℝ} (hσ : 0 < σ) :
    MellinConvergent (fun u : ℝ => (p u : ℂ)) (σ : ℂ) := by
  have hfc : LocallyIntegrableOn (fun u : ℝ => (p u : ℂ)) (Set.Ioi 0) :=
    ContinuousOn.locallyIntegrableOn (f := fun u : ℝ => (p u : ℂ)) (K := Set.Ioi (0 : ℝ))
      (fun x _ =>
        ((Complex.continuous_ofReal.comp hpC.continuous).continuousAt).continuousWithinAt)
      measurableSet_Ioi
  have htop : (fun u : ℝ => (p u : ℂ)) =O[Filter.atTop] (fun u : ℝ => u ^ (-(σ + 1))) := by
    refine Asymptotics.IsBigO.of_bound 0 ?_
    filter_upwards [Filter.eventually_gt_atTop ((1 + θ) * N)] with u hu
    have hp : p u = 0 := by
      by_contra h
      exact absurd (hsupp u h).2 (not_le.mpr hu)
    simp [hp]
  have hbot : (fun u : ℝ => (p u : ℂ)) =O[𝓝[>] (0 : ℝ)] (fun u : ℝ => u ^ (-(σ - 1))) := by
    refine Asymptotics.IsBigO.of_bound 0 ?_
    have hev : ∀ᶠ u : ℝ in 𝓝[>] (0 : ℝ), u < N := by
      rw [eventually_nhdsWithin_iff]
      filter_upwards [Iio_mem_nhds hN] with u hu _
      exact hu
    filter_upwards [hev] with u hu
    have hp : p u = 0 := by
      by_contra h
      exact absurd (hsupp u h).1 (not_lt.mpr hu.le)
    simp [hp]
  refine mellinConvergent_of_isBigO_rpow (a := σ + 1) (b := σ - 1) hfc htop ?_ hbot ?_
  · rw [Complex.ofReal_re]; linarith
  · rw [Complex.ofReal_re]; linarith

/-- **Vertical integrability** of the Mellin transform of the mollifier on the line `re s = σ`,
for `1/2 ≤ σ ≤ 2`: this is the decay `mellin_decay` (16.28), together with the convergence input. -/
lemma verticalIntegrable_mellin_mollifier {p : ℝ → ℝ} {N θ : ℝ} (hN : 0 < N) (hθ : 0 < θ)
    (hθ1 : θ ≤ 1) (hpC : ContDiff ℝ 2 p) (hp0 : ∀ u, 0 ≤ p u) (hp1 : ∀ u, p u ≤ 1)
    (hsupp : ∀ u, p u ≠ 0 → N < u ∧ u ≤ (1 + θ) * N)
    (hd2 : ∀ u, |iteratedDeriv 2 p u| ≤ 1048576 / (θ * N) ^ 2)
    {σ : ℝ} (hσ1 : 1 / 2 ≤ σ) (hσ2 : σ ≤ 2) :
    Complex.VerticalIntegrable (mellin (fun u : ℝ => (p u : ℂ))) σ := by
  have hσ0 : 0 < σ := by linarith
  have hfc : LocallyIntegrableOn (fun u : ℝ => (p u : ℂ)) (Set.Ioi 0) :=
    ContinuousOn.locallyIntegrableOn (f := fun u : ℝ => (p u : ℂ)) (K := Set.Ioi (0 : ℝ))
      (fun x _ =>
        ((Complex.continuous_ofReal.comp hpC.continuous).continuousAt).continuousWithinAt)
      measurableSet_Ioi
  have htop : (fun u : ℝ => (p u : ℂ)) =O[Filter.atTop] (fun u : ℝ => u ^ (-(σ + 1))) := by
    refine Asymptotics.IsBigO.of_bound 0 ?_
    filter_upwards [Filter.eventually_gt_atTop ((1 + θ) * N)] with u hu
    have hp : p u = 0 := by
      by_contra h
      exact absurd (hsupp u h).2 (not_le.mpr hu)
    simp [hp]
  have hbot : (fun u : ℝ => (p u : ℂ)) =O[𝓝[>] (0 : ℝ)] (fun u : ℝ => u ^ (-(σ - 1))) := by
    refine Asymptotics.IsBigO.of_bound 0 ?_
    have hev : ∀ᶠ u : ℝ in 𝓝[>] (0 : ℝ), u < N := by
      rw [eventually_nhdsWithin_iff]
      filter_upwards [Iio_mem_nhds hN] with u hu _
      exact hu
    filter_upwards [hev] with u hu
    have hp : p u = 0 := by
      by_contra h
      exact absurd (hsupp u h).1 (not_lt.mpr hu.le)
    simp [hp]
  -- the pointwise decay, a.e. (the single point `y = 0` is irrelevant)
  have hpt : ∀ᵐ y : ℝ, ‖mellin (fun u : ℝ => (p u : ℂ)) ((σ : ℂ) + (y : ℂ) * Complex.I)‖
      ≤ 10000000 * θ * N ^ σ * (1 + (θ * y) ^ 2)⁻¹ := by
    have hne : ∀ᵐ y : ℝ, y ≠ 0 := by
      rw [MeasureTheory.ae_iff]
      simp
    filter_upwards [hne] with y hy
    rw [mellin_mollifier_eq_interval hN hθ hsupp]
    exact mellin_decay p N θ hN hθ hθ1 hpC hp0 hp1 hsupp hd2 σ y hσ1 hσ2 hy
  -- the dominating function is integrable
  have hbase : Integrable (fun y : ℝ => 10000000 * θ * N ^ σ * (1 + (θ * y) ^ 2)⁻¹) :=
    (integrable_inv_one_add_sq.comp_mul_left' hθ.ne').const_mul _
  -- the target function is continuous (Mellin transform of a compactly supported function)
  have hcont : Continuous fun y : ℝ =>
      mellin (fun u : ℝ => (p u : ℂ)) ((σ : ℂ) + (y : ℂ) * Complex.I) := by
    refine continuous_iff_continuousAt.mpr fun y => ?_
    have hd := mellin_differentiableAt_of_isBigO_rpow (a := σ + 1) (b := σ - 1)
      (s := (σ : ℂ) + (y : ℂ) * Complex.I)
      hfc htop (by rw [show ((σ : ℂ) + (y : ℂ) * Complex.I).re = σ by simp]; linarith)
      hbot (by rw [show ((σ : ℂ) + (y : ℂ) * Complex.I).re = σ by simp]; linarith)
    have h2 : ContinuousAt (fun y : ℝ => ((σ : ℂ) + (y : ℂ) * Complex.I)) y := by fun_prop
    have h3 : ContinuousAt ((mellin (fun u : ℝ => (p u : ℂ))) ∘
        (fun y : ℝ => ((σ : ℂ) + (y : ℂ) * Complex.I))) y :=
      ContinuousAt.comp hd.continuousAt h2
    exact h3
  exact hbase.mono' hcont.aestronglyMeasurable hpt

/-- **Mellin inversion for the radius mollifier of (16.28).**  For `p : ℝ → ℝ` of class `C²`,
valued in `[0,1]`, supported in `(N, (1+θ)N]`, with the (4.14) second-derivative bound, and for
`1/2 ≤ σ ≤ 2` and `n > 0`,
  `p(n) = (1/2π) · ∫_ℝ (∫_0^∞ p(u) u^{σ+iτ-1} du) · n^{-(σ+iτ)} dτ`. -/
theorem mellin_inversion (p : ℝ → ℝ) (N θ σ : ℝ) (n : ℝ)
    (hN : 0 < N) (hθ : 0 < θ) (hθ1 : θ ≤ 1) (hpC : ContDiff ℝ 2 p) (hp0 : ∀ u, 0 ≤ p u)
    (hp1 : ∀ u, p u ≤ 1) (hsupp : ∀ u, p u ≠ 0 → N < u ∧ u ≤ (1 + θ) * N)
    (hd2 : ∀ u, |iteratedDeriv 2 p u| ≤ 1048576 / (θ * N) ^ 2)
    (hσ1 : 1 / 2 ≤ σ) (hσ2 : σ ≤ 2) (hn : 0 < n) :
    (p n : ℂ) = (1 / (2 * Real.pi)) * ∫ τ : ℝ,
      (∫ u in Set.Ioi (0 : ℝ), (p u : ℂ) * (u : ℂ) ^ ((σ : ℂ) + (τ : ℂ) * Complex.I - 1))
        * (n : ℂ) ^ (-((σ : ℂ) + (τ : ℂ) * Complex.I)) := by
  have hσ0 : 0 < σ := by linarith
  have hconv := mellinConvergent_mollifier (p := p) hN hθ hpC hsupp hσ0
  have hvert := verticalIntegrable_mellin_mollifier (N := N) (θ := θ)
    hN hθ hθ1 hpC hp0 hp1 hsupp hd2 hσ1 hσ2
  have hcont : ContinuousAt (fun u : ℝ => (p u : ℂ)) n :=
    (Complex.continuous_ofReal.comp hpC.continuous).continuousAt
  have h := mellinInv_mellin_eq σ (fun u : ℝ => (p u : ℂ)) hn hconv hvert hcont
  rw [← h]
  unfold mellinInv
  rw [Complex.real_smul]
  simp only [smul_eq_mul_complex]
  rw [show ((1 / (2 * Real.pi) : ℝ) : ℂ) = (1 / (2 * ↑Real.pi) : ℂ) by push_cast; ring]
  congr 1
  refine MeasureTheory.integral_congr_ae ?_
  filter_upwards with τ
  rw [mellin_mollifier_eq, mul_comm]

end

end Work.FIArea5.S16
