import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Submission.Work.FTS.StrongPersist.N6Trans.OpenTwins.bt_prod_integrable_open
import Submission.Work.FTS_RegExport.RXT.SysAux.explicit_piece_bounds
import Submission.Work.Spaces.ThetaAgmon.agmon_interval

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.EpsLocalPStar

open scoped Real Topology
open MeasureTheory Set Filter

set_option maxHeartbeats 2000000

/-! ## The angular trace of a `C¹` slice at `θ = π/2`, with the weighted Hardy rate

This file proves the lemma `SliceTracePiO`: for a function `u` of class `C¹` on `(0,π/2)` whose
weighted angular energy `(u')² sin(2·)^{2-γ}` is integrable on `Iθ = [0,π/2]`, the slice `u` has
a trace `mu` at `θ = π/2⁻`, and the convergence happens at the weighted Hardy rate

  `(u θ - mu)² ≤ (100/(γ-1)) · sin(2θ)^{γ-1} · ∫_{Iθ} (u')² sin(2σ)^{2-γ}`,   `π/4 < θ < π/2`,

where `γ = Work.Spaces.gam α = 1 + α/10`.

The mathematics is the classical weighted Hardy argument, run from the *right* endpoint.  On
`[a,b] ⊆ [π/4, π/2)` the fundamental theorem of calculus and the weighted Cauchy–Schwarz
inequality (`Work.Spaces.hardyZ_interval_integral_mul_le_sqrt`) give

  `|u b - u a| ≤ √(∫_a^b (u')² sin(2·)^{2-γ}) · √(∫_a^b sin(2·)^{γ-2})`,

the first factor is `≤ √A` with `A = ∫_{Iθ} (u')² sin(2·)^{2-γ}`
(`Work.FTS.H2.interval_integral_le_setIntegral_Iθ`), and the second is
`≤ √(100 sin(2a)^{γ-1}/(γ-1))` (`SinPowIntegralPiO`: here `sin(2·)` *decreases* on
`[π/4, π/2]`, so the weight integral is controlled by the *left* endpoint `a`).  The resulting
oscillation bound vanishes as `a → π/2⁻`, so the slice is Cauchy at `π/2` and its limit `mu`
obeys the same bound (`TraceOfOscPiO`); squaring it is the stated inequality. -/

/-- `sin (2θ) ≥ 0` on the closed angular interval `Iθ = [0,π/2]`. -/
private lemma sin_two_nonneg_Iθ_core {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) : 0 ≤ Real.sin (2 * θ) :=
  Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])

/-- **The weighted oscillation bound at `π/2`.**  For `u` of class `C¹` on `(0,π/2)` whose
weighted angular energy `(u')² sin(2·)^{2-γ}` is integrable on `Iθ`, and `1 < γ`,

  `|u b - u a| ≤ √(A · 100/(γ-1)) · sin(2a)^{(γ-1)/2}`   for `π/4 ≤ a ≤ b < π/2`,

with `A = ∫_{Iθ} (u')² sin(2·)^{2-γ}`.  This is the rate at which the slice is Cauchy at `π/2`;
the hypothesis `hPow` is the elementary `sin`-power integral bound `SinPowIntegralPiO`. -/
private lemma osc_bound_pio {γ : ℝ} (hγ1 : 1 < γ) {u : ℝ → ℝ}
    (hsm : ContDiffOn ℝ 1 u (Set.Ioo 0 (Real.pi / 2)))
    (hint : MeasureTheory.IntegrableOn
      (fun σ => (deriv u σ) ^ 2 * (Real.sin (2 * σ)) ^ (2 - γ)) Work.Spaces.Iθ)
    (hPow : ∀ {a b : ℝ}, Real.pi / 4 ≤ a → a ≤ b → b ≤ Real.pi / 2 →
      ∫ x in a..b, (Real.sin (2 * x)) ^ (γ - 2)
        ≤ (100 / (γ - 1)) * (Real.sin (2 * a)) ^ (γ - 1)) :
    ∀ a b : ℝ, Real.pi / 4 ≤ a → a ≤ b → b < Real.pi / 2 →
      |u b - u a| ≤ Real.sqrt ((∫ σ in Work.Spaces.Iθ,
          (deriv u σ) ^ 2 * (Real.sin (2 * σ)) ^ (2 - γ)) * (100 / (γ - 1)))
        * (Real.sin (2 * a)) ^ ((γ - 1) / 2) := by
  have hne0 : (1 : WithTop ℕ∞) ≠ 0 := by norm_num
  have hAnn : 0 ≤ ∫ σ in Work.Spaces.Iθ,
      (deriv u σ) ^ 2 * (Real.sin (2 * σ)) ^ (2 - γ) :=
    setIntegral_nonneg measurableSet_Icc fun σ hσ =>
      mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (sin_two_nonneg_Iθ_core hσ) _)
  have hCnn : 0 ≤ 100 / (γ - 1) := by positivity
  intro a b ha hab hb
  have ha0 : (0 : ℝ) < a := lt_of_lt_of_le (by linarith [Real.pi_pos] : (0:ℝ) < Real.pi / 4) ha
  have hb2 : b < Real.pi / 2 := hb
  -- the interval `[a,b]` sits strictly inside `(0,π/2)`
  have hsub : Set.uIcc a b ⊆ Set.Ioo (0 : ℝ) (Real.pi / 2) := by
    intro x hx
    rw [Set.uIcc_of_le hab] at hx
    exact ⟨lt_of_lt_of_le ha0 hx.1, lt_of_le_of_lt hx.2 hb2⟩
  have hsubI : Set.Icc a b ⊆ Set.Ioo (0 : ℝ) (Real.pi / 2) := by
    rw [← Set.uIcc_of_le hab]; exact hsub
  have hsinpos : ∀ s ∈ Set.uIcc a b, 0 < Real.sin (2 * s) := by
    intro s hs
    exact Real.sin_pos_of_pos_of_lt_pi (by linarith [(hsub hs).1])
      (by linarith [(hsub hs).2, Real.pi_pos])
  have hsincont : ∀ c : ℝ,
      ContinuousOn (fun s : ℝ => (Real.sin (2 * s)) ^ c) (Set.uIcc a b) := fun c =>
    ((Real.continuous_sin.comp (continuous_const.mul continuous_id)).continuousOn).rpow_const
      (fun s hs => Or.inl (ne_of_gt (hsinpos s hs)))
  -- continuity, differentiability and the fundamental theorem of calculus on `[a,b]`
  have hcont : ContinuousOn u (Set.Icc a b) := hsm.continuousOn.mono hsubI
  have hpthcont : ContinuousOn (deriv u) (Set.uIcc a b) :=
    (hsm.continuousOn_deriv_of_isOpen isOpen_Ioo le_rfl).mono hsub
  have hderiv : ∀ x ∈ Set.Ioo a b, HasDerivAt u (deriv u x) x := by
    intro x hx
    have hx' : x ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) :=
      ⟨lt_trans ha0 hx.1, lt_of_lt_of_le hx.2 hb2.le⟩
    exact ((hsm.differentiableOn hne0).differentiableAt
      (isOpen_Ioo.mem_nhds hx')).hasDerivAt
  have hFTC : ∫ s in a..b, deriv u s = u b - u a :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hab hcont hderiv
      hpthcont.intervalIntegrable
  -- weighted Cauchy–Schwarz
  have hcs := Work.Spaces.hardyZ_interval_integral_mul_le_sqrt a b hab
    (hpthcont.mul (hsincont ((2 - γ) / 2))) (hsincont ((γ - 2) / 2))
  -- the first Cauchy–Schwarz factor is at most the weighted energy `A`
  have hAint : ∫ s in a..b,
      (deriv u s * (Real.sin (2 * s)) ^ ((2 - γ) / 2)) ^ 2
      ≤ ∫ σ in Work.Spaces.Iθ, (deriv u σ) ^ 2 * (Real.sin (2 * σ)) ^ (2 - γ) := by
    have hEq : ∫ s in a..b, (deriv u s * (Real.sin (2 * s)) ^ ((2 - γ) / 2)) ^ 2
        = ∫ s in a..b, (deriv u s) ^ 2 * (Real.sin (2 * s)) ^ (2 - γ) := by
      refine intervalIntegral.integral_congr fun s hs => ?_
      have hsin : 0 < Real.sin (2 * s) := hsinpos s hs
      have h1 : ((Real.sin (2 * s)) ^ ((2 - γ) / 2)) ^ 2 = (Real.sin (2 * s)) ^ (2 - γ) := by
        rw [pow_two, ← Real.rpow_add hsin]
        congr 1
        ring
      rw [mul_pow, h1]
    rw [hEq]
    exact Work.FTS.H2.interval_integral_le_setIntegral_Iθ ha0 hab hb2 hint
      (fun x hx => mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (sin_two_nonneg_Iθ_core hx) _))
  -- the second Cauchy–Schwarz factor is the `sin`-power weight bound
  have hBint : ∫ s in a..b, ((Real.sin (2 * s)) ^ ((γ - 2) / 2)) ^ 2
      ≤ (100 / (γ - 1)) * (Real.sin (2 * a)) ^ (γ - 1) := by
    have hEq : ∫ s in a..b, ((Real.sin (2 * s)) ^ ((γ - 2) / 2)) ^ 2
        = ∫ s in a..b, (Real.sin (2 * s)) ^ (γ - 2) := by
      refine intervalIntegral.integral_congr fun s hs => ?_
      have hsin : 0 < Real.sin (2 * s) := hsinpos s hs
      rw [pow_two, ← Real.rpow_add hsin]
      congr 1
      ring
    rw [hEq]
    exact hPow ha hab (le_of_lt hb)
  -- the two factors recombine into `u b - u a`
  have hprod : ∫ s in a..b,
      (deriv u s * (Real.sin (2 * s)) ^ ((2 - γ) / 2)) * (Real.sin (2 * s)) ^ ((γ - 2) / 2)
      = u b - u a := by
    rw [← hFTC]
    refine intervalIntegral.integral_congr fun s hs => ?_
    have hsin : 0 < Real.sin (2 * s) := hsinpos s hs
    rw [mul_assoc, ← Real.rpow_add hsin,
      show (2 - γ) / 2 + (γ - 2) / 2 = 0 by ring, Real.rpow_zero, mul_one]
  have hstep : |u b - u a| ≤ Real.sqrt (∫ σ in Work.Spaces.Iθ,
        (deriv u σ) ^ 2 * (Real.sin (2 * σ)) ^ (2 - γ))
      * Real.sqrt ((100 / (γ - 1)) * (Real.sin (2 * a)) ^ (γ - 1)) := by
    rw [← hprod]
    exact hcs.trans (mul_le_mul (Real.sqrt_le_sqrt hAint) (Real.sqrt_le_sqrt hBint)
      (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
  -- collect the two square roots into the single factor `√(A·100/(γ-1)) · sin(2a)^{(γ-1)/2}`
  refine hstep.trans (le_of_eq ?_)
  have hs0 : 0 ≤ Real.sin (2 * a) :=
    sin_two_nonneg_Iθ_core ⟨le_of_lt ha0, le_of_lt (lt_of_le_of_lt hab hb)⟩
  have hsqrt : Real.sqrt ((Real.sin (2 * a)) ^ (γ - 1)) = (Real.sin (2 * a)) ^ ((γ - 1) / 2) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hs0]
    congr 1
    ring
  calc Real.sqrt (∫ σ in Work.Spaces.Iθ, (deriv u σ) ^ 2 * (Real.sin (2 * σ)) ^ (2 - γ))
        * Real.sqrt ((100 / (γ - 1)) * (Real.sin (2 * a)) ^ (γ - 1))
      = Real.sqrt (∫ σ in Work.Spaces.Iθ, (deriv u σ) ^ 2 * (Real.sin (2 * σ)) ^ (2 - γ))
          * (Real.sqrt (100 / (γ - 1)) * Real.sqrt ((Real.sin (2 * a)) ^ (γ - 1))) := by
        rw [Real.sqrt_mul hCnn]
    _ = (Real.sqrt (∫ σ in Work.Spaces.Iθ, (deriv u σ) ^ 2 * (Real.sin (2 * σ)) ^ (2 - γ))
          * Real.sqrt (100 / (γ - 1))) * Real.sqrt ((Real.sin (2 * a)) ^ (γ - 1)) := by ring
    _ = Real.sqrt ((∫ σ in Work.Spaces.Iθ, (deriv u σ) ^ 2 * (Real.sin (2 * σ)) ^ (2 - γ))
          * (100 / (γ - 1))) * Real.sqrt ((Real.sin (2 * a)) ^ (γ - 1)) := by
        rw [Real.sqrt_mul hAnn]
    _ = Real.sqrt ((∫ σ in Work.Spaces.Iθ, (deriv u σ) ^ 2 * (Real.sin (2 * σ)) ^ (2 - γ))
          * (100 / (γ - 1))) * (Real.sin (2 * a)) ^ ((γ - 1) / 2) := by rw [hsqrt]

theorem SliceTracePiO {α : ℝ} (hα : α ∈ Set.Ioc 0 1) {u : ℝ → ℝ}
    (hsm : ContDiffOn ℝ 1 u (Set.Ioo 0 (Real.pi/2)))
    (hint : MeasureTheory.IntegrableOn
      (fun θ => (deriv u θ)^2 * (Real.sin (2*θ))^(2 - Work.Spaces.gam α)) Work.Spaces.Iθ) :
    ∃ mu : ℝ, Filter.Tendsto u (nhdsWithin (Real.pi/2) (Set.Iio (Real.pi/2))) (nhds mu) ∧
      ∀ θ ∈ Set.Ioo (Real.pi/4) (Real.pi/2),
      (u θ - mu)^2 ≤ 100/(Work.Spaces.gam α - 1) * (Real.sin (2*θ))^(Work.Spaces.gam α - 1)
        * ∫ σ in Work.Spaces.Iθ,
            (deriv u σ)^2 * (Real.sin (2*σ))^(2 - Work.Spaces.gam α) := by
  have hα0 : 0 < α := hα.1
  have hα1 : α ≤ 1 := hα.2
  have hg1 : 1 < Work.Spaces.gam α := by rw [Work.Spaces.gam]; linarith
  have hg2 : Work.Spaces.gam α ≤ 2 := by rw [Work.Spaces.gam]; linarith
  have hgp : 0 < Work.Spaces.gam α - 1 := by rw [Work.Spaces.gam]; linarith
  -- the weighted energy
  set A : ℝ := ∫ σ in Work.Spaces.Iθ,
      (deriv u σ)^2 * (Real.sin (2*σ))^(2 - Work.Spaces.gam α) with hAdef
  have hAnn : 0 ≤ A := by
    rw [hAdef]
    exact setIntegral_nonneg measurableSet_Icc fun σ hσ =>
      mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (sin_two_nonneg_Iθ_core hσ) _)
  have hKnn : 0 ≤ A * (100 / (Work.Spaces.gam α - 1)) :=
    mul_nonneg hAnn (by positivity)
  -- the oscillation estimate
  have hcore := osc_bound_pio (γ := Work.Spaces.gam α) hg1 hsm hint
    (fun {a b} ha hab hb => SinPowIntegralPiO hg1 hg2 ha hab hb)
  rw [← hAdef] at hcore
  -- the trace and its rate
  obtain ⟨mu, hmu, hbd⟩ := TraceOfOscPiO (u := u) (γ := Work.Spaces.gam α)
    (K := Real.sqrt (A * (100 / (Work.Spaces.gam α - 1)))) hgp (Real.sqrt_nonneg _) hcore
  refine ⟨mu, hmu, fun θ hθ => ?_⟩
  have h := hbd θ hθ
  rw [Real.sq_sqrt hKnn] at h
  calc (u θ - mu)^2
      ≤ (A * (100 / (Work.Spaces.gam α - 1)))
          * (Real.sin (2*θ))^(Work.Spaces.gam α - 1) := h
    _ = 100/(Work.Spaces.gam α - 1) * (Real.sin (2*θ))^(Work.Spaces.gam α - 1) * A := by ring

end Work.FTS.StrongEps.EpsLocalPStar
