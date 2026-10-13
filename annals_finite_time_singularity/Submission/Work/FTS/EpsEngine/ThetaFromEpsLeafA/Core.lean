import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.EpsEngine.ClassCStepEngine
import Submission.Work.FTS.EpsEngine.ThetaFromEpsLeafA.subst_kernel_iter
import Submission.Work.FTS.EpsEngine.ThetaFromEpsLeafA.mixed_routed_sq_le

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `ThetaFromEpsLeafA/Core` — the strip bound for an arbitrary angular truncation

This file contains the *generic* part of `sinpow_mixed_Jeps_le_strip`: the pointwise bound of the
routed slot of `J_ε g` by the strip energy of **any** truncation `h` which agrees with `g` on the
kernel window (`θ' = thShift θ p₂` with `|p₂| ≤ ε`).

Nothing here mentions `stripLo`/`stripHi`, so the file is independent of
`EpsEngine/ThetaFromEps.lean`; the two truncations are instantiated in
`sinpow_mixed_Jeps_le_strip.lean`.

## Route

* `mixed_routed_sq_le` (Cauchy–Schwarz, unweighted) turns the routed identity into
  `(mixed b a (J_ε g))² ≤ 4^a (∫ |KdK|) ∫ p, |KdK p| (g ∘ shift)²`; the factor `sin(2θ)^{1-γ}`
  is moved inside the `p`-integral.
* `subst_kernel_iter` rewrites the `p`-integral as a quadrant integral with Jacobian density
  `2/(z' sin 2θ')`.
* On the window the truncation agrees with `g`, and the pointwise density comparison
  `|KdK p| sin(2θ)^{1-γ} 2/(z' sin 2θ') ≤ K e^{γ-1} (epsW α z' θ')²` holds
  (`density_le_epsW`).
* `ofReal_EpsSq_eq_lintegral` identifies the resulting weighted quadrature with `EpsSq α h`.
-/

namespace Work.FTS.EpsEngine.ThetaFromEpsLeafA

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

open scoped Real Topology ENNReal
open MeasureTheory Set Filter

/-! ## Elementary weight facts -/

/-- `2 ≤ z·w(z)²` for `z > 0`: with `w z = (1+z)²/z²` this is `2 z³ ≤ (1+z)⁴`, a consequence of
`256 z³ ≤ 27 (1+z)⁴` (the factorisation `27(1+z)⁴ − 256z³ = (z−3)²(27z²+14z+3)`). -/
theorem two_le_mul_w_sq {z : ℝ} (hz : 0 < z) : 2 ≤ z * (Work.Spaces.w z) ^ 2 := by
  have hp : 256 * z ^ 3 ≤ 27 * (1 + z) ^ 4 := by
    have hfac : 27 * (1 + z) ^ 4 - 256 * z ^ 3
        = (z - 3) ^ 2 * (27 * z ^ 2 + 14 * z + 3) := by ring
    have h2 : 0 ≤ (z - 3) ^ 2 * (27 * z ^ 2 + 14 * z + 3) := by
      apply mul_nonneg (sq_nonneg _); nlinarith [sq_nonneg z]
    linarith
  have hz3 : 0 < z ^ 3 := pow_pos hz 3
  have hw : z * (Work.Spaces.w z) ^ 2 = (1 + z) ^ 4 / z ^ 3 := by
    rw [Work.Spaces.w, div_pow]
    field_simp
  rw [hw, le_div_iff₀ hz3]
  have h1 : (2 : ℝ) * z ^ 3 ≤ 256 * z ^ 3 := by nlinarith [hz3]
  nlinarith [h1, hp]

/-- `(epsW α z θ)² = w(z)² / sin(2θ)^γ` on the open quadrant. -/
theorem epsW_sq_eq {α θ z : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    (Work.FTS.StrongEps.epsW α z θ) ^ 2
      = (Work.Spaces.w z) ^ 2 / Real.sin (2 * θ) ^ (Work.Spaces.gam α) := by
  rw [Work.FTS.StrongEps.epsW, div_pow]
  congr 1
  rw [pow_two, ← Real.rpow_add (Work.FTS.StrongEps.sin_two_pos hθ)]
  congr 1
  ring

/-! ## A constant bound for the routed kernel -/

/-- The kernel datum `sigKd ρ M` vanishes outside the closed unit ball (the sharp Euclidean
support of `Kdr ρ a b`). -/
theorem sigKd_mem_closedBall {ρ : ℝ × ℝ → ℝ} (hρ : Work.FTS.StrongEps.IsSmoothKernel ρ) (M : ℕ)
    {q : ℝ × ℝ} (hq : Work.FTS.StrongEps.EpsE4Thr.sigKd ρ M q ≠ 0) :
    q ∈ Metric.closedBall (0 : ℝ × ℝ) 1 := by
  have hsupp := Work.FTS.StrongEps.EpsE4Thr.sigKd_support hρ M hq
  rw [Metric.mem_closedBall, dist_zero_right, Prod.norm_def, Real.norm_eq_abs, Real.norm_eq_abs]
  have h1 : |q.1| ≤ 1 := by
    rw [← sq_le_one_iff_abs_le_one]
    nlinarith [hsupp, sq_nonneg q.2]
  have h2 : |q.2| ≤ 1 := by
    rw [← sq_le_one_iff_abs_le_one]
    nlinarith [hsupp, sq_nonneg q.1]
  exact max_le h1 h2

/-- The kernel datum `sigKd ρ M` is bounded. -/
theorem exists_sigKd_bound {ρ : ℝ × ℝ → ℝ} (hρ : Work.FTS.StrongEps.IsSmoothKernel ρ) (M : ℕ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ q : ℝ × ℝ, Work.FTS.StrongEps.EpsE4Thr.sigKd ρ M q ≤ B := by
  obtain ⟨q₀, -, hmax⟩ := (isCompact_closedBall (0 : ℝ × ℝ) 1).exists_isMaxOn
    ((Metric.nonempty_closedBall).mpr (by norm_num : (0 : ℝ) ≤ 1))
    (Work.FTS.StrongEps.EpsE4Thr.sigKd_continuous hρ M).continuousOn
  refine ⟨Work.FTS.StrongEps.EpsE4Thr.sigKd ρ M q₀,
    Work.FTS.StrongEps.EpsE4Thr.sigKd_nonneg ρ M q₀, fun q => ?_⟩
  by_cases hq : Work.FTS.StrongEps.EpsE4Thr.sigKd ρ M q = 0
  · rw [hq]; exact Work.FTS.StrongEps.EpsE4Thr.sigKd_nonneg ρ M q₀
  · exact hmax (sigKd_mem_closedBall hρ M hq)

/-- The routed density `LamFull ρ ε c M` is bounded by a constant. -/
theorem LamFull_le_const {ρ : ℝ × ℝ → ℝ} (hρ : Work.FTS.StrongEps.IsSmoothKernel ρ) {ε c : ℝ}
    (hε : 0 < ε) (M : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ p : ℝ × ℝ, Work.FTS.StrongEps.EpsE4Thr.LamFull ρ ε c M p ≤ K := by
  obtain ⟨B, hBnn, hB⟩ := exists_sigKd_bound hρ M
  refine ⟨ε⁻¹ ^ M * Real.exp (4 * c * ε) * ε⁻¹ ^ 2 * B + 1, by positivity, fun p => ?_⟩
  have hℓ : Work.FTS.StrongEps.EpsE4Thr.LamFull ρ ε c M p
      = ε⁻¹ ^ M * Real.exp (4 * c * ε)
        * (ε⁻¹ ^ 2 * Work.FTS.StrongEps.EpsE4Thr.sigKd ρ M (ε⁻¹ • p)) := by
    rw [Work.FTS.StrongEps.EpsE4Thr.LamFull_eq, Work.FTS.StrongEps.EpsE4Thr.LamK,
      Work.FTS.StrongEps.Jker]
    try ring
  rw [hℓ]
  have h0 : 0 ≤ ε⁻¹ ^ M * Real.exp (4 * c * ε) := by positivity
  have h1 : ε⁻¹ ^ 2 * Work.FTS.StrongEps.EpsE4Thr.sigKd ρ M (ε⁻¹ • p) ≤ ε⁻¹ ^ 2 * B :=
    mul_le_mul_of_nonneg_left (hB (ε⁻¹ • p)) (by positivity)
  have h2 : 0 ≤ ε⁻¹ ^ M * Real.exp (4 * c * ε) * ε⁻¹ ^ 2 * B := by positivity
  calc ε⁻¹ ^ M * Real.exp (4 * c * ε)
        * (ε⁻¹ ^ 2 * Work.FTS.StrongEps.EpsE4Thr.sigKd ρ M (ε⁻¹ • p))
      ≤ ε⁻¹ ^ M * Real.exp (4 * c * ε) * (ε⁻¹ ^ 2 * B) := mul_le_mul_of_nonneg_left h1 h0
    _ ≤ ε⁻¹ ^ M * Real.exp (4 * c * ε) * ε⁻¹ ^ 2 * B + 1 := by linarith

/-- A constant bound for the routed kernel derivatives `KdK ρ ε a b`. -/
theorem KdK_abs_le_const {ρ : ℝ × ℝ → ℝ} (hρ : Work.FTS.StrongEps.IsSmoothKernel ρ) {ε : ℝ}
    (hε : 0 < ε) (hε1 : ε ≤ 1) (a b : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ p : ℝ × ℝ,
      |Work.FTS.StrongEps.EpsE4Thr.KdK ρ ε a b p| ≤ K := by
  obtain ⟨L, hL0, hL⟩ := LamFull_le_const (c := 0) hρ hε (a + b)
  refine ⟨max L 1, le_trans zero_le_one (le_max_right L 1), fun p => ?_⟩
  have h1 : |Work.FTS.StrongEps.EpsE4Thr.KdK ρ ε a b p|
      * Real.exp (2 * 0 * (|p.1| + |p.2|))
      ≤ Work.FTS.StrongEps.EpsE4Thr.LamFull ρ ε 0 (a + b) p :=
    Work.FTS.StrongEps.EpsE4Thr.abs_KdK_mul_exp_le_LamFull hρ hε hε1 (le_refl 0)
      (le_refl (a + b)) p
  rw [mul_zero, zero_mul, Real.exp_zero, mul_one] at h1
  exact le_trans (le_trans h1 (hL p)) (le_max_left _ _)

/-- The routed kernel `KdK ρ ε a b` is supported in the ball of radius `ε`; in particular
`|p.2| ≤ ε` wherever it does not vanish. -/
theorem KdK_support_snd {ρ : ℝ × ℝ → ℝ} (hρ : Work.FTS.StrongEps.IsSmoothKernel ρ) {ε : ℝ}
    (hε : 0 < ε) (hε1 : ε ≤ 1) (a b : ℕ) {p : ℝ × ℝ}
    (hp : Work.FTS.StrongEps.EpsE4Thr.KdK ρ ε a b p ≠ 0) : |p.2| ≤ ε := by
  have hLam : Work.FTS.StrongEps.EpsE4Thr.LamFull ρ ε 0 (a + b) p ≠ 0 := by
    intro h2
    have h3 := Work.FTS.StrongEps.EpsE4Thr.abs_KdK_mul_exp_le_LamFull hρ hε hε1 (le_refl 0)
      (le_refl (a + b)) p
    rw [mul_zero, zero_mul, Real.exp_zero, mul_one] at h3
    rw [h2] at h3
    exact hp (abs_eq_zero.mp (le_antisymm h3 (abs_nonneg _)))
  have h4 := Work.FTS.StrongEps.EpsE4Thr.LamFull_support (c := 0) hρ (a + b) hLam
  have h5 : |p.2| ≤ |ε| := by
    rw [← sq_le_sq]
    linarith [h4, sq_nonneg p.1]
  rwa [abs_of_nonneg hε.le] at h5

/-! ## The `θ`-comparison at the shifted point -/

/-- The log-coordinate relation `p₂ = log tan θ − log tan θ'` identifies `θ'` with the shifted
angle. -/
theorem thShift_eq_of_logrel {θ θ' p₂ : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2))
    (hθ' : θ' ∈ Set.Ioo 0 (Real.pi / 2))
    (hrel : p₂ = Real.log (Real.tan θ) - Real.log (Real.tan θ')) :
    Work.FTS.StrongEps.thShift θ p₂ = θ' := by
  have ht : 0 < Real.tan θ := Real.tan_pos_of_pos_of_lt_pi_div_two hθ.1 hθ.2
  have ht' : 0 < Real.tan θ' := Real.tan_pos_of_pos_of_lt_pi_div_two hθ'.1 hθ'.2
  have harct : Real.arctan (Real.tan θ') = θ' :=
    Real.arctan_tan (by linarith [Real.pi_pos, hθ'.1]) (by linarith [Real.pi_pos, hθ'.2])
  rw [Work.FTS.StrongEps.thShift, hrel, neg_sub, Real.exp_sub, Real.exp_log ht',
    Real.exp_log ht]
  have hmul : Real.tan θ * (Real.tan θ' / Real.tan θ) = Real.tan θ' := by
    field_simp
  rw [hmul, harct]

/-- The angular weight comparison on the window: `sin(2θ)^{1-γ} ≤ e^{γ-1} sin(2θ')^{1-γ}` when
`θ'` is the `p₂`-shift of `θ` and `|p₂| ≤ ε ≤ 1`, `γ ≥ 1`. -/
theorem sinpow_le_of_logrel {θ θ' p₂ γ ε : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2))
    (hθ' : θ' ∈ Set.Ioo 0 (Real.pi / 2)) (hp₂ : |p₂| ≤ ε) (hε : 0 ≤ ε) (hε1 : ε ≤ 1)
    (hγ : 1 ≤ γ) (hrel : p₂ = Real.log (Real.tan θ) - Real.log (Real.tan θ')) :
    Real.sin (2 * θ) ^ (1 - γ) ≤ Real.exp (γ - 1) * Real.sin (2 * θ') ^ (1 - γ) := by
  have h1 := Work.FTS.StrongEps.Traces.sin_rpow_thShift_le θ p₂ ε (1 - γ) hθ hε hp₂
  rw [thShift_eq_of_logrel hθ hθ' hrel] at h1
  refine h1.trans ?_
  refine mul_le_mul_of_nonneg_right ?_
    (Real.rpow_nonneg (le_of_lt (Work.FTS.StrongEps.sin_two_pos hθ')) _)
  rw [Real.exp_le_exp, abs_of_nonpos (by linarith : (1 : ℝ) - γ ≤ 0),
    show -(1 - γ) = γ - 1 by ring]
  exact mul_le_of_le_one_left (by linarith : (0 : ℝ) ≤ γ - 1) hε1

/-- **The density comparison.**  On the window (`|p₂| ≤ ε`, `θ'` the shift of `θ`),

  `Λ · sin(2θ)^{1-γ} · 2/(z' sin 2θ') ≤ (K e^{γ-1}) · (epsW α z' θ')²`

for any `0 ≤ Λ ≤ K`.  The gain `sin(2θ')^{γ-1} ≥ e^{-ε(γ-1)} sin(2θ)^{γ-1}` on the window is kept
(`Traces.sin_rpow_thShift_le`), and the remaining Jacobian is absorbed by `2 ≤ z' w(z')²`. -/
theorem density_le_epsW {α : ℝ} (hα : 0 ≤ α) {ε θ θ' p₂ z' Λ K : ℝ}
    (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) (hθ' : θ' ∈ Set.Ioo 0 (Real.pi / 2))
    (hε : 0 ≤ ε) (hε1 : ε ≤ 1) (hp₂ : |p₂| ≤ ε) (hz' : 0 < z')
    (hΛ0 : 0 ≤ Λ) (hK0 : 0 ≤ K) (hΛK : Λ ≤ K)
    (hrel : p₂ = Real.log (Real.tan θ) - Real.log (Real.tan θ')) :
    Λ * Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α) * (2 / (z' * Real.sin (2 * θ')))
      ≤ (K * Real.exp (Work.Spaces.gam α - 1)) * (Work.FTS.StrongEps.epsW α z' θ') ^ 2 := by
  have hγ1 : (1 : ℝ) ≤ Work.Spaces.gam α := by
    rw [Work.Spaces.gam]; linarith
  have hsin : 0 < Real.sin (2 * θ) := Work.FTS.StrongEps.sin_two_pos hθ
  have hsin' : 0 < Real.sin (2 * θ') := Work.FTS.StrongEps.sin_two_pos hθ'
  have hw0 : 0 ≤ Work.Spaces.w z' := by rw [Work.Spaces.w]; positivity
  have hSnn : 0 ≤ Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α) := Real.rpow_nonneg hsin.le _
  have hJnn : 0 ≤ 2 / (z' * Real.sin (2 * θ')) :=
    div_nonneg (by norm_num) (mul_nonneg hz'.le hsin'.le)
  have hss : Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α)
      ≤ Real.exp (Work.Spaces.gam α - 1) * Real.sin (2 * θ') ^ (1 - Work.Spaces.gam α) :=
    sinpow_le_of_logrel hθ hθ' hp₂ hε hε1 hγ1 hrel
  have hpure : Real.sin (2 * θ') ^ (1 - Work.Spaces.gam α)
        * (2 / (z' * Real.sin (2 * θ')))
      ≤ (Work.Spaces.w z') ^ 2 / Real.sin (2 * θ') ^ (Work.Spaces.gam α) := by
    rw [le_div_iff₀ (Real.rpow_pos_of_pos hsin' _)]
    have hA : Real.sin (2 * θ') ^ (1 - Work.Spaces.gam α)
        * Real.sin (2 * θ') ^ (Work.Spaces.gam α) = Real.sin (2 * θ') := by
      rw [← Real.rpow_add hsin',
        show (1 - Work.Spaces.gam α) + Work.Spaces.gam α = 1 by ring, Real.rpow_one]
    have h2z : (2 : ℝ) / z' ≤ (Work.Spaces.w z') ^ 2 := by
      rw [div_le_iff₀ hz']
      nlinarith [two_le_mul_w_sq hz']
    calc Real.sin (2 * θ') ^ (1 - Work.Spaces.gam α)
          * (2 / (z' * Real.sin (2 * θ'))) * Real.sin (2 * θ') ^ (Work.Spaces.gam α)
        = (Real.sin (2 * θ') ^ (1 - Work.Spaces.gam α)
            * Real.sin (2 * θ') ^ (Work.Spaces.gam α)) * (2 / (z' * Real.sin (2 * θ'))) := by
          ring
      _ = Real.sin (2 * θ') * (2 / (z' * Real.sin (2 * θ'))) := by rw [hA]
      _ = 2 / z' := by field_simp
      _ ≤ (Work.Spaces.w z') ^ 2 := h2z
  rw [epsW_sq_eq (α := α) (z := z') hθ']
  calc Λ * Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α) * (2 / (z' * Real.sin (2 * θ')))
      = (Λ * Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α)) * (2 / (z' * Real.sin (2 * θ'))) := by
        ring
    _ ≤ (K * (Real.exp (Work.Spaces.gam α - 1) * Real.sin (2 * θ') ^ (1 - Work.Spaces.gam α)))
          * (2 / (z' * Real.sin (2 * θ'))) :=
        mul_le_mul_of_nonneg_right (mul_le_mul hΛK hss hSnn hK0) hJnn
    _ = (K * Real.exp (Work.Spaces.gam α - 1))
          * (Real.sin (2 * θ') ^ (1 - Work.Spaces.gam α)
              * (2 / (z' * Real.sin (2 * θ')))) := by ring
    _ ≤ (K * Real.exp (Work.Spaces.gam α - 1))
          * ((Work.Spaces.w z') ^ 2 / Real.sin (2 * θ') ^ (Work.Spaces.gam α)) :=
        mul_le_mul_of_nonneg_left hpure (by positivity)

/-! ## The pointwise step of the substitution integral -/

/-- **The pointwise comparison in the `(z',θ')`-integral.**  On the open quadrant the integrand
produced by `subst_kernel_iter` is dominated by `(K e^{γ-1}) (epsW α z' θ')²` times the squared
truncation, *provided* the truncation `h` agrees with `g` at every point of the window. -/
theorem strip_pointwise_le {ρ : ℝ × ℝ → ℝ} (hρ : Work.FTS.StrongEps.IsSmoothKernel ρ) {α : ℝ}
    (hα : α ∈ Set.Ioc 0 1) {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) (a b : ℕ) {K : ℝ} (hK0 : 0 ≤ K)
    (hK : ∀ p : ℝ × ℝ, |Work.FTS.StrongEps.EpsE4Thr.KdK ρ ε b a p| ≤ K)
    {g h : Work.FTS.Galerkin.Fn} {θ z : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2))
    (hagr : ∀ z' θ' p₂ : ℝ, 0 < z' → θ' ∈ Set.Ioo 0 (Real.pi / 2) → |p₂| ≤ ε →
        p₂ = Real.log (Real.tan θ) - Real.log (Real.tan θ') → h z' θ' = g z' θ')
    {z' θ' : ℝ} (hz' : 0 < z') (hθ' : θ' ∈ Set.Ioo 0 (Real.pi / 2)) :
    ENNReal.ofReal (|Work.FTS.StrongEps.EpsE4Thr.KdK ρ ε b a
          (Real.log z - Real.log z', Real.log (Real.tan θ) - Real.log (Real.tan θ'))|)
        * ENNReal.ofReal (Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α) * (g z' θ') ^ 2)
        * ENNReal.ofReal (2 / (z' * Real.sin (2 * θ')))
      ≤ ENNReal.ofReal
          ((K * Real.exp (Work.Spaces.gam α - 1)) * (Work.FTS.StrongEps.epsW α z' θ') ^ 2)
        * ENNReal.ofReal ((h z' θ') ^ 2) := by
  set p₂ : ℝ := Real.log (Real.tan θ) - Real.log (Real.tan θ') with hp₂def
  set Λ : ℝ := |Work.FTS.StrongEps.EpsE4Thr.KdK ρ ε b a (Real.log z - Real.log z', p₂)|
    with hΛdef
  set S : ℝ := Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α) with hSdef
  set J : ℝ := 2 / (z' * Real.sin (2 * θ')) with hJdef
  set Cd : ℝ := K * Real.exp (Work.Spaces.gam α - 1) with hCddef
  have hSnn : 0 ≤ S := by
    rw [hSdef]
    exact Real.rpow_nonneg (le_of_lt (Work.FTS.StrongEps.sin_two_pos hθ)) _
  have hJnn : 0 ≤ J := by
    rw [hJdef]
    exact div_nonneg (by norm_num)
      (mul_nonneg hz'.le (le_of_lt (Work.FTS.StrongEps.sin_two_pos hθ')))
  have hCd0 : 0 ≤ Cd := by rw [hCddef]; positivity
  have hΛnn : 0 ≤ Λ := by rw [hΛdef]; exact abs_nonneg _
  have hgnn : 0 ≤ (g z' θ') ^ 2 := sq_nonneg _
  by_cases hΛ0 : Λ = 0
  · rw [hΛ0, ENNReal.ofReal_zero, zero_mul, zero_mul]
    exact bot_le
  · have hsupp : |p₂| ≤ ε := by
      rw [hΛdef] at hΛ0
      exact KdK_support_snd hρ hε hε1 b a (abs_ne_zero.mp hΛ0)
    have hrel : p₂ = Real.log (Real.tan θ) - Real.log (Real.tan θ') := by rw [hp₂def]
    have hagree : h z' θ' = g z' θ' := hagr z' θ' p₂ hz' hθ' hsupp hrel
    rw [hagree]
    have hdens : Λ * S * J ≤ Cd * (Work.FTS.StrongEps.epsW α z' θ') ^ 2 := by
      rw [hΛdef, hSdef, hJdef, hCddef]
      exact density_le_epsW hα.1.le hθ hθ' hε.le hε1 hsupp hz' (abs_nonneg _) hK0
        (hK (Real.log z - Real.log z', Real.log (Real.tan θ) - Real.log (Real.tan θ'))) hrel
    have hkey : Λ * (S * (g z' θ') ^ 2) * J
        ≤ (Cd * (Work.FTS.StrongEps.epsW α z' θ') ^ 2) * (g z' θ') ^ 2 := by
      calc Λ * (S * (g z' θ') ^ 2) * J = (Λ * S * J) * (g z' θ') ^ 2 := by ring
        _ ≤ (Cd * (Work.FTS.StrongEps.epsW α z' θ') ^ 2) * (g z' θ') ^ 2 :=
            mul_le_mul_of_nonneg_right hdens hgnn
    have e1 : ENNReal.ofReal Λ * ENNReal.ofReal (S * (g z' θ') ^ 2) * ENNReal.ofReal J
        = ENNReal.ofReal (Λ * (S * (g z' θ') ^ 2) * J) := by
      rw [← ENNReal.ofReal_mul hΛnn,
        ← ENNReal.ofReal_mul (mul_nonneg hΛnn (mul_nonneg hSnn hgnn))]
    calc ENNReal.ofReal Λ * ENNReal.ofReal (S * (g z' θ') ^ 2) * ENNReal.ofReal J
        = ENNReal.ofReal (Λ * (S * (g z' θ') ^ 2) * J) := e1
      _ ≤ ENNReal.ofReal ((Cd * (Work.FTS.StrongEps.epsW α z' θ') ^ 2) * (g z' θ') ^ 2) :=
          ENNReal.ofReal_le_ofReal hkey
      _ = ENNReal.ofReal (Cd * (Work.FTS.StrongEps.epsW α z' θ') ^ 2)
            * ENNReal.ofReal ((g z' θ') ^ 2) := by
          rw [ENNReal.ofReal_mul (mul_nonneg hCd0 (sq_nonneg _))]

/-! ## The generic strip bound -/

/-- **The generic bound.**  For any truncation `h` agreeing with `g` on the kernel window, the
weighted squared routed slot of `J_ε g` is bounded by `C · EpsSq α h`. -/
theorem core_bound {ρ : ℝ × ℝ → ℝ} (hρ : Work.FTS.StrongEps.IsSmoothKernel ρ) {α : ℝ}
    (hα : α ∈ Set.Ioc 0 1) {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) (a b : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ g : Work.FTS.Galerkin.Fn,
      (∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry g) Work.FTS.StrongEps.Quad) →
      ∀ z θ : ℝ, 0 < z → θ ∈ Set.Ioo 0 (Real.pi / 2) → ∀ h : Work.FTS.Galerkin.Fn,
        Work.FTS.StrongEps.EpsMem α h →
        (∀ z' θ' p₂ : ℝ, 0 < z' → θ' ∈ Set.Ioo 0 (Real.pi / 2) → |p₂| ≤ ε →
            p₂ = Real.log (Real.tan θ) - Real.log (Real.tan θ') → h z' θ' = g z' θ') →
        Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α)
            * (Work.Spaces.mixed b a (Work.FTS.StrongEps.Jeps ρ ε g) z θ) ^ 2
          ≤ C * Work.FTS.StrongEps.EpsSq α h := by
  obtain ⟨K, hK0, hK⟩ := KdK_abs_le_const hρ hε hε1 b a
  set Cd : ℝ := K * Real.exp (Work.Spaces.gam α - 1) with hCddef
  have hCd0 : 0 ≤ Cd := by rw [hCddef]; positivity
  set A : ℝ := (4 : ℝ) ^ a * ∫ p : ℝ × ℝ, |Work.FTS.StrongEps.EpsE4Thr.KdK ρ ε b a p|
    with hAdef
  have hAnn : 0 ≤ A := by
    rw [hAdef]
    exact mul_nonneg (by positivity) (integral_nonneg fun p => abs_nonneg _)
  refine ⟨A * Cd + 1, by positivity, ?_⟩
  intro g hg z θ hz hθI h hhm hagr
  set S : ℝ := Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α) with hSdef
  have hSnn : 0 ≤ S := by
    rw [hSdef]
    exact Real.rpow_nonneg (le_of_lt (Work.FTS.StrongEps.sin_two_pos hθI)) _
  set I : ℝ := ∫ p : ℝ × ℝ, |Work.FTS.StrongEps.EpsE4Thr.KdK ρ ε b a p|
      * (g (Work.FTS.StrongEps.zShift z p.1) (Work.FTS.StrongEps.thShift θ p.2)) ^ 2 with hIdef
  -- (1) Cauchy–Schwarz for the routed slot
  have hsq := mixed_routed_sq_le hρ hε hg hz hθI a b
  -- (2) move `sin^{1-γ}` inside the `p`-integral
  have hmove : S * (Work.Spaces.mixed b a (Work.FTS.StrongEps.Jeps ρ ε g) z θ) ^ 2
      ≤ A * ∫ p : ℝ × ℝ, |Work.FTS.StrongEps.EpsE4Thr.KdK ρ ε b a p|
          * (S * (g (Work.FTS.StrongEps.zShift z p.1)
              (Work.FTS.StrongEps.thShift θ p.2)) ^ 2) := by
    have hSI : S * I = ∫ p : ℝ × ℝ, |Work.FTS.StrongEps.EpsE4Thr.KdK ρ ε b a p|
        * (S * (g (Work.FTS.StrongEps.zShift z p.1)
            (Work.FTS.StrongEps.thShift θ p.2)) ^ 2) := by
      rw [hIdef, ← MeasureTheory.integral_const_mul]
      exact MeasureTheory.integral_congr_ae
        (Eventually.of_forall (fun p => by ring))
    calc S * (Work.Spaces.mixed b a (Work.FTS.StrongEps.Jeps ρ ε g) z θ) ^ 2
        ≤ S * (A * I) := mul_le_mul_of_nonneg_left hsq hSnn
      _ = A * (S * I) := by ring
      _ = A * ∫ p : ℝ × ℝ, |Work.FTS.StrongEps.EpsE4Thr.KdK ρ ε b a p|
            * (S * (g (Work.FTS.StrongEps.zShift z p.1)
                (Work.FTS.StrongEps.thShift θ p.2)) ^ 2) := by rw [hSI]
  -- (3) pass to `ℝ≥0∞`
  have h3 : ENNReal.ofReal (S * (Work.Spaces.mixed b a (Work.FTS.StrongEps.Jeps ρ ε g) z θ) ^ 2)
      ≤ ENNReal.ofReal A
        * ∫⁻ p : ℝ × ℝ, ENNReal.ofReal (|Work.FTS.StrongEps.EpsE4Thr.KdK ρ ε b a p|
            * (S * (g (Work.FTS.StrongEps.zShift z p.1)
                (Work.FTS.StrongEps.thShift θ p.2)) ^ 2)) := by
    refine (ENNReal.ofReal_le_ofReal hmove).trans ?_
    rw [ENNReal.ofReal_mul hAnn]
    refine mul_le_mul_of_nonneg_left ?_ bot_le
    exact Work.FTS.StrongEps.StepFacts.ofReal_integral_le_lintegral_ofReal
      (fun p => mul_nonneg (abs_nonneg _) (mul_nonneg hSnn (sq_nonneg _)))
  -- (4) product measure
  have h4 : (∫⁻ p : ℝ × ℝ, ENNReal.ofReal (|Work.FTS.StrongEps.EpsE4Thr.KdK ρ ε b a p|
          * (S * (g (Work.FTS.StrongEps.zShift z p.1)
              (Work.FTS.StrongEps.thShift θ p.2)) ^ 2)))
      ≤ ∫⁻ s : ℝ, ∫⁻ ζ : ℝ, ENNReal.ofReal (|Work.FTS.StrongEps.EpsE4Thr.KdK ρ ε b a (s, ζ)|)
          * ENNReal.ofReal (S * (g (Work.FTS.StrongEps.zShift z s)
              (Work.FTS.StrongEps.thShift θ ζ)) ^ 2) := by
    rw [MeasureTheory.Measure.volume_eq_prod ℝ ℝ]
    refine (MeasureTheory.lintegral_prod_le _).trans (le_of_eq ?_)
    refine MeasureTheory.lintegral_congr (fun s => MeasureTheory.lintegral_congr (fun ζ => ?_))
    rw [ENNReal.ofReal_mul (abs_nonneg _)]
  -- (5) the log-coordinate substitution
  have h5 := subst_kernel_iter (K := fun q : ℝ × ℝ =>
      ENNReal.ofReal (|Work.FTS.StrongEps.EpsE4Thr.KdK ρ ε b a q|)) hz hθI
    (fun z' θ' => ENNReal.ofReal (S * (g z' θ') ^ 2))
  -- (6) the pointwise density/strip comparison
  have h6 : (∫⁻ z' in Set.Ioi 0, ∫⁻ θ' in Set.Ioo 0 (Real.pi / 2),
        ENNReal.ofReal (|Work.FTS.StrongEps.EpsE4Thr.KdK ρ ε b a
              (Real.log z - Real.log z',
                Real.log (Real.tan θ) - Real.log (Real.tan θ'))|)
          * ENNReal.ofReal (S * (g z' θ') ^ 2)
          * ENNReal.ofReal (2 / (z' * Real.sin (2 * θ'))))
      ≤ ∫⁻ z' in Set.Ioi 0, ∫⁻ θ' in Set.Ioo 0 (Real.pi / 2),
          ENNReal.ofReal (Cd * (Work.FTS.StrongEps.epsW α z' θ') ^ 2)
            * ENNReal.ofReal ((h z' θ') ^ 2) := by
    refine MeasureTheory.setLIntegral_mono' measurableSet_Ioi (fun z' hz' => ?_)
    refine MeasureTheory.setLIntegral_mono' measurableSet_Ioo (fun θ' hθ' => ?_)
    rw [hSdef, hCddef]
    exact strip_pointwise_le hρ hα hε hε1 a b hK0 hK hθI hagr hz' ⟨hθ'.1, hθ'.2⟩
  -- (7) pull the constant `Cd` out
  have h7 : (∫⁻ z' in Set.Ioi 0, ∫⁻ θ' in Set.Ioo 0 (Real.pi / 2),
        ENNReal.ofReal (Cd * (Work.FTS.StrongEps.epsW α z' θ') ^ 2)
          * ENNReal.ofReal ((h z' θ') ^ 2))
      = ENNReal.ofReal Cd * (∫⁻ z' in Set.Ioi 0, ∫⁻ θ' in Set.Ioo 0 (Real.pi / 2),
          ENNReal.ofReal ((h z' θ' * Work.FTS.StrongEps.epsW α z' θ') ^ 2)) := by
    have hpt : ∀ z' θ' : ℝ,
        ENNReal.ofReal (Cd * (Work.FTS.StrongEps.epsW α z' θ') ^ 2)
            * ENNReal.ofReal ((h z' θ') ^ 2)
          = ENNReal.ofReal Cd
            * ENNReal.ofReal ((h z' θ' * Work.FTS.StrongEps.epsW α z' θ') ^ 2) := by
      intro z' θ'
      rw [ENNReal.ofReal_mul hCd0, mul_assoc,
        ← ENNReal.ofReal_mul (sq_nonneg (Work.FTS.StrongEps.epsW α z' θ'))]
      congr 1
      ring
    calc (∫⁻ z' in Set.Ioi 0, ∫⁻ θ' in Set.Ioo 0 (Real.pi / 2),
          ENNReal.ofReal (Cd * (Work.FTS.StrongEps.epsW α z' θ') ^ 2)
            * ENNReal.ofReal ((h z' θ') ^ 2))
        = ∫⁻ z' in Set.Ioi 0, ∫⁻ θ' in Set.Ioo 0 (Real.pi / 2),
            ENNReal.ofReal Cd
              * ENNReal.ofReal ((h z' θ' * Work.FTS.StrongEps.epsW α z' θ') ^ 2) := by
          refine MeasureTheory.lintegral_congr (fun z' =>
            MeasureTheory.lintegral_congr (fun θ' => hpt z' θ'))
      _ = ENNReal.ofReal Cd * (∫⁻ z' in Set.Ioi 0, ∫⁻ θ' in Set.Ioo 0 (Real.pi / 2),
            ENNReal.ofReal ((h z' θ' * Work.FTS.StrongEps.epsW α z' θ') ^ 2)) := by
          rw [show (∫⁻ z' in Set.Ioi 0, ∫⁻ θ' in Set.Ioo 0 (Real.pi / 2),
                ENNReal.ofReal Cd
                  * ENNReal.ofReal ((h z' θ' * Work.FTS.StrongEps.epsW α z' θ') ^ 2))
              = ∫⁻ z' in Set.Ioi 0, ENNReal.ofReal Cd
                  * (∫⁻ θ' in Set.Ioo 0 (Real.pi / 2),
                      ENNReal.ofReal ((h z' θ' * Work.FTS.StrongEps.epsW α z' θ') ^ 2)) from
                MeasureTheory.lintegral_congr (fun z' =>
                  MeasureTheory.lintegral_const_mul' _ _ ENNReal.ofReal_ne_top)]
          exact MeasureTheory.lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
  -- (8) identify the strip energy
  have h8 : (∫⁻ z' in Set.Ioi 0, ∫⁻ θ' in Set.Ioo 0 (Real.pi / 2),
        ENNReal.ofReal ((h z' θ' * Work.FTS.StrongEps.epsW α z' θ') ^ 2))
      ≤ ENNReal.ofReal (Work.FTS.StrongEps.EpsSq α h) := by
    rw [Work.FTS.StrongEps.EpsSrc.ofReal_EpsSq_eq_lintegral hhm]
    refine (MeasureTheory.lintegral_mono_set (s := Set.Ioi 0) (t := Work.Spaces.Iz)
      (f := fun z' : ℝ => ∫⁻ θ' in Set.Ioo 0 (Real.pi / 2),
        ENNReal.ofReal ((h z' θ' * Work.FTS.StrongEps.epsW α z' θ') ^ 2))
      (fun z' hz' => by
        simpa [Work.Spaces.Iz] using le_of_lt hz')).trans ?_
    refine MeasureTheory.lintegral_mono (fun z' =>
      MeasureTheory.lintegral_mono_set (s := Set.Ioo 0 (Real.pi / 2)) (t := Work.Spaces.Iθ)
        (f := fun θ' : ℝ => ENNReal.ofReal ((h z' θ' * Work.FTS.StrongEps.epsW α z' θ') ^ 2))
        (fun θ' hθ' => by
          simpa [Work.Spaces.Iθ] using (⟨hθ'.1.le, hθ'.2.le⟩ : θ' ∈ Set.Icc 0 (Real.pi / 2))))
  -- assembly
  have hbig : ENNReal.ofReal (S * (Work.Spaces.mixed b a (Work.FTS.StrongEps.Jeps ρ ε g) z θ) ^ 2)
      ≤ ENNReal.ofReal (A * Cd * Work.FTS.StrongEps.EpsSq α h) := by
    refine h3.trans ?_
    calc ENNReal.ofReal A
          * (∫⁻ p : ℝ × ℝ, ENNReal.ofReal (|Work.FTS.StrongEps.EpsE4Thr.KdK ρ ε b a p|
              * (S * (g (Work.FTS.StrongEps.zShift z p.1)
                  (Work.FTS.StrongEps.thShift θ p.2)) ^ 2)))
        ≤ ENNReal.ofReal A
            * (∫⁻ s : ℝ, ∫⁻ ζ : ℝ,
                ENNReal.ofReal (|Work.FTS.StrongEps.EpsE4Thr.KdK ρ ε b a (s, ζ)|)
                  * ENNReal.ofReal (S * (g (Work.FTS.StrongEps.zShift z s)
                      (Work.FTS.StrongEps.thShift θ ζ)) ^ 2)) :=
          mul_le_mul_of_nonneg_left h4 bot_le
      _ = ENNReal.ofReal A
            * (∫⁻ z' in Set.Ioi 0, ∫⁻ θ' in Set.Ioo 0 (Real.pi / 2),
                ENNReal.ofReal (|Work.FTS.StrongEps.EpsE4Thr.KdK ρ ε b a
                      (Real.log z - Real.log z',
                        Real.log (Real.tan θ) - Real.log (Real.tan θ'))|)
                  * ENNReal.ofReal (S * (g z' θ') ^ 2)
                  * ENNReal.ofReal (2 / (z' * Real.sin (2 * θ')))) := by rw [h5]
      _ ≤ ENNReal.ofReal A
            * (∫⁻ z' in Set.Ioi 0, ∫⁻ θ' in Set.Ioo 0 (Real.pi / 2),
                ENNReal.ofReal (Cd * (Work.FTS.StrongEps.epsW α z' θ') ^ 2)
                  * ENNReal.ofReal ((h z' θ') ^ 2)) :=
          mul_le_mul_of_nonneg_left h6 bot_le
      _ = ENNReal.ofReal A
            * (ENNReal.ofReal Cd * (∫⁻ z' in Set.Ioi 0, ∫⁻ θ' in Set.Ioo 0 (Real.pi / 2),
                ENNReal.ofReal ((h z' θ' * Work.FTS.StrongEps.epsW α z' θ') ^ 2))) := by
          rw [h7]
      _ ≤ ENNReal.ofReal A
            * (ENNReal.ofReal Cd * ENNReal.ofReal (Work.FTS.StrongEps.EpsSq α h)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h8 bot_le) bot_le
      _ = ENNReal.ofReal (A * Cd * Work.FTS.StrongEps.EpsSq α h) := by
          rw [ENNReal.ofReal_mul (mul_nonneg hAnn hCd0), ENNReal.ofReal_mul hAnn]
          ring
  have hreal : S * (Work.Spaces.mixed b a (Work.FTS.StrongEps.Jeps ρ ε g) z θ) ^ 2
      ≤ A * Cd * Work.FTS.StrongEps.EpsSq α h :=
    (ENNReal.ofReal_le_ofReal_iff (mul_nonneg (mul_nonneg hAnn hCd0)
      (Work.FTS.StrongEps.EpsSq_nonneg α h))).mp hbig
  calc S * (Work.Spaces.mixed b a (Work.FTS.StrongEps.Jeps ρ ε g) z θ) ^ 2
      ≤ A * Cd * Work.FTS.StrongEps.EpsSq α h := hreal
    _ ≤ (A * Cd + 1) * Work.FTS.StrongEps.EpsSq α h :=
        mul_le_mul_of_nonneg_right (by linarith)
          (Work.FTS.StrongEps.EpsSq_nonneg α h)

end Work.FTS.EpsEngine.ThetaFromEpsLeafA
