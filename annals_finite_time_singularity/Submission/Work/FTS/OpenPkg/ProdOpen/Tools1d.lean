/-
# `Work.FTS.OpenPkg.ProdOpen.Tools1d`

The two one-dimensional inequalities behind the open-quadrant product rule
`Work.FTS.OpenPkg.prod_field`.

In the class `Work.FTS.VocabO.HQo` (`SmoothOpen` + `HkMem`) there is *no* decay and *no*
boundary vanishing available, so neither of the two classical Hardy inequalities
(`Work.Spaces.HardyZ`, `Work.Spaces.HardyTheta`) can be applied.  What replaces them is the
**mean term** form: the boundary/decay defect is paid for by an average over a *fixed*
window, which is itself an `L²`-quantity and hence controlled by the `ℋ⁴`-norm.

* `sob_z_mean`: for a function `h` which is differentiable on `(0,∞)` with `h'` continuous,
  `h(z)² ≤ 2 (∫_{[1,2]} h² + ∫_0^∞ (z h'(z) w(z))² dz)`.
  (`z h'` is `D_z h`, and `∫_0^∞ (·)² w²` is the radial slot of the `ℋ⁴`-norm.)
* `sob_theta_mean`: for `h` differentiable on `(0,π/2)` with `deriv h` continuous,
  `h(θ)² ≤ 204 (∫_{Iθ} h² + (γ-1)⁻¹ ∫_{Iθ} (h')² sin(2·)^{2-γ})`.

Everything rests on `[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Submission.Work.Spaces.HardyZ
import Submission.Work.FTS.H2.OscSqLe
import Submission.Work.FTS.EllipticEst.OpenQDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.OpenPkg.ProdOpen

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

open Work.Spaces

/-! ## Elementary facts on the radial weight -/

theorem w_pos_of_pos {z : ℝ} (hz : 0 < z) : 0 < w z := by
  rw [w]
  positivity

theorem one_le_w_of_pos {z : ℝ} (hz : 0 < z) : (1 : ℝ) ≤ w z := by
  have h2 : (0 : ℝ) < z ^ 2 := by positivity
  rw [w, le_div_iff₀ h2]
  nlinarith [sq_nonneg z]

theorem w_mul_psi_eq' {h' : ℝ → ℝ} {x : ℝ} (hx : 0 < x) :
    (x * h' x * w x) * (x / (1 + x) ^ 2) = h' x := by
  have h1 : (1 + x) ≠ 0 := ne_of_gt (by linarith)
  have h2 : x ≠ 0 := ne_of_gt hx
  simp only [w]
  field_simp

/-! ## A minimiser of a continuous nonnegative function is at most its mean -/

theorem exists_min_le_mean {φ : ℝ → ℝ} {a b : ℝ} (hab : a < b)
    (hcont : ContinuousOn φ (Set.Icc a b)) :
    ∃ x ∈ Set.Icc a b, φ x ≤ (b - a)⁻¹ * ∫ t in a..b, φ t := by
  obtain ⟨x₀, hx₀, hmin⟩ := (isCompact_Icc (a := a) (b := b)).exists_isMinOn
    ⟨a, by simp only [Set.mem_Icc]; exact ⟨le_rfl, hab.le⟩⟩ hcont
  refine ⟨x₀, hx₀, ?_⟩
  have hint : IntervalIntegrable φ volume a b :=
    (show ContinuousOn φ (Set.uIcc a b) by rwa [Set.uIcc_of_le hab.le]).intervalIntegrable
  have hconst : IntervalIntegrable (fun _ : ℝ => φ x₀) volume a b := intervalIntegrable_const
  have hmono : ∫ t in a..b, φ x₀ ≤ ∫ t in a..b, φ t :=
    intervalIntegral.integral_mono_on hab.le hconst hint (fun t ht => hmin ht)
  have hval : ∫ t in a..b, φ x₀ = φ x₀ * (b - a) := by
    rw [intervalIntegral.integral_const, smul_eq_mul]; ring
  rw [hval] at hmono
  have hpos : 0 < b - a := sub_pos.mpr hab
  rw [inv_mul_eq_div, le_div_iff₀ hpos]
  linarith [hmono]

/-! ## The radial Hardy inequality with a fixed window -/

/-- **The radial Hardy inequality with a mean term.**  For `h` differentiable on `(0,∞)`
whose derivative `h'` is continuous there and whose weighted square is integrable,

  `h(z)² ≤ 2 (∫_{[1,2]} h² + ∫_{0}^{∞} (z h'(z) w(z))² dz)`.

The window `[1,2]` may be replaced by any interval of positive length on which `h²` is
controlled; it is fixed here since it is all the product rule needs. -/
theorem sob_z_mean :
    ∃ C : ℝ, 0 < C ∧ ∀ (h h' : ℝ → ℝ) (z : ℝ), 0 < z →
      (∀ x, 0 < x → HasDerivAt h (h' x) x) → ContinuousOn h' (Set.Ioi 0) →
      IntegrableOn (fun x => (x * h' x * w x) ^ 2) Iz →
      (h z) ^ 2 ≤ C * ((∫ x in (1 : ℝ)..2, (h x) ^ 2)
        + ∫ x in Iz, (x * h' x * w x) ^ 2) := by
  refine ⟨2, by norm_num, ?_⟩
  intro h h' z hz hder hcont hint
  -- `h` is continuous on `[1,2]`
  have hdiff : DifferentiableOn ℝ h (Set.Icc 1 2) := fun x hx =>
    (hder x (by linarith [hx.1])).differentiableAt.differentiableWithinAt
  have hcontI : ContinuousOn h (Set.Icc 1 2) := hdiff.continuousOn
  -- a minimiser of `h²` on `[1,2]`
  obtain ⟨z₀, hz₀mem, hz₀min⟩ :=
    exists_min_le_mean (φ := fun x => (h x) ^ 2) (a := 1) (b := 2) (by norm_num)
      (hcontI.pow 2)
  have hz₀pos : 0 < z₀ := by linarith [hz₀mem.1]
  have hmin : (h z₀) ^ 2 ≤ ∫ x in (1 : ℝ)..2, (h x) ^ 2 := by
    have h1 : (2 - 1 : ℝ)⁻¹ * ∫ t in (1 : ℝ)..2, (h t) ^ 2
        = ∫ x in (1 : ℝ)..2, (h x) ^ 2 := by norm_num
    rw [← h1]
    exact hz₀min
  -- the weighted square of the derivative is nonnegative, and dominates the interval integral
  set P : ℝ := ∫ x in Iz, (x * h' x * w x) ^ 2 with hP
  have hPnn : 0 ≤ P :=
    setIntegral_nonneg measurableSet_Ici fun x _ => sq_nonneg _
  -- the Cauchy–Schwarz step on the interval between `z₀` and `z`
  have hkey : (h z - h z₀) ^ 2 ≤ P := by
    obtain ⟨a, b, hab, hapos, hcases⟩ :
        ∃ a b : ℝ, a ≤ b ∧ 0 < a ∧ ((a = z ∧ b = z₀) ∨ (a = z₀ ∧ b = z)) := by
      rcases le_total z₀ z with hle | hle
      · exact ⟨z₀, z, hle, hz₀pos, Or.inr ⟨rfl, rfl⟩⟩
      · exact ⟨z, z₀, hle, hz, Or.inl ⟨rfl, rfl⟩⟩
    -- the derivative of `h` on `[a,b]`
    have hder' : ∀ x ∈ Set.Icc a b, HasDerivAt h (h' x) x := fun x hx =>
      hder x (by linarith [hx.1])
    have hcontI' : ContinuousOn h' (Set.Icc a b) :=
      hcont.mono (fun x hx => Set.mem_Ioi.mpr (by linarith [hx.1]))
    have hcontI'' : ContinuousOn h' (Set.uIcc a b) := by rwa [Set.uIcc_of_le hab]
    -- the FTC
    have hFTC : ∫ x in a..b, h' x = h b - h a := by
      refine intervalIntegral.integral_eq_sub_of_hasDerivAt ?_ hcontI''.intervalIntegrable
      intro x hx
      rw [Set.uIcc_of_le hab] at hx
      exact hder x (by linarith [hx.1])
    -- the Cauchy–Schwarz inequality
    have hcontA : ContinuousOn (fun x => x * h' x * w x) (Set.uIcc a b) := by
      rw [Set.uIcc_of_le hab]
      refine ContinuousOn.mul (ContinuousOn.mul continuousOn_id hcontI') ?_
      unfold w
      refine ContinuousOn.div ((continuousOn_const.add continuousOn_id).pow 2)
        (continuousOn_id.pow 2) ?_
      intro x hx
      exact pow_ne_zero 2 (ne_of_gt (by linarith [hx.1]))
    have hcontψ : ContinuousOn (fun x => x / (1 + x) ^ 2) (Set.uIcc a b) := by
      rw [Set.uIcc_of_le hab]
      refine ContinuousOn.div continuousOn_id ((continuousOn_const.add continuousOn_id).pow 2) ?_
      intro x hx
      exact pow_ne_zero 2 (ne_of_gt (by linarith [hx.1]))
    have hcs := hardyZ_interval_integral_mul_le_sqrt a b hab hcontA hcontψ
    -- rewriting the integrand
    have hcongr : ∫ x in a..b, (x * h' x * w x) * (x / (1 + x) ^ 2) = ∫ x in a..b, h' x :=
      intervalIntegral.integral_congr fun x hx => by
        rw [Set.uIcc_of_le hab] at hx
        exact w_mul_psi_eq' (lt_of_lt_of_le hapos hx.1)
    -- the two factors
    have hA : ∫ x in a..b, (x * h' x * w x) ^ 2 ≤ P := by
      rw [hP]
      refine hardyZ_integral_Ioc_le_integral_Iz hapos.le hab hint fun x _ => sq_nonneg _
    have hB : ∫ x in a..b, (x / (1 + x) ^ 2) ^ 2 ≤ 1 :=
      hardyZ_integral_psi_sq_le_one hapos.le hab
    have hAnn : 0 ≤ ∫ x in a..b, (x * h' x * w x) ^ 2 :=
      intervalIntegral.integral_nonneg hab fun x _ => sq_nonneg _
    have hBnn : 0 ≤ ∫ x in a..b, (x / (1 + x) ^ 2) ^ 2 :=
      intervalIntegral.integral_nonneg hab fun x _ => sq_nonneg _
    have hsq : (∫ x in a..b, h' x) ^ 2 ≤ P := by
      rw [← hcongr, ← sq_abs]
      refine le_trans (pow_le_pow_left₀ (abs_nonneg _) hcs 2) ?_
      rw [mul_pow, Real.sq_sqrt hAnn, Real.sq_sqrt hBnn]
      nlinarith [hA, hB, hPnn]
    rcases hcases with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rw [hFTC] at hsq
      nlinarith [hsq]
    · rw [hFTC] at hsq
      exact hsq
  -- assemble
  have h1 : (h z) ^ 2 ≤ 2 * (h z - h z₀) ^ 2 + 2 * (h z₀) ^ 2 := by
    nlinarith [sq_nonneg (h z - 2 * h z₀)]
  calc (h z) ^ 2 ≤ 2 * (h z - h z₀) ^ 2 + 2 * (h z₀) ^ 2 := h1
    _ ≤ 2 * P + 2 * ∫ x in (1 : ℝ)..2, (h x) ^ 2 := by linarith [hkey, hmin]
    _ = 2 * ((∫ x in (1 : ℝ)..2, (h x) ^ 2) + P) := by ring

/-! ## The angular Hardy inequality with a mean term -/

/-- **The angular Hardy inequality with a mean term** (the "`θ`-Sobolev with the mean
term" of the design note `FTS/ELL_H2_LEAD.md` §B1).  For `h` differentiable on the open
interval with continuous derivative,

  `h(θ)² ≤ 204 (∫_{Iθ} h² + (γ-1)⁻¹ ∫_{Iθ} (h')² sin(2·)^{2-γ})`.

The mean term replaces the value `h(θ₀)` at a point where `h` would have to vanish. -/
theorem sob_theta_mean :
    ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ) (h : ℝ → ℝ) (θ : ℝ), 0 < α → α ≤ 1 →
      θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) →
      (∀ x ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), HasDerivAt h (deriv h x) x) →
      ContinuousOn (deriv h) (Set.Ioo (0 : ℝ) (Real.pi / 2)) →
      IntegrableOn (fun σ => (h σ) ^ 2) Iθ →
      IntegrableOn (fun σ => (deriv h σ) ^ 2 * (Real.sin (2 * σ)) ^ (2 - gam α)) Iθ →
      (h θ) ^ 2 ≤ C * ((∫ σ in Iθ, (h σ) ^ 2)
        + (gam α - 1)⁻¹ * ∫ σ in Iθ, (deriv h σ) ^ 2 * (Real.sin (2 * σ)) ^ (2 - gam α)) := by
  refine ⟨204, by norm_num, ?_⟩
  intro α h θ hα hα1 hθ hder hcont hint hint'
  have hγ : 0 < gam α - 1 := by rw [gam_sub_one]; linarith
  have hπ : 0 < Real.pi := Real.pi_pos
  -- continuity of `h` on `[π/8, 3π/8]`
  have hcont8 : ContinuousOn h (Set.Icc (Real.pi / 8) (3 * Real.pi / 8)) := by
    have hdiff : DifferentiableOn ℝ h (Set.Ioo (0 : ℝ) (Real.pi / 2)) := fun x hx =>
      (hder x hx).differentiableAt.differentiableWithinAt
    refine hdiff.continuousOn.mono ?_
    intro x hx
    exact ⟨by linarith [hx.1, hπ], by linarith [hx.2, hπ]⟩
  -- a minimiser of `h²` on the middle half of `Iθ`
  obtain ⟨θ₀, hθ₀mem, hmin⟩ :=
    exists_min_le_mean (φ := fun σ => (h σ) ^ 2) (a := Real.pi / 8) (b := 3 * Real.pi / 8)
      (by linarith [hπ]) (hcont8.pow 2)
  have hθ₀Ioo : θ₀ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) :=
    ⟨by linarith [hθ₀mem.1, hπ], by linarith [hθ₀mem.2, hπ]⟩
  -- the minimiser is at most the mean over `Iθ`
  have hmean : (h θ₀) ^ 2 ≤ (4 / Real.pi) * ∫ σ in Iθ, (h σ) ^ 2 := by
    have hsub : Set.Icc (Real.pi / 8) (3 * Real.pi / 8) ⊆ Iθ := by
      intro x hx
      simp only [Iθ, Set.mem_Icc]
      exact ⟨by linarith [hx.1, hπ], by linarith [hx.2, hπ]⟩
    have hmono2 : (∫ σ in Set.Icc (Real.pi / 8) (3 * Real.pi / 8), (h σ) ^ 2)
        ≤ ∫ σ in Iθ, (h σ) ^ 2 :=
      setIntegral_mono_set hint
        (ae_restrict_of_forall_mem measurableSet_Icc fun σ _ => sq_nonneg _)
        (Eventually.of_forall hsub)
    have hconv : (∫ t in Real.pi / 8..3 * Real.pi / 8, (h t) ^ 2)
        = ∫ σ in Set.Icc (Real.pi / 8) (3 * Real.pi / 8), (h σ) ^ 2 := by
      rw [intervalIntegral.integral_of_le (by linarith [hπ]),
        ← MeasureTheory.integral_Icc_eq_integral_Ioc]
    have hcfg : (3 * Real.pi / 8 - Real.pi / 8)⁻¹ = 4 / Real.pi := by
      rw [show 3 * Real.pi / 8 - Real.pi / 8 = Real.pi / 4 by ring, inv_div]
    have hstep := hmin
    rw [hcfg, hconv] at hstep
    exact le_trans hstep (mul_le_mul_of_nonneg_left hmono2 (by positivity))
  -- the oscillation bound
  have huIcc : Set.uIcc θ θ₀ ⊆ Set.Ioo (0 : ℝ) (Real.pi / 2) := by
    intro x hx
    rw [Set.mem_uIcc] at hx
    rcases hx with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact ⟨by linarith [hθ.1, h1], by linarith [h2, hθ₀Ioo.2]⟩
    · exact ⟨by linarith [hθ₀Ioo.1, h1], by linarith [h2, hθ.2]⟩
  have hder' : ∀ x ∈ Set.uIcc θ θ₀, HasDerivAt h (deriv h x) x := fun x hx =>
    hder x (huIcc hx)
  have hcontd : ContinuousOn (deriv h) (Set.uIcc θ θ₀) := hcont.mono huIcc
  have hosc := Work.FTS.H2.OscSqLe α hα hα1 h
    (Set.mem_Icc.mpr ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩)
    (Set.mem_Icc.mpr ⟨le_of_lt hθ₀Ioo.1, le_of_lt hθ₀Ioo.2⟩) hder' hcontd hint'
  -- the angular integrand is nonnegative and the mean term is nonnegative
  have hA : 0 ≤ ∫ σ in Iθ, (h σ) ^ 2 :=
    setIntegral_nonneg measurableSet_Icc fun σ _ => sq_nonneg _
  have hB : 0 ≤ ∫ σ in Iθ, (deriv h σ) ^ 2 * (Real.sin (2 * σ)) ^ (2 - gam α) :=
    setIntegral_nonneg measurableSet_Icc fun σ hσ => mul_nonneg (sq_nonneg _)
      (Real.rpow_nonneg (Real.sin_nonneg_of_mem_Icc
        ⟨by linarith [hσ.1], by linarith [hσ.2]⟩) _)
  have h8 : 8 / Real.pi ≤ 4 := by
    rw [div_le_iff₀ hπ]; linarith [Real.pi_gt_three]
  -- assemble
  have h1 : (h θ) ^ 2 ≤ 2 * (h θ - h θ₀) ^ 2 + 2 * (h θ₀) ^ 2 := by
    nlinarith [sq_nonneg (h θ - 2 * h θ₀)]
  have h2 : 2 * (h θ - h θ₀) ^ 2
      ≤ (200 / (gam α - 1)) * (∫ σ in Iθ,
          (deriv h σ) ^ 2 * (Real.sin (2 * σ)) ^ (2 - gam α)) := by
    have hstep2 := mul_le_mul_of_nonneg_left hosc (by norm_num : (0 : ℝ) ≤ 2)
    calc 2 * (h θ - h θ₀) ^ 2
        ≤ 2 * (100 / (gam α - 1) * (∫ σ in Iθ,
            (deriv h σ) ^ 2 * (Real.sin (2 * σ)) ^ (2 - gam α))) := hstep2
      _ = (200 / (gam α - 1)) * (∫ σ in Iθ,
            (deriv h σ) ^ 2 * (Real.sin (2 * σ)) ^ (2 - gam α)) := by ring
  have h3 : 2 * (h θ₀) ^ 2 ≤ (8 / Real.pi) * (∫ σ in Iθ, (h σ) ^ 2) := by
    have hstep3 := mul_le_mul_of_nonneg_left hmean (by norm_num : (0 : ℝ) ≤ 2)
    calc 2 * (h θ₀) ^ 2 ≤ 2 * ((4 / Real.pi) * (∫ σ in Iθ, (h σ) ^ 2)) := hstep3
      _ = (8 / Real.pi) * (∫ σ in Iθ, (h σ) ^ 2) := by ring
  have h4 : (200 / (gam α - 1)) * (∫ σ in Iθ,
        (deriv h σ) ^ 2 * (Real.sin (2 * σ)) ^ (2 - gam α))
      ≤ 204 * ((gam α - 1)⁻¹ * ∫ σ in Iθ,
        (deriv h σ) ^ 2 * (Real.sin (2 * σ)) ^ (2 - gam α)) := by
    rw [div_eq_mul_inv]
    nlinarith [hB, hγ, inv_nonneg.mpr hγ.le]
  have h5 : (8 / Real.pi) * (∫ σ in Iθ, (h σ) ^ 2) ≤ 204 * (∫ σ in Iθ, (h σ) ^ 2) := by
    nlinarith [hA, h8]
  nlinarith [h1, h2, h3, h4, h5]

end Work.FTS.OpenPkg.ProdOpen
