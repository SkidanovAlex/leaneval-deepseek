import ChallengeDeps
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.MeasureTheory.Order.Group.Lattice
import Submission.ScatProfileExterior
import Submission.Work.BoseFixB2.Pot.lintegral_wPairC_le
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB1B.ae_integrable_fibre_wPairC`

For an admissible potential `v` (compactly supported, `0 ≤ v`, radial, with a radial
scattering solution) the *fibre* of the χ-renormalized localized two-body kernel with
numerator `g₀ = v(1−ω)`,

    y ↦ χ_ℓ(y) · |g₀(x−y)| / (χ⋆χ)_ℓ(x−y) ,

is Lebesgue integrable for a.e. `x` with `χ_ℓ(x) ≠ 0`.

The point of the statement is that **no diluteness hypothesis** `R₀ ≤ ℓ·chiR0` is
assumed: the denominator `(χ⋆χ)_ℓ` is *not* known to be bounded below on the whole
support of `g₀`.  The rescue is the geometry of the cutoff `χ_ℓ`:

* `χ` is the bump of `Submission.CubicChi`, so `χ y = 0` for `‖y‖ ≥ 1/2`, i.e.
  `χ_ℓ y = 0` for `‖y‖ ≥ ℓ/2`.  Hence `χ_ℓ x ≠ 0` forces `‖x‖ < ℓ/2`, and then for
  every `y` in the support of the `y`-integrand (`χ_ℓ y ≠ 0`, so `‖y‖ < ℓ/2`) one has
  `‖x − y‖ ≤ ‖x‖ + ℓ/2 < ℓ`.
* `(χ⋆χ)` is continuous and strictly positive on the open ball of radius `1`
  (`conv3_chi_pos_of_norm_lt_one`), since both factors of the convolution integrand
  can be made strictly positive; on the compact ball `‖z‖ ≤ r < ℓ` its minimum is
  therefore strictly positive, and that minimum controls the denominator on the
  support of the fibre.

The fibre is then dominated pointwise by a constant (depending on `x`) times
`|g₀(x−·)|`, and `g₀` is integrable by `Submission.BoseGases.g0_integrable`.
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped Topology Real ENNReal

namespace Work.BoseFixB1B

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## 1. The cutoff `χ_ℓ` kills the ball of radius `ℓ/2` -/

/-- The bump `χ` vanishes outside the closed ball of radius `1/2`. -/
private lemma chi_eq_zero_of_half_le_norm (y : EuclideanSpace ℝ (Fin 3)) (hy : 1 / 2 ≤ ‖y‖) :
    Submission.BoseGases.chi y = 0 := by
  have h0 : Submission.BoseGases.chiBase y = 0 := by
    rw [Submission.BoseGases.chiBase]
    exact Submission.BoseGases.chiBump.zero_of_le_dist
      (by simpa [Submission.BoseGases.chiBump, dist_eq_norm] using hy)
  simp [Submission.BoseGases.chi, h0]

/-- If `χ_ℓ(x) ≠ 0` then `‖x‖ < ℓ/2`. -/
private lemma chiScale_ne_zero_imp_norm_lt {ℓ : ℝ} (hℓ : 0 < ℓ)
    {x : EuclideanSpace ℝ (Fin 3)} (hx : Submission.BoseGases.chiScale ℓ x ≠ 0) :
    ‖x‖ < ℓ / 2 := by
  have h1 : ‖(ℓ⁻¹ : ℝ) • x‖ < 1 / 2 := by
    by_contra hcon
    exact hx (chi_eq_zero_of_half_le_norm _ (le_of_not_gt hcon))
  have h2 : ℓ * ‖(ℓ⁻¹ : ℝ) • x‖ = ‖x‖ := by
    calc ℓ * ‖(ℓ⁻¹ : ℝ) • x‖ = |ℓ| * ‖(ℓ⁻¹ : ℝ) • x‖ := by rw [abs_of_pos hℓ]
      _ = ‖ℓ • ((ℓ⁻¹ : ℝ) • x)‖ := (norm_smul ℓ ((ℓ⁻¹ : ℝ) • x)).symm
      _ = ‖x‖ := by rw [smul_smul, mul_inv_cancel₀ (ne_of_gt hℓ), one_smul]
  have h3 : ℓ * ‖(ℓ⁻¹ : ℝ) • x‖ < ℓ / 2 := by
    have := mul_lt_mul_of_pos_left h1 hℓ
    linarith
  rw [← h2]
  exact h3

/-! ## 2. Positivity of the self-convolution `χ⋆χ` on the unit ball -/

/-- `χ ⋆ χ` is strictly positive on the open unit ball.  Indeed, for `‖w‖ < 1` both
`w/2` and `w − w/2 = w/2` lie strictly inside the support ball of `χ`, where `χ > 0`;
by continuity the convolution integrand is then positive on a set of positive measure. -/
private lemma conv3_chi_pos_of_norm_lt_one {w : EuclideanSpace ℝ (Fin 3)} (hw : ‖w‖ < 1) :
    0 < Submission.BoseGases.conv3 Submission.BoseGases.chi Submission.BoseGases.chi w := by
  have hZ : 0 < Real.sqrt Submission.BoseGases.chiNormSq :=
    Real.sqrt_pos.mpr Submission.BoseGases.chiNormSq_pos
  have hy0n : ‖(2 : ℝ)⁻¹ • w‖ < 1 / 2 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2⁻¹)]
    linarith
  have hwyn : ‖w - (2 : ℝ)⁻¹ • w‖ < 1 / 2 := by
    have heq : w - (2 : ℝ)⁻¹ • w = (1 - (2 : ℝ)⁻¹) • w := by rw [sub_smul, one_smul]
    rw [heq, show (1 : ℝ) - 2⁻¹ = 2⁻¹ by norm_num]
    exact hy0n
  have hpos1 : 0 < Submission.BoseGases.chi ((2 : ℝ)⁻¹ • w) := by
    rw [Submission.BoseGases.chi]
    refine div_pos ?_ hZ
    rw [Submission.BoseGases.chiBase]
    exact Submission.BoseGases.chiBump.pos_of_mem_ball (by
      rw [Metric.mem_ball, dist_eq_norm, sub_zero]
      simpa [Submission.BoseGases.chiBump] using hy0n)
  have hpos2 : 0 < Submission.BoseGases.chi (w - (2 : ℝ)⁻¹ • w) := by
    rw [Submission.BoseGases.chi]
    refine div_pos ?_ hZ
    rw [Submission.BoseGases.chiBase]
    exact Submission.BoseGases.chiBump.pos_of_mem_ball (by
      rw [Metric.mem_ball, dist_eq_norm, sub_zero]
      simpa [Submission.BoseGases.chiBump] using hwyn)
  have hcont : Continuous fun y : EuclideanSpace ℝ (Fin 3) =>
      Submission.BoseGases.chi y * Submission.BoseGases.chi (w - y) :=
    Submission.BoseGases.chi_continuous.mul
      (Submission.BoseGases.chi_continuous.comp (continuous_const.sub continuous_id))
  have hsupp : HasCompactSupport fun y : EuclideanSpace ℝ (Fin 3) =>
      Submission.BoseGases.chi y * Submission.BoseGases.chi (w - y) :=
    Submission.BoseGases.chi_hasCompactSupport.mul_right
  have hgoal := Continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero
    (μ := MeasureTheory.volume) hcont hsupp
    (fun y => mul_nonneg (Submission.BoseGases.chi_nonneg y)
      (Submission.BoseGases.chi_nonneg (w - y)))
    (mul_ne_zero (ne_of_gt hpos1) (ne_of_gt hpos2))
  simpa [Submission.BoseGases.conv3] using hgoal

/-- A uniform positive lower bound for `χ ⋆ χ` on any closed ball of radius `< 1`. -/
private lemma exists_pos_le_conv3_chi_closedBall {d : ℝ} (hd : d < 1) :
    ∃ m : ℝ, 0 < m ∧ ∀ z : EuclideanSpace ℝ (Fin 3),
      ‖z‖ ≤ d → m ≤ Submission.BoseGases.conv3 Submission.BoseGases.chi
        Submission.BoseGases.chi z := by
  by_cases hd0 : d < 0
  · exact ⟨1, one_pos,
      fun z hz => absurd hz (not_le.mpr (lt_of_lt_of_le hd0 (norm_nonneg z)))⟩
  · have hd0' : 0 ≤ d := le_of_not_gt hd0
    have hne : (Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) d).Nonempty :=
      ⟨0, by simp [Metric.mem_closedBall, hd0']⟩
    obtain ⟨z0, hz0mem, hz0min⟩ := (isCompact_closedBall (0 : EuclideanSpace ℝ (Fin 3)) d)
      |>.exists_isMinOn hne Submission.BoseGases.conv_contDiff.continuous.continuousOn
    refine ⟨Submission.BoseGases.conv3 Submission.BoseGases.chi Submission.BoseGases.chi z0,
      ?_, ?_⟩
    · have hz0 : ‖z0‖ ≤ d := by simpa [Metric.mem_closedBall] using hz0mem
      exact conv3_chi_pos_of_norm_lt_one (lt_of_le_of_lt hz0 hd)
    · intro z hz
      exact hz0min (by simpa [Metric.mem_closedBall] using hz)

/-! ## 3. The same for the scaled convolution -/

/-- A uniform positive lower bound for `(χ⋆χ)_ℓ` on any closed ball of radius `< ℓ`. -/
private lemma exists_pos_le_convScale_closedBall {ℓ r : ℝ} (hℓ : 0 < ℓ) (hr : r < ℓ) :
    ∃ m : ℝ, 0 < m ∧ ∀ z : EuclideanSpace ℝ (Fin 3),
      ‖z‖ ≤ r → m ≤ Submission.BoseGases.convScale ℓ z := by
  obtain ⟨m, hmpos, hm⟩ :=
    exists_pos_le_conv3_chi_closedBall (d := r / ℓ) (by rw [div_lt_one hℓ]; exact hr)
  refine ⟨m, hmpos, fun z hz => ?_⟩
  have hz' : ‖(ℓ⁻¹ : ℝ) • z‖ ≤ r / ℓ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hℓ), ← div_eq_inv_mul]
    exact div_le_div_of_nonneg_right hz (le_of_lt hℓ)
  exact hm _ hz'

/-! ## 4. The fibre is integrable -/

/-- **Fibre integrability of the kernel with numerator `g₀`.**  For every `x` with
`χ_ℓ(x) ≠ 0` (no exceptional set is needed) the function
`y ↦ χ_ℓ(y)·|g₀(x−y)|/(χ⋆χ)_ℓ(x−y)` is integrable. -/
private lemma integrable_fibre_g0 {v : EuclideanSpace ℝ (Fin 3) → ℝ} {R0 : ℝ}
    (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R0) (hR0 : 0 < R0)
    (h : ∃ w : EuclideanSpace ℝ (Fin 3) → ℝ,
      _root_.BoseGases.IsRadial w ∧ _root_.BoseGases.IsScatteringSolution w v)
    {ℓ : ℝ} (hℓ : 0 < ℓ) {x : EuclideanSpace ℝ (Fin 3)}
    (hx : Submission.BoseGases.chiScale ℓ x ≠ 0) :
    MeasureTheory.Integrable
      (fun y : EuclideanSpace ℝ (Fin 3) =>
        Submission.BoseGases.chiScale ℓ y *
          (|Submission.BoseGases.g0 v h (x - y)| / Submission.BoseGases.convScale ℓ (x - y)))
      (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3))) := by
  have hg0int : MeasureTheory.Integrable (Submission.BoseGases.g0 v h)
      (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3))) :=
    Submission.BoseGases.g0_integrable hR0 hv_supp h
  -- the cutoff forces `‖x‖ < ℓ/2`, so the relevant `z = x − y` stay inside the ball
  -- of radius `‖x‖ + ℓ/2 < ℓ`, where `(χ⋆χ)_ℓ` is bounded below
  have hxnorm : ‖x‖ < ℓ / 2 := chiScale_ne_zero_imp_norm_lt hℓ hx
  obtain ⟨m, hmpos, hmin⟩ :=
    exists_pos_le_convScale_closedBall (ℓ := ℓ) (r := ‖x‖ + ℓ / 2) hℓ (by linarith)
  set A : ℝ := (Real.sqrt Submission.BoseGases.chiNormSq)⁻¹ with hA
  have hApos : 0 < A := by
    rw [hA]; exact inv_pos.mpr (Real.sqrt_pos.mpr Submission.BoseGases.chiNormSq_pos)
  have hAmnn : 0 ≤ A / m := div_nonneg (le_of_lt hApos) (le_of_lt hmpos)
  -- the dominating function
  have hdom : MeasureTheory.Integrable
      (fun y : EuclideanSpace ℝ (Fin 3) =>
        (A / m) * |Submission.BoseGases.g0 v h (x - y)|)
      (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3))) :=
    (hg0int.abs.comp_sub_left x).const_mul (A / m)
  -- the pointwise bound
  have hpt : ∀ y : EuclideanSpace ℝ (Fin 3),
      ‖Submission.BoseGases.chiScale ℓ y *
        (|Submission.BoseGases.g0 v h (x - y)| / Submission.BoseGases.convScale ℓ (x - y))‖
      ≤ (A / m) * |Submission.BoseGases.g0 v h (x - y)| := by
    intro y
    rw [Real.norm_eq_abs]
    by_cases hy : Submission.BoseGases.chiScale ℓ y = 0
    · rw [hy, zero_mul, abs_zero]
      exact mul_nonneg hAmnn (abs_nonneg _)
    · have hynorm : ‖y‖ < ℓ / 2 := chiScale_ne_zero_imp_norm_lt hℓ hy
      have hznorm : ‖x - y‖ ≤ ‖x‖ + ℓ / 2 := by
        calc ‖x - y‖ ≤ ‖x‖ + ‖y‖ := norm_sub_le x y
          _ ≤ ‖x‖ + ℓ / 2 := by linarith
      have hden : m ≤ Submission.BoseGases.convScale ℓ (x - y) := hmin _ hznorm
      have hdenpos : 0 < Submission.BoseGases.convScale ℓ (x - y) := lt_of_lt_of_le hmpos hden
      rw [abs_mul, abs_div, abs_of_nonneg (abs_nonneg _), abs_of_pos hdenpos]
      have hAsup : |Submission.BoseGases.chiScale ℓ y| ≤ A := by
        rw [hA]; exact Submission.BoseGases.abs_chiScale_le ℓ y
      have hquot : |Submission.BoseGases.g0 v h (x - y)| / Submission.BoseGases.convScale ℓ (x - y)
          ≤ |Submission.BoseGases.g0 v h (x - y)| / m :=
        div_le_div_of_nonneg_left (abs_nonneg _) hmpos hden
      calc |Submission.BoseGases.chiScale ℓ y|
            * (|Submission.BoseGases.g0 v h (x - y)| / Submission.BoseGases.convScale ℓ (x - y))
          ≤ A * (|Submission.BoseGases.g0 v h (x - y)| / m) :=
            mul_le_mul hAsup hquot (div_nonneg (abs_nonneg _) (le_of_lt hdenpos))
              (le_of_lt hApos)
        _ = (A / m) * |Submission.BoseGases.g0 v h (x - y)| := by ring
  -- a.e. strong measurability
  have hmeas : AEStronglyMeasurable
      (fun y : EuclideanSpace ℝ (Fin 3) =>
        Submission.BoseGases.chiScale ℓ y *
          (|Submission.BoseGases.g0 v h (x - y)| / Submission.BoseGases.convScale ℓ (x - y)))
      (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3))) := by
    have hqmp : Measure.QuasiMeasurePreserving (fun y : EuclideanSpace ℝ (Fin 3) => x - y)
        (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3)))
        (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3))) :=
      MeasureTheory.quasiMeasurePreserving_sub_left_of_right_invariant
        (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3))) x
    have hshift : AEMeasurable (fun y : EuclideanSpace ℝ (Fin 3) =>
        Submission.BoseGases.g0 v h (x - y))
        (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3))) := by
      have := hg0int.aestronglyMeasurable.aemeasurable |>.comp_quasiMeasurePreserving hqmp
      simpa [Function.comp_def] using this
    have hquot : AEMeasurable (fun y : EuclideanSpace ℝ (Fin 3) =>
        |Submission.BoseGases.g0 v h (x - y)| / Submission.BoseGases.convScale ℓ (x - y))
        (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3))) :=
      hshift.abs.div
        ((Submission.BoseGases.convScale_continuous ℓ).comp
          (by fun_prop : Continuous fun y : EuclideanSpace ℝ (Fin 3) => x - y)).measurable.aemeasurable
    have hchi : AEMeasurable (fun y : EuclideanSpace ℝ (Fin 3) =>
        Submission.BoseGases.chiScale ℓ y)
        (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3))) :=
      (Submission.BoseGases.chiScale_continuous ℓ).measurable.aemeasurable
    exact (hchi.mul hquot).aestronglyMeasurable
  exact MeasureTheory.Integrable.mono' hdom hmeas (Filter.Eventually.of_forall hpt)

/-! ## 5. The requested statement -/

theorem ae_integrable_fibre_wPairC {v : EuclideanSpace ℝ (Fin 3) → ℝ} {R0 : ℝ}
    (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R0) (hR0 : 0 < R0)
    (hv : 0 ≤ v) (hvrad : _root_.BoseGases.IsRadial v)
    (h : ∃ w : EuclideanSpace ℝ (Fin 3) → ℝ,
      _root_.BoseGases.IsRadial w ∧ _root_.BoseGases.IsScatteringSolution w v)
    (ℓ : ℝ) (hℓ : 0 < ℓ) :
    ∀ᵐ x ∂(MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3))),
      Submission.BoseGases.chiScale ℓ x ≠ 0 →
      MeasureTheory.Integrable
        (fun y : EuclideanSpace ℝ (Fin 3) =>
          Submission.BoseGases.chiScale ℓ y *
            (|Submission.BoseGases.g0 v h (x - y)| / Submission.BoseGases.convScale ℓ (x - y)))
        (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3))) :=
  Filter.Eventually.of_forall fun x hx =>
    integrable_fibre_g0 hv_supp hR0 h hℓ hx

end Work.BoseFixB1B
