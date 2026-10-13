import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Submission.Work.FTS_RegExport.THL.angular_L2_noTrace
import Submission.Work.FTS_RegExport.THL.integral_sin_two_rpow_le
import Submission.Work.FTS_RegExport.RXT.Slots.v2_theta_sup_aux
import Submission.Work.Spaces.HardyZ

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `THL.theta_holder_of_HkMem` — `ℋ⁴` membership gives a uniform `θ`-Hölder modulus

The trace-free leaf **A3** of `THL.Leaves`: for `0 < β ≤ 1`, a function `f` which is `C⁴` on the
open quadrant `Q0 = (0,∞) × (0,π/2)` and honestly in the weighted space `ℋ⁴` is `θ`-Hölder of
exponent `(γ-1)/2 = β/20` (with `γ = gam β = 1 + β/10`), uniformly in `z > 0`:

  `|f(z,θ) - f(z,θ')| ≤ C · min(z,1) · |f|_{ℋ⁴} · |θ - θ'|^{(γ-1)/2}`.

**Route.**  For `0 < a ≤ b < π/2`, the fundamental theorem of calculus for the `θ`-slice gives
`f(z,b) - f(z,a) = ∫_a^b ∂_θ f(z,σ) dσ`; writing `∂_θ f = D_θ f / sin(2σ)` and splitting the
integrand into the two factors

  `A₁ σ = sin(2σ)^{-γ/2} · D_θ f(z,σ)`,  `A₂ σ = sin(2σ)^{(γ-2)/2}`

the interval Cauchy–Schwarz `Work.Spaces.hardyZ_interval_integral_mul_le_sqrt` gives

  `|f(z,b) - f(z,a)|² ≤ (∫_a^b A₁²)(∫_a^b A₂²)`.

The first factor is bounded by the trace-free angular `L²` estimate `angular_L2_noTrace`
(`∫_{Iθ} sin(2σ)^{-γ}(D_θf)² ≤ 5 z³/(1+z)⁴ |f|²_{ℋ⁴}`, monotone in the interval), the second by
the one-variable bound `integral_sin_two_rpow_le` with `p = γ-1 = β/10`.  Extracting square roots
and using `√(z³/(1+z)⁴) ≤ min(z,1)` and `√(2(π/4)^{1-β/10}·10/β) ≤ 10/β + 1` gives the claim with
the explicit constant `C = √5 · (10/β + 1)`.
-/

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS_RegExport.THL

set_option autoImplicit false
set_option maxHeartbeats 800000

/-! ## Elementary angular facts -/

/-- `sin(2θ) > 0` on the open angular interval. -/
private lemma sin_two_pos_of_mem_Ioo' {θ : ℝ} (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    0 < Real.sin (2 * θ) :=
  Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])

/-- `sin(2θ) ≥ 0` on the closed angular interval `Iθ`. -/
private lemma sin_two_nonneg_Iθ' {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    0 ≤ Real.sin (2 * θ) :=
  Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])

/-! ## Monotonicity of the interval integral against the set integral over `Iθ` -/

/-- For `0 < a ≤ b < π/2` the interval `[a,b]` sits inside `Iθ`, so the integral of a
nonnegative integrable function over `[a,b]` is at most its integral over `Iθ`. -/
private lemma interval_integral_le_setIntegral_Iθ' {F : ℝ → ℝ} {a b : ℝ} (ha : 0 < a)
    (hab : a ≤ b) (hb : b < Real.pi / 2) (hint : IntegrableOn F Work.Spaces.Iθ)
    (hnn : ∀ x ∈ Work.Spaces.Iθ, 0 ≤ F x) :
    (∫ x in a..b, F x) ≤ ∫ x in Work.Spaces.Iθ, F x := by
  rw [intervalIntegral.integral_of_le hab]
  refine setIntegral_mono_set hint (ae_restrict_of_forall_mem measurableSet_Icc hnn) ?_
  exact Eventually.of_forall fun x hx =>
    ⟨le_of_lt (lt_trans ha hx.1), le_of_lt (lt_of_le_of_lt hx.2 hb)⟩

/-! ## The radial factor `√(z³/(1+z)⁴) ≤ min(z,1)` -/

private lemma sqrt_z_cube_div_le_min {z : ℝ} (hz : 0 < z) :
    Real.sqrt (z ^ 3 / (1 + z) ^ 4) ≤ min z 1 := by
  have hnn : 0 ≤ min z 1 := le_min hz.le zero_le_one
  refine le_trans (Real.sqrt_le_sqrt ?_) (le_of_eq (Real.sqrt_sq hnn))
  rcases le_or_gt z 1 with h | h
  · rw [min_eq_left h, div_le_iff₀ (by positivity : (0:ℝ) < (1 + z) ^ 4)]
    have h32 : z ^ 3 ≤ z ^ 2 := by
      rw [show z ^ 3 = z ^ 2 * z by ring]
      exact mul_le_of_le_one_right (sq_nonneg z) h
    have h4 : (1:ℝ) ≤ (1 + z) ^ 4 := one_le_pow₀ (by linarith)
    have h2 := mul_le_mul_of_nonneg_left h4 (sq_nonneg z)
    linarith [h32, h2]
  · rw [min_eq_right h.le, one_pow, div_le_one (by positivity : (0:ℝ) < (1 + z) ^ 4)]
    have h34 : z ^ 3 ≤ z ^ 4 := by nlinarith [h, pow_pos hz 3]
    have h4 : z ^ 4 ≤ (1 + z) ^ 4 := pow_le_pow_left₀ hz.le (by linarith) 4
    linarith

/-! ## The main estimate -/

theorem theta_holder_of_HkMem {β : ℝ} (hβ : 0 < β) (hβ1 : β ≤ 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ f : ℝ → ℝ → ℝ,
      ContDiffOn ℝ 4 (Function.uncurry f) Work.FTS.EllipticEst.Q0 → Work.Spaces.HkMem β 4 f →
      ∀ z : ℝ, 0 < z → ∀ θ ∈ Set.Ioo (0:ℝ) (Real.pi / 2),
      ∀ θ' ∈ Set.Ioo (0:ℝ) (Real.pi / 2),
        |f z θ - f z θ'|
          ≤ C * min z 1 * Work.Spaces.HkNorm β 4 f *
            |θ - θ'| ^ ((Work.Spaces.gam β - 1) / 2) := by
  have hgam : Work.Spaces.gam β - 1 = β / 10 := Work.Spaces.gam_sub_one β
  have hpi4pos : (0 : ℝ) < Real.pi / 4 := by positivity
  have hpi4le : Real.pi / 4 ≤ 1 := by nlinarith [Real.pi_lt_four]
  refine ⟨Real.sqrt 5 * (10 / β + 1), by positivity, ?_⟩
  intro f h4 hmem z hz θ hθ θ' hθ'
  -- ### the angular `L²` input (leaf A2)
  obtain ⟨hintL2, hboundL2⟩ := angular_L2_noTrace hβ hβ1 h4 hmem hz
  -- ### the scalar bound `√(2(π/4)^{1-β/10}·10/β) ≤ 10/β + 1`
  have hSle : Real.sqrt (2 * (Real.pi / 4) ^ (1 - β / 10) * (10 / β)) ≤ 10 / β + 1 := by
    have hnn : (0 : ℝ) ≤ 10 / β + 1 := by positivity
    rw [Real.sqrt_le_iff]
    refine ⟨hnn, ?_⟩
    have hpow : (Real.pi / 4) ^ (1 - β / 10) ≤ 1 :=
      Real.rpow_le_one hpi4pos.le hpi4le (by linarith)
    have h10 : (0 : ℝ) ≤ 10 / β := by positivity
    nlinarith [hpow, h10, hnn]
  -- ### the estimate for `a ≤ b`
  have key : ∀ a b : ℝ, 0 < a → a ≤ b → b < Real.pi / 2 →
      |f z a - f z b|
        ≤ Real.sqrt 5 * (10 / β + 1) * min z 1 * Work.Spaces.HkNorm β 4 f
          * (b - a) ^ ((Work.Spaces.gam β - 1) / 2) := by
    intro a b ha hab hb
    have hban : 0 ≤ b - a := by linarith
    have hsub : Set.uIcc a b ⊆ Set.Ioo (0 : ℝ) (Real.pi / 2) := by
      rw [Set.uIcc_of_le hab]
      exact fun x hx => ⟨lt_of_lt_of_le ha hx.1, lt_of_le_of_lt hx.2 hb⟩
    -- (0) the slice derivative and the fundamental theorem of calculus
    have hslice_cd : ContDiffOn ℝ 1 (fun s => f z s) (Set.Ioo 0 (Real.pi / 2)) :=
      Work.FTS_RegExport.RXA1w.contDiffOn_slice_mixed h4 0 0 1 (by norm_num) hz
    have hderiv : ∀ σ ∈ Set.uIcc a b,
        HasDerivAt (fun s => f z s) (Work.Spaces.pth f z σ) σ := fun σ hσ =>
      ((hslice_cd.differentiableOn (by norm_num)).differentiableAt
        (isOpen_Ioo.mem_nhds (hsub hσ))).hasDerivAt
    have hpthcont : ContinuousOn (fun s => Work.Spaces.pth f z s) (Set.uIcc a b) :=
      (Work.FTS_RegExport.RXT.Slots.continuousOn_pth_mixed_slice_aux h4 0 0 (by norm_num)
        hz).mono hsub
    have hFTC : ∫ s in a..b, Work.Spaces.pth f z s = f z b - f z a :=
      intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hpthcont.intervalIntegrable
    -- (1) the two factors and their continuity
    set A1 : ℝ → ℝ := fun σ =>
      (Real.sin (2 * σ)) ^ (-(Work.Spaces.gam β / 2)) * Work.Spaces.mixed 0 1 f z σ with hA1
    set A2 : ℝ → ℝ := fun σ => (Real.sin (2 * σ)) ^ ((Work.Spaces.gam β - 2) / 2) with hA2
    have hsincont : ContinuousOn (fun σ : ℝ => Real.sin (2 * σ)) (Set.uIcc a b) :=
      (Real.continuous_sin.comp (continuous_const.mul continuous_id)).continuousOn
    have hmixcont : ContinuousOn (fun σ => Work.Spaces.mixed 0 1 f z σ) (Set.uIcc a b) :=
      (Work.FTS_RegExport.RXA1w.contDiffOn_slice_mixed h4 0 1 0 (by norm_num) hz).continuousOn.mono
        hsub
    have hA1cont : ContinuousOn A1 (Set.uIcc a b) := by
      rw [hA1]
      exact (hsincont.rpow_const fun σ hσ =>
        Or.inl (ne_of_gt (sin_two_pos_of_mem_Ioo' (hsub hσ)))).mul hmixcont
    have hA2cont : ContinuousOn A2 (Set.uIcc a b) := by
      rw [hA2]
      exact hsincont.rpow_const fun σ hσ =>
        Or.inl (ne_of_gt (sin_two_pos_of_mem_Ioo' (hsub hσ)))
    have hcs := Work.Spaces.hardyZ_interval_integral_mul_le_sqrt a b hab hA1cont hA2cont
    -- (2) the two squared integrals, evaluated
    have hA1sq : (∫ σ in a..b, (A1 σ) ^ 2)
        = ∫ σ in a..b, (Real.sin (2 * σ)) ^ (-(Work.Spaces.gam β))
            * (Work.Spaces.mixed 0 1 f z σ) ^ 2 := by
      refine intervalIntegral.integral_congr fun σ hσ => ?_
      have hspos : 0 < Real.sin (2 * σ) := sin_two_pos_of_mem_Ioo' (hsub hσ)
      simp only [hA1]
      rw [mul_pow, pow_two, ← Real.rpow_add hspos,
        show -(Work.Spaces.gam β / 2) + -(Work.Spaces.gam β / 2) = -(Work.Spaces.gam β) by ring]
    have hA2sq : (∫ σ in a..b, (A2 σ) ^ 2)
        = ∫ σ in a..b, (Real.sin (2 * σ)) ^ (Work.Spaces.gam β - 2) := by
      refine intervalIntegral.integral_congr fun σ hσ => ?_
      have hspos : 0 < Real.sin (2 * σ) := sin_two_pos_of_mem_Ioo' (hsub hσ)
      simp only [hA2]
      rw [pow_two, ← Real.rpow_add hspos,
        show (Work.Spaces.gam β - 2) / 2 + (Work.Spaces.gam β - 2) / 2
          = Work.Spaces.gam β - 2 by ring]
    -- (3) the two square-root bounds
    have hb1 : Real.sqrt (∫ σ in a..b, (A1 σ) ^ 2)
        ≤ Real.sqrt (5 * (z ^ 3 / (1 + z) ^ 4) * Work.Spaces.HkSq β 4 f) := by
      refine Real.sqrt_le_sqrt ?_
      rw [hA1sq]
      exact le_trans (interval_integral_le_setIntegral_Iθ' ha hab hb hintL2 fun x hx =>
        mul_nonneg (Real.rpow_nonneg (sin_two_nonneg_Iθ' hx) _) (sq_nonneg _)) hboundL2
    have hb2 : Real.sqrt (∫ σ in a..b, (A2 σ) ^ 2)
        ≤ Real.sqrt (2 * (Real.pi / 4) ^ (1 - β / 10) * (10 / β) * (b - a) ^ (β / 10)) := by
      rw [hA2sq]
      have h1 : ∫ σ in a..b, (Real.sin (2 * σ)) ^ (Work.Spaces.gam β - 2)
          ≤ 2 * (Real.pi / 4) ^ (1 - β / 10) / (β / 10) * (b - a) ^ (β / 10) := by
        have hp : (0 : ℝ) < β / 10 := by linarith
        have hp1 : β / 10 ≤ 1 := by linarith
        have h := integral_sin_two_rpow_le (p := β / 10) hp hp1 ha hab hb
        rwa [show β / 10 - 1 = Work.Spaces.gam β - 2 by rw [← hgam]; ring] at h
      refine le_trans (Real.sqrt_le_sqrt h1) (le_of_eq ?_)
      congr 1
      rw [div_eq_mul_inv, inv_div]
    -- (4) the product identity
    have hprod : ∫ σ in a..b, A1 σ * A2 σ = f z b - f z a := by
      rw [← hFTC]
      refine intervalIntegral.integral_congr fun σ hσ => ?_
      have hspos : 0 < Real.sin (2 * σ) := sin_two_pos_of_mem_Ioo' (hsub hσ)
      have hpow : (Real.sin (2 * σ)) ^ (-(Work.Spaces.gam β / 2))
          * (Real.sin (2 * σ)) ^ ((Work.Spaces.gam β - 2) / 2) * Real.sin (2 * σ) = 1 := by
        rw [← Real.rpow_add hspos, ← Real.rpow_add_one hspos.ne',
          show -(Work.Spaces.gam β / 2) + ((Work.Spaces.gam β - 2) / 2) + 1 = 0 by ring,
          Real.rpow_zero]
      simp only [hA1, hA2]
      rw [show Work.Spaces.mixed 0 1 f z σ
            = Real.sin (2 * σ) * Work.Spaces.pth f z σ from rfl]
      calc (Real.sin (2 * σ)) ^ (-(Work.Spaces.gam β / 2))
            * (Real.sin (2 * σ) * Work.Spaces.pth f z σ)
            * (Real.sin (2 * σ)) ^ ((Work.Spaces.gam β - 2) / 2)
          = ((Real.sin (2 * σ)) ^ (-(Work.Spaces.gam β / 2))
              * (Real.sin (2 * σ)) ^ ((Work.Spaces.gam β - 2) / 2) * Real.sin (2 * σ))
            * Work.Spaces.pth f z σ := by ring
        _ = 1 * Work.Spaces.pth f z σ := by rw [hpow]
        _ = Work.Spaces.pth f z σ := one_mul _
    -- (5) the middle estimate
    have hmid : Real.sqrt (5 * (z ^ 3 / (1 + z) ^ 4) * Work.Spaces.HkSq β 4 f)
          * Real.sqrt (2 * (Real.pi / 4) ^ (1 - β / 10) * (10 / β) * (b - a) ^ (β / 10))
        ≤ Real.sqrt 5 * min z 1 * Work.Spaces.HkNorm β 4 f
          * Real.sqrt (2 * (Real.pi / 4) ^ (1 - β / 10) * (10 / β))
          * (b - a) ^ ((Work.Spaces.gam β - 1) / 2) := by
      have hCnn : (0 : ℝ) ≤ 2 * (Real.pi / 4) ^ (1 - β / 10) * (10 / β) := by positivity
      have hsq : Real.sqrt ((b - a) ^ (β / 10)) = (b - a) ^ ((Work.Spaces.gam β - 1) / 2) := by
        rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hban, hgam,
          show β / 10 * (1 / 2) = β / 10 / 2 by ring]
      have hfac : Real.sqrt 5 * Real.sqrt (z ^ 3 / (1 + z) ^ 4) * Work.Spaces.HkNorm β 4 f
            * Real.sqrt (2 * (Real.pi / 4) ^ (1 - β / 10) * (10 / β))
          ≤ Real.sqrt 5 * min z 1 * Work.Spaces.HkNorm β 4 f
            * Real.sqrt (2 * (Real.pi / 4) ^ (1 - β / 10) * (10 / β)) :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left (sqrt_z_cube_div_le_min hz) (Real.sqrt_nonneg 5))
            (Work.Spaces.HkNorm_nonneg β 4 f))
          (Real.sqrt_nonneg _)
      calc Real.sqrt (5 * (z ^ 3 / (1 + z) ^ 4) * Work.Spaces.HkSq β 4 f)
            * Real.sqrt (2 * (Real.pi / 4) ^ (1 - β / 10) * (10 / β) * (b - a) ^ (β / 10))
          = (Real.sqrt 5 * Real.sqrt (z ^ 3 / (1 + z) ^ 4)
              * Real.sqrt (Work.Spaces.HkSq β 4 f)
              * Real.sqrt (2 * (Real.pi / 4) ^ (1 - β / 10) * (10 / β)))
            * (b - a) ^ ((Work.Spaces.gam β - 1) / 2) := by
            rw [Real.sqrt_mul (by positivity : (0:ℝ) ≤ 5 * (z ^ 3 / (1 + z) ^ 4)),
              Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 5), Real.sqrt_mul hCnn, hsq]
            ring
        _ ≤ (Real.sqrt 5 * min z 1 * Work.Spaces.HkNorm β 4 f
              * Real.sqrt (2 * (Real.pi / 4) ^ (1 - β / 10) * (10 / β)))
            * (b - a) ^ ((Work.Spaces.gam β - 1) / 2) :=
            mul_le_mul_of_nonneg_right hfac (Real.rpow_nonneg hban _)
    -- (6) the constant
    have hconst : Real.sqrt 5 * min z 1 * Work.Spaces.HkNorm β 4 f
          * Real.sqrt (2 * (Real.pi / 4) ^ (1 - β / 10) * (10 / β))
          * (b - a) ^ ((Work.Spaces.gam β - 1) / 2)
        ≤ Real.sqrt 5 * (10 / β + 1) * min z 1 * Work.Spaces.HkNorm β 4 f
          * (b - a) ^ ((Work.Spaces.gam β - 1) / 2) := by
      have hM : (0 : ℝ) ≤ min z 1 * Work.Spaces.HkNorm β 4 f
          * (b - a) ^ ((Work.Spaces.gam β - 1) / 2) :=
        mul_nonneg (mul_nonneg (le_min hz.le zero_le_one)
          (Work.Spaces.HkNorm_nonneg β 4 f)) (Real.rpow_nonneg hban _)
      rw [show Real.sqrt 5 * min z 1 * Work.Spaces.HkNorm β 4 f
            * Real.sqrt (2 * (Real.pi / 4) ^ (1 - β / 10) * (10 / β))
            * (b - a) ^ ((Work.Spaces.gam β - 1) / 2)
          = (Real.sqrt 5 * Real.sqrt (2 * (Real.pi / 4) ^ (1 - β / 10) * (10 / β)))
            * (min z 1 * Work.Spaces.HkNorm β 4 f
              * (b - a) ^ ((Work.Spaces.gam β - 1) / 2)) by ring,
        show Real.sqrt 5 * (10 / β + 1) * min z 1 * Work.Spaces.HkNorm β 4 f
            * (b - a) ^ ((Work.Spaces.gam β - 1) / 2)
          = (Real.sqrt 5 * (10 / β + 1))
            * (min z 1 * Work.Spaces.HkNorm β 4 f
              * (b - a) ^ ((Work.Spaces.gam β - 1) / 2)) by ring]
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hSle (Real.sqrt_nonneg 5)) hM
    -- ### assemble
    calc |f z a - f z b| = |f z b - f z a| := abs_sub_comm _ _
      _ = |∫ σ in a..b, A1 σ * A2 σ| := by rw [hprod]
      _ ≤ Real.sqrt (∫ σ in a..b, (A1 σ) ^ 2) * Real.sqrt (∫ σ in a..b, (A2 σ) ^ 2) := hcs
      _ ≤ Real.sqrt (5 * (z ^ 3 / (1 + z) ^ 4) * Work.Spaces.HkSq β 4 f)
            * Real.sqrt (2 * (Real.pi / 4) ^ (1 - β / 10) * (10 / β) * (b - a) ^ (β / 10)) :=
          mul_le_mul hb1 hb2 (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
      _ ≤ Real.sqrt 5 * min z 1 * Work.Spaces.HkNorm β 4 f
            * Real.sqrt (2 * (Real.pi / 4) ^ (1 - β / 10) * (10 / β))
            * (b - a) ^ ((Work.Spaces.gam β - 1) / 2) := hmid
      _ ≤ Real.sqrt 5 * (10 / β + 1) * min z 1 * Work.Spaces.HkNorm β 4 f
            * (b - a) ^ ((Work.Spaces.gam β - 1) / 2) := hconst
  -- ### symmetry in the two angles
  rcases le_or_gt θ θ' with h | h
  · have hk := key θ θ' hθ.1 h hθ'.2
    have h1 : |θ - θ'| ^ ((Work.Spaces.gam β - 1) / 2)
        = (θ' - θ) ^ ((Work.Spaces.gam β - 1) / 2) := by
      rw [abs_sub_comm θ θ', abs_of_nonneg (sub_nonneg.mpr h)]
    rw [h1]
    exact hk
  · have hk := key θ' θ hθ'.1 h.le hθ.2
    have h1 : |f z θ - f z θ'| = |f z θ' - f z θ| := abs_sub_comm _ _
    have h2 : |θ - θ'| ^ ((Work.Spaces.gam β - 1) / 2)
        = (θ - θ') ^ ((Work.Spaces.gam β - 1) / 2) := by
      rw [abs_of_nonneg (sub_nonneg.mpr h.le)]
    rw [h1, h2]
    exact hk

end Work.FTS_RegExport.THL
