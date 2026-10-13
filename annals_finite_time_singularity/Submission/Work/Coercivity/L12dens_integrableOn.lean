/-
# Integrability of the `L₁₂`-density

The density of the fundamental model is
`L12dens K g s = ∫_θ K(θ) g(s,θ) dθ / s`
(`Work.FM.L12dens`, with `K = Work.Spaces.K`, the angular weight `3 sin θ cos²θ`).

This file proves that `L12dens K g` is integrable on `(0,∞)` as soon as `g` is smooth on a
neighbourhood of the closed quadrant `[0,∞) × [0,π/2]` and belongs to `ℋ^n` for *any* `n`
(in particular `n = 0`, i.e. only the `D_z^0`-term of the `ℋ^n`-integrand is used).

The two factors of the estimate
`|L12dens K g s| ≤ C · (s/(1+s)²) · √(∫_θ ℋ^n-integrand(g)(s,θ) dθ)`
are square-integrable on `(0,∞)`: `(s/(1+s)²)²` is an elementary integrable weight, and the
angular `ℋ^n`-integrand is integrable in `z` over `[0,∞)` by the hypothesis `HkMem α n g`.
The sublinearity of `s ↦ s/(1+s)²` at `0` is exactly what absorbs the `1/s` of the density
(the `s²` of the radial weight `w`): `1/(s · w s) = s/(1+s)²`.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Submission.Work.Spaces.Defs
import Submission.Work.FM.Defs
import Submission.Work.Elliptic.L12densFacts
import Submission.Work.Spaces.HkSq_terms

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.Coercivity

set_option autoImplicit false

/-! ## The pointwise estimate on the density -/

/-- The angular integral defining the density is dominated by the square root of the
`ℋ^n`-integrand of the slice, with the weight `s/(1+s)²`: for `s > 0`,
`|L₁₂dens g s| ≤ C (s/(1+s)²) √(∫_θ HkIntegrand α n g s θ)`.

Only the `D_z^0`-term of `HkIntegrand` is used, so the statement is uniform in `n`. -/
private theorem L12dens_abs_le_gen_aux (α : ℝ) (n : ℕ) (g : ℝ → ℝ → ℝ)
    (hsm : Work.Spaces.SmoothNbhd g) (hmem : Work.Spaces.HkMem α n g) :
    ∃ C : ℝ, 0 < C ∧ ∀ s : ℝ, 0 < s →
      |Work.Elliptic.L12dens g s| ≤ C * (s / (1 + s) ^ 2)
        * Real.sqrt (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α n g s θ) := by
  refine ⟨Real.sqrt (∫ θ in Work.Spaces.Iθ, Work.Elliptic.Ktheta θ ^ 2) + 1, by positivity,
    fun s hs => ?_⟩
  have hw_pos : 0 < Work.Spaces.w s := by rw [Work.Spaces.w]; positivity
  have hsin_cont : ContinuousOn (fun θ => g s θ) (Set.uIcc (0 : ℝ) (π/2)) := by
    rw [Set.uIcc_of_le (by positivity : (0 : ℝ) ≤ π/2)]
    exact Work.Elliptic.continuousOn_slice_theta_Iθ g hsm (by simp only [Set.mem_Ioi]; linarith)
  -- pointwise domination of `g²` by the `ℋ^n`-integrand
  have hpt : ∀ θ : ℝ, 0 < θ → θ < π/2 →
      (g s θ) ^ 2 ≤ Work.Spaces.HkIntegrand α n g s θ / (Work.Spaces.w s) ^ 2 := by
    intro θ hθ0 hθ1
    have hsin : 0 < Real.sin (2 * θ) :=
      Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos])
    set S : ℝ := (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2) with hSdef
    have hS : 0 < S := by rw [hSdef]; exact Real.rpow_pos_of_pos hsin _
    have hkey := Work.Spaces.sq_le_HkIntegrand_z α n g s θ 0 (Nat.zero_le n)
    simp only [Work.Spaces.DzIter_zero] at hkey
    have hrewrite : (g s θ) ^ 2
        = (g s θ * (Work.Spaces.w s / S)) ^ 2 * (S / Work.Spaces.w s) ^ 2 := by
      rw [mul_pow, div_pow, div_pow]
      field_simp
    have hSsq : S ^ 2 ≤ (1 : ℝ) := by
      have h2 : S ^ 2 = (Real.sin (2 * θ)) ^ Work.Spaces.eta := by
        rw [hSdef, ← Real.rpow_natCast, ← Real.rpow_mul (le_of_lt hsin)]
        norm_num
      calc S ^ 2 = (Real.sin (2 * θ)) ^ Work.Spaces.eta := h2
        _ ≤ 1 := Real.rpow_le_one (le_of_lt hsin) (Real.sin_le_one _)
            (le_of_lt Work.Spaces.eta_pos)
    have hSw : (S / Work.Spaces.w s) ^ 2 ≤ 1 / (Work.Spaces.w s) ^ 2 := by
      rw [div_pow, div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith [hSsq, pow_pos hw_pos 2]
    rw [hrewrite]
    refine le_trans (mul_le_mul_of_nonneg_right hkey (sq_nonneg _)) ?_
    refine le_trans (mul_le_mul_of_nonneg_left hSw
      (Work.Spaces.HkIntegrand_nonneg α n g s θ)) ?_
    rw [one_div, div_eq_mul_inv]
  have hg2_int : IntegrableOn (fun θ => (g s θ) ^ 2) Work.Spaces.Iθ :=
    ((Work.Elliptic.continuousOn_slice_theta_Iθ g hsm
      (by simp only [Set.mem_Ioi]; linarith)).pow 2).integrableOn_compact isCompact_Icc
  have hk_int : IntegrableOn (fun θ => Work.Spaces.HkIntegrand α n g s θ / (Work.Spaces.w s) ^ 2)
      Work.Spaces.Iθ := (hmem.1 s hs.le).div_const _
  have hg2_le : ∫ θ in Work.Spaces.Iθ, (g s θ) ^ 2
      ≤ (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α n g s θ) / (Work.Spaces.w s) ^ 2 := by
    refine le_trans (integral_mono_ae hg2_int hk_int (Work.Elliptic.ae_restrict_Iθ_of_Ioo hpt)) ?_
    rw [MeasureTheory.integral_div]
  -- Cauchy–Schwarz in the angle
  have hCS : |Work.Elliptic.angMoment g s| ≤ Real.sqrt (∫ θ in Work.Spaces.Iθ, Work.Elliptic.Ktheta θ ^ 2)
      * Real.sqrt (∫ θ in Work.Spaces.Iθ, (g s θ) ^ 2) := by
    have h := Work.Spaces.hardyZ_interval_integral_mul_le_sqrt 0 (π/2) (by positivity)
      (f := Work.Elliptic.Ktheta) (g := fun θ => g s θ)
      Work.Elliptic.continuous_ktheta.continuousOn hsin_cont
    simpa only [Work.Elliptic.angMoment,
      ← Work.Elliptic.integral_Iθ_eq_interval_aux (fun θ => Work.Elliptic.Ktheta θ * g s θ),
      ← Work.Elliptic.integral_Iθ_eq_interval_aux (fun θ => Work.Elliptic.Ktheta θ ^ 2),
      ← Work.Elliptic.integral_Iθ_eq_interval_aux (fun θ => (g s θ) ^ 2)] using h
  have hsqrt_le : Real.sqrt (∫ θ in Work.Spaces.Iθ, (g s θ) ^ 2)
      ≤ Real.sqrt (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α n g s θ) / Work.Spaces.w s := by
    refine le_trans (Real.sqrt_le_sqrt hg2_le) ?_
    rw [Real.sqrt_div (integral_nonneg fun θ => Work.Spaces.HkIntegrand_nonneg α n g s θ),
      Real.sqrt_sq_eq_abs, abs_of_pos hw_pos]
  have hmain : |Work.Elliptic.L12dens g s| ≤ Real.sqrt (∫ θ in Work.Spaces.Iθ, Work.Elliptic.Ktheta θ ^ 2)
      * ((s / (1 + s) ^ 2)
        * Real.sqrt (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α n g s θ)) := by
    have hstep : |Work.Elliptic.angMoment g s| / s
        ≤ (Real.sqrt (∫ θ in Work.Spaces.Iθ, Work.Elliptic.Ktheta θ ^ 2)
          * (Real.sqrt (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α n g s θ)
            / Work.Spaces.w s)) / s := by
      rw [div_le_div_iff_of_pos_right hs]
      exact le_trans hCS (mul_le_mul_of_nonneg_left hsqrt_le (Real.sqrt_nonneg _))
    calc |Work.Elliptic.L12dens g s| = |Work.Elliptic.angMoment g s| / s := by
          rw [Work.Elliptic.L12dens_eq_angMoment_div, abs_div, abs_of_pos hs]
      _ ≤ _ := hstep
      _ = Real.sqrt (∫ θ in Work.Spaces.Iθ, Work.Elliptic.Ktheta θ ^ 2)
            * ((s / (1 + s) ^ 2)
              * Real.sqrt (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α n g s θ)) := by
          rw [Work.Spaces.w]
          field_simp
  refine le_trans hmain ?_
  have hX : 0 ≤ (s / (1 + s) ^ 2)
      * Real.sqrt (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α n g s θ) :=
    mul_nonneg (by positivity) (Real.sqrt_nonneg _)
  calc Real.sqrt (∫ θ in Work.Spaces.Iθ, Work.Elliptic.Ktheta θ ^ 2)
        * ((s / (1 + s) ^ 2)
          * Real.sqrt (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α n g s θ))
      ≤ (Real.sqrt (∫ θ in Work.Spaces.Iθ, Work.Elliptic.Ktheta θ ^ 2) + 1)
        * ((s / (1 + s) ^ 2)
          * Real.sqrt (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α n g s θ)) :=
        mul_le_mul_of_nonneg_right (le_add_of_nonneg_right zero_le_one) hX
    _ = (Real.sqrt (∫ θ in Work.Spaces.Iθ, Work.Elliptic.Ktheta θ ^ 2) + 1) * (s / (1 + s) ^ 2)
        * Real.sqrt (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α n g s θ) := by ring

/-! ## Definitional identification of the two densities -/

/-- The elliptic `L₁₂`-density is the fundamental-model density: both are
`∫_θ K(θ) g(s,θ) dθ / s` with the angular weight `K(θ) = 3 sin θ cos²θ`, and
`Iθ = Icc 0 (π/2)`. -/
theorem L12dens_eq_fm (g : ℝ → ℝ → ℝ) :
    Work.FM.L12dens Work.Spaces.K g = Work.Elliptic.L12dens g := by
  funext s
  simp only [Work.FM.L12dens, Work.Elliptic.L12dens, Work.Spaces.Iθ,
    Work.Elliptic.Ktheta, Work.Spaces.K]

/-! ## Integrability -/

theorem L12dens_integrableOn (α : ℝ) (n : ℕ) (g : ℝ → ℝ → ℝ)
    (hsm : Work.Spaces.SmoothNbhd g) (hmem : Work.Spaces.HkMem α n g) :
    MeasureTheory.IntegrableOn (Work.FM.L12dens Work.Spaces.K g) (Set.Ioi 0) := by
  rw [L12dens_eq_fm g]
  obtain ⟨C, hCpos, hCbd⟩ := L12dens_abs_le_gen_aux α n g hsm hmem
  -- the two factors of the pointwise bound are integrable
  have hH_int : IntegrableOn
      (fun s => ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α n g s θ) (Set.Ioi 0) :=
    hmem.2.mono_set Set.Ioi_subset_Ici_self
  have hdom : IntegrableOn (fun s => (C / 2) * ((s / (1 + s) ^ 2) ^ 2
      + ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α n g s θ)) (Set.Ioi 0) :=
    (Work.Elliptic.psi_sq_integrable_aux.add hH_int).const_mul (C / 2)
  have hcontOn : ContinuousOn (Work.Elliptic.L12dens g) (Set.Ioi 0) :=
    Work.Elliptic.L12dens_continuousOn_aux g hsm
  refine hdom.mono' (hcontOn.aestronglyMeasurable measurableSet_Ioi) ?_
  filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with s hs
  have hHnn : 0 ≤ ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α n g s θ :=
    integral_nonneg fun θ => Work.Spaces.HkIntegrand_nonneg α n g s θ
  have hAM : 2 * ((s / (1 + s) ^ 2)
      * Real.sqrt (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α n g s θ))
      ≤ (s / (1 + s) ^ 2) ^ 2
        + ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α n g s θ := by
    nlinarith [sq_nonneg ((s / (1 + s) ^ 2)
        - Real.sqrt (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α n g s θ)),
      Real.sq_sqrt hHnn]
  rw [Real.norm_eq_abs]
  calc |Work.Elliptic.L12dens g s| ≤ C * (s / (1 + s) ^ 2)
        * Real.sqrt (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α n g s θ) := hCbd s hs
    _ = (C / 2) * (2 * ((s / (1 + s) ^ 2)
        * Real.sqrt (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α n g s θ))) := by ring
    _ ≤ (C / 2) * ((s / (1 + s) ^ 2) ^ 2
        + ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α n g s θ) :=
        mul_le_mul_of_nonneg_left hAM (by linarith)

end Work.Coercivity
