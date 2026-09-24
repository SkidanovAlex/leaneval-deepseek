import Mathlib
import Submission.Work.GM.S3.Defs
import Submission.Work.GM.S3.hhat_defs
import Submission.Work.GM.S3.Iterm_eq_integral
import Submission.Work.GM.S3.osc_integral_decay
import Submission.Work.GM.S3.Rl4Aux

/-!
# Vocabulary for GM Proposition 7.1 (`Work.GM.S3.prop71_main`)

After the substitution `v₁ = u₁/u₃`, `v₂ = u₂/u₃` (Jacobian `u₃²`) in the integral
representation `Work.GM.S3.Iterm_eq_integral` of `Iterm`, the `R`-factors no longer depend on
`u₃`, and the `u₃`-integral becomes a *linear* oscillatory integral:

`innerInt N m v = ∫ e(-N(m₁v₁+m₂v₂+m₃)u₃) w₂(u₃,v₁,v₂) du₃`,  `w₂ = u₃²w(u₃)²w(v₁u₃)²w(v₂u₃)²`.

* `phas m v = m₁v₁ + m₂v₂ + m₃` is the (linear) phase;
* `pbox = [1/2,2] × [1/2,2]` is the region where `w₂` can be nonzero (GM, proof of Prop 7.1:
  "the inner integral vanishes unless `v₁,v₂ ∈ [1/2,2]`");
* `w2v v u = u² w(u)² w(v₁u)² w(v₂u)`, the `u₃`-weight (GM (7.4));
* `innerInt N m v` is the inner integral;
* `Rprod W v = R(v₁)R(v₂/v₁)R(1/v₂)`, the `v`-dependent `R`-factor.
-/

namespace Work.GM.S3

open Complex Finset MeasureTheory
open scoped BigOperators
open Submission.GM (Rfun Separated Iterm hhat hfun)

/-- The linear phase `m₁v₁ + m₂v₂ + m₃` of the oscillatory integral in GM Prop 7.1. -/
noncomputable def phas (m : ℤ × ℤ × ℤ) (v : ℝ × ℝ) : ℝ :=
  (m.1 : ℝ) * v.1 + (m.2.1 : ℝ) * v.2 + (m.2.2 : ℝ)

/-- GM, proof of Prop 7.1: the inner integral vanishes unless `v₁, v₂ ∈ [1/2,2]`. -/
def pbox : Set (ℝ × ℝ) := Set.Icc (1 / 2 : ℝ) 2 ×ˢ Set.Icc (1 / 2 : ℝ) 2

theorem measurableSet_pbox : MeasurableSet pbox :=
  (isClosed_Icc.prod isClosed_Icc).measurableSet

/-- GM (7.4): the `u₃`-weight `w₂(u₃,v₁,v₂) = u₃²w(u₃)²w(v₁u₃)²w(v₂u₃)²`. -/
noncomputable def w2v (v : ℝ × ℝ) (u : ℝ) : ℂ :=
  (u : ℂ) ^ 2 * w2C u * w2C (v.1 * u) * w2C (v.2 * u)

/-- The inner (oscillatory, linear) integral of GM Prop 7.1. -/
noncomputable def innerInt (N : ℕ) (m : ℤ × ℤ × ℤ) (v : ℝ × ℝ) : ℂ :=
  ∫ u : ℝ, Complex.exp (-(2 * Real.pi * Complex.I * ((N : ℝ) * phas m v) * u)) * w2v v u

/-- The `R`-factor `R(v₁)R(v₂/v₁)R(1/v₂)` of GM Prop 7.1. -/
noncomputable def Rprod (W : Finset ℝ) (v : ℝ × ℝ) : ℂ :=
  Rfun W v.1 * Rfun W (v.2 / v.1) * Rfun W (1 / v.2)

theorem Rfun_measurable (W : Finset ℝ) : Measurable (Rfun W) := by
  unfold Submission.GM.Rfun
  fun_prop

theorem Rprod_measurable (W : Finset ℝ) : Measurable (Rprod W) := by
  have h1 : Measurable fun v : ℝ × ℝ => Rfun W v.1 := (Rfun_measurable W).comp measurable_fst
  have h2 : Measurable fun v : ℝ × ℝ => Rfun W (v.2 / v.1) :=
    (Rfun_measurable W).comp (measurable_snd.div measurable_fst)
  have h3 : Measurable fun v : ℝ × ℝ => Rfun W (1 / v.2) :=
    (Rfun_measurable W).comp (measurable_const.div measurable_snd)
  exact (h1.mul h2).mul h3

theorem norm_Rprod_le (W : Finset ℝ) (v : ℝ × ℝ) : ‖Rprod W v‖ ≤ (W.card : ℝ) ^ 3 := by
  have h1 : ‖Rfun W v.1‖ ≤ (W.card : ℝ) := Rfun_norm_le_card W _
  have h2 : ‖Rfun W (v.2 / v.1)‖ ≤ (W.card : ℝ) := Rfun_norm_le_card W _
  have h3 : ‖Rfun W (1 / v.2)‖ ≤ (W.card : ℝ) := Rfun_norm_le_card W _
  unfold Rprod
  calc ‖Rfun W v.1 * Rfun W (v.2 / v.1) * Rfun W (1 / v.2)‖
      = ‖Rfun W v.1‖ * ‖Rfun W (v.2 / v.1)‖ * ‖Rfun W (1 / v.2)‖ := by rw [norm_mul, norm_mul]
    _ ≤ (W.card : ℝ) * (W.card : ℝ) * (W.card : ℝ) := by gcongr
    _ = (W.card : ℝ) ^ 3 := by ring

/-- If `w(u) ≠ 0` then `u ∈ [1,2]`, and for `v ∉ [1/2,2]` and `u ∈ [1,2]` we have `vu ∉ [1,2]`;
hence `w(u)w(vu) = 0` for every `u`. -/
theorem bumpW_mul_bumpW_eq_zero {v u : ℝ} (hv : v ∉ Set.Icc (1 / 2 : ℝ) 2) :
    Submission.LargeValues.bumpW u * Submission.LargeValues.bumpW (v * u) = 0 := by
  by_cases hu : Submission.LargeValues.bumpW u = 0
  · rw [hu, zero_mul]
  · have huI : u ∈ Set.Icc (1 : ℝ) 2 :=
      Submission.LargeValues.bumpW_spec.2.2.1 u hu
    have hvI : v * u ∉ Set.Icc (1 : ℝ) 2 := by
      rintro ⟨h1, h2⟩
      have hv1 : (1 / 2 : ℝ) ≤ v := by
        by_contra h
        rw [not_le] at h
        by_cases hv0 : v ≤ 0
        · nlinarith [huI.1]
        · rw [not_le] at hv0
          nlinarith [huI.1, huI.2, h, hv0]
      exact hv ⟨hv1, by by_contra h; rw [not_le] at h; nlinarith [huI.1, huI.2, h, h1, h2]⟩
    rw [Submission.LargeValues.bumpW_eq_zero_of_notMem hvI, mul_zero]

/-- `w₂(·,v)` vanishes identically unless `v ∈ [1/2,2]²`. -/
theorem w2v_eq_zero_of_not_mem {v : ℝ × ℝ} {u : ℝ}
    (hv : v.1 ∉ Set.Icc (1 / 2 : ℝ) 2 ∨ v.2 ∉ Set.Icc (1 / 2 : ℝ) 2) : w2v v u = 0 := by
  have h : w2C u * w2C (v.1 * u) = 0 ∨ w2C u * w2C (v.2 * u) = 0 := by
    rcases hv with hv | hv
    · left
      have hz : ((Submission.LargeValues.bumpW u : ℂ)) *
          ((Submission.LargeValues.bumpW (v.1 * u) : ℂ)) = 0 := by
        rw [← Complex.ofReal_mul, bumpW_mul_bumpW_eq_zero hv, Complex.ofReal_zero]
      rw [w2C, w2C]
      calc ((Submission.LargeValues.bumpW u : ℂ)) ^ 2 *
            ((Submission.LargeValues.bumpW (v.1 * u) : ℂ)) ^ 2
          = (((Submission.LargeValues.bumpW u : ℂ)) *
              ((Submission.LargeValues.bumpW (v.1 * u) : ℂ))) ^ 2 := by ring
        _ = 0 := by rw [hz]; ring
    · right
      have hz : ((Submission.LargeValues.bumpW u : ℂ)) *
          ((Submission.LargeValues.bumpW (v.2 * u) : ℂ)) = 0 := by
        rw [← Complex.ofReal_mul, bumpW_mul_bumpW_eq_zero hv, Complex.ofReal_zero]
      rw [w2C, w2C]
      calc ((Submission.LargeValues.bumpW u : ℂ)) ^ 2 *
            ((Submission.LargeValues.bumpW (v.2 * u) : ℂ)) ^ 2
          = (((Submission.LargeValues.bumpW u : ℂ)) *
              ((Submission.LargeValues.bumpW (v.2 * u) : ℂ))) ^ 2 := by ring
        _ = 0 := by rw [hz]; ring
  rcases h with h | h
  · rw [w2v, show (u : ℂ) ^ 2 * w2C u * w2C (v.1 * u) * w2C (v.2 * u)
        = (u : ℂ) ^ 2 * (w2C u * w2C (v.1 * u)) * w2C (v.2 * u) by ring, h]
    ring
  · rw [w2v, show (u : ℂ) ^ 2 * w2C u * w2C (v.1 * u) * w2C (v.2 * u)
        = (u : ℂ) ^ 2 * w2C (v.1 * u) * (w2C u * w2C (v.2 * u)) by ring, h]
    ring

/-- Integrability of a bounded measurable function whose support is contained in a compact set. -/
theorem integrable_of_measurable_bounded_support {X : Type*} [MeasurableSpace X] [TopologicalSpace X]
    [OpensMeasurableSpace X] [T2Space X] {μ : Measure X} [IsFiniteMeasureOnCompacts μ]
    {f : X → ℂ} {K : Set X} (hK : IsCompact K) (hmeas : Measurable f)
    (hsub : Function.support f ⊆ K) {C : ℝ} (hb : ∀ x, ‖f x‖ ≤ C) : Integrable f μ := by
  have hKmeas : MeasurableSet K := hK.measurableSet
  have hgi : Integrable (K.indicator fun _ => C) μ :=
    (MeasureTheory.integrableOn_const hK.measure_lt_top.ne).integrable_indicator hKmeas
  refine Integrable.mono' hgi hmeas.aestronglyMeasurable ?_
  filter_upwards with x
  by_cases hx : x ∈ K
  · rw [Set.indicator_of_mem hx]
    exact hb x
  · have hx0 : f x = 0 := by
      by_contra h
      exact hx (hsub (Function.mem_support.mpr h))
    rw [Set.indicator_of_notMem hx, hx0]
    simp


/-- The integrand of the triple integral of GM (7.3), `Iterm_eq_integral`. -/
noncomputable def IFun (N : ℕ) (W : Finset ℝ) (m : ℤ × ℤ × ℤ) (u : ℝ × ℝ × ℝ) : ℂ :=
  ((Real.fourierChar (-((N : ℝ) * ((m.1 : ℝ) * u.1 + (m.2.1 : ℝ) * u.2.1 +
      (m.2.2 : ℝ) * u.2.2))) : Circle) : ℂ) *
    (w2C u.1 * w2C u.2.1 * w2C u.2.2) *
    Rfun W (u.1 / u.2.2) * Rfun W (u.2.1 / u.1) * Rfun W (u.2.2 / u.2.1)

/-- A bound for `|w| = |bumpW|` (`iteratedDeriv 0 = id`). -/
noncomputable def Cw : ℝ := Classical.choose (Submission.LargeValues.bumpW_deriv_bdd 0)

theorem Cw_nonneg : 0 ≤ Cw := (Classical.choose_spec (Submission.LargeValues.bumpW_deriv_bdd 0)).1

theorem abs_bumpW_le_Cw (x : ℝ) : |Submission.LargeValues.bumpW x| ≤ Cw :=
  (Classical.choose_spec (Submission.LargeValues.bumpW_deriv_bdd 0)).2 x

theorem bumpW_le_Cw (x : ℝ) : Submission.LargeValues.bumpW x ≤ Cw :=
  (abs_le.mp (abs_bumpW_le_Cw x)).2

theorem norm_w2C_le (x : ℝ) : ‖w2C x‖ ≤ Cw ^ 2 := by
  rw [norm_w2C]
  exact pow_le_pow_left₀ (Submission.LargeValues.bumpW_nonneg x) (bumpW_le_Cw x) 2

theorem norm_w2v_le (w : ℝ × ℝ) (u : ℝ) : ‖w2v w u‖ ≤ 4 * Cw ^ 6 := by
  rw [w2v, norm_mul, norm_mul, norm_mul, norm_pow, norm_w2C, norm_w2C, norm_w2C,
    Complex.norm_real, Real.norm_eq_abs, sq_abs]
  have hC : 0 ≤ Cw := Cw_nonneg
  have h1 : Submission.LargeValues.bumpW u ^ 2 ≤ Cw ^ 2 :=
    pow_le_pow_left₀ (Submission.LargeValues.bumpW_nonneg u) (bumpW_le_Cw u) 2
  have h2 : Submission.LargeValues.bumpW (w.1 * u) ^ 2 ≤ Cw ^ 2 :=
    pow_le_pow_left₀ (Submission.LargeValues.bumpW_nonneg _) (bumpW_le_Cw _) 2
  have h3 : Submission.LargeValues.bumpW (w.2 * u) ^ 2 ≤ Cw ^ 2 :=
    pow_le_pow_left₀ (Submission.LargeValues.bumpW_nonneg _) (bumpW_le_Cw _) 2
  by_cases hu : Submission.LargeValues.bumpW u = 0
  · rw [hu]
    have : (0 : ℝ) ≤ 4 * Cw ^ 6 := by positivity
    nlinarith [sq_nonneg u, sq_nonneg (Submission.LargeValues.bumpW (w.1 * u)),
      sq_nonneg (Submission.LargeValues.bumpW (w.2 * u))]
  · have huI : u ∈ Set.Icc (1 : ℝ) 2 := Submission.LargeValues.bumpW_spec.2.2.1 u hu
    have hu2 : u ^ 2 ≤ 4 := by nlinarith [huI.1, huI.2]
    calc u ^ 2 * Submission.LargeValues.bumpW u ^ 2 *
          Submission.LargeValues.bumpW (w.1 * u) ^ 2 * Submission.LargeValues.bumpW (w.2 * u) ^ 2
        ≤ 4 * Cw ^ 2 * Cw ^ 2 * Cw ^ 2 := by gcongr
      _ = 4 * Cw ^ 6 := by ring


/-- The `v`-integrand of GM Prop 7.1 *after* the substitution `v₁ = u₁/u₃`, `v₂ = u₂/u₃`:
`R(v₁)R(v₂/v₁)R(1/v₂) · e(-N(m₁v₁+m₂v₂+m₃)u₃) w₂(u₃,v)`. -/
noncomputable def Gterm (N : ℕ) (W : Finset ℝ) (m : ℤ × ℤ × ℤ) (w : ℝ × ℝ) (u : ℝ) : ℂ :=
  Rprod W w * (Complex.exp (-(2 * Real.pi * Complex.I * ((N : ℝ) * phas m w) * u)) * w2v w u)

/-- `innerInt N m w = ∫ u, e(-N(m·w)u) w₂(u,w)`, so `∫ u, Gterm N W m w u = Rprod W w * innerInt N m w`. -/
theorem integral_Gterm (N : ℕ) (W : Finset ℝ) (m : ℤ × ℤ × ℤ) (w : ℝ × ℝ) :
    ∫ u : ℝ, Gterm N W m w u = Rprod W w * innerInt N m w := by
  simp only [Gterm]
  rw [MeasureTheory.integral_const_mul]
  rfl

end Work.GM.S3
