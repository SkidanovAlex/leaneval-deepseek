import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Average
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Submission.Work.FTS.TransportS.TvUniform.csc_sqrt_specialise
import Submission.Work.FTS.TransportS.TvUniform.integral_sqrt_mul_sqrt_le

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.TransportS.T2SupB2.TvSub

open MeasureTheory

/-- On a subinterval `[a,b]` of `(0, π/2)` the profile weight is positive. -/
theorem sin_two_pos_of_mem_Icc {a b t : ℝ} (ha : 0 < a) (hb : b < Real.pi / 2)
    (ht : t ∈ Set.Icc a b) : 0 < Real.sin (2 * t) := by
  refine Real.sin_pos_of_pos_of_lt_pi (by linarith [ht.1]) ?_
  linarith [ht.2, hb]

/-- **A point below the average**, on an arbitrary interval `[a,b]` with `a < b`: a function
integrable there is at most its own average `(b-a)⁻¹ ∫_{[a,b]} f` at some point of `[a,b]`.
(No continuity is needed; it is the minimum of an integrable function versus its mean.) -/
theorem exists_min_le_average_Icc {f : ℝ → ℝ} {a b : ℝ} (hab : a < b)
    (hint : IntegrableOn f (Set.Icc a b)) :
    ∃ θ₀ ∈ Set.Icc a b, f θ₀ ≤ (b - a)⁻¹ * ∫ t in Set.Icc a b, f t := by
  have hμ0 : volume (Set.Icc a b) ≠ 0 := by
    rw [Real.volume_Icc]
    exact ENNReal.ofReal_ne_zero_iff.mpr (by linarith)
  have hμtop : volume (Set.Icc a b) ≠ ⊤ := by
    rw [Real.volume_Icc]
    exact ENNReal.ofReal_ne_top
  obtain ⟨x, hx, hle⟩ := exists_le_setAverage (μ := volume) (s := Set.Icc a b)
    (f := f) hμ0 hμtop hint
  refine ⟨x, hx, ?_⟩
  rw [setAverage_eq volume f (Set.Icc a b), Real.volume_real_Icc_of_le hab.le,
    smul_eq_mul] at hle
  exact hle

/-- For `a ≤ u ≤ v ≤ b`, the interval integral of a nonnegative function is at most its set
integral over `Icc a b`. -/
theorem intervalIntegral_le_setIntegral_Icc {p : ℝ → ℝ} {a b u v : ℝ}
    (hau : a ≤ u) (huv : u ≤ v) (hvb : v ≤ b)
    (hpnn : ∀ t ∈ Set.Icc a b, 0 ≤ p t)
    (hpint : IntegrableOn p (Set.Icc a b)) :
    ∫ t in u..v, p t ≤ ∫ t in Set.Icc a b, p t := by
  rw [intervalIntegral.integral_of_le huv]
  refine setIntegral_mono_set hpint ?_ ?_
  · exact ae_restrict_of_forall_mem measurableSet_Icc hpnn
  · exact Filter.Eventually.of_forall fun t ht =>
      ⟨le_trans hau ht.1.le, le_trans ht.2 hvb⟩

/-- **The total-variation bound, integrated form, over a subinterval.**  Same as
`TvUniform.integral_tv_le`, with the outer interval `[0, π/2]` replaced by `[a,b]`. -/
theorem integral_tv_le_Icc {F p q : ℝ → ℝ} {a b u v : ℝ}
    (hau : a ≤ u) (huv : u ≤ v) (hvb : v ≤ b)
    (hFpq : Set.EqOn F (fun θ => 2 * (Real.sqrt (p θ) * Real.sqrt (q θ))) (Set.Ioo u v))
    (hpnn : ∀ θ ∈ Set.Icc a b, 0 ≤ p θ)
    (hqnn : ∀ θ ∈ Set.Icc a b, 0 ≤ q θ)
    (hpint : IntegrableOn p (Set.Icc a b))
    (hqint : IntegrableOn q (Set.Icc a b)) :
    ∫ θ in u..v, F θ
      ≤ 2 * Real.sqrt ((∫ θ in Set.Icc a b, p θ) * (∫ θ in Set.Icc a b, q θ)) := by
  have hsub : Set.Ioc u v ⊆ Set.Icc a b := fun x hx =>
    ⟨le_trans hau hx.1.le, le_trans hx.2 hvb⟩
  have hpI : IntegrableOn p (Set.Ioc u v) := hpint.mono_set hsub
  have hqI : IntegrableOn q (Set.Ioc u v) := hqint.mono_set hsub
  have hpn' : 0 ≤ᵐ[volume.restrict (Set.Ioc u v)] p :=
    ae_restrict_of_forall_mem measurableSet_Ioc fun x hx => hpnn x (hsub hx)
  have hqn' : 0 ≤ᵐ[volume.restrict (Set.Ioc u v)] q :=
    ae_restrict_of_forall_mem measurableSet_Ioc fun x hx => hqnn x (hsub hx)
  have hCS := Work.FTS.TransportS.TvUniform.integral_sqrt_mul_sqrt_le
    (volume.restrict (Set.Ioc u v)) hpn' hqn' hpI hqI
  have hCS' : ∫ θ in Set.Ioc u v, Real.sqrt (p θ) * Real.sqrt (q θ)
      ≤ Real.sqrt (∫ θ in Set.Ioc u v, p θ) * Real.sqrt (∫ θ in Set.Ioc u v, q θ) := hCS
  have hIp' : ∫ θ in Set.Ioc u v, p θ ≤ ∫ θ in Set.Icc a b, p θ := by
    rw [← intervalIntegral.integral_of_le huv]
    exact intervalIntegral_le_setIntegral_Icc hau huv hvb hpnn hpint
  have hIq' : ∫ θ in Set.Ioc u v, q θ ≤ ∫ θ in Set.Icc a b, q θ := by
    rw [← intervalIntegral.integral_of_le huv]
    exact intervalIntegral_le_setIntegral_Icc hau huv hvb hqnn hqint
  have hA0 : 0 ≤ ∫ θ in Set.Icc a b, p θ := setIntegral_nonneg measurableSet_Icc hpnn
  have hstep : ∫ θ in Set.Ioc u v, Real.sqrt (p θ) * Real.sqrt (q θ)
      ≤ Real.sqrt (∫ θ in Set.Icc a b, p θ) * Real.sqrt (∫ θ in Set.Icc a b, q θ) :=
    le_trans hCS' (mul_le_mul (Real.sqrt_le_sqrt hIp') (Real.sqrt_le_sqrt hIq')
      (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
  have hcongr : ∫ θ in u..v, F θ
      = ∫ θ in u..v, 2 * (Real.sqrt (p θ) * Real.sqrt (q θ)) :=
    intervalIntegral.integral_congr_Ioo_of_le huv hFpq
  rw [hcongr, intervalIntegral.integral_const_mul]
  calc 2 * ∫ θ in u..v, Real.sqrt (p θ) * Real.sqrt (q θ)
      = 2 * ∫ θ in Set.Ioc u v, Real.sqrt (p θ) * Real.sqrt (q θ) := by
        rw [intervalIntegral.integral_of_le huv]
    _ ≤ 2 * (Real.sqrt (∫ θ in Set.Icc a b, p θ)
          * Real.sqrt (∫ θ in Set.Icc a b, q θ)) :=
        mul_le_mul_of_nonneg_left hstep (by norm_num)
    _ = 2 * Real.sqrt ((∫ θ in Set.Icc a b, p θ) * (∫ θ in Set.Icc a b, q θ)) := by
        rw [Real.sqrt_mul hA0]

-- `hcont` is part of the assigned statement but is not needed by the argument: the minimum of an
-- integrable function lies below its mean without any continuity assumption.
set_option linter.unusedVariables false in
theorem tv_bound_subinterval {Ξ Ξ₁ : ℝ → ℝ} {c a b x : ℝ}
    (hab : a < b) (ha : 0 < a) (hb : b < Real.pi / 2)
    (hx : x ∈ Set.Icc a b)
    (hcont : ContinuousOn Ξ (Set.Icc a b))
    (hΞnn : ∀ t ∈ Set.Icc a b, 0 ≤ Ξ t)
    (hΞ₁nn : ∀ t ∈ Set.Icc a b, 0 ≤ Ξ₁ t)
    (hTV : ∀ u v : ℝ, a ≤ u → u ≤ v → v ≤ b →
      |Ξ v - Ξ u| ≤ ∫ t in u..v, 2 * (Real.sin (2 * t))⁻¹ * Real.sqrt (Ξ t * Ξ₁ t))
    (hintΞ : MeasureTheory.IntegrableOn Ξ (Set.Icc a b))
    (hintA : MeasureTheory.IntegrableOn
      (fun t : ℝ => Ξ t * (Real.sin (2 * t)) ^ (-c)) (Set.Icc a b))
    (hintB : MeasureTheory.IntegrableOn
      (fun t : ℝ => Ξ₁ t * (Real.sin (2 * t)) ^ (c - 2)) (Set.Icc a b)) :
    Ξ x ≤ (2 / (b - a)) * (∫ t in Set.Icc a b, Ξ t)
      + 2 * Real.sqrt
          ((∫ t in Set.Icc a b, Ξ t * (Real.sin (2 * t)) ^ (-c))
            * (∫ t in Set.Icc a b, Ξ₁ t * (Real.sin (2 * t)) ^ (c - 2))) := by
  -- a point of `[a,b]` at which `Ξ` is below its average
  obtain ⟨θ₀, hθ₀, hθ₀le⟩ := exists_min_le_average_Icc (f := Ξ) hab hintΞ
  have hI0 : 0 ≤ ∫ t in Set.Icc a b, Ξ t := setIntegral_nonneg measurableSet_Icc hΞnn
  have hθ₀le' : Ξ θ₀ ≤ (2 / (b - a)) * (∫ t in Set.Icc a b, Ξ t) := by
    have h1 : (b - a)⁻¹ ≤ 2 / (b - a) := by
      rw [div_eq_mul_inv]
      have h2 : (0 : ℝ) ≤ (b - a)⁻¹ := inv_nonneg.mpr (by linarith)
      linarith
    have h2 : (b - a)⁻¹ * (∫ t in Set.Icc a b, Ξ t)
        ≤ (2 / (b - a)) * (∫ t in Set.Icc a b, Ξ t) :=
      mul_le_mul_of_nonneg_right h1 hI0
    exact le_trans hθ₀le h2
  -- nonnegativity of the two weighted profiles on `[a,b]`
  have hpnn : ∀ t ∈ Set.Icc a b,
      0 ≤ Ξ t * (Real.sin (2 * t)) ^ (-c) := fun t ht =>
    mul_nonneg (hΞnn t ht) (Real.rpow_nonneg (le_of_lt (sin_two_pos_of_mem_Icc ha hb ht)) _)
  have hqnn : ∀ t ∈ Set.Icc a b,
      0 ≤ Ξ₁ t * (Real.sin (2 * t)) ^ (c - 2) := fun t ht =>
    mul_nonneg (hΞ₁nn t ht) (Real.rpow_nonneg (le_of_lt (sin_two_pos_of_mem_Icc ha hb ht)) _)
  -- the pointwise identification of the two forms of the total-variation integrand
  have hFpq : ∀ {u v : ℝ}, a ≤ u → v ≤ b →
      Set.EqOn (fun t => 2 * (Real.sin (2 * t))⁻¹ * Real.sqrt (Ξ t * Ξ₁ t))
        (fun t => 2 * (Real.sqrt (Ξ t * (Real.sin (2 * t)) ^ (-c))
          * Real.sqrt (Ξ₁ t * (Real.sin (2 * t)) ^ (c - 2)))) (Set.Ioo u v) := by
    intro u v hau hvb t ht
    have htA : t ∈ Set.Icc a b := ⟨le_trans hau ht.1.le, le_trans ht.2.le hvb⟩
    have ht0 : 0 < t := lt_of_lt_of_le ha htA.1
    have ht1 : t < Real.pi / 2 := lt_of_le_of_lt htA.2 hb
    have h := Work.FTS.TransportS.TvUniform.csc_sqrt_specialise (c := c) ⟨ht0, ht1⟩
      (hΞnn t htA) (hΞ₁nn t htA)
    simpa only [mul_assoc] using h
  -- the uniform bound for the total variation between `x` and `θ₀`
  have hTVb : |Ξ x - Ξ θ₀| ≤ 2 * Real.sqrt
      ((∫ t in Set.Icc a b, Ξ t * (Real.sin (2 * t)) ^ (-c))
        * (∫ t in Set.Icc a b, Ξ₁ t * (Real.sin (2 * t)) ^ (c - 2))) := by
    rcases le_total x θ₀ with hle | hle
    · have h1 := hTV x θ₀ hx.1 hle hθ₀.2
      have h2 := integral_tv_le_Icc
        (F := fun t => 2 * (Real.sin (2 * t))⁻¹ * Real.sqrt (Ξ t * Ξ₁ t))
        (p := fun t => Ξ t * (Real.sin (2 * t)) ^ (-c))
        (q := fun t => Ξ₁ t * (Real.sin (2 * t)) ^ (c - 2))
        hx.1 hle hθ₀.2 (hFpq hx.1 hθ₀.2) hpnn hqnn hintA hintB
      rw [abs_sub_comm]
      exact le_trans h1 h2
    · have h1 := hTV θ₀ x hθ₀.1 hle hx.2
      have h2 := integral_tv_le_Icc
        (F := fun t => 2 * (Real.sin (2 * t))⁻¹ * Real.sqrt (Ξ t * Ξ₁ t))
        (p := fun t => Ξ t * (Real.sin (2 * t)) ^ (-c))
        (q := fun t => Ξ₁ t * (Real.sin (2 * t)) ^ (c - 2))
        hθ₀.1 hle hx.2 (hFpq hθ₀.1 hx.2) hpnn hqnn hintA hintB
      exact le_trans h1 h2
  calc Ξ x = Ξ θ₀ + (Ξ x - Ξ θ₀) := by ring
    _ ≤ Ξ θ₀ + |Ξ x - Ξ θ₀| := by linarith [le_abs_self (Ξ x - Ξ θ₀)]
    _ ≤ (2 / (b - a)) * (∫ t in Set.Icc a b, Ξ t)
        + 2 * Real.sqrt
            ((∫ t in Set.Icc a b, Ξ t * (Real.sin (2 * t)) ^ (-c))
              * (∫ t in Set.Icc a b, Ξ₁ t * (Real.sin (2 * t)) ^ (c - 2))) :=
        add_le_add hθ₀le' hTVb

end Work.FTS.TransportS.T2SupB2.TvSub
