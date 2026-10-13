import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Order.Interval.Basic
import Submission.Work.FTS.CoercivityFix.Coer1T.Hardy.tail_ibp
import Submission.Work.FTS.CoercivityFix.Coer1T.Hardy.Pieces.tail_continuous

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.CoercivityFix.Coer1T.Hardy

open MeasureTheory Set Filter
open scoped Topology
open scoped Interval

/-- **Cauchy–Schwarz for the Bochner integral of real functions.**
`(∫ f g)² ≤ (∫ f²)(∫ g²)`, proved via the (non-negative) quadratic form
`t ↦ ∫ (f + t g)²` and its discriminant. -/
theorem cs_L2 {α : Type*} [MeasurableSpace α] {μ : Measure α} {f g : α → ℝ}
    (hf2 : Integrable (fun x => f x ^ 2) μ) (hg2 : Integrable (fun x => g x ^ 2) μ)
    (hfg : Integrable (fun x => f x * g x) μ) :
    (∫ x, f x * g x ∂μ) ^ 2 ≤ (∫ x, f x ^ 2 ∂μ) * (∫ x, g x ^ 2 ∂μ) := by
  set A := ∫ x, f x ^ 2 ∂μ
  set B := ∫ x, f x * g x ∂μ
  set C := ∫ x, g x ^ 2 ∂μ
  have hC0 : 0 ≤ C := integral_nonneg (fun x => sq_nonneg (g x))
  have hquad : ∀ t : ℝ, 0 ≤ A + 2 * t * B + t ^ 2 * C := by
    intro t
    have hexp : ∫ x, (f x + t * g x) ^ 2 ∂μ = A + 2 * t * B + t ^ 2 * C := by
      have h1 : (fun x => (f x + t * g x) ^ 2)
          = fun x => (f x ^ 2 + 2 * t * (f x * g x)) + t ^ 2 * g x ^ 2 := by
        funext x; ring
      rw [h1]
      rw [integral_add (f := fun x => f x ^ 2 + 2 * t * (f x * g x))
        (g := fun x => t ^ 2 * g x ^ 2) (hf2.add (hfg.const_mul (2 * t)))
        (hg2.const_mul (t ^ 2))]
      rw [integral_add hf2 (hfg.const_mul (2 * t)), integral_const_mul, integral_const_mul]
    have hnn : 0 ≤ ∫ x, (f x + t * g x) ^ 2 ∂μ := integral_nonneg (fun x => sq_nonneg _)
    linarith [hnn, hexp]
  rcases eq_or_lt_of_le hC0 with hCeq | hCpos
  · have hB0 : B = 0 := by
      by_contra hBne
      have hbad := hquad (-(A + 1) / (2 * B))
      have key : A + 2 * (-(A + 1) / (2 * B)) * B + (-(A + 1) / (2 * B)) ^ 2 * C = -1 := by
        rw [← hCeq]; field_simp; ring
      linarith [hbad, key]
    rw [hB0, ← hCeq]; norm_num
  · have hbad := hquad (-B / C)
    have key : A + 2 * (-B / C) * B + (-B / C) ^ 2 * C = A - B ^ 2 / C := by
      field_simp; ring
    have hle : B ^ 2 / C ≤ A := by linarith [hbad, key]
    have h2 : B ^ 2 ≤ A * C := by
      rw [div_le_iff₀ hCpos] at hle
      linarith [hle]
    exact h2

/-- The elementary AM–GM step for the tail Hardy inequality: pointwise
`(z · F z) · G z ≤ (1/4) F z² + z² G z²` (with `F z = ∫_{Ioi z} G`), integrated
over `[1,R]`. -/
theorem tail_amgm (G : ℝ → ℝ)
    (hint : MeasureTheory.IntegrableOn (fun s => (G s) ^ 2 * s ^ 2) (Set.Ioi 1))
    (hG : MeasureTheory.IntegrableOn G (Set.Ioi 1)) (R : ℝ) (hR : 1 < R) :
    ∫ z in (1:ℝ)..R, (z * (∫ s in Set.Ioi z, G s)) * G z
      ≤ (1/4) * (∫ z in (1:ℝ)..R, (∫ s in Set.Ioi z, G s) ^ 2)
        + ∫ z in (1:ℝ)..R, (G z) ^ 2 * z ^ 2 := by
  have hcont : ContinuousOn (fun z => ∫ s in Set.Ioi z, G s) (Set.Ici 1) :=
    Pieces.tail_continuous G hG
  have hpoint : ∀ x : ℝ, (x * (∫ s in Set.Ioi x, G s)) * G x
      ≤ (1/4) * (∫ s in Set.Ioi x, G s) ^ 2 + (G x) ^ 2 * x ^ 2 := by
    intro x
    nlinarith [sq_nonneg ((∫ s in Set.Ioi x, G s) / 2 - x * G x)]
  have hGint : IntervalIntegrable G volume (1:ℝ) R :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hR.le).mpr (hG.mono_set Set.Ioc_subset_Ioi_self)
  have hcontu : ContinuousOn (fun z => ∫ s in Set.Ioi z, G s) (Set.uIcc (1:ℝ) R) :=
    hcont.mono (by rw [Set.uIcc_of_le hR.le]; exact fun x hx => hx.1)
  have hcontA : ContinuousOn (fun z => z * (∫ s in Set.Ioi z, G s)) (Set.uIcc (1:ℝ) R) :=
    continuousOn_id.mul hcontu
  have hf : IntervalIntegrable (fun z => (z * (∫ s in Set.Ioi z, G s)) * G z) volume (1:ℝ) R :=
    hGint.continuousOn_mul hcontA
  have hA : IntervalIntegrable (fun z => (1/4) * (∫ s in Set.Ioi z, G s) ^ 2) volume (1:ℝ) R :=
    (hcontu.pow 2).intervalIntegrable.const_mul (1/4)
  have hB : IntervalIntegrable (fun z => (G z) ^ 2 * z ^ 2) volume (1:ℝ) R :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hR.le).mpr (hint.mono_set Set.Ioc_subset_Ioi_self)
  have hg : IntervalIntegrable
      (fun z => (1/4) * (∫ s in Set.Ioi z, G s) ^ 2 + (G z) ^ 2 * z ^ 2) volume (1:ℝ) R :=
    hA.add hB
  calc ∫ z in (1:ℝ)..R, (z * (∫ s in Set.Ioi z, G s)) * G z
      ≤ ∫ z in (1:ℝ)..R, ((1/4) * (∫ s in Set.Ioi z, G s) ^ 2 + (G z) ^ 2 * z ^ 2) :=
        intervalIntegral.integral_mono hR.le hf hg hpoint
    _ = (1/4) * (∫ z in (1:ℝ)..R, (∫ s in Set.Ioi z, G s) ^ 2)
        + ∫ z in (1:ℝ)..R, (G z) ^ 2 * z ^ 2 := by
        rw [intervalIntegral.integral_add (f := fun z => (1/4) * (∫ s in Set.Ioi z, G s) ^ 2)
              (g := fun z => (G z) ^ 2 * z ^ 2) hA hB, intervalIntegral.integral_const_mul]

/-- The endpoint decay needed for the sharp Hardy constant:
`R · (∫_{Ioi R} G)² → 0`, from the Cauchy–Schwarz bound `R (∫_{Ioi R} G)² ≤ ∫_{Ioi R} G² s²`. -/
theorem tail_tendsto_zero (G : ℝ → ℝ)
    (hint : MeasureTheory.IntegrableOn (fun s => (G s) ^ 2 * s ^ 2) (Set.Ioi 1))
    (hG : MeasureTheory.IntegrableOn G (Set.Ioi 1)) :
    Filter.Tendsto (fun R : ℝ => R * (∫ s in Set.Ioi R, G s) ^ 2) Filter.atTop (nhds 0) := by
  have hbound : ∀ᶠ R : ℝ in atTop,
      R * (∫ s in Set.Ioi R, G s) ^ 2 ≤ ∫ s in Set.Ioi R, (G s) ^ 2 * s ^ 2 := by
    filter_upwards [eventually_ge_atTop (1:ℝ)] with R hR1
    have hR0 : (0:ℝ) < R := lt_of_lt_of_le one_pos hR1
    have hf2 : IntegrableOn (fun x : ℝ => (G x * x) ^ 2) (Set.Ioi R) := by
      refine (hint.mono_set (Ioi_subset_Ioi hR1)).congr_fun ?_ measurableSet_Ioi
      intro x hx; ring
    have hg2 : IntegrableOn (fun x : ℝ => (x⁻¹) ^ 2) (Set.Ioi R) := by
      refine (integrableOn_Ioi_rpow_of_lt (a := (-2:ℝ)) (by norm_num) hR0).congr_fun ?_
        measurableSet_Ioi
      intro x hx
      have hx0 : (0:ℝ) < x := lt_of_lt_of_le hR0 (le_of_lt hx)
      show x ^ (-2:ℝ) = (x⁻¹) ^ 2
      rw [inv_pow, ← Real.rpow_natCast x 2, ← Real.rpow_neg hx0.le]
      simp only [Nat.cast_ofNat]
    have hfg : IntegrableOn (fun x : ℝ => (G x * x) * x⁻¹) (Set.Ioi R) := by
      refine (hG.mono_set (Ioi_subset_Ioi hR1)).congr_fun ?_ measurableSet_Ioi
      intro x hx
      have hx0 : x ≠ 0 := ne_of_gt (lt_of_lt_of_le hR0 (le_of_lt hx))
      show G x = (G x * x) * x⁻¹
      rw [mul_assoc, mul_inv_cancel₀ hx0, mul_one]
    have hcs := cs_L2 hf2 hg2 hfg
    have h_int_inv : (∫ x : ℝ, (x⁻¹) ^ 2 ∂(volume.restrict (Set.Ioi R))) = R⁻¹ := by
      calc ∫ x : ℝ, (x⁻¹) ^ 2 ∂(volume.restrict (Set.Ioi R))
          = ∫ x in Set.Ioi R, x ^ (-2:ℝ) :=
            setIntegral_congr_fun measurableSet_Ioi (fun x hx => by
              have hx0 : (0:ℝ) < x := lt_of_lt_of_le hR0 (le_of_lt hx)
              show (x⁻¹) ^ 2 = x ^ (-2:ℝ)
              rw [inv_pow, ← Real.rpow_natCast x 2, ← Real.rpow_neg hx0.le]
              simp only [Nat.cast_ofNat])
        _ = R⁻¹ := by
            rw [integral_Ioi_rpow_of_lt (a := (-2:ℝ)) (by norm_num) hR0]
            norm_num
            rw [Real.rpow_neg_one]
    rw [show (∫ x : ℝ, (G x * x) * x⁻¹ ∂(volume.restrict (Set.Ioi R))) = ∫ x in Set.Ioi R, G x
          from setIntegral_congr_fun measurableSet_Ioi (fun x hx => by
            have hx0 : x ≠ 0 := ne_of_gt (lt_of_lt_of_le hR0 (le_of_lt hx))
            show (G x * x) * x⁻¹ = G x
            rw [mul_assoc, mul_inv_cancel₀ hx0, mul_one]),
        show (∫ x : ℝ, (G x * x) ^ 2 ∂(volume.restrict (Set.Ioi R)))
            = ∫ x in Set.Ioi R, (G x) ^ 2 * x ^ 2 from
          setIntegral_congr_fun measurableSet_Ioi (fun x hx => by ring),
        h_int_inv] at hcs
    have h2 := mul_le_mul_of_nonneg_left hcs hR0.le
    have heq : R * ((∫ x in Set.Ioi R, (G x) ^ 2 * x ^ 2) * R⁻¹)
        = ∫ x in Set.Ioi R, (G x) ^ 2 * x ^ 2 := by
      rw [← mul_assoc, mul_comm R (∫ x in Set.Ioi R, (G x) ^ 2 * x ^ 2), mul_assoc,
        mul_inv_cancel₀ (ne_of_gt hR0), mul_one]
    linarith [h2, heq]
  have hlim : Tendsto (fun R : ℝ => ∫ s in Set.Ioi R, (G s) ^ 2 * s ^ 2) Filter.atTop (nhds 0) :=
    tendsto_integral_Ioi_zero (b := fun R : ℝ => R) (l := atTop)
      (f := fun s => (G s) ^ 2 * s ^ 2) tendsto_id
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' (b := atTop) (a := 0)
    (g := fun _ : ℝ => (0:ℝ)) (h := fun R : ℝ => ∫ s in Set.Ioi R, (G s) ^ 2 * s ^ 2)
    (f := fun R : ℝ => R * (∫ s in Set.Ioi R, G s) ^ 2) tendsto_const_nhds hlim ?_ hbound
  filter_upwards [eventually_ge_atTop (1:ℝ)] with R hR1
  exact mul_nonneg (by linarith) (sq_nonneg _)

/-- **Hardy inequality for the tail integral, with integrability.**
For `G` integrable on `(1,∞)` with `∫_{1}^{∞} G² s² < ∞`, the function
`z ↦ (∫_{z}^{∞} G)²` is integrable on `(1,∞)` and
`∫_1^∞ (∫_z^∞ G)² ≤ 4 ∫_1^∞ G(z)² z²`. -/
theorem Ioi_tail_sq_integrable (G : ℝ → ℝ)
    (hint : MeasureTheory.IntegrableOn (fun s => (G s) ^ 2 * s ^ 2) (Set.Ioi 1))
    (hG : MeasureTheory.IntegrableOn G (Set.Ioi 1)) :
    MeasureTheory.IntegrableOn (fun z => (∫ s in Set.Ioi z, G s) ^ 2) (Set.Ioi 1) ∧
    ∫ z in Set.Ioi 1, (∫ s in Set.Ioi z, G s) ^ 2
      ≤ 4 * ∫ s in Set.Ioi 1, (G s) ^ 2 * s ^ 2 := by
  set F : ℝ → ℝ := fun z => ∫ s in Set.Ioi z, G s with hFdef
  have hcont : ContinuousOn F (Set.Ici 1) := by
    rw [hFdef]; exact Pieces.tail_continuous G hG
  have hDnn : 0 ≤ ∫ s in Set.Ioi 1, (G s) ^ 2 * s ^ 2 :=
    integral_nonneg (fun s => mul_nonneg (sq_nonneg _) (sq_nonneg _))
  -- Uniform bound for the truncated integrals, using IBP + AM–GM + the endpoint decay.
  have hbound_all : ∀ R : ℝ, 1 < R → R * F R ^ 2 ≤ 1 →
      (∫ z in (1:ℝ)..R, F z ^ 2) ≤ 2 + 4 * (∫ s in Set.Ioi 1, (G s) ^ 2 * s ^ 2) := by
    intro R hR hsmall
    have h1 := tail_ibp G hG R hR
    have h3 := tail_amgm G hint hG R hR
    simp only [hFdef] at h1 h3 hsmall ⊢
    have hDle : (∫ z in (1:ℝ)..R, (G z) ^ 2 * z ^ 2)
        ≤ ∫ s in Set.Ioi 1, (G s) ^ 2 * s ^ 2 := by
      rw [intervalIntegral.integral_of_le hR.le]
      refine setIntegral_mono_set hint ?_ ?_
      · exact Eventually.of_forall (fun x => mul_nonneg (sq_nonneg _) (sq_nonneg _))
      · exact Eventually.of_forall (fun x hx => hx.1)
    have hW : 0 ≤ (∫ s in Set.Ioi 1, G s) ^ 2 := sq_nonneg _
    nlinarith [h1, h3, hDle, hW, hsmall]
  -- Integrability of `F²` on `(1,∞)` via boundedness of the truncated integrals.
  have hintF : IntegrableOn (fun z => F z ^ 2) (Set.Ioi 1) := by
    refine integrableOn_Ioi_of_intervalIntegral_norm_bounded
      (2 + 4 * (∫ s in Set.Ioi 1, (G s) ^ 2 * s ^ 2)) 1
      (b := fun i : ℕ => (i:ℝ) + 2) (l := atTop) ?_ ?_ ?_
    · intro i
      have hi : (1:ℝ) ≤ (i:ℝ) + 2 := by
        have h0 : (0:ℝ) ≤ (i:ℝ) := Nat.cast_nonneg i; linarith
      refine (intervalIntegrable_iff_integrableOn_Ioc_of_le hi).mp ?_
      exact ((hcont.mono (by rw [Set.uIcc_of_le hi]; exact fun x hx => hx.1)).pow 2).intervalIntegrable
    · exact tendsto_atTop_add_const_right atTop 2 (tendsto_natCast_atTop_atTop (R := ℝ))
    · have hb : Tendsto (fun i : ℕ => (i:ℝ) + 2) atTop atTop :=
        tendsto_atTop_add_const_right atTop 2 (tendsto_natCast_atTop_atTop (R := ℝ))
      filter_upwards [hb.eventually ((tail_tendsto_zero G hint hG).eventually
        (isOpen_Iio.mem_nhds (by norm_num : (0:ℝ) < 1)))] with i hsmall
      have hR : (1:ℝ) < (i:ℝ) + 2 := by
        have h0 : (0:ℝ) ≤ (i:ℝ) := Nat.cast_nonneg i; linarith
      have hsmall' : ((i:ℝ) + 2) * F ((i:ℝ) + 2) ^ 2 ≤ 1 := by
        simpa only [hFdef] using le_of_lt hsmall
      rw [show (∫ x in (1:ℝ)..((i:ℝ) + 2), ‖F x ^ 2‖) = ∫ x in (1:ℝ)..((i:ℝ) + 2), F x ^ 2
            from intervalIntegral.integral_congr
              (fun x _ => by rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)])]
      exact hbound_all ((i:ℝ) + 2) hR hsmall'
  refine ⟨hintF, ?_⟩
  change ∫ z in Set.Ioi 1, F z ^ 2 ≤ 4 * ∫ s in Set.Ioi 1, (G s) ^ 2 * s ^ 2
  -- The sharp constant, via IBP + AM–GM + the endpoint decay in the limit `R → ∞`.
  have hmain : ∀ᶠ R : ℝ in atTop,
      (1/2) * (∫ z in (1:ℝ)..R, F z ^ 2)
        ≤ R * F R ^ 2 - F 1 ^ 2 + 2 * (∫ z in (1:ℝ)..R, (G z) ^ 2 * z ^ 2) := by
    filter_upwards [eventually_gt_atTop (1:ℝ)] with R hR
    have h1 := tail_ibp G hG R hR
    have h3 := tail_amgm G hint hG R hR
    simp only [hFdef] at h1 h3 ⊢
    linarith
  have hu : Tendsto (fun R : ℝ => (1/2) * (∫ z in (1:ℝ)..R, F z ^ 2)) atTop
      (nhds ((1/2) * ∫ z in Set.Ioi 1, F z ^ 2)) :=
    (intervalIntegral_tendsto_integral_Ioi (1:ℝ) hintF (b := fun R : ℝ => R) (l := atTop)
      tendsto_id).const_mul (1/2)
  have hv : Tendsto
      (fun R : ℝ => R * F R ^ 2 - F 1 ^ 2 + 2 * (∫ z in (1:ℝ)..R, (G z) ^ 2 * z ^ 2)) atTop
      (nhds (0 - F 1 ^ 2 + 2 * (∫ z in Set.Ioi 1, (G z) ^ 2 * z ^ 2))) := by
    have hP2 : Tendsto (fun R : ℝ => R * F R ^ 2) atTop (nhds 0) := by
      simpa only [hFdef] using tail_tendsto_zero G hint hG
    have hI : Tendsto (fun R : ℝ => ∫ z in (1:ℝ)..R, (G z) ^ 2 * z ^ 2) atTop
        (nhds (∫ z in Set.Ioi 1, (G z) ^ 2 * z ^ 2)) :=
      intervalIntegral_tendsto_integral_Ioi (1:ℝ) hint (b := fun R : ℝ => R) (l := atTop) tendsto_id
    exact (hP2.sub tendsto_const_nhds).add (hI.const_mul 2)
  have hle := le_of_tendsto_of_tendsto hu hv hmain
  have hsq : 0 ≤ F 1 ^ 2 := sq_nonneg _
  linarith

end Work.FTS.CoercivityFix.Coer1T.Hardy
