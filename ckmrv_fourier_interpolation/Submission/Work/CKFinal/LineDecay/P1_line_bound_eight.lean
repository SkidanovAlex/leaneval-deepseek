import Mathlib
import Submission.Work.CKFinal.LineDecay.Defs
import Submission.Work.CKFinal.LineDecay.PhiAxis
import Submission.Work.CKFinal.LineDecay.Ncusp8Clean
import Submission.Work.CKFinal.LineDecay.qParamFun_line_norm_sub
import Submission.Work.CKFinal.LineDecay.sinSqC_gaussWeight_bound
import Submission.Work.CKFinal.rpow_exp_neg_bound
import Submission.Work.Asymptotics.KPlus_slash_bound_half
import Submission.Work.Asymptotics.divisor_qdiff_lower
import Submission.Work.Asymptotics.KPlusFunnel.ZFacts
import Submission.Work.Asymptotics.KMinusCuspBallDefs

open UpperHalfPlane MeasureTheory
open scoped Topology Manifold

namespace Work.CKFinal.LineDecay

noncomputable section

/-- `(1+u)^A e^{-πu}` is bounded on `u ≥ 0`. -/
private lemma one_add_rpow_exp_bound (A : ℝ) (hA : 0 ≤ A) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ u : ℝ, 0 ≤ u →
      (1 + u) ^ A * Real.exp (-(Real.pi * u)) ≤ K := by
  refine ⟨2 ^ A * max 1 ((1 / Real.pi) ^ A * (A / Real.exp 1) ^ A) + 1, by positivity,
    fun u hu => ?_⟩
  have hmax1 : (0:ℝ) ≤ max 1 ((1 / Real.pi) ^ A * (A / Real.exp 1) ^ A) :=
    le_trans zero_le_one (le_max_left _ _)
  rcases le_or_gt u 1 with h1 | h1
  · have h2 : (1 + u) ^ A ≤ 2 ^ A := Real.rpow_le_rpow (by positivity) (by linarith) hA
    have h3 : Real.exp (-(Real.pi * u)) ≤ 1 :=
      Real.exp_le_one_iff.mpr (by nlinarith [hu, Real.pi_pos])
    have h4 : (2:ℝ) ^ A * 1 ≤ 2 ^ A * max 1 ((1 / Real.pi) ^ A * (A / Real.exp 1) ^ A) :=
      mul_le_mul_of_nonneg_left (le_max_left _ _) (by positivity)
    calc (1 + u) ^ A * Real.exp (-(Real.pi * u))
        ≤ 2 ^ A * 1 := mul_le_mul h2 h3 (Real.exp_nonneg _) (by positivity)
      _ ≤ 2 ^ A * max 1 ((1 / Real.pi) ^ A * (A / Real.exp 1) ^ A) + 1 := by linarith
  · have h2 : (1 + u) ^ A ≤ 2 ^ A * u ^ A := by
      have hle : 1 + u ≤ 2 * u := by linarith
      calc (1 + u) ^ A ≤ (2 * u) ^ A := Real.rpow_le_rpow (by positivity) hle hA
        _ = 2 ^ A * u ^ A := Real.mul_rpow (by norm_num) (by positivity)
    have h3 : u ^ A * Real.exp (-(Real.pi * u))
        ≤ (1 / Real.pi) ^ A * (A / Real.exp 1) ^ A := by
      have hb := rpow_exp_neg_bound A (Real.pi * u) hA (by positivity)
      have hup : u ^ A = (1 / Real.pi) ^ A * (Real.pi * u) ^ A := by
        calc u ^ A = ((1 / Real.pi) * (Real.pi * u)) ^ A := by
              congr 1
              field_simp
          _ = (1 / Real.pi) ^ A * (Real.pi * u) ^ A :=
              Real.mul_rpow (by positivity) (by positivity)
      rw [hup]
      calc (1 / Real.pi) ^ A * (Real.pi * u) ^ A * Real.exp (-(Real.pi * u))
          = (1 / Real.pi) ^ A * ((Real.pi * u) ^ A * Real.exp (-(Real.pi * u))) := by ring
        _ ≤ (1 / Real.pi) ^ A * (A / Real.exp 1) ^ A :=
            mul_le_mul_of_nonneg_left hb (by positivity)
    have h4 : (0:ℝ) ≤ (1 / Real.pi) ^ A * (A / Real.exp 1) ^ A := by positivity
    have h5 : (2:ℝ) ^ A * ((1 / Real.pi) ^ A * (A / Real.exp 1) ^ A)
        ≤ 2 ^ A * max 1 ((1 / Real.pi) ^ A * (A / Real.exp 1) ^ A) :=
      mul_le_mul_of_nonneg_left (le_max_right _ _) (by positivity)
    calc (1 + u) ^ A * Real.exp (-(Real.pi * u))
        ≤ (2 ^ A * u ^ A) * Real.exp (-(Real.pi * u)) :=
          mul_le_mul_of_nonneg_right h2 (Real.exp_nonneg _)
      _ = 2 ^ A * (u ^ A * Real.exp (-(Real.pi * u))) := by ring
      _ ≤ 2 ^ A * ((1 / Real.pi) ^ A * (A / Real.exp 1) ^ A) :=
          mul_le_mul_of_nonneg_left h3 (by positivity)
      _ ≤ 2 ^ A * max 1 ((1 / Real.pi) ^ A * (A / Real.exp 1) ^ A) + 1 := by linarith

/-- The scalar estimate. -/
theorem axis_exp_scalar_aux (A : ℝ) (hA : 0 ≤ A) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ y s : ℝ, 1 ≤ y → 1 ≤ s →
      (1 + s) ^ A * (1 / s ^ 2) * Real.exp (-(Real.pi * s)) /
          (1 + Real.exp (2 * Real.pi * (y - s)))
        ≤ K * (1 + y) ^ (2 * A) * Real.exp (-(Real.pi * y)) := by
  obtain ⟨K2, hK2, hb2⟩ := one_add_rpow_exp_bound A hA
  refine ⟨max 1 K2, by positivity, fun y s hy hs => ?_⟩
  have hs0 : (0:ℝ) < s := lt_of_lt_of_le one_pos hs
  have hspos' : (0:ℝ) < s ^ 2 := by positivity
  have hden : (0:ℝ) < 1 + Real.exp (2 * Real.pi * (y - s)) := by positivity
  have h1y : (1:ℝ) ≤ 1 + y := by linarith
  have h2A : (1:ℝ) ≤ (1 + y) ^ (2 * A) := Real.one_le_rpow h1y (by positivity)
  have hsp2 : (1:ℝ) / s ^ 2 ≤ 1 := by
    rw [div_le_one hspos']; nlinarith [hs]
  have hsA : (0:ℝ) ≤ (1 + s) ^ A := by positivity
  have hbase : (1 + s) ^ A * (1 / s ^ 2) * Real.exp (-(Real.pi * s))
        / (1 + Real.exp (2 * Real.pi * (y - s)))
      ≤ (1 + s) ^ A * Real.exp (-(Real.pi * s)) := by
    rw [div_le_iff₀ hden]
    calc (1 + s) ^ A * (1 / s ^ 2) * Real.exp (-(Real.pi * s))
        ≤ (1 + s) ^ A * 1 * Real.exp (-(Real.pi * s)) := by
          apply mul_le_mul_of_nonneg_right _ (Real.exp_nonneg _)
          exact mul_le_mul_of_nonneg_left hsp2 hsA
      _ ≤ (1 + s) ^ A * Real.exp (-(Real.pi * s))
            * (1 + Real.exp (2 * Real.pi * (y - s))) := by
          have hpos2 : (0:ℝ) ≤ (1 + s) ^ A * Real.exp (-(Real.pi * s)) := by positivity
          nlinarith [Real.exp_nonneg (2 * Real.pi * (y - s)), hpos2]
      _ = (1 + s) ^ A * Real.exp (-(Real.pi * s))
            * (1 + Real.exp (2 * Real.pi * (y - s))) := rfl
  have hmax1 : (1:ℝ) ≤ max 1 K2 := le_max_left _ _
  have hK2max : K2 ≤ max 1 K2 := le_max_right _ _
  rcases le_or_gt s y with hle | hlt
  · -- `s ≤ y`
    have hden2 : (0:ℝ) < 1 + Real.exp (2 * Real.pi * (y - s)) := hden
    have hE2 : Real.exp (-(Real.pi * s)) / (1 + Real.exp (2 * Real.pi * (y - s)))
        ≤ Real.exp (-(Real.pi * y)) := by
      have h2 : (1:ℝ) / (1 + Real.exp (2 * Real.pi * (y - s)))
          ≤ Real.exp (-(2 * Real.pi * (y - s))) := by
        have ha : (0:ℝ) < Real.exp (2 * Real.pi * (y - s)) := Real.exp_pos _
        calc (1:ℝ) / (1 + Real.exp (2 * Real.pi * (y - s)))
            ≤ 1 / Real.exp (2 * Real.pi * (y - s)) :=
              one_div_le_one_div_of_le ha (by linarith)
          _ = Real.exp (-(2 * Real.pi * (y - s))) := by rw [one_div, Real.exp_neg]
      calc Real.exp (-(Real.pi * s)) / (1 + Real.exp (2 * Real.pi * (y - s)))
          = Real.exp (-(Real.pi * s)) * (1 / (1 + Real.exp (2 * Real.pi * (y - s)))) := by
            rw [mul_one_div]
        _ ≤ Real.exp (-(Real.pi * s)) * Real.exp (-(2 * Real.pi * (y - s))) :=
            mul_le_mul_of_nonneg_left h2 (Real.exp_nonneg _)
        _ = Real.exp (-(Real.pi * s) - 2 * Real.pi * (y - s)) := (Real.exp_add _ _).symm
        _ ≤ Real.exp (-(Real.pi * y)) :=
            Real.exp_le_exp.mpr (by
              have hps : Real.pi * s ≤ Real.pi * y := mul_le_mul_of_nonneg_left hle Real.pi_pos.le
              linarith)
    have hsp1 : (1:ℝ) / s ^ 2 ≤ 1 := hsp2
    calc (1 + s) ^ A * (1 / s ^ 2) * Real.exp (-(Real.pi * s))
          / (1 + Real.exp (2 * Real.pi * (y - s)))
        = (1 + s) ^ A * (1 / s ^ 2)
            * (Real.exp (-(Real.pi * s)) / (1 + Real.exp (2 * Real.pi * (y - s)))) := by
          ring
      _ ≤ (1 + y) ^ A * 1 * Real.exp (-(Real.pi * y)) := by
          apply mul_le_mul
          · exact mul_le_mul (Real.rpow_le_rpow (by linarith) (by linarith) hA) hsp1
              (by positivity) (by positivity)
          · exact hE2
          · positivity
          · positivity
      _ = (1 + y) ^ A * Real.exp (-(Real.pi * y)) := by ring
      _ ≤ max 1 K2 * (1 + y) ^ (2 * A) * Real.exp (-(Real.pi * y)) := by
          have hyA : (0:ℝ) ≤ (1 + y) ^ (2 * A) := by positivity
          calc (1 + y) ^ A * Real.exp (-(Real.pi * y))
              ≤ (1 + y) ^ (2 * A) * Real.exp (-(Real.pi * y)) :=
                mul_le_mul_of_nonneg_right
                  (Real.rpow_le_rpow_of_exponent_le h1y (by linarith)) (Real.exp_nonneg _)
            _ ≤ max 1 K2 * (1 + y) ^ (2 * A) * Real.exp (-(Real.pi * y)) := by
                apply mul_le_mul_of_nonneg_right _ (Real.exp_nonneg _)
                calc (1 + y) ^ (2 * A) = 1 * (1 + y) ^ (2 * A) := by ring
                  _ ≤ max 1 K2 * (1 + y) ^ (2 * A) := mul_le_mul_of_nonneg_right hmax1 hyA
  · -- `y < s`
    have hu0 : (0:ℝ) ≤ s - y := by linarith
    have hE : (1 + s) ^ A * Real.exp (-(Real.pi * s))
        ≤ max 1 K2 * (1 + y) ^ (2 * A) * Real.exp (-(Real.pi * y)) := by
      have hle1 : 1 + s ≤ (1 + y) * (1 + (s - y)) := by nlinarith [hu0, hy]
      have hA1 : (1 + s) ^ A ≤ (1 + y) ^ A * (1 + (s - y)) ^ A := by
        calc (1 + s) ^ A ≤ ((1 + y) * (1 + (s - y))) ^ A :=
              Real.rpow_le_rpow (by positivity) hle1 hA
          _ = (1 + y) ^ A * (1 + (s - y)) ^ A :=
              Real.mul_rpow (by positivity) (by positivity)
      have hexp : Real.exp (-(Real.pi * s))
          = Real.exp (-(Real.pi * y)) * Real.exp (-(Real.pi * (s - y))) := by
        rw [← Real.exp_add]; congr 1; ring
      have hb2' := hb2 (s - y) hu0
      have hAy : (1 + y) ^ A ≤ (1 + y) ^ (2 * A) :=
        Real.rpow_le_rpow_of_exponent_le h1y (by linarith)
      have hstep1 : (1 + s) ^ A * Real.exp (-(Real.pi * s))
          ≤ (1 + y) ^ A * ((1 + (s - y)) ^ A * Real.exp (-(Real.pi * (s - y))))
              * Real.exp (-(Real.pi * y)) := by
        calc (1 + s) ^ A * Real.exp (-(Real.pi * s))
            ≤ ((1 + y) ^ A * (1 + (s - y)) ^ A)
                * (Real.exp (-(Real.pi * y)) * Real.exp (-(Real.pi * (s - y)))) := by
              rw [hexp]
              exact mul_le_mul_of_nonneg_right hA1 (by positivity)
          _ = (1 + y) ^ A * ((1 + (s - y)) ^ A * Real.exp (-(Real.pi * (s - y))))
                * Real.exp (-(Real.pi * y)) := by ring
      have hstep2 : (1 + y) ^ A * ((1 + (s - y)) ^ A * Real.exp (-(Real.pi * (s - y))))
            * Real.exp (-(Real.pi * y))
          ≤ (1 + y) ^ (2 * A) * K2 * Real.exp (-(Real.pi * y)) := by
        have h0 : (0:ℝ) ≤ (1 + y) ^ (2 * A) * Real.exp (-(Real.pi * y)) := by positivity
        have h1 : (1 + y) ^ A * ((1 + (s - y)) ^ A * Real.exp (-(Real.pi * (s - y))))
            ≤ (1 + y) ^ (2 * A) * K2 := by
          calc (1 + y) ^ A * ((1 + (s - y)) ^ A * Real.exp (-(Real.pi * (s - y))))
              = (1 + y) ^ A * ((1 + (s - y)) ^ A * Real.exp (-(Real.pi * (s - y)))) := rfl
            _ ≤ (1 + y) ^ A * K2 := mul_le_mul_of_nonneg_left hb2' (by positivity)
            _ ≤ (1 + y) ^ (2 * A) * K2 := mul_le_mul_of_nonneg_right hAy hK2
        calc (1 + y) ^ A * ((1 + (s - y)) ^ A * Real.exp (-(Real.pi * (s - y))))
              * Real.exp (-(Real.pi * y))
            = ((1 + y) ^ A * ((1 + (s - y)) ^ A * Real.exp (-(Real.pi * (s - y)))))
                * Real.exp (-(Real.pi * y)) := by ring
          _ ≤ ((1 + y) ^ (2 * A) * K2) * Real.exp (-(Real.pi * y)) :=
              mul_le_mul_of_nonneg_right h1 (Real.exp_nonneg _)
          _ = (1 + y) ^ (2 * A) * K2 * Real.exp (-(Real.pi * y)) := by ring
      have hstep3 : (1 + y) ^ (2 * A) * K2 * Real.exp (-(Real.pi * y))
          ≤ (1 + y) ^ (2 * A) * max 1 K2 * Real.exp (-(Real.pi * y)) := by
        apply mul_le_mul_of_nonneg_right _ (Real.exp_nonneg _)
        exact mul_le_mul_of_nonneg_left hK2max (by positivity)
      calc (1 + s) ^ A * Real.exp (-(Real.pi * s))
          ≤ (1 + y) ^ A * ((1 + (s - y)) ^ A * Real.exp (-(Real.pi * (s - y))))
              * Real.exp (-(Real.pi * y)) := hstep1
        _ ≤ (1 + y) ^ (2 * A) * K2 * Real.exp (-(Real.pi * y)) := hstep2
        _ ≤ (1 + y) ^ (2 * A) * max 1 K2 * Real.exp (-(Real.pi * y)) := hstep3
        _ = max 1 K2 * (1 + y) ^ (2 * A) * Real.exp (-(Real.pi * y)) := by ring
    exact le_trans hbase hE

/-! ### exponential bookkeeping -/

private lemma exp_ratio (y s : ℝ) :
    Real.exp (-(Real.pi * s) - 2 * Real.pi * y) /
        (Real.exp (-(2 * Real.pi * y)) + Real.exp (-(2 * Real.pi * s)))
      = Real.exp (-(Real.pi * s)) / (1 + Real.exp (2 * Real.pi * (y - s))) := by
  have hden : Real.exp (-(2 * Real.pi * y)) + Real.exp (-(2 * Real.pi * s))
      = Real.exp (-(2 * Real.pi * y)) * (1 + Real.exp (2 * Real.pi * (y - s))) := by
    rw [mul_add, mul_one, ← Real.exp_add]
    congr 1
    ring_nf
  have hnum : Real.exp (-(Real.pi * s) - 2 * Real.pi * y)
      = Real.exp (-(2 * Real.pi * y)) * Real.exp (-(Real.pi * s)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [hden, hnum, mul_div_mul_left _ _ (Real.exp_ne_zero _)]


/-- `imagAxis` depends only on its value argument. -/
private lemma imagAxis_congr {a b : ℝ} (h : a = b) (ha : 0 < a) (hb : 0 < b) :
    Work.Kernels.imagAxis a ha = Work.Kernels.imagAxis b hb := by
  apply UpperHalfPlane.ext
  simp only [Work.Kernels.imagAxis, UpperHalfPlane.coe_mk]
  rw [h]

/-- The scalar estimate in the shape needed below. -/
private lemma axis_exp_scalar_div (A : ℝ) (hA : 0 ≤ A) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ y t : ℝ, 1 ≤ y → 0 < t → t ≤ 1 →
      (1 + t⁻¹) ^ A * (t ^ 2 * Real.exp (-(Real.pi * t⁻¹) - 2 * Real.pi * y)
          / (Real.exp (-(2 * Real.pi * y)) + Real.exp (-(2 * Real.pi * t⁻¹))))
        ≤ K * (1 + y) ^ (2 * A) * Real.exp (-(Real.pi * y)) := by
  obtain ⟨K, hK, h⟩ := axis_exp_scalar_aux A hA
  refine ⟨K, hK, fun y t hy ht ht1 => ?_⟩
  have ht0 : t ≠ 0 := ne_of_gt ht
  have hs1 : (1 : ℝ) ≤ t⁻¹ := (one_le_inv₀ ht).mpr ht1
  have hkey := h y t⁻¹ hy hs1
  have hL : (1 + t⁻¹) ^ A * (t ^ 2 * Real.exp (-(Real.pi * t⁻¹) - 2 * Real.pi * y)
        / (Real.exp (-(2 * Real.pi * y)) + Real.exp (-(2 * Real.pi * t⁻¹))))
      = (1 + t⁻¹) ^ A * (1 / (t⁻¹) ^ 2) * Real.exp (-(Real.pi * t⁻¹))
          / (1 + Real.exp (2 * Real.pi * (y - t⁻¹))) := by
    rw [mul_div_assoc, exp_ratio y t⁻¹]
    have h2 : t ^ 2 = 1 / (t⁻¹) ^ 2 := by
      rw [one_div, inv_pow, inv_inv]
    rw [h2]
    ring
  rw [hL]
  exact hkey

/-! ### the `K_-` slash bound in the low regime -/

private lemma kmins_slash_bound_low (ℓ : Work.Kernels.LogLambdaData) :
    ∃ C A : ℝ, 0 ≤ C ∧ 0 ≤ A ∧ ∀ (τ z : ℍ), τ ∈ Work.Asymptotics.DomainD →
      (1 : ℝ) / 2 ≤ τ.im → (1 : ℝ) / 3 ≤ z.im →
      Work.Kernels.jInvariantFun τ ≠ Work.Kernels.jInvariantFun z →
      ‖(z : ℂ) ^ 2 * Work.Kernels.KMinus ℓ 8 τ (ModularGroup.S • z)‖
        ≤ C * (1 + ‖(τ : ℂ)‖) ^ A * (1 + ‖(z : ℂ)‖) ^ A * Real.exp (-(Real.pi * z.im))
            / ‖Work.Kernels.DeltaFun z * (Work.Kernels.jInvariantFun τ - Work.Kernels.jInvariantFun z)‖ := by
  obtain ⟨Cn, An, hCn, hAn, hN⟩ := ncusp8_decay_bound ℓ
  obtain ⟨cΔ, hcΔ, hΔlow⟩ := Work.Asymptotics.delta_lower_third
  refine ⟨Cn / cΔ + 1, An, by positivity, hAn, ?_⟩
  intro τ z hD hτ2 hz3 hne
  have hτ3 : (1 : ℝ) / 3 ≤ τ.im := by linarith
  have hΔz : Work.Kernels.DeltaFun z
      * (Work.Kernels.jInvariantFun τ - Work.Kernels.jInvariantFun z) ≠ 0 :=
    mul_ne_zero (Work.Kernels.ClassicalFacts.DeltaFun_ne_zero z) (sub_ne_zero.mpr hne)
  have hkey : Work.Asymptotics.Ncusp ℓ 8 τ z
      = (Work.Kernels.DeltaFun z
          * (Work.Kernels.jInvariantFun τ - Work.Kernels.jInvariantFun z))
        * ((z : ℂ) ^ 2 * Work.Kernels.KMinus ℓ 8 τ (ModularGroup.S • z)) := by
    have h := Work.Asymptotics.Ncusp_ident ℓ 8 (Or.inl rfl) τ z hne
    rw [show -((2 : ℤ) - ((8 : ℕ) : ℤ) / 2) = ((2 : ℕ) : ℤ) by norm_num, zpow_natCast] at h
    exact h
  have hmul : ‖Work.Asymptotics.Ncusp ℓ 8 τ z‖
      = ‖Work.Kernels.DeltaFun z
          * (Work.Kernels.jInvariantFun τ - Work.Kernels.jInvariantFun z)‖
        * ‖(z : ℂ) ^ 2 * Work.Kernels.KMinus ℓ 8 τ (ModularGroup.S • z)‖ := by
    rw [hkey, norm_mul]
  have hΔτlow : cΔ * Real.exp (-(2 * Real.pi * τ.im)) ≤ ‖Work.Kernels.DeltaFun τ‖ := by
    have h := hΔlow τ hτ3
    rwa [Work.Asymptotics.norm_qParamFun] at h
  have hexp1 : Real.exp (-(Real.pi * (2 * τ.im + z.im)))
      = Real.exp (-(2 * Real.pi * τ.im)) * Real.exp (-(Real.pi * z.im)) := by
    rw [← Real.exp_add]; congr 1; ring
  have hnum : ‖Work.Asymptotics.Ncusp ℓ 8 τ z‖
      ≤ (Cn / cΔ + 1) * (1 + ‖(τ : ℂ)‖) ^ An * (1 + ‖(z : ℂ)‖) ^ An
          * Real.exp (-(Real.pi * z.im)) := by
    have h1 := hN τ z hτ3 hz3
    rw [norm_mul] at h1
    have hstep : cΔ * Real.exp (-(2 * Real.pi * τ.im)) * ‖Work.Asymptotics.Ncusp ℓ 8 τ z‖
        ≤ (cΔ * Real.exp (-(2 * Real.pi * τ.im)))
            * ((Cn / cΔ) * (1 + ‖(τ : ℂ)‖) ^ An * (1 + ‖(z : ℂ)‖) ^ An
                * Real.exp (-(Real.pi * z.im))) := by
      calc cΔ * Real.exp (-(2 * Real.pi * τ.im)) * ‖Work.Asymptotics.Ncusp ℓ 8 τ z‖
          ≤ ‖Work.Kernels.DeltaFun τ‖ * ‖Work.Asymptotics.Ncusp ℓ 8 τ z‖ :=
            mul_le_mul_of_nonneg_right hΔτlow (norm_nonneg _)
        _ ≤ Cn * (1 + ‖(τ : ℂ)‖) ^ An * (1 + ‖(z : ℂ)‖) ^ An
              * Real.exp (-(Real.pi * (2 * τ.im + z.im))) := h1
        _ = Cn * (1 + ‖(τ : ℂ)‖) ^ An * (1 + ‖(z : ℂ)‖) ^ An
              * (Real.exp (-(2 * Real.pi * τ.im)) * Real.exp (-(Real.pi * z.im))) := by
            rw [hexp1]
        _ = (cΔ * Real.exp (-(2 * Real.pi * τ.im)))
              * ((Cn / cΔ) * (1 + ‖(τ : ℂ)‖) ^ An * (1 + ‖(z : ℂ)‖) ^ An
                  * Real.exp (-(Real.pi * z.im))) := by
            field_simp
    have hbase : ‖Work.Asymptotics.Ncusp ℓ 8 τ z‖
        ≤ (Cn / cΔ) * (1 + ‖(τ : ℂ)‖) ^ An * (1 + ‖(z : ℂ)‖) ^ An
            * Real.exp (-(Real.pi * z.im)) :=
      le_of_mul_le_mul_left hstep (by positivity)
    refine le_trans hbase ?_
    have h1' : Cn / cΔ ≤ Cn / cΔ + 1 := by linarith
    have hnn : (0 : ℝ) ≤ (1 + ‖(τ : ℂ)‖) ^ An * (1 + ‖(z : ℂ)‖) ^ An
        * Real.exp (-(Real.pi * z.im)) := by positivity
    calc (Cn / cΔ) * (1 + ‖(τ : ℂ)‖) ^ An * (1 + ‖(z : ℂ)‖) ^ An
            * Real.exp (-(Real.pi * z.im))
        = (Cn / cΔ) * ((1 + ‖(τ : ℂ)‖) ^ An * (1 + ‖(z : ℂ)‖) ^ An
            * Real.exp (-(Real.pi * z.im))) := by ring
      _ ≤ (Cn / cΔ + 1) * ((1 + ‖(τ : ℂ)‖) ^ An * (1 + ‖(z : ℂ)‖) ^ An
            * Real.exp (-(Real.pi * z.im))) := mul_le_mul_of_nonneg_right h1' hnn
      _ = (Cn / cΔ + 1) * (1 + ‖(τ : ℂ)‖) ^ An * (1 + ‖(z : ℂ)‖) ^ An
            * Real.exp (-(Real.pi * z.im)) := by ring
  have hD'0 : (0 : ℝ) ≤ ‖Work.Kernels.DeltaFun z
      * (Work.Kernels.jInvariantFun τ - Work.Kernels.jInvariantFun z)‖ := norm_nonneg _
  have hD'pos : (0 : ℝ) < ‖Work.Kernels.DeltaFun z
      * (Work.Kernels.jInvariantFun τ - Work.Kernels.jInvariantFun z)‖ :=
    norm_pos_iff.mpr hΔz
  have hquot : ‖Work.Asymptotics.Ncusp ℓ 8 τ z‖
        / ‖Work.Kernels.DeltaFun z
            * (Work.Kernels.jInvariantFun τ - Work.Kernels.jInvariantFun z)‖
      = ‖(z : ℂ) ^ 2 * Work.Kernels.KMinus ℓ 8 τ (ModularGroup.S • z)‖ := by
    rw [hmul, mul_div_cancel_left₀ _ (ne_of_gt hD'pos)]
  rw [← hquot]
  exact div_le_div_of_nonneg_right hnum hD'0

/-! ### the `K_+` slash bound in the low regime -/

private lemma kplus_slash_bound_low :
    ∃ C A : ℝ, 0 ≤ C ∧ 0 ≤ A ∧ ∀ (τ z : ℍ), τ ∈ Work.Asymptotics.DomainD →
      (1 : ℝ) / 2 ≤ τ.im → (1 : ℝ) / 3 ≤ z.im →
      Work.Kernels.jInvariantFun τ ≠ Work.Kernels.jInvariantFun z →
      ‖(z : ℂ) ^ 2 * Work.Kernels.KPlus 8 τ (ModularGroup.S • z)‖
        ≤ C * (1 + ‖(τ : ℂ)‖) ^ A * (1 + ‖(z : ℂ)‖) ^ A * Real.exp (-(Real.pi * z.im))
            / ‖Work.Kernels.DeltaFun z * (Work.Kernels.jInvariantFun τ - Work.Kernels.jInvariantFun z)‖ := by
  obtain ⟨C, A, hC, hA, h⟩ := Work.Asymptotics.KPlus_slash_bound_half 8 (Or.inl rfl)
  refine ⟨C, A, hC.le, hA, ?_⟩
  intro τ z hD hτ2 hz3 hne
  have h1 := h τ z hD hτ2 hz3 hne
  rw [show (((8 : ℕ) : ℤ) / 2 - 2) = (2 : ℤ) by norm_num, zpow_ofNat] at h1
  have hge : (1 : ℝ) ≤ (1 + ‖(z : ℂ)‖) ^ A :=
    Real.one_le_rpow (by have := norm_nonneg (z : ℂ); linarith) hA
  have hD'0 : (0 : ℝ) ≤ ‖Work.Kernels.DeltaFun z
      * (Work.Kernels.jInvariantFun τ - Work.Kernels.jInvariantFun z)‖ := norm_nonneg _
  refine le_trans h1 ?_
  apply div_le_div_of_nonneg_right _ hD'0
  have hb : (0 : ℝ) ≤ C * (1 + ‖(τ : ℂ)‖) ^ A * Real.exp (-(Real.pi * z.im)) := by positivity
  calc C * (1 + ‖(τ : ℂ)‖) ^ A * Real.exp (-(Real.pi * z.im))
      = C * (1 + ‖(τ : ℂ)‖) ^ A * Real.exp (-(Real.pi * z.im)) * 1 := by ring
    _ ≤ C * (1 + ‖(τ : ℂ)‖) ^ A * Real.exp (-(Real.pi * z.im)) * (1 + ‖(z : ℂ)‖) ^ A :=
        mul_le_mul_of_nonneg_left hge hb
    _ = C * (1 + ‖(τ : ℂ)‖) ^ A * (1 + ‖(z : ℂ)‖) ^ A * Real.exp (-(Real.pi * z.im)) := by ring

/-! ### the pointwise kernel bound from a slash bound -/

private lemma axis_bound_of_slash (K : ℍ → ℍ → ℂ) (C A : ℝ) (hC : 0 ≤ C) (hA : 0 ≤ A)
    (hslash : ∀ (τ z : ℍ), τ ∈ Work.Asymptotics.DomainD → (1 : ℝ) / 2 ≤ τ.im →
      (1 : ℝ) / 3 ≤ z.im →
      Work.Kernels.jInvariantFun τ ≠ Work.Kernels.jInvariantFun z →
      ‖(z : ℂ) ^ 2 * K τ (ModularGroup.S • z)‖
        ≤ C * (1 + ‖(τ : ℂ)‖) ^ A * (1 + ‖(z : ℂ)‖) ^ A * Real.exp (-(Real.pi * z.im))
            / ‖Work.Kernels.DeltaFun z * (Work.Kernels.jInvariantFun τ - Work.Kernels.jInvariantFun z)‖) :
    ∃ C' N' Y₀' : ℝ, 0 ≤ C' ∧ 0 ≤ N' ∧ 1 ≤ Y₀' ∧
      ∀ (τ : ℍ) (t : ℝ) (ht : 0 < t), (τ.re = 1 / 2 ∨ τ.re = - 1 / 2) → Y₀' ≤ τ.im → t ≤ 1 →
        ‖K τ (Work.Kernels.imagAxis t ht)‖ ≤ C' * τ.im ^ N' * Real.exp (-(Real.pi * τ.im)) := by
  obtain ⟨CD, hCD, hΔup⟩ := Work.Asymptotics.delta_upper_third
  obtain ⟨cc, T₀, hcc, hT₀, hdiv⟩ := Work.Asymptotics.divisor_qdiff_lower
  obtain ⟨Ks, hKs, hscal⟩ := axis_exp_scalar_div A hA
  refine ⟨C * CD / cc * Ks * 3 ^ (3 * A) + 1, 3 * A, max 1 T₀, by positivity, by positivity,
    le_max_left 1 T₀, ?_⟩
  intro τ t ht hre hy ht1
  have hy1 : (1 : ℝ) ≤ τ.im := le_trans (le_max_left 1 T₀) hy
  have hyT0 : T₀ ≤ τ.im := le_trans (le_max_right 1 T₀) hy
  have hτ12 : (1 : ℝ) / 2 ≤ τ.im := by linarith
  have hτ13 : (1 : ℝ) / 3 ≤ τ.im := by linarith
  have hpos : (0 : ℝ) < t⁻¹ := inv_pos.mpr ht
  set z : ℍ := Work.Kernels.imagAxis t⁻¹ hpos with hzdef
  have hzim : z.im = t⁻¹ := by rw [hzdef]; simp [Work.Kernels.imagAxis]
  have hs1 : (1 : ℝ) ≤ t⁻¹ := (one_le_inv₀ ht).mpr ht1
  have hz3 : (1 : ℝ) / 3 ≤ z.im := by rw [hzim]; linarith
  have hSz : ModularGroup.S • z = Work.Kernels.imagAxis t ht := by
    rw [hzdef, S_smul_imagAxis t⁻¹ hpos]
    exact imagAxis_congr (by rw [one_div, inv_inv]) _ _
  have hnormz : ‖(z : ℂ)‖ = t⁻¹ := by
    rw [hzdef]
    simp only [Work.Kernels.imagAxis, UpperHalfPlane.coe_mk]
    rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real,
      Real.norm_of_nonneg (by positivity)]
  have hDmem : τ ∈ Work.Asymptotics.DomainD := by
    rw [Work.Asymptotics.mem_DomainD]
    have hb1 : (1 : ℝ) / 2 < ‖(τ : ℂ) - (1 / 2 : ℂ)‖ := by
      have h := Complex.abs_im_le_norm ((τ : ℂ) - (1 / 2 : ℂ))
      rw [Complex.sub_im, UpperHalfPlane.coe_im,
        show ((1 / 2 : ℂ)).im = 0 by norm_num, sub_zero,
        abs_of_pos τ.im_pos] at h
      linarith [h, hy1]
    have hb2 : (1 : ℝ) / 2 < ‖(τ : ℂ) + (1 / 2 : ℂ)‖ := by
      have h := Complex.abs_im_le_norm ((τ : ℂ) + (1 / 2 : ℂ))
      rw [Complex.add_im, UpperHalfPlane.coe_im,
        show ((1 / 2 : ℂ)).im = 0 by norm_num, add_zero,
        abs_of_pos τ.im_pos] at h
      linarith [h, hy1]
    rcases hre with h | h
    · exact ⟨by rw [h]; norm_num, by rw [h]; norm_num, hb1, hb2⟩
    · exact ⟨by rw [h]; norm_num, by rw [h]; norm_num, hb1, hb2⟩
  have hq : ‖Work.Kernels.qParamFun τ - Work.Kernels.qParamFun z‖
      = Real.exp (-(2 * Real.pi * τ.im)) + Real.exp (-(2 * Real.pi * t⁻¹)) := by
    rw [hzdef]; exact qParamFun_line_norm_sub τ hre t⁻¹ hpos
  have hden_low : cc * (Real.exp (-(2 * Real.pi * τ.im)) + Real.exp (-(2 * Real.pi * t⁻¹)))
      ≤ ‖Work.Kernels.DeltaFun τ * Work.Kernels.DeltaFun z
          * (Work.Kernels.jInvariantFun τ - Work.Kernels.jInvariantFun z)‖ := by
    have h := hdiv τ z hyT0 hz3
    rwa [hq] at h
  have hDpos : (0 : ℝ) < ‖Work.Kernels.DeltaFun τ * Work.Kernels.DeltaFun z
      * (Work.Kernels.jInvariantFun τ - Work.Kernels.jInvariantFun z)‖ :=
    lt_of_lt_of_le (mul_pos hcc (by positivity)) hden_low
  have hne : Work.Kernels.jInvariantFun τ ≠ Work.Kernels.jInvariantFun z := by
    intro hc
    have h0 : Work.Kernels.DeltaFun τ * Work.Kernels.DeltaFun z
        * (Work.Kernels.jInvariantFun τ - Work.Kernels.jInvariantFun z) = 0 := by
      rw [hc, sub_self, mul_zero]
    rw [h0, norm_zero] at hDpos
    exact absurd hDpos (lt_irrefl 0)
  have hsla := hslash τ z hDmem hτ12 hz3 hne
  have hD'pos : (0 : ℝ) < ‖Work.Kernels.DeltaFun z
      * (Work.Kernels.jInvariantFun τ - Work.Kernels.jInvariantFun z)‖ :=
    norm_pos_iff.mpr (mul_ne_zero (Work.Kernels.ClassicalFacts.DeltaFun_ne_zero z)
      (sub_ne_zero.mpr hne))
  have hΔτle : ‖Work.Kernels.DeltaFun τ‖ ≤ CD * Real.exp (-(2 * Real.pi * τ.im)) := by
    calc ‖Work.Kernels.DeltaFun τ‖ ≤ CD * ‖Work.Kernels.qParamFun τ‖ := hΔup τ hτ13
      _ = CD * Real.exp (-(2 * Real.pi * τ.im)) := by rw [Work.Asymptotics.norm_qParamFun]
  have hsplit : ‖Work.Kernels.DeltaFun τ * Work.Kernels.DeltaFun z
        * (Work.Kernels.jInvariantFun τ - Work.Kernels.jInvariantFun z)‖
      = ‖Work.Kernels.DeltaFun τ‖
        * ‖Work.Kernels.DeltaFun z
            * (Work.Kernels.jInvariantFun τ - Work.Kernels.jInvariantFun z)‖ := by
    rw [show Work.Kernels.DeltaFun τ * Work.Kernels.DeltaFun z
          * (Work.Kernels.jInvariantFun τ - Work.Kernels.jInvariantFun z)
        = Work.Kernels.DeltaFun τ * (Work.Kernels.DeltaFun z
            * (Work.Kernels.jInvariantFun τ - Work.Kernels.jInvariantFun z)) by ring]
    rw [norm_mul]
  have hWle : cc * (Real.exp (-(2 * Real.pi * τ.im)) + Real.exp (-(2 * Real.pi * t⁻¹)))
        / (CD * Real.exp (-(2 * Real.pi * τ.im)))
      ≤ ‖Work.Kernels.DeltaFun z
          * (Work.Kernels.jInvariantFun τ - Work.Kernels.jInvariantFun z)‖ := by
    rw [div_le_iff₀ (by positivity : (0 : ℝ) < CD * Real.exp (-(2 * Real.pi * τ.im)))]
    rw [hsplit] at hden_low
    calc cc * (Real.exp (-(2 * Real.pi * τ.im)) + Real.exp (-(2 * Real.pi * t⁻¹)))
        ≤ ‖Work.Kernels.DeltaFun τ‖
            * ‖Work.Kernels.DeltaFun z
                * (Work.Kernels.jInvariantFun τ - Work.Kernels.jInvariantFun z)‖ := hden_low
      _ ≤ (CD * Real.exp (-(2 * Real.pi * τ.im)))
            * ‖Work.Kernels.DeltaFun z
                * (Work.Kernels.jInvariantFun τ - Work.Kernels.jInvariantFun z)‖ :=
          mul_le_mul_of_nonneg_right hΔτle (norm_nonneg _)
      _ = ‖Work.Kernels.DeltaFun z
                * (Work.Kernels.jInvariantFun τ - Work.Kernels.jInvariantFun z)‖
            * (CD * Real.exp (-(2 * Real.pi * τ.im))) := by ring
  have hinv : 1 / ‖Work.Kernels.DeltaFun z
        * (Work.Kernels.jInvariantFun τ - Work.Kernels.jInvariantFun z)‖
      ≤ (CD * Real.exp (-(2 * Real.pi * τ.im)))
          / (cc * (Real.exp (-(2 * Real.pi * τ.im)) + Real.exp (-(2 * Real.pi * t⁻¹)))) := by
    calc 1 / ‖Work.Kernels.DeltaFun z
          * (Work.Kernels.jInvariantFun τ - Work.Kernels.jInvariantFun z)‖
        ≤ 1 / (cc * (Real.exp (-(2 * Real.pi * τ.im)) + Real.exp (-(2 * Real.pi * t⁻¹)))
              / (CD * Real.exp (-(2 * Real.pi * τ.im)))) :=
          one_div_le_one_div_of_le (by positivity) hWle
      _ = (CD * Real.exp (-(2 * Real.pi * τ.im)))
            / (cc * (Real.exp (-(2 * Real.pi * τ.im)) + Real.exp (-(2 * Real.pi * t⁻¹)))) :=
          one_div_div _ _
  have hA1nn : (0 : ℝ) ≤ C * (1 + ‖(τ : ℂ)‖) ^ A * (1 + ‖(z : ℂ)‖) ^ A
      * Real.exp (-(Real.pi * z.im)) := by positivity
  have hk2 : ‖(z : ℂ) ^ 2 * K τ (ModularGroup.S • z)‖
      ≤ (C * (1 + ‖(τ : ℂ)‖) ^ A * (1 + ‖(z : ℂ)‖) ^ A * Real.exp (-(Real.pi * z.im)))
          * ((CD * Real.exp (-(2 * Real.pi * τ.im)))
              / (cc * (Real.exp (-(2 * Real.pi * τ.im))
                  + Real.exp (-(2 * Real.pi * t⁻¹))))) := by
    have h1 : ‖(z : ℂ) ^ 2 * K τ (ModularGroup.S • z)‖
        ≤ (C * (1 + ‖(τ : ℂ)‖) ^ A * (1 + ‖(z : ℂ)‖) ^ A * Real.exp (-(Real.pi * z.im)))
            * (‖Work.Kernels.DeltaFun z
                * (Work.Kernels.jInvariantFun τ - Work.Kernels.jInvariantFun z)‖)⁻¹ := by
      rw [div_eq_mul_inv] at hsla
      exact hsla
    have h2 : (‖Work.Kernels.DeltaFun z
          * (Work.Kernels.jInvariantFun τ - Work.Kernels.jInvariantFun z)‖)⁻¹
        ≤ (CD * Real.exp (-(2 * Real.pi * τ.im)))
            / (cc * (Real.exp (-(2 * Real.pi * τ.im))
                + Real.exp (-(2 * Real.pi * t⁻¹)))) := by
      rw [← one_div]; exact hinv
    exact le_trans h1 (mul_le_mul_of_nonneg_left h2 hA1nn)
  have hnorm_eq : ‖K τ (Work.Kernels.imagAxis t ht)‖
      = t ^ 2 * ‖(z : ℂ) ^ 2 * K τ (ModularGroup.S • z)‖ := by
    rw [← hSz, norm_mul, norm_pow, hnormz]
    field_simp
  have hzA : (1 + ‖(z : ℂ)‖) ^ A = (1 + t⁻¹) ^ A := by rw [hnormz]
  have hze : Real.exp (-(Real.pi * z.im)) = Real.exp (-(Real.pi * t⁻¹)) := by rw [hzim]
  have halg : t ^ 2 * ((C * (1 + ‖(τ : ℂ)‖) ^ A * (1 + ‖(z : ℂ)‖) ^ A
          * Real.exp (-(Real.pi * z.im)))
        * ((CD * Real.exp (-(2 * Real.pi * τ.im)))
            / (cc * (Real.exp (-(2 * Real.pi * τ.im))
                + Real.exp (-(2 * Real.pi * t⁻¹))))))
      = (C * CD / cc) * (1 + ‖(τ : ℂ)‖) ^ A
          * ((1 + t⁻¹) ^ A * (t ^ 2 * Real.exp (-(Real.pi * t⁻¹) - 2 * Real.pi * τ.im)
              / (Real.exp (-(2 * Real.pi * τ.im)) + Real.exp (-(2 * Real.pi * t⁻¹))))) := by
    rw [hzA, hze]
    rw [show Real.exp (-(Real.pi * t⁻¹) - 2 * Real.pi * τ.im)
        = Real.exp (-(Real.pi * t⁻¹)) * Real.exp (-(2 * Real.pi * τ.im)) by
      rw [show -(Real.pi * t⁻¹) - 2 * Real.pi * τ.im
          = -(Real.pi * t⁻¹) + -(2 * Real.pi * τ.im) by ring, Real.exp_add]]
    field_simp
  have hsc := hscal τ.im t hy1 ht ht1
  have hchain : ‖K τ (Work.Kernels.imagAxis t ht)‖
      ≤ (C * CD / cc) * (1 + ‖(τ : ℂ)‖) ^ A
          * ((1 + t⁻¹) ^ A * (t ^ 2 * Real.exp (-(Real.pi * t⁻¹) - 2 * Real.pi * τ.im)
              / (Real.exp (-(2 * Real.pi * τ.im)) + Real.exp (-(2 * Real.pi * t⁻¹))))) := by
    rw [hnorm_eq]
    exact le_trans (mul_le_mul_of_nonneg_left hk2 (by positivity)) (le_of_eq halg)
  -- exponent bookkeeping
  have hτnorm : 1 + ‖(τ : ℂ)‖ ≤ 3 * τ.im := by
    have h := Complex.norm_le_abs_re_add_abs_im (τ : ℂ)
    rw [UpperHalfPlane.coe_re, UpperHalfPlane.coe_im, abs_of_pos τ.im_pos] at h
    have hre' : |τ.re| ≤ 1 / 2 := by rcases hre with hh | hh <;> rw [hh] <;> norm_num
    linarith [h, hre', hy1]
  have h1y : 1 + τ.im ≤ 3 * τ.im := by linarith [hy1]
  have hp1 : (1 + ‖(τ : ℂ)‖) ^ A ≤ (3 * τ.im) ^ A :=
    Real.rpow_le_rpow (by positivity) hτnorm hA
  have hp2 : (1 + τ.im) ^ (2 * A) ≤ (3 * τ.im) ^ (2 * A) :=
    Real.rpow_le_rpow (by positivity) h1y (by positivity)
  have hprod : (1 + ‖(τ : ℂ)‖) ^ A * (1 + τ.im) ^ (2 * A)
      ≤ 3 ^ (3 * A) * τ.im ^ (3 * A) := by
    calc (1 + ‖(τ : ℂ)‖) ^ A * (1 + τ.im) ^ (2 * A)
        ≤ (3 * τ.im) ^ A * (3 * τ.im) ^ (2 * A) := mul_le_mul hp1 hp2 (by positivity) (by positivity)
      _ = (3 * τ.im) ^ (3 * A) := by
          rw [← Real.rpow_add (by positivity)]; congr 1; ring
      _ = 3 ^ (3 * A) * τ.im ^ (3 * A) := by
          rw [Real.mul_rpow (by norm_num) (by positivity)]
  have hfinal : ‖K τ (Work.Kernels.imagAxis t ht)‖
      ≤ (C * CD / cc * Ks * 3 ^ (3 * A) + 1) * τ.im ^ (3 * A)
          * Real.exp (-(Real.pi * τ.im)) := by
    refine le_trans hchain ?_
    have hA0 : (0 : ℝ) ≤ (C * CD / cc) * (1 + ‖(τ : ℂ)‖) ^ A := by positivity
    have hstep1 : (C * CD / cc) * (1 + ‖(τ : ℂ)‖) ^ A
          * ((1 + t⁻¹) ^ A * (t ^ 2 * Real.exp (-(Real.pi * t⁻¹) - 2 * Real.pi * τ.im)
              / (Real.exp (-(2 * Real.pi * τ.im)) + Real.exp (-(2 * Real.pi * t⁻¹)))))
        ≤ (C * CD / cc) * (1 + ‖(τ : ℂ)‖) ^ A * (Ks * (1 + τ.im) ^ (2 * A)
            * Real.exp (-(Real.pi * τ.im))) :=
      mul_le_mul_of_nonneg_left hsc hA0
    refine le_trans hstep1 ?_
    have hKs0 : (0 : ℝ) ≤ Ks := hKs
    have hfac : (0 : ℝ) ≤ (C * CD / cc) * Ks := by positivity
    calc (C * CD / cc) * (1 + ‖(τ : ℂ)‖) ^ A
          * (Ks * (1 + τ.im) ^ (2 * A) * Real.exp (-(Real.pi * τ.im)))
        = (C * CD / cc) * Ks * ((1 + ‖(τ : ℂ)‖) ^ A * (1 + τ.im) ^ (2 * A))
            * Real.exp (-(Real.pi * τ.im)) := by ring
      _ ≤ (C * CD / cc) * Ks * (3 ^ (3 * A) * τ.im ^ (3 * A))
            * Real.exp (-(Real.pi * τ.im)) := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          exact mul_le_mul_of_nonneg_left hprod hfac
      _ = (C * CD / cc * Ks * 3 ^ (3 * A)) * τ.im ^ (3 * A)
            * Real.exp (-(Real.pi * τ.im)) := by ring
      _ ≤ (C * CD / cc * Ks * 3 ^ (3 * A) + 1) * τ.im ^ (3 * A)
            * Real.exp (-(Real.pi * τ.im)) := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          linarith
  exact hfinal

/-! ### the target -/

theorem P1_line_bound_eight (ℓ : Work.Kernels.LogLambdaData) :
    ∃ C N Y₀ : ℝ, 0 ≤ C ∧ 0 ≤ N ∧ 1 ≤ Y₀ ∧
      ∀ (τ : UpperHalfPlane) (r : ℝ), (τ.re = 1 / 2 ∨ τ.re = - 1 / 2) → Y₀ ≤ τ.im →
        (‖Work.CKFinal.P1 (Work.Kernels.Kfun ℓ 8) r τ‖
            ≤ C * τ.im ^ N * Real.exp (-(Real.pi * τ.im))
          ∧ ‖Work.CKFinal.P1 (Work.Kernels.Khat ℓ 8) r τ‖
            ≤ C * τ.im ^ N * Real.exp (-(Real.pi * τ.im))) := by
  obtain ⟨Cp, Ap, hCp, hAp, hP⟩ := kplus_slash_bound_low
  obtain ⟨Cm, Am, hCm, hAm, hM⟩ := kmins_slash_bound_low ℓ
  obtain ⟨C', N', Y', hC', hN', hY', hbP⟩ :=
    axis_bound_of_slash (Work.Kernels.KPlus 8) Cp Ap hCp hAp hP
  obtain ⟨C'', N'', Y'', hC'', hN'', hY'', hbM⟩ :=
    axis_bound_of_slash (Work.Kernels.KMinus ℓ 8) Cm Am hCm hAm hM
  refine ⟨4 * max C' C'', max N' N'', max (max Y' Y'') 1, by positivity, by positivity,
    le_max_right _ _, ?_⟩
  intro τ r hre hy
  have hy1 : (1 : ℝ) ≤ τ.im := le_trans (le_max_right (max Y' Y'') 1) hy
  have hy' : Y' ≤ τ.im := le_trans (le_max_left Y' Y'') (le_trans (le_max_left (max Y' Y'') 1) hy)
  have hy'' : Y'' ≤ τ.im := le_trans (le_max_right Y' Y'') (le_trans (le_max_left (max Y' Y'') 1) hy)
  set M : ℝ := max C' C'' * τ.im ^ (max N' N'') * Real.exp (-(Real.pi * τ.im)) with hMdef
  have hM0 : (0 : ℝ) ≤ M := by rw [hMdef]; positivity
  have hker : ∀ (K : ℍ → ℍ → ℂ), (∀ t (ht : 0 < t), t ≤ 1 →
        ‖K τ (Work.Kernels.imagAxis t ht)‖ ≤ M) →
      ∀ t (ht : 0 < t), t ≤ 1 →
        ‖Work.CKFinal.Kax K τ 0 t‖ ≤ M := by
    intro K hK t ht ht1
    rw [Work.CKFinal.Kax, dif_pos ht, zero_vadd]
    exact hK t ht ht1
  have hmono : ∀ a b : ℝ, a ≤ max C' C'' → b ≤ max N' N'' →
      a * τ.im ^ b * Real.exp (-(Real.pi * τ.im)) ≤ M := by
    intro a b ha hb
    rw [hMdef]
    have hn : τ.im ^ b ≤ τ.im ^ (max N' N'') :=
      Real.rpow_le_rpow_of_exponent_le hy1 hb
    have hmul : τ.im ^ b * Real.exp (-(Real.pi * τ.im))
        ≤ τ.im ^ (max N' N'') * Real.exp (-(Real.pi * τ.im)) :=
      mul_le_mul_of_nonneg_right hn (by positivity)
    calc a * τ.im ^ b * Real.exp (-(Real.pi * τ.im))
        = a * (τ.im ^ b * Real.exp (-(Real.pi * τ.im))) := by ring
      _ ≤ max C' C'' * (τ.im ^ (max N' N'') * Real.exp (-(Real.pi * τ.im))) :=
          mul_le_mul ha hmul (by positivity) (by positivity)
      _ = max C' C'' * τ.im ^ (max N' N'') * Real.exp (-(Real.pi * τ.im)) := by ring
  have hPk : ∀ t (ht : 0 < t), t ≤ 1 →
      ‖Work.Kernels.KPlus 8 τ (Work.Kernels.imagAxis t ht)‖ ≤ M :=
    fun t ht ht1 => le_trans (hbP τ t ht hre hy' ht1)
      (hmono C' N' (le_max_left _ _) (le_max_left _ _))
  have hMk : ∀ t (ht : 0 < t), t ≤ 1 →
      ‖Work.Kernels.KMinus ℓ 8 τ (Work.Kernels.imagAxis t ht)‖ ≤ M :=
    fun t ht ht1 => le_trans (hbM τ t ht hre hy'' ht1)
      (hmono C'' N'' (le_max_right _ _) (le_max_right _ _))
  have hKfun : ∀ t (ht : 0 < t), t ≤ 1 →
      ‖Work.Kernels.Kfun ℓ 8 τ (Work.Kernels.imagAxis t ht)‖ ≤ M := by
    intro t ht ht1
    have h1 := hPk t ht ht1
    have h2 := hMk t ht ht1
    have h3 := norm_add_le (Work.Kernels.KPlus 8 τ (Work.Kernels.imagAxis t ht))
      (Work.Kernels.KMinus ℓ 8 τ (Work.Kernels.imagAxis t ht))
    rw [Work.Kernels.Kfun, norm_div, show ‖(2 : ℂ)‖ = 2 by norm_num]
    linarith
  have hKhat : ∀ t (ht : 0 < t), t ≤ 1 →
      ‖Work.Kernels.Khat ℓ 8 τ (Work.Kernels.imagAxis t ht)‖ ≤ M := by
    intro t ht ht1
    have h1 := hPk t ht ht1
    have h2 := hMk t ht ht1
    have h3 := norm_sub_le (Work.Kernels.KPlus 8 τ (Work.Kernels.imagAxis t ht))
      (Work.Kernels.KMinus ℓ 8 τ (Work.Kernels.imagAxis t ht))
    rw [Work.Kernels.Khat, norm_div, show ‖(2 : ℂ)‖ = 2 by norm_num]
    linarith
  have hgw : ∀ t (ht : 0 ≤ t), ‖Work.Asymptotics.gaussWeight r t‖ ≤ 1 :=
    fun t ht => (sinSqC_gaussWeight_bound r t ht).2
  have hsin : ‖Work.Asymptotics.sinSqC r‖ ≤ 4 := (sinSqC_gaussWeight_bound r 0 le_rfl).1
  have hint : ∀ (K : ℍ → ℍ → ℂ), (∀ t (ht : 0 < t), t ≤ 1 →
        ‖K τ (Work.Kernels.imagAxis t ht)‖ ≤ M) →
      ‖∫ t in (0 : ℝ)..1,
          Work.CKFinal.Kax K τ 0 t * Work.Asymptotics.gaussWeight r t‖ ≤ M * |(1 : ℝ) - 0| := by
    intro K hK
    refine intervalIntegral.norm_integral_le_of_norm_le_const (fun x hx => ?_)
    rw [Set.uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hx
    have hx0 : 0 < x := hx.1
    have hx1 : x ≤ 1 := hx.2
    calc ‖Work.CKFinal.Kax K τ 0 x * Work.Asymptotics.gaussWeight r x‖
        = ‖Work.CKFinal.Kax K τ 0 x‖ * ‖Work.Asymptotics.gaussWeight r x‖ := norm_mul _ _
      _ ≤ M * 1 := mul_le_mul (hker K hK x hx0 hx1) (hgw x hx0.le) (norm_nonneg _) hM0
      _ = M := by ring
  have hp1 : ‖Work.CKFinal.P1 (Work.Kernels.Kfun ℓ 8) r τ‖ ≤ 4 * max C' C'' * τ.im ^ max N' N''
      * Real.exp (-(Real.pi * τ.im)) := by
    have h := hint (Work.Kernels.Kfun ℓ 8) hKfun
    rw [Work.CKFinal.P1, Work.CKFinal.hsplit]
    calc ‖Work.Asymptotics.sinSqC r * ∫ t in (0 : ℝ)..1,
            Work.CKFinal.Kax (Work.Kernels.Kfun ℓ 8) τ 0 t * Work.Asymptotics.gaussWeight r t‖
        = ‖Work.Asymptotics.sinSqC r‖ * ‖∫ t in (0 : ℝ)..1,
            Work.CKFinal.Kax (Work.Kernels.Kfun ℓ 8) τ 0 t * Work.Asymptotics.gaussWeight r t‖ :=
          norm_mul _ _
      _ ≤ 4 * (M * |(1 : ℝ) - 0|) :=
          mul_le_mul hsin h (norm_nonneg _) (by norm_num)
      _ = 4 * max C' C'' * τ.im ^ max N' N'' * Real.exp (-(Real.pi * τ.im)) := by
          rw [hMdef]; norm_num; ring
  have hp2 : ‖Work.CKFinal.P1 (Work.Kernels.Khat ℓ 8) r τ‖ ≤ 4 * max C' C'' * τ.im ^ max N' N''
      * Real.exp (-(Real.pi * τ.im)) := by
    have h := hint (Work.Kernels.Khat ℓ 8) hKhat
    rw [Work.CKFinal.P1, Work.CKFinal.hsplit]
    calc ‖Work.Asymptotics.sinSqC r * ∫ t in (0 : ℝ)..1,
            Work.CKFinal.Kax (Work.Kernels.Khat ℓ 8) τ 0 t * Work.Asymptotics.gaussWeight r t‖
        = ‖Work.Asymptotics.sinSqC r‖ * ‖∫ t in (0 : ℝ)..1,
            Work.CKFinal.Kax (Work.Kernels.Khat ℓ 8) τ 0 t * Work.Asymptotics.gaussWeight r t‖ :=
          norm_mul _ _
      _ ≤ 4 * (M * |(1 : ℝ) - 0|) :=
          mul_le_mul hsin h (norm_nonneg _) (by norm_num)
      _ = 4 * max C' C'' * τ.im ^ max N' N'' * Real.exp (-(Real.pi * τ.im)) := by
          rw [hMdef]; norm_num; ring
  exact ⟨hp1, hp2⟩

end

end Work.CKFinal.LineDecay
