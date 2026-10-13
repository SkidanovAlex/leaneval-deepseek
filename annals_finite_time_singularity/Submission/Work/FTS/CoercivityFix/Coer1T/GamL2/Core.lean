import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.Coercivity.Defs
import Submission.Work.FTS.CoercivityFix.Coer1T.GamL2.Prelim

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The two main estimates for `GammaL2Bnd`

* `int_F`: `∫_{Iθ}(Γ − K)² ≤ 25π/32 − 2 + 6p(π/2)` (`p = α/3`), the `α = 0` value
  `∫(1 − K)² = π/2 − 2 + 9π/32` corrected by the pointwise bound
  `(u^p − 3u)² ≤ (1 − 3u)² + 6p(1 − u)`;
* `c_le_one`, `one_sub_c_le`: the two one-sided bounds for the normalisation
  constant `c = ∫_{Iθ} Γ K`, namely `c ≤ 1` and `1 − c ≤ 3p(π/2)`.
-/

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.CoercivityFix.Coer1T.GamL2

/-- The elementary inequality `(a+b)² ≤ a² + 2|a||b| + b²`. -/
lemma sq_abs_add_le (a b : ℝ) : (a + b) ^ 2 ≤ a ^ 2 + 2 * |a| * |b| + b ^ 2 := by
  have h : a * b ≤ |a| * |b| := by rw [← abs_mul]; exact le_abs_self _
  nlinarith [h]

/-- `∫_{Iθ} c = c·(π/2)` for a constant `c`. -/
lemma int_const (c : ℝ) : (∫ θ in Work.Spaces.Iθ, c) = c * (Real.pi / 2) := by
  rw [MeasureTheory.setIntegral_const, smul_eq_mul, MeasureTheory.measureReal_def,
      Work.Spaces.Iθ, Real.volume_Icc, ENNReal.toReal_ofReal (by linarith [Real.pi_pos])]
  ring

/-- `K` is continuous. -/
lemma cont_K : Continuous Work.Spaces.K := by
  change Continuous fun θ : ℝ => 3 * Real.sin θ * Real.cos θ ^ 2
  fun_prop

/-- `Γ` is continuous for `α > 0`. -/
lemma continuous_Gam (α : ℝ) (hα : 0 < α) : Continuous (fun θ : ℝ => Work.Spaces.Gam α θ) := by
  simpa only [Work.Spaces.Gam] using
    (Continuous.rpow_const (f := fun θ : ℝ => Real.sin θ * Real.cos θ ^ 2) (by fun_prop)
      (fun _ => Or.inr (le_of_lt (by positivity : (0 : ℝ) < α / 3))))

/-- `K ≥ 0` on `Iθ`. -/
lemma K_nonneg {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) : 0 ≤ Work.Spaces.K θ := by
  have h := (Work.Spaces.sin_mul_cos_sq_mem_Icc θ hθ).1
  have hK : Work.Spaces.K θ = 3 * (Real.sin θ * Real.cos θ ^ 2) := by
    rw [Work.Spaces.K]; ring
  rw [hK]; linarith

/-- `K ≤ 3` on `Iθ`. -/
lemma K_le_three {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) : Work.Spaces.K θ ≤ 3 := by
  have h := (Work.Spaces.sin_mul_cos_sq_mem_Icc θ hθ).2
  have hK : Work.Spaces.K θ = 3 * (Real.sin θ * Real.cos θ ^ 2) := by
    rw [Work.Spaces.K]; ring
  rw [hK]; linarith

/-- The `F`-part of the estimate: `∫(Γ − K)² ≤ 25π/32 − 2 + 6p(π/2)`, `p = α/3`. -/
lemma int_F (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) :
    (∫ θ in Work.Spaces.Iθ, (Work.Spaces.Gam α θ - Work.Spaces.K θ) ^ 2)
      ≤ 25 * Real.pi / 32 - 2 + 6 * (α / 3) * (Real.pi / 2) := by
  set p : ℝ := α / 3 with hp
  have hp0 : 0 < p := by rw [hp]; linarith
  have hp1 : p ≤ 1 := by rw [hp]; linarith
  have hpt : ∀ θ ∈ Work.Spaces.Iθ, (Work.Spaces.Gam α θ - Work.Spaces.K θ) ^ 2
      ≤ 1 - 6 * (Real.sin θ * Real.cos θ ^ 2) + 6 * p * (1 - (Real.sin θ * Real.cos θ ^ 2))
        + 9 * (Real.sin θ * Real.cos θ ^ 2) ^ 2 := by
    intro θ hθ
    have hu := Work.Spaces.sin_mul_cos_sq_mem_Icc θ hθ
    have hcore := pow_sub_three_mul_sq_le (Real.sin θ * Real.cos θ ^ 2) p hu.1 hu.2 hp0 hp1
    have hG : Work.Spaces.Gam α θ = (Real.sin θ * Real.cos θ ^ 2) ^ p := by
      rw [Work.Spaces.Gam, hp]
    have hK : Work.Spaces.K θ = 3 * (Real.sin θ * Real.cos θ ^ 2) := by
      rw [Work.Spaces.K]; ring
    rw [hG, hK]
    exact hcore
  have hcontG : Continuous (fun θ : ℝ => Work.Spaces.Gam α θ) := continuous_Gam α hα
  have hintL : IntegrableOn (fun θ : ℝ => (Work.Spaces.Gam α θ - Work.Spaces.K θ) ^ 2)
      Work.Spaces.Iθ := ((hcontG.sub cont_K).pow 2).integrableOn_Icc
  have hintR : IntegrableOn (fun θ : ℝ => 1 - 6 * (Real.sin θ * Real.cos θ ^ 2)
      + 6 * p * (1 - (Real.sin θ * Real.cos θ ^ 2))
      + 9 * (Real.sin θ * Real.cos θ ^ 2) ^ 2) Work.Spaces.Iθ :=
    (by fun_prop : Continuous fun θ : ℝ => 1 - 6 * (Real.sin θ * Real.cos θ ^ 2)
      + 6 * p * (1 - (Real.sin θ * Real.cos θ ^ 2))
      + 9 * (Real.sin θ * Real.cos θ ^ 2) ^ 2).integrableOn_Icc
  have hmono : (∫ θ in Work.Spaces.Iθ, (Work.Spaces.Gam α θ - Work.Spaces.K θ) ^ 2)
      ≤ ∫ θ in Work.Spaces.Iθ, (1 - 6 * (Real.sin θ * Real.cos θ ^ 2)
          + 6 * p * (1 - (Real.sin θ * Real.cos θ ^ 2))
          + 9 * (Real.sin θ * Real.cos θ ^ 2) ^ 2) :=
    integral_mono_ae hintL hintR
      (by filter_upwards [ae_restrict_mem measurableSet_Icc] with θ hθ; exact hpt θ hθ)
  have h1 : IntegrableOn (fun _ : ℝ => (1 : ℝ)) Work.Spaces.Iθ := continuous_const.integrableOn_Icc
  have h2 : IntegrableOn (fun θ : ℝ => Real.sin θ * Real.cos θ ^ 2) Work.Spaces.Iθ :=
    (by fun_prop : Continuous fun θ : ℝ => Real.sin θ * Real.cos θ ^ 2).integrableOn_Icc
  have h3 : IntegrableOn (fun θ : ℝ => (Real.sin θ * Real.cos θ ^ 2) ^ 2) Work.Spaces.Iθ :=
    (by fun_prop : Continuous fun θ : ℝ => (Real.sin θ * Real.cos θ ^ 2) ^ 2).integrableOn_Icc
  have hA : (∫ θ in Work.Spaces.Iθ, (1 - 3 * (Real.sin θ * Real.cos θ ^ 2)) ^ 2)
      = Real.pi / 2 - 2 + 9 * (Real.pi / 32) := by
    have h6 : IntegrableOn (fun θ : ℝ => 6 * (Real.sin θ * Real.cos θ ^ 2)) Work.Spaces.Iθ :=
      (by fun_prop : Continuous fun θ : ℝ => 6 * (Real.sin θ * Real.cos θ ^ 2)).integrableOn_Icc
    have hA1 : IntegrableOn (fun θ : ℝ => 1 - 6 * (Real.sin θ * Real.cos θ ^ 2)) Work.Spaces.Iθ :=
      (by fun_prop : Continuous fun θ : ℝ => 1 - 6 * (Real.sin θ * Real.cos θ ^ 2)).integrableOn_Icc
    have hA2 : IntegrableOn (fun θ : ℝ => 9 * (Real.sin θ * Real.cos θ ^ 2) ^ 2) Work.Spaces.Iθ :=
      (by fun_prop : Continuous fun θ : ℝ => 9 * (Real.sin θ * Real.cos θ ^ 2) ^ 2).integrableOn_Icc
    rw [show (fun θ : ℝ => (1 - 3 * (Real.sin θ * Real.cos θ ^ 2)) ^ 2)
        = fun θ => (1 - 6 * (Real.sin θ * Real.cos θ ^ 2))
          + 9 * (Real.sin θ * Real.cos θ ^ 2) ^ 2 from by funext θ; ring]
    rw [integral_add hA1 hA2, integral_sub h1 h6, integral_const_mul, integral_const_mul,
        int_Iθ_one, int_Iθ_sinCos2, int_Iθ_sinCos2_sq]
    ring
  have hB : (∫ θ in Work.Spaces.Iθ, (1 - (Real.sin θ * Real.cos θ ^ 2)))
      = Real.pi / 2 - 1 / 3 := by
    rw [integral_sub h1 h2, int_Iθ_one, int_Iθ_sinCos2]
  have hval : (∫ θ in Work.Spaces.Iθ, (1 - 6 * (Real.sin θ * Real.cos θ ^ 2)
          + 6 * p * (1 - (Real.sin θ * Real.cos θ ^ 2))
          + 9 * (Real.sin θ * Real.cos θ ^ 2) ^ 2))
      = Real.pi / 2 - 2 + 9 * (Real.pi / 32) + 6 * p * (Real.pi / 2 - 1 / 3) := by
    have h6 : IntegrableOn (fun θ : ℝ => 6 * p * (1 - (Real.sin θ * Real.cos θ ^ 2)))
        Work.Spaces.Iθ :=
      (by fun_prop : Continuous fun θ : ℝ =>
        6 * p * (1 - (Real.sin θ * Real.cos θ ^ 2))).integrableOn_Icc
    have hA1 : IntegrableOn (fun θ : ℝ => (1 - 3 * (Real.sin θ * Real.cos θ ^ 2)) ^ 2)
        Work.Spaces.Iθ :=
      (by fun_prop : Continuous fun θ : ℝ =>
        (1 - 3 * (Real.sin θ * Real.cos θ ^ 2)) ^ 2).integrableOn_Icc
    rw [show (fun θ : ℝ => 1 - 6 * (Real.sin θ * Real.cos θ ^ 2)
          + 6 * p * (1 - (Real.sin θ * Real.cos θ ^ 2))
          + 9 * (Real.sin θ * Real.cos θ ^ 2) ^ 2)
        = fun θ => (1 - 3 * (Real.sin θ * Real.cos θ ^ 2)) ^ 2
          + 6 * p * (1 - (Real.sin θ * Real.cos θ ^ 2)) from by funext θ; ring]
    rw [integral_add hA1 h6, integral_const_mul, hA, hB]
  rw [hval] at hmono
  have hπ : Real.pi / 2 - 2 + 9 * (Real.pi / 32) = 25 * Real.pi / 32 - 2 := by ring
  have hcorr : 6 * p * (Real.pi / 2 - 1 / 3) ≤ 6 * p * (Real.pi / 2) := by
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    linarith
  linarith

/-- The normalisation constant is `≤ 1`. -/
lemma c_le_one (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) : Work.Spaces.c α ≤ 1 := by
  have hK : IntegrableOn Work.Spaces.K Work.Spaces.Iθ := cont_K.integrableOn_Icc
  have hGK : IntegrableOn (fun θ => Work.Spaces.Gam α θ * Work.Spaces.K θ) Work.Spaces.Iθ :=
    Work.Spaces.CAux.integrableOn_GamK α hα
  have hpt : ∀ θ ∈ Work.Spaces.Iθ, Work.Spaces.Gam α θ * Work.Spaces.K θ ≤ Work.Spaces.K θ := by
    intro θ hθ
    have hG := (Work.Spaces.Gam_bounds α θ hα hθ).2
    have hK0 := K_nonneg hθ
    nlinarith
  calc Work.Spaces.c α = ∫ θ in Work.Spaces.Iθ, Work.Spaces.Gam α θ * Work.Spaces.K θ := rfl
    _ ≤ ∫ θ in Work.Spaces.Iθ, Work.Spaces.K θ :=
        integral_mono_ae hGK hK
          (by filter_upwards [ae_restrict_mem measurableSet_Icc] with θ hθ; exact hpt θ hθ)
    _ = 1 := Work.Coercivity.integral_Itheta_K

/-- The normalisation defect: `1 − c ≤ 3p(π/2)`, `p = α/3`. -/
lemma one_sub_c_le (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1 / 10 ^ 14) :
    1 - Work.Spaces.c α ≤ 3 * (α / 3) * (Real.pi / 2) := by
  set p : ℝ := α / 3 with hp
  have hp0 : 0 < p := by rw [hp]; linarith
  have hα1' : α ≤ 1 := by
    have : (1 : ℝ) / 10 ^ 14 ≤ 1 := by norm_num
    linarith
  have hK : IntegrableOn Work.Spaces.K Work.Spaces.Iθ := cont_K.integrableOn_Icc
  have hGK : IntegrableOn (fun θ => Work.Spaces.Gam α θ * Work.Spaces.K θ) Work.Spaces.Iθ :=
    Work.Spaces.CAux.integrableOn_GamK α hα
  have hpt : ∀ θ ∈ Work.Spaces.Iθ, Work.Spaces.K θ - Work.Spaces.Gam α θ * Work.Spaces.K θ
      ≤ 3 * p := by
    intro θ hθ
    have hu := Work.Spaces.sin_mul_cos_sq_mem_Icc θ hθ
    have hG : Work.Spaces.Gam α θ = (Real.sin θ * Real.cos θ ^ 2) ^ p := by
      rw [Work.Spaces.Gam, hp]
    have hK' : Work.Spaces.K θ = 3 * (Real.sin θ * Real.cos θ ^ 2) := by
      rw [Work.Spaces.K]; ring
    rw [hG, hK']
    have hb := unit_sub_pow_le' (Real.sin θ * Real.cos θ ^ 2) p hu.1 hu.2 (le_of_lt hp0)
    have h3 : 3 * (Real.sin θ * Real.cos θ ^ 2)
          - (Real.sin θ * Real.cos θ ^ 2) ^ p * (3 * (Real.sin θ * Real.cos θ ^ 2))
        = 3 * ((Real.sin θ * Real.cos θ ^ 2) * (1 - (Real.sin θ * Real.cos θ ^ 2) ^ p)) := by
      ring
    rw [h3]
    have h4 : (Real.sin θ * Real.cos θ ^ 2) * (1 - (Real.sin θ * Real.cos θ ^ 2) ^ p) ≤ p := by
      nlinarith [hb, hu.1]
    linarith
  have hInt : IntegrableOn (fun θ => Work.Spaces.K θ - Work.Spaces.Gam α θ * Work.Spaces.K θ)
      Work.Spaces.Iθ := hK.sub hGK
  have hconst : IntegrableOn (fun _ : ℝ => 3 * p) Work.Spaces.Iθ :=
    continuous_const.integrableOn_Icc
  have hstep : (∫ θ in Work.Spaces.Iθ, (Work.Spaces.K θ - Work.Spaces.Gam α θ * Work.Spaces.K θ))
      ≤ 3 * p * (Real.pi / 2) := by
    have h := integral_mono_ae hInt hconst
      (by filter_upwards [ae_restrict_mem measurableSet_Icc] with θ hθ; exact hpt θ hθ)
    rwa [int_const] at h
  have hsub : 1 - Work.Spaces.c α
      = ∫ θ in Work.Spaces.Iθ, (Work.Spaces.K θ - Work.Spaces.Gam α θ * Work.Spaces.K θ) := by
    rw [show Work.Spaces.c α = ∫ θ in Work.Spaces.Iθ, Work.Spaces.Gam α θ * Work.Spaces.K θ from rfl,
        ← Work.Coercivity.integral_Itheta_K]
    exact (integral_sub hK hGK).symm
  rw [hsub]
  exact hstep

end Work.FTS.CoercivityFix.Coer1T.GamL2
