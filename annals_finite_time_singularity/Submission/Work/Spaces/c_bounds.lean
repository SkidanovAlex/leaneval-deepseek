import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.Spaces.Defs
import Submission.Work.Spaces.CAux.integrableOn_GamK

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.Spaces

/-!
# Bounds for the normalisation constant `c(α)`

`c α = ∫ θ in Iθ, Γ(θ)K(θ) dθ` is the normalisation constant of Elgindi's paper
(`c = ∫₀^{π/2} Γ(θ)K(θ) dθ`, with `Γ(θ) = (sin θ cos²θ)^{α/3}` and
`K(θ) = 3 sin θ cos²θ`).  The paper only ever uses the coarse range
`1/10 ≤ c(α) ≤ 10`, which is what we establish here for `0 < α ≤ 1`.

The integrand is `3 (sin θ cos²θ)^{1 + α/3}`; on `[0, π/2]` the base
`u = sin θ cos²θ` lies in `[0,1]` and the exponent `1 + α/3 ∈ (1, 4/3]`, so the
integrand is squeezed between `0` and `3` (upper bound) and is bounded below by
`3 (1/4)^{4/3} ≥ 2/5` on the sub-interval `[π/6, π/4]`, where `u ≥ 1/4` (lower
bound: `(1/4)^{4/3} ≥ 2/15` since `(2/15)³ = 8/3375 ≤ 1/256 = (1/4)⁴`).
-/

/-- Pointwise bounds for the integrand of `c`: on the domain `Iθ` the product
`Γ(θ)K(θ)` takes values in `[0,3]`. -/
theorem gamK_bounds (α θ : ℝ) (hα : 0 < α) (hθ : θ ∈ Iθ) :
    0 ≤ Gam α θ * K θ ∧ Gam α θ * K θ ≤ 3 := by
  have hs0 : 0 ≤ Real.sin θ :=
    Real.sin_nonneg_of_mem_Icc ⟨hθ.1, by linarith [hθ.2, Real.pi_pos]⟩
  have ht0 : 0 ≤ Real.sin θ * Real.cos θ ^ 2 := mul_nonneg hs0 (by positivity)
  have ht1 : Real.sin θ * Real.cos θ ^ 2 ≤ 1 := by
    have hs1 : Real.sin θ ≤ 1 := Real.sin_le_one θ
    have hc1 : Real.cos θ ^ 2 ≤ 1 := by
      have h := sq_le_sq' (Real.neg_one_le_cos θ) (Real.cos_le_one θ)
      simpa using h
    have hc0 : (0 : ℝ) ≤ Real.cos θ ^ 2 := by positivity
    have h := mul_le_mul hs1 hc1 hc0 (by norm_num : (0 : ℝ) ≤ 1)
    simpa using h
  have hα3 : 0 ≤ α / 3 := by linarith
  have hGam0 : 0 ≤ Gam α θ := by
    rw [Gam]; exact Real.rpow_nonneg ht0 _
  have hGam1 : Gam α θ ≤ 1 := by
    rw [Gam]; exact Real.rpow_le_one ht0 ht1 hα3
  have hKθ : K θ = 3 * (Real.sin θ * Real.cos θ ^ 2) := by rw [K]; ring
  have hK0 : 0 ≤ K θ := by rw [hKθ]; exact mul_nonneg (by norm_num) ht0
  have hK1 : K θ ≤ 3 := by rw [hKθ]; linarith
  exact ⟨mul_nonneg hGam0 hK0, by nlinarith [hGam0, hGam1, hK0, hK1]⟩

/-- Lower bound for the integrand of `c` on the sub-interval `[π/6, π/4]`:
there `u = sin θ cos²θ ≥ 1/4`, whence
`Γ(θ)K(θ) = 3 u^{1+α/3} ≥ 3 u^{4/3} ≥ 3 (1/4)^{4/3} ≥ 2/5`. -/
theorem gamK_lower (α θ : ℝ) (hα : 0 < α) (hα1 : α ≤ 1)
    (hθ : θ ∈ Set.Icc (π/6) (π/4)) : (2 : ℝ) / 5 ≤ Gam α θ * K θ := by
  have hsin : (1/2 : ℝ) ≤ Real.sin θ := by
    have h1 : Real.sin (π/6) ≤ Real.sin θ :=
      Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith [Real.pi_pos])
        (by linarith [hθ.2, Real.pi_pos]) hθ.1
    rwa [Real.sin_pi_div_six] at h1
  have hcos2 : (1/2 : ℝ) ≤ Real.cos θ ^ 2 := by
    have h1 : Real.cos (π/4) ≤ Real.cos θ :=
      Real.cos_le_cos_of_nonneg_of_le_pi (by linarith [hθ.1, Real.pi_pos])
        (by linarith [Real.pi_pos]) hθ.2
    rw [Real.cos_pi_div_four] at h1
    have hsq : (√2/2)^2 = (1/2 : ℝ) := by
      rw [div_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]; norm_num
    have h2 : (√2/2)^2 ≤ (Real.cos θ)^2 := pow_le_pow_left₀ (by positivity) h1 2
    linarith [h2, hsq]
  have hsin0 : (0 : ℝ) ≤ Real.sin θ := le_trans (by norm_num) hsin
  have ht_ge : (1/4 : ℝ) ≤ Real.sin θ * Real.cos θ ^ 2 := by
    have h1 := mul_le_mul hsin hcos2 (by norm_num : (0 : ℝ) ≤ 1/2) hsin0
    rw [show (1/2 : ℝ) * (1/2) = 1/4 by norm_num] at h1
    exact h1
  have ht_pos : (0 : ℝ) < Real.sin θ * Real.cos θ ^ 2 := by linarith
  have ht_le1 : Real.sin θ * Real.cos θ ^ 2 ≤ 1 := by
    have hs : Real.sin θ ≤ 1 := Real.sin_le_one θ
    have hc : Real.cos θ ^ 2 ≤ 1 := by
      have := sq_le_sq' (Real.neg_one_le_cos θ) (Real.cos_le_one θ); simpa using this
    have hc0 : (0 : ℝ) ≤ Real.cos θ ^ 2 := by positivity
    have h1 := mul_le_mul hs hc hc0 (by norm_num : (0 : ℝ) ≤ 1)
    simpa using h1
  have ht_nonneg : (0 : ℝ) ≤ Real.sin θ * Real.cos θ ^ 2 := le_of_lt ht_pos
  have hprod : Gam α θ * K θ = 3 * (Real.sin θ * Real.cos θ ^ 2) ^ (α/3 + 1) := by
    rw [Gam, K, Real.rpow_add' ht_nonneg (by positivity : α/3 + 1 ≠ 0), Real.rpow_one]
    ring
  have hexp : (Real.sin θ * Real.cos θ ^ 2)^((4:ℝ)/3)
      ≤ (Real.sin θ * Real.cos θ ^ 2)^(α/3 + 1) :=
    Real.rpow_le_rpow_of_exponent_ge ht_pos ht_le1 (by linarith)
  have hbase : (1/4 : ℝ)^((4:ℝ)/3) ≤ (Real.sin θ * Real.cos θ ^ 2)^((4:ℝ)/3) :=
    Real.rpow_le_rpow (by norm_num) ht_ge (by norm_num)
  have hnum : (2 : ℝ)/5 ≤ 3 * (1/4 : ℝ)^(4/3 : ℝ) := by
    have h : ((8 : ℝ)/15) ≤ (1/4 : ℝ)^(1/3 : ℝ) := by
      have hbase' : ((8 : ℝ)/15) ^ ((3:ℕ):ℝ) ≤ (1/4 : ℝ) := by
        rw [Real.rpow_natCast]; norm_num
      have hle : (((8 : ℝ)/15) ^ ((3:ℕ):ℝ))^(1/3:ℝ) ≤ (1/4 : ℝ)^(1/3:ℝ) :=
        Real.rpow_le_rpow (by positivity) hbase' (by norm_num)
      have hsimp : (((8 : ℝ)/15) ^ ((3:ℕ):ℝ))^(1/3:ℝ) = (8 : ℝ)/15 := by
        rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 8/15) ((3:ℕ):ℝ) (1/3),
            show (((3:ℕ):ℝ) * (1/3:ℝ)) = 1 by norm_num, Real.rpow_one]
      rwa [hsimp] at hle
    have h4 : (1/4 : ℝ)^(4/3 : ℝ) = (1/4 : ℝ) * (1/4 : ℝ)^(1/3 : ℝ) := by
      rw [show ((4 : ℝ)/3) = 1 + 1/3 by norm_num,
          Real.rpow_add (by norm_num : (0 : ℝ) < 1/4) 1 (1/3), Real.rpow_one]
    nlinarith [h, h4]
  rw [hprod]
  linarith [hnum, hbase, hexp]

theorem c_bounds (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) :
    (1 : ℝ) / 10 ≤ Work.Spaces.c α ∧ Work.Spaces.c α ≤ 10 := by
  have h_int : IntegrableOn (fun θ : ℝ => Gam α θ * K θ) Iθ :=
    CAux.integrableOn_GamK α hα
  have h_nonneg : ∀ᵐ θ ∂(volume.restrict Iθ), (0 : ℝ) ≤ Gam α θ * K θ := by
    rw [Iθ, MeasureTheory.ae_restrict_iff' measurableSet_Icc]
    exact Filter.Eventually.of_forall fun θ hθ => (gamK_bounds α θ hα hθ).1
  have hvolθ : volume.real Iθ = π / 2 := by
    rw [Iθ, MeasureTheory.measureReal_def, Real.volume_Icc,
        ENNReal.toReal_ofReal (by linarith [Real.pi_pos])]
    ring
  have hvolS : volume.real (Set.Icc (π/6) (π/4)) = π / 12 := by
    rw [MeasureTheory.measureReal_def, Real.volume_Icc,
        ENNReal.toReal_ofReal (by linarith [Real.pi_pos])]
    ring
  have hsub : Set.Icc (π/6) (π/4) ⊆ Iθ := fun θ hθ =>
    ⟨by linarith [hθ.1, Real.pi_pos], by linarith [hθ.2, Real.pi_pos]⟩
  have hst : Set.Icc (π/6) (π/4) ≤ᵐ[volume] Iθ := by
    filter_upwards with θ hθ
    exact hsub hθ
  have hfin : volume (Set.Icc (π/6) (π/4)) ≠ ⊤ := by
    rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top
  constructor
  · have hge : (2 : ℝ)/5 * volume.real (Set.Icc (π/6) (π/4))
        ≤ ∫ θ in Set.Icc (π/6) (π/4), Gam α θ * K θ :=
      MeasureTheory.setIntegral_ge_of_const_le_real measurableSet_Icc hfin
        (fun θ hθ => gamK_lower α θ hα hα1 hθ) (h_int.mono_set hsub)
    have hle : ∫ θ in Set.Icc (π/6) (π/4), Gam α θ * K θ
        ≤ ∫ θ in Iθ, Gam α θ * K θ :=
      MeasureTheory.setIntegral_mono_set h_int h_nonneg hst
    have hnum : (1 : ℝ)/10 ≤ (2 : ℝ)/5 * volume.real (Set.Icc (π/6) (π/4)) := by
      rw [hvolS]; linarith [Real.pi_gt_three]
    calc (1 : ℝ)/10 ≤ (2 : ℝ)/5 * volume.real (Set.Icc (π/6) (π/4)) := hnum
      _ ≤ ∫ θ in Set.Icc (π/6) (π/4), Gam α θ * K θ := hge
      _ ≤ ∫ θ in Iθ, Gam α θ * K θ := hle
      _ = Work.Spaces.c α := rfl
  · have hle3 : ∫ θ in Iθ, Gam α θ * K θ ≤ ∫ θ in Iθ, (3 : ℝ) :=
      MeasureTheory.setIntegral_mono_on h_int
        (MeasureTheory.integrableOn_const (by rw [Iθ, Real.volume_Icc]; exact ENNReal.ofReal_ne_top))
        measurableSet_Icc (fun θ hθ => (gamK_bounds α θ hα hθ).2)
    have hconst : ∫ θ in Iθ, (3 : ℝ) = 3 * (π/2) := by
      rw [MeasureTheory.setIntegral_const, hvolθ, smul_eq_mul]; ring
    calc Work.Spaces.c α = ∫ θ in Iθ, Gam α θ * K θ := rfl
      _ ≤ ∫ θ in Iθ, (3 : ℝ) := hle3
      _ = 3 * (π/2) := hconst
      _ ≤ 10 := by linarith [Real.pi_le_four]

end Work.Spaces
