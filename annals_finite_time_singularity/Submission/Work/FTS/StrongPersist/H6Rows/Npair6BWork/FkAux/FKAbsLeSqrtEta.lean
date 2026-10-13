import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.Construction.Defs
import Submission.Work.FTS.Nonlinear.Pieces.Rl1.n5Bound
import Submission.Work.FTS.TransportS.TvUniform.integral_sqrt_mul_sqrt_le
import Submission.Work.Spaces.PairIntegralLe

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongPersist.H6Rows.Npair6BWork.FkAux

open MeasureTheory

/-! ## The weighted angular Cauchy–Schwarz for the angular moment `(F,K)_{L²_θ}`

`FK Y z = ∫_θ Y(z,θ) K(θ) dθ` with `K(θ) = 3 sinθ cos²θ`.  Against the *weighted* slice
energy `∫_θ sin(2θ)^{-η} Y(z,θ)² dθ` (which is what the `ℋ^k` slot energies control) the
correct constant is `4`, since `K(θ) = (3/2) cosθ · sin(2θ)` and
`√(∫_θ K(θ)² sin(2θ)^{η} dθ) ≤ √(∫_θ 3K(θ) dθ) = √3 ≤ 4`.

The proof uses only that `sin(2θ)^{-η} Y²` is integrable on `Iθ`: no measurability is
assumed on `Y` itself.  (When `θ ↦ Y(z,θ)K(θ)` is not a.e. strongly measurable both sides of
the final inequality are handled by the a.e. identities, which hold unconditionally.)
-/

/-- On `Iθ = [0,π/2]`, `sin(2θ) ≥ 0`. -/
private lemma sin_two_nonneg_Iθ {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) : 0 ≤ Real.sin (2 * θ) :=
  Real.sin_nonneg_of_mem_Icc ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩

/-- `K(θ)² ≤ 3K(θ)` on `Iθ`, since `K = 3 sinθ cos²θ` and `sinθ cos²θ ≤ 1`. -/
private lemma K_sq_le_three_mul_K {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    (Work.Spaces.K θ) ^ 2 ≤ 3 * Work.Spaces.K θ := by
  have hs0 : 0 ≤ Real.sin θ := Real.sin_nonneg_of_mem_Icc ⟨hθ.1, by linarith [hθ.2, Real.pi_pos]⟩
  have hc2nn : 0 ≤ Real.cos θ ^ 2 := sq_nonneg _
  have hc2 : Real.cos θ ^ 2 ≤ 1 := by nlinarith [Real.neg_one_le_cos θ, Real.cos_le_one θ]
  have huv0 : 0 ≤ Real.sin θ * Real.cos θ ^ 2 := mul_nonneg hs0 hc2nn
  have huv1 : Real.sin θ * Real.cos θ ^ 2 ≤ 1 := by nlinarith [Real.sin_le_one θ, hc2, huv0, hc2nn]
  have huvsq : (Real.sin θ * Real.cos θ ^ 2) ^ 2 ≤ Real.sin θ * Real.cos θ ^ 2 :=
    by nlinarith [sq_nonneg (Real.sin θ * Real.cos θ ^ 2)]
  rw [Work.Spaces.K]
  nlinarith [huvsq]

/-- `K(θ)² sin(2θ)^η ≤ 3K(θ)` on `Iθ` (`sin(2θ)^η ≤ 1` since `0 < η`). -/
private lemma K_sq_mul_sin_pow_le_three {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    (Work.Spaces.K θ) ^ 2 * Real.sin (2 * θ) ^ Work.Spaces.eta ≤ 3 * Work.Spaces.K θ := by
  have hsin0 : 0 ≤ Real.sin (2 * θ) := sin_two_nonneg_Iθ hθ
  have h1 : Real.sin (2 * θ) ^ Work.Spaces.eta ≤ 1 :=
    Real.rpow_le_one hsin0 (Real.sin_le_one _) (by norm_num [Work.Spaces.eta])
  calc (Work.Spaces.K θ) ^ 2 * Real.sin (2 * θ) ^ Work.Spaces.eta
      ≤ (Work.Spaces.K θ) ^ 2 * 1 := mul_le_mul_of_nonneg_left h1 (sq_nonneg _)
    _ = (Work.Spaces.K θ) ^ 2 := mul_one _
    _ ≤ 3 * Work.Spaces.K θ := K_sq_le_three_mul_K hθ

/-- Almost everywhere on `Iθ`, `sin(2θ) > 0` (the vanishing set is `{0, π/2}`). -/
private lemma ae_sin_two_pos_Iθ :
    ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ), 0 < Real.sin (2 * θ) := by
  have h : ∀ᵐ θ ∂(MeasureTheory.volume.restrict (Set.Ioo (0:ℝ) (Real.pi/2))),
      0 < Real.sin (2 * θ) :=
    MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioo (fun θ hθ =>
      Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos]))
  have hset : MeasureTheory.volume.restrict (Set.Ioo (0:ℝ) (Real.pi/2))
      = MeasureTheory.volume.restrict Work.Spaces.Iθ :=
    MeasureTheory.Measure.restrict_congr_set
      (MeasureTheory.Ioo_ae_eq_Icc (a := (0:ℝ)) (b := Real.pi / 2))
  rwa [hset] at h

theorem FKAbsLeSqrtEta {z : ℝ} {Y : ℝ → ℝ → ℝ}
    (hY : MeasureTheory.IntegrableOn
      (fun θ => Real.sin (2 * θ) ^ (-(Work.Spaces.eta)) * (Y z θ) ^ 2) Work.Spaces.Iθ) :
    |Work.Construction.FK Y z| ≤ 4 * Real.sqrt
      (∫ θ in Work.Spaces.Iθ, Real.sin (2 * θ) ^ (-(Work.Spaces.eta)) * (Y z θ) ^ 2) := by
  have hηpos : 0 < Work.Spaces.eta := by norm_num [Work.Spaces.eta]
  set p : ℝ → ℝ := fun θ => Real.sin (2 * θ) ^ (-(Work.Spaces.eta)) * (Y z θ) ^ 2 with hp
  set q : ℝ → ℝ := fun θ => (Work.Spaces.K θ) ^ 2 * Real.sin (2 * θ) ^ Work.Spaces.eta with hq
  have hp_int : MeasureTheory.Integrable p (MeasureTheory.volume.restrict Work.Spaces.Iθ) := hY
  -- `q` is continuous, hence a.e. strongly measurable
  have hKcont : Continuous Work.Spaces.K := by
    unfold Work.Spaces.K
    exact (continuous_const.mul Real.continuous_sin).mul (Real.continuous_cos.pow 2)
  have hq_cont : Continuous q := by
    rw [hq]
    exact (hKcont.pow 2).mul
      ((Real.continuous_sin.comp (continuous_const.mul continuous_id)).rpow_const
        (fun θ => Or.inr hηpos.le))
  have hq_aesm : AEStronglyMeasurable q (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
    hq_cont.aestronglyMeasurable
  have hK3_int : MeasureTheory.Integrable (fun θ => 3 * Work.Spaces.K θ)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
    Work.FTS.Nonlinear.Pieces.Rl1.n5_integrableOn_K.const_mul 3
  have hqnn : 0 ≤ᵐ[MeasureTheory.volume.restrict Work.Spaces.Iθ] q := by
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with θ hθ
    rw [hq]
    exact mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (sin_two_nonneg_Iθ hθ) _)
  have hqle : q ≤ᵐ[MeasureTheory.volume.restrict Work.Spaces.Iθ]
      (fun θ => 3 * Work.Spaces.K θ) := by
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with θ hθ
    rw [hq]
    exact K_sq_mul_sin_pow_le_three hθ
  have hq_int : MeasureTheory.Integrable q (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
    refine hK3_int.mono' hq_aesm ?_
    filter_upwards [hqnn, hqle] with θ hnn hle
    rwa [Real.norm_eq_abs, abs_of_nonneg hnn]
  -- `∫_θ q ≤ 3`
  have hq_le3 : (∫ θ in Work.Spaces.Iθ, q θ) ≤ 3 := by
    have h1 : (∫ θ in Work.Spaces.Iθ, q θ) ≤ ∫ θ in Work.Spaces.Iθ, 3 * Work.Spaces.K θ :=
      MeasureTheory.integral_mono_ae hq_int hK3_int hqle
    rw [MeasureTheory.integral_const_mul, Work.Coercivity.integral_Itheta_K, mul_one] at h1
    linarith
  have hpnn : 0 ≤ᵐ[MeasureTheory.volume.restrict Work.Spaces.Iθ] p := by
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with θ hθ
    rw [hp]
    exact mul_nonneg (Real.rpow_nonneg (sin_two_nonneg_Iθ hθ) _) (sq_nonneg _)
  -- Cauchy–Schwarz against the weight `sin(2θ)^{η}`
  have hcs := Work.FTS.TransportS.TvUniform.integral_sqrt_mul_sqrt_le
    (MeasureTheory.volume.restrict Work.Spaces.Iθ) hpnn hqnn hp_int hq_int
  -- the pointwise identity `|Y K| = √p √q`
  have hid : ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
      |Y z θ * Work.Spaces.K θ| = Real.sqrt (p θ) * Real.sqrt (q θ) := by
    filter_upwards [ae_sin_two_pos_Iθ] with θ hsin
    have hs1 : Real.sqrt (Real.sin (2 * θ) ^ (-(Work.Spaces.eta)))
        * Real.sqrt (Real.sin (2 * θ) ^ Work.Spaces.eta) = 1 := by
      rw [← Real.sqrt_mul (Real.rpow_nonneg hsin.le _), ← Real.rpow_add hsin,
        show -(Work.Spaces.eta) + Work.Spaces.eta = 0 by ring, Real.rpow_zero, Real.sqrt_one]
    rw [hp, hq, Real.sqrt_mul (Real.rpow_nonneg hsin.le _), Real.sqrt_sq_eq_abs,
      Real.sqrt_mul (sq_nonneg (Work.Spaces.K θ)), Real.sqrt_sq_eq_abs, abs_mul]
    rw [show (Real.sqrt (Real.sin (2 * θ) ^ (-(Work.Spaces.eta))) * |Y z θ|)
          * (|Work.Spaces.K θ| * Real.sqrt (Real.sin (2 * θ) ^ Work.Spaces.eta))
        = (Real.sqrt (Real.sin (2 * θ) ^ (-(Work.Spaces.eta)))
            * Real.sqrt (Real.sin (2 * θ) ^ Work.Spaces.eta))
          * (|Y z θ| * |Work.Spaces.K θ|) from by ring, hs1, one_mul]
  have hFK_le : |Work.Construction.FK Y z|
      ≤ ∫ θ in Work.Spaces.Iθ, Real.sqrt (p θ) * Real.sqrt (q θ) := by
    rw [Work.Construction.FK]
    calc |∫ θ in Work.Spaces.Iθ, Y z θ * Work.Spaces.K θ|
        ≤ ∫ θ in Work.Spaces.Iθ, |Y z θ * Work.Spaces.K θ| :=
          MeasureTheory.abs_integral_le_integral_abs
      _ = ∫ θ in Work.Spaces.Iθ, Real.sqrt (p θ) * Real.sqrt (q θ) :=
          MeasureTheory.integral_congr_ae hid
  have hsqrtq : Real.sqrt (∫ θ in Work.Spaces.Iθ, q θ) ≤ 4 := by
    have h16 : (∫ θ in Work.Spaces.Iθ, q θ) ≤ 16 := by linarith
    calc Real.sqrt (∫ θ in Work.Spaces.Iθ, q θ) ≤ Real.sqrt 16 := Real.sqrt_le_sqrt h16
      _ = 4 := by rw [show (16:ℝ) = 4 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  calc |Work.Construction.FK Y z|
      ≤ ∫ θ in Work.Spaces.Iθ, Real.sqrt (p θ) * Real.sqrt (q θ) := hFK_le
    _ ≤ Real.sqrt (∫ θ in Work.Spaces.Iθ, p θ) * Real.sqrt (∫ θ in Work.Spaces.Iθ, q θ) := hcs
    _ ≤ Real.sqrt (∫ θ in Work.Spaces.Iθ, p θ) * 4 :=
        mul_le_mul_of_nonneg_left hsqrtq (Real.sqrt_nonneg _)
    _ = 4 * Real.sqrt (∫ θ in Work.Spaces.Iθ, p θ) := by ring
    _ = 4 * Real.sqrt (∫ θ in Work.Spaces.Iθ,
          Real.sin (2 * θ) ^ (-(Work.Spaces.eta)) * (Y z θ) ^ 2) := by rw [hp]

end Work.FTS.StrongPersist.H6Rows.Npair6BWork.FkAux
