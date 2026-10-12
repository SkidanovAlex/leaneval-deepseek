import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Topology.UniformSpace.Uniformizable
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Submission.Work.BoseBoxFock.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.FRK.etaH_majorant_exists`

A single `C^∞` majorant for FS's threshold profile `η_H(k) = 1 - f_u(‖k‖/(2κ))`, uniformly in
the `LowCut` `f_u`, with the two properties the `η_H`-row computations need: smoothness with
`L¹`-control of the sixth derivative at the `κ^{-3}` scaling, and the pinching

`0 ≤ H κ k ≤ (if 3κ/2 ≤ ‖k‖ then 1 else 0)`.

## The construction

* `etaTheta x = smoothTransition ((4 - ‖x‖²)·(4/7))` is a smooth bump with values in `[0,1]`,
  equal to `1` on the closed ball of radius `3/2` and to `0` off the ball of radius `2`.
  In particular it is compactly supported, so every iterated derivative of it is compactly
  supported and continuous, hence integrable (`HasCompactSupport.iteratedFDeriv`).
* `etaPsi = 1 - etaTheta` is the complementary profile (`0` on the ball of radius `3/2`, `1` off
  the ball of radius `2`); its sixth derivative is `-D⁶Θ` and hence also integrable.
* `etaMajorant κ k = etaPsi (κ⁻¹ • k)` is the rescaled majorant.

## The two ingredients of the scaling

* the chain rule for a scalar reparametrisation
  (Mathlib's `iteratedFDeriv_comp_const_smul`):
  `D⁶ (etaMajorant κ) p = (κ⁻¹)^6 • D⁶ etaPsi (κ⁻¹ • p)`;
* the change of variables `Measure.integral_comp_inv_smul`:
  `∫ p, g (κ⁻¹ • p) = |κ ^ finrank ℝ ℝ³| • ∫ p, g p = κ³ ∫ p, g p` for `κ > 0`.

Together: `∫ ‖D⁶ (etaMajorant κ)‖ = κ^(-3) ∫ ‖D⁶ etaPsi‖`.
-/

noncomputable section

open MeasureTheory

namespace Work.BoseBoxFock.FRK

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-! ## 1. The smooth bump `Θ` and the complementary profile `Ψ` -/

/-- The smooth bump `x ↦ smoothTransition ((4 - ‖x‖²)·(4/7))`: it equals `1` on the closed ball of
radius `3/2`, `0` off the ball of radius `2`, and takes values in `[0,1]`. -/
def etaTheta (x : E3) : ℝ := Real.smoothTransition ((4 - ‖x‖ ^ 2) * (4 / 7))

/-- The complementary profile `Ψ = 1 - Θ`: it equals `0` on the closed ball of radius `3/2`,
`1` off the ball of radius `2`, and takes values in `[0,1]`. -/
def etaPsi (x : E3) : ℝ := 1 - etaTheta x

/-- The majorant profile at scale `κ`: `etaMajorant κ k = Ψ (κ⁻¹ • k)`. -/
def etaMajorant (κ : ℝ) (k : E3) : ℝ := etaPsi (κ⁻¹ • k)

lemma etaTheta_apply (x : E3) :
    etaTheta x = Real.smoothTransition ((4 - ‖x‖ ^ 2) * (4 / 7)) := rfl

lemma etaPsi_apply (x : E3) : etaPsi x = 1 - etaTheta x := rfl

lemma etaMajorant_apply (κ : ℝ) (k : E3) : etaMajorant κ k = etaPsi (κ⁻¹ • k) := rfl

lemma etaTheta_contDiff : ContDiff ℝ (⊤ : ℕ∞) etaTheta := by
  unfold etaTheta
  refine Real.smoothTransition.contDiff.comp ?_
  have h1 : ContDiff ℝ (⊤ : ℕ∞) (fun x : E3 => ‖x‖ ^ 2) := contDiff_norm_sq ℝ
  have h2 : ContDiff ℝ (⊤ : ℕ∞) (fun x : E3 => (4 : ℝ) - ‖x‖ ^ 2) :=
    (contDiff_const (c := (4 : ℝ))).sub h1
  exact h2.mul (contDiff_const (c := (4 / 7 : ℝ)))

lemma etaTheta_nonneg (x : E3) : 0 ≤ etaTheta x := by
  rw [etaTheta_apply]; exact Real.smoothTransition.nonneg _

lemma etaTheta_le_one (x : E3) : etaTheta x ≤ 1 := by
  rw [etaTheta_apply]; exact Real.smoothTransition.le_one _

lemma etaTheta_eq_one {x : E3} (hx : ‖x‖ ^ 2 ≤ 9 / 4) : etaTheta x = 1 := by
  rw [etaTheta_apply]
  apply Real.smoothTransition.one_of_one_le
  linarith

lemma etaTheta_eq_zero {x : E3} (hx : (4 : ℝ) ≤ ‖x‖ ^ 2) : etaTheta x = 0 := by
  rw [etaTheta_apply]
  apply Real.smoothTransition.zero_of_nonpos
  linarith

lemma etaPsi_contDiff : ContDiff ℝ (⊤ : ℕ∞) etaPsi := by
  have h : etaPsi = (fun _ : E3 => (1 : ℝ)) - etaTheta := rfl
  rw [h]
  exact (contDiff_const (c := (1 : ℝ))).sub etaTheta_contDiff

lemma etaPsi_nonneg (x : E3) : 0 ≤ etaPsi x := by
  rw [etaPsi_apply]; linarith [etaTheta_le_one x]

lemma etaPsi_le_one (x : E3) : etaPsi x ≤ 1 := by
  rw [etaPsi_apply]; linarith [etaTheta_nonneg x]

lemma etaPsi_eq_zero {x : E3} (hx : ‖x‖ ^ 2 ≤ 9 / 4) : etaPsi x = 0 := by
  rw [etaPsi_apply, etaTheta_eq_one hx]; norm_num

lemma etaPsi_eq_one {x : E3} (hx : (4 : ℝ) ≤ ‖x‖ ^ 2) : etaPsi x = 1 := by
  rw [etaPsi_apply, etaTheta_eq_zero hx]; norm_num

lemma etaPsi_eq_zero_of_le {x : E3} (hx : ‖x‖ ≤ 3 / 2) : etaPsi x = 0 := by
  apply etaPsi_eq_zero
  nlinarith [norm_nonneg x]

lemma etaPsi_eq_one_of_le {x : E3} (hx : (2 : ℝ) ≤ ‖x‖) : etaPsi x = 1 := by
  apply etaPsi_eq_one
  nlinarith [norm_nonneg x]

/-! ## 2. Compact support and integrability -/

lemma etaTheta_support_subset :
    Function.support etaTheta ⊆ Metric.closedBall (0 : E3) 2 := by
  intro x hx
  rw [Metric.mem_closedBall, dist_eq_norm, sub_zero]
  by_contra h
  rw [not_le] at h
  exact hx (etaTheta_eq_zero (by nlinarith [h, norm_nonneg x]))

lemma etaTheta_hasCompactSupport : HasCompactSupport etaTheta :=
  HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall (0 : E3) 2)
    etaTheta_support_subset

/-- `D⁶ Ψ = - D⁶ Θ`: `Ψ` is the difference of a constant and `Θ`. -/
lemma etaPsi_iteratedFDeriv_eq_neg :
    iteratedFDeriv ℝ 6 etaPsi = -iteratedFDeriv ℝ 6 etaTheta := by
  have hfun : etaPsi = (fun _ : E3 => (1 : ℝ)) - etaTheta := rfl
  have hsub := iteratedFDeriv_sub (𝕜 := ℝ) (i := 6) (f := fun _ : E3 => (1 : ℝ))
    (g := etaTheta) (contDiff_const (c := (1 : ℝ)))
    (etaTheta_contDiff.of_le (WithTop.coe_le_coe.mpr le_top))
  rw [hfun, hsub, iteratedFDeriv_const_of_ne (𝕜 := ℝ) (E := E3) (F := ℝ) (n := 6)
    (by norm_num) (1 : ℝ), zero_sub]

lemma etaTheta_iteratedFDeriv_integrable :
    Integrable (fun p : E3 => iteratedFDeriv ℝ 6 etaTheta p) :=
  (etaTheta_contDiff.continuous_iteratedFDeriv (m := 6)
      (WithTop.coe_le_coe.mpr le_top)).integrable_of_hasCompactSupport
    (etaTheta_hasCompactSupport.iteratedFDeriv 6)

lemma etaPsi_iteratedFDeriv_norm_integrable :
    Integrable (fun p : E3 => ‖iteratedFDeriv ℝ 6 etaPsi p‖) := by
  refine etaTheta_iteratedFDeriv_integrable.norm.congr ?_
  filter_upwards with p
  rw [etaPsi_iteratedFDeriv_eq_neg]
  simp

/-! ## 3. The scaling of `D⁶` -/

/-- The chain rule for the rescaled profile: `D⁶ (Ψ ∘ (κ⁻¹ • ·)) p = (κ⁻¹)^6 • D⁶ Ψ (κ⁻¹ • p)`. -/
lemma etaMajorant_iteratedFDeriv (κ : ℝ) (_hκ : 0 < κ) (p : E3) :
    iteratedFDeriv ℝ 6 (etaMajorant κ) p
      = (κ⁻¹) ^ 6 • iteratedFDeriv ℝ 6 etaPsi (κ⁻¹ • p) := by
  have h := iteratedFDeriv_comp_const_smul (𝕜 := ℝ) (f := etaPsi) (i := 6) (κ⁻¹)
    (etaPsi_contDiff.of_le (WithTop.coe_le_coe.mpr le_top))
  have hfun : etaMajorant κ = fun z : E3 => etaPsi (κ⁻¹ • z) := rfl
  rw [hfun, h]

lemma etaMajorant_iteratedFDeriv_norm_integrable (κ : ℝ) (hκ : 0 < κ) :
    Integrable (fun p : E3 => ‖iteratedFDeriv ℝ 6 (etaMajorant κ) p‖) := by
  refine ((etaPsi_iteratedFDeriv_norm_integrable.comp_smul
    (inv_ne_zero hκ.ne')).const_mul ((κ⁻¹) ^ 6)).congr ?_
  filter_upwards with p
  rw [etaMajorant_iteratedFDeriv κ hκ p, norm_smul,
    Real.norm_of_nonneg (pow_nonneg (inv_nonneg.mpr hκ.le) 6)]

/-- The `L¹`-norm of `D⁶` of the rescaled profile, exactly:
`∫ ‖D⁶ (Ψ ∘ (κ⁻¹•·))‖ = κ^{-3} ∫ ‖D⁶ Ψ‖`. -/
lemma etaMajorant_integral (κ : ℝ) (hκ : 0 < κ) :
    (∫ p : E3, ‖iteratedFDeriv ℝ 6 (etaMajorant κ) p‖)
      = (∫ p : E3, ‖iteratedFDeriv ℝ 6 etaPsi p‖) * κ ^ (-3 : ℤ) := by
  have hcv := MeasureTheory.Measure.integral_comp_inv_smul (volume : Measure E3)
    (fun y : E3 => ‖iteratedFDeriv ℝ 6 etaPsi y‖) κ
  rw [show (∫ p : E3, ‖iteratedFDeriv ℝ 6 (etaMajorant κ) p‖)
      = ∫ p : E3, (κ⁻¹) ^ 6 * ‖iteratedFDeriv ℝ 6 etaPsi (κ⁻¹ • p)‖ from by
    apply integral_congr_ae
    filter_upwards with p
    rw [etaMajorant_iteratedFDeriv κ hκ p, norm_smul,
      Real.norm_of_nonneg (pow_nonneg (inv_nonneg.mpr hκ.le) 6)]]
  rw [integral_const_mul, hcv, smul_eq_mul, finrank_euclideanSpace_fin,
    abs_of_nonneg (pow_nonneg hκ.le 3)]
  rw [show (-3 : ℤ) = Int.negSucc 2 from rfl, zpow_negSucc]
  norm_num
  field_simp

/-! ## 4. The pointwise bounds -/

/-- The majorant dominates `η_H`, uniformly in the `LowCut`. -/
lemma etaMajorant_ge_etaH (fu : Work.BoseBoxFix.LowCut) {κ : ℝ} (hκ : 0 < κ) (k : E3) :
    Work.BoseBoxFock.etaH fu κ k ≤ etaMajorant κ k := by
  rcases le_or_gt (‖k‖ / (2 * κ)) 1 with ht | ht
  · have h1 : fu.f (‖k‖ / (2 * κ)) = 1 := fu.one _ ht
    have h0 : Work.BoseBoxFock.etaH fu κ k = 0 := by
      rw [Work.BoseBoxFock.etaH, h1]; ring
    rw [h0, etaMajorant_apply]
    exact etaPsi_nonneg _
  · have hk2 : 0 < 2 * κ := by linarith
    have hlt : 2 * κ < ‖k‖ := by simpa using (lt_div_iff₀ hk2).mp ht
    have hnorm : ‖κ⁻¹ • k‖ = κ⁻¹ * ‖k‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr hκ.le)]
    have hge : (2 : ℝ) ≤ ‖κ⁻¹ • k‖ := by
      rw [hnorm]
      have hpos : 0 < κ⁻¹ := inv_pos.mpr hκ
      have hmul : κ⁻¹ * (2 * κ) < κ⁻¹ * ‖k‖ := mul_lt_mul_of_pos_left hlt hpos
      have hval : κ⁻¹ * (2 * κ) = 2 := by field_simp
      linarith
    rw [etaMajorant_apply, etaPsi_eq_one_of_le hge]
    exact Work.BoseBoxFock.etaH_le_one fu κ k

/-- The majorant is supported above the `3κ/2` threshold: `H κ k ≤ 1` there and `≤ 0` below. -/
lemma etaMajorant_le_indicator {κ : ℝ} (hκ : 0 < κ) (k : E3) :
    etaMajorant κ k ≤ (if 3 * κ / 2 ≤ ‖k‖ then (1 : ℝ) else 0) := by
  by_cases h : 3 * κ / 2 ≤ ‖k‖
  · rw [if_pos h, etaMajorant_apply]
    exact etaPsi_le_one _
  · rw [if_neg h, etaMajorant_apply]
    have hlt : ‖k‖ < 3 * κ / 2 := not_le.mp h
    have hpos : 0 < κ⁻¹ := inv_pos.mpr hκ
    have hmul : κ⁻¹ * ‖k‖ < κ⁻¹ * (3 * κ / 2) := mul_lt_mul_of_pos_left hlt hpos
    have hval : κ⁻¹ * (3 * κ / 2) = 3 / 2 := by field_simp
    have h1 : ‖κ⁻¹ • k‖ ≤ 3 / 2 := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr hκ.le)]
      linarith
    rw [etaPsi_eq_zero_of_le h1]

lemma etaMajorant_contDiff (κ : ℝ) : ContDiff ℝ (⊤ : ℕ∞) (etaMajorant κ) := by
  have hfun : etaMajorant κ = etaPsi ∘ (fun k : E3 => κ⁻¹ • k) := rfl
  rw [hfun]
  exact etaPsi_contDiff.comp ((contDiff_id (𝕜 := ℝ) (E := E3)).const_smul (κ⁻¹))

lemma etaMajorant_nonneg (κ : ℝ) (k : E3) : 0 ≤ etaMajorant κ k := by
  rw [etaMajorant_apply]; exact etaPsi_nonneg _

lemma etaMajorant_abs_le (κ : ℝ) (k : E3) :
    |etaMajorant κ k| ≤ 1 * (1 + ‖k‖) ^ 2 := by
  have h1 : |etaMajorant κ k| ≤ 1 := by
    rw [abs_le]
    constructor
    · linarith [etaMajorant_nonneg κ k]
    · rw [etaMajorant_apply]; exact etaPsi_le_one _
  have h2 : (1 : ℝ) ≤ (1 + ‖k‖) ^ 2 := by
    have := norm_nonneg k
    nlinarith
  rw [one_mul]
  exact h1.trans h2

/-! ## 5. The theorem -/

theorem etaH_majorant_exists :
    ∃ (C : ℝ) (H : ℝ → EuclideanSpace ℝ (Fin 3) → ℝ), 0 ≤ C ∧
      (∀ (fu : Work.BoseBoxFix.LowCut) {κ : ℝ}, 0 < κ → ∀ k : EuclideanSpace ℝ (Fin 3),
        Work.BoseBoxFock.etaH fu κ k ≤ H κ k) ∧
      (∀ {κ : ℝ}, 0 < κ → ∀ k : EuclideanSpace ℝ (Fin 3),
        H κ k ≤ (if 3 * κ / 2 ≤ ‖k‖ then (1 : ℝ) else 0)) ∧
      (∀ {κ : ℝ}, 0 < κ → ContDiff ℝ (⊤ : ℕ∞) (H κ)) ∧
      (∀ {κ : ℝ}, 0 < κ → ∀ k : EuclideanSpace ℝ (Fin 3), 0 ≤ H κ k) ∧
      (∀ {κ : ℝ}, 0 < κ →
        ∃ A : ℝ, ∀ k : EuclideanSpace ℝ (Fin 3), |H κ k| ≤ A * (1 + ‖k‖) ^ 2) ∧
      (∀ {κ : ℝ}, 0 < κ →
        MeasureTheory.Integrable (fun p : EuclideanSpace ℝ (Fin 3) =>
          ‖iteratedFDeriv ℝ 6 (H κ) p‖)) ∧
      (∀ {κ : ℝ}, 0 < κ → (∫ p : EuclideanSpace ℝ (Fin 3),
        ‖iteratedFDeriv ℝ 6 (H κ) p‖) ≤ C * κ ^ (-3 : ℤ)) := by
  refine ⟨(∫ p : E3, ‖iteratedFDeriv ℝ 6 etaPsi p‖), etaMajorant, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact integral_nonneg (fun p => norm_nonneg _)
  · intro fu κ hκ k
    exact etaMajorant_ge_etaH fu hκ k
  · intro κ hκ k
    exact etaMajorant_le_indicator hκ k
  · intro κ _
    exact etaMajorant_contDiff κ
  · intro κ hκ k
    exact etaMajorant_nonneg κ k
  · intro κ _
    exact ⟨1, fun k => etaMajorant_abs_le κ k⟩
  · intro κ hκ
    exact etaMajorant_iteratedFDeriv_norm_integrable κ hκ
  · intro κ hκ
    rw [etaMajorant_integral κ hκ]

end Work.BoseBoxFock.FRK
