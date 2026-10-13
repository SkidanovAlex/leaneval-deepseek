import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.StrongPersist.Clauses
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.Defs
import Submission.Work.FTS.TransportS.Slots
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6BWork.rowAux
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6BWork.rowCoefExpansion
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6BWork.FlatP.Basic
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6BWork.FlatP.DomAQ
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6BWork.FlatP.abs_mixed_mul_le
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6BWork.FlatP.zWeight_flat
import Submission.Work.Spaces.sin_two_rpow
import Submission.Work.FTS.PhiStar.Series.Weil.integrableOn_prod_mul

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongPersist.H6Rows.Npair6BWork

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

/-! ## §1. Small helpers

The flat-price star row is proved by a "min-split" Cauchy–Schwarz: the two decay factors
`z/(1+z)` and `z/(1+z)²` of the two coefficient slots are combined into
`(z²/(1+z)³)²`, whose `w²`-weighted integral collapses to `∫ (1+z)^{-2} = 1`. -/

/-- `(z/(1+z))²·(z/(1+z)²)² = (z²/(1+z)³)²`. -/
theorem pq_sq_eq {z : ℝ} (hz1 : 1 + z ≠ 0) :
    ((z / (1 + z)) * (z / (1 + z) ^ 2)) ^ 2 = (z ^ 2 / (1 + z) ^ 3) ^ 2 := by
  rw [show (z / (1 + z)) * (z / (1 + z) ^ 2) = z ^ 2 / (1 + z) ^ 3 by field_simp]

/-- The two angular powers of the `a ≥ 1` case combine:
`σ^{-γ}·(8192·σ^{α/5})² = 8192²·σ^{-1+3α/10}`. -/
theorem gam_sigma_combine {σ α : ℝ} (hσ : 0 < σ) :
    σ ^ (-(Work.Spaces.gam α)) * ((8192 : ℝ) * σ ^ (α / 5)) ^ 2
      = (8192 : ℝ) ^ 2 * σ ^ (-1 + 3 * α / 10) := by
  have h2 : (σ ^ (α / 5)) ^ 2 = σ ^ (2 * α / 5) := by
    rw [← Real.rpow_natCast (σ ^ (α / 5)) 2, ← Real.rpow_mul hσ.le]
    congr 1
    ring
  have h3 : σ ^ (-(Work.Spaces.gam α)) * σ ^ (2 * α / 5) = σ ^ (-1 + 3 * α / 10) := by
    rw [← Real.rpow_add hσ]
    congr 1
    rw [Work.Spaces.gam]
    ring
  rw [mul_pow, h2, ← h3]
  ring

/-- The pointwise input of the two-weight Cauchy–Schwarz for the pairing `ρ·X·Z`. -/
theorem abs_mul_one_sq_le {ρ X Z : ℝ} (hρ : 0 ≤ ρ) :
    |ρ * X * 1 * Z| ≤ 1 * (Real.sqrt (ρ * X ^ 2) * Real.sqrt (ρ * Z ^ 2)) := by
  have hs : Real.sqrt ρ * Real.sqrt ρ = ρ := Real.mul_self_sqrt hρ
  have h1 : Real.sqrt (ρ * X ^ 2) = Real.sqrt ρ * |X| := by
    rw [Real.sqrt_mul hρ, Real.sqrt_sq_eq_abs]
  have h2 : Real.sqrt (ρ * Z ^ 2) = Real.sqrt ρ * |Z| := by
    rw [Real.sqrt_mul hρ, Real.sqrt_sq_eq_abs]
  have hA : |ρ * X * 1 * Z| = ρ * |X| * |Z| := by
    rw [abs_mul, abs_mul, abs_mul, abs_one, abs_of_nonneg hρ]
    ring
  rw [hA, h1, h2, one_mul]
  have h7 : ρ * |X| ≤ (Real.sqrt ρ * Real.sqrt ρ) * |X| :=
    mul_le_mul_of_nonneg_right (le_of_eq hs.symm) (abs_nonneg X)
  calc ρ * |X| * |Z| = (ρ * |X|) * |Z| := by ring
    _ ≤ ((Real.sqrt ρ * Real.sqrt ρ) * |X|) * |Z| := mul_le_mul_of_nonneg_right h7 (abs_nonneg Z)
    _ = Real.sqrt ρ * |X| * (Real.sqrt ρ * |Z|) := by ring

/-! ## §2. The `zWeight_flat` estimate in product-measure form -/

/-- `FlatP.zWeight_flat` transported to the product measure `PM` of `(dz|Iz) ⊗ (dθ|Iθ)`. -/
theorem zWeight_flat_PM {E : ℝ → ℝ} {B : ℝ}
    (hbint : MeasureTheory.IntegrableOn E Work.Spaces.Iθ)
    (hble : (∫ θ in Work.Spaces.Iθ, E θ) ≤ B) :
    MeasureTheory.Integrable (fun p : ℝ × ℝ =>
        (Work.Spaces.w p.1) ^ 2 * E p.2 * (p.1 ^ 2 / (1 + p.1) ^ 3) ^ 2) PM ∧
    (∫ p, (Work.Spaces.w p.1) ^ 2 * E p.2 * (p.1 ^ 2 / (1 + p.1) ^ 3) ^ 2 ∂PM) ≤ B := by
  obtain ⟨h1, h2⟩ := FlatP.zWeight_flat E B hbint hble
  rw [FlatP.PM_eq_restrict]
  exact ⟨h1, h2⟩

/-! ## §3. The final arithmetic -/

/-- **The final arithmetic.**  With `D₀ = 819200²`, the Cauchy–Schwarz output
`√((KA·KQ)²·D₀/α)·√(H)` is bounded by `10⁷·α^{-3}·(1+KA)(1+KQ)(1+M)(1+H)` for
`α ∈ (0,1]` and nonnegative data. -/
theorem final_arith {α KA KQ M H : ℝ} (hα0 : 0 < α) (hα1 : α ≤ 1)
    (hKA0 : 0 ≤ KA) (hKQ0 : 0 ≤ KQ) (hM0 : 0 ≤ M) (hH0 : 0 ≤ H) :
    Real.sqrt ((KA * KQ) ^ 2 * (((819200 : ℝ) ^ 2) / α)) * Real.sqrt H
      ≤ 10000000 * α ^ (-(3 : ℝ)) * (1 + KA) * (1 + KQ) * (1 + M) * (1 + H) := by
  have hy1 : (1 : ℝ) ≤ 1 / α := by rw [one_le_div hα0]; exact hα1
  have hrpow : α ^ (-(3 : ℝ)) = (1 / α) ^ 3 := by
    have h3 : α ^ (3 : ℝ) = α ^ 3 := Real.rpow_natCast α 3
    rw [Real.rpow_neg hα0.le, h3, one_div, inv_pow]
  have hsqrt1 : Real.sqrt ((1 : ℝ) / α) ≤ α ^ (-(3 : ℝ)) := by
    rw [hrpow, Real.sqrt_le_left (by positivity)]
    have h5 : (1 : ℝ) ≤ (1 / α) ^ 5 := one_le_pow₀ hy1
    nlinarith [hy1, h5]
  have hsqrtD : Real.sqrt (((819200 : ℝ) ^ 2) / α) = 819200 * Real.sqrt (1 / α) := by
    rw [show ((819200 : ℝ) ^ 2) / α = (819200 : ℝ) ^ 2 * (1 / α) by ring,
      Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ (819200 : ℝ) ^ 2), Real.sqrt_sq (by norm_num)]
  have h1 : Real.sqrt ((KA * KQ) ^ 2 * (((819200 : ℝ) ^ 2) / α))
      = (KA * KQ) * (819200 * Real.sqrt (1 / α)) := by
    rw [Real.sqrt_mul (sq_nonneg (KA * KQ)), Real.sqrt_sq_eq_abs,
      abs_of_nonneg (mul_nonneg hKA0 hKQ0), hsqrtD]
  have e2 : Real.sqrt H ≤ 1 + H := by nlinarith [Real.sq_sqrt hH0, Real.sqrt_nonneg H]
  have e3 : KA * KQ ≤ (1 + KA) * (1 + KQ) := by nlinarith
  have e4 : (819200 : ℝ) ≤ 10000000 * (1 + M) := by nlinarith
  have hnA : (0 : ℝ) ≤ 1 + KA := by linarith
  have hnQ : (0 : ℝ) ≤ 1 + KQ := by linarith
  have hnH : (0 : ℝ) ≤ 1 + H := by linarith
  calc Real.sqrt ((KA * KQ) ^ 2 * (((819200 : ℝ) ^ 2) / α)) * Real.sqrt H
      = (KA * KQ) * (819200 * Real.sqrt (1 / α)) * Real.sqrt H := by rw [h1]
    _ ≤ ((1 + KA) * (1 + KQ)) * (819200 * α ^ (-(3 : ℝ))) * (1 + H) := by
        have hb : 819200 * Real.sqrt (1 / α) ≤ 819200 * α ^ (-(3 : ℝ)) :=
          mul_le_mul_of_nonneg_left hsqrt1 (by norm_num)
        have h12 : (KA * KQ) * (819200 * Real.sqrt (1 / α))
            ≤ ((1 + KA) * (1 + KQ)) * (819200 * α ^ (-(3 : ℝ))) :=
          mul_le_mul e3 hb (by positivity) (by positivity)
        exact mul_le_mul h12 e2 (Real.sqrt_nonneg H) (by positivity)
    _ ≤ 10000000 * α ^ (-(3 : ℝ)) * (1 + KA) * (1 + KQ) * (1 + M) * (1 + H) := by
        have hfac : (0 : ℝ) ≤ (1 + KA) * (1 + KQ) * α ^ (-(3 : ℝ)) * (1 + H) := by positivity
        have h := mul_le_mul_of_nonneg_right e4 hfac
        calc ((1 + KA) * (1 + KQ)) * (819200 * α ^ (-(3 : ℝ))) * (1 + H)
            = 819200 * ((1 + KA) * (1 + KQ) * α ^ (-(3 : ℝ)) * (1 + H)) := by ring
          _ ≤ (10000000 * (1 + M)) * ((1 + KA) * (1 + KQ) * α ^ (-(3 : ℝ)) * (1 + H)) := h
          _ = 10000000 * α ^ (-(3 : ℝ)) * (1 + KA) * (1 + KQ) * (1 + M) * (1 + H) := by ring

/-! ## §4. The row -/

theorem rowStarP : ∃ C : ℝ, 0 < C ∧ ∀ α ∈ Set.Ioc 0 1,
    ∀ (A Q f : Work.FTS.Galerkin.Fn) (KA KQ M : ℝ) (a b : ℕ) (ρ : ℝ → ℝ → ℝ),
      Work.FTS.EllipticEst.SmoothOpen A → Work.FTS.EllipticEst.SmoothOpen Q →
      Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.DatData α f M →
      (∀ j i : ℕ, j + i ≤ 6 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
          |Work.Spaces.mixed j i A z θ| ≤ KA * (z / (1 + z)) *
            (if 1 ≤ i then (α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5) else 1)) →
      (∀ j i : ℕ, j + i ≤ 6 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
          |Work.Spaces.mixed j i Q z θ| ≤ KQ * (z / (1 + z) ^ 2) *
            (if 1 ≤ i then (Real.sin (2 * θ)) ^ (α / 3) else 1)) →
      a + b ≤ 6 → Work.FTS.TransportS.IsLeafW α a ρ →
      |Work.FTS.TransportS.slotPairing ρ a b (fun z θ => A z θ * Q z θ) f|
        ≤ C * α ^ (-(3 : ℝ)) * (1 + KA) * (1 + KQ) * (1 + M)
            * (1 + Work.Spaces.HkSq α 6 f) := by
  refine ⟨10000000, by norm_num, ?_⟩
  intro α hα A Q f KA KQ M a b ρ hA hQ hdat hAdec hQdec hab hleaf
  obtain ⟨hα0, hα1⟩ := hα
  -- nonnegativity of the two prices
  have hka : 0 ≤ KA := by
    have h := hAdec 0 0 (by omega) 1 (Real.pi / 4) (by norm_num)
      (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos])
    simp only [Work.Spaces.mixed, Work.Spaces.DzIter_zero, Work.Spaces.DthIter_zero] at h
    have h2 : (1 : ℝ) / (1 + 1) = 1 / 2 := by norm_num
    rw [h2] at h
    rw [if_neg (by norm_num : ¬ 1 ≤ (0 : ℕ))] at h
    nlinarith [abs_nonneg (A 1 (Real.pi / 4))]
  have hkq : 0 ≤ KQ := by
    have h := hQdec 0 0 (by omega) 1 (Real.pi / 4) (by norm_num)
      (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos])
    simp only [Work.Spaces.mixed, Work.Spaces.DzIter_zero, Work.Spaces.DthIter_zero] at h
    have h2 : (1 : ℝ) / (1 + 1) ^ 2 = 1 / 4 := by norm_num
    rw [h2] at h
    rw [if_neg (by norm_num : ¬ 1 ≤ (0 : ℕ))] at h
    nlinarith [abs_nonneg (Q 1 (Real.pi / 4))]
  have hM0 : 0 ≤ M := le_trans (Work.Spaces.HkNorm_nonneg α 4 f) hdat.bdd
  have hSq0 : 0 ≤ Work.Spaces.HkSq α 6 f := Work.Spaces.HkSq_nonneg α 6 f
  have hX : Work.FTS.EllipticEst.SmoothOpen (fun z θ => A z θ * Q z θ) :=
    FlatP.smoothOpen_mul hA hQ
  have habs := FlatP.abs_mixed_mul_le hα0 hα1 hA hQ hAdec hQdec hab
  -- the `L²` mass of the product slot
  have hpmass : MeasureTheory.Integrable (fun p : ℝ × ℝ =>
        ρ p.1 p.2 * (Work.Spaces.mixed b a (fun z θ => A z θ * Q z θ) p.1 p.2) ^ 2) PM ∧
      (∫ p, ρ p.1 p.2
          * (Work.Spaces.mixed b a (fun z θ => A z θ * Q z θ) p.1 p.2) ^ 2 ∂PM)
        ≤ (KA * KQ) ^ 2 * (((819200 : ℝ) ^ 2) / α) := by
    rcases le_or_gt 1 a with ha1 | ha1
    · -- ## `1 ≤ a`: the angular profile `8192²·σ^{-1+3α/10}`
      have hσ := Work.Spaces.sin_two_rpow (-1 + 3 * α / 10) (by linarith) (by nlinarith)
      have hbint : MeasureTheory.IntegrableOn
          (fun θ : ℝ => (8192 : ℝ) ^ 2 * (Real.sin (2 * θ)) ^ (-1 + 3 * α / 10))
          Work.Spaces.Iθ := hσ.1.const_mul _
      have hble : (∫ θ in Work.Spaces.Iθ,
            (8192 : ℝ) ^ 2 * (Real.sin (2 * θ)) ^ (-1 + 3 * α / 10))
          ≤ (8192 : ℝ) ^ 2 * (10000 / α) := by
        rw [MeasureTheory.integral_const_mul]
        have h := hσ.2
        have hp1 : -1 + 3 * α / 10 + 1 = 3 * α / 10 := by ring
        rw [hp1] at h
        have h2 : 100 / (3 * α / 10) = 1000 / (3 * α) := by
          field_simp
          ring
        rw [h2] at h
        have h3 : 1000 / (3 * α) ≤ 10000 / α := by
          rw [div_le_div_iff₀ (by positivity) hα0]
          nlinarith
        exact le_trans (mul_le_mul_of_nonneg_left h (by norm_num))
          (mul_le_mul_of_nonneg_left h3 (by norm_num))
      have hDg := zWeight_flat_PM hbint hble
      have hdom := FlatP.domAQ (a := a) (b := b) (E := fun θ : ℝ =>
            (8192 : ℝ) ^ 2 * (Real.sin (2 * θ)) ^ (-1 + 3 * α / 10))
          (B := (8192 : ℝ) ^ 2 * (10000 / α)) hka hkq hA hQ hleaf hDg ?_
      · refine ⟨hdom.1, le_trans hdom.2 (mul_le_mul_of_nonneg_left ?_ (sq_nonneg _))⟩
        rw [show (8192 : ℝ) ^ 2 * (10000 / α) = ((819200 : ℝ) ^ 2) / α by ring]
      · intro z θ hz hθ0 hθ1
        have hσp : 0 < Real.sin (2 * θ) :=
          Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos])
        have hz1 : (1 + z) ≠ 0 := by positivity
        have hρle := leafW_le_canonW_gam hα0 hleaf z θ hz hθ0 hθ1
        have hρle' : ρ z θ
            ≤ (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) := by
          simpa only [leafGam_eq_canonW, FlatP.canonW_eq] using hρle
        have habs' := habs z θ hz hθ0 hθ1
        rw [if_pos ha1] at habs'
        have hXsq : (Work.Spaces.mixed b a (fun z θ => A z θ * Q z θ) z θ) ^ 2
            ≤ (KA * KQ * (z / (1 + z)) * (z / (1 + z) ^ 2)
                * (8192 * (Real.sin (2 * θ)) ^ (α / 5))) ^ 2 :=
          sq_le_sq' (by linarith [abs_le.mp habs']) (abs_le.mp habs').2
        have hw0 : 0 ≤ (Work.Spaces.w z) ^ 2
            * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) :=
          mul_nonneg (sq_nonneg _) (Real.rpow_nonneg hσp.le _)
        calc ρ z θ * (Work.Spaces.mixed b a (fun z θ => A z θ * Q z θ) z θ) ^ 2
            ≤ ((Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)))
                * (KA * KQ * (z / (1 + z)) * (z / (1 + z) ^ 2)
                    * (8192 * (Real.sin (2 * θ)) ^ (α / 5))) ^ 2 :=
              le_trans (mul_le_mul_of_nonneg_right hρle' (sq_nonneg _))
                (mul_le_mul_of_nonneg_left hXsq hw0)
          _ = (KA * KQ) ^ 2 * ((Work.Spaces.w z) ^ 2
                * ((Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
                    * (8192 * (Real.sin (2 * θ)) ^ (α / 5)) ^ 2)
                * ((z / (1 + z)) * (z / (1 + z) ^ 2)) ^ 2) := by ring
          _ = (KA * KQ) ^ 2 * ((Work.Spaces.w z) ^ 2
                * ((8192 : ℝ) ^ 2 * (Real.sin (2 * θ)) ^ (-1 + 3 * α / 10))
                * ((z / (1 + z)) * (z / (1 + z) ^ 2)) ^ 2) := by
              rw [gam_sigma_combine hσp]
          _ = (KA * KQ) ^ 2 * ((Work.Spaces.w z) ^ 2
                * ((8192 : ℝ) ^ 2 * (Real.sin (2 * θ)) ^ (-1 + 3 * α / 10))
                * (z ^ 2 / (1 + z) ^ 3) ^ 2) := by
              rw [pq_sq_eq hz1]
    · -- ## `a = 0`: the angular profile `8192²·σ^{-η}`
      have ha0 : a = 0 := by omega
      subst ha0
      have hσ := Work.Spaces.sin_two_rpow (-(Work.Spaces.eta)) (by norm_num [Work.Spaces.eta])
        (by norm_num [Work.Spaces.eta])
      have hbint : MeasureTheory.IntegrableOn
          (fun θ : ℝ => (8192 : ℝ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
          Work.Spaces.Iθ := hσ.1.const_mul _
      have hble : (∫ θ in Work.Spaces.Iθ,
            (8192 : ℝ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
          ≤ (8192 : ℝ) ^ 2 * 10000 := by
        rw [MeasureTheory.integral_const_mul]
        have h := hσ.2
        have hp1 : -(Work.Spaces.eta) + 1 = (1 : ℝ) / 100 := by norm_num [Work.Spaces.eta]
        rw [hp1] at h
        rw [show (100 : ℝ) / (1 / 100) = 10000 by norm_num] at h
        exact mul_le_mul_of_nonneg_left h (by norm_num)
      have hDg := zWeight_flat_PM hbint hble
      have hdom := FlatP.domAQ (a := 0) (b := b) (E := fun θ : ℝ =>
            (8192 : ℝ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
          (B := (8192 : ℝ) ^ 2 * 10000) hka hkq hA hQ hleaf hDg ?_
      · refine ⟨hdom.1, le_trans hdom.2 (mul_le_mul_of_nonneg_left ?_ (sq_nonneg _))⟩
        rw [show (8192 : ℝ) ^ 2 * 10000 = ((819200 : ℝ) ^ 2) by ring]
        rw [le_div_iff₀ hα0]
        nlinarith
      · intro z θ hz hθ0 hθ1
        have hz1 : (1 + z) ≠ 0 := by positivity
        have hρle := leafW_le_canonW_eta hleaf z θ hz hθ0 hθ1
        have hρle' : ρ z θ
            ≤ (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) := by
          simpa only [leafEta_eq_canonW, FlatP.canonW_eq] using hρle
        have hσnn : 0 ≤ Real.sin (2 * θ) :=
          Real.sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith [Real.pi_pos])
        have habs' := habs z θ hz hθ0 hθ1
        rw [if_neg (by omega : ¬ 1 ≤ (0 : ℕ))] at habs'
        have hXsq : (Work.Spaces.mixed b 0 (fun z θ => A z θ * Q z θ) z θ) ^ 2
            ≤ (KA * KQ * (z / (1 + z)) * (z / (1 + z) ^ 2) * 8192) ^ 2 :=
          sq_le_sq' (by linarith [abs_le.mp habs']) (abs_le.mp habs').2
        have hw0 : 0 ≤ (Work.Spaces.w z) ^ 2
            * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) :=
          mul_nonneg (sq_nonneg _) (Real.rpow_nonneg hσnn _)
        calc ρ z θ * (Work.Spaces.mixed b 0 (fun z θ => A z θ * Q z θ) z θ) ^ 2
            ≤ ((Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
                * (KA * KQ * (z / (1 + z)) * (z / (1 + z) ^ 2) * 8192) ^ 2 :=
              le_trans (mul_le_mul_of_nonneg_right hρle' (sq_nonneg _))
                (mul_le_mul_of_nonneg_left hXsq hw0)
          _ = (KA * KQ) ^ 2 * ((Work.Spaces.w z) ^ 2
                * ((8192 : ℝ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
                * ((z / (1 + z)) * (z / (1 + z) ^ 2)) ^ 2) := by ring
          _ = (KA * KQ) ^ 2 * ((Work.Spaces.w z) ^ 2
                * ((8192 : ℝ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
                * (z ^ 2 / (1 + z) ^ 3) ^ 2) := by
              rw [pq_sq_eq hz1]
  -- the `L²` mass of the datum slot
  have hfmass : MeasureTheory.Integrable (fun p : ℝ × ℝ =>
        ρ p.1 p.2 * (Work.Spaces.mixed b a f p.1 p.2) ^ 2) PM ∧
      (∫ p, ρ p.1 p.2 * (Work.Spaces.mixed b a f p.1 p.2) ^ 2 ∂PM)
        ≤ Work.Spaces.HkSq α 6 f :=
    val_le_HkSq hdat.sm hdat.h6 (leafW_nonneg hleaf)
      (fun z θ hz hθ0 hθ1 => FlatP.fSlot_le_HkIntegrand hα0 hab hleaf hz hθ0 hθ1)
      ((aesm_leafW hleaf).mul ((aesm_mixed hdat.sm b a).pow 2))
  -- the Cauchy–Schwarz pairing
  obtain ⟨hint, hbd⟩ := rowSummand_core
    (α := α) (KY := 1) (AX := (KA * KQ) ^ 2 * (((819200 : ℝ) ^ 2) / α))
    (AZ := Work.Spaces.HkSq α 6 f)
    (f := f) (X := fun z θ => Work.Spaces.mixed b a (fun z θ => A z θ * Q z θ) z θ)
    (Y := fun _ _ => (1 : ℝ)) (Z := fun z θ => Work.Spaces.mixed b a f z θ)
    (ρv := ρ) (ρ₁ := ρ) (ρ₂ := ρ)
    (by norm_num) (by positivity) hSq0 (leafW_nonneg hleaf) hpmass.1 hfmass.1
    hpmass.2 hfmass.2
    (ae_of_forall_Qd fun z θ hz hθ0 hθ1 => leafW_nonneg hleaf z θ hz hθ0 hθ1)
    (ae_of_forall_Qd fun z θ hz hθ0 hθ1 => leafW_nonneg hleaf z θ hz hθ0 hθ1)
    (Real.continuous_sqrt.comp_aestronglyMeasurable hpmass.1.aestronglyMeasurable)
    (Real.continuous_sqrt.comp_aestronglyMeasurable hfmass.1.aestronglyMeasurable)
    (aesm_leafW hleaf) (aesm_mixed hX b a) aestronglyMeasurable_const (aesm_mixed hdat.sm b a)
    (fun z θ hz hθ0 hθ1 =>
      abs_mul_one_sq_le (leafW_nonneg hleaf z θ hz hθ0 hθ1))
  -- convert `∫ ρ·X·Z` into the slot pairing
  have hEq : (fun p : ℝ × ℝ => ρ p.1 p.2
        * (Work.Spaces.mixed b a (fun z θ => A z θ * Q z θ) p.1 p.2)
        * (1 : ℝ) * Work.Spaces.mixed b a f p.1 p.2)
      = fun p : ℝ × ℝ => ρ p.1 p.2
        * (Work.Spaces.mixed b a (fun z θ => A z θ * Q z θ) p.1 p.2)
        * Work.Spaces.mixed b a f p.1 p.2 := by
    funext p; ring
  have hint' : MeasureTheory.Integrable (Function.uncurry (fun z θ => ρ z θ
      * Work.Spaces.mixed b a (fun z θ => A z θ * Q z θ) z θ
      * Work.Spaces.mixed b a f z θ)) PM := by
    have h : MeasureTheory.Integrable (fun p : ℝ × ℝ => ρ p.1 p.2
        * (Work.Spaces.mixed b a (fun z θ => A z θ * Q z θ) p.1 p.2)
        * Work.Spaces.mixed b a f p.1 p.2) PM := hint.congr (by rw [hEq])
    exact h
  rw [slotPairing_eq_prod (ρv := ρ) (u := fun z θ => A z θ * Q z θ) (v := f) a b hint']
  rw [← hEq]
  refine le_trans hbd (le_trans (le_of_eq (by ring)) (final_arith hα0 hα1 hka hkq hM0 hSq0))

end

end Work.FTS.StrongPersist.H6Rows.Npair6BWork
