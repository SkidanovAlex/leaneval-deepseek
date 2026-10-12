import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBoxFock.SqrtKin.kinFT_sq_integrable
import Submission.Work.BoseBoxFock.SqrtKin.kinFT_weight2_integrable
import Submission.Work.BoseBoxFock.SqrtKin.kinFT_weight_integrable
import Submission.Work.BoseBoxFock.lattice_heatSubordination
import Submission.Work.BoseBoxFock.tauGapDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseBoxFock

open MeasureTheory
open scoped BigOperators

set_option linter.unusedVariables false

/-!
# `Work.BoseBoxFock.nu_tauTheta_eq_truncated`

The **exact lattice/continuum bookkeeping for the cap weight** `tauTheta c r = (max 0 (c - r))²`.

The point of the identity is that the cap is *exactly* the truncation of the low-frequency
parabola: with

    τ_c(r) = (c - r)₊² = 1_{r ≤ c}·(c² - 2c·r + r²) ,

the difference between the lattice sum and the continuum integral of `τ_c(‖·‖)·‖kinFT g‖²` is the
*same* three-term combination of the truncated lattice sums and truncated continuum integrals
`1_{‖·‖ ≤ c}`, `‖·‖·1_{‖·‖ ≤ c}`, `‖·‖²·1_{‖·‖ ≤ c}`.  So the identity is the algebraic expansion
of the square, valid whenever the three truncated lattice densities are summable — which they are,
being dominated by the full densities `ℓ⁻³‖k_n‖^j‖kinFT g k_n‖²`
(`Work.BoseBoxFock.summable_lattice_kinFT_weight`) — and the three truncated continuum densities
are integrable, being dominated by `‖p‖^j‖kinFT g p‖²`
(`Work.BoseBoxFock.SqrtKin.kinFT_sq_integrable`, `…kinFT_weight_integrable`,
`…kinFT_weight2_integrable`).

Nothing here needs the support hypothesis `tsupport g ⊆ ball 0 (ℓ/2)`; the content is the
expansion and the two linearity computations.
-/

/-- **Pointwise expansion of the cap.**  For every `r` and every `G`,
`(ℓ³)⁻¹τ_c(r)G` is the same three-term combination of the truncation indicators that appears on
the right-hand side of `nu_tauTheta_eq_truncated`. -/
lemma tauTheta_mul_ite (ℓ c r G : ℝ) :
    (ℓ ^ 3)⁻¹ * tauTheta c r * G
      = c ^ 2 * (if r ≤ c then (ℓ ^ 3)⁻¹ * G else 0)
        - 2 * c * (if r ≤ c then (ℓ ^ 3)⁻¹ * r * G else 0)
        + (if r ≤ c then (ℓ ^ 3)⁻¹ * r ^ 2 * G else 0) := by
  rw [tauTheta]
  by_cases h : r ≤ c
  · rw [if_pos h, if_pos h, if_pos h, max_eq_right (by linarith)]
    ring
  · rw [if_neg h, if_neg h, if_neg h, max_eq_left (by linarith)]
    ring

/-- **Summability of the truncated lattice kinetic densities.**  The truncation
`1_{‖k_n‖ ≤ c}` can only decrease the (nonnegative) full density, which is summable by
`Work.BoseBoxFock.summable_lattice_kinFT_weight`. -/
lemma summable_trunc_weight {ℓ c : ℝ} (hℓ : 0 < ℓ)
    {g : EuclideanSpace ℝ (Fin 3) → ℂ} (hg : ContDiff ℝ (⊤ : ENat) g)
    (hgc : HasCompactSupport g) (j : ℕ) :
    Summable (fun n : Fin 3 → ℤ => if ‖kmomInt ℓ n‖ ≤ c then
      (ℓ ^ 3)⁻¹ * ‖kmomInt ℓ n‖ ^ j * ‖Submission.BoseGases.kinFT g (kmomInt ℓ n)‖ ^ 2
      else 0) := by
  refine Summable.of_nonneg_of_le (fun n => ?_) (fun n => ?_)
    (summable_lattice_kinFT_weight (ℓ := ℓ) hℓ hg hgc j)
  · split_ifs <;> positivity
  · split_ifs with h
    · exact le_rfl
    · positivity

/-- **Linearity of the lattice sum** in the quadratic expansion
`c²·A - 2c·B + C`. -/
lemma tsum_quad_split {A B C : (Fin 3 → ℤ) → ℝ} {c : ℝ}
    (hA : Summable A) (hB : Summable B) (hC : Summable C) :
    (∑' n, (c ^ 2 * A n - 2 * c * B n + C n))
      = c ^ 2 * (∑' n, A n) - 2 * c * (∑' n, B n) + (∑' n, C n) := by
  have h1 : Summable (fun n => c ^ 2 * A n) := hA.mul_left (c ^ 2)
  have h2 : Summable (fun n => 2 * c * B n) := hB.mul_left (2 * c)
  have h3 : Summable (fun n => c ^ 2 * A n - 2 * c * B n) := h1.sub h2
  rw [Summable.tsum_add h3 hC, Summable.tsum_sub h1 h2, hA.tsum_mul_left, hB.tsum_mul_left]

/-- **The continuum half of `nu_tauTheta_eq_truncated`.**  With
`s = {p | ‖p‖ ≤ c}` and `G ≥ 0`-free assumptions only on integrability,
`∫ τ_c(‖p‖)G = c²∫_s G - 2c∫_s ‖p‖G + ∫_s ‖p‖²G`: off `s` the weight vanishes and the
truncation indicators vanish, and on `s` the weight is `(c - ‖p‖)² = c² - 2c‖p‖ + ‖p‖²`. -/
lemma integral_cap_split {c : ℝ} {G : EuclideanSpace ℝ (Fin 3) → ℝ}
    (h0 : Integrable G)
    (h1 : Integrable (fun p : EuclideanSpace ℝ (Fin 3) => ‖p‖ * G p))
    (h2 : Integrable (fun p : EuclideanSpace ℝ (Fin 3) => ‖p‖ ^ 2 * G p)) :
    (∫ p : EuclideanSpace ℝ (Fin 3), tauTheta c ‖p‖ * G p)
      = c ^ 2 * (∫ p in {p : EuclideanSpace ℝ (Fin 3) | ‖p‖ ≤ c}, G p)
        - 2 * c * (∫ p in {p : EuclideanSpace ℝ (Fin 3) | ‖p‖ ≤ c}, ‖p‖ * G p)
        + (∫ p in {p : EuclideanSpace ℝ (Fin 3) | ‖p‖ ≤ c}, ‖p‖ ^ 2 * G p) := by
  have hs : MeasurableSet {p : EuclideanSpace ℝ (Fin 3) | ‖p‖ ≤ c} :=
    measurableSet_le continuous_norm.measurable measurable_const
  have hzero : ∀ p : EuclideanSpace ℝ (Fin 3),
      p ∉ {p : EuclideanSpace ℝ (Fin 3) | ‖p‖ ≤ c} → tauTheta c ‖p‖ * G p = 0 := by
    intro p hp
    have hpc : c < ‖p‖ := by simpa using hp
    have hz : tauTheta c ‖p‖ = 0 := by
      rw [tauTheta, max_eq_left (by linarith : c - ‖p‖ ≤ 0)]
      ring
    rw [hz, zero_mul]
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero
        (f := fun p : EuclideanSpace ℝ (Fin 3) => tauTheta c ‖p‖ * G p) hzero]
  rw [show (∫ p in {p : EuclideanSpace ℝ (Fin 3) | ‖p‖ ≤ c}, tauTheta c ‖p‖ * G p)
      = ∫ p in {p : EuclideanSpace ℝ (Fin 3) | ‖p‖ ≤ c},
          ((c ^ 2 * G p - (2 * c) * (‖p‖ * G p)) + ‖p‖ ^ 2 * G p) from by
    refine setIntegral_congr_fun hs (fun p hp => ?_)
    rw [tauTheta, max_eq_right (by linarith [(show ‖p‖ ≤ c from hp)] : (0 : ℝ) ≤ c - ‖p‖)]
    ring]
  rw [integral_add (f := fun p : EuclideanSpace ℝ (Fin 3) =>
          c ^ 2 * G p - (2 * c) * (‖p‖ * G p))
        (g := fun p : EuclideanSpace ℝ (Fin 3) => ‖p‖ ^ 2 * G p)
        ((h0.integrableOn.const_mul (c ^ 2)).sub (h1.integrableOn.const_mul (2 * c)))
        h2.integrableOn]
  rw [integral_sub (f := fun p : EuclideanSpace ℝ (Fin 3) => c ^ 2 * G p)
        (g := fun p : EuclideanSpace ℝ (Fin 3) => (2 * c) * (‖p‖ * G p))
        (h0.integrableOn.const_mul (c ^ 2)) (h1.integrableOn.const_mul (2 * c))]
  rw [integral_const_mul (c ^ 2) (fun p : EuclideanSpace ℝ (Fin 3) => G p),
      integral_const_mul (2 * c) (fun p : EuclideanSpace ℝ (Fin 3) => ‖p‖ * G p)]

theorem nu_tauTheta_eq_truncated {ℓ c : ℝ} (hℓ : 0 < ℓ) (hc : 0 < c)
    {g : EuclideanSpace ℝ (Fin 3) → ℂ} (hg : ContDiff ℝ (⊤ : ENat) g)
    (hgc : HasCompactSupport g) (hgsupp : tsupport g ⊆ Metric.ball 0 (ℓ / 2)) :
    (∑' n : Fin 3 → ℤ, (ℓ ^ 3)⁻¹ * Work.BoseBoxFock.tauTheta c
          ‖Work.BoseBoxFock.kmomInt ℓ n‖
        * ‖Submission.BoseGases.kinFT g (Work.BoseBoxFock.kmomInt ℓ n)‖ ^ 2)
      - ((2 * Real.pi) ^ 3)⁻¹ * ∫ p : EuclideanSpace ℝ (Fin 3),
          Work.BoseBoxFock.tauTheta c ‖p‖ * ‖Submission.BoseGases.kinFT g p‖ ^ 2
    = c ^ 2 * ((∑' n : Fin 3 → ℤ, if ‖Work.BoseBoxFock.kmomInt ℓ n‖ ≤ c then
                  (ℓ ^ 3)⁻¹ * ‖Submission.BoseGases.kinFT g (Work.BoseBoxFock.kmomInt ℓ n)‖ ^ 2
                else 0)
              - ((2 * Real.pi) ^ 3)⁻¹ * ∫ p in {p : EuclideanSpace ℝ (Fin 3) | ‖p‖ ≤ c},
                  ‖Submission.BoseGases.kinFT g p‖ ^ 2)
      - 2 * c * ((∑' n : Fin 3 → ℤ, if ‖Work.BoseBoxFock.kmomInt ℓ n‖ ≤ c then
                  (ℓ ^ 3)⁻¹ * ‖Work.BoseBoxFock.kmomInt ℓ n‖
                    * ‖Submission.BoseGases.kinFT g (Work.BoseBoxFock.kmomInt ℓ n)‖ ^ 2
                else 0)
              - ((2 * Real.pi) ^ 3)⁻¹ * ∫ p in {p : EuclideanSpace ℝ (Fin 3) | ‖p‖ ≤ c},
                  ‖p‖ * ‖Submission.BoseGases.kinFT g p‖ ^ 2)
      + ((∑' n : Fin 3 → ℤ, if ‖Work.BoseBoxFock.kmomInt ℓ n‖ ≤ c then
                  (ℓ ^ 3)⁻¹ * ‖Work.BoseBoxFock.kmomInt ℓ n‖ ^ 2
                    * ‖Submission.BoseGases.kinFT g (Work.BoseBoxFock.kmomInt ℓ n)‖ ^ 2
                else 0)
              - ((2 * Real.pi) ^ 3)⁻¹ * ∫ p in {p : EuclideanSpace ℝ (Fin 3) | ‖p‖ ≤ c},
                  ‖p‖ ^ 2 * ‖Submission.BoseGases.kinFT g p‖ ^ 2) := by
  -- the three truncated lattice densities are summable
  have hA : Summable (fun n : Fin 3 → ℤ => if ‖kmomInt ℓ n‖ ≤ c then
      (ℓ ^ 3)⁻¹ * ‖Submission.BoseGases.kinFT g (kmomInt ℓ n)‖ ^ 2 else 0) := by
    simpa using summable_trunc_weight (ℓ := ℓ) (c := c) hℓ hg hgc 0
  have hB : Summable (fun n : Fin 3 → ℤ => if ‖kmomInt ℓ n‖ ≤ c then
      (ℓ ^ 3)⁻¹ * ‖kmomInt ℓ n‖ * ‖Submission.BoseGases.kinFT g (kmomInt ℓ n)‖ ^ 2
      else 0) := by
    simpa using summable_trunc_weight (ℓ := ℓ) (c := c) hℓ hg hgc 1
  have hC : Summable (fun n : Fin 3 → ℤ => if ‖kmomInt ℓ n‖ ≤ c then
      (ℓ ^ 3)⁻¹ * ‖kmomInt ℓ n‖ ^ 2 * ‖Submission.BoseGases.kinFT g (kmomInt ℓ n)‖ ^ 2
      else 0) := by
    simpa using summable_trunc_weight (ℓ := ℓ) (c := c) hℓ hg hgc 2
  -- the lattice half
  have hsum : (∑' n : Fin 3 → ℤ, (ℓ ^ 3)⁻¹ * Work.BoseBoxFock.tauTheta c
        ‖Work.BoseBoxFock.kmomInt ℓ n‖
        * ‖Submission.BoseGases.kinFT g (Work.BoseBoxFock.kmomInt ℓ n)‖ ^ 2)
      = c ^ 2 * (∑' n : Fin 3 → ℤ, if ‖Work.BoseBoxFock.kmomInt ℓ n‖ ≤ c then
                  (ℓ ^ 3)⁻¹ * ‖Submission.BoseGases.kinFT g (Work.BoseBoxFock.kmomInt ℓ n)‖ ^ 2
                else 0)
        - 2 * c * (∑' n : Fin 3 → ℤ, if ‖Work.BoseBoxFock.kmomInt ℓ n‖ ≤ c then
                  (ℓ ^ 3)⁻¹ * ‖Work.BoseBoxFock.kmomInt ℓ n‖
                    * ‖Submission.BoseGases.kinFT g (Work.BoseBoxFock.kmomInt ℓ n)‖ ^ 2
                else 0)
        + (∑' n : Fin 3 → ℤ, if ‖Work.BoseBoxFock.kmomInt ℓ n‖ ≤ c then
                  (ℓ ^ 3)⁻¹ * ‖Work.BoseBoxFock.kmomInt ℓ n‖ ^ 2
                    * ‖Submission.BoseGases.kinFT g (Work.BoseBoxFock.kmomInt ℓ n)‖ ^ 2
                else 0) := by
    have hcongr : (∑' n : Fin 3 → ℤ, (ℓ ^ 3)⁻¹ * Work.BoseBoxFock.tauTheta c
          ‖Work.BoseBoxFock.kmomInt ℓ n‖
          * ‖Submission.BoseGases.kinFT g (Work.BoseBoxFock.kmomInt ℓ n)‖ ^ 2)
        = ∑' n : Fin 3 → ℤ,
            (c ^ 2 * (if ‖Work.BoseBoxFock.kmomInt ℓ n‖ ≤ c then
                  (ℓ ^ 3)⁻¹ * ‖Submission.BoseGases.kinFT g (Work.BoseBoxFock.kmomInt ℓ n)‖ ^ 2
                else 0)
              - 2 * c * (if ‖Work.BoseBoxFock.kmomInt ℓ n‖ ≤ c then
                  (ℓ ^ 3)⁻¹ * ‖Work.BoseBoxFock.kmomInt ℓ n‖
                    * ‖Submission.BoseGases.kinFT g (Work.BoseBoxFock.kmomInt ℓ n)‖ ^ 2
                else 0)
              + (if ‖Work.BoseBoxFock.kmomInt ℓ n‖ ≤ c then
                  (ℓ ^ 3)⁻¹ * ‖Work.BoseBoxFock.kmomInt ℓ n‖ ^ 2
                    * ‖Submission.BoseGases.kinFT g (Work.BoseBoxFock.kmomInt ℓ n)‖ ^ 2
                else 0)) :=
      tsum_congr (fun n : Fin 3 → ℤ => tauTheta_mul_ite ℓ c ‖Work.BoseBoxFock.kmomInt ℓ n‖
        (‖Submission.BoseGases.kinFT g (Work.BoseBoxFock.kmomInt ℓ n)‖ ^ 2))
    rw [hcongr]
    exact tsum_quad_split hA hB hC
  -- the continuum half
  have hI : (∫ p : EuclideanSpace ℝ (Fin 3),
        Work.BoseBoxFock.tauTheta c ‖p‖ * ‖Submission.BoseGases.kinFT g p‖ ^ 2)
      = c ^ 2 * (∫ p in {p : EuclideanSpace ℝ (Fin 3) | ‖p‖ ≤ c},
                  ‖Submission.BoseGases.kinFT g p‖ ^ 2)
        - 2 * c * (∫ p in {p : EuclideanSpace ℝ (Fin 3) | ‖p‖ ≤ c},
                  ‖p‖ * ‖Submission.BoseGases.kinFT g p‖ ^ 2)
        + (∫ p in {p : EuclideanSpace ℝ (Fin 3) | ‖p‖ ≤ c},
                  ‖p‖ ^ 2 * ‖Submission.BoseGases.kinFT g p‖ ^ 2) :=
    integral_cap_split
      (G := fun p : EuclideanSpace ℝ (Fin 3) => ‖Submission.BoseGases.kinFT g p‖ ^ 2)
      (SqrtKin.kinFT_sq_integrable hg hgc)
      (SqrtKin.kinFT_weight_integrable hg hgc)
      (SqrtKin.kinFT_weight2_integrable hg hgc)
  rw [hsum, hI]
  ring

end Work.BoseBoxFock
