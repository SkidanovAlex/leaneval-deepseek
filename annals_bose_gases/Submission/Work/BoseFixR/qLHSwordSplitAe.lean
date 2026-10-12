import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixB1S.qLHSword_split
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

noncomputable section

open MeasureTheory

namespace Work.BoseFixR

/-- The measure-theoretic splitting of `qLHSword` into its one-body (`μ`) part and its
two-body (pair) part, under *integrability* hypotheses on the finitely many pieces rather
than continuity of `Φ`, `w`, `w₁`.  This is the `ae`-flavoured companion of
`Work.BoseFixB1S.qLHSword_split`. -/
theorem qLHSwordSplitAe {N : ℕ} {ℓ μ : ℝ} (hℓ : 0 < ℓ)
    {w w1 : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) → ℝ}
    {Φ : Submission.BoseGases.X N → ℝ}
    (hfi : ∀ i : Fin N, MeasureTheory.IntegrableOn
      (fun x : Submission.BoseGases.X N => (Φ x) ^ 2 * Submission.BoseGases.w1Fibre ℓ w1 (x i))
      (Submission.BoseGases.abox N ℓ) MeasureTheory.volume)
    (hWi : ∀ p ∈ Submission.BoseGases.pairSet N, MeasureTheory.IntegrableOn
      (fun x : Submission.BoseGases.X N => (Φ x) ^ 2 * w (x p.1) (x p.2))
      (Submission.BoseGases.abox N ℓ) MeasureTheory.volume) :
    Submission.BoseGases.qLHSword (N := N) ℓ μ w w1 Φ
      = -μ * (∑ i : Fin N, Work.BoseFixB1S.boxMuPhi (N := N) ℓ w1 Φ i)
        + (1 / 2) * (∑ p ∈ Submission.BoseGases.pairSet N,
            ∫ x in Submission.BoseGases.abox N ℓ, (Φ x) ^ 2 * w (x p.1) (x p.2)) := by
  -- Integrability of the slot-sum `Φ² · Σᵢ w₁-fibre(xᵢ)` and of the pair-sum `Φ² · Σ_{p} w(x_p)`.
  have hA : IntegrableOn
      (fun x : Submission.BoseGases.X N =>
        (Φ x) ^ 2 * (∑ i : Fin N, Submission.BoseGases.w1Fibre ℓ w1 (x i)))
      (Submission.BoseGases.abox N ℓ) volume := by
    have h :
        (fun x : Submission.BoseGases.X N =>
            (Φ x) ^ 2 * (∑ i : Fin N, Submission.BoseGases.w1Fibre ℓ w1 (x i)))
          = fun x : Submission.BoseGases.X N =>
              ∑ i : Fin N, (Φ x) ^ 2 * Submission.BoseGases.w1Fibre ℓ w1 (x i) := by
      funext x
      rw [Finset.mul_sum]
    rw [h]
    exact integrable_finsetSum Finset.univ (fun i _ => by
      simpa [MeasureTheory.IntegrableOn] using hfi i)
  have hB : IntegrableOn
      (fun x : Submission.BoseGases.X N =>
        (Φ x) ^ 2 * (∑ p ∈ Submission.BoseGases.pairSet N, w (x p.1) (x p.2)))
      (Submission.BoseGases.abox N ℓ) volume := by
    have h :
        (fun x : Submission.BoseGases.X N =>
            (Φ x) ^ 2 * (∑ p ∈ Submission.BoseGases.pairSet N, w (x p.1) (x p.2)))
          = fun x : Submission.BoseGases.X N =>
              ∑ p ∈ Submission.BoseGases.pairSet N, (Φ x) ^ 2 * w (x p.1) (x p.2) := by
      funext x
      rw [Finset.mul_sum]
    rw [h]
    exact integrable_finsetSum (Submission.BoseGases.pairSet N) (fun p hp => by
      simpa [MeasureTheory.IntegrableOn] using hWi p hp)
  -- Integrability of the two summands of the density.
  have hint1 : IntegrableOn
      (fun x : Submission.BoseGases.X N =>
        (Φ x) ^ 2 * (-μ * (∑ i : Fin N, Submission.BoseGases.w1Fibre ℓ w1 (x i))))
      (Submission.BoseGases.abox N ℓ) volume := by
    have h :
        (fun x : Submission.BoseGases.X N =>
            (Φ x) ^ 2 * (-μ * (∑ i : Fin N, Submission.BoseGases.w1Fibre ℓ w1 (x i))))
          = fun x : Submission.BoseGases.X N =>
              -μ * ((Φ x) ^ 2 * (∑ i : Fin N, Submission.BoseGases.w1Fibre ℓ w1 (x i))) := by
      funext x
      ring
    rw [h]
    exact hA.const_mul (-μ)
  have hint2 : IntegrableOn
      (fun x : Submission.BoseGases.X N =>
        (Φ x) ^ 2 * ((1 / 2) * (∑ p ∈ Submission.BoseGases.pairSet N, w (x p.1) (x p.2))))
      (Submission.BoseGases.abox N ℓ) volume := by
    have h :
        (fun x : Submission.BoseGases.X N =>
            (Φ x) ^ 2 * ((1 / 2) * (∑ p ∈ Submission.BoseGases.pairSet N, w (x p.1) (x p.2))))
          = fun x : Submission.BoseGases.X N =>
              (1 / 2) * ((Φ x) ^ 2 * (∑ p ∈ Submission.BoseGases.pairSet N, w (x p.1) (x p.2))) := by
      funext x
      ring
    rw [h]
    exact hB.const_mul (1 / 2)
  -- The `μ` part: pull the slot-sum out of the integral.
  have hmu :
      (∫ x in Submission.BoseGases.abox N ℓ,
          (Φ x) ^ 2 * (-μ * (∑ i : Fin N, Submission.BoseGases.w1Fibre ℓ w1 (x i))))
        = -μ * (∑ i : Fin N, Work.BoseFixB1S.boxMuPhi (N := N) ℓ w1 Φ i) := by
    calc
      (∫ x in Submission.BoseGases.abox N ℓ,
          (Φ x) ^ 2 * (-μ * (∑ i : Fin N, Submission.BoseGases.w1Fibre ℓ w1 (x i))))
          = (∫ x in Submission.BoseGases.abox N ℓ,
              (-μ) * ((Φ x) ^ 2 * (∑ i : Fin N, Submission.BoseGases.w1Fibre ℓ w1 (x i)))) := by
            apply integral_congr_ae
            filter_upwards with x
            ring
      _ = -μ * (∫ x in Submission.BoseGases.abox N ℓ,
              (Φ x) ^ 2 * (∑ i : Fin N, Submission.BoseGases.w1Fibre ℓ w1 (x i))) := by
            rw [← integral_const_mul (-μ)
              (fun x : Submission.BoseGases.X N =>
                (Φ x) ^ 2 * (∑ i : Fin N, Submission.BoseGases.w1Fibre ℓ w1 (x i)))]
      _ = -μ * (∑ i : Fin N,
              (∫ x in Submission.BoseGases.abox N ℓ,
                (Φ x) ^ 2 * Submission.BoseGases.w1Fibre ℓ w1 (x i))) := by
            congr 1
            calc
              (∫ x in Submission.BoseGases.abox N ℓ,
                  (Φ x) ^ 2 * (∑ i : Fin N, Submission.BoseGases.w1Fibre ℓ w1 (x i)))
                  = ∫ x in Submission.BoseGases.abox N ℓ,
                      (∑ i : Fin N, (Φ x) ^ 2 * Submission.BoseGases.w1Fibre ℓ w1 (x i)) := by
                    apply integral_congr_ae
                    filter_upwards with x
                    rw [Finset.mul_sum]
              _ = ∑ i : Fin N, (∫ x in Submission.BoseGases.abox N ℓ,
                    (Φ x) ^ 2 * Submission.BoseGases.w1Fibre ℓ w1 (x i)) := by
                    exact integral_finsetSum (Finset.univ : Finset (Fin N))
                      (fun i _ => by simpa [MeasureTheory.IntegrableOn] using hfi i)
      _ = -μ * (∑ i : Fin N, Work.BoseFixB1S.boxMuPhi (N := N) ℓ w1 Φ i) := by
            simp [Work.BoseFixB1S.boxMuPhi]
  -- The pair part: pull the pair-sum out of the integral.
  have hpair :
      (∫ x in Submission.BoseGases.abox N ℓ,
          (Φ x) ^ 2 * ((1 / 2) * (∑ p ∈ Submission.BoseGases.pairSet N, w (x p.1) (x p.2))))
        = (1 / 2) * (∑ p ∈ Submission.BoseGases.pairSet N,
            ∫ x in Submission.BoseGases.abox N ℓ, (Φ x) ^ 2 * w (x p.1) (x p.2)) := by
    calc
      (∫ x in Submission.BoseGases.abox N ℓ,
          (Φ x) ^ 2 * ((1 / 2) * (∑ p ∈ Submission.BoseGases.pairSet N, w (x p.1) (x p.2))))
          = (∫ x in Submission.BoseGases.abox N ℓ,
              (1 / 2) * ((Φ x) ^ 2 * (∑ p ∈ Submission.BoseGases.pairSet N, w (x p.1) (x p.2)))) := by
            apply integral_congr_ae
            filter_upwards with x
            ring
      _ = (1 / 2) * (∫ x in Submission.BoseGases.abox N ℓ,
              (Φ x) ^ 2 * (∑ p ∈ Submission.BoseGases.pairSet N, w (x p.1) (x p.2))) := by
            rw [← integral_const_mul (1 / 2 : ℝ)
              (fun x : Submission.BoseGases.X N =>
                (Φ x) ^ 2 * (∑ p ∈ Submission.BoseGases.pairSet N, w (x p.1) (x p.2)))]
      _ = (1 / 2) * (∑ p ∈ Submission.BoseGases.pairSet N,
              ∫ x in Submission.BoseGases.abox N ℓ, (Φ x) ^ 2 * w (x p.1) (x p.2)) := by
            congr 1
            calc
              (∫ x in Submission.BoseGases.abox N ℓ,
                  (Φ x) ^ 2 * (∑ p ∈ Submission.BoseGases.pairSet N, w (x p.1) (x p.2)))
                  = ∫ x in Submission.BoseGases.abox N ℓ,
                      (∑ p ∈ Submission.BoseGases.pairSet N,
                        (Φ x) ^ 2 * w (x p.1) (x p.2)) := by
                    apply integral_congr_ae
                    filter_upwards with x
                    rw [Finset.mul_sum]
              _ = ∑ p ∈ Submission.BoseGases.pairSet N,
                    (∫ x in Submission.BoseGases.abox N ℓ,
                      (Φ x) ^ 2 * w (x p.1) (x p.2)) := by
                    exact integral_finsetSum (Submission.BoseGases.pairSet N)
                      (fun p hp => by simpa [MeasureTheory.IntegrableOn] using hWi p hp)
  calc
    Submission.BoseGases.qLHSword (N := N) ℓ μ w w1 Φ
        = ∫ x in Submission.BoseGases.abox N ℓ, (Φ x) ^ 2 *
            (-μ * (∑ i : Fin N, Submission.BoseGases.w1Fibre ℓ w1 (x i))
              + (1 / 2) * (∑ p ∈ Submission.BoseGases.pairSet N, w (x p.1) (x p.2))) := rfl
    _ = (∫ x in Submission.BoseGases.abox N ℓ,
            (Φ x) ^ 2 * (-μ * (∑ i : Fin N, Submission.BoseGases.w1Fibre ℓ w1 (x i))))
        + (∫ x in Submission.BoseGases.abox N ℓ,
            (Φ x) ^ 2 * ((1 / 2) * (∑ p ∈ Submission.BoseGases.pairSet N, w (x p.1) (x p.2)))) := by
          rw [← integral_add hint1 hint2]
          apply integral_congr_ae
          filter_upwards with x
          ring
    _ = -μ * (∑ i : Fin N, Work.BoseFixB1S.boxMuPhi (N := N) ℓ w1 Φ i)
        + (1 / 2) * (∑ p ∈ Submission.BoseGases.pairSet N,
            ∫ x in Submission.BoseGases.abox N ℓ, (Φ x) ^ 2 * w (x p.1) (x p.2)) := by
          rw [hmu, hpair]

end Work.BoseFixR
