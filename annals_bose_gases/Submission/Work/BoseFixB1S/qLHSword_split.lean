import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixB1S.BoxPotDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

noncomputable section

open MeasureTheory
open scoped Real BigOperators

namespace Work.BoseFixB1S

open Submission.BoseGases

theorem qLHSword_split {N : ℕ} {ℓ μ : ℝ} (hℓ : 0 < ℓ)
    {w w1 om : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) → ℝ}
    (hwc : Continuous (fun p : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) => w p.1 p.2))
    (homc : Continuous (fun p : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) => om p.1 p.2))
    (hw1rel : ∀ x y : EuclideanSpace ℝ (Fin 3), w1 x y = w x y * (1 - om x y))
    {Φ : Submission.BoseGases.X N → ℝ} (hΦc : Continuous Φ) :
    Submission.BoseGases.qLHSword (N := N) ℓ μ w w1 Φ
      = -μ * (∑ i : Fin N, Work.BoseFixB1S.boxMuPhi (N := N) ℓ w1 Φ i)
        + (1 / 2) * (∑ p ∈ Submission.BoseGases.pairSet N,
            ∫ x in Submission.BoseGases.abox N ℓ,
              (Φ x) ^ 2 * w (x p.1) (x p.2)) := by
  -- continuity of the fibre mean and of the two-body slot sum
  have hw1c : Continuous
      (fun p : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) => w1 p.1 p.2) :=
    Submission.BoseGases.w1_continuous hwc homc hw1rel
  have hfibc : ∀ i : Fin N, Continuous (fun x : X N => w1Fibre ℓ w1 (x i)) := by
    intro i
    exact (Submission.BoseGases.w1Fibre_continuous hℓ hw1c).comp
      (by fun_prop : Continuous (fun x : X N => x i))
  have hWsumc : Continuous (fun x : X N => ∑ p ∈ pairSet N, w (x p.1) (x p.2)) := by
    refine continuous_finsetSum (pairSet N) (fun p hp => ?_)
    exact hwc.comp (by fun_prop : Continuous (fun x : X N => (x p.1, x p.2)))
  -- integrability of the two pieces
  have hint1 : IntegrableOn (fun x : X N => (Φ x) ^ 2 * (- μ * (∑ i : Fin N, w1Fibre ℓ w1 (x i))))
      (abox N ℓ) volume := integrableOn_abox_of_continuous hℓ (by fun_prop)
  have hint2 : IntegrableOn
      (fun x : X N => (Φ x) ^ 2 * ((1 / 2) * (∑ p ∈ pairSet N, w (x p.1) (x p.2))))
      (abox N ℓ) volume := integrableOn_abox_of_continuous hℓ (by fun_prop)
  have hfi : ∀ i : Fin N,
      IntegrableOn (fun x : X N => (Φ x) ^ 2 * w1Fibre ℓ w1 (x i)) (abox N ℓ) volume := by
    intro i
    refine integrableOn_abox_of_continuous hℓ ?_
    exact (hΦc.pow 2).mul (hfibc i)
  have hWi : ∀ p ∈ pairSet N,
      IntegrableOn (fun x : X N => (Φ x) ^ 2 * w (x p.1) (x p.2)) (abox N ℓ) volume := by
    intro p hp
    refine integrableOn_abox_of_continuous hℓ ?_
    exact (hΦc.pow 2).mul (hwc.comp (by fun_prop : Continuous (fun x : X N => (x p.1, x p.2))))
  -- the μ part: pull the slot-sum out of the integral
  have hmu : (∫ x in abox N ℓ, (Φ x) ^ 2 * (- μ * (∑ i : Fin N, w1Fibre ℓ w1 (x i)))) =
      - μ * (∑ i : Fin N, boxMuPhi (N := N) ℓ w1 Φ i) := by
    calc
      (∫ x in abox N ℓ, (Φ x) ^ 2 * (- μ * (∑ i : Fin N, w1Fibre ℓ w1 (x i))))
          = (∫ x in abox N ℓ, (- μ) * ((Φ x) ^ 2 * (∑ i : Fin N, w1Fibre ℓ w1 (x i)))) := by
            apply integral_congr_ae
            filter_upwards with x
            ring
      _ = - μ * (∫ x in abox N ℓ, (Φ x) ^ 2 * (∑ i : Fin N, w1Fibre ℓ w1 (x i))) := by
            rw [← integral_const_mul (- μ)
              (fun x : X N => (Φ x) ^ 2 * (∑ i : Fin N, w1Fibre ℓ w1 (x i)))]
      _ = - μ * (∑ i : Fin N, (∫ x in abox N ℓ, (Φ x) ^ 2 * w1Fibre ℓ w1 (x i))) := by
            congr 1
            calc
              (∫ x in abox N ℓ, (Φ x) ^ 2 * (∑ i : Fin N, w1Fibre ℓ w1 (x i)))
                  = ∫ x in abox N ℓ, (∑ i : Fin N, (Φ x) ^ 2 * w1Fibre ℓ w1 (x i)) := by
                    apply integral_congr_ae
                    filter_upwards with x
                    rw [Finset.mul_sum]
              _ = ∑ i : Fin N, (∫ x in abox N ℓ, (Φ x) ^ 2 * w1Fibre ℓ w1 (x i)) := by
                    exact integral_finsetSum (Finset.univ : Finset (Fin N))
                      (fun i hi => by simpa [IntegrableOn] using hfi i)
      _ = - μ * (∑ i : Fin N, boxMuPhi (N := N) ℓ w1 Φ i) := by
            simp [boxMuPhi]
  -- the pair part: pull the pair-sum out of the integral
  have hpair : (∫ x in abox N ℓ, (Φ x) ^ 2 * ((1 / 2) * (∑ p ∈ pairSet N, w (x p.1) (x p.2)))) =
      (1 / 2) * (∑ p ∈ pairSet N, ∫ x in abox N ℓ, (Φ x) ^ 2 * w (x p.1) (x p.2)) := by
    calc
      (∫ x in abox N ℓ, (Φ x) ^ 2 * ((1 / 2) * (∑ p ∈ pairSet N, w (x p.1) (x p.2))))
          = (∫ x in abox N ℓ, (1 / 2) * ((Φ x) ^ 2 * (∑ p ∈ pairSet N, w (x p.1) (x p.2)))) := by
            apply integral_congr_ae
            filter_upwards with x
            ring
      _ = (1 / 2) * (∫ x in abox N ℓ, (Φ x) ^ 2 * (∑ p ∈ pairSet N, w (x p.1) (x p.2))) := by
            rw [← integral_const_mul (1 / 2 : ℝ)
              (fun x : X N => (Φ x) ^ 2 * (∑ p ∈ pairSet N, w (x p.1) (x p.2)))]
      _ = (1 / 2) * (∑ p ∈ pairSet N, ∫ x in abox N ℓ, (Φ x) ^ 2 * w (x p.1) (x p.2)) := by
            congr 1
            calc
              (∫ x in abox N ℓ, (Φ x) ^ 2 * (∑ p ∈ pairSet N, w (x p.1) (x p.2)))
                  = ∫ x in abox N ℓ, (∑ p ∈ pairSet N, (Φ x) ^ 2 * w (x p.1) (x p.2)) := by
                    apply integral_congr_ae
                    filter_upwards with x
                    rw [Finset.mul_sum]
              _ = ∑ p ∈ pairSet N, (∫ x in abox N ℓ, (Φ x) ^ 2 * w (x p.1) (x p.2)) := by
                    exact integral_finsetSum (pairSet N)
                      (fun p hp => by simpa [IntegrableOn] using hWi p hp)
  calc
    Submission.BoseGases.qLHSword (N := N) ℓ μ w w1 Φ
        = ∫ x in abox N ℓ, (Φ x) ^ 2 * (- μ * (∑ i : Fin N, w1Fibre ℓ w1 (x i))
            + (1 / 2) * (∑ p ∈ pairSet N, w (x p.1) (x p.2))) := rfl
    _ = (∫ x in abox N ℓ, (Φ x) ^ 2 * (- μ * (∑ i : Fin N, w1Fibre ℓ w1 (x i))))
        + (∫ x in abox N ℓ, (Φ x) ^ 2 * ((1 / 2) * (∑ p ∈ pairSet N, w (x p.1) (x p.2)))) := by
          rw [← integral_add hint1 hint2]
          apply integral_congr_ae
          filter_upwards with x
          ring
    _ = -μ * (∑ i : Fin N, boxMuPhi (N := N) ℓ w1 Φ i)
        + (1 / 2) * (∑ p ∈ pairSet N,
            ∫ x in abox N ℓ, (Φ x) ^ 2 * w (x p.1) (x p.2)) := by
          rw [hmu, hpair]

end Work.BoseFixB1S

end
