import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.PotWords
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

open MeasureTheory

namespace Work.BoseBoxFock

/-- The two-body side of FS `eq:potsplit`: the potential word `qLHSword` splits into its μ-part and its pair part,
`qLHSword = −μ·Σᵢ muPhi i + ½·Σ_{p ∈ pairSet} ∫ Φ²·w(x_{p.1},x_{p.2})`,
for a continuous `Φ`, given only that the one-body fibres `x ↦ ∫_y w1(xᵢ,y)` (all `i`) and the pair kernels `w(xᵢ,xⱼ)` (`i ≠ j`) are integrable over the centred box — no continuity of `w`, `w1` is assumed.  Route: split the integrand pointwise (`ring`), apply `MeasureTheory.integral_add` and `integral_const_mul` (each piece is a continuous coefficient, namely `Φ²`, times one of the integrable functions, so `MeasureTheory.IntegrableOn.continuousOn_mul` applies), then `MeasureTheory.integral_finsetSum` twice to pull the slot/pair sums out of the integral.  The pattern to transcribe is the block `hmu`/`hpair`/`hint1`/`hint2`/`hLHS` of `Submission.BoseGases.potsplit_chosen` (`Submission/PotChosen.lean`), with the chosen-kernel integrability lemmas replaced by `MeasureTheory.IntegrableOn.continuousOn_mul` at the given hypotheses. -/
theorem qLHSword_eq_mu_add_pair {N : ℕ} {ℓ μ : ℝ} (hℓ : 0 < ℓ)
    {w w1 : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) → ℝ}
    {Φ : Submission.BoseGases.X N → ℝ} (hΦc : Continuous Φ)
    (hfib : ∀ i : Fin N, MeasureTheory.IntegrableOn
      (fun x : Submission.BoseGases.X N => Submission.BoseGases.w1Fibre ℓ w1 (x i))
      (Submission.BoseGases.abox N ℓ) MeasureTheory.volume)
    (hW : ∀ i j : Fin N, i ≠ j → MeasureTheory.IntegrableOn
      (fun x : Submission.BoseGases.X N => w (x i) (x j))
      (Submission.BoseGases.abox N ℓ) MeasureTheory.volume) :
    Submission.BoseGases.qLHSword (N := N) ℓ μ w w1 Φ =
      - μ * (∑ i : Fin N, Submission.BoseGases.muPhi ℓ w1 Φ i)
        + (1 / 2) * (∑ p ∈ Submission.BoseGases.pairSet N,
            ∫ x in Submission.BoseGases.abox N ℓ, (Φ x) ^ 2 * w (x p.1) (x p.2)) := by
  have hK : IsCompact (Submission.BoseGases.abox N ℓ) := Submission.BoseGases.abox_compact N hℓ
  have hS2c : Continuous (fun x : Submission.BoseGases.X N => (Φ x) ^ 2) := hΦc.pow 2
  have hfi : ∀ i : Fin N, MeasureTheory.IntegrableOn
      (fun x : Submission.BoseGases.X N => (Φ x) ^ 2 * Submission.BoseGases.w1Fibre ℓ w1 (x i))
      (Submission.BoseGases.abox N ℓ) MeasureTheory.volume :=
    fun i => (hfib i).continuousOn_mul hS2c.continuousOn hK
  have hWi : ∀ p ∈ Submission.BoseGases.pairSet N, MeasureTheory.IntegrableOn
      (fun x : Submission.BoseGases.X N => (Φ x) ^ 2 * w (x p.1) (x p.2))
      (Submission.BoseGases.abox N ℓ) MeasureTheory.volume := by
    intro p hp
    have hpne : p.1 ≠ p.2 := by simpa [Submission.BoseGases.pairSet] using hp
    exact (hW p.1 p.2 hpne).continuousOn_mul hS2c.continuousOn hK
  have hmu : (∫ x in Submission.BoseGases.abox N ℓ,
        (Φ x) ^ 2 * (- μ * (∑ i : Fin N, Submission.BoseGases.w1Fibre ℓ w1 (x i)))) =
      - μ * (∑ i : Fin N, Submission.BoseGases.muPhi ℓ w1 Φ i) := by
    calc
      (∫ x in Submission.BoseGases.abox N ℓ, (Φ x) ^ 2 * (- μ * (∑ i : Fin N, Submission.BoseGases.w1Fibre ℓ w1 (x i))))
          = (∫ x in Submission.BoseGases.abox N ℓ, (- μ) * ((Φ x) ^ 2 * (∑ i : Fin N, Submission.BoseGases.w1Fibre ℓ w1 (x i)))) := by
            apply MeasureTheory.integral_congr_ae
            filter_upwards with x
            ring
      _ = - μ * (∫ x in Submission.BoseGases.abox N ℓ, (Φ x) ^ 2 * (∑ i : Fin N, Submission.BoseGases.w1Fibre ℓ w1 (x i))) := by
            rw [← MeasureTheory.integral_const_mul (- μ) (fun x : Submission.BoseGases.X N => (Φ x) ^ 2 * (∑ i : Fin N, Submission.BoseGases.w1Fibre ℓ w1 (x i)))]
      _ = - μ * (∑ i : Fin N, (∫ x in Submission.BoseGases.abox N ℓ, (Φ x) ^ 2 * Submission.BoseGases.w1Fibre ℓ w1 (x i))) := by
            congr 1
            calc
              (∫ x in Submission.BoseGases.abox N ℓ, (Φ x) ^ 2 * (∑ i : Fin N, Submission.BoseGases.w1Fibre ℓ w1 (x i)))
                  = ∫ x in Submission.BoseGases.abox N ℓ, (∑ i : Fin N, (Φ x) ^ 2 * Submission.BoseGases.w1Fibre ℓ w1 (x i)) := by
                    apply MeasureTheory.integral_congr_ae
                    filter_upwards with x
                    rw [Finset.mul_sum]
              _ = ∑ i : Fin N, (∫ x in Submission.BoseGases.abox N ℓ, (Φ x) ^ 2 * Submission.BoseGases.w1Fibre ℓ w1 (x i)) := by
                    exact MeasureTheory.integral_finsetSum (Finset.univ : Finset (Fin N))
                      (f := fun (i : Fin N) (x : Submission.BoseGases.X N) => (Φ x) ^ 2 * Submission.BoseGases.w1Fibre ℓ w1 (x i))
                      (fun i _ => by simpa [MeasureTheory.IntegrableOn] using hfi i)
      _ = - μ * (∑ i : Fin N, Submission.BoseGases.muPhi ℓ w1 Φ i) := by
            simp [Submission.BoseGases.muPhi]
  have hpair : (∫ x in Submission.BoseGases.abox N ℓ, (Φ x) ^ 2 * ((1 / 2) * (∑ p ∈ Submission.BoseGases.pairSet N, w (x p.1) (x p.2)))) =
      (1 / 2) * (∑ p ∈ Submission.BoseGases.pairSet N, ∫ x in Submission.BoseGases.abox N ℓ, (Φ x) ^ 2 * w (x p.1) (x p.2)) := by
    calc
      (∫ x in Submission.BoseGases.abox N ℓ, (Φ x) ^ 2 * ((1 / 2) * (∑ p ∈ Submission.BoseGases.pairSet N, w (x p.1) (x p.2))))
          = (∫ x in Submission.BoseGases.abox N ℓ, (1 / 2) * ((Φ x) ^ 2 * (∑ p ∈ Submission.BoseGases.pairSet N, w (x p.1) (x p.2)))) := by
            apply MeasureTheory.integral_congr_ae
            filter_upwards with x
            ring
      _ = (1 / 2) * (∫ x in Submission.BoseGases.abox N ℓ, (Φ x) ^ 2 * (∑ p ∈ Submission.BoseGases.pairSet N, w (x p.1) (x p.2))) := by
            rw [← MeasureTheory.integral_const_mul (1 / 2 : ℝ) (fun x : Submission.BoseGases.X N => (Φ x) ^ 2 * (∑ p ∈ Submission.BoseGases.pairSet N, w (x p.1) (x p.2)))]
      _ = (1 / 2) * (∑ p ∈ Submission.BoseGases.pairSet N, ∫ x in Submission.BoseGases.abox N ℓ, (Φ x) ^ 2 * w (x p.1) (x p.2)) := by
            congr 1
            calc
              (∫ x in Submission.BoseGases.abox N ℓ, (Φ x) ^ 2 * (∑ p ∈ Submission.BoseGases.pairSet N, w (x p.1) (x p.2)))
                  = ∫ x in Submission.BoseGases.abox N ℓ, (∑ p ∈ Submission.BoseGases.pairSet N, (Φ x) ^ 2 * w (x p.1) (x p.2)) := by
                    apply MeasureTheory.integral_congr_ae
                    filter_upwards with x
                    rw [Finset.mul_sum]
              _ = ∑ p ∈ Submission.BoseGases.pairSet N, (∫ x in Submission.BoseGases.abox N ℓ, (Φ x) ^ 2 * w (x p.1) (x p.2)) := by
                    exact MeasureTheory.integral_finsetSum (Submission.BoseGases.pairSet N)
                      (f := fun (p : Fin N × Fin N) (x : Submission.BoseGases.X N) => (Φ x) ^ 2 * w (x p.1) (x p.2))
                      (fun p hp => by simpa [MeasureTheory.IntegrableOn] using hWi p hp)
  have hint1 : MeasureTheory.IntegrableOn (fun x : Submission.BoseGases.X N =>
      (Φ x) ^ 2 * (- μ * (∑ i : Fin N, Submission.BoseGases.w1Fibre ℓ w1 (x i)))) (Submission.BoseGases.abox N ℓ) MeasureTheory.volume := by
    have hfs : MeasureTheory.IntegrableOn (fun x : Submission.BoseGases.X N => (∑ i : Fin N, (Φ x) ^ 2 * Submission.BoseGases.w1Fibre ℓ w1 (x i)))
        (Submission.BoseGases.abox N ℓ) MeasureTheory.volume := by
      change Integrable (fun x : Submission.BoseGases.X N => ∑ i : Fin N, (Φ x) ^ 2 * Submission.BoseGases.w1Fibre ℓ w1 (x i))
          (MeasureTheory.volume.restrict (Submission.BoseGases.abox N ℓ))
      simpa using (MeasureTheory.integrable_finsetSum (Finset.univ : Finset (Fin N))
        (f := fun (i : Fin N) (x : Submission.BoseGases.X N) => (Φ x) ^ 2 * Submission.BoseGases.w1Fibre ℓ w1 (x i))
        (fun i hi => by simpa [MeasureTheory.IntegrableOn] using hfi i))
    have hpt : (fun x : Submission.BoseGases.X N => (Φ x) ^ 2 * (- μ * (∑ i : Fin N, Submission.BoseGases.w1Fibre ℓ w1 (x i)))) =ᵐ[MeasureTheory.volume.restrict (Submission.BoseGases.abox N ℓ)]
        fun x : Submission.BoseGases.X N => (- μ) * (∑ i : Fin N, (Φ x) ^ 2 * Submission.BoseGases.w1Fibre ℓ w1 (x i)) := by
      apply ae_of_all
      intro x
      calc
        (Φ x) ^ 2 * (- μ * (∑ i : Fin N, Submission.BoseGases.w1Fibre ℓ w1 (x i)))
            = (- μ) * ((Φ x) ^ 2 * (∑ i : Fin N, Submission.BoseGases.w1Fibre ℓ w1 (x i))) := by ring
        _ = (- μ) * (∑ i : Fin N, (Φ x) ^ 2 * Submission.BoseGases.w1Fibre ℓ w1 (x i)) := by
              rw [Finset.mul_sum]
    have hfsm : Integrable (fun x : Submission.BoseGases.X N => (- μ) * (∑ i : Fin N, (Φ x) ^ 2 * Submission.BoseGases.w1Fibre ℓ w1 (x i)))
        (MeasureTheory.volume.restrict (Submission.BoseGases.abox N ℓ)) := by
      simpa [MeasureTheory.IntegrableOn] using hfs.const_mul (-μ)
    change Integrable (fun x : Submission.BoseGases.X N =>
        (Φ x) ^ 2 * (- μ * (∑ i : Fin N, Submission.BoseGases.w1Fibre ℓ w1 (x i)))) (MeasureTheory.volume.restrict (Submission.BoseGases.abox N ℓ))
    exact hfsm.congr hpt.symm
  have hint2 : MeasureTheory.IntegrableOn (fun x : Submission.BoseGases.X N =>
      (Φ x) ^ 2 * ((1 / 2) * (∑ p ∈ Submission.BoseGases.pairSet N, w (x p.1) (x p.2)))) (Submission.BoseGases.abox N ℓ) MeasureTheory.volume := by
    have hfs : MeasureTheory.IntegrableOn (fun x : Submission.BoseGases.X N => (∑ p ∈ Submission.BoseGases.pairSet N, (Φ x) ^ 2 * w (x p.1) (x p.2)))
        (Submission.BoseGases.abox N ℓ) MeasureTheory.volume := by
      change Integrable (fun x : Submission.BoseGases.X N => ∑ p ∈ Submission.BoseGases.pairSet N, (Φ x) ^ 2 * w (x p.1) (x p.2))
          (MeasureTheory.volume.restrict (Submission.BoseGases.abox N ℓ))
      simpa using (MeasureTheory.integrable_finsetSum (Submission.BoseGases.pairSet N)
        (f := fun (p : Fin N × Fin N) (x : Submission.BoseGases.X N) => (Φ x) ^ 2 * w (x p.1) (x p.2))
        (fun p hp => by simpa [MeasureTheory.IntegrableOn] using hWi p hp))
    have hpt : (fun x : Submission.BoseGases.X N => (Φ x) ^ 2 * ((1 / 2) * (∑ p ∈ Submission.BoseGases.pairSet N, w (x p.1) (x p.2)))) =ᵐ[MeasureTheory.volume.restrict (Submission.BoseGases.abox N ℓ)]
        fun x : Submission.BoseGases.X N => (1 / 2) * (∑ p ∈ Submission.BoseGases.pairSet N, (Φ x) ^ 2 * w (x p.1) (x p.2)) := by
      apply ae_of_all
      intro x
      calc
        (Φ x) ^ 2 * ((1 / 2) * (∑ p ∈ Submission.BoseGases.pairSet N, w (x p.1) (x p.2)))
            = (1 / 2) * ((Φ x) ^ 2 * (∑ p ∈ Submission.BoseGases.pairSet N, w (x p.1) (x p.2))) := by ring
        _ = (1 / 2) * (∑ p ∈ Submission.BoseGases.pairSet N, (Φ x) ^ 2 * w (x p.1) (x p.2)) := by
              rw [Finset.mul_sum]
    have hfsm : Integrable (fun x : Submission.BoseGases.X N => (1 / 2) * (∑ p ∈ Submission.BoseGases.pairSet N, (Φ x) ^ 2 * w (x p.1) (x p.2)))
        (MeasureTheory.volume.restrict (Submission.BoseGases.abox N ℓ)) := by
      simpa [MeasureTheory.IntegrableOn] using hfs.const_mul (1 / 2)
    change Integrable (fun x : Submission.BoseGases.X N =>
        (Φ x) ^ 2 * ((1 / 2) * (∑ p ∈ Submission.BoseGases.pairSet N, w (x p.1) (x p.2)))) (MeasureTheory.volume.restrict (Submission.BoseGases.abox N ℓ))
    exact hfsm.congr hpt.symm
  calc
    Submission.BoseGases.qLHSword (N := N) ℓ μ w w1 Φ = ∫ x in Submission.BoseGases.abox N ℓ, (Φ x) ^ 2 * (- μ * (∑ i : Fin N, Submission.BoseGases.w1Fibre ℓ w1 (x i))
        + (1 / 2) * (∑ p ∈ Submission.BoseGases.pairSet N, w (x p.1) (x p.2))) := by
          rfl
    _ = (∫ x in Submission.BoseGases.abox N ℓ, (Φ x) ^ 2 * (- μ * (∑ i : Fin N, Submission.BoseGases.w1Fibre ℓ w1 (x i))))
        + (∫ x in Submission.BoseGases.abox N ℓ, (Φ x) ^ 2 * ((1 / 2) * (∑ p ∈ Submission.BoseGases.pairSet N, w (x p.1) (x p.2)))) := by
            rw [← MeasureTheory.integral_add hint1 hint2]
            apply MeasureTheory.integral_congr_ae
            filter_upwards with x
            ring
    _ = - μ * (∑ i : Fin N, Submission.BoseGases.muPhi ℓ w1 Φ i)
        + (1 / 2) * (∑ p ∈ Submission.BoseGases.pairSet N, ∫ x in Submission.BoseGases.abox N ℓ, (Φ x) ^ 2 * w (x p.1) (x p.2)) := by
          rw [hmu, hpair]

end Work.BoseBoxFock
