import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBoxFock.block3Row1_expanded
import Submission.Work.BoseBoxFock.block3Row2_expanded
import Submission.Work.BoseBoxFock.pinQ_etaOf
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseBoxFock

theorem potPairRows_kernelExpanded {n : ℕ} {v : EuclideanSpace ℝ (Fin 3) → ℝ} {μ : ℝ}
    (HM : Work.BoseBoxFock.HonestModes v μ)
    {e : Fin HM.m → EuclideanSpace ℝ (Fin 3) → ℂ}
    (hmeas : ∀ l, Measurable (e l))
    (hbdd : ∀ l, ∃ C : ℝ, ∀ x, ‖e l x‖ ≤ C)
    (hsupp : ∀ l, Function.support (e l) ⊆ Work.BoseK15.corpusBox.boxL (Work.BoseBoxFock.ellH v μ))
    (horth : ∀ l l', (∫ z : EuclideanSpace ℝ (Fin 3), star (e l z) * e l' z)
      = (if l = l' then (1 : ℂ) else 0))
    (hMemLp : ∀ l, MeasureTheory.MemLp (e l) ⊤)
    (c : ℂ) (hpin0 : e 0 =ᵐ[MeasureTheory.volume] Work.BoseBoxFock.pinCond v μ c)
    (hpairF : ∀ (k : Work.BoseBoxFock.Lab HM.N) (l : Fin HM.m),
      (∫ z : EuclideanSpace ℝ (Fin 3), star (e l z) *
          Work.BoseK15.corpusBox.qVec (Work.BoseBoxFock.ellH v μ)
            (Work.BoseBoxFock.kmomLab (Work.BoseBoxFock.ellH v μ) HM.N k) z)
        = (((Work.BoseBoxFock.ellH v μ) ^ (3 / 2 : ℝ) * HM.f k l : ℝ) : ℂ))
    (E : Work.BoseB7.Q3Env (Work.BoseBoxFock.Lab HM.N))
    (Theta : Work.BoseDict.Xn n → ℂ) (hΘm : Measurable Theta)
    (hΘb : ∃ C : ℝ, ∀ x, ‖Theta x‖ ≤ C)
    (hΘs : Function.support Theta ⊆ Work.MB.boxPow n (Work.BoseBoxFock.ellH v μ)) :
    Work.BoseDict.cIPn n Theta
        (Work.BoseBoxFock.potPairRows (fun T => Work.BoseDict.boxSlotSum e T) HM.f E Theta)
      = (E.ell ^ (-(3 : ℝ))) •
          (∑ p ∈ Submission.BoseGases.pairSet n,
            ∫ x : Work.BoseDict.Xn n, ∫ y : EuclideanSpace ℝ (Fin 3),
              ∫ u : EuclideanSpace ℝ (Fin 3),
              (starRingEnd ℂ) (Theta x) * Work.BoseBoxFock.pinCond v μ c (x p.1)
                * Work.BoseBoxFock.K1exp v μ HM.N
                    (fun k : Work.BoseBoxFock.Lab HM.N => E.W1 k + E.W1omega k) (x p.2) y
                * (starRingEnd ℂ) (Work.BoseBoxFock.pinCond v μ c u)
                * Theta (Function.update (Function.update x p.1 y) p.2 u))
        + ((1 / 2 : ℝ) * E.ell ^ (-(3 : ℝ))) •
          ((∑ p ∈ Submission.BoseGases.pairSet n,
              ∫ x : Work.BoseDict.Xn n, ∫ y : EuclideanSpace ℝ (Fin 3),
                ∫ u : EuclideanSpace ℝ (Fin 3),
                (starRingEnd ℂ) (Theta x) * Work.BoseBoxFock.pinCond v μ c (x p.1)
                  * Work.BoseBoxFock.pinCond v μ c (x p.2)
                  * Work.BoseBoxFock.K1exp v μ HM.N E.W1 u y
                  * Theta (Function.update (Function.update x p.1 y) p.2 u))
            + (∑ p ∈ Submission.BoseGases.pairSet n,
              ∫ x : Work.BoseDict.Xn n, ∫ y : EuclideanSpace ℝ (Fin 3),
                ∫ u : EuclideanSpace ℝ (Fin 3),
                (starRingEnd ℂ) (Theta x)
                  * Work.BoseBoxFock.K1exp v μ HM.N E.W1 (x p.1) (x p.2)
                  * (starRingEnd ℂ) (Work.BoseBoxFock.pinCond v μ c y)
                  * (starRingEnd ℂ) (Work.BoseBoxFock.pinCond v μ c u)
                  * Theta (Function.update (Function.update x p.1 y) p.2 u)))
        + ((E.ell ^ (-(3 : ℝ)) * E.W1 0 + E.ell ^ (-(3 : ℝ)) * E.W1omega0) •
              (∑ p ∈ Submission.BoseGases.pairSet n,
                ∫ x : Work.BoseDict.Xn n, ∫ y : EuclideanSpace ℝ (Fin 3),
                  ∫ u : EuclideanSpace ℝ (Fin 3),
                  (starRingEnd ℂ) (Theta x) * Work.BoseBoxFock.pinCond v μ c (x p.1)
                    * (starRingEnd ℂ) (Work.BoseBoxFock.pinCond v μ c y)
                    * Work.BoseBoxFock.K1exp v μ HM.N
                        (fun _ : Work.BoseBoxFock.Lab HM.N => (1 : ℝ)) (x p.2) u
                    * Theta (Function.update (Function.update x p.1 y) p.2 u))
            - (E.mu * E.W1 0) •
              (∑ j : Fin n,
                ∫ x : Work.BoseDict.Xn n, ∫ y : EuclideanSpace ℝ (Fin 3),
                  (starRingEnd ℂ) (Theta x)
                    * Work.BoseBoxFock.K1exp v μ HM.N
                        (fun _ : Work.BoseBoxFock.Lab HM.N => (1 : ℝ)) (x j) y
                    * Theta (Function.update x j y))) := by
  classical
  -- The row in **kernel form** (`potPairRows_kernelForm`) at the honest pinned data
  -- `Fp k = pinQ v μ HM.N k`, `Th = pinCond v μ c`.
  have hker := potPairRows_kernelForm (m := HM.m) (n := n) (ℓ := ellH v μ) (Mode := Lab HM.N)
      hmeas hbdd hsupp horth HM.f HM.hf0 E (fun k => pinQ v μ HM.N k) (pinCond v μ c)
      (fun k => pinQ_etaOf HM horth hpairF hMemLp k) (etaOf_evec0_eq_pinCond hpin0)
      Theta hΘm hΘb hΘs
  rw [hker]
  -- The third block carries its mode sum outside the position integrals; it splits, and each of
  -- the two single-mode rows is exchanged with its integral (`block3Row1_expanded`,
  -- `block3Row2_expanded`).
  rw [Finset.sum_sub_distrib]
  rw [block3Row1_expanded (n := n) (N := HM.N) (v := v) (μ := μ) c E Theta hΘm hΘb hΘs,
      block3Row2_expanded (n := n) (N := HM.N) (v := v) (μ := μ) E Theta hΘm hΘb hΘs]
  -- The first two blocks already carry the `pinQ`-kernel in their integrands; the three
  -- pointwise expansions at `pinQ(-k) = conj ∘ pinQ k` turn it into `K1exp`.
  simp only [sum_W1_add_W1omega_kernel, sum_W1_conj_neg, sum_W1_pinQ_neg]

end Work.BoseBoxFock
