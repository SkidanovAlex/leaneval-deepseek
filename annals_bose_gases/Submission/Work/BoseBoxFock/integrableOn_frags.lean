import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.PotWords
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseBoxFock

/-- Pointwise decomposition of the `Q4` pair-summand integrand `fg4`, based only on the
two kernel relations `ω·w = w − w1` (`hw1rel`) and `ω²·w = w − w2` (`hw2rel`).

Writing `D := aQ j (aQ i Φ)`, `U := aP j (aP i Φ) + aP j (aQ i Φ) + aQ j (aP i Φ)` and
`ω := om (x i) (x j)`, one has `q4B = D + ω·U`, so

`fg4 = ½·(D + ω·U)²·w = ½·D²·w + (D·U)·(w − w1) + ½·U²·(w − w2)`

(the two `ω`-weighted terms in the square are absorbed by `ω·w = w − w1` and
`ω²·w = w − w2`).  This is the algebraic identity behind the integrability of `fg4`. -/
lemma fg4_pointwise_decomp {N : ℕ} {ℓ : ℝ}
    {w w1 w2 om : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) → ℝ}
    (hw1rel : ∀ x y, w1 x y = w x y * (1 - om x y))
    (hw2rel : ∀ x y, w2 x y = w x y * (1 - om x y ^ 2))
    {Φ : Submission.BoseGases.X N → ℝ} {i j : Fin N} (x : Submission.BoseGases.X N) :
    Submission.BoseGases.fg4 ℓ w om Φ i j x =
      (1 / 2) * (Submission.BoseGases.aQ ℓ j (Submission.BoseGases.aQ ℓ i Φ) x) ^ 2 * w (x i) (x j)
      + ((Submission.BoseGases.aQ ℓ j (Submission.BoseGases.aQ ℓ i Φ) x) *
          (Submission.BoseGases.aP ℓ j (Submission.BoseGases.aP ℓ i Φ) x
            + Submission.BoseGases.aP ℓ j (Submission.BoseGases.aQ ℓ i Φ) x
            + Submission.BoseGases.aQ ℓ j (Submission.BoseGases.aP ℓ i Φ) x))
        * (w (x i) (x j) - w1 (x i) (x j))
      + (1 / 2) * (Submission.BoseGases.aP ℓ j (Submission.BoseGases.aP ℓ i Φ) x
            + Submission.BoseGases.aP ℓ j (Submission.BoseGases.aQ ℓ i Φ) x
            + Submission.BoseGases.aQ ℓ j (Submission.BoseGases.aP ℓ i Φ) x) ^ 2
        * (w (x i) (x j) - w2 (x i) (x j)) := by
  simp only [Submission.BoseGases.fg4, Submission.BoseGases.q4B]
  rw [hw1rel (x i) (x j), hw2rel (x i) (x j)]
  ring

/-- Integrability of the seven per-pair word-fragment integrands `fg0 … fg4` (the `pairSet`-summands of `q0word`–`q4word` at the ordered pair `(i,j)`) over the centred box `abox N ℓ`, given only that the three kernels `w, w1, w2` at `(i,j)` are integrable there (no continuity of the kernels).  Route: `fg0`–`fg3` are a *continuous* coefficient times an integrable kernel (`MeasureTheory.IntegrableOn.continuousOn_mul` together with `Submission.BoseGases.abox_compact`); `fg4 = ½·(q4B)²·w` needs the pointwise identity `(q4B)²·w = D²·w + 2·D·U·(w − w1) + U²·(w − w2)` where `q4B = D + ω·U` with `D := aQ j (aQ i Φ)` and `U := aP j (aP i Φ) + aP j (aQ i Φ) + aQ j (aP i Φ)`, which follows from the two relations `ω·w = w − w1` and `ω²·w = w − w2` (i.e. `hw1rel`, `hw2rel`); each of the three resulting pieces is a continuous coefficient times an integrable function. -/
theorem integrableOn_frags {N : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ)
    {w w1 w2 om : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) → ℝ}
    (hw1rel : ∀ x y, w1 x y = w x y * (1 - om x y))
    (hw2rel : ∀ x y, w2 x y = w x y * (1 - om x y ^ 2))
    {Φ : Submission.BoseGases.X N → ℝ} (hΦc : Continuous Φ)
    {i j : Fin N} (hij : i ≠ j)
    (hW : MeasureTheory.IntegrableOn (fun x : Submission.BoseGases.X N => w (x i) (x j)) (Submission.BoseGases.abox N ℓ) MeasureTheory.volume)
    (hW1 : MeasureTheory.IntegrableOn (fun x : Submission.BoseGases.X N => w1 (x i) (x j)) (Submission.BoseGases.abox N ℓ) MeasureTheory.volume)
    (hW2 : MeasureTheory.IntegrableOn (fun x : Submission.BoseGases.X N => w2 (x i) (x j)) (Submission.BoseGases.abox N ℓ) MeasureTheory.volume) :
    MeasureTheory.IntegrableOn (fun x : Submission.BoseGases.X N => Submission.BoseGases.fg0 ℓ w2 Φ i j x) (Submission.BoseGases.abox N ℓ) MeasureTheory.volume ∧
      MeasureTheory.IntegrableOn (fun x : Submission.BoseGases.X N => Submission.BoseGases.fg1 ℓ w2 Φ i j x) (Submission.BoseGases.abox N ℓ) MeasureTheory.volume ∧
      MeasureTheory.IntegrableOn (fun x : Submission.BoseGases.X N => Submission.BoseGases.fg2a ℓ w2 Φ i j x) (Submission.BoseGases.abox N ℓ) MeasureTheory.volume ∧
      MeasureTheory.IntegrableOn (fun x : Submission.BoseGases.X N => Submission.BoseGases.fg2b ℓ w2 Φ i j x) (Submission.BoseGases.abox N ℓ) MeasureTheory.volume ∧
      MeasureTheory.IntegrableOn (fun x : Submission.BoseGases.X N => Submission.BoseGases.fg2c ℓ w1 Φ i j x) (Submission.BoseGases.abox N ℓ) MeasureTheory.volume ∧
      MeasureTheory.IntegrableOn (fun x : Submission.BoseGases.X N => Submission.BoseGases.fg3 ℓ w1 Φ i j x) (Submission.BoseGases.abox N ℓ) MeasureTheory.volume ∧
      MeasureTheory.IntegrableOn (fun x : Submission.BoseGases.X N => Submission.BoseGases.fg4 ℓ w om Φ i j x) (Submission.BoseGases.abox N ℓ) MeasureTheory.volume := by
  -- `fg0`–`fg3` are continuous coefficients times the integrable kernels; the box is compact.
  have hK : IsCompact (Submission.BoseGases.abox N ℓ) := Submission.BoseGases.abox_compact N hℓ
  have hPP : Continuous (fun x : Submission.BoseGases.X N => Submission.BoseGases.aP ℓ i (Submission.BoseGases.aP ℓ j Φ) x) :=
    Submission.BoseGases.aP_continuous hℓ i (Submission.BoseGases.aP_continuous hℓ j hΦc)
  have hPQij : Continuous (fun x : Submission.BoseGases.X N => Submission.BoseGases.aP ℓ i (Submission.BoseGases.aQ ℓ j Φ) x) :=
    Submission.BoseGases.aP_continuous hℓ i (Submission.BoseGases.aQ_continuous hℓ j hΦc)
  have hPPji : Continuous (fun x : Submission.BoseGases.X N => Submission.BoseGases.aP ℓ j (Submission.BoseGases.aP ℓ i Φ) x) :=
    Submission.BoseGases.aP_continuous hℓ j (Submission.BoseGases.aP_continuous hℓ i hΦc)
  have hPQji : Continuous (fun x : Submission.BoseGases.X N => Submission.BoseGases.aP ℓ j (Submission.BoseGases.aQ ℓ i Φ) x) :=
    Submission.BoseGases.aP_continuous hℓ j (Submission.BoseGases.aQ_continuous hℓ i hΦc)
  have hQPji : Continuous (fun x : Submission.BoseGases.X N => Submission.BoseGases.aQ ℓ j (Submission.BoseGases.aP ℓ i Φ) x) :=
    Submission.BoseGases.aQ_continuous hℓ j (Submission.BoseGases.aP_continuous hℓ i hΦc)
  have hQQji : Continuous (fun x : Submission.BoseGases.X N => Submission.BoseGases.aQ ℓ j (Submission.BoseGases.aQ ℓ i Φ) x) :=
    Submission.BoseGases.aQ_continuous hℓ j (Submission.BoseGases.aQ_continuous hℓ i hΦc)
  have h0 : Continuous (fun x : Submission.BoseGases.X N => (1 / 2) * (Submission.BoseGases.aP ℓ i (Submission.BoseGases.aP ℓ j Φ) x) ^ 2) := by fun_prop
  have h1 : Continuous (fun x : Submission.BoseGases.X N => 2 * (Submission.BoseGases.aP ℓ i (Submission.BoseGases.aQ ℓ j Φ) x) * (Submission.BoseGases.aP ℓ i (Submission.BoseGases.aP ℓ j Φ) x)) := by fun_prop
  have h2 : Continuous (fun x : Submission.BoseGases.X N => (Submission.BoseGases.aP ℓ i (Submission.BoseGases.aQ ℓ j Φ) x) * (Submission.BoseGases.aP ℓ j (Submission.BoseGases.aQ ℓ i Φ) x)) := by fun_prop
  have h3 : Continuous (fun x : Submission.BoseGases.X N => (Submission.BoseGases.aP ℓ i (Submission.BoseGases.aQ ℓ j Φ) x) * (Submission.BoseGases.aQ ℓ j (Submission.BoseGases.aP ℓ i Φ) x)) := by fun_prop
  have h4 : Continuous (fun x : Submission.BoseGases.X N => (Submission.BoseGases.aP ℓ i (Submission.BoseGases.aP ℓ j Φ) x) * (Submission.BoseGases.aQ ℓ j (Submission.BoseGases.aQ ℓ i Φ) x)) := by fun_prop
  have h5 : Continuous (fun x : Submission.BoseGases.X N => 2 * (Submission.BoseGases.aP ℓ i (Submission.BoseGases.aQ ℓ j Φ) x) * (Submission.BoseGases.aQ ℓ j (Submission.BoseGases.aQ ℓ i Φ) x)) := by fun_prop
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [Submission.BoseGases.fg0] using
      (MeasureTheory.IntegrableOn.continuousOn_mul h0.continuousOn hW2 hK)
  · simpa only [Submission.BoseGases.fg1] using
      (MeasureTheory.IntegrableOn.continuousOn_mul h1.continuousOn hW2 hK)
  · simpa only [Submission.BoseGases.fg2a] using
      (MeasureTheory.IntegrableOn.continuousOn_mul h2.continuousOn hW2 hK)
  · simpa only [Submission.BoseGases.fg2b] using
      (MeasureTheory.IntegrableOn.continuousOn_mul h3.continuousOn hW2 hK)
  · simpa only [Submission.BoseGases.fg2c] using
      (MeasureTheory.IntegrableOn.continuousOn_mul h4.continuousOn hW1 hK)
  · simpa only [Submission.BoseGases.fg3] using
      (MeasureTheory.IntegrableOn.continuousOn_mul h5.continuousOn hW1 hK)
  · -- `fg4 = ½·D²·w + (D·U)·(w − w1) + ½·U²·(w − w2)`, three pieces.
    have hA : Continuous (fun x : Submission.BoseGases.X N =>
        (1 / 2) * (Submission.BoseGases.aQ ℓ j (Submission.BoseGases.aQ ℓ i Φ) x) ^ 2) := by fun_prop
    have hB : Continuous (fun x : Submission.BoseGases.X N =>
        (Submission.BoseGases.aQ ℓ j (Submission.BoseGases.aQ ℓ i Φ) x) *
          (Submission.BoseGases.aP ℓ j (Submission.BoseGases.aP ℓ i Φ) x
            + Submission.BoseGases.aP ℓ j (Submission.BoseGases.aQ ℓ i Φ) x
            + Submission.BoseGases.aQ ℓ j (Submission.BoseGases.aP ℓ i Φ) x)) := by fun_prop
    have hC : Continuous (fun x : Submission.BoseGases.X N =>
        (1 / 2) * (Submission.BoseGases.aP ℓ j (Submission.BoseGases.aP ℓ i Φ) x
            + Submission.BoseGases.aP ℓ j (Submission.BoseGases.aQ ℓ i Φ) x
            + Submission.BoseGases.aQ ℓ j (Submission.BoseGases.aP ℓ i Φ) x) ^ 2) := by fun_prop
    rw [funext (fun x => fg4_pointwise_decomp (ℓ := ℓ) hw1rel hw2rel x)]
    exact ((MeasureTheory.IntegrableOn.continuousOn_mul hA.continuousOn hW hK).add
      (MeasureTheory.IntegrableOn.continuousOn_mul hB.continuousOn (hW.sub hW1) hK)).add
      (MeasureTheory.IntegrableOn.continuousOn_mul hC.continuousOn (hW.sub hW2) hK)

end Work.BoseBoxFock
