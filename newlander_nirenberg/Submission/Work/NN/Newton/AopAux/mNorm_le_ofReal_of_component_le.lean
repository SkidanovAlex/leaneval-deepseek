import Mathlib
import Submission.Work.NN.Newton.pushforward_norms

open scoped ENNReal

namespace Work.NN.Newton.AopAux

/-- Componentwise bound on `mNorm`: if every component family that enters the
bookkeeping norm `mNorm 1 α T Ω` is bounded by `K` in the `C^{1,α}`-norm on `Ω`,
then `mNorm 1 α T Ω ≤ 4 n² K`.

There are `n` components for each of the four families
`(T z e_j)`, `(T z (i e_j))`, `linCoef (T z) p`, `antiCoef (T z) p`, each with `n`
coordinates, and `vNorm` is a sum over the `n` coordinates; this gives the factor
`4 n · n`. -/
theorem mNorm_le_ofReal_of_component_le {n : ℕ} {α K : ℝ} (hK : 0 ≤ K)
    {Ω : Set (Work.NN.Core.Cn n)}
    {T : Work.NN.Core.Cn n → Work.NN.Core.Cn n →L[ℝ] Work.NN.Core.Cn n}
    (h1 : ∀ j l : Fin n, Work.CR.Flat.holderNorm 1 α (fun z => (T z (Pi.single j 1)) l) Ω
      ≤ ENNReal.ofReal K)
    (h2 : ∀ j l : Fin n, Work.CR.Flat.holderNorm 1 α
      (fun z => (T z (Pi.single j (Complex.I : ℂ))) l) Ω ≤ ENNReal.ofReal K)
    (h3 : ∀ p l : Fin n, Work.CR.Flat.holderNorm 1 α
      (fun z => (Work.NN.Newton.linCoef (T z) p) l) Ω ≤ ENNReal.ofReal K)
    (h4 : ∀ p l : Fin n, Work.CR.Flat.holderNorm 1 α
      (fun z => (Work.NN.Newton.antiCoef (T z) p) l) Ω ≤ ENNReal.ofReal K) :
    Work.NN.Newton.mNorm 1 α T Ω ≤ ENNReal.ofReal (4 * (n : ℝ) * (n : ℝ) * K) := by
  -- Each single `vNorm` is the sum of `n` `holderNorm`s, hence at most `n * ofReal K`.
  have hvn : ∀ F : Work.NN.Core.Cn n → Work.NN.Core.Cn n,
      (∀ l : Fin n, Work.CR.Flat.holderNorm 1 α (fun z => F z l) Ω ≤ ENNReal.ofReal K) →
      Work.NN.Newton.vNorm 1 α F Ω ≤ (n : ℝ≥0∞) * ENNReal.ofReal K := by
    intro F hF
    unfold Work.NN.Newton.vNorm
    calc (∑ l, Work.CR.Flat.holderNorm 1 α (fun z => F z l) Ω)
        ≤ ∑ _l : Fin n, ENNReal.ofReal K := Finset.sum_le_sum fun l _ => hF l
      _ = (n : ℝ≥0∞) * ENNReal.ofReal K := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hA : ∀ j : Fin n, Work.NN.Newton.vNorm 1 α (fun z => T z (Pi.single j 1)) Ω
      ≤ (n : ℝ≥0∞) * ENNReal.ofReal K := fun j => hvn _ (fun l => h1 j l)
  have hB : ∀ j : Fin n, Work.NN.Newton.vNorm 1 α
      (fun z => T z (Pi.single j (Complex.I : ℂ))) Ω
      ≤ (n : ℝ≥0∞) * ENNReal.ofReal K := fun j => hvn _ (fun l => h2 j l)
  have hC : ∀ p : Fin n, Work.NN.Newton.vNorm 1 α
      (fun z => Work.NN.Newton.linCoef (T z) p) Ω
      ≤ (n : ℝ≥0∞) * ENNReal.ofReal K := fun p => hvn _ (fun l => h3 p l)
  have hD : ∀ p : Fin n, Work.NN.Newton.vNorm 1 α
      (fun z => Work.NN.Newton.antiCoef (T z) p) Ω
      ≤ (n : ℝ≥0∞) * ENNReal.ofReal K := fun p => hvn _ (fun l => h4 p l)
  -- Summing over the `n` components of each family.
  have hsumA : (∑ j, Work.NN.Newton.vNorm 1 α (fun z => T z (Pi.single j 1)) Ω)
      ≤ (n : ℝ≥0∞) * ((n : ℝ≥0∞) * ENNReal.ofReal K) := by
    calc (∑ j, Work.NN.Newton.vNorm 1 α (fun z => T z (Pi.single j 1)) Ω)
        ≤ ∑ _j : Fin n, (n : ℝ≥0∞) * ENNReal.ofReal K := Finset.sum_le_sum fun j _ => hA j
      _ = (n : ℝ≥0∞) * ((n : ℝ≥0∞) * ENNReal.ofReal K) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hsumB : (∑ j, Work.NN.Newton.vNorm 1 α
        (fun z => T z (Pi.single j (Complex.I : ℂ))) Ω)
      ≤ (n : ℝ≥0∞) * ((n : ℝ≥0∞) * ENNReal.ofReal K) := by
    calc (∑ j, Work.NN.Newton.vNorm 1 α (fun z => T z (Pi.single j (Complex.I : ℂ))) Ω)
        ≤ ∑ _j : Fin n, (n : ℝ≥0∞) * ENNReal.ofReal K := Finset.sum_le_sum fun j _ => hB j
      _ = (n : ℝ≥0∞) * ((n : ℝ≥0∞) * ENNReal.ofReal K) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hsumCD : (∑ p, (Work.NN.Newton.vNorm 1 α
        (fun z => Work.NN.Newton.linCoef (T z) p) Ω
        + Work.NN.Newton.vNorm 1 α (fun z => Work.NN.Newton.antiCoef (T z) p) Ω))
      ≤ (n : ℝ≥0∞) * (2 * ((n : ℝ≥0∞) * ENNReal.ofReal K)) := by
    calc (∑ p, (Work.NN.Newton.vNorm 1 α (fun z => Work.NN.Newton.linCoef (T z) p) Ω
          + Work.NN.Newton.vNorm 1 α (fun z => Work.NN.Newton.antiCoef (T z) p) Ω))
        ≤ ∑ _p : Fin n, (2 * ((n : ℝ≥0∞) * ENNReal.ofReal K)) := by
            refine Finset.sum_le_sum fun p _ => ?_
            rw [two_mul]
            exact add_le_add (hC p) (hD p)
      _ = (n : ℝ≥0∞) * (2 * ((n : ℝ≥0∞) * ENNReal.ofReal K)) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  -- The numeric core: `4 · n² · ofReal K = ofReal (4 n² K)`.
  have hmain : (4 : ℝ≥0∞) * ((n : ℝ≥0∞) * ((n : ℝ≥0∞) * ENNReal.ofReal K))
      = ENNReal.ofReal (4 * (n : ℝ) * (n : ℝ) * K) := by
    rw [← ENNReal.ofReal_ofNat 4, ← ENNReal.ofReal_natCast n,
      ← ENNReal.ofReal_mul (Nat.cast_nonneg n),
      ← ENNReal.ofReal_mul (Nat.cast_nonneg n),
      ← ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 4)]
    congr 1
    ring
  unfold Work.NN.Newton.mNorm
  refine le_trans (add_le_add (add_le_add hsumA hsumB) hsumCD) (le_of_eq ?_)
  rw [show (n : ℝ≥0∞) * ((n : ℝ≥0∞) * ENNReal.ofReal K)
        + (n : ℝ≥0∞) * ((n : ℝ≥0∞) * ENNReal.ofReal K)
        + (n : ℝ≥0∞) * (2 * ((n : ℝ≥0∞) * ENNReal.ofReal K))
      = (4 : ℝ≥0∞) * ((n : ℝ≥0∞) * ((n : ℝ≥0∞) * ENNReal.ofReal K)) from by ring]
  exact hmain

end Work.NN.Newton.AopAux
