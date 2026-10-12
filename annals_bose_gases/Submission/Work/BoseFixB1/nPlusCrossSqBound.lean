import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixB1.fSqMul_le
import Submission.Work.BoseFixB1.sqSumInt_le
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB1.nPlusCrossSqBound`

The `Q`-side second-moment bound

`∑ᵢ ∫_{Λᴺ}  (∑_k Q_k (Q_i Φ)(x))² · f(x_i)  ≤  B·N²·n₊(Φ)`

used in the B1 (a-priori) chain to dominate the crossed `P·Q·Q` inner product
by `√(P²-mass)·√(Q²-mass)` (see `_cw_dev.lean`, `nPlusCrossSqBound` at `B = Kfib`).

The proof is a three-step `L²` estimate:

* **Slot reduction** (`fSqMul_le`): since `f ≥ −B` and the square is nonnegative,
  `∫ (∑_k Q_k(Q_iΦ))²·f(x_i) ≤ B ∫ (∑_k Q_k(Q_iΦ))²`;
* **Cauchy–Schwarz** (`sqSumInt_le`): for each fixed `x`,
  `(∑_k a_k)² ≤ N ∑_k a_k²`, hence
  `∫ (∑_k Q_k(Q_iΦ))² ≤ N ∑_k ∫ (Q_k(Q_iΦ))²`;
* **Contraction** (`aQ_sq_le`, the orthogonal-projection algebra
  `∫(Q_kΨ)² = ∫Ψ² − ∫(P_kΨ)²`): each `∫ (Q_k(Q_iΦ))² ≤ ∫ (Q_iΦ)²`, so
  `N ∑_k ∫ (Q_k(Q_iΦ))² ≤ N² ∫ (Q_iΦ)²`.

Summing over `i` and recognising `n₊(Φ) = ∑_i ∫ (Q_iΦ)²` gives the claim.
-/

namespace Work.BoseFixB1

open MeasureTheory

/-- Contraction of the complement projection `Qᵢ` in `L²(Λᴺ)`: subtracting the
mean over `Λ` in coordinate `i` never increases the `L²` norm.  This is the
orthogonality algebra `∫(Q_iΨ)² = ∫Ψ² − ∫(P_iΨ)²` of `sq_norm_decomp`. -/
theorem aQ_sq_le {N : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) (k : Fin N)
    {ψ : Submission.BoseGases.X N → ℝ} (hψc : Continuous ψ) :
    (∫ x in Submission.BoseGases.abox N ℓ, (Submission.BoseGases.aQ ℓ k ψ x) ^ 2)
      ≤ (∫ x in Submission.BoseGases.abox N ℓ, (ψ x) ^ 2) := by
  have h := Submission.BoseGases.sq_norm_decomp hℓ k hψc
  have hP : 0 ≤ ∫ x in Submission.BoseGases.abox N ℓ, (Submission.BoseGases.aP ℓ k ψ x) ^ 2 :=
    MeasureTheory.integral_nonneg (fun x => sq_nonneg _)
  linarith

theorem nPlusCrossSqBound {N : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ)
    {Φ : Submission.BoseGases.X N → ℝ} (hΦc : Continuous Φ)
    {f : EuclideanSpace ℝ (Fin 3) → ℝ} {B : ℝ} (hB0 : 0 ≤ B)
    (hfm : MeasureTheory.AEStronglyMeasurable f
      (MeasureTheory.volume.restrict (Submission.BoseGases.acube ℓ)))
    (hfb : ∀ z, |f z| ≤ B) :
    (∑ i : Fin N, ∫ x in Submission.BoseGases.abox N ℓ,
        (∑ k : Fin N, Submission.BoseGases.aQ ℓ k (Submission.BoseGases.aQ ℓ i Φ) x) ^ 2
          * f (x i))
      ≤ B * (N : ℝ) ^ 2 * Submission.BoseGases.cnPlus ℓ Φ := by
  -- Per-slot bound: the `i`-th summand is at most `B·N²·∫(QᵢΦ)²`.
  have hslot : ∀ i : Fin N,
      (∫ x in Submission.BoseGases.abox N ℓ,
        (∑ k : Fin N, Submission.BoseGases.aQ ℓ k (Submission.BoseGases.aQ ℓ i Φ) x) ^ 2 * f (x i))
        ≤ B * (N : ℝ) ^ 2
          * (∫ x in Submission.BoseGases.abox N ℓ, (Submission.BoseGases.aQ ℓ i Φ x) ^ 2) := by
    intro i
    have hθc : Continuous (Submission.BoseGases.aQ ℓ i Φ) :=
      Submission.BoseGases.aQ_continuous hℓ i hΦc
    have hGc : Continuous (fun x : Submission.BoseGases.X N =>
        ∑ k : Fin N, Submission.BoseGases.aQ ℓ k (Submission.BoseGases.aQ ℓ i Φ) x) :=
      continuous_finsetSum _ (fun k _ => Submission.BoseGases.aQ_continuous hℓ k hθc)
    -- slot reduction
    have h1 := fSqMul_le (N := N) (ℓ := ℓ) hℓ
      (g := fun x : Submission.BoseGases.X N =>
        ∑ k : Fin N, Submission.BoseGases.aQ ℓ k (Submission.BoseGases.aQ ℓ i Φ) x)
      hGc hB0 hfm hfb i
    -- Cauchy–Schwarz
    have h2 := sqSumInt_le (N := N) (ℓ := ℓ) hℓ
      (g := fun k : Fin N => Submission.BoseGases.aQ ℓ k (Submission.BoseGases.aQ ℓ i Φ))
      (fun k => Submission.BoseGases.aQ_continuous hℓ k hθc)
    -- contraction, summed over `k`
    have h3 : (∑ k : Fin N, ∫ x in Submission.BoseGases.abox N ℓ,
          (Submission.BoseGases.aQ ℓ k (Submission.BoseGases.aQ ℓ i Φ) x) ^ 2)
        ≤ (N : ℝ) * (∫ x in Submission.BoseGases.abox N ℓ, (Submission.BoseGases.aQ ℓ i Φ x) ^ 2) := by
      calc (∑ k : Fin N, ∫ x in Submission.BoseGases.abox N ℓ,
              (Submission.BoseGases.aQ ℓ k (Submission.BoseGases.aQ ℓ i Φ) x) ^ 2)
          ≤ ∑ k : Fin N, ∫ x in Submission.BoseGases.abox N ℓ,
              (Submission.BoseGases.aQ ℓ i Φ x) ^ 2 :=
            Finset.sum_le_sum (fun k _ => aQ_sq_le hℓ k hθc)
        _ = (N : ℝ)
              * (∫ x in Submission.BoseGases.abox N ℓ, (Submission.BoseGases.aQ ℓ i Φ x) ^ 2) := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
            simp [nsmul_eq_mul]
    calc (∫ x in Submission.BoseGases.abox N ℓ,
            (∑ k : Fin N, Submission.BoseGases.aQ ℓ k (Submission.BoseGases.aQ ℓ i Φ) x) ^ 2 * f (x i))
        ≤ B * (∫ x in Submission.BoseGases.abox N ℓ,
            (∑ k : Fin N, Submission.BoseGases.aQ ℓ k (Submission.BoseGases.aQ ℓ i Φ) x) ^ 2) := h1
      _ ≤ B * ((N : ℝ) * (∑ k : Fin N, ∫ x in Submission.BoseGases.abox N ℓ,
            (Submission.BoseGases.aQ ℓ k (Submission.BoseGases.aQ ℓ i Φ) x) ^ 2)) :=
            mul_le_mul_of_nonneg_left h2 hB0
      _ ≤ B * ((N : ℝ) * ((N : ℝ)
            * (∫ x in Submission.BoseGases.abox N ℓ, (Submission.BoseGases.aQ ℓ i Φ x) ^ 2))) := by
            apply mul_le_mul_of_nonneg_left _ hB0
            exact mul_le_mul_of_nonneg_left h3 (Nat.cast_nonneg N)
      _ = B * (N : ℝ) ^ 2
            * (∫ x in Submission.BoseGases.abox N ℓ, (Submission.BoseGases.aQ ℓ i Φ x) ^ 2) := by
            ring
  -- Sum the per-slot bounds over the `N` slots and recognise `cnPlus`.
  calc (∑ i : Fin N, ∫ x in Submission.BoseGases.abox N ℓ,
          (∑ k : Fin N, Submission.BoseGases.aQ ℓ k (Submission.BoseGases.aQ ℓ i Φ) x) ^ 2 * f (x i))
      ≤ ∑ i : Fin N, B * (N : ℝ) ^ 2
          * (∫ x in Submission.BoseGases.abox N ℓ, (Submission.BoseGases.aQ ℓ i Φ x) ^ 2) :=
          Finset.sum_le_sum (fun i _ => hslot i)
    _ = B * (N : ℝ) ^ 2
          * (∑ i : Fin N, ∫ x in Submission.BoseGases.abox N ℓ, (Submission.BoseGases.aQ ℓ i Φ x) ^ 2) := by
          rw [Finset.mul_sum]
    _ = B * (N : ℝ) ^ 2 * Submission.BoseGases.cnPlus ℓ Φ := rfl

end Work.BoseFixB1
