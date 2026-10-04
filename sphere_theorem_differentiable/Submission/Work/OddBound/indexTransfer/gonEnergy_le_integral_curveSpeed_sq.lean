import Mathlib
import Submission.Work.OddBound.indexTransfer.Infra
import Submission.Work.OddBound.piecewiseDist
import Submission.Work.OddBound.indexTransfer.intervalIntegrable_curveSpeed_sq
import Submission.Work.OddBound.indexTransfer.gonEnergy_eq_sum_riemannianDist
import Submission.Work.OddBound.indexTransfer.sum_fin_integral_chain_partition
import Submission.Work.OddBound.indexTransfer.sq_intervalIntegral_curveSpeed_le

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.OddBound.indexTransfer

open scoped Manifold ContDiff Bundle Topology ENNReal
open Bundle ContDiff Set MeasureTheory

/-!
# The energy of the inscribed polygon of a loop is bounded by the energy of the loop

For a closed curve `Φ : ℝ → M` of class `C¹` on `[0,T]` (`Φ 0 = Φ T = p`) and any `N > 0`, the
polygon energy of the inscribed `N`-gon through the equally spaced points `Φ (i * T / N)`,
`i = 0, …, N`, is bounded by `T/2` times the energy `∫_0^T ‖Φ'‖²` of the curve:

`gonEnergy p (Φ (· * T / N)) ≤ T/2 * ∫_0^T curveSpeed Φ s ^ 2 ds`.

The proof is the classical one, per side `i`:
* `d(Φ tᵢ, Φ tᵢ₊₁) ≤ ∫_{tᵢ}^{tᵢ₊₁} curveSpeed Φ` (distance ≤ length, `piecewiseDist`);
* Cauchy–Schwarz `(∫_{tᵢ}^{tᵢ₊₁} speed)² ≤ (tᵢ₊₁ - tᵢ) ∫_{tᵢ}^{tᵢ₊₁} speed²` with
  `tᵢ₊₁ - tᵢ = T/N`;
summing over the `N` equal sides and telescoping the integrals
(`sum_fin_integral_chain_partition`) gives `∑ d² ≤ (T/N) ∫_0^T speed²`, and multiplying by `N/2`
yields the claim.
-/

theorem gonEnergy_le_integral_curveSpeed_sq
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M]
    [IsManifold I ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    [Bundle.RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I ((⊤ : ℕ∞) : WithTop ℕ∞) E (fun x : M ↦ TangentSpace I x)]
    [I.Boundaryless] [Nontrivial E] [CompactSpace M] [PathConnectedSpace M] [RegularSpace M]
    {Φ : ℝ → M} {T : ℝ} (hT : 0 < T) {p : M}
    (h0 : Φ 0 = p) (hTp : Φ T = p)
    (hΦ : ContMDiffOn (modelWithCornersSelf ℝ ℝ) I 1 Φ (Set.Icc (0 : ℝ) T)) {N : ℕ}
    (hN : 0 < N) :
    Work.OddBound.gonEnergy (I := I) p
        (fun i : Fin (N - 1) => Φ ((((i : ℕ) : ℝ) + 1) * T / N))
      ≤ T / 2 * intervalIntegral (fun s : ℝ => (Submission.Length.curveSpeed (I := I) Φ s) ^ 2)
          (0 : ℝ) T MeasureTheory.volume := by
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  -- the partition points
  have hleft : ∀ i : Fin N, (0 : ℝ) ≤ (i : ℝ) * T / N := by
    intro i
    exact div_nonneg (mul_nonneg (Nat.cast_nonneg _) hT.le) hNpos.le
  have hmono : ∀ i : Fin N, (i : ℝ) * T / N ≤ ((i : ℝ) + 1) * T / N := by
    intro i
    apply div_le_div_of_nonneg_right _ hNpos.le
    nlinarith [hT]
  have hright : ∀ i : Fin N, ((i : ℝ) + 1) * T / N ≤ T := by
    intro i
    have hi1 : (i : ℝ) + 1 ≤ (N : ℝ) := by
      have h : (((i : ℕ) + 1 : ℕ) : ℝ) ≤ ((N : ℕ) : ℝ) := by
        exact_mod_cast Nat.succ_le_of_lt i.isLt
      simpa [Nat.cast_add, Nat.cast_one] using h
    rw [div_le_iff₀ hNpos]
    calc ((i : ℝ) + 1) * T ≤ (N : ℝ) * T := mul_le_mul_of_nonneg_right hi1 hT.le
      _ = T * N := by ring
  -- the Cauchy-Schwarz bound on each side
  have hkey : ∀ i : Fin N,
      (Submission.Distance.riemannianDist (I := I) (Φ ((i : ℝ) * T / N))
          (Φ (((i : ℝ) + 1) * T / N))) ^ 2
        ≤ (T / N) * ∫ s in ((i : ℝ) * T / N)..(((i : ℝ) + 1) * T / N),
            (Submission.Length.curveSpeed (I := I) Φ s) ^ 2 := by
    intro i
    have hdist := Work.OddBound.piecewiseDist.dist_le_curveLength_of_contMDiffOn_Icc
      (I := I) (h := Φ) (α := 0) (β := T) (c := (i : ℝ) * T / N)
      (d := ((i : ℝ) + 1) * T / N) hT.le hΦ (hleft i) (hmono i) (hright i)
    rw [Submission.Length.curveLength_def] at hdist
    have hcs := sq_intervalIntegral_curveSpeed_le (I := I) (γ := Φ) (S := T) hΦ
      (hleft i) (hmono i) (hright i)
    have hsub : ((i : ℝ) + 1) * T / N - (i : ℝ) * T / N = T / N := by
      rw [← sub_div]
      congr 1
      ring
    calc (Submission.Distance.riemannianDist (I := I) (Φ ((i : ℝ) * T / N))
            (Φ (((i : ℝ) + 1) * T / N))) ^ 2
        ≤ (∫ s in ((i : ℝ) * T / N)..(((i : ℝ) + 1) * T / N),
            Submission.Length.curveSpeed (I := I) Φ s) ^ 2 :=
          pow_le_pow_left₀ (Submission.Distance.riemannianDist_nonneg _ _) hdist 2
      _ ≤ (((i : ℝ) + 1) * T / N - (i : ℝ) * T / N) *
            ∫ s in ((i : ℝ) * T / N)..(((i : ℝ) + 1) * T / N),
              (Submission.Length.curveSpeed (I := I) Φ s) ^ 2 := hcs
      _ = (T / N) * ∫ s in ((i : ℝ) * T / N)..(((i : ℝ) + 1) * T / N),
              (Submission.Length.curveSpeed (I := I) Φ s) ^ 2 := by rw [hsub]
  -- sum the bounds
  have hsum : (∑ i : Fin N,
      (Submission.Distance.riemannianDist (I := I) (Φ ((i : ℝ) * T / N))
          (Φ (((i : ℝ) + 1) * T / N))) ^ 2)
      ≤ (T / N) * ∫ s in (0 : ℝ)..T, (Submission.Length.curveSpeed (I := I) Φ s) ^ 2 := by
    calc (∑ i : Fin N,
        (Submission.Distance.riemannianDist (I := I) (Φ ((i : ℝ) * T / N))
            (Φ (((i : ℝ) + 1) * T / N))) ^ 2)
        ≤ ∑ i : Fin N, (T / N) * ∫ s in ((i : ℝ) * T / N)..(((i : ℝ) + 1) * T / N),
            (Submission.Length.curveSpeed (I := I) Φ s) ^ 2 :=
          Finset.sum_le_sum (fun i _ => hkey i)
      _ = (T / N) * ∑ i : Fin N, ∫ s in ((i : ℝ) * T / N)..(((i : ℝ) + 1) * T / N),
            (Submission.Length.curveSpeed (I := I) Φ s) ^ 2 := by rw [Finset.mul_sum]
      _ = (T / N) * ∫ s in (0 : ℝ)..T, (Submission.Length.curveSpeed (I := I) Φ s) ^ 2 := by
          congr 1
          exact sum_fin_integral_chain_partition (fun s : ℝ =>
              (Submission.Length.curveSpeed (I := I) Φ s) ^ 2) hN
            (fun i => intervalIntegrable_curveSpeed_sq (I := I) (γ := Φ) (S := T) hΦ
              (hleft i) (hmono i) (hright i))
  rw [gonEnergy_eq_sum_riemannianDist (I := I) hT h0 hTp hN]
  have hmul : (N : ℝ) / 2 * (T / N) = T / 2 := by
    field_simp
  calc (N : ℝ) / 2 * (∑ i : Fin N,
        (Submission.Distance.riemannianDist (I := I) (Φ ((i : ℝ) * T / N))
            (Φ (((i : ℝ) + 1) * T / N))) ^ 2)
      ≤ (N : ℝ) / 2 * ((T / N) *
          ∫ s in (0 : ℝ)..T, (Submission.Length.curveSpeed (I := I) Φ s) ^ 2) :=
        mul_le_mul_of_nonneg_left hsum (div_nonneg (Nat.cast_nonneg N) (by norm_num))
    _ = T / 2 * ∫ s in (0 : ℝ)..T, (Submission.Length.curveSpeed (I := I) Φ s) ^ 2 := by
        rw [← mul_assoc, hmul]

end Work.OddBound.indexTransfer
