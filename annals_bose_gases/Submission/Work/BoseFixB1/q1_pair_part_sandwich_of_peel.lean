import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.Q1Peel
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseFixB1

open MeasureTheory
open scoped BigOperators
open Submission.BoseGases

/-- **Kernel-agnostic q1-pair peel chain** (`depends_on` supplies `Submission.Work.Q1Peel`).

For an *arbitrary* kernel `K`, if the per-pair peel identity (LHS kernel integral ↦ RHS fibre integral, premise `hpeel`) holds for every pair `(i,j)`: `i ≠ j`, and every RHS summand is integrable (premise `hint`), then the total `pairSet` identity holds with the `Σ_{j≠i}P_jΦ` written as an explicit `if`-guarded `Finset` sum.

This is the kernel-general form of `Submission.BoseGases.q1_pair_part_sandwich` (`Submission/Work/Q1Peel.lean`), whose proof uses only Finset bookkeeping (`pairSet_sum_swap_split`, `integral_finsetSum`), the pointwise collapse `q1_n0_collapse` and the two premises — no property of the kernel itself. -/
theorem q1_pair_part_sandwich_of_peel {N : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ)
    {K : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) → ℝ}
    {Φ : Submission.BoseGases.X N → ℝ} (hΦc : Continuous Φ)
    (hpeel : ∀ i j : Fin N, i ≠ j →
      (∫ x in Submission.BoseGases.abox N ℓ,
        (Submission.BoseGases.aP ℓ j (Submission.BoseGases.aQ ℓ i Φ) x)
          * (Submission.BoseGases.aP ℓ j (Submission.BoseGases.aP ℓ i Φ) x)
          * K (x j) (x i))
      = (ℓ ^ 3)⁻¹ * (∫ x in Submission.BoseGases.abox N ℓ,
        (Submission.BoseGases.aP ℓ j (Submission.BoseGases.aQ ℓ i Φ) x)
          * (Submission.BoseGases.aP ℓ i Φ x)
          * Submission.BoseGases.w1Fibre ℓ K (x i)))
    (hint : ∀ i j : Fin N, i ≠ j →
      MeasureTheory.IntegrableOn
        (fun x => (Submission.BoseGases.aP ℓ j (Submission.BoseGases.aQ ℓ i Φ) x)
          * (Submission.BoseGases.aP ℓ i Φ x)
          * Submission.BoseGases.w1Fibre ℓ K (x i))
        (Submission.BoseGases.abox N ℓ) MeasureTheory.volume) :
    2 * (∑ p ∈ Submission.BoseGases.pairSet N, ∫ x in Submission.BoseGases.abox N ℓ,
        (Submission.BoseGases.aP ℓ p.1 (Submission.BoseGases.aQ ℓ p.2 Φ) x)
          * (Submission.BoseGases.aP ℓ p.1 (Submission.BoseGases.aP ℓ p.2 Φ) x)
          * K (x p.1) (x p.2))
      = 2 * (ℓ ^ 3)⁻¹ * (∑ i : Fin N, ∫ x in Submission.BoseGases.abox N ℓ,
        (Submission.BoseGases.aP ℓ i Φ x)
          * (Submission.BoseGases.w1Fibre ℓ K (x i))
          * (Submission.BoseGases.aQ ℓ i (fun y : Submission.BoseGases.X N =>
              (∑ j : Fin N, if _hj : j ≠ i then Submission.BoseGases.aP ℓ j Φ y else 0)) x))
    := by
  classical
  -- ## Step 1: apply the per-pair peel identity to each pair of `pairSet`
  have htotal : (∑ p ∈ pairSet N, ∫ x in abox N ℓ,
        (aP ℓ p.1 (aQ ℓ p.2 Φ) x) * (aP ℓ p.1 (aP ℓ p.2 Φ) x) * K (x p.1) (x p.2))
      = (ℓ ^ 3)⁻¹ * (∑ p ∈ pairSet N, ∫ x in abox N ℓ,
        (aP ℓ p.1 (aQ ℓ p.2 Φ) x) * (aP ℓ p.2 Φ x) * w1Fibre ℓ K (x p.2)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro p hp
    have hpij : p.1 ≠ p.2 := by
      simpa [pairSet] using (Finset.mem_filter.mp hp).2
    exact hpeel p.2 p.1 hpij.symm
  -- ## Step 2: reindex the `pairSet`-sum by its second component (the Q-slot)
  have hreg : (∑ p ∈ pairSet N, ∫ x in abox N ℓ,
        (aP ℓ p.1 (aQ ℓ p.2 Φ) x) * (aP ℓ p.2 Φ x) * w1Fibre ℓ K (x p.2))
      = ∑ i : Fin N, (∑ j : Fin N, if _hj : j ≠ i then
          (∫ x in abox N ℓ,
            (aP ℓ j (aQ ℓ i Φ) x) * (aP ℓ i Φ x) * w1Fibre ℓ K (x i)) else 0) := by
    have hsp := pairSet_sum_swap_split (N := N) (f := fun a b : Fin N =>
        ∫ x in abox N ℓ, (aP ℓ a (aQ ℓ b Φ) x) * (aP ℓ b Φ x) * w1Fibre ℓ K (x b))
    simpa using hsp
  -- ## Step 3: per Q-slot, interchange the `j`-sum with the integral
  have hslot : ∀ i : Fin N,
      (∑ j : Fin N, if _hj : j ≠ i then
        (∫ x in abox N ℓ,
          (aP ℓ j (aQ ℓ i Φ) x) * (aP ℓ i Φ x) * w1Fibre ℓ K (x i)) else 0)
      = ∫ x in abox N ℓ,
          (aP ℓ i Φ x) * (w1Fibre ℓ K (x i)) *
            (∑ j : Fin N, if _hj : j ≠ i then aP ℓ j (aQ ℓ i Φ) x else 0) := by
    intro i
    let s : Finset (Fin N) := Finset.univ.filter (fun j => j ≠ i)
    have hfint : ∀ j : Fin N, j ∈ s → MeasureTheory.Integrable
        (fun x : X N =>
          (aP ℓ j (aQ ℓ i Φ) x) * (aP ℓ i Φ x) * (w1Fibre ℓ K (x i)))
        (volume.restrict (abox N ℓ)) := by
      intro j hj
      have hji : j ≠ i := by
        simpa [s] using (Finset.mem_filter.mp hj).2
      exact hint i j hji.symm
    have hswap : (∑ j ∈ s, (∫ x in abox N ℓ,
          (aP ℓ j (aQ ℓ i Φ) x) * (aP ℓ i Φ x) * (w1Fibre ℓ K (x i))))
        = ∫ x in abox N ℓ,
            (aP ℓ i Φ x) * (w1Fibre ℓ K (x i)) * (∑ j ∈ s, aP ℓ j (aQ ℓ i Φ) x) := by
      calc
        (∑ j ∈ s, (∫ x in abox N ℓ,
            (aP ℓ j (aQ ℓ i Φ) x) * (aP ℓ i Φ x) * (w1Fibre ℓ K (x i))))
            = ∫ x in abox N ℓ,
                (∑ j ∈ s,
                  (aP ℓ j (aQ ℓ i Φ) x) * (aP ℓ i Φ x) * (w1Fibre ℓ K (x i))) := by
                rw [← integral_finsetSum s hfint]
        _ = ∫ x in abox N ℓ,
            (aP ℓ i Φ x) * (w1Fibre ℓ K (x i)) * (∑ j ∈ s, aP ℓ j (aQ ℓ i Φ) x) := by
                apply integral_congr_ae
                refine ae_of_all _ (fun x => ?_)
                change (∑ j ∈ s,
                    aP ℓ j (aQ ℓ i Φ) x * aP ℓ i Φ x * w1Fibre ℓ K (x i))
                    = aP ℓ i Φ x * w1Fibre ℓ K (x i) * (∑ j ∈ s, aP ℓ j (aQ ℓ i Φ) x)
                rw [Finset.mul_sum]
                apply Finset.sum_congr rfl
                intro j _hj
                ring
    calc
      (∑ j : Fin N, if hj : j ≠ i then
          (∫ x in abox N ℓ,
            (aP ℓ j (aQ ℓ i Φ) x) * (aP ℓ i Φ x) * (w1Fibre ℓ K (x i))) else 0)
          = ∑ j ∈ s, (∫ x in abox N ℓ,
              (aP ℓ j (aQ ℓ i Φ) x) * (aP ℓ i Φ x) * (w1Fibre ℓ K (x i))) := by
              simp [s, Finset.sum_filter]
      _ = ∫ x in abox N ℓ,
            (aP ℓ i Φ x) * (w1Fibre ℓ K (x i)) * (∑ j ∈ s, aP ℓ j (aQ ℓ i Φ) x) := hswap
      _ = ∫ x in abox N ℓ,
          (aP ℓ i Φ x) * (w1Fibre ℓ K (x i)) *
            (∑ j : Fin N, if hj : j ≠ i then aP ℓ j (aQ ℓ i Φ) x else 0) := by
              apply integral_congr_ae
              refine ae_of_all _ (fun x => ?_)
              simp [s, Finset.sum_filter]
  -- ## Step 4: pointwise `n₀`-collapse inside the Q-slot
  have hcol : ∀ i : Fin N,
      (∫ x in abox N ℓ,
          (aP ℓ i Φ x) * (w1Fibre ℓ K (x i)) *
            (∑ j : Fin N, if _hj : j ≠ i then aP ℓ j (aQ ℓ i Φ) x else 0))
      = ∫ x in abox N ℓ,
          (aP ℓ i Φ x) * (w1Fibre ℓ K (x i)) *
            (aQ ℓ i (fun y : X N =>
              (∑ j : Fin N, if _hj : j ≠ i then aP ℓ j Φ y else 0)) x) := by
    intro i
    apply integral_congr_ae
    refine ae_of_all _ (fun x => ?_)
    show aP ℓ i Φ x * w1Fibre ℓ K (x i) *
        (∑ j : Fin N, if _hj : j ≠ i then aP ℓ j (aQ ℓ i Φ) x else 0)
      = aP ℓ i Φ x * w1Fibre ℓ K (x i) *
        (aQ ℓ i (fun y : X N =>
          (∑ j : Fin N, if _hj : j ≠ i then aP ℓ j Φ y else 0)) x)
    rw [q1_n0_collapse hℓ i hΦc x]
  have hsum : (∑ i : Fin N, (∑ j : Fin N, if _hj : j ≠ i then
        (∫ x in abox N ℓ,
          (aP ℓ j (aQ ℓ i Φ) x) * (aP ℓ i Φ x) * w1Fibre ℓ K (x i)) else 0))
      = ∑ i : Fin N, ∫ x in abox N ℓ,
          (aP ℓ i Φ x) * (w1Fibre ℓ K (x i)) *
            (aQ ℓ i (fun y : X N =>
              (∑ j : Fin N, if _hj : j ≠ i then aP ℓ j Φ y else 0)) x) := by
    apply Finset.sum_congr rfl
    intro i _hi
    exact (hslot i).trans (hcol i)
  calc
    2 * (∑ p ∈ pairSet N, ∫ x in abox N ℓ,
        (aP ℓ p.1 (aQ ℓ p.2 Φ) x) * (aP ℓ p.1 (aP ℓ p.2 Φ) x) * K (x p.1) (x p.2))
        = 2 * ((ℓ ^ 3)⁻¹ * (∑ p ∈ pairSet N, ∫ x in abox N ℓ,
        (aP ℓ p.1 (aQ ℓ p.2 Φ) x) * (aP ℓ p.2 Φ x) * w1Fibre ℓ K (x p.2))) := by
            rw [htotal]
    _ = 2 * (ℓ ^ 3)⁻¹ * (∑ p ∈ pairSet N, ∫ x in abox N ℓ,
        (aP ℓ p.1 (aQ ℓ p.2 Φ) x) * (aP ℓ p.2 Φ x) * w1Fibre ℓ K (x p.2)) := by
            ring
    _ = 2 * (ℓ ^ 3)⁻¹ * (∑ i : Fin N, (∑ j : Fin N, if _hj : j ≠ i then
        (∫ x in abox N ℓ,
          (aP ℓ j (aQ ℓ i Φ) x) * (aP ℓ i Φ x) * w1Fibre ℓ K (x i)) else 0)) := by
            rw [hreg]
    _ = 2 * (ℓ ^ 3)⁻¹ * (∑ i : Fin N, ∫ x in abox N ℓ,
        (aP ℓ i Φ x) * (w1Fibre ℓ K (x i)) *
          (aQ ℓ i (fun y : X N =>
            (∑ j : Fin N, if _hj : j ≠ i then aP ℓ j Φ y else 0)) x)) := by
            rw [hsum]

end Work.BoseFixB1
