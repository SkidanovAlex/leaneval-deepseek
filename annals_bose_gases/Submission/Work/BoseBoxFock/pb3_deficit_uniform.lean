import ChallengeDeps
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Submission.Work.BoseBoxFock.PB3SecondHalfV2
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.pb3_deficit_uniform` — the block-III frame tail at a `μ`-uniform constant

`Work.BoseBoxFock.PB3SecondHalfV2` proves the frame-tail bound

    Σ_j limSlotForm ℓ j Θ − Σ_j frameSlotForm v μ N j Θ
      ≤ C * (ℓ/(2πN))² * pinDirChi ℓ Ψ + C * n * ‖Φ‖²/N²

but with the constant `C = max 2 (6 D² ℓ²/(2π)²)` where `D` is produced by
`Work.BSKinetic.exists_chiScale_bound (s := sideAt μ (a v))` *after* `μ` is fixed, i.e. `C` is
allowed to depend on `μ`.  The consumer `Work.BoseBoxFock.pairRowB3_le_massWord` cannot use that:
its constant `C` is fixed *before* the `∀ μ`, while `errKafz v R μ C` is linear in `C`.

This module re-runs the (otherwise identical) assembly with the *explicit* derivative bound
`D = M/ℓ`, where `M` is a universal constant of the bump `χ`
(`∃ M, ∀ ℓ > 0, |fderiv (chiScale ℓ) x w| ≤ (M/ℓ)‖w‖` — the child `exists_fderiv_chiScale_bound_inv`).
Since `6 D² ℓ² = 6 M²` the resulting constant `max 2 (6 M²/(2π)²)` is independent of `μ`.
-/

namespace Work.BoseBoxFock

noncomputable section

open MeasureTheory
open scoped BigOperators

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

/-- **The frame tail of the block-III row at a `μ`-uniform constant.**  If `M` bounds the derivative
of the bump uniformly in the scaling (`|fderiv (chiScale s) x w| ≤ (M/s)‖w‖` for `s > 0`), then for
every `N ≥ 1` and every smooth box state `Φ` of the box of side `ellH v μ`,

    Σ_j limSlotForm − Σ_j frameSlotForm
      ≤ max 2 (6 M²/(2π)²)·[(ℓ/(2πN))² pinDirChi + n·‖Φ‖²/N²] .
-/
theorem pb3_deficit_uniform {n : ℕ} {v : EuclideanSpace ℝ (Fin 3) → ℝ} {μ M : ℝ}
    (hμ : 0 < μ) (hav : 0 < BoseGases.a v) (hM0 : 0 ≤ M)
    (hMder : ∀ (s : ℝ), 0 < s → ∀ (x w : EuclideanSpace ℝ (Fin 3)),
        |fderiv ℝ (Submission.BoseGases.chiScale s) x w| ≤ (M / s) * ‖w‖)
    {Φ : Submission.BoseGases.X n → ℝ} (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ)
    (hnorm : 0 < Work.BoseBoxFix.normB v μ n Φ) (N : ℕ) (hN : 1 ≤ N) :
    (∑ j : Fin n, Work.BoseBoxFock.limSlotForm (Work.BoseBoxFock.ellH v μ) j
        (Work.BoseBoxFock.boxRestrictC (Work.BoseBoxFock.ellH v μ) Φ))
      - (∑ j : Fin n, Work.BoseBoxFock.frameSlotForm v μ N j
          (Work.BoseBoxFock.boxRestrictC (Work.BoseBoxFock.ellH v μ) Φ))
      ≤ max 2 (6 * M ^ 2 / (2 * Real.pi) ^ 2)
          * ((Work.BoseBoxFock.ellH v μ / (2 * Real.pi * (N : ℝ))) ^ 2
              * Work.BoseBoxFock.pinDirChi (Work.BoseBoxFock.ellH v μ)
                  (fun x => ((Φ x : ℝ) : ℂ))
            + (n : ℝ) * Work.BoseBoxFix.normB v μ n Φ / ((N : ℝ) ^ 2)) := by
  have hℓ : 0 < Work.BoseBoxFock.ellH v μ := Work.BoseBoxFock.ellH_pos v μ
  have hℓE : Work.BoseBoxFock.ellH v μ = Work.BoseBox.sideAt μ (BoseGases.a v) := by
    rw [Work.BoseBoxFock.ellH, if_pos (Work.BoseBox.sideAt_pos hμ hav)]
  set Ψ : Work.BoseDict.Xn n → ℂ := fun x => ((Φ x : ℝ) : ℂ) with hΨdef
  set D : ℝ := M / Work.BoseBoxFock.ellH v μ with hDdef
  have hD0 : 0 ≤ D := by rw [hDdef]; positivity
  have hD : ∀ x w : EuclideanSpace ℝ (Fin 3),
      |fderiv ℝ (Submission.BoseGases.chiScale (Work.BoseBoxFock.ellH v μ)) x w| ≤ D * ‖w‖ := by
    intro x w
    rw [hDdef]
    exact hMder (Work.BoseBoxFock.ellH v μ) hℓ x w
  set Λ : ℝ := 2 * Real.pi * ((N : ℝ) + 1) / Work.BoseBoxFock.ellH v μ with hΛdef
  have hΛpos : 0 < Λ := by rw [hΛdef]; positivity
  have hΛk : ∀ k : Fin 3 → ℤ, k ∉ Work.BoseBoxFock.labSet N →
      Λ ≤ ‖Work.BoseBoxFock.kappaL (Work.BoseBoxFock.ellH v μ) k‖ := by
    intro k hk
    have h1 : (N : ℝ) + 1 ≤ ‖Work.BoseBoxFock.latVec k‖ :=
      Work.BoseBoxFock.norm_ge_of_not_mem_labSet hk
    have h2 : ‖Work.BoseBoxFock.kappaL (Work.BoseBoxFock.ellH v μ) k‖
        = 2 * Real.pi * ‖Work.BoseBoxFock.latVec k‖ / Work.BoseBoxFock.ellH v μ := by
      rw [show Work.BoseBoxFock.kappaL (Work.BoseBoxFock.ellH v μ) k
            = (Work.BoseBoxFock.ellH v μ)⁻¹ • Work.BoseB4.vec k from rfl, norm_smul,
        Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr (Work.BoseBoxFock.ellH_pos v μ).le),
        Work.BoseBoxFock.L1Tails.norm_vec_eq_latVec, inv_mul_eq_div]
    rw [show Λ = 2 * Real.pi * ((N : ℝ) + 1) / Work.BoseBoxFock.ellH v μ from rfl, h2,
      div_le_div_iff_of_pos_right (Work.BoseBoxFock.ellH_pos v μ)]
    nlinarith [Real.pi_pos, h1]
  -- the per-slot bound
  have hper : ∀ j : Fin n,
      Work.BoseBoxFock.limSlotForm (Work.BoseBoxFock.ellH v μ) j
          (Work.BoseBoxFock.boxRestrictC (Work.BoseBoxFock.ellH v μ) Φ)
        - Work.BoseBoxFock.frameSlotForm v μ N j
            (Work.BoseBoxFock.boxRestrictC (Work.BoseBoxFock.ellH v μ) Φ)
        ≤ (Λ ^ 2)⁻¹ * (6 * D ^ 2 * PB3V2.fibreMassFree (Work.BoseBoxFock.ellH v μ) j Ψ
            + 2 * PB3V2.fibreWave (Work.BoseBoxFock.ellH v μ) j Ψ) := by
    intro j
    have h := PB3V2.perSlot_bound_aux (v := v) (μ := μ) N (Φ := Φ) hΦ hD0 hD hΛpos hΛk j
    simpa only [hΨdef] using h
  -- the sum over the slots
  have hsum : (∑ j : Fin n, Work.BoseBoxFock.limSlotForm (Work.BoseBoxFock.ellH v μ) j
        (Work.BoseBoxFock.boxRestrictC (Work.BoseBoxFock.ellH v μ) Φ))
      - (∑ j : Fin n, Work.BoseBoxFock.frameSlotForm v μ N j
        (Work.BoseBoxFock.boxRestrictC (Work.BoseBoxFock.ellH v μ) Φ))
      ≤ (Λ ^ 2)⁻¹ * (6 * D ^ 2 * (∑ j : Fin n, PB3V2.fibreMassFree (Work.BoseBoxFock.ellH v μ) j Ψ)
          + 2 * (∑ j : Fin n, PB3V2.fibreWave (Work.BoseBoxFock.ellH v μ) j Ψ)) := by
    rw [← Finset.sum_sub_distrib]
    calc (∑ j : Fin n, (Work.BoseBoxFock.limSlotForm (Work.BoseBoxFock.ellH v μ) j
            (Work.BoseBoxFock.boxRestrictC (Work.BoseBoxFock.ellH v μ) Φ)
          - Work.BoseBoxFock.frameSlotForm v μ N j
              (Work.BoseBoxFock.boxRestrictC (Work.BoseBoxFock.ellH v μ) Φ)))
        ≤ ∑ j : Fin n, (Λ ^ 2)⁻¹ * (6 * D ^ 2 * PB3V2.fibreMassFree (Work.BoseBoxFock.ellH v μ) j Ψ
            + 2 * PB3V2.fibreWave (Work.BoseBoxFock.ellH v μ) j Ψ) :=
          Finset.sum_le_sum (fun j _ => hper j)
      _ = (Λ ^ 2)⁻¹ * (∑ j : Fin n, (6 * D ^ 2 * PB3V2.fibreMassFree (Work.BoseBoxFock.ellH v μ) j Ψ
            + 2 * PB3V2.fibreWave (Work.BoseBoxFock.ellH v μ) j Ψ)) := by rw [Finset.mul_sum]
      _ = (Λ ^ 2)⁻¹ * (6 * D ^ 2 * (∑ j : Fin n, PB3V2.fibreMassFree (Work.BoseBoxFock.ellH v μ) j Ψ)
            + 2 * (∑ j : Fin n, PB3V2.fibreWave (Work.BoseBoxFock.ellH v μ) j Ψ)) := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  -- the two state functionals
  have hnormB : (∫ x in Submission.BoseGases.abox n (Work.BoseBoxFock.ellH v μ), ‖Ψ x‖ ^ 2)
      = Work.BoseBoxFix.normB v μ n Φ := by
    rw [Work.BoseBoxFix.normB, Work.BoseKinLoc.sqNormB, hℓE]
    refine MeasureTheory.setIntegral_congr_fun (Submission.BoseGases.abox_measurable n _)
      (fun x _ => ?_)
    rw [hΨdef]
    simp only []
    rw [Complex.norm_real, Real.norm_eq_abs, sq_abs]
  have hMmass : (∑ j : Fin n, PB3V2.fibreMassFree (Work.BoseBoxFock.ellH v μ) j Ψ)
      ≤ (n : ℝ) * Work.BoseBoxFix.normB v μ n Φ := by
    have hcont : Continuous Ψ := by
      rw [hΨdef]
      exact Complex.continuous_ofReal.comp hΦ.continuous
    have h := PB3V2.sum_fibreMassFree_le (ℓ := Work.BoseBoxFock.ellH v μ)
      (Work.BoseBoxFock.ellH_pos v μ) hcont
    rw [hnormB] at h
    exact h
  have hG : (∑ j : Fin n, PB3V2.fibreWave (Work.BoseBoxFock.ellH v μ) j Ψ)
      = Work.BoseBoxFock.pinDirChi (Work.BoseBoxFock.ellH v μ) Ψ := by
    have h := PB3V2.sum_fibreWave_eq_pinDirChi (ℓ := Work.BoseBoxFock.ellH v μ)
      (Work.BoseBoxFock.ellH_pos v μ) hΦ
    simpa only [hΨdef] using h
  -- assembly
  have hkey : (Λ ^ 2)⁻¹ * (6 * D ^ 2 * (∑ j : Fin n, PB3V2.fibreMassFree (Work.BoseBoxFock.ellH v μ) j Ψ)
        + 2 * (∑ j : Fin n, PB3V2.fibreWave (Work.BoseBoxFock.ellH v μ) j Ψ))
      ≤ (Λ ^ 2)⁻¹ * (6 * D ^ 2 * ((n : ℝ) * Work.BoseBoxFix.normB v μ n Φ)
          + 2 * Work.BoseBoxFock.pinDirChi (Work.BoseBoxFock.ellH v μ) Ψ) := by
    refine mul_le_mul_of_nonneg_left ?_ (inv_nonneg.mpr (sq_nonneg Λ))
    have h1 : 6 * D ^ 2 * (∑ j : Fin n, PB3V2.fibreMassFree (Work.BoseBoxFock.ellH v μ) j Ψ)
        ≤ 6 * D ^ 2 * ((n : ℝ) * Work.BoseBoxFix.normB v μ n Φ) :=
      mul_le_mul_of_nonneg_left hMmass (by positivity)
    have h2 : 2 * (∑ j : Fin n, PB3V2.fibreWave (Work.BoseBoxFock.ellH v μ) j Ψ)
        ≤ 2 * Work.BoseBoxFock.pinDirChi (Work.BoseBoxFock.ellH v μ) Ψ := by rw [hG]
    linarith [h1, h2]
  have hCD : 6 * D ^ 2 * (Work.BoseBoxFock.ellH v μ) ^ 2 / (2 * Real.pi) ^ 2
      ≤ max 2 (6 * M ^ 2 / (2 * Real.pi) ^ 2) := by
    have hD2 : D ^ 2 * (Work.BoseBoxFock.ellH v μ) ^ 2 = M ^ 2 := by
      rw [hDdef, div_pow]
      rw [div_mul_cancel₀ _ (pow_ne_zero 2 (ne_of_gt hℓ))]
    have heq : 6 * D ^ 2 * (Work.BoseBoxFock.ellH v μ) ^ 2 / (2 * Real.pi) ^ 2
        = 6 * M ^ 2 / (2 * Real.pi) ^ 2 := by
      rw [← hD2]; ring
    rw [heq]
    exact le_max_right (2 : ℝ) _
  have hfin : (Λ ^ 2)⁻¹ * (6 * D ^ 2 * ((n : ℝ) * Work.BoseBoxFix.normB v μ n Φ)
        + 2 * Work.BoseBoxFock.pinDirChi (Work.BoseBoxFock.ellH v μ) Ψ)
      ≤ max 2 (6 * M ^ 2 / (2 * Real.pi) ^ 2)
          * (Work.BoseBoxFock.ellH v μ / (2 * Real.pi * (N : ℝ))) ^ 2
          * Work.BoseBoxFock.pinDirChi (Work.BoseBoxFock.ellH v μ) Ψ
        + max 2 (6 * M ^ 2 / (2 * Real.pi) ^ 2)
          * ((n : ℝ) * Work.BoseBoxFix.normB v μ n Φ)
          / ((N : ℝ) ^ 2) := by
    have h := PB3V2.arith_bound (ℓ := Work.BoseBoxFock.ellH v μ) (D := D)
      (M := (n : ℝ) * Work.BoseBoxFix.normB v μ n Φ)
      (pin := Work.BoseBoxFock.pinDirChi (Work.BoseBoxFock.ellH v μ) Ψ)
      (C := max 2 (6 * M ^ 2 / (2 * Real.pi) ^ 2))
      hℓ hN (mul_nonneg (Nat.cast_nonneg n) hnorm.le) (Work.BoseBoxFock.pinDirChi_nonneg _ Ψ)
      (le_max_left (2 : ℝ) _) hCD
    rw [show 2 * Real.pi * ((N : ℝ) + 1) / Work.BoseBoxFock.ellH v μ = Λ from rfl] at h
    exact h
  have hmain : (∑ j : Fin n, Work.BoseBoxFock.limSlotForm (Work.BoseBoxFock.ellH v μ) j
        (Work.BoseBoxFock.boxRestrictC (Work.BoseBoxFock.ellH v μ) Φ))
      - (∑ j : Fin n, Work.BoseBoxFock.frameSlotForm v μ N j
        (Work.BoseBoxFock.boxRestrictC (Work.BoseBoxFock.ellH v μ) Φ))
      ≤ max 2 (6 * M ^ 2 / (2 * Real.pi) ^ 2)
          * ((Work.BoseBoxFock.ellH v μ / (2 * Real.pi * (N : ℝ))) ^ 2
              * Work.BoseBoxFock.pinDirChi (Work.BoseBoxFock.ellH v μ) Ψ
            + (n : ℝ) * Work.BoseBoxFix.normB v μ n Φ / ((N : ℝ) ^ 2)) := by
    refine le_trans hsum (le_trans hkey ?_)
    calc (Λ ^ 2)⁻¹ * (6 * D ^ 2 * ((n : ℝ) * Work.BoseBoxFix.normB v μ n Φ)
          + 2 * Work.BoseBoxFock.pinDirChi (Work.BoseBoxFock.ellH v μ) Ψ)
        ≤ max 2 (6 * M ^ 2 / (2 * Real.pi) ^ 2)
            * (Work.BoseBoxFock.ellH v μ / (2 * Real.pi * (N : ℝ))) ^ 2
            * Work.BoseBoxFock.pinDirChi (Work.BoseBoxFock.ellH v μ) Ψ
          + max 2 (6 * M ^ 2 / (2 * Real.pi) ^ 2)
            * ((n : ℝ) * Work.BoseBoxFix.normB v μ n Φ) / ((N : ℝ) ^ 2) := hfin
      _ = max 2 (6 * M ^ 2 / (2 * Real.pi) ^ 2)
            * ((Work.BoseBoxFock.ellH v μ / (2 * Real.pi * (N : ℝ))) ^ 2
                * Work.BoseBoxFock.pinDirChi (Work.BoseBoxFock.ellH v μ) Ψ
              + (n : ℝ) * Work.BoseBoxFix.normB v μ n Φ / ((N : ℝ) ^ 2)) := by
          rw [mul_add]; ring
  simpa only [hΨdef] using hmain

end

end Work.BoseBoxFock
