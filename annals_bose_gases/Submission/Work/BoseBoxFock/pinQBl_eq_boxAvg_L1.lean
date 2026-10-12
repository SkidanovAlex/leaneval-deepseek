import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Submission.Work.BoseBoxFock.latSum_latPer3_integral_swap_L1
import Submission.Work.BoseBoxFock.pinQBl_eq_periodisation_L1
import Submission.Work.BoseBoxFock.pinQDl_eq_boxAvg
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.pinQBl_eq_boxAvg_L1` — the box-average form of the first `χ̂`-lattice sum,
## in the `L¹` hypothesis set

`K1lim` (and hence the whole `Q₂`-row dictionary `K1lim_eq_qmqK…`) is fed with *abstract* kernels
`W : ℝ³ → ℝ` that are known only to be **integrable** with compact support (and even, with support
in a ball of radius `R`) — the pointwise bound `∃ C, ∀ x, ‖W x‖ ≤ C` of
`pinQBl_eq_boxAvg` / `pinQBl_eq_periodisation` is *not* available (an `L¹` function may be
unbounded on a set of positive measure).  This file removes that bound:

    `pinQBl ℓ W w = (ℓ³)⁻¹ ∫_{acube ℓ} χ_ℓ(y)·latPer3 ℓ W (w − y) dy`

for every `W` that is `L¹`, compactly supported, even, and supported in the ball of radius `R`.

The two places where the *pointwise* bound was used are exactly the two places where the old proof
manufactured `Integrable W` from `AEStronglyMeasurable W` + a bound + compact support; both are now
hypotheses, so the two auxiliary lemmas are re-proved in the `L¹` hypothesis set (delegated,
`pinQBl_eq_periodisation_L1` and `latSum_latPer3_integral_swap_L1`), and the remaining assembly —
the measure-preserving substitution `x ↦ w + ℓm − x`, the transfer of the `∫_{ℝ³}` to `∫_{acube ℓ}`
(valid because `χ_ℓ` is carried by the cube), and the `ℓ³` bookkeeping of `latPer3` — is the body
of the theorem below.

## Proof

* (1) `pinQBl_eq_periodisation_L1` evaluates the lattice sum `pinQBl` as
  `Σ'_m ∫_x W x·χ_ℓ(w + ℓm − x) dx`, and the measure-preserving reflection `x ↦ (w + ℓm) − x`
  (`MeasureTheory.integral_sub_left_eq_self`) turns each summand into
  `∫_y χ_ℓ(y)·W(w − y + ℓm) dy`.
* (2) `latSum_latPer3_integral_swap_L1` interchanges the `m`-sum with the `y`-integral; both
  series are finite (the supports of `χ_ℓ` — radius `ℓ/2` — and of `W` — radius `R` — do it).
* (3) `integral_eq_acube_integral` moves the integral onto the cube, `χ_ℓ` vanishing off it.
* (4) `latPer3 = ↑(ℓ³)·latPer`, so the two `ℓ³`'s cancel.
-/

noncomputable section

open MeasureTheory

namespace Work.BoseBoxFock

theorem pinQBl_eq_boxAvg_L1 {ℓ R : ℝ} (hℓ : 0 < ℓ) {W : EuclideanSpace ℝ (Fin 3) → ℝ}
    (hWi : MeasureTheory.Integrable W) (hWs : HasCompactSupport W)
    (hWev : ∀ z, W (-z) = W z)
    (hW : ∀ z, R < ‖z‖ → W z = 0) (w : EuclideanSpace ℝ (Fin 3)) :
    Work.BoseBoxFock.pinQBl ℓ W w
      = ((ℓ ^ 3)⁻¹ : ℂ) * ∫ y in Submission.BoseGases.acube ℓ,
          (((Submission.BoseGases.chiScale ℓ y : ℝ)) : ℂ)
            * Work.BoseBoxFock.latPer3 ℓ W (w - y) := by
  classical
  -- (1) the periodisation form, each summand reflected onto `χ_ℓ(y)·W(w − y + ℓm)`
  have htrans : ∀ m : Fin 3 → ℤ,
      (∫ x : EuclideanSpace ℝ (Fin 3), ((W x : ℝ) : ℂ)
          * ((Submission.BoseGases.chiScale ℓ (w + ℓ • latVec m - x) : ℝ) : ℂ))
        = ∫ y : EuclideanSpace ℝ (Fin 3),
            (((Submission.BoseGases.chiScale ℓ y : ℝ)) : ℂ)
              * ((W (w - y + ℓ • latVec m) : ℝ) : ℂ) := by
    intro m
    have hstep : (∫ y : EuclideanSpace ℝ (Fin 3), ((W ((w + ℓ • latVec m) - y) : ℝ) : ℂ)
          * ((Submission.BoseGases.chiScale ℓ
              ((w + ℓ • latVec m) - ((w + ℓ • latVec m) - y)) : ℝ) : ℂ))
        = ∫ x : EuclideanSpace ℝ (Fin 3), ((W x : ℝ) : ℂ)
            * ((Submission.BoseGases.chiScale ℓ ((w + ℓ • latVec m) - x) : ℝ) : ℂ) :=
      MeasureTheory.integral_sub_left_eq_self
        (fun x : EuclideanSpace ℝ (Fin 3) => ((W x : ℝ) : ℂ)
          * ((Submission.BoseGases.chiScale ℓ ((w + ℓ • latVec m) - x) : ℝ) : ℂ))
        volume (w + ℓ • latVec m)
    rw [← hstep]
    apply MeasureTheory.integral_congr_ae
    filter_upwards with y
    rw [show (w + ℓ • latVec m) - ((w + ℓ • latVec m) - y) = y from sub_sub_cancel _ _,
      show (w + ℓ • latVec m) - y = w - y + ℓ • latVec m by abel, mul_comm]
  have h1 : Work.BoseBoxFock.pinQBl ℓ W w = ∑' m : Fin 3 → ℤ,
      ∫ y : EuclideanSpace ℝ (Fin 3),
        (((Submission.BoseGases.chiScale ℓ y : ℝ)) : ℂ)
          * ((W (w - y + ℓ • latVec m) : ℝ) : ℂ) := by
    rw [pinQBl_eq_periodisation_L1 hℓ hWi hWs hWev w]
    exact tsum_congr htrans
  -- (2) the lattice-sum/integral interchange
  have h2 := latSum_latPer3_integral_swap_L1 (ℓ := ℓ) hℓ (W := W) hWi hW w
  -- (3) support transfer to the centred cube
  have h3 : (∫ y : EuclideanSpace ℝ (Fin 3),
        (((Submission.BoseGases.chiScale ℓ y : ℝ)) : ℂ)
          * (∑' m : Fin 3 → ℤ, ((W (w - y + ℓ • latVec m) : ℝ) : ℂ)))
      = ∫ y in Submission.BoseGases.acube ℓ,
          (((Submission.BoseGases.chiScale ℓ y : ℝ)) : ℂ)
            * (∑' m : Fin 3 → ℤ, ((W (w - y + ℓ • latVec m) : ℝ) : ℂ)) :=
    integral_eq_acube_integral (fun y hy => by
      have hχ : Submission.BoseGases.chiScale ℓ y ≠ 0 := fun h => hy (by simp [h])
      exact Submission.BoseGases.chiScale_mem_acube hℓ hχ)
  have hmain : Work.BoseBoxFock.pinQBl ℓ W w = ∫ y in Submission.BoseGases.acube ℓ,
      (((Submission.BoseGases.chiScale ℓ y : ℝ)) : ℂ)
        * (∑' m : Fin 3 → ℤ, ((W (w - y + ℓ • latVec m) : ℝ) : ℂ)) :=
    h1.trans (h2.trans h3)
  -- (4) the `ℓ³` bookkeeping of `latPer3`
  have h3' : ((ℓ ^ 3)⁻¹ : ℂ) * ((ℓ ^ 3 : ℝ) : ℂ) = 1 := by
    rw [Complex.ofReal_pow, inv_mul_cancel₀]
    exact pow_ne_zero 3 (by exact_mod_cast (ne_of_gt hℓ))
  have hA : (∫ y in Submission.BoseGases.acube ℓ,
        (((Submission.BoseGases.chiScale ℓ y : ℝ)) : ℂ)
          * Work.BoseBoxFock.latPer3 ℓ W (w - y))
      = ((ℓ ^ 3 : ℝ) : ℂ) * ∫ y in Submission.BoseGases.acube ℓ,
          (((Submission.BoseGases.chiScale ℓ y : ℝ)) : ℂ) * LatFourier.latPer ℓ W (w - y) := by
    rw [show (∫ y in Submission.BoseGases.acube ℓ,
          (((Submission.BoseGases.chiScale ℓ y : ℝ)) : ℂ)
            * Work.BoseBoxFock.latPer3 ℓ W (w - y))
        = ∫ y in Submission.BoseGases.acube ℓ, ((ℓ ^ 3 : ℝ) : ℂ)
            * ((((Submission.BoseGases.chiScale ℓ y : ℝ)) : ℂ)
              * LatFourier.latPer ℓ W (w - y)) from by
      apply MeasureTheory.integral_congr_ae
      filter_upwards with y
      simp only [Work.BoseBoxFock.latPer3]
      ring]
    rw [MeasureTheory.integral_const_mul]
  rw [hmain, hA, ← mul_assoc, h3', one_mul]
  simp only [LatFourier.latPer]

end Work.BoseBoxFock
