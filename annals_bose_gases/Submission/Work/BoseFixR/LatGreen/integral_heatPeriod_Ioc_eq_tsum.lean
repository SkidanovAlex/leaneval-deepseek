import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixR.LatGreen.LatGreenParsevalBDefs
import Submission.Work.BoseFixR.LatGreen.heatK3_head_le
import Submission.Work.BoseFixR.LatGreen.integral_tsum_Ioc
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `integral_heatPeriod_Ioc_eq_tsum`

For `0 < ε ≤ 1` and a point `u` of `ℝ³` that is not a lattice point, the short-time integral of
the periodised heat kernel equals the series of the per-lattice-point heat-kernel integrals:

`∫_{Ioc 0 ε} heatPeriod s u = ∑'_n ∫_{Ioc 0 ε} heatK3 s (u − latVec n)`.

## Proof

The exchange of the integral with the lattice series is Tonelli for the non-negative family
`F n t = 1_{Ioc 0 ε}(t) · heatK3 t (u − latVec n)` (the lemma `integral_tsum_Ioc`; the indicator
is what makes the non-negativity hypothesis available *globally* in `t`, which is how that lemma
is stated).

The series of integrals is summable because the truncated heat-kernel head bound
`heatK3_head_le` turns each term into a Gaussian:

`∫_{Ioc 0 ε} heatK3 t (u − latVec n) ≤ √ε · e^{−‖u−n‖²/(4ε)} / (2π^{3/2}‖u−n‖²)`,

and, with `δ > 0` a lower bound for the distance of `u` to the lattice (`exists_dist_pos`, which
uses that `u` is not a lattice point) and `ε ≤ 1` so that `1/(4ε) ≥ 1/8`,

`√ε · e^{−‖u−n‖²/(4ε)} / (2π^{3/2}‖u−n‖²) ≤ (√ε / (2π^{3/2} δ²)) · e^{−‖u−n‖²/8}`,

while `Σ_n e^{−‖u − latVec n‖²/8}` is summable (`GaussSummable`).
-/

noncomputable section

open scoped Real BigOperators
open MeasureTheory Set

namespace Work.BoseFixR.LatGreen

set_option maxHeartbeats 800000

/-- Elementary ledger for the head bound: for `0 < ε ≤ 1`, `A > 0`, `δ > 0`, `δ² ≤ A`,

`√ε · e^{−A/(4ε)} / (8π^{3/2}(A/4)) ≤ (√ε / (2π^{3/2}δ²)) · e^{−A/8}`.

Since `8·(A/4) = 2A`, after cancelling the common positive factor it is enough to know
`δ²·e^{−A/(4ε)} ≤ A·e^{−A/8}`, which follows from `δ² ≤ A` and `e^{−A/(4ε)} ≤ e^{−A/8}`
(the latter is `A/(4ε) ≥ A/8`, i.e. `ε ≤ 2`). -/
private lemma head_ioc_le_gauss {ε A δ : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hA : 0 < A) (hδ : 0 < δ) (hδA : δ ^ 2 ≤ A) :
    Real.sqrt ε * Real.exp (-(A / 4 / ε)) / (8 * Real.pi ^ (3 / 2 : ℝ) * (A / 4))
      ≤ (Real.sqrt ε / (2 * Real.pi ^ (3 / 2 : ℝ) * δ ^ 2)) * Real.exp (-A / 8) := by
  have hpi : (0 : ℝ) < Real.pi ^ (3 / 2 : ℝ) := Real.rpow_pos_of_pos Real.pi_pos _
  have hden1 : (0 : ℝ) < 8 * Real.pi ^ (3 / 2 : ℝ) * (A / 4) := by positivity
  have hden2 : (0 : ℝ) < 2 * Real.pi ^ (3 / 2 : ℝ) * δ ^ 2 := by positivity
  have hexp : Real.exp (-(A / 4 / ε)) ≤ Real.exp (-A / 8) := by
    rw [Real.exp_le_exp]
    have h8 : A / 8 ≤ A / (4 * ε) :=
      div_le_div_of_nonneg_left hA.le (by positivity) (by linarith)
    have h4 : A / 4 / ε = A / (4 * ε) := by ring
    rw [h4]
    linarith
  calc Real.sqrt ε * Real.exp (-(A / 4 / ε)) / (8 * Real.pi ^ (3 / 2 : ℝ) * (A / 4))
      ≤ Real.sqrt ε * Real.exp (-A / 8) / (8 * Real.pi ^ (3 / 2 : ℝ) * (A / 4)) :=
        div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left hexp (Real.sqrt_nonneg ε)) hden1.le
    _ = Real.sqrt ε * Real.exp (-A / 8) / (2 * Real.pi ^ (3 / 2 : ℝ) * A) := by
        rw [show 8 * Real.pi ^ (3 / 2 : ℝ) * (A / 4) = 2 * Real.pi ^ (3 / 2 : ℝ) * A by ring]
    _ ≤ Real.sqrt ε * Real.exp (-A / 8) / (2 * Real.pi ^ (3 / 2 : ℝ) * δ ^ 2) :=
        div_le_div_of_nonneg_left (by positivity) hden2
          (mul_le_mul_of_nonneg_left hδA (by positivity))
    _ = (Real.sqrt ε / (2 * Real.pi ^ (3 / 2 : ℝ) * δ ^ 2)) * Real.exp (-A / 8) := by ring

-- `hu2` (the bound `|u i| ≤ 2`) is part of the requested statement but is not needed by the
-- argument: the estimate only uses that `u` is not a lattice point.
set_option linter.unusedVariables false in
theorem integral_heatPeriod_Ioc_eq_tsum {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1)
    {u : EuclideanSpace ℝ (Fin 3)} (hu2 : ∀ i : Fin 3, |u i| ≤ 2)
    (hu : ∀ n : Fin 3 → ℤ, u ≠ Work.BoseFixR.LatGreen.latVec n) :
    ∫ s in Set.Ioc 0 ε, Work.BoseFixR.LatGreen.heatPeriod s u
      = ∑' n : Fin 3 → ℤ, ∫ s in Set.Ioc 0 ε,
          Work.BoseFixR.LatGreen.heatK3 s (u - Work.BoseFixR.LatGreen.latVec n) := by
  classical
  -- The pointwise series term, zeroed off `Ioc 0 ε` so that the non-negativity hypothesis of
  -- `integral_tsum_Ioc` holds globally in `t`.
  set F : (Fin 3 → ℤ) → ℝ → ℝ :=
    fun n t => if t ∈ Set.Ioc 0 ε then heatK3 t (u - latVec n) else 0 with hF
  have hFnn : ∀ n t, 0 ≤ F n t := by
    intro n t
    rw [hF]
    by_cases ht : t ∈ Set.Ioc 0 ε
    · simp only [ht, if_true]
      exact heatK3_nonneg ht.1 _
    · simp only [ht, if_false]
      exact le_refl 0
  -- Integrability of each term on `Ioc 0 ε`, from the head bound.
  have hFint : ∀ n, IntegrableOn (F n) (Set.Ioc 0 ε) := by
    intro n
    have hx0 : u - latVec n ≠ 0 := sub_ne_zero.mpr (hu n)
    have hpos : 0 < ‖u - latVec n‖ ^ 2 / 4 := by
      have hp : 0 < ‖u - latVec n‖ := norm_pos_iff.mpr hx0
      positivity
    refine ((heatK3_head_le hpos hε).1).congr_fun ?_ measurableSet_Ioc
    intro t ht
    rw [hF]
    simp only [ht, if_true, heatK3]
    congr 1
    ring_nf
  -- `δ` is a positive lower bound for the distance of `u` to the lattice.
  obtain ⟨δ, hδpos, hδ⟩ := exists_dist_pos hu
  have hGauss : Summable (fun n : Fin 3 → ℤ => Real.exp (-‖u - latVec n‖ ^ 2 / 8)) := by
    have h := GaussSummable (t := 2) (by norm_num) u
    exact h.congr (fun m => by congr 1; ring)
  -- The Gaussian majorant of the series of head integrals.
  set g : (Fin 3 → ℤ) → ℝ := fun n =>
      Real.sqrt ε / (2 * Real.pi ^ (3 / 2 : ℝ) * δ ^ 2) * Real.exp (-‖u - latVec n‖ ^ 2 / 8)
    with hg
  have hG : Summable g := by
    rw [hg]
    exact hGauss.mul_left _
  have hbound : ∀ n : Fin 3 → ℤ, (∫ t in Set.Ioc 0 ε, F n t) ≤ g n := by
    intro n
    have hx0 : u - latVec n ≠ 0 := sub_ne_zero.mpr (hu n)
    have hA : 0 < ‖u - latVec n‖ ^ 2 := by
      have hp : 0 < ‖u - latVec n‖ := norm_pos_iff.mpr hx0
      positivity
    have hpos : 0 < ‖u - latVec n‖ ^ 2 / 4 := by positivity
    have hcongr : (∫ t in Set.Ioc 0 ε, F n t)
        = ∫ t in Set.Ioc 0 ε,
            (4 * Real.pi * t) ^ (-(3 / 2 : ℝ)) * Real.exp (-(‖u - latVec n‖ ^ 2 / 4 / t)) := by
      refine setIntegral_congr_fun measurableSet_Ioc fun t ht => ?_
      rw [hF]
      simp only [ht, if_true, heatK3]
      congr 1
      ring_nf
    rw [hcongr, hg]
    refine le_trans (heatK3_head_le hpos hε).2 ?_
    have hδA : δ ^ 2 ≤ ‖u - latVec n‖ ^ 2 := by
      nlinarith [hδ n, norm_nonneg (u - latVec n)]
    exact head_ioc_le_gauss hε hε1 hA hδpos hδA
  have hsummInt : Summable fun n : Fin 3 → ℤ => ∫ t in Set.Ioc 0 ε, F n t :=
    Summable.of_nonneg_of_le
      (fun n => setIntegral_nonneg measurableSet_Ioc fun t ht => hFnn n t)
      hbound hG
  -- Tonelli: exchange the integral over `Ioc 0 ε` with the lattice series.
  have hkey : (∫ t in Set.Ioc 0 ε, heatPeriod t u)
      = ∑' n : Fin 3 → ℤ, ∫ t in Set.Ioc 0 ε, F n t := by
    have hpt : ∀ t ∈ Set.Ioc 0 ε, heatPeriod t u = ∑' n : Fin 3 → ℤ, F n t := by
      intro t ht
      rw [heatPeriod]
      exact tsum_congr fun n => by
        rw [hF]
        simp only [ht, if_true]
    rw [setIntegral_congr_fun measurableSet_Ioc hpt]
    exact integral_tsum_Ioc hε hFnn hFint hsummInt
  rw [hkey]
  -- Finally, `F n` and `heatK3 · (u − latVec n)` agree on `Ioc 0 ε`.
  refine tsum_congr fun n => ?_
  exact setIntegral_congr_fun measurableSet_Ioc fun t ht => by
    rw [hF]
    simp only [ht, if_true]

end Work.BoseFixR.LatGreen
