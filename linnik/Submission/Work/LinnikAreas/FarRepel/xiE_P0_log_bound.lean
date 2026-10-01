import Mathlib
import Submission.Work.LinnikAreas.DhK.XiAux

/-!
# `Work.LinnikAreas.FarRepel.xiE_P0_log_bound`

The origin value of the divisor product of `Ξ` on the disc of radius `T`:

`|log ‖∏ᶠ u, (0 - u)^{d_T u}‖| ≤ Z_T · (log T + |log δ₀|)`,

where `d_T` is the divisor of `Ξ` on `closedBall 0 T`, `Z_T = ∑ᶠ u, d_T u` its total mass, and
`δ₀ > 0` is a lower bound for the modulus of the zeros of `Ξ`.

Exact analogue of `Commons.NumberTheory.Linnik.pf_P0_log_bound` (and of
`Commons.NumberTheory.Zeta.XiPF.xiF_P0_log_bound`) with `Λ := DhK.Xi`; the mean-value
hypotheses of those versions are replaced by the `Xi` ball-divisor API of `DhK.XiAux`.
-/

open scoped Classical BigOperators
open Metric

noncomputable section

namespace Work.LinnikAreas.FarRepel

theorem xiE_P0_log_bound {T : ℝ} (hT : 1 ≤ T) (δ₀ : ℝ) (hδ₀pos : 0 < δ₀)
    (hδ₀ : ∀ u : ℂ, Work.LinnikAreas.DhK.Xi u = 0 → δ₀ ≤ ‖u‖) :
    |Real.log ‖(∏ᶠ u : ℂ, ((0 : ℂ) - u) ^ (MeromorphicOn.divisor
      Work.LinnikAreas.DhK.Xi (Metric.closedBall (0 : ℂ) T) u))‖| ≤
      (∑ᶠ u : ℂ, ((MeromorphicOn.divisor Work.LinnikAreas.DhK.Xi
        (Metric.closedBall (0 : ℂ) T)) u : ℝ)) * (Real.log T + |Real.log δ₀|) := by
  classical
  let d : ℂ → ℤ := fun u =>
    MeromorphicOn.divisor Work.LinnikAreas.DhK.Xi (Metric.closedBall (0 : ℂ) T) u
  have hd_nonneg : ∀ u, 0 ≤ d u := by
    intro u
    dsimp [d]
    exact Work.LinnikAreas.DhK.Xi_divisor_nonneg T u
  have hsupport : (Function.support d).Finite := by
    dsimp [d]
    exact Work.LinnikAreas.DhK.Xi_divisor_support_finite T
  let S : Finset ℂ := hsupport.toFinset
  have hmemS : ∀ u : ℂ, u ∈ S ↔ d u ≠ 0 := by
    intro u
    dsimp [S]
    rw [Set.Finite.mem_toFinset]
    rfl
  have hdist0 : ∀ u : ℂ, u ∈ S → δ₀ ≤ ‖u‖ ∧ ‖u‖ ≤ T := by
    intro u hu
    have hdne : d u ≠ 0 := (hmemS u).mp hu
    have hzu : Work.LinnikAreas.DhK.Xi u = 0 := by
      dsimp [d] at hdne
      exact Work.LinnikAreas.DhK.Xi_divisor_ne_zero_is_zero (R := T) hdne
    have huδ : δ₀ ≤ ‖u‖ := hδ₀ u hzu
    have hdne0 : (MeromorphicOn.divisor Work.LinnikAreas.DhK.Xi
        (Metric.closedBall (0 : ℂ) T)) u ≠ 0 := by
      simpa [d] using hdne
    have huT : ‖u‖ ≤ T := by
      have hmemB : u ∈ Metric.closedBall (0 : ℂ) T := by
        by_contra hout
        rw [MeromorphicOn.divisor_def] at hdne0
        simp [hout] at hdne0
      simpa [Metric.mem_closedBall, dist_eq_norm] using hmemB
    exact ⟨huδ, huT⟩
  let B : ℝ := Real.log T + |Real.log δ₀|
  have hlogTpos : 0 ≤ Real.log T := Real.log_nonneg hT
  have hlogB : ∀ u : ℂ, u ∈ S → |Real.log ‖u‖| ≤ B := by
    intro u hu
    have hδle : δ₀ ≤ ‖u‖ := (hdist0 u hu).1
    have hTge : ‖u‖ ≤ T := (hdist0 u hu).2
    have hpos : 0 < ‖u‖ := lt_of_lt_of_le hδ₀pos hδle
    have hle1 : Real.log ‖u‖ ≤ B := by
      have h : Real.log ‖u‖ ≤ Real.log T := Real.log_le_log hpos hTge
      have habs : 0 ≤ |Real.log δ₀| := abs_nonneg _
      dsimp [B]
      linarith
    have hle2 : -B ≤ Real.log ‖u‖ := by
      have h : Real.log δ₀ ≤ Real.log ‖u‖ := Real.log_le_log hδ₀pos hδle
      have hnegabs : -|Real.log δ₀| ≤ Real.log δ₀ := neg_abs_le (Real.log δ₀)
      have h3 : -B ≤ -|Real.log δ₀| := by
        dsimp [B]
        linarith
      exact le_trans (le_trans h3 hnegabs) h
    exact abs_le.mpr ⟨hle2, hle1⟩
  have hnorm_fac : ∀ u : ℂ, u ∈ S → ‖(0 : ℂ) - u‖ = ‖u‖ := by
    intro u hu
    simp
  have hprod_eq : (∏ᶠ u : ℂ, ((0 : ℂ) - u) ^ (d u)) = ∏ u ∈ S, ((0 : ℂ) - u) ^ (d u) := by
    refine finprod_eq_prod_of_mulSupport_subset (fun u : ℂ => ((0 : ℂ) - u) ^ (d u)) ?_
    intro u hu
    rw [Function.mem_mulSupport] at hu
    have hdne : d u ≠ 0 := by
      intro hd0
      have : ((0 : ℂ) - u) ^ (d u) = 1 := by simp [hd0]
      exact hu this
    exact (hmemS u).mpr hdne
  have hpos_fac : ∀ u : ℂ, u ∈ S → 0 < ‖((0 : ℂ) - u) ^ (d u)‖ := by
    intro u hu
    have hp : 0 < ‖(0 : ℂ) - u‖ := by
      rw [hnorm_fac u hu]
      exact lt_of_lt_of_le hδ₀pos (hdist0 u hu).1
    simpa [Commons.NumberTheory.Linnik.pf_norm_zpow_eq] using
      Commons.NumberTheory.Linnik.pf_zpow_pos hp (hd_nonneg u)
  have hlogS : |(∑ u ∈ S, ((d u : ℤ) : ℝ) * Real.log ‖(0 : ℂ) - u‖)| ≤
      (∑ u ∈ S, ((d u : ℤ) : ℝ)) * B := by
    have h1 : |∑ u ∈ S, ((d u : ℤ) : ℝ) * Real.log ‖(0 : ℂ) - u‖| ≤
        ∑ u ∈ S, |((d u : ℤ) : ℝ) * Real.log ‖(0 : ℂ) - u‖| := by
      exact Finset.abs_sum_le_sum_abs (fun u => ((d u : ℤ) : ℝ) * Real.log ‖(0 : ℂ) - u‖) S
    have h2 : (∑ u ∈ S, |((d u : ℤ) : ℝ) * Real.log ‖(0 : ℂ) - u‖|) ≤
        ∑ u ∈ S, (((d u : ℤ) : ℝ) * B) := by
      refine Finset.sum_le_sum (fun u hu => ?_)
      have hd0 : 0 ≤ (d u : ℝ) := by exact_mod_cast (hd_nonneg u)
      have hb : |Real.log ‖u‖| ≤ B := hlogB u hu
      calc
        |((d u : ℤ) : ℝ) * Real.log ‖(0 : ℂ) - u‖| = (d u : ℝ) * |Real.log ‖(0 : ℂ) - u‖| := by
          rw [abs_mul, abs_of_nonneg hd0]
        _ = (d u : ℝ) * |Real.log ‖u‖| := by rw [hnorm_fac u hu]
        _ ≤ (d u : ℝ) * B := mul_le_mul_of_nonneg_left hb hd0
    have h3 : (∑ u ∈ S, (((d u : ℤ) : ℝ) * B)) = (∑ u ∈ S, ((d u : ℤ) : ℝ)) * B := by
      rw [Finset.sum_mul]
    linarith
  have hfin_eq : (∑ᶠ u : ℂ, ((d u : ℤ) : ℝ)) = ∑ u ∈ S, ((d u : ℤ) : ℝ) := by
    refine finsum_eq_sum_of_support_subset (fun u : ℂ => ((d u : ℤ) : ℝ)) ?_
    intro u hu
    rw [Function.mem_support] at hu
    have hdne : d u ≠ 0 := by
      intro hd0
      exact hu (by simp [hd0])
    exact (hmemS u).mpr hdne
  calc
    |Real.log ‖(∏ᶠ u : ℂ, ((0 : ℂ) - u) ^ (MeromorphicOn.divisor
        Work.LinnikAreas.DhK.Xi (Metric.closedBall (0 : ℂ) T) u))‖|
        = |Real.log ‖∏ᶠ u : ℂ, ((0 : ℂ) - u) ^ (d u)‖| := by dsimp only [d]
    _ = |Real.log ‖∏ u ∈ S, ((0 : ℂ) - u) ^ (d u)‖| := by rw [hprod_eq]
    _ = |Real.log (∏ u ∈ S, ‖((0 : ℂ) - u) ^ (d u)‖)| := by
            rw [Commons.NumberTheory.Linnik.pf_norm_finset_prod S
              (fun u => ((0 : ℂ) - u) ^ (d u))]
    _ = |∑ u ∈ S, Real.log ‖((0 : ℂ) - u) ^ (d u)‖| := by
            rw [Real.log_prod]
            intro u hu
            exact (hpos_fac u hu).ne'
    _ = |∑ u ∈ S, ((d u : ℤ) : ℝ) * Real.log ‖(0 : ℂ) - u‖| := by
            congr 1
            apply Finset.sum_congr rfl
            intro u hu
            have hp0 : 0 < ‖(0 : ℂ) - u‖ := by
              rw [hnorm_fac u hu]
              exact lt_of_lt_of_le hδ₀pos (hdist0 u hu).1
            have hlog : Real.log (‖(0 : ℂ) - u‖ ^ (d u)) =
                (d u : ℝ) * Real.log ‖(0 : ℂ) - u‖ :=
              Commons.NumberTheory.Linnik.pf_log_zpow hp0 (hd_nonneg u)
            rw [Commons.NumberTheory.Linnik.pf_norm_zpow_eq ((0 : ℂ) - u) (d u), hlog]
    _ ≤ (∑ u ∈ S, ((d u : ℤ) : ℝ)) * B := hlogS
    _ = (∑ᶠ u : ℂ, ((d u : ℤ) : ℝ)) * B := by rw [hfin_eq]
    _ = (∑ᶠ u : ℂ, ((MeromorphicOn.divisor Work.LinnikAreas.DhK.Xi
          (Metric.closedBall (0 : ℂ) T)) u : ℝ)) * (Real.log T + |Real.log δ₀|) := by
            dsimp only [d, B]

end Work.LinnikAreas.FarRepel
