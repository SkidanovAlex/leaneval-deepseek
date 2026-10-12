import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.BoseFixR.LatGreen.heatK3_ioc_integral_le_gauss
import Submission.Work.BoseFixR.LatGreen.heatK3_ioc_integral_le_green
import Submission.Work.BoseFixR.LatGreen.integral_heatPeriod_Ioc_eq_tsum
import Submission.Work.BoseFixR.LatGreen.latSum_invSq_gauss_le
import Submission.Work.BoseFixR.LatGreen.latticeGaussSum_le
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

noncomputable section

open scoped Real BigOperators
open MeasureTheory Set

namespace Work.BoseFixR.LatGreen

/-- **Domination of the small-time part of the periodic Coulomb kernel** (piece of
`Work.BoseFixR.LatGreen.LatGreenParsevalB`).

There is `C` such that for every `ε ∈ (0,1]` and every `u ∈ ℝ³` with `|u i| ≤ 2` that is not a
lattice vector,

`∫_{(0,ε]} |heatPeriod s u − 1| ds ≤ C·(1 + Σ_{n ∈ latBox} 1/‖u − latVec n‖)`,

where `heatPeriod s u = Σ_{n∈ℤ³} (4πs)^{−3/2}e^{−‖u−n‖²/(4s)}` and `latBox = {-4,…,4}³ ⊆ ℤ³`
(the finite set defined in `LatGreenParsevalBDefs`; for `|u i| ≤ 2` it contains the nearest
lattice point of `u`, since the nearest point satisfies `|n i| ≤ 2`).

This is the *domination* input of the Fubini step of `LatGreenParsevalB`: it bounds the
ε-truncated heat integral of the periodic kernel by the local Coulomb kernel at the nearest
lattice point, which hypothesis **(B)** of the target (absolute integrability against
`K_♯ = ℓ²latGreen(ℓ⁻¹·)`) then dominates.

Route: `|heatPeriod s u − 1| ≤ heatPeriod s u + 1` and
`∫_{(0,ε]} heatPeriod s u ds = Σ_n ∫_{(0,ε]} heatK3 s (u − n) ds` (Tonelli, nonnegative terms).
For `n ∈ latBox` use `∫_{(0,ε]} ≤ ∫_0^∞ heatK3 = 1/(4π‖u−n‖)` (`HeatIntegral`); for
`n ∉ latBox` (so `‖u − n‖ ≥ 3`, since some `|n i| ≥ 5` while `|u i| ≤ 2`) use the head bound
`∫_{(0,ε]} (4πs)^{−3/2}e^{−a/s} ds ≤ √ε e^{−a/ε}/(8π^{3/2}a)` with `a = ‖u−n‖²/4`
(`heatK3_head_le`), whose sum over `n ∉ latBox` is bounded uniformly in `u` and `ε ≤ 1`
(the summands decay like `e^{−‖u−n‖²/4}/‖u−n‖²`, summable over the lattice; a uniform bound for
the lattice Gaussian sum is supplied by `latticeGaussSum_le`, or by `heatPeriod_eq_tsum` at
`t = 1`).  The terms `ε` and the far sum are absorbed into `C·1`. -/
theorem HeatPeriodIocDomination :
    ∃ C : ℝ, ∀ ε : ℝ, 0 < ε → ε ≤ 1 → ∀ u : EuclideanSpace ℝ (Fin 3),
      (∀ i : Fin 3, |u i| ≤ 2) → (∀ n : Fin 3 → ℤ, u ≠ Work.BoseFixR.LatGreen.latVec n) →
        ∫ s in Set.Ioc 0 ε, |Work.BoseFixR.LatGreen.heatPeriod s u - 1|
          ≤ C * (1 + ∑ n ∈ Work.BoseFixR.LatGreen.latBox,
              1 / ‖u - Work.BoseFixR.LatGreen.latVec n‖) := by
  obtain ⟨K, hK⟩ := latSum_invSq_gauss_le
  refine ⟨1 / (4 * Real.pi) + max K 0 + 2, ?_⟩
  intro ε hε hε1 u hu2 hu
  set S : ℝ := ∑ n ∈ latBox, 1 / ‖u - latVec n‖ with hS
  have hSnn : 0 ≤ S := by
    rw [hS]
    exact Finset.sum_nonneg fun n _ => div_nonneg zero_le_one (norm_nonneg _)
  -- ### integrability of `heatPeriod · u` on `(0,ε]`
  have hint : IntegrableOn (fun s : ℝ => heatPeriod s u - 1) (Set.Ioi 0) := PeriodIntegrable hu
  have hintIoc : IntegrableOn (fun s : ℝ => heatPeriod s u - 1) (Set.Ioc 0 ε) :=
    hint.mono_set (fun x hx => hx.1)
  have hone : IntegrableOn (fun _ : ℝ => (1 : ℝ)) (Set.Ioc 0 ε) := by
    refine integrableOn_const (C := (1 : ℝ)) ?_ ?_
    · rw [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top
    · simp
  have hfint : IntegrableOn (fun s : ℝ => heatPeriod s u) (Set.Ioc 0 ε) := by
    have h := hintIoc.add hone
    refine h.congr_fun ?_ measurableSet_Ioc
    intro s hs
    simp
  have hplus : IntegrableOn (fun s : ℝ => heatPeriod s u + 1) (Set.Ioc 0 ε) := by
    have h := hfint.add hone
    refine h.congr_fun ?_ measurableSet_Ioc
    intro s hs
    simp
  -- ### pointwise bound and the integral comparison
  have hpt : ∀ s ∈ Set.Ioc 0 ε, |heatPeriod s u - 1| ≤ heatPeriod s u + 1 := by
    intro s hs
    have h0 : 0 ≤ heatPeriod s u := heatPeriod_nonneg s hs.1 u
    rw [abs_sub_le_iff]
    exact ⟨by linarith, by linarith⟩
  have hmono : ∫ s in Set.Ioc 0 ε, |heatPeriod s u - 1|
      ≤ ∫ s in Set.Ioc 0 ε, (heatPeriod s u + 1) := by
    refine integral_mono_of_nonneg ?_ hplus ?_
    · exact Filter.Eventually.of_forall (fun s => abs_nonneg _)
    · filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
      exact hpt s hs
  have hconst : ∫ s in Set.Ioc 0 ε, (1 : ℝ) = ε := by
    rw [setIntegral_const, Real.volume_real_Ioc, max_eq_left (by linarith : (0 : ℝ) ≤ ε - 0),
      sub_zero, smul_eq_mul, mul_one]
  have hsum1 : ∫ s in Set.Ioc 0 ε, (heatPeriod s u + 1)
      = (∫ s in Set.Ioc 0 ε, heatPeriod s u) + ε := by
    have h := integral_add (μ := MeasureTheory.volume.restrict (Set.Ioc 0 ε))
      (f := fun s : ℝ => heatPeriod s u) (g := fun _ : ℝ => (1 : ℝ)) hfint hone
    rw [hconst] at h
    exact h
  -- ### Tonelli: the time integral of `heatPeriod` is the series of heat-kernel integrals
  have hTon : ∫ s in Set.Ioc 0 ε, heatPeriod s u
      = ∑' n : Fin 3 → ℤ, ∫ s in Set.Ioc 0 ε, heatK3 s (u - latVec n) :=
    integral_heatPeriod_Ioc_eq_tsum hε hε1 hu2 hu
  -- ### the two comparison families and the majorant
  set T : (Fin 3 → ℤ) → ℝ := fun n =>
    (1 / ‖u - latVec n‖ ^ 2) * Real.exp (-‖u - latVec n‖ ^ 2 / 4) with hT
  set A : (Fin 3 → ℤ) → ℝ := fun n => 1 / (4 * Real.pi * ‖u - latVec n‖) with hA
  set Q : (Fin 3 → ℤ) → ℝ := fun n => if n ∈ latBox then 0 else T n with hQ
  set P : (Fin 3 → ℤ) → ℝ := fun n => if n ∈ latBox then A n else 0 with hP
  have hQsumm : Summable Q := (hK u hu2).1
  have hPsumm : Summable P := by
    refine summable_of_ne_finset_zero (s := latBox) (fun b hb => ?_)
    simp only [hP, if_neg hb]
  have hPQsumm : Summable (fun n : Fin 3 → ℤ => P n + Q n) := hPsumm.add hQsumm
  have hTnn : ∀ n : Fin 3 → ℤ, 0 ≤ T n := by
    intro n
    rw [hT]
    exact mul_nonneg (div_nonneg zero_le_one (sq_nonneg _)) (Real.exp_nonneg _)
  -- pointwise domination of each time-integral
  have hterm_le : ∀ n : Fin 3 → ℤ,
      (∫ s in Set.Ioc 0 ε, heatK3 s (u - latVec n)) ≤ P n + Q n := by
    intro n
    by_cases hn : n ∈ latBox
    · have hx : u - latVec n ≠ 0 := sub_ne_zero.mpr (hu n)
      have h1 := heatK3_ioc_integral_le_green hε hx
      have hAn : A n = 1 / (4 * Real.pi * ‖u - latVec n‖) := by rw [hA]
      simp only [hP, hQ, hn, if_true, if_false, add_zero, hAn]
      exact h1
    · have h3 : 3 ≤ ‖u - latVec n‖ := latBox_notMem_norm_ge_three hu2 hn
      have h1 := heatK3_ioc_integral_le_gauss hε hε1 h3
      have hQn : Q n = T n := by simp only [hQ, if_neg hn]
      have hcoef : 1 / (2 * Real.pi ^ (3 / 2 : ℝ)) ≤ 1 := by
        rw [div_le_one (by positivity)]
        have hpi : (1 : ℝ) ≤ Real.pi ^ (3 / 2 : ℝ) :=
          Real.one_le_rpow (le_trans (by norm_num : (1 : ℝ) ≤ 3) (le_of_lt Real.pi_gt_three))
            (by norm_num)
        linarith
      rw [show P n + Q n = T n from by simp only [hP, if_neg hn, zero_add, hQn]]
      calc (∫ s in Set.Ioc 0 ε, heatK3 s (u - latVec n))
          ≤ 1 / (2 * Real.pi ^ (3 / 2 : ℝ))
              * (1 / ‖u - latVec n‖ ^ 2) * Real.exp (-‖u - latVec n‖ ^ 2 / 4) := h1
        _ = (1 / (2 * Real.pi ^ (3 / 2 : ℝ))) * T n := by rw [hT]; ring
        _ ≤ 1 * T n := mul_le_mul_of_nonneg_right hcoef (hTnn n)
        _ = T n := one_mul _
  have hFsumm : Summable (fun n : Fin 3 → ℤ => ∫ s in Set.Ioc 0 ε, heatK3 s (u - latVec n)) :=
    Summable.of_nonneg_of_le
      (f := fun n : Fin 3 → ℤ => P n + Q n)
      (g := fun n : Fin 3 → ℤ => ∫ s in Set.Ioc 0 ε, heatK3 s (u - latVec n))
      (fun n => setIntegral_nonneg measurableSet_Ioc
        (fun s hs => heatK3_nonneg hs.1 (u - latVec n)))
      hterm_le hPQsumm
  have htsum_le : (∑' n : Fin 3 → ℤ, ∫ s in Set.Ioc 0 ε, heatK3 s (u - latVec n))
      ≤ ∑' n : Fin 3 → ℤ, (P n + Q n) :=
    Summable.tsum_le_tsum hterm_le hFsumm hPQsumm
  have hPval : (∑' n : Fin 3 → ℤ, P n) = ∑ n ∈ latBox, A n := by
    rw [hP]
    rw [tsum_eq_sum (s := latBox) (fun b hb => by simp only [if_neg hb])]
    exact Finset.sum_congr rfl (fun b hb => by simp only [if_pos hb])
  have hQle : (∑' n : Fin 3 → ℤ, Q n) ≤ max K 0 := by
    have hQeq : (fun n : Fin 3 → ℤ => Q n)
        = (fun n : Fin 3 → ℤ => if n ∈ latBox then 0 else
            (1 / ‖u - latVec n‖ ^ 2) * Real.exp (-‖u - latVec n‖ ^ 2 / 4)) := by
      funext n
      simp only [hQ, hT]
    rw [hQeq]
    exact le_trans (hK u hu2).2 (le_max_left _ _)
  have hAval : ∑ n ∈ latBox, A n = (1 / (4 * Real.pi)) * S := by
    rw [hS]
    have h1 : ∑ n ∈ latBox, A n
        = ∑ n ∈ latBox, (1 / (4 * Real.pi)) * (1 / ‖u - latVec n‖) := by
      refine Finset.sum_congr rfl (fun n _ => ?_)
      rw [hA]
      rcases eq_or_ne ‖u - latVec n‖ 0 with h0 | h0
      · simp [h0]
      · field_simp
    calc ∑ n ∈ latBox, A n
        = ∑ n ∈ latBox, (1 / (4 * Real.pi)) * (1 / ‖u - latVec n‖) := h1
      _ = (1 / (4 * Real.pi)) * ∑ n ∈ latBox, 1 / ‖u - latVec n‖ := by rw [Finset.mul_sum]
  have hFbound : (∑' n : Fin 3 → ℤ, ∫ s in Set.Ioc 0 ε, heatK3 s (u - latVec n))
      ≤ (1 / (4 * Real.pi)) * S + max K 0 := by
    calc (∑' n : Fin 3 → ℤ, ∫ s in Set.Ioc 0 ε, heatK3 s (u - latVec n))
        ≤ ∑' n : Fin 3 → ℤ, (P n + Q n) := htsum_le
      _ = (∑' n : Fin 3 → ℤ, P n) + ∑' n : Fin 3 → ℤ, Q n := hPsumm.tsum_add hQsumm
      _ ≤ (∑ n ∈ latBox, A n) + max K 0 := by rw [hPval]; linarith [hQle]
      _ = (1 / (4 * Real.pi)) * S + max K 0 := by rw [hAval]
  -- ### assembly
  calc ∫ s in Set.Ioc 0 ε, |heatPeriod s u - 1|
      ≤ ∫ s in Set.Ioc 0 ε, (heatPeriod s u + 1) := hmono
    _ = (∫ s in Set.Ioc 0 ε, heatPeriod s u) + ε := hsum1
    _ = (∑' n : Fin 3 → ℤ, ∫ s in Set.Ioc 0 ε, heatK3 s (u - latVec n)) + ε := by rw [hTon]
    _ ≤ ((1 / (4 * Real.pi)) * S + max K 0) + ε := by linarith [hFbound]
    _ ≤ ((1 / (4 * Real.pi)) * S + max K 0) + 1 := by linarith [hε1]
    _ ≤ (1 / (4 * Real.pi) + max K 0 + 2) * (1 + S) := by
        have hmax : 0 ≤ max K 0 := le_max_right K 0
        have hpi : 0 < 1 / (4 * Real.pi) := by positivity
        nlinarith [hSnn, hmax]

end Work.BoseFixR.LatGreen
