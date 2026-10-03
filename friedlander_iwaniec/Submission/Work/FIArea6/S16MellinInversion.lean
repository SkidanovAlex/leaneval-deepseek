import Mathlib
import Submission.Work.FIArea5.S16.mellin_decay
import Submission.Work.FIArea5.S16.mellin_ibp
import Submission.Work.FIArea5.S16.p_endpoint_zero

/-!
# Mellin inversion for a smooth bump supported on `(N, (1+θ)N]`  (*FI* §16)

For a `C²` bump function `p` with `0 ≤ p ≤ 1`, supported in `(N, (1+θ)N]`, and with second
derivative bounded by `2^20 (θN)^{-2}`, the inverse Mellin transform of the Mellin transform
of `p` reproduces `p` at every `n > 0`, uniformly for `σ ∈ [1/2, 2]`:

`mellinInv σ (mellin p) n = p n`.

The proof combines Mathlib's Mellin inversion formula `mellinInv_mellin_eq` with the vertical
decay `mellin p (σ + it) ≪ θ N^σ (1 + θ²t²)^{-1}` established in `FIArea5/S16/mellin_decay`.
Ingredients:

* **Support reduction** (`S16MellinSupport`): `p` vanishes off `(N, (1+θ)N]`, so the Mellin
  integral over `(0, ∞)` collapses to the interval integral over `N .. (1+θ)N`.
* **Vertical integrability**: `s ↦ mellin p (σ + is)` is a.e. dominated by
  `10^7 θ N^σ (1 + θ²s²)^{-1}` (`S16MellinVerticalBound`, from `mellin_decay`), which is
  integrable on `ℝ` (`S16InvSqIntegrable`), and it is continuous
  (`S16MellinVerticalContinuous`).
* **Mellin convergence** `MellinConvergent p σ` (`S16MellinConvergent`), from the compact
  support and continuity of `p`.
-/

open MeasureTheory
open scoped Topology

namespace Work.FIArea6

theorem S16MellinSupport (p : ℝ → ℝ) (N B : ℝ) (hN : 0 < N) (hNB : N ≤ B)
    (hsupp : ∀ u, p u ≠ 0 → N < u ∧ u ≤ B) (s : ℂ) :
    mellin (fun u : ℝ => (p u : ℂ)) s = ∫ u in N..B, (u : ℂ) ^ (s - 1) * (p u : ℂ) := by
  have hzero : ∀ u, (u ≤ N ∨ B < u) → p u = 0 := by
    intro u hu
    by_contra h
    rcases hsupp u h with ⟨h1, h2⟩
    rcases hu with h3 | h3
    · exact absurd h1 (not_lt.mpr h3)
    · exact absurd h2 (not_le.mpr h3)
  have hmain : ∫ u : ℝ in Set.Ioi (0:ℝ), (u : ℂ) ^ (s - 1) • (p u : ℂ)
      = ∫ u : ℝ in Set.Ioc N B, (u : ℂ) ^ (s - 1) • (p u : ℂ) := by
    refine setIntegral_eq_of_subset_of_ae_sdiff_eq_zero ?_ ?_ ?_
    · exact measurableSet_Ioi.nullMeasurableSet
    · intro u hu
      exact hN.trans hu.1
    · filter_upwards with u hu
      rcases hu with ⟨hu0, hnot⟩
      have hcase : u ≤ N ∨ B < u := by
        by_cases h : N < u
        · by_cases h' : u ≤ B
          · exact absurd ⟨h, h'⟩ hnot
          · exact Or.inr (not_le.mp h')
        · exact Or.inl (not_lt.mp h)
      rw [hzero u hcase, Complex.ofReal_zero, smul_zero]
  have hL : mellin (fun u : ℝ => (p u : ℂ)) s
      = ∫ u : ℝ in Set.Ioi (0:ℝ), (u : ℂ) ^ (s - 1) • (p u : ℂ) := rfl
  rw [hL, hmain, ← intervalIntegral.integral_of_le hNB]
  refine intervalIntegral.integral_congr ?_
  intro u hu
  rfl

theorem S16InvSqIntegrable (θ C : ℝ) (hθ : θ ≠ 0) :
    Integrable (fun y : ℝ => C * (1 + (θ * y) ^ 2)⁻¹) := by
  have h : Integrable (fun y : ℝ => (1 + y^2)⁻¹) := integrable_inv_one_add_sq
  have h2 : Integrable (fun y : ℝ => (1 + (θ*y)^2)⁻¹) := h.comp_mul_left' hθ
  simpa using h2.const_mul C

theorem S16MellinConvergent (p : ℝ → ℝ) (N B σ : ℝ) (hN : 0 < N) (hNB : N ≤ B)
    (hpC : Continuous p) (hp1 : ∀ u, |p u| ≤ 1)
    (hsupp : ∀ u, p u ≠ 0 → N < u ∧ u ≤ B) :
    MellinConvergent (fun u : ℝ => (p u : ℂ)) σ := by
  have hzero : ∀ u, (u ≤ N ∨ B < u) → p u = 0 := by
    intro u hu
    by_contra h
    rcases hsupp u h with ⟨h1, h2⟩
    rcases hu with h3 | h3
    · exact absurd h1 (not_lt.mpr h3)
    · exact absurd h2 (not_le.mpr h3)
  have hG : ∀ u, (u ≤ N ∨ B < u) → (u : ℂ) ^ ((σ:ℂ) - 1) • (p u : ℂ) = 0 := by
    intro u hu; rw [hzero u hu, Complex.ofReal_zero, smul_zero]
  have h1 : IntegrableOn (fun u : ℝ => (u:ℂ)^((σ:ℂ)-1) • (p u:ℂ)) (Set.Ioc 0 N) := by
    refine (integrableOn_congr_fun ?_ measurableSet_Ioc).mp integrableOn_zero
    intro u hu
    exact (hG u (Or.inl hu.2)).symm
  have h2 : IntegrableOn (fun u : ℝ => (u:ℂ)^((σ:ℂ)-1) • (p u:ℂ)) (Set.Ioc N B) := by
    have hcontIcc : ContinuousOn (fun t : ℝ => t ^ (σ - 1)) (Set.Icc N B) := by
      intro t ht
      exact (Real.continuousAt_rpow_const t (σ - 1) (Or.inl (ne_of_gt (hN.trans_le ht.1)))).continuousWithinAt
    have hb : IntegrableOn (fun t : ℝ => t ^ (σ - 1)) (Set.Ioc N B) volume :=
      (hcontIcc.integrableOn_compact isCompact_Icc).mono_set Set.Ioc_subset_Icc_self
    refine Integrable.mono' hb ?_ ?_
    · have hcont : ContinuousOn (fun u : ℝ => (u:ℂ)^((σ:ℂ)-1) • (p u:ℂ)) (Set.Ioc N B) := by
        intro t ht
        have ht0 : (t:ℝ) ≠ 0 := ne_of_gt (hN.trans ht.1)
        have h1' : ContinuousAt (fun u : ℝ => (u:ℂ)^((σ:ℂ)-1)) t :=
          Complex.continuousAt_ofReal_cpow_const t ((σ:ℂ)-1) (Or.inr ht0)
        have h2' : ContinuousAt (fun u : ℝ => (p u : ℂ)) t :=
          Complex.continuous_ofReal.continuousAt.comp hpC.continuousAt
        exact (h1'.smul h2').continuousWithinAt
      exact hcont.aestronglyMeasurable measurableSet_Ioc
    · filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
      have ht0 : (0:ℝ) < t := hN.trans ht.1
      have hre : ((σ:ℂ) - 1).re = σ - 1 := by simp
      have hone : ‖(t:ℂ)^((σ:ℂ)-1) • (p t : ℂ)‖ = t^(σ-1) * |p t| := by
        rw [norm_smul, Complex.norm_cpow_eq_rpow_re_of_pos ht0, hre, Complex.norm_real,
          Real.norm_eq_abs]
      rw [hone]
      have htσ : (0:ℝ) ≤ t^(σ-1) := Real.rpow_nonneg ht0.le _
      nlinarith [hp1 t, htσ]
  have h3 : IntegrableOn (fun u : ℝ => (u:ℂ)^((σ:ℂ)-1) • (p u:ℂ)) (Set.Ioi B) := by
    refine (integrableOn_congr_fun ?_ measurableSet_Ioi).mp integrableOn_zero
    intro u hu
    exact (hG u (Or.inr hu)).symm
  have hunion : IntegrableOn (fun u : ℝ => (u:ℂ)^((σ:ℂ)-1) • (p u:ℂ))
      (Set.Ioc 0 N ∪ (Set.Ioc N B ∪ Set.Ioi B)) := h1.union (h2.union h3)
  have hset : Set.Ioc (0:ℝ) N ∪ (Set.Ioc N B ∪ Set.Ioi B) = Set.Ioi (0:ℝ) := by
    ext u; constructor
    · intro hu; rcases hu with h | h | h
      · exact h.1
      · exact hN.trans h.1
      · exact (hN.trans_le hNB).trans h
    · intro hu
      by_cases h : u ≤ N
      · exact Or.inl ⟨hu, h⟩
      · have hNu : N < u := not_le.mp h
        by_cases h' : u ≤ B
        · exact Or.inr (Or.inl ⟨hNu, h'⟩)
        · exact Or.inr (Or.inr (not_le.mp h'))
  rw [hset] at hunion
  exact hunion

theorem S16MellinVerticalBound (p : ℝ → ℝ) (N θ σ : ℝ) (hN : 0 < N) (hθ : 0 < θ) (hθ1 : θ ≤ 1)
    (hpC : ContDiff ℝ 2 p) (hp0 : ∀ u, 0 ≤ p u) (hp1 : ∀ u, p u ≤ 1)
    (hpsupp : ∀ u, p u ≠ 0 → N < u ∧ u ≤ (1 + θ) * N)
    (hd2 : ∀ u, |iteratedDeriv 2 p u| ≤ 1048576 / (θ * N) ^ 2)
    (hσ : 1 / 2 ≤ σ) (hσ2 : σ ≤ 2) (y : ℝ) (hy : y ≠ 0) :
    ‖mellin (fun u : ℝ => (p u : ℂ)) ((σ : ℂ) + (y : ℂ) * Complex.I)‖
      ≤ 10000000 * θ * N ^ σ * (1 + (θ * y) ^ 2)⁻¹ := by
  have hB : N ≤ (1 + θ) * N := by nlinarith
  rw [S16MellinSupport p N ((1 + θ) * N) hN hB hpsupp ((σ:ℂ) + (y:ℂ) * Complex.I)]
  have h := Work.FIArea5.S16.mellin_decay p N θ hN hθ hθ1 hpC hp0 hp1 hpsupp hd2 σ y hσ hσ2 hy
  have h' : (∫ u in N..(1+θ)*N, (u:ℂ)^(((σ:ℂ)+(y:ℂ)*Complex.I)-1) * (p u:ℂ))
          = (∫ u in N..(1+θ)*N, (p u:ℂ) * (u:ℂ)^(((σ:ℂ)+(y:ℂ)*Complex.I)-1)) := by
    apply intervalIntegral.integral_congr
    intro u hu
    ring
  rw [h']
  exact h

theorem S16MellinVerticalContinuous (p : ℝ → ℝ) (N B σ : ℝ) (hN : 0 < N) (hNB : N ≤ B)
    (hpC : Continuous p) (hp1 : ∀ u, |p u| ≤ 1) (hσ : 0 < σ)
    (hsupp : ∀ u, p u ≠ 0 → N < u ∧ u ≤ B) :
    Continuous (fun y : ℝ => mellin (fun u : ℝ => (p u : ℂ)) ((σ : ℂ) + (y : ℂ) * Complex.I)) := by
  have hb : IntervalIntegrable (fun u : ℝ => u ^ (σ-1)) volume N B :=
    intervalIntegral.intervalIntegrable_rpow' (by linarith)
  rw [continuous_iff_continuousAt]
  intro y₀
  have heq : (fun y : ℝ => mellin (fun u : ℝ => (p u : ℂ)) ((σ:ℂ) + (y:ℂ)*Complex.I))
      = (fun y : ℝ => ∫ u in N..B, (u:ℂ)^(((σ:ℂ) + (y:ℂ)*Complex.I) - 1) * (p u : ℂ)) := by
    funext y
    exact S16MellinSupport p N B hN hNB hsupp _
  rw [heq]
  refine intervalIntegral.continuousAt_of_dominated_interval
    (F := fun (y : ℝ) (u : ℝ) => (u:ℂ)^(((σ:ℂ)+(y:ℂ)*Complex.I)-1) * (p u : ℂ))
    (μ := volume) (bound := fun u : ℝ => u^(σ-1)) ?_ ?_ hb ?_
  · filter_upwards with y
    have hcont : ContinuousOn (fun u : ℝ => (u:ℂ)^(((σ:ℂ)+(y:ℂ)*Complex.I)-1) * (p u:ℂ)) (Set.uIoc N B) := by
      intro t ht
      rw [Set.uIoc_of_le hNB] at ht
      have ht0 : (t:ℝ) ≠ 0 := ne_of_gt (hN.trans ht.1)
      exact ((Complex.continuousAt_ofReal_cpow_const t (((σ:ℂ)+(y:ℂ)*Complex.I)-1) (Or.inr ht0)).mul
        (Complex.continuous_ofReal.continuousAt.comp hpC.continuousAt)).continuousWithinAt
    exact hcont.aestronglyMeasurable measurableSet_uIoc
  · filter_upwards with y
    refine Filter.Eventually.of_forall (fun t ht => ?_)
    rw [Set.uIoc_of_le hNB] at ht
    have ht0 : (0:ℝ) < t := hN.trans ht.1
    have hone : ‖(t:ℂ)^(((σ:ℂ)+(y:ℂ)*Complex.I)-1)‖ = t^(σ-1) := by
      rw [Complex.norm_cpow_eq_rpow_re_of_pos ht0]
      congr 1
      simp
    rw [norm_mul, hone, Complex.norm_real, Real.norm_eq_abs]
    nlinarith [hp1 t, Real.rpow_nonneg ht0.le (σ-1)]
  · filter_upwards with t ht
    rw [Set.uIoc_of_le hNB] at ht
    have ht0 : (t:ℂ) ≠ 0 := by
      norm_cast; exact ne_of_gt (hN.trans ht.1)
    have hc : ContinuousAt (fun y : ℝ => (t:ℂ) ^ (((σ:ℂ)+(y:ℂ)*Complex.I)-1)) y₀ :=
      (continuousAt_const_cpow (a := (t:ℂ)) ht0).comp (by fun_prop)
    exact hc.mul continuousAt_const

theorem S16MellinInversion (p : ℝ → ℝ) (N θ σ n : ℝ) (hN : 0 < N) (hθ : 0 < θ) (hθ1 : θ ≤ 1)
    (hpC : ContDiff ℝ 2 p) (hp0 : ∀ u, 0 ≤ p u) (hp1 : ∀ u, p u ≤ 1)
    (hpsupp : ∀ u, p u ≠ 0 → N < u ∧ u ≤ (1 + θ) * N)
    (hd2 : ∀ u, |iteratedDeriv 2 p u| ≤ 1048576 / (θ * N) ^ 2)
    (hσ : 1 / 2 ≤ σ) (hσ2 : σ ≤ 2) (hn : 0 < n) :
    mellinInv σ (mellin (fun u : ℝ => (p u : ℂ))) n = (p n : ℂ) := by
  have hB : N ≤ (1 + θ) * N := by nlinarith
  have hσpos : 0 < σ := by linarith
  have hpabs : ∀ u, |p u| ≤ 1 := fun u => abs_le.mpr ⟨by linarith [hp0 u], hp1 u⟩
  set f : ℝ → ℂ := fun u => (p u : ℂ) with hfdef
  have hconv : MellinConvergent f σ := by
    have h := S16MellinConvergent p N ((1+θ)*N) σ hN hB hpC.continuous hpabs hpsupp
    simpa [hfdef] using h
  have hcont : Continuous (fun y : ℝ => mellin f ((σ:ℂ) + (y:ℂ)*Complex.I)) := by
    have h := S16MellinVerticalContinuous p N ((1+θ)*N) σ hN hB hpC.continuous hpabs hσpos hpsupp
    simpa [hfdef] using h
  have hDint : Integrable (fun y : ℝ => 10000000 * θ * N^σ * (1 + (θ*y)^2)⁻¹) :=
    S16InvSqIntegrable θ (10000000 * θ * N^σ) hθ.ne'
  have hbnd : ∀ᵐ y : ℝ ∂volume,
      ‖mellin f ((σ:ℂ) + (y:ℂ)*Complex.I)‖ ≤ 10000000 * θ * N^σ * (1 + (θ*y)^2)⁻¹ := by
    filter_upwards [Measure.ae_ne volume 0] with y hy
    have h := S16MellinVerticalBound p N θ σ hN hθ hθ1 hpC hp0 hp1 hpsupp hd2 hσ hσ2 y hy
    simpa [hfdef] using h
  have hint : Integrable (fun y : ℝ => mellin f ((σ:ℂ) + (y:ℂ)*Complex.I)) volume :=
    Integrable.mono' hDint hcont.aestronglyMeasurable hbnd
  have hvert : Complex.VerticalIntegrable (mellin f) σ := hint
  have hfx : ContinuousAt f n :=
    Complex.continuous_ofReal.continuousAt.comp hpC.continuous.continuousAt
  have hfinal := mellinInv_mellin_eq σ f hn hconv hvert hfx
  simpa [hfdef] using hfinal

end Work.FIArea6
