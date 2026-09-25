import Mathlib
import Submission.Work.BourgainPlan.Oscillation.Lacunary.cesaro_defs

namespace Work.BourgainPlan.Oscillation.Lacunary

open MeasureTheory intervalIntegral
open scoped ComplexConjugate

/-! ## Auxiliary pointwise conjugation identities

The reflection `θ ↦ 1 - θ` turns the planewave `e(θ) = exp (2πiθ)` into its conjugate, up to
the harmless factor `e(1) = 1`; the same holds for `e(-xθ)` when `x` is an integer.  These are
the pointwise ingredients of the half-circle symmetry of the Cesàro integral. -/

private lemma star_exp_int_shift (j : ℤ) (ε : ℝ) :
    (starRingEnd ℂ) (Complex.exp (2 * Real.pi * Complex.I * ((j:ℂ) * (((1:ℝ) - ε : ℝ):ℂ))))
      = Complex.exp (2 * Real.pi * Complex.I * ((j:ℂ) * (ε:ℂ))) := by
  have harg : 2 * Real.pi * Complex.I * ((j:ℂ) * (((1:ℝ) - ε : ℝ):ℂ))
      = (-(2 * Real.pi * Complex.I * ((j:ℂ) * (ε:ℂ)))) + (j:ℂ) * (2 * Real.pi * Complex.I) := by
    push_cast; ring
  rw [harg, Complex.exp_add, exp_int_mul_two_pi_I, mul_one]
  rw [← Complex.exp_conj]
  congr 1
  simp only [map_neg, map_mul, map_ofNat, Complex.conj_ofReal, Complex.conj_I, map_intCast]
  ring

private lemma star_exp_int_shift' (x : ℤ) (ε : ℝ) :
    (starRingEnd ℂ) (Complex.exp (-(2 * Real.pi * Complex.I * ((x:ℤ):ℂ) * (((1:ℝ) - ε : ℝ):ℂ))))
      = Complex.exp (-(2 * Real.pi * Complex.I * ((x:ℤ):ℂ) * (ε:ℂ))) := by
  have harg : -(2 * Real.pi * Complex.I * ((x:ℤ):ℂ) * (((1:ℝ) - ε : ℝ):ℂ))
      = (2 * Real.pi * Complex.I * ((x:ℤ):ℂ) * (ε:ℂ)) + ((-x : ℤ):ℂ) * (2 * Real.pi * Complex.I) := by
    push_cast; ring
  rw [harg, Complex.exp_add, exp_int_mul_two_pi_I, mul_one]
  rw [← Complex.exp_conj]
  congr 1
  simp only [map_mul, map_ofNat, Complex.conj_ofReal, Complex.conj_I, map_intCast]
  ring

/-- The half-circle symmetry `m_N(1-ε) = conj (m_N ε)` combined with the factorisation
`m_N(ε) = r(ε) · h(Nε)` on `(0, 1/2]`, where `r` is the truncated weight `cesRT`. -/
private lemma star_cesM_one_sub (N : ℕ) (hN : 1 ≤ N) {ε : ℝ} (hε : ε ∈ Set.Ioc (0:ℝ) (1/2)) :
    (starRingEnd ℂ) (cesM N (1 - ε)) = cesRT ε * cesH ((N:ℝ) * ε) := by
  have hε1 : ε ∈ Set.Ioc (0:ℝ) 1 := ⟨hε.1, by linarith [hε.2]⟩
  have hsym := cesM_conj_symm N hε1
  have hcs : (starRingEnd ℂ) (cesM N (1 - ε)) = cesM N ε := by
    rw [hsym, Complex.conj_conj]
  rw [hcs, cesM_eq_cesH_cesR N hN hε1]
  have hRT : cesRT ε = cesR ε := by
    rw [cesRT, if_pos ⟨hε.1, hε.2⟩]
  rw [hRT]
  ring

theorem cesaro_second_half (N : ℕ) (hN : 1 ≤ N) (x : ℤ) (f : ℤ → ℂ) (s : Finset ℤ)
    (hs : ∀ n, n ∉ s → f n = 0) :
    (∫ θ in ((1:ℝ)/2)..1,
        Work.BourgainPlan.Oscillation.Lacunary.cesM N θ *
        (∑ j ∈ s, f j * Complex.exp (2 * Real.pi * Complex.I * ((j : ℂ) * (θ : ℂ)))) *
        Complex.exp (-(2 * Real.pi * Complex.I * ((x : ℤ) : ℂ) * (θ : ℂ))))
      = (starRingEnd ℂ) (∫ ε in (0:ℝ)..1,
        (Work.BourgainPlan.Oscillation.Lacunary.cesRT ε *
          Work.BourgainPlan.Oscillation.Lacunary.cesH ((N : ℝ) * ε)) *
        (∑ j ∈ s, (starRingEnd ℂ) (f j) * Complex.exp (2 * Real.pi * Complex.I * ((j : ℂ) * (ε : ℂ)))) *
        Complex.exp (-(2 * Real.pi * Complex.I * ((x : ℤ) : ℂ) * (ε : ℂ)))) := by
  set G : ℝ → ℂ := fun θ => cesM N θ *
        (∑ j ∈ s, f j * Complex.exp (2 * Real.pi * Complex.I * ((j : ℂ) * (θ : ℂ)))) *
        Complex.exp (-(2 * Real.pi * Complex.I * ((x : ℤ) : ℂ) * (θ : ℂ))) with hG
  set H : ℝ → ℂ := fun ε => (cesRT ε * cesH ((N : ℝ) * ε)) *
        (∑ j ∈ s, (starRingEnd ℂ) (f j) * Complex.exp (2 * Real.pi * Complex.I * ((j : ℂ) * (ε : ℂ)))) *
        Complex.exp (-(2 * Real.pi * Complex.I * ((x : ℤ) : ℂ) * (ε : ℂ))) with hH
  have key : ∀ ε ∈ Set.Ioc (0:ℝ) (1/2),
      (starRingEnd ℂ) (cesM N (1 - ε) *
          (∑ j ∈ s, f j * Complex.exp (2 * Real.pi * Complex.I * ((j:ℂ) * (((1:ℝ) - ε : ℝ):ℂ)))) *
          Complex.exp (-(2 * Real.pi * Complex.I * ((x:ℤ):ℂ) * (((1:ℝ) - ε : ℝ):ℂ))))
        = (cesRT ε * cesH ((N:ℝ) * ε)) *
          (∑ j ∈ s, (starRingEnd ℂ) (f j) * Complex.exp (2 * Real.pi * Complex.I * ((j:ℂ) * (ε:ℂ)))) *
          Complex.exp (-(2 * Real.pi * Complex.I * ((x:ℤ):ℂ) * (ε:ℂ))) := by
    intro ε hε
    have hsum : (starRingEnd ℂ) (∑ j ∈ s, f j * Complex.exp (2 * Real.pi * Complex.I * ((j:ℂ) * (((1:ℝ)-ε : ℝ):ℂ))))
        = ∑ j ∈ s, (starRingEnd ℂ) (f j) * Complex.exp (2 * Real.pi * Complex.I * ((j:ℂ) * (ε:ℂ))) := by
      rw [map_sum]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [map_mul]
      congr 1
      exact star_exp_int_shift j ε
    rw [map_mul, map_mul, star_cesM_one_sub N hN hε, hsum, star_exp_int_shift' x ε]
  have h1 : (starRingEnd ℂ) (∫ θ in ((1:ℝ)/2)..1, G θ)
      = ∫ θ in ((1:ℝ)/2)..1, (starRingEnd ℂ) (G θ) := by
    rw [integral_of_le (by norm_num : ((1:ℝ)/2) ≤ 1)]
    rw [← integral_conj]
    rw [integral_of_le (by norm_num : ((1:ℝ)/2) ≤ 1)]
  have h2 : ∫ θ in ((1:ℝ)/2)..1, (starRingEnd ℂ) (G θ)
      = ∫ ε in (0:ℝ)..((1:ℝ)/2), (starRingEnd ℂ) (G (1 - ε)) := by
    have hcomp := intervalIntegral.integral_comp_sub_left (a := ((1:ℝ)/2)) (b := 1)
      (f := fun y : ℝ => (starRingEnd ℂ) (G (1 - y))) (1:ℝ)
    rw [show (1:ℝ) - 1 = 0 by norm_num,
        show (1:ℝ) - ((1:ℝ)/2) = ((1:ℝ)/2) by norm_num] at hcomp
    simpa only [sub_sub_cancel] using hcomp
  have h3 : ∫ ε in (0:ℝ)..((1:ℝ)/2), (starRingEnd ℂ) (G (1 - ε))
      = ∫ ε in (0:ℝ)..((1:ℝ)/2), H ε := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards with ε hε
    have hk := key ε (by rwa [Set.uIoc_of_le (by norm_num : (0:ℝ) ≤ (1:ℝ)/2)] at hε)
    rw [hG, hH]
    exact hk
  have h4 : ∫ ε in (0:ℝ)..((1:ℝ)/2), H ε = ∫ ε in (0:ℝ)..1, H ε := by
    rw [integral_of_le (by norm_num : (0:ℝ) ≤ (1:ℝ)/2)]
    rw [integral_of_le (by norm_num : (0:ℝ) ≤ 1)]
    rw [← MeasureTheory.integral_indicator (f := H) measurableSet_Ioc,
        ← MeasureTheory.integral_indicator (f := H) measurableSet_Ioc]
    apply MeasureTheory.integral_congr_ae
    filter_upwards with y
    by_cases hy : y ∈ Set.Ioc (0:ℝ) 1
    · by_cases hy2 : y ≤ (1:ℝ)/2
      · have hm : y ∈ Set.Ioc (0:ℝ) ((1:ℝ)/2) := ⟨hy.1, hy2⟩
        rw [Set.indicator_of_mem hm, Set.indicator_of_mem hy]
      · have hn : y ∉ Set.Ioc (0:ℝ) ((1:ℝ)/2) := fun hc => hy2 hc.2
        have hz : H y = 0 := by
          have hc : ¬(0 < y ∧ y ≤ (1:ℝ)/2) := fun h => hy2 h.2
          simp only [hH, cesRT, if_neg hc, zero_mul]
        rw [Set.indicator_of_notMem hn, Set.indicator_of_mem hy, hz]
    · have hn : y ∉ Set.Ioc (0:ℝ) ((1:ℝ)/2) :=
        fun hc => hy ⟨hc.1, le_trans hc.2 (by norm_num)⟩
      rw [Set.indicator_of_notMem hn, Set.indicator_of_notMem hy]
  have hmain : (starRingEnd ℂ) (∫ θ in ((1:ℝ)/2)..1, G θ) = ∫ ε in (0:ℝ)..1, H ε :=
    h1.trans (h2.trans (h3.trans h4))
  calc (∫ θ in ((1:ℝ)/2)..1, G θ)
      = (starRingEnd ℂ) ((starRingEnd ℂ) (∫ θ in ((1:ℝ)/2)..1, G θ)) := by simp
    _ = (starRingEnd ℂ) (∫ ε in (0:ℝ)..1, H ε) := by rw [hmain]

end Work.BourgainPlan.Oscillation.Lacunary
