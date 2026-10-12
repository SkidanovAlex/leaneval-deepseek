import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBoxFock.PotCubicLowBandAux.selfPairG
import Submission.Work.BoseBoxFock.boxAnnOf_norm_sq_le
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseBoxFock.PotCubicLowBandAux

noncomputable section

open MeasureTheory
open scoped BigOperators

local notation "Ω" => EuclideanSpace ℝ (Fin 3)

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## Auxiliary: the squared norm of a bounded box state is integrable

These are the one-particle and `n`-particle instances of the elementary fact that a measurable,
everywhere bounded function supported in the corpus box has an integrable squared norm (the box
has finite volume).  They produce the `MemLp _ 2` hypotheses of
`Work.BoseBoxFock.boxAnnOf_norm_sq_le`. -/

/-- The squared norm of a bounded measurable one-particle function supported in the corpus box
`boxL ℓ` is integrable (against Lebesgue measure on `ℝ³`). -/
private theorem integrable_normSq_of_bounded_boxL {ℓ : ℝ} {η : Ω → ℂ}
    (hηm : Measurable η) (hηb : ∃ C : ℝ, ∀ z, ‖η z‖ ≤ C)
    (hηs : Function.support η ⊆ Work.BoseK15.corpusBox.boxL ℓ) :
    MeasureTheory.Integrable (fun z : Ω => ‖η z‖ ^ 2) := by
  obtain ⟨C, hC⟩ := hηb
  refine MeasureTheory.Integrable.mono'
    (g := (Work.BoseK15.corpusBox.boxL ℓ).indicator (fun _ => (max C 0) ^ 2)) ?_ ?_ ?_
  · rw [integrable_indicator_iff
      (Work.BoseB4.BoxData.boxL_measurableSet Work.BoseK15.corpusBox ℓ)]
    exact integrableOn_const
      (Work.BoseB4.BoxData.boxL_compact Work.BoseK15.corpusBox ℓ).measure_lt_top.ne
  · exact (hηm.norm.pow_const 2).aestronglyMeasurable
  · filter_upwards with z
    by_cases hz : z ∈ Work.BoseK15.corpusBox.boxL ℓ
    · rw [Set.indicator_of_mem hz]
      have h1 : (0 : ℝ) ≤ ‖η z‖ ^ 2 := by positivity
      rw [Real.norm_eq_abs, abs_of_nonneg h1]
      exact pow_le_pow_left₀ (norm_nonneg _) ((hC z).trans (le_max_left _ _)) 2
    · rw [Set.indicator_of_notMem hz]
      have h0 : η z = 0 := Function.notMem_support.mp (fun h => hz (hηs h))
      rw [h0]
      simp

/-- The squared norm of a bounded measurable `n`-particle function supported in the corpus box
`boxPow n ℓ` is integrable. -/
private theorem integrable_normSq_of_bounded_boxPow {n : ℕ} {ℓ : ℝ}
    {Θ : Work.BoseDict.Xn n → ℂ}
    (hΘm : Measurable Θ) (hΘb : ∃ C : ℝ, ∀ x, ‖Θ x‖ ≤ C)
    (hΘs : Function.support Θ ⊆ Work.MB.boxPow n ℓ) :
    MeasureTheory.Integrable (fun x : Work.BoseDict.Xn n => ‖Θ x‖ ^ 2) := by
  obtain ⟨C, hC⟩ := hΘb
  refine MeasureTheory.Integrable.mono'
    (g := (Work.MB.boxPow n ℓ).indicator (fun _ => (max C 0) ^ 2)) ?_ ?_ ?_
  · rw [integrable_indicator_iff (Work.MB.measurableSet_boxPow n ℓ)]
    exact integrableOn_const (Work.MB.volume_boxPow_lt_top n ℓ)
  · exact (hΘm.norm.pow_const 2).aestronglyMeasurable
  · filter_upwards with x
    by_cases hx : x ∈ Work.MB.boxPow n ℓ
    · rw [Set.indicator_of_mem hx]
      have h1 : (0 : ℝ) ≤ ‖Θ x‖ ^ 2 := by positivity
      rw [Real.norm_eq_abs, abs_of_nonneg h1]
      exact pow_le_pow_left₀ (norm_nonneg _) ((hC x).trans (le_max_left _ _)) 2
    · rw [Set.indicator_of_notMem hx]
      have h0 : Θ x = 0 := Function.notMem_support.mp (fun h => hx (hΘs h))
      rw [h0]
      simp

/-- The superposition at the coordinate vector `e_0` is the mode `e 0`. -/
private theorem etaOf_evec_zero {m : ℕ} [NeZero m] (e : Fin m → Ω → ℂ) :
    Work.BoseDict.etaOf e (Work.BoseB4.evec m 0) = e 0 := by
  funext z
  simp only [Work.BoseDict.etaOf, Work.BoseB4.evec, Pi.single_apply]
  rw [Finset.sum_eq_single (0 : Fin m)]
  · simp
  · intro b _ hb
    simp [hb]
  · intro h
    exact absurd (Finset.mem_univ (0 : Fin m)) h

theorem cIPn_evecZero_boxAnnOf_le {m d : ℕ} [NeZero m] {ℓ : ℝ}
    {e : Fin m → EuclideanSpace ℝ (Fin 3) → ℂ}
    (hmeas : ∀ l, Measurable (e l)) (hbdd : ∀ l, ∃ C : ℝ, ∀ x, ‖e l x‖ ≤ C)
    (hsupp : ∀ l, Function.support (e l) ⊆ Work.BoseK15.corpusBox.boxL ℓ)
    (horth : ∀ l l', (∫ z : EuclideanSpace ℝ (Fin 3), star (e l z) * e l' z)
      = (if l = l' then (1 : ℂ) else 0))
    {φ : Work.BoseDict.Xn (d + 1) → ℂ}
    (hφm : Measurable φ) (hφb : ∃ C : ℝ, ∀ x, ‖φ x‖ ≤ C)
    (hφsupp : Function.support φ ⊆ Work.MB.boxPow (d + 1) ℓ) :
    (Work.BoseDict.cIPn d
        (Work.BoseDict.boxAnnOf e (Work.BoseB4.evec m 0) d φ)
        (Work.BoseDict.boxAnnOf e (Work.BoseB4.evec m 0) d φ)).re
      ≤ ((d : ℝ) + 2) * (Work.BoseDict.cIPn (d + 1) φ φ).re := by
  classical
  -- the superposed one-particle function is `e 0`, whose `L²`-mass is one by orthonormality
  have heta : Work.BoseDict.etaOf e (Work.BoseB4.evec m 0) = e 0 := etaOf_evec_zero e
  have hnorm_e0 : (∫ z : Ω, ‖e 0 z‖ ^ 2) = 1 := by
    have hpt : ∀ z : Ω, star (e 0 z) * e 0 z = ((‖e 0 z‖ ^ 2 : ℝ) : ℂ) := by
      intro z
      change (starRingEnd ℂ) (e 0 z) * e 0 z = ((‖e 0 z‖ ^ 2 : ℝ) : ℂ)
      rw [Complex.conj_mul', ← Complex.ofReal_pow]
    have hc : (∫ z : Ω, star (e 0 z) * e 0 z) = 1 := by
      simpa using horth 0 0
    have hcomplex : (∫ z : Ω, ((‖e 0 z‖ ^ 2 : ℝ) : ℂ)) = 1 := by
      rw [← hc]
      exact MeasureTheory.integral_congr_ae
        (Filter.Eventually.of_forall (fun z => (hpt z).symm))
    have hreal : ((∫ z : Ω, ‖e 0 z‖ ^ 2 : ℝ) : ℂ) = 1 := by
      rw [← integral_complex_ofReal]
      exact hcomplex
    exact Complex.ofReal_inj.mp hreal
  have hnorm_eta : (∫ z : Ω, ‖Work.BoseDict.etaOf e (Work.BoseB4.evec m 0) z‖ ^ 2) = 1 := by
    rw [heta]
    exact hnorm_e0
  -- the two `L²`-memberships entering the operator bound
  have hη_memLp : MeasureTheory.MemLp (Work.BoseDict.etaOf e (Work.BoseB4.evec m 0)) 2
      (MeasureTheory.volume : MeasureTheory.Measure Ω) := by
    obtain ⟨C, _hC0, hC⟩ := Work.MB.etaOf_weak_bound hbdd (Work.BoseB4.evec m 0)
    refine (MeasureTheory.memLp_two_iff_integrable_sq_norm
      (Work.MB.etaOf_weak_measurable hmeas (Work.BoseB4.evec m 0)).aestronglyMeasurable).mpr ?_
    exact integrable_normSq_of_bounded_boxL
      (Work.MB.etaOf_weak_measurable hmeas (Work.BoseB4.evec m 0)) ⟨C, hC⟩
      (Work.MB.etaOf_weak_support hsupp (Work.BoseB4.evec m 0))
  have hφ_memLp : MeasureTheory.MemLp φ 2
      (MeasureTheory.volume : MeasureTheory.Measure (Work.BoseDict.Xn (d + 1))) := by
    obtain ⟨C, hC⟩ := hφb
    refine (MeasureTheory.memLp_two_iff_integrable_sq_norm hφm.aestronglyMeasurable).mpr ?_
    exact integrable_normSq_of_bounded_boxPow hφm ⟨C, hC⟩ hφsupp
  -- the operator (Bessel) bound for the box annihilation
  have hmain := Work.BoseBoxFock.boxAnnOf_norm_sq_le (d := d) (e := e)
    (Work.BoseB4.evec m 0) hη_memLp hφ_memLp
  rw [hnorm_eta] at hmain
  -- convert the pairings into squared norms
  rw [Work.BoseBoxFock.cIPn_self_re
        (Work.BoseDict.boxAnnOf e (Work.BoseB4.evec m 0) d φ),
      Work.BoseBoxFock.cIPn_self_re φ]
  have hJ : 0 ≤ ∫ x : Work.BoseDict.Xn (d + 1), ‖φ x‖ ^ 2 :=
    MeasureTheory.integral_nonneg (fun x => sq_nonneg _)
  refine hmain.trans ?_
  calc ((d : ℝ) + 1) * 1 * (∫ x : Work.BoseDict.Xn (d + 1), ‖φ x‖ ^ 2)
      = ((d : ℝ) + 1) * (∫ x : Work.BoseDict.Xn (d + 1), ‖φ x‖ ^ 2) := by ring
    _ ≤ ((d : ℝ) + 2) * (∫ x : Work.BoseDict.Xn (d + 1), ‖φ x‖ ^ 2) :=
        mul_le_mul_of_nonneg_right (by linarith) hJ

end

end Work.BoseBoxFock.PotCubicLowBandAux
