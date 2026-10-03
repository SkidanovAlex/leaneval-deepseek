import Mathlib

/-!
# The fundamental lemma of the calculus of variations (complex form)

If a continuous complex-valued function `g` on an open set `U ⊆ ℂ` has `∫_U g ψ = 0` against every
`C¹` compactly supported test function `ψ` supported in `U`, then `g ≡ 0` on `U`.

This is the *localisation* step of Weyl's lemma: it turns a weak equation (a statement about
pairings against test functions) into a pointwise statement.

The proof is the classical one: if `g z₀ ≠ 0`, take the *complex* test function `Φ = Ψ · conj (g z₀)`
with `Ψ` a non-negative real bump concentrated in a small disc around `z₀`.  On that disc
`Re (g z · conj (g z₀)) ≥ ‖g z₀‖²/2`, so `∫ g Φ` has real part `≥ (‖g z₀‖²/2) ∫ Ψ > 0`.
-/

open MeasureTheory Set
open scoped Topology

noncomputable section

namespace Work.Analysis.Complex.DbarCauchy

/-- **A test function detecting a non-zero value.**  For `g` continuous on the open `U` and
`g z₀ ≠ 0`, `z₀ ∈ U`, there is a `C¹` compactly supported `Φ` with `tsupport Φ ⊆ U` and
`∫ z in U, g z * Φ z ≠ 0`. -/
theorem exists_testFunction_integral_ne_zero {U : Set ℂ} (hU : IsOpen U) {g : ℂ → ℂ}
    (hg : ContinuousOn g U) {z₀ : ℂ} (hz₀ : z₀ ∈ U) (hz : g z₀ ≠ 0) :
    ∃ Φ : ℂ → ℂ, ContDiff ℝ 1 Φ ∧ HasCompactSupport Φ ∧ tsupport Φ ⊆ U ∧
      (∫ z in U, g z * Φ z) ≠ 0 := by
  set c : ℂ := g z₀ with hcdef
  have hc : c ≠ 0 := hz
  have hcle : (0 : ℝ) < ‖c‖ ^ 2 := by positivity
  have hcont : ContinuousAt (fun z : ℂ => (g z * (starRingEnd ℂ) c).re) z₀ :=
    Complex.continuous_re.continuousAt.comp
      ((hg.continuousAt (hU.mem_nhds hz₀)).mul continuousAt_const)
  have hval : (g z₀ * (starRingEnd ℂ) c).re = ‖c‖ ^ 2 := by
    rw [← hcdef, Complex.mul_conj', pow_two, ← Complex.ofReal_mul, Complex.ofReal_re]
    ring
  obtain ⟨r₁, hr₁, h₁⟩ := Metric.continuousAt_iff.mp hcont (‖c‖ ^ 2 / 2) (by positivity)
  obtain ⟨r₂, hr₂, h₂⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds hz₀)
  set ρ : ℝ := min r₁ r₂ with hρdef
  have hρ : 0 < ρ := lt_min hr₁ hr₂
  have hρU : Metric.ball z₀ ρ ⊆ U :=
    (Metric.ball_subset_ball (min_le_right _ _)).trans h₂
  have hpt : ∀ z ∈ Metric.ball z₀ ρ, ‖c‖ ^ 2 / 2 ≤ (g z * (starRingEnd ℂ) c).re := by
    intro z hz'
    have hlt : dist z z₀ < r₁ := lt_of_lt_of_le hz' (min_le_left _ _)
    have h := h₁ hlt
    rw [Real.dist_eq, hval] at h
    have h2 := abs_lt.mp h
    linarith [h2.1]
  obtain ⟨Ψ, hΨsupp, hΨc, hΨcd, hΨrange, hΨ1⟩ :=
    exists_contDiff_tsupport_subset (E := ℂ) (s := Metric.ball z₀ ρ) (x := z₀) (n := 1)
      (Metric.ball_mem_nhds z₀ hρ)
  have hΨnn : ∀ z, 0 ≤ Ψ z := fun z => (hΨrange (mem_range_self z)).1
  have hΨint : 0 < ∫ z, Ψ z := by
    have hne : Ψ z₀ ≠ 0 := by rw [hΨ1]; norm_num
    have hsupp : Function.support Ψ ∈ 𝓝 z₀ :=
      hΨcd.continuous.continuousAt.eventually_ne hne
    exact (MeasureTheory.integral_pos_iff_support_of_nonneg_ae
      (Filter.Eventually.of_forall hΨnn)
      (hΨcd.continuous.integrable_of_hasCompactSupport hΨc)).mpr
      (MeasureTheory.Measure.measure_pos_of_mem_nhds _ hsupp)
  refine ⟨fun z : ℂ => (Ψ z : ℂ) * (starRingEnd ℂ) c, ?_, ?_, ?_, ?_⟩
  · exact (Complex.ofRealCLM.contDiff.comp hΨcd).mul contDiff_const
  · have h1 : HasCompactSupport (fun z : ℂ => (Ψ z : ℂ)) := by
      have hsm := hΨc.smul_right (f' := fun _ : ℂ => (1 : ℂ))
      have hEq : (Ψ • fun _ : ℂ => (1 : ℂ)) = (fun z => (Ψ z : ℂ)) := by
        funext z; simp
      rwa [hEq] at hsm
    exact h1.smul_right (f' := fun _ : ℂ => (starRingEnd ℂ) c)
  · have hEq : tsupport (fun z : ℂ => (Ψ z : ℂ)) ⊆ tsupport Ψ :=
      closure_mono (fun z hz => by
        simp only [Function.mem_support] at hz ⊢
        intro h
        exact hz (by rw [h, Complex.ofReal_zero]))
    refine (closure_mono (fun z hz => ?_)).trans (hEq.trans (hΨsupp.trans hρU))
    simp only [Function.mem_support] at hz ⊢
    intro h
    exact hz (by rw [h, zero_mul])
  · intro hzero
    have hKU : tsupport Ψ ⊆ U := hΨsupp.trans hρU
    have hKc : IsCompact (tsupport Ψ) := hΨc
    have hzero' : ∫ z, g z * ((Ψ z : ℂ) * (starRingEnd ℂ) c) = 0 := by
      rw [← MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero (s := U)
        (f := fun z : ℂ => g z * ((Ψ z : ℂ) * (starRingEnd ℂ) c)) (fun z hz => ?_)]
      · exact hzero
      · rw [image_eq_zero_of_notMem_tsupport (fun h => hz (hKU h)), Complex.ofReal_zero,
            zero_mul, mul_zero]
    have hbig : ∫ z in tsupport Ψ, g z * ((Ψ z : ℂ) * (starRingEnd ℂ) c) = 0 := by
      rw [MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero (s := tsupport Ψ)
        (f := fun z : ℂ => g z * ((Ψ z : ℂ) * (starRingEnd ℂ) c)) (fun z hz => by
          rw [image_eq_zero_of_notMem_tsupport hz, Complex.ofReal_zero, zero_mul,
            mul_zero])]
      exact hzero'
    have hcontK : ContinuousOn (fun z : ℂ => g z * ((Ψ z : ℂ) * (starRingEnd ℂ) c)) (tsupport Ψ) :=
      (hg.mono hKU).mul (((Complex.continuous_ofReal.comp hΨcd.continuous).mul
        continuous_const).continuousOn)
    have hintK : IntegrableOn (fun z : ℂ => g z * ((Ψ z : ℂ) * (starRingEnd ℂ) c))
        (tsupport Ψ) :=
      ContinuousOn.integrableOn_compact hKc hcontK
    have hre : (∫ z in tsupport Ψ, g z * ((Ψ z : ℂ) * (starRingEnd ℂ) c)).re
        = ∫ z in tsupport Ψ, Ψ z * (g z * (starRingEnd ℂ) c).re := by
      change Complex.reCLM (∫ z in tsupport Ψ, g z * ((Ψ z : ℂ) * (starRingEnd ℂ) c))
          = ∫ z in tsupport Ψ, Ψ z * (g z * (starRingEnd ℂ) c).re
      rw [(ContinuousLinearMap.integral_comp_comm Complex.reCLM hintK).symm]
      refine MeasureTheory.setIntegral_congr_fun hKc.isClosed.measurableSet (fun z _ => ?_)
      simp only [Complex.reCLM_apply, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
        Complex.im_ofReal_mul, Complex.re_ofReal_mul, zero_mul, sub_zero]
      ring
    have hcont2 : ContinuousOn (fun z : ℂ => Ψ z * (g z * (starRingEnd ℂ) c).re) (tsupport Ψ) :=
      (hΨcd.continuous.continuousOn).mul
        (Complex.continuous_re.continuousOn.comp ((hg.mono hKU).mul continuousOn_const)
          (fun z _ => Set.mem_univ _))
    have hcont3 : ContinuousOn (fun z : ℂ => Ψ z * (‖c‖ ^ 2 / 2)) (tsupport Ψ) :=
      (hΨcd.continuous.continuousOn).mul continuousOn_const
    have hmono : ∫ z in tsupport Ψ, Ψ z * (‖c‖ ^ 2 / 2)
        ≤ ∫ z in tsupport Ψ, Ψ z * (g z * (starRingEnd ℂ) c).re := by
      refine MeasureTheory.setIntegral_mono
        (ContinuousOn.integrableOn_compact hKc hcont3)
        (ContinuousOn.integrableOn_compact hKc hcont2) (fun z => ?_)
      by_cases hz : z ∈ tsupport Ψ
      · exact mul_le_mul_of_nonneg_left (hpt z (hΨsupp hz)) (hΨnn z)
      · rw [image_eq_zero_of_notMem_tsupport hz, zero_mul, zero_mul]
    have heval : ∫ z in tsupport Ψ, Ψ z * (‖c‖ ^ 2 / 2) = (‖c‖ ^ 2 / 2) * ∫ z, Ψ z := by
      rw [← MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero (s := tsupport Ψ)
            (f := Ψ) (fun z hz => image_eq_zero_of_notMem_tsupport hz)]
      rw [show (fun z : ℂ => Ψ z * (‖c‖ ^ 2 / 2)) = (fun z : ℂ => (‖c‖ ^ 2 / 2) * Ψ z) from
        funext fun z => mul_comm _ _]
      rw [MeasureTheory.integral_const_mul]
    have hzre : (∫ z in tsupport Ψ, g z * ((Ψ z : ℂ) * (starRingEnd ℂ) c)).re = 0 := by
      rw [hbig]; rfl
    have hfinal : (0 : ℝ) < (‖c‖ ^ 2 / 2) * ∫ z, Ψ z := by
      have := mul_pos (by positivity : (0:ℝ) < ‖c‖ ^ 2 / 2) hΨint
      simpa using this
    rw [hre] at hzre
    rw [heval] at hmono
    linarith [hmono, hzre, hfinal]

end Work.Analysis.Complex.DbarCauchy
