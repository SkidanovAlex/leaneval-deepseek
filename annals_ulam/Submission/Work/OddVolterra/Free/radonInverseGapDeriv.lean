import Mathlib
import Submission.Work.OddCurve.LowSlope.gapKernel_derivs
import Submission.Work.OddRadon.Abel
import Submission.Work.OddCurve.LowSlope.abel_integral_trig_substitution_no_hyp
import Submission.Work.OddVolterra.Free.gap_inversion_bounds_free

/-!
# Smoothness of the Abel inversion of a datum supported in a gap (free tips)

`Work.OddRadon.radonInverse n δ` is the Abel inversion of the reduced datum
`Φ = abelReduceIter (n - 3/2) (n - 1) ((2 |S^{2n-2}|)⁻¹ c^{2n-2} δ)`: it is
`(2/π)` times the derivative of the classical Abel integral `v ↦ ∫₀^v c Φ c / √(v²-c²) dc`.

If `δ` is smooth on `(0,1)` and vanishes on `(0,m)` and beyond `M'`, where
`0 < m ≤ M' < 79/100`, then `Φ` is again supported in `[m,M']` and continuous there;
for `v > M'` the Abel integral therefore collapses to the nonsingular gap integral
`∫_m^{M'} c Φ c (v²-c²)^{-1/2} dc`, whose three successive derivatives exist by
`Work.OddCurve.LowSlope.gapKernel_derivs`.  Consequently `radonInverse n δ` and its
derivative are differentiable on `[4/5, 1]`.

This is the differentiability half of `Work.OddVolterra.Free.gap_inversion_bounds_free`
(the *bounds* there use the extra hypothesis `δ = radonProfile (2n+1) γ`, which the
smoothness statement does not need).
-/

namespace Work.OddVolterra.Free

open MeasureTheory Set Filter
open scoped Topology Interval

noncomputable section

/-- **The Abel integral of a gap-supported datum is the gap integral.**

If `G` vanishes on `(0,m)` and beyond `M'`, then for every `v > M'` the (singular)
Abel integral of `G` over `(0,v)` equals the nonsingular integral over the gap `[m,M']`,
with the kernel written as a `rpow`.  This is
`Work.OddVolterra.Free.abelIntegral_eq_gapIntegral` with the artificial hypothesis
`v < 1` removed (it is not needed: the datum vanishes beyond `M'` *globally*). -/
private lemma abelIntegral_eq_gapIntegral' {m M' v : ℝ} (hm : 0 < m) (hmM' : m ≤ M')
    (hM'v : M' < v) {G : ℝ → ℝ} (hGl : ∀ c ∈ Set.Ioo 0 m, G c = 0)
    (hGr : ∀ c : ℝ, M' < c → G c = 0) :
    (∫ c in (0 : ℝ)..v, c * G c / Real.sqrt (v ^ 2 - c ^ 2))
      = ∫ c in m..M', c * G c * (v ^ 2 - c ^ 2) ^ (-(1 / 2 : ℝ)) := by
  have hv0 : 0 < v := lt_trans (lt_of_lt_of_le hm hmM') hM'v
  set f : ℝ → ℝ := fun c => c * G c * (v ^ 2 - c ^ 2) ^ (-(1 / 2 : ℝ)) with hf
  have hstep1 : (∫ c in (0 : ℝ)..v, c * G c / Real.sqrt (v ^ 2 - c ^ 2))
      = ∫ c in (0 : ℝ)..v, f c := by
    apply intervalIntegral.integral_congr
    intro c hc
    rw [Set.uIcc_of_le hv0.le] at hc
    have hnn : 0 ≤ v ^ 2 - c ^ 2 := by nlinarith [hc.1, hc.2]
    simp only [hf]
    rw [Real.sqrt_eq_rpow, Real.rpow_neg hnn, div_eq_mul_inv]
  rw [hstep1, intervalIntegral.integral_of_le hv0.le, intervalIntegral.integral_of_le hmM']
  have h1 : ∫ x in Set.Ioc (0 : ℝ) v, f x = ∫ x in Set.Icc m M', f x := by
    refine MeasureTheory.setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioc ?_ ?_
    · intro x hx
      exact ⟨lt_of_lt_of_le hm hx.1, le_of_lt (lt_of_le_of_lt hx.2 hM'v)⟩
    · intro x hx
      obtain ⟨hx1, hx2⟩ := hx
      rcases lt_or_ge x m with h | h
      · have hxI : x ∈ Set.Ioo 0 m := ⟨hx1.1, h⟩
        simp only [hf]
        rw [hGl x hxI]
        ring
      · have hxM' : M' < x := by
          by_contra hh
          exact hx2 ⟨h, le_of_not_gt hh⟩
        simp only [hf]
        rw [hGr x hxM']
        ring
  have h2 : ∫ x in Set.Icc m M', f x = ∫ x in Set.Ioc m M', f x :=
    MeasureTheory.setIntegral_congr_set
      (MeasureTheory.Ioc_ae_eq_Icc (μ := volume) (a := m) (b := M')).symm
  rw [h1, h2]

theorem radonInverseGapDeriv (n : ℕ) (hn : 1 ≤ n) {δ : ℝ → ℝ} {m M' : ℝ}
    (hm : 0 < m) (hmM' : m ≤ M') (hM' : M' < (79 / 100 : ℝ))
    (hδ : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) δ (Set.Ioo (0 : ℝ) 1))
    (hδl : ∀ c ∈ Set.Ioo (0 : ℝ) 1, c < m → δ c = 0)
    (hδr : ∀ c : ℝ, M' < c → δ c = 0) :
    ∀ u ∈ Set.Icc (4 / 5 : ℝ) 1,
      DifferentiableAt ℝ (fun v : ℝ => Work.OddRadon.radonInverse n δ v) u ∧
      DifferentiableAt ℝ (deriv (fun v : ℝ => Work.OddRadon.radonInverse n δ v)) u := by
  intro u hu
  -- ### the reduced datum and the reduced-to-gap function
  set α : ℝ := (n : ℝ) - 3 / 2 with hαdef
  set Ψ : ℝ → ℝ :=
    fun c => (2 * Work.OddRadon.sphereArea (2 * n - 2))⁻¹ * c ^ (2 * n - 2) * δ c with hΨdef
  set G : ℝ → ℝ := Work.OddRadon.abelReduceIter α (n - 1) Ψ with hGdef
  set Bfun : ℝ → ℝ := fun w => ∫ c in (0 : ℝ)..w, c * G c / Real.sqrt (w ^ 2 - c ^ 2) with hBfundef
  -- ### basic numeric facts
  have hm0 : (0 : ℝ) ≤ m := le_of_lt hm
  have hM'1 : M' < 1 := lt_trans hM' (by norm_num)
  have hm1 : m < 1 := lt_of_le_of_lt hmM' hM'1
  have hM'u : M' < u := lt_of_lt_of_le hM' (show (79 / 100 : ℝ) ≤ u by linarith [hu.1])
  -- ### 1. smoothness of the reduced datum on `(0,1)`
  have hΨ_smooth : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Ψ (Set.Ioo (0 : ℝ) 1) := by
    rw [hΨdef]
    have hpoly : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun c : ℝ => (2 * Work.OddRadon.sphereArea (2 * n - 2))⁻¹ * c ^ (2 * n - 2))
        (Set.Ioo (0 : ℝ) 1) := by fun_prop
    simpa [mul_assoc] using hpoly.mul hδ
  have hG_smooth : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) G (Set.Ioo (0 : ℝ) 1) := by
    rw [hGdef]
    refine abelReduceIter_contDiffOn (β := α) (k := n - 1) ?_ hΨ_smooth
    intro j hj
    have hnc : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by rw [Nat.cast_sub hn]; norm_num
    have h2 : (j : ℝ) + 1 ≤ ((n - 1 : ℕ) : ℝ) := by
      have : j + 1 ≤ n - 1 := by omega
      exact_mod_cast this
    rw [hnc] at h2
    rw [hαdef]
    intro hzero
    linarith
  have hG_cont : ContinuousOn G (Set.Icc m M') :=
    hG_smooth.continuousOn.mono (fun x hx => ⟨lt_of_lt_of_le hm hx.1, lt_of_le_of_lt hx.2 hM'1⟩)
  -- ### 2. vanishing of the reduced datum off the gap
  have hΨ_zero_l : Set.EqOn Ψ 0 (Set.Ioo (0 : ℝ) m) := by
    intro c hc
    rw [hΨdef]
    simp only [Pi.zero_apply]
    rw [hδl c ⟨hc.1, lt_trans hc.2 hm1⟩ hc.2]
    ring
  have hG_zero_l : ∀ c ∈ Set.Ioo (0 : ℝ) m, G c = 0 := by
    have h := Work.OddRadon.abelReduceIter_congr_open isOpen_Ioo (n - 1) α hΨ_zero_l
    intro c hc
    rw [hGdef, h hc, Work.OddVolterra.Free.abelReduceIter_zero]
    simp
  have hΨ_zero_r : Set.EqOn Ψ 0 (Set.Ioi M') := by
    intro c hc
    rw [hΨdef]
    simp only [Pi.zero_apply]
    rw [hδr c hc]
    ring
  have hG_zero_r : ∀ c : ℝ, M' < c → G c = 0 := by
    have h := Work.OddRadon.abelReduceIter_congr_open isOpen_Ioi (n - 1) α hΨ_zero_r
    intro c hc
    rw [hGdef, h hc, Work.OddVolterra.Free.abelReduceIter_zero]
    simp
  -- ### 3. the gap kernel family and its first three derivatives
  obtain ⟨B, hB⟩ := (isCompact_Icc (a := m) (b := M')).exists_bound_of_continuousOn hG_cont
  have hBabs : ∀ c ∈ Set.Icc m M', |G c| ≤ B := by
    intro c hc
    have h := hB c hc
    rwa [Real.norm_eq_abs] at h
  have hgap := Work.OddCurve.LowSlope.gapKernel_derivs (m := m) (M' := M') (B := B)
    hm0 hmM' hM' hG_cont hBabs
  set I : ℝ → ℝ := fun v => ∫ c in m..M', c * G c * (v ^ 2 - c ^ 2) ^ (-(1 / 2 : ℝ)) with hIdef
  set J1 : ℝ → ℝ :=
    fun v => ∫ c in m..M', c * G c * (-v * (v ^ 2 - c ^ 2) ^ (-(3 / 2 : ℝ))) with hJ1def
  set J2 : ℝ → ℝ :=
    fun v => ∫ c in m..M', c * G c * ((2 * v ^ 2 + c ^ 2) * (v ^ 2 - c ^ 2) ^ (-(5 / 2 : ℝ)))
    with hJ2def
  set J3 : ℝ → ℝ :=
    fun v => ∫ c in m..M', c * G c * ((-(6 * v ^ 3) - 9 * v * c ^ 2) * (v ^ 2 - c ^ 2) ^ (-(7 / 2 : ℝ)))
    with hJ3def
  have hu79 : (79 / 100 : ℝ) < u := by linarith [hu.1]
  have hu11 : u < (11 / 10 : ℝ) := by linarith [hu.2]
  have huS : u ∈ Set.Ioo (79 / 100 : ℝ) (11 / 10) := ⟨hu79, hu11⟩
  have hd1 : ∀ v ∈ Set.Ioo (79 / 100 : ℝ) (11 / 10), HasDerivAt I (J1 v) v := by
    intro v hv; simpa [hIdef, hJ1def] using (hgap v hv).1
  have hd2 : ∀ v ∈ Set.Ioo (79 / 100 : ℝ) (11 / 10), HasDerivAt J1 (J2 v) v := by
    intro v hv; simpa [hJ1def, hJ2def] using (hgap v hv).2.1
  have hd3 : ∀ v ∈ Set.Ioo (79 / 100 : ℝ) (11 / 10), HasDerivAt J2 (J3 v) v := by
    intro v hv; simpa [hJ2def, hJ3def] using (hgap v hv).2.2
  -- ### 4. `Bfun` agrees with the gap integral above the gap
  have hcmp : ∀ v : ℝ, M' < v → Bfun v = I v := by
    intro v hv
    rw [hBfundef, hIdef]
    exact abelIntegral_eq_gapIntegral' hm hmM' hv hG_zero_l hG_zero_r
  -- ### 5. eventual equalities at `u`
  have hS_nhds : Set.Ioo (79 / 100 : ℝ) (11 / 10) ∈ 𝓝 u := isOpen_Ioo.mem_nhds huS
  have hS'_nhds : (Set.Ioo (79 / 100 : ℝ) (11 / 10) ∩ Set.Ioi M') ∈ 𝓝 u :=
    Filter.inter_mem hS_nhds (isOpen_Ioi.mem_nhds hM'u)
  have hBfunI : Bfun =ᶠ[𝓝 u] I := by
    filter_upwards [hS'_nhds] with v hv
    exact hcmp v hv.2
  have hdI_J1 : deriv I =ᶠ[𝓝 u] J1 := by
    filter_upwards [hS_nhds] with v hv
    exact (hd1 v hv).deriv
  have hdJ1_J2 : deriv J1 =ᶠ[𝓝 u] J2 := by
    filter_upwards [hS_nhds] with v hv
    exact (hd2 v hv).deriv
  have hF0J : deriv Bfun =ᶠ[𝓝 u] J1 := hBfunI.deriv.trans hdI_J1
  have hF1J : deriv (deriv Bfun) =ᶠ[𝓝 u] J2 := hF0J.deriv.trans hdJ1_J2
  have hF0diff : DifferentiableAt ℝ (deriv Bfun) u :=
    (Filter.EventuallyEq.differentiableAt_iff hF0J).mpr (hd2 u huS).differentiableAt
  have hF1diff : DifferentiableAt ℝ (deriv (deriv Bfun)) u :=
    (Filter.EventuallyEq.differentiableAt_iff hF1J).mpr (hd3 u huS).differentiableAt
  -- ### 6. `radonInverse` and its derivative
  have hGval : G = Work.OddRadon.abelReduceIter ((n : ℝ) - 3 / 2) (n - 1)
      (fun c => (2 * Work.OddRadon.sphereArea (2 * n - 2))⁻¹ * c ^ (2 * n - 2) * δ c) := by
    simp only [hGdef, hαdef, hΨdef]
  have hR0 : ∀ v : ℝ, Work.OddRadon.radonInverse n δ v = (2 / Real.pi) * deriv Bfun v := by
    intro v
    simp only [Work.OddRadon.radonInverse, Work.OddRadon.abelInvert, hBfundef, hGval]
  have hRfun : (fun v : ℝ => Work.OddRadon.radonInverse n δ v)
      = fun v => (2 / Real.pi) * deriv Bfun v := funext hR0
  have hR1 : deriv (fun v : ℝ => Work.OddRadon.radonInverse n δ v)
      = fun v => (2 / Real.pi) * deriv (deriv Bfun) v := by
    rw [hRfun]
    funext v
    exact deriv_const_mul_uncond (2 / Real.pi) (deriv Bfun) v
  refine ⟨?_, ?_⟩
  · rw [hRfun]
    exact hF0diff.const_mul (2 / Real.pi)
  · rw [hR1]
    exact hF1diff.const_mul (2 / Real.pi)

end

end Work.OddVolterra.Free
