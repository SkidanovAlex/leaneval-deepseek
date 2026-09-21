import Mathlib

set_option linter.unusedVariables false

noncomputable section

open Set Filter MeasureTheory
open scoped Topology Interval

namespace Work.VolterraLong

/-- Membership in a closed ball, stated with `‖y - x‖ ≤ r`. -/
lemma mem_closedBall_iff_norm {E : Type*} [NormedAddCommGroup E] {x y : E} {r : ℝ} :
    y ∈ Metric.closedBall x r ↔ ‖y - x‖ ≤ r := by
  rw [Metric.mem_closedBall, dist_eq_norm]

/-- Interval-integrability of the `Θ`-integrand along a continuous state curve which stays in the
ball of radius `r` around the base state `Z₀`: the integrand is continuous on the open interval
(where the state bound applies) and bounded there, and the two endpoints are negligible. -/
lemma intervalIntegrable_theta_integrand
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {Θ : ℝ → ℝ → E → E} {Z₀ : ℝ → E} {b₀ b₁ C r : ℝ}
    (hBd : ∀ s ∈ Set.Icc b₀ b₁, ∀ σ ∈ Set.Ioo s b₁,
      ∀ z ∈ Metric.closedBall (Z₀ σ) r, ‖Θ s σ z‖ ≤ C)
    (hCont : ∀ s ∈ Set.Icc b₀ b₁, ContinuousOn (fun p : ℝ × E => Θ s p.1 p.2)
      {p : ℝ × E | p.1 ∈ Set.Ioo s b₁ ∧ p.2 ∈ Metric.closedBall (Z₀ p.1) r})
    {s : ℝ} (hs : s ∈ Set.Icc b₀ b₁) (hsb₁ : s ≤ b₁)
    {Z : ℝ → E} (hZc : ContinuousOn Z (Set.Icc s b₁))
    (hZb : ∀ σ ∈ Set.Icc s b₁, ‖Z σ - Z₀ σ‖ ≤ r) :
    IntervalIntegrable (fun σ => Θ s σ (Z σ)) volume s b₁ := by
  have hopen : ContinuousOn (fun σ => Θ s σ (Z σ)) (Set.Ioo s b₁) := by
    refine ContinuousOn.comp (g := fun p : ℝ × E => Θ s p.1 p.2)
      (f := fun σ : ℝ => (σ, Z σ)) (hCont s hs) ?_ ?_
    · intro σ hσ
      refine ContinuousWithinAt.prodMk continuousWithinAt_id ?_
      exact (hZc.mono (fun x hx => ⟨hx.1.le, hx.2.le⟩)).continuousWithinAt hσ
    · intro σ hσ
      exact ⟨hσ, mem_closedBall_iff_norm.mpr (hZb σ ⟨hσ.1.le, hσ.2.le⟩)⟩
  have hmeas_open : AEStronglyMeasurable (fun σ => Θ s σ (Z σ))
      (volume.restrict (Set.Ioo s b₁)) :=
    hopen.aestronglyMeasurable isOpen_Ioo.measurableSet
  have hset : Set.Ioo s b₁ =ᵐ[(volume : Measure ℝ)] Set.Ioc s b₁ := by
    rw [MeasureTheory.ae_eq_set]
    constructor
    · have hempty : Set.Ioo s b₁ \ Set.Ioc s b₁ = ∅ := by
        rw [Set.sdiff_eq_empty.mpr]
        intro x hx
        exact ⟨hx.1, hx.2.le⟩
      rw [hempty]
      exact measure_empty
    · refine measure_mono_null (t := ({b₁} : Set ℝ)) ?_ (Real.volume_singleton (a := b₁))
      intro x hx
      rw [Set.mem_singleton_iff]
      by_contra hx1
      exact hx.2 ⟨hx.1.1, lt_of_le_of_ne hx.1.2 hx1⟩
  have hmeas : AEStronglyMeasurable (fun σ => Θ s σ (Z σ))
      (volume.restrict (Set.Ioc s b₁)) := by
    rw [← MeasureTheory.Measure.restrict_congr_set hset]
    exact hmeas_open
  have hbound : ∀ᵐ σ ∂(volume.restrict (Set.Ioc s b₁)),
      ‖Θ s σ (Z σ)‖ ≤ max C 0 := by
    have hbad : (volume : Measure ℝ)
        {σ : ℝ | σ ∈ Set.Ioc s b₁ ∧ ¬ (‖Θ s σ (Z σ)‖ ≤ max C 0)} = 0 := by
      refine measure_mono_null (t := ({b₁} : Set ℝ)) ?_ (Real.volume_singleton (a := b₁))
      intro σ hσ
      rw [Set.mem_singleton_iff]
      by_contra hσ1
      refine hσ.2 (le_trans (hBd s hs σ ⟨hσ.1.1, lt_of_le_of_ne hσ.1.2 hσ1⟩ (Z σ) ?_)
        (le_max_left _ _))
      exact mem_closedBall_iff_norm.mpr (hZb σ ⟨hσ.1.1.le, hσ.1.2⟩)
    rw [MeasureTheory.ae_restrict_iff' measurableSet_Ioc, MeasureTheory.ae_iff]
    refine measure_mono_null ?_ hbad
    intro x hx
    simp only [Set.mem_ofPred_eq] at hx ⊢
    exact Classical.not_imp.mp hx
  refine intervalIntegrable_iff.mpr ?_
  rw [Set.uIoc_of_le hsb₁]
  exact MeasureTheory.IntegrableOn.of_bound measure_Ioc_lt_top hmeas (max C 0) hbound

theorem GronwallUnique {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {b₀ b₁ : ℝ} (hb : b₀ < b₁)
    {G : ℝ → E → E} {Θ : ℝ → ℝ → E → E} {Ξ : ℝ → E} {Z₀ : ℝ → E}
    {L C c r : ℝ} (hL : 0 ≤ L) (hc : 0 < c) (hr : 0 < r)
    (hLip : ∀ s ∈ Set.Icc b₀ b₁, ∀ σ ∈ Set.Ioo s b₁,
      ∀ z ∈ Metric.closedBall (Z₀ σ) r, ∀ z' ∈ Metric.closedBall (Z₀ σ) r,
        ‖Θ s σ z - Θ s σ z'‖ ≤ L * ‖z - z'‖)
    (hBd : ∀ s ∈ Set.Icc b₀ b₁, ∀ σ ∈ Set.Ioo s b₁,
      ∀ z ∈ Metric.closedBall (Z₀ σ) r, ‖Θ s σ z‖ ≤ C)
    (hCont : ∀ s ∈ Set.Icc b₀ b₁, ContinuousOn (fun p : ℝ × E => Θ s p.1 p.2)
      {p : ℝ × E | p.1 ∈ Set.Ioo s b₁ ∧ p.2 ∈ Metric.closedBall (Z₀ p.1) r})
    (hInj : ∀ s ∈ Set.Icc b₀ b₁, ∀ z ∈ Metric.closedBall (Z₀ s) r,
      ∀ z' ∈ Metric.closedBall (Z₀ s) r, c * ‖z - z'‖ ≤ ‖G s z - G s z'‖)
    {Z W : ℝ → E} (hZc : ContinuousOn Z (Set.Icc b₀ b₁))
    (hWc : ContinuousOn W (Set.Icc b₀ b₁))
    (hZe : ∀ s ∈ Set.Ioo b₀ b₁, G s (Z s) = (∫ σ in s..b₁, Θ s σ (Z σ)) + Ξ s)
    (hWe : ∀ s ∈ Set.Ioo b₀ b₁, G s (W s) = (∫ σ in s..b₁, Θ s σ (W σ)) + Ξ s)
    (hZb : ∀ s ∈ Set.Icc b₀ b₁, ‖Z s - Z₀ s‖ ≤ r)
    (hWb : ∀ s ∈ Set.Icc b₀ b₁, ‖W s - Z₀ s‖ ≤ r) :
    ∀ s ∈ Set.Ioo b₀ b₁, Z s = W s := by
  -- the functional inequality obtained by subtracting the two equations
  have hkey : ∀ s ∈ Set.Ioo b₀ b₁,
      c * ‖Z s - W s‖ ≤ L * (∫ σ in s..b₁, ‖Z σ - W σ‖) := by
    intro s hs
    have hsb : s ∈ Set.Icc b₀ b₁ := ⟨hs.1.le, hs.2.le⟩
    have hZs : Z s ∈ Metric.closedBall (Z₀ s) r :=
      mem_closedBall_iff_norm.mpr (hZb s hsb)
    have hWs : W s ∈ Metric.closedBall (Z₀ s) r :=
      mem_closedBall_iff_norm.mpr (hWb s hsb)
    have hZsub : ContinuousOn Z (Set.Icc s b₁) :=
      hZc.mono (Set.Icc_subset_Icc_left hs.1.le)
    have hWsub : ContinuousOn W (Set.Icc s b₁) :=
      hWc.mono (Set.Icc_subset_Icc_left hs.1.le)
    have hIZ := intervalIntegrable_theta_integrand (Θ := Θ) (Z₀ := Z₀) hBd hCont hsb hs.2.le
      hZsub (fun σ hσ => hZb σ ⟨hs.1.le.trans hσ.1, hσ.2⟩)
    have hIW := intervalIntegrable_theta_integrand (Θ := Θ) (Z₀ := Z₀) hBd hCont hsb hs.2.le
      hWsub (fun σ hσ => hWb σ ⟨hs.1.le.trans hσ.1, hσ.2⟩)
    have hdiff : G s (Z s) - G s (W s)
        = ∫ σ in s..b₁, (Θ s σ (Z σ) - Θ s σ (W σ)) := by
      have hsub : (∫ σ in s..b₁, Θ s σ (Z σ)) + Ξ s -
            ((∫ σ in s..b₁, Θ s σ (W σ)) + Ξ s)
          = (∫ σ in s..b₁, Θ s σ (Z σ)) - (∫ σ in s..b₁, Θ s σ (W σ)) := by abel
      rw [hZe s hs, hWe s hs, hsub, ← intervalIntegral.integral_sub hIZ hIW]
    have hnorm : ‖∫ σ in s..b₁, (Θ s σ (Z σ) - Θ s σ (W σ))‖
        ≤ ∫ σ in s..b₁, L * ‖Z σ - W σ‖ := by
      refine intervalIntegral.norm_integral_le_of_norm_le hs.2.le ?_ ?_
      · have hbad : (volume : Measure ℝ)
            {x : ℝ | x ∈ Set.Ioc s b₁ ∧
              ¬ (‖Θ s x (Z x) - Θ s x (W x)‖ ≤ L * ‖Z x - W x‖)} = 0 := by
          refine measure_mono_null (t := ({b₁} : Set ℝ)) ?_ (Real.volume_singleton (a := b₁))
          intro x hx
          rw [Set.mem_singleton_iff]
          by_contra hx1
          refine hx.2 (hLip s hsb x ⟨hx.1.1, lt_of_le_of_ne hx.1.2 hx1⟩ (Z x) ?_ (W x) ?_)
          · exact mem_closedBall_iff_norm.mpr (hZb x ⟨hs.1.le.trans hx.1.1.le, hx.1.2⟩)
          · exact mem_closedBall_iff_norm.mpr (hWb x ⟨hs.1.le.trans hx.1.1.le, hx.1.2⟩)
        rw [MeasureTheory.ae_iff]
        refine measure_mono_null ?_ hbad
        intro x hx
        simp only [Set.mem_ofPred_eq] at hx ⊢
        exact Classical.not_imp.mp hx
      · have hcont' : ContinuousOn (fun σ => L * ‖Z σ - W σ‖) (Set.uIcc s b₁) :=
          ((hZc.sub hWc).norm.const_mul L).mono (fun x hx => by
            rw [Set.uIcc_of_le hs.2.le] at hx
            exact ⟨hs.1.le.trans hx.1, hx.2⟩)
        exact hcont'.intervalIntegrable
    calc c * ‖Z s - W s‖ ≤ ‖G s (Z s) - G s (W s)‖ :=
          hInj s hsb (Z s) hZs (W s) hWs
      _ = ‖∫ σ in s..b₁, (Θ s σ (Z σ) - Θ s σ (W σ))‖ := by rw [hdiff]
      _ ≤ ∫ σ in s..b₁, L * ‖Z σ - W σ‖ := hnorm
      _ = L * ∫ σ in s..b₁, ‖Z σ - W σ‖ := by
            rw [intervalIntegral.integral_const_mul]
  -- the tail distance function and the exponentially weighted Gronwall argument
  set H : ℝ → ℝ := fun σ => ‖Z (max b₀ (min σ b₁)) - W (max b₀ (min σ b₁))‖ with hH
  have hHcont : Continuous H := by
    have hclamp : Continuous fun σ : ℝ => max b₀ (min σ b₁) := by fun_prop
    have hmem : ∀ σ : ℝ, max b₀ (min σ b₁) ∈ Set.Icc b₀ b₁ := fun σ =>
      ⟨le_max_left _ _, max_le hb.le (min_le_right _ _)⟩
    have := (hZc.sub hWc).norm.comp_continuous hclamp hmem
    simpa only [hH, Function.comp_def, Pi.sub_apply] using this
  set g : ℝ → ℝ := fun s => ∫ σ in s..b₁, ‖Z σ - W σ‖ with hg
  have hkeyg : ∀ s ∈ Set.Ioo b₀ b₁, c * ‖Z s - W s‖ ≤ L * g s := by
    intro s hs
    simpa only [hg] using hkey s hs
  have hg_eq : ∀ s ∈ Set.Icc b₀ b₁, g s = ∫ σ in s..b₁, H σ := by
    intro s hs
    refine intervalIntegral.integral_congr ?_
    intro σ hσ
    rw [Set.uIcc_of_le hs.2] at hσ
    simp only [hH]
    rw [min_eq_left hσ.2, max_eq_right (le_trans hs.1 hσ.1)]
  have hgnonneg : ∀ s ≤ b₁, 0 ≤ g s := by
    intro s hle
    rw [hg]
    exact intervalIntegral.integral_nonneg hle (fun u _ => norm_nonneg _)
  have hgcont : ContinuousOn g (Set.Icc b₀ b₁) := by
    have hprim : Continuous fun u : ℝ => ∫ σ in b₁..u, H σ :=
      intervalIntegral.continuous_primitive (fun a b => hHcont.intervalIntegrable a b) b₁
    refine (hprim.neg.continuousOn).congr ?_
    intro s hs
    rw [hg_eq s hs, intervalIntegral.integral_symm]
    rfl
  have hgderiv : ∀ τ ∈ Set.Ioo b₀ b₁, HasDerivAt g (-(‖Z τ - W τ‖)) τ := by
    intro τ hτ
    have hcontτ : ContinuousAt (fun σ => ‖Z σ - W σ‖) τ :=
      ((hZc.continuousAt (Icc_mem_nhds hτ.1 hτ.2)).sub
        (hWc.continuousAt (Icc_mem_nhds hτ.1 hτ.2))).norm
    have hmeasτ : StronglyMeasurableAtFilter (fun σ => ‖Z σ - W σ‖) (𝓝 τ) volume :=
      ContinuousAt.stronglyMeasurableAtFilter (s := Set.Ioo b₀ b₁) isOpen_Ioo
        (fun x hx => ((hZc.continuousAt (Icc_mem_nhds hx.1 hx.2)).sub
          (hWc.continuousAt (Icc_mem_nhds hx.1 hx.2))).norm) τ hτ
    have hInt : IntervalIntegrable (fun σ => ‖Z σ - W σ‖) volume τ b₁ :=
      (((hZc.sub hWc).norm.mono (fun x hx => by
        rw [Set.uIcc_of_le hτ.2.le] at hx
        exact ⟨hτ.1.le.trans hx.1, hx.2⟩)).intervalIntegrable)
    have h := intervalIntegral.integral_hasDerivAt_left hInt hmeasτ hcontτ
    simpa only [hg] using h
  -- the exponential weight `exp (lam ·) g` is monotone from the right end
  set lam : ℝ := L / c with hlam
  intro s hs
  have hsb : s ∈ Set.Icc b₀ b₁ := ⟨hs.1.le, hs.2.le⟩
  have hmono : Real.exp (lam * s) * g s ≤ Real.exp (lam * b₁) * g b₁ := by
    have hφmono : MonotoneOn (fun τ => Real.exp (lam * τ) * g τ) (Set.Icc s b₁) := by
      refine monotoneOn_of_deriv_nonneg (convex_Icc s b₁) ?_ ?_ ?_
      · exact ((Real.continuous_exp.comp (continuous_const.mul continuous_id)).continuousOn).mul
          (hgcont.mono (fun x hx => ⟨hs.1.le.trans hx.1, hx.2⟩))
      · intro x hx
        rw [interior_Icc] at hx
        have hx' : x ∈ Set.Ioo b₀ b₁ := ⟨lt_trans hs.1 hx.1, hx.2⟩
        exact (((Real.hasDerivAt_exp _).comp x ((hasDerivAt_id x).const_mul lam)).mul
          (hgderiv x hx')).differentiableAt.differentiableWithinAt
      · intro x hx
        rw [interior_Icc] at hx
        have hx' : x ∈ Set.Ioo b₀ b₁ := ⟨lt_trans hs.1 hx.1, hx.2⟩
        have hderiv : deriv (fun τ : ℝ => Real.exp (lam * τ) * g τ) x
            = Real.exp (lam * x) * (lam * g x - ‖Z x - W x‖) := by
          have h1 : HasDerivAt (fun τ : ℝ => Real.exp (lam * τ)) (Real.exp (lam * x) * lam) x := by
            simpa using ((hasDerivAt_id x).const_mul lam).exp
          have h2 := h1.mul (hgderiv x hx')
          have h2d : deriv (fun τ : ℝ => Real.exp (lam * τ) * g τ) x
              = Real.exp (lam * x) * lam * g x + Real.exp (lam * x) * (-(‖Z x - W x‖)) := by
            have hfun : (fun τ : ℝ => Real.exp (lam * τ) * g τ)
                = (fun τ : ℝ => Real.exp (lam * τ)) * g := rfl
            rw [hfun]
            exact h2.deriv
          rw [h2d]; ring
        rw [hderiv]
        have hgx : ‖Z x - W x‖ ≤ lam * g x := by
          have h := hkeyg x hx'
          have h2 : ‖Z x - W x‖ ≤ (L * g x) / c := (le_div_iff₀ hc).mpr (by rw [mul_comm]; exact h)
          have h3 : (L * g x) / c = lam * g x := by rw [hlam]; ring
          rw [h3] at h2; exact h2
        exact mul_nonneg (Real.exp_pos _).le (by linarith)
    exact hφmono ⟨le_rfl, hs.2.le⟩ ⟨hs.2.le, le_rfl⟩ hs.2.le
  have hg1 : g b₁ = 0 := by simp [hg]
  have hgs : g s = 0 := by
    have h := hmono
    rw [hg1, mul_zero] at h
    have hexp : 0 < Real.exp (lam * s) := Real.exp_pos _
    have hle : g s ≤ 0 := by nlinarith [h, hexp]
    exact le_antisymm hle (hgnonneg s hs.2.le)
  have hfinal : c * ‖Z s - W s‖ ≤ 0 := by
    have h := hkeyg s hs
    rw [hgs, mul_zero] at h
    exact h
  have hzero : ‖Z s - W s‖ = 0 := by
    have hle : ‖Z s - W s‖ ≤ 0 := by nlinarith [hfinal, hc, norm_nonneg (Z s - W s)]
    exact le_antisymm hle (norm_nonneg _)
  exact sub_eq_zero.mp (norm_eq_zero.mp hzero)

end Work.VolterraLong
