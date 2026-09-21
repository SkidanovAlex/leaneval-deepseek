import Mathlib
import Submission.Work.OddVolterra.Defs

/-!
# Uniqueness of the odd Volterra system on a tail interval

A copy (with distinct names) of the two lemmas of
`Submission.Work.OddVolterra.Existence.glue_local_solutions` needed for the tail argument of the
window statement: interval-integrability of the `Θ`-integrand of a continuous state curve inside
the state ball, and the Gronwall uniqueness argument.  The copy is needed because
`glue_local_solutions` imports `...Existence.base_volterra`, which cannot be imported together with
`...Existence.base_volterra_on_Ioo` (duplicate name `profileX_lt_one`).

The same clash rules out importing `...Existence.theta_lipschitz_state_ball` and
`...Existence.godd_injective_modulus_state_ball_compat` (both import `...Existence.base_volterra`)
together with `...Existence.base_volterra_on_Ioo`: a file that needs the base identity with upper
limit `1` *and* the state facts about `Θ`/`Godd` must re-prove the state facts itself, or restrict
them to the unperturbed data `h ≡ 0` (where they are elementary, since for `h = 0` the kernel
radicand is `(σ + a) t²`).
-/

namespace Work.OddVolterra.Window

open MeasureTheory Set Filter
open scoped Topology ContDiff Interval

noncomputable section

variable {n : ℕ} {h : ℝ → ℝ}

lemma intervalIntegrable_Theta_integrand_win {b C : ℝ}
    (hBd : ∀ s ∈ Set.Icc b 1, ∀ σ ∈ Set.Ioo s 1,
      ∀ z ∈ Metric.closedBall (baseState σ) (1 / 2), ‖Theta n h s σ z‖ ≤ C)
    (hCont : ∀ s ∈ Set.Icc b 1,
      ContinuousOn (fun p : ℝ × St => Theta n h s p.1 p.2)
        {p : ℝ × St | p.1 ∈ Set.Ioo s 1 ∧ p.2 ∈ Metric.closedBall (baseState p.1) (1 / 2)})
    {r s₁ : ℝ} (hr : r ∈ Set.Icc b 1) (hrs₁ : r ≤ s₁) (hs₁1 : s₁ ≤ 1)
    {Z : ℝ → St} (hZc : ContinuousOn Z (Set.Icc r s₁))
    (hZb : ∀ σ ∈ Set.Icc r s₁, ‖Z σ - baseState σ‖ ≤ 1 / 2) :
    IntervalIntegrable (fun σ => Theta n h r σ (Z σ)) volume r s₁ := by
  have hopen : ContinuousOn (fun σ => Theta n h r σ (Z σ)) (Set.Ioo r s₁) := by
    refine ContinuousOn.comp (g := fun p : ℝ × St => Theta n h r p.1 p.2)
      (f := fun σ : ℝ => (σ, Z σ)) (hCont r hr) ?_ ?_
    · intro σ hσ
      refine ContinuousWithinAt.prodMk continuousWithinAt_id ?_
      exact (hZc.mono (fun x hx => ⟨hx.1.le, hx.2.le⟩)).continuousWithinAt hσ
    · intro σ hσ
      exact ⟨⟨hσ.1, hσ.2.trans_le hs₁1⟩, hZb σ ⟨hσ.1.le, hσ.2.le⟩⟩
  have hmeas_open : AEStronglyMeasurable (fun σ => Theta n h r σ (Z σ))
      (volume.restrict (Set.Ioo r s₁)) :=
    hopen.aestronglyMeasurable isOpen_Ioo.measurableSet
  have hset : Set.Ioo r s₁ =ᵐ[(volume : Measure ℝ)] Set.Ioc r s₁ := by
    rw [MeasureTheory.ae_eq_set]
    constructor
    · have hempty : Set.Ioo r s₁ \ Set.Ioc r s₁ = ∅ := by
        rw [Set.sdiff_eq_empty.mpr]
        intro x hx
        exact ⟨hx.1, hx.2.le⟩
      rw [hempty]
      exact measure_empty
    · refine measure_mono_null (t := ({s₁} : Set ℝ)) ?_ (Real.volume_singleton (a := s₁))
      intro x hx
      rw [Set.mem_singleton_iff]
      by_contra hx1
      exact hx.2 ⟨hx.1.1, lt_of_le_of_ne hx.1.2 hx1⟩
  have hmeas : AEStronglyMeasurable (fun σ => Theta n h r σ (Z σ))
      (volume.restrict (Set.Ioc r s₁)) := by
    rw [← MeasureTheory.Measure.restrict_congr_set hset]
    exact hmeas_open
  have hbound : ∀ᵐ σ ∂(volume.restrict (Set.Ioc r s₁)),
      ‖Theta n h r σ (Z σ)‖ ≤ max C 0 := by
    have hbad : (volume : Measure ℝ)
        {σ : ℝ | σ ∈ Set.Ioc r s₁ ∧ ¬ (‖Theta n h r σ (Z σ)‖ ≤ max C 0)} = 0 := by
      refine measure_mono_null (t := ({s₁} : Set ℝ)) ?_ (Real.volume_singleton (a := s₁))
      intro σ hσ
      rw [Set.mem_singleton_iff]
      by_contra hσ1
      refine hσ.2 (le_trans (hBd r hr σ
        ⟨hσ.1.1, lt_of_lt_of_le (lt_of_le_of_ne hσ.1.2 hσ1) hs₁1⟩ (Z σ) ?_)
        (le_max_left _ _))
      rw [Metric.mem_closedBall]
      exact hZb σ ⟨hσ.1.1.le, hσ.1.2⟩
    rw [MeasureTheory.ae_restrict_iff' measurableSet_Ioc, MeasureTheory.ae_iff]
    refine measure_mono_null ?_ hbad
    intro x hx
    simp only [Set.mem_setOf_eq] at hx ⊢
    exact Classical.not_imp.mp hx
  refine intervalIntegrable_iff.mpr ?_
  rw [Set.uIoc_of_le hrs₁]
  exact MeasureTheory.IntegrableOn.of_bound measure_Ioc_lt_top hmeas (max C 0) hbound

/-- **Uniqueness of the odd Volterra system on `(b,1)`.**  Two continuous solutions whose states
stay in the ball of radius `1/2` around `baseState` coincide on `(b,1)`, provided the state
injectivity modulus `c` and the state Lipschitz constant `L` of the data hold on `[b,1]`. -/
theorem eqOn_of_solves_win {b L C c : ℝ}
    (hL : 0 ≤ L) (hc : 0 < c) (hb : 0 < b) (hb1 : b ≤ 1)
    (hLip : ∀ s ∈ Set.Icc b 1, ∀ σ ∈ Set.Ioo s 1,
      ∀ z ∈ Metric.closedBall (baseState σ) (1 / 2),
      ∀ z' ∈ Metric.closedBall (baseState σ) (1 / 2),
      ‖Theta n h s σ z - Theta n h s σ z'‖ ≤ L * ‖z - z'‖)
    (hBd : ∀ s ∈ Set.Icc b 1, ∀ σ ∈ Set.Ioo s 1,
      ∀ z ∈ Metric.closedBall (baseState σ) (1 / 2), ‖Theta n h s σ z‖ ≤ C)
    (hCont : ∀ s ∈ Set.Icc b 1,
      ContinuousOn (fun p : ℝ × St => Theta n h s p.1 p.2)
        {p : ℝ × St | p.1 ∈ Set.Ioo s 1 ∧ p.2 ∈ Metric.closedBall (baseState p.1) (1 / 2)})
    (hInj : ∀ s ∈ Set.Icc b 1, ∀ z ∈ Metric.closedBall (baseState s) (1 / 2),
      ∀ z' ∈ Metric.closedBall (baseState s) (1 / 2),
      c * ‖z - z'‖ ≤ ‖Godd n h s z - Godd n h s z'‖)
    {Z W : ℝ → St}
    (hZc : ContinuousOn Z (Set.Icc b 1)) (hWc : ContinuousOn W (Set.Icc b 1))
    (hZe : ∀ s ∈ Set.Ioo b 1, Godd n h s (Z s) =
      (∫ σ in s..(1 : ℝ), Theta n h s σ (Z σ)) + Xi n h s)
    (hWe : ∀ s ∈ Set.Ioo b 1, Godd n h s (W s) =
      (∫ σ in s..(1 : ℝ), Theta n h s σ (W σ)) + Xi n h s)
    (hZb : ∀ s ∈ Set.Icc b 1, ‖Z s - baseState s‖ ≤ 1 / 2)
    (hWb : ∀ s ∈ Set.Icc b 1, ‖W s - baseState s‖ ≤ 1 / 2) :
    ∀ s ∈ Set.Ioo b 1, Z s = W s := by
  -- the functional inequality obtained by subtracting the two equations
  have hkey : ∀ s ∈ Set.Ioo b 1,
      c * ‖Z s - W s‖ ≤ L * (∫ σ in s..(1 : ℝ), ‖Z σ - W σ‖) := by
    intro s hs
    have hsb : s ∈ Set.Icc b 1 := ⟨hs.1.le, hs.2.le⟩
    have hZs : Z s ∈ Metric.closedBall (baseState s) (1 / 2) := by
      rw [Metric.mem_closedBall]; exact hZb s hsb
    have hWs : W s ∈ Metric.closedBall (baseState s) (1 / 2) := by
      rw [Metric.mem_closedBall]; exact hWb s hsb
    have hZsub : ContinuousOn Z (Set.Icc s 1) :=
      hZc.mono (Set.Icc_subset_Icc_left hs.1.le)
    have hWsub : ContinuousOn W (Set.Icc s 1) :=
      hWc.mono (Set.Icc_subset_Icc_left hs.1.le)
    have hIZ := intervalIntegrable_Theta_integrand_win (n := n) (h := h) hBd hCont hsb hs.2.le le_rfl
      hZsub (fun σ hσ => hZb σ ⟨hs.1.le.trans hσ.1, hσ.2⟩)
    have hIW := intervalIntegrable_Theta_integrand_win (n := n) (h := h) hBd hCont hsb hs.2.le le_rfl
      hWsub (fun σ hσ => hWb σ ⟨hs.1.le.trans hσ.1, hσ.2⟩)
    have hdiff : Godd n h s (Z s) - Godd n h s (W s)
        = ∫ σ in s..(1 : ℝ), (Theta n h s σ (Z σ) - Theta n h s σ (W σ)) := by
      have hsub : (∫ σ in s..(1 : ℝ), Theta n h s σ (Z σ)) + Xi n h s -
            ((∫ σ in s..(1 : ℝ), Theta n h s σ (W σ)) + Xi n h s)
          = (∫ σ in s..(1 : ℝ), Theta n h s σ (Z σ)) -
            (∫ σ in s..(1 : ℝ), Theta n h s σ (W σ)) := by abel
      rw [hZe s hs, hWe s hs, hsub, ← intervalIntegral.integral_sub hIZ hIW]
    have hnorm : ‖∫ σ in s..(1 : ℝ), (Theta n h s σ (Z σ) - Theta n h s σ (W σ))‖
        ≤ ∫ σ in s..(1 : ℝ), L * ‖Z σ - W σ‖ := by
      refine intervalIntegral.norm_integral_le_of_norm_le hs.2.le ?_ ?_
      · have hbad : (volume : Measure ℝ)
            {x : ℝ | x ∈ Set.Ioc s 1 ∧
              ¬ (‖Theta n h s x (Z x) - Theta n h s x (W x)‖ ≤ L * ‖Z x - W x‖)} = 0 := by
          refine measure_mono_null (t := ({1} : Set ℝ)) ?_ (Real.volume_singleton (a := 1))
          intro x hx
          rw [Set.mem_singleton_iff]
          by_contra hx1
          refine hx.2 (hLip s hsb x ⟨hx.1.1, lt_of_le_of_ne hx.1.2 hx1⟩ (Z x) ?_ (W x) ?_)
          · rw [Metric.mem_closedBall]
            exact hZb x ⟨hs.1.le.trans hx.1.1.le, hx.1.2⟩
          · rw [Metric.mem_closedBall]
            exact hWb x ⟨hs.1.le.trans hx.1.1.le, hx.1.2⟩
        rw [MeasureTheory.ae_iff]
        refine measure_mono_null ?_ hbad
        intro x hx
        simp only [Set.mem_setOf_eq] at hx ⊢
        exact Classical.not_imp.mp hx
      · have hcont' : ContinuousOn (fun σ => L * ‖Z σ - W σ‖) (Set.uIcc s 1) :=
          ((hZc.sub hWc).norm.const_mul L).mono (fun x hx => by
            rw [Set.uIcc_of_le hs.2.le] at hx
            exact ⟨hs.1.le.trans hx.1, hx.2⟩)
        exact hcont'.intervalIntegrable
    calc c * ‖Z s - W s‖ ≤ ‖Godd n h s (Z s) - Godd n h s (W s)‖ :=
          hInj s hsb (Z s) hZs (W s) hWs
      _ = ‖∫ σ in s..(1 : ℝ), (Theta n h s σ (Z σ) - Theta n h s σ (W σ))‖ := by rw [hdiff]
      _ ≤ ∫ σ in s..(1 : ℝ), L * ‖Z σ - W σ‖ := hnorm
      _ = L * ∫ σ in s..(1 : ℝ), ‖Z σ - W σ‖ := by
            rw [intervalIntegral.integral_const_mul]
  -- the tail distance function and the exponentially weighted Gronwall argument
  set H : ℝ → ℝ := fun σ => ‖Z (max b (min σ 1)) - W (max b (min σ 1))‖ with hH
  have hHcont : Continuous H := by
    have hclamp : Continuous fun σ : ℝ => max b (min σ 1) := by fun_prop
    have hmem : ∀ σ : ℝ, max b (min σ 1) ∈ Set.Icc b 1 := fun σ =>
      ⟨le_max_left _ _, max_le hb1 (min_le_right _ _)⟩
    have := (hZc.sub hWc).norm.comp_continuous hclamp hmem
    simpa only [hH, Function.comp_def, Pi.sub_apply] using this
  set g : ℝ → ℝ := fun s => ∫ σ in s..(1 : ℝ), ‖Z σ - W σ‖ with hg
  have hkeyg : ∀ s ∈ Set.Ioo b 1, c * ‖Z s - W s‖ ≤ L * g s := by
    intro s hs
    simpa only [hg] using hkey s hs
  have hg_eq : ∀ s ∈ Set.Icc b 1, g s = ∫ σ in s..(1 : ℝ), H σ := by
    intro s hs
    refine intervalIntegral.integral_congr ?_
    intro σ hσ
    rw [Set.uIcc_of_le hs.2] at hσ
    simp only [hH]
    rw [min_eq_left hσ.2, max_eq_right (le_trans hs.1 hσ.1)]
  have hgnonneg : ∀ s ≤ 1, 0 ≤ g s := by
    intro s hle
    rw [hg]
    exact intervalIntegral.integral_nonneg hle (fun u _ => norm_nonneg _)
  have hgcont : ContinuousOn g (Set.Icc b 1) := by
    have hprim : Continuous fun u : ℝ => ∫ σ in (1 : ℝ)..u, H σ :=
      intervalIntegral.continuous_primitive (fun a b => hHcont.intervalIntegrable a b) 1
    refine (hprim.neg.continuousOn).congr ?_
    intro s hs
    rw [hg_eq s hs, intervalIntegral.integral_symm]
    rfl
  have hgderiv : ∀ τ ∈ Set.Ioo b 1, HasDerivAt g (-(‖Z τ - W τ‖)) τ := by
    intro τ hτ
    have hcontτ : ContinuousAt (fun σ => ‖Z σ - W σ‖) τ :=
      ((hZc.continuousAt (Icc_mem_nhds hτ.1 hτ.2)).sub
        (hWc.continuousAt (Icc_mem_nhds hτ.1 hτ.2))).norm
    have hmeasτ : StronglyMeasurableAtFilter (fun σ => ‖Z σ - W σ‖) (𝓝 τ) volume :=
      ContinuousAt.stronglyMeasurableAtFilter (s := Set.Ioo b 1) isOpen_Ioo
        (fun x hx => ((hZc.continuousAt (Icc_mem_nhds hx.1 hx.2)).sub
          (hWc.continuousAt (Icc_mem_nhds hx.1 hx.2))).norm) τ hτ
    have hInt : IntervalIntegrable (fun σ => ‖Z σ - W σ‖) volume τ 1 :=
      (((hZc.sub hWc).norm.mono (fun x hx => by
        rw [Set.uIcc_of_le hτ.2.le] at hx
        exact ⟨hτ.1.le.trans hx.1, hx.2⟩)).intervalIntegrable)
    have h := intervalIntegral.integral_hasDerivAt_left hInt hmeasτ hcontτ
    simpa only [hg] using h
  -- the exponential weight `exp (lam ·) g` is monotone from the right end
  set lam : ℝ := L / c with hlam
  intro s hs
  have hsb : s ∈ Set.Icc b 1 := ⟨hs.1.le, hs.2.le⟩
  have hmono : Real.exp (lam * s) * g s ≤ Real.exp (lam * 1) * g 1 := by
    have hφmono : MonotoneOn (fun τ => Real.exp (lam * τ) * g τ) (Set.Icc s 1) := by
      refine monotoneOn_of_deriv_nonneg (convex_Icc s 1) ?_ ?_ ?_
      · exact ((Real.continuous_exp.comp (continuous_const.mul continuous_id)).continuousOn).mul
          (hgcont.mono (fun x hx => ⟨hs.1.le.trans hx.1, hx.2⟩))
      · intro x hx
        rw [interior_Icc] at hx
        have hx' : x ∈ Set.Ioo b 1 := ⟨lt_trans hs.1 hx.1, hx.2⟩
        exact (((Real.hasDerivAt_exp _).comp x ((hasDerivAt_id x).const_mul lam)).mul
          (hgderiv x hx')).differentiableAt.differentiableWithinAt
      · intro x hx
        rw [interior_Icc] at hx
        have hx' : x ∈ Set.Ioo b 1 := ⟨lt_trans hs.1 hx.1, hx.2⟩
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
  have hg1 : g 1 = 0 := by simp [hg]
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

end

end Work.OddVolterra.Window
