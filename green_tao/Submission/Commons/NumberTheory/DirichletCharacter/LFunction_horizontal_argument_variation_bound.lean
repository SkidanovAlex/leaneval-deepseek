import Mathlib
import Submission.Commons.NumberTheory.DirichletCharacter.reZeros_finset_log_bound
import Submission.Commons.NumberTheory.DirichletCharacter.LFunction_conj
import Submission.Commons.NumberTheory.DirichletCharacter.LFunction_norm_half_plane
import Submission.Commons.NumberTheory.DirichletCharacter.norm_LFunction_le_re_ge_one
import Submission.Commons.NumberTheory.DirichletCharacter.diskZeroCount_two_half

open Complex DirichletCharacter MeasureTheory intervalIntegral Filter Topology
open scoped Real Topology
set_option autoImplicit false
noncomputable section

namespace Commons.NumberTheory.DirichletCharacter


private lemma hasDerivAt_im {f : ℝ → ℂ} {c : ℂ} {x : ℝ} (h : HasDerivAt f c x) :
    HasDerivAt (fun y => (f y).im) c.im x := by
  have h1 : HasFDerivAt f (ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) c) x := h.hasFDerivAt
  have h2 : HasFDerivAt (fun y => (f y).im)
      (Complex.imCLM.comp (ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) c)) x :=
    Complex.imCLM.hasFDerivAt.comp x h1
  simpa using h2.hasDerivAt

private lemma hasDerivAt_re {f : ℝ → ℂ} {c : ℂ} {x : ℝ} (h : HasDerivAt f c x) :
    HasDerivAt (fun y => (f y).re) c.re x := by
  have h1 : HasFDerivAt f (ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) c) x := h.hasFDerivAt
  have h2 : HasFDerivAt (fun y => (f y).re)
      (Complex.reCLM.comp (ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) c)) x :=
    Complex.reCLM.hasFDerivAt.comp x h1
  simpa using h2.hasDerivAt

/-- Derivative of `σ ↦ arctan (Im G σ / Re G σ)` is `Im (G'/G)`. -/
private lemma hasDerivAt_arctan_div (G : ℝ → ℂ) (G' : ℂ) (σ : ℝ) (hG : HasDerivAt G G' σ)
    (hne : (G σ).re ≠ 0) :
    HasDerivAt (fun τ => Real.arctan ((G τ).im / (G τ).re)) (G'/G σ).im σ := by
  have hA : HasDerivAt (fun y => (G y).im) G'.im σ := hasDerivAt_im hG
  have hB : HasDerivAt (fun y => (G y).re) G'.re σ := hasDerivAt_re hG
  have hdiv := hA.div hB hne
  have harctan := hdiv.arctan
  simp only [Pi.div_apply] at harctan
  convert harctan using 1
  rw [Complex.div_im, Complex.normSq_apply]
  field_simp


private theorem abs_integral_im_logDeriv_horizontal_le_card
    (g : ℂ → ℂ) (hg : Differentiable ℂ g) {T a b : ℝ} (hab : a ≤ b) (Z : Finset ℝ)
    (hsub : ∀ z ∈ Z, a ≤ z ∧ z ≤ b)
    (hZ : ∀ σ : ℝ, a ≤ σ → σ ≤ b → (g ((σ : ℂ) + (T : ℂ) * Complex.I)).re = 0 → σ ∈ Z)
    (hbdd : ∃ C : ℝ, ∀ σ : ℝ, a ≤ σ → σ ≤ b →
      |(logDeriv g ((σ : ℂ) + (T : ℂ) * Complex.I)).im| ≤ C) :
    |∫ σ : ℝ in a..b, (logDeriv g ((σ : ℂ) + (T : ℂ) * Complex.I)).im| ≤ (Z.card + 1) * Real.pi := by
  obtain ⟨C, hC⟩ := hbdd
  set G : ℝ → ℂ := fun σ => g ((σ : ℂ) + (T : ℂ) * Complex.I) with hGdef
  set hh : ℝ → ℝ := fun σ => (logDeriv G σ).im with hhdef
  have hC0 : 0 ≤ C := by
    have := hC a (le_refl a) hab
    linarith [abs_nonneg (logDeriv g ((a : ℂ) + (T : ℂ) * Complex.I)).im]
  -- derivative of G
  have hGderiv : ∀ σ : ℝ, HasDerivAt G (deriv g ((σ : ℂ) + (T : ℂ) * Complex.I)) σ := by
    intro σ
    have hc0 : HasDerivAt (fun τ : ℝ => (τ : ℂ)) 1 σ := by
      simpa using (hasDerivAt_id (𝕜 := ℝ) σ).ofReal_comp
    have hc : HasDerivAt (fun τ : ℝ => (τ : ℂ) + (T : ℂ) * Complex.I) 1 σ := by
      simpa using hc0.add_const ((T : ℂ) * Complex.I)
    have h2 : HasDerivAt g (deriv g ((σ : ℂ) + (T : ℂ) * Complex.I))
        ((σ : ℂ) + (T : ℂ) * Complex.I) := (hg _).hasDerivAt
    have h3 := h2.comp σ hc
    simpa [hGdef, Function.comp_def, mul_one] using h3
  have hlog_eq : ∀ σ : ℝ, logDeriv G σ = logDeriv g ((σ : ℂ) + (T : ℂ) * Complex.I) := by
    intro σ
    simp only [logDeriv_apply, hGdef]
    rw [(hGderiv σ).deriv]
  have hh_eq : ∀ σ : ℝ, hh σ = (logDeriv g ((σ : ℂ) + (T : ℂ) * Complex.I)).im := by
    intro σ; rw [hhdef]; exact congrArg Complex.im (hlog_eq σ)
  have hGcont : Continuous G := by
    rw [hGdef]
    exact hg.continuous.comp (Continuous.add continuous_ofReal continuous_const)
  -- measurability
  have hmeas : Measurable hh := by
    have h1 : Measurable (fun z : ℂ => logDeriv g z) := by
      have h2 : Measurable (deriv g) := hg.deriv.continuous.measurable
      have h3 : Measurable g := hg.continuous.measurable
      exact h2.div h3
    have h4 : Measurable (fun σ : ℝ => (σ : ℂ) + (T : ℂ) * Complex.I) := by fun_prop
    have h5 : Measurable (fun σ : ℝ => (logDeriv g ((σ : ℂ) + (T : ℂ) * Complex.I)).im) := by
      simpa [Function.comp_def] using Complex.measurable_im.comp (h1.comp h4)
    rw [show hh = fun σ : ℝ => (logDeriv g ((σ : ℂ) + (T : ℂ) * Complex.I)).im from funext hh_eq]
    exact h5
  -- integrability on subintervals
  have hint : ∀ u v : ℝ, a ≤ u → u ≤ v → v ≤ b → IntervalIntegrable hh volume u v := by
    intro u v hau huv hvb
    have hbdd' : ∀ᵐ x ∂(volume.restrict (Set.Icc u v)), ‖hh x‖ ≤ C := by
      filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
      rw [Real.norm_eq_abs]
      simpa [hh_eq x] using hC x (le_trans hau hx.1) (le_trans hx.2 hvb)
    have hInt : IntegrableOn hh (Set.uIcc u v) volume := by
      rw [Set.uIcc_of_le huv]
      exact IntegrableOn.of_bound measure_Icc_lt_top hmeas.aestronglyMeasurable C hbdd'
    exact hInt.intervalIntegrable
  -- the primitive
  set Ψ : ℝ → ℝ := fun σ => ∫ x in a..σ, hh x with hΨdef
  have hPsi_sub : ∀ σ σ' : ℝ, a ≤ σ → σ ≤ σ' → σ' ≤ b → ∫ x in σ..σ', hh x = Ψ σ' - Ψ σ := by
    intro σ σ' h1 h2 h3
    have h4 := intervalIntegral.integral_interval_sub_left (f := hh) (μ := volume)
      (hint a σ' le_rfl (le_trans h1 h2) h3) (hint a σ le_rfl h1 (le_trans h2 h3))
    simp only [hΨdef]
    linarith [h4]
  have hLip : ∀ σ σ' : ℝ, a ≤ σ → σ ≤ σ' → σ' ≤ b → |Ψ σ' - Ψ σ| ≤ C * (σ' - σ) := by
    intro σ σ' h1 h2 h3
    have h4 : ∫ x in σ..σ', hh x = Ψ σ' - Ψ σ := hPsi_sub σ σ' h1 h2 h3
    have h5 : |∫ x in σ..σ', hh x| ≤ ∫ x in σ..σ', |hh x| :=
      intervalIntegral.abs_integral_le_integral_abs h2
    have h6 : ∫ x in σ..σ', |hh x| ≤ ∫ x in σ..σ', C := by
      apply intervalIntegral.integral_mono_on h2
      · exact (hint σ σ' h1 h2 h3).abs
      · exact intervalIntegrable_const
      · intro x hx
        simpa [hh_eq x] using hC x (le_trans h1 hx.1) (le_trans hx.2 h3)
    rw [h4] at h5
    refine h5.trans (h6.trans ?_)
    rw [intervalIntegral.integral_const, smul_eq_mul]
    nlinarith
  -- key bound on a clean interval
  have key : ∀ u v : ℝ, a ≤ u → u ≤ v → v ≤ b →
      (∀ σ : ℝ, u < σ → σ < v → (G σ).re ≠ 0) → |Ψ v - Ψ u| ≤ Real.pi := by
    intro u v hau huv hvb hno0
    rcases eq_or_lt_of_le huv with rfl | huvlt
    · simp [Real.pi_pos.le]
    set ψ : ℝ → ℝ := fun σ => Real.arctan ((G σ).im / (G σ).re) with hψdef
    have hψcont_at : ∀ x ∈ Set.Ioo u v, ContinuousAt ψ x := by
      intro x hx
      have hxne : (G x).re ≠ 0 := hno0 x hx.1 hx.2
      have hnum : ContinuousAt (fun σ : ℝ => (G σ).im) x :=
        Complex.continuous_im.continuousAt.comp hGcont.continuousAt
      have hden : ContinuousAt (fun σ : ℝ => (G σ).re) x :=
        Complex.continuous_re.continuousAt.comp hGcont.continuousAt
      have hq : ContinuousAt (fun σ : ℝ => (G σ).im / (G σ).re) x := hnum.div hden hxne
      rw [hψdef]
      exact Real.continuous_arctan.continuousAt.comp hq
    have hψderiv : ∀ x ∈ Set.Ioo u v, HasDerivAt ψ (hh x) x := by
      intro x hx
      have hxne : (G x).re ≠ 0 := hno0 x hx.1 hx.2
      have h1 := hasDerivAt_arctan_div G (deriv g ((x : ℂ) + (T : ℂ) * Complex.I)) x
        (hGderiv x) hxne
      have h2 : (deriv g ((x : ℂ) + (T : ℂ) * Complex.I) / G x).im = hh x := by
        show (deriv g ((x : ℂ) + (T : ℂ) * Complex.I) / G x).im = (logDeriv G x).im
        rw [hlog_eq x, logDeriv_apply, hGdef]
      rw [h2] at h1
      rw [hψdef]
      exact h1
    have hFTC : ∀ σ σ' : ℝ, u < σ → σ < σ' → σ' < v → ∫ x in σ..σ', hh x = ψ σ' - ψ σ := by
      intro σ σ' h1 h2 h3
      have hcont : ContinuousOn ψ (Set.Icc σ σ') := by
        have hIcc : Set.Icc σ σ' ⊆ Set.Ioo u v := fun x hx =>
          ⟨lt_of_lt_of_le h1 hx.1, lt_of_le_of_lt hx.2 h3⟩
        intro x hx
        exact ((hψcont_at x (hIcc hx)).continuousWithinAt)
      refine intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le h2.le hcont ?_
        (hint σ σ' (le_trans hau h1.le) h2.le (le_trans h3.le hvb))
      intro x hx
      exact hψderiv x ⟨lt_trans h1 hx.1, lt_trans hx.2 h3⟩
    have hstep : ∀ σ σ' : ℝ, u < σ → σ < σ' → σ' < v → |Ψ σ' - Ψ σ| ≤ Real.pi := by
      intro σ σ' h1 h2 h3
      have h4 : ∫ x in σ..σ', hh x = ψ σ' - ψ σ := hFTC σ σ' h1 h2 h3
      rw [← hPsi_sub σ σ' (le_trans hau h1.le) h2.le (le_trans h3.le hvb), h4]
      have h5 : |ψ σ' - ψ σ| ≤ Real.pi := by
        have ha := Real.neg_pi_div_two_lt_arctan ((G σ).im / (G σ).re)
        have hb := Real.arctan_lt_pi_div_two ((G σ).im / (G σ).re)
        have ha' := Real.neg_pi_div_two_lt_arctan ((G σ').im / (G σ').re)
        have hb' := Real.arctan_lt_pi_div_two ((G σ').im / (G σ').re)
        rw [hψdef]
        rw [abs_sub_le_iff]
        constructor <;> linarith
      exact h5
    -- limits
    have hδpos : ∀ n : ℕ, (0 : ℝ) < (v - u) / ((n : ℝ) + 3) := fun n =>
      div_pos (sub_pos.mpr huvlt) (by positivity)
    have hδhalf : ∀ n : ℕ, (v - u) / ((n : ℝ) + 3) < (v - u) / 2 := by
      intro n
      have hpos : (0 : ℝ) < v - u := sub_pos.mpr huvlt
      have h2 : (2:ℝ) < (n:ℝ) + 3 := by
        have : (0:ℝ) ≤ (n:ℝ) := Nat.cast_nonneg n
        linarith
      rw [div_lt_div_iff₀ (by linarith : (0:ℝ) < (n:ℝ) + 3) (by norm_num : (0:ℝ) < 2)]
      nlinarith
    have hstep_n : ∀ n : ℕ,
        |Ψ (v - (v - u) / ((n : ℝ) + 3)) - Ψ (u + (v - u) / ((n : ℝ) + 3))| ≤ Real.pi := by
      intro n
      refine hstep (u + (v - u) / ((n : ℝ) + 3)) (v - (v - u) / ((n : ℝ) + 3)) ?_ ?_ ?_
      · linarith [hδpos n]
      · linarith [hδhalf n]
      · linarith [hδpos n]
    have htendδ : Tendsto (fun n : ℕ => (v - u) / (((n : ℝ) + 3))) atTop (𝓝 0) := by
      have h1 : Tendsto (fun x : ℝ => x⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_zero
      have h2 : Tendsto (fun x : ℝ => (v - u) * x⁻¹) atTop (𝓝 ((v - u) * 0)) :=
        tendsto_const_nhds.mul h1
      rw [mul_zero] at h2
      have h3 : Tendsto (fun n : ℕ => ((n : ℝ) + 3)) atTop atTop :=
        tendsto_atTop_add_const_right atTop (3 : ℝ) tendsto_natCast_atTop_atTop
      simpa [div_eq_mul_inv, Function.comp_def] using h2.comp h3
    have hδle : ∀ n : ℕ, (v - u) / ((n : ℝ) + 3) ≤ v - u := by
      intro n
      have hpos : (0:ℝ) < (n:ℝ) + 3 := by positivity
      have h1 : (1:ℝ) ≤ (n:ℝ) + 3 := by
        have : (0:ℝ) ≤ (n:ℝ) := Nat.cast_nonneg n
        linarith
      have hvu : (0:ℝ) < v - u := sub_pos.mpr huvlt
      rw [div_le_iff₀ hpos]
      nlinarith
    have htend_u : Tendsto (fun n : ℕ => Ψ (u + (v - u) / (((n : ℝ) + 3)))) atTop (𝓝 (Ψ u)) := by
      rw [Metric.tendsto_nhds]
      intro ε hε
      have hCpos : 0 < C + 1 := by linarith
      have hε' : 0 < ε / (C + 1) := by positivity
      have hsmall : ∀ᶠ n : ℕ in atTop, (v - u) / (((n : ℝ) + 3)) < ε / (C + 1) := by
        filter_upwards [(Metric.tendsto_nhds.mp htendδ) (ε / (C + 1)) (by simpa using hε')]
          with n hn
        rwa [Real.dist_eq, sub_zero, abs_of_pos (hδpos n)] at hn
      filter_upwards [hsmall] with n hn
      rw [Real.dist_eq]
      have h1 : |Ψ (u + (v - u) / (((n : ℝ) + 3))) - Ψ u| ≤
          C * ((v - u) / (((n : ℝ) + 3))) := by
        have hh1 := hLip u (u + (v - u) / (((n : ℝ) + 3))) hau
          (by linarith [hδpos n]) (by linarith [hδle n, hvb])
        rwa [add_sub_cancel_left] at hh1
      have h2 : C * ((v - u) / (((n : ℝ) + 3))) < ε := by
        have h3 : (0:ℝ) ≤ (v - u) / (((n : ℝ) + 3)) := le_of_lt (hδpos n)
        calc C * ((v - u) / ((n:ℝ) + 3)) ≤ (C + 1) * ((v - u) / ((n:ℝ) + 3)) := by nlinarith
          _ < (C + 1) * (ε / (C + 1)) := by nlinarith [hε']
          _ = ε := by field_simp
      linarith
    have htend_v : Tendsto (fun n : ℕ => Ψ (v - (v - u) / (((n : ℝ) + 3)))) atTop (𝓝 (Ψ v)) := by
      rw [Metric.tendsto_nhds]
      intro ε hε
      have hCpos : 0 < C + 1 := by linarith
      have hε' : 0 < ε / (C + 1) := by positivity
      have hsmall : ∀ᶠ n : ℕ in atTop, (v - u) / (((n : ℝ) + 3)) < ε / (C + 1) := by
        filter_upwards [(Metric.tendsto_nhds.mp htendδ) (ε / (C + 1)) (by simpa using hε')]
          with n hn
        rwa [Real.dist_eq, sub_zero, abs_of_pos (hδpos n)] at hn
      filter_upwards [hsmall] with n hn
      rw [Real.dist_eq]
      have hδp : (0:ℝ) < (v - u) / (((n : ℝ) + 3)) := hδpos n
      have h1 : |Ψ (v - (v - u) / (((n : ℝ) + 3))) - Ψ v| ≤
          C * ((v - u) / (((n : ℝ) + 3))) := by
        have hh1 := hLip (v - (v - u) / (((n : ℝ) + 3))) v
          (by linarith [hδle n, hau]) (by linarith [hδp]) hvb
        rw [abs_sub_comm]
        rwa [sub_sub_cancel] at hh1
      have h2 : C * ((v - u) / (((n : ℝ) + 3))) < ε := by
        have h3 : (0:ℝ) ≤ (v - u) / (((n : ℝ) + 3)) := le_of_lt hδp
        calc C * ((v - u) / ((n:ℝ) + 3)) ≤ (C + 1) * ((v - u) / ((n:ℝ) + 3)) := by nlinarith
          _ < (C + 1) * (ε / (C + 1)) := by nlinarith [hε']
          _ = ε := by field_simp
      linarith
    have htend : Tendsto (fun n : ℕ => |Ψ (v - (v - u) / (((n : ℝ) + 3)))
        - Ψ (u + (v - u) / (((n : ℝ) + 3)))|) atTop (𝓝 |Ψ v - Ψ u|) := by
      have h1 : Tendsto (fun n : ℕ => Ψ (v - (v - u) / (((n : ℝ) + 3)))
          - Ψ (u + (v - u) / (((n : ℝ) + 3)))) atTop (𝓝 (Ψ v - Ψ u)) :=
        htend_v.sub htend_u
      simpa [Real.norm_eq_abs] using h1.norm
    exact le_of_tendsto htend (Eventually.of_forall hstep_n)
  -- induction on the number of cut points in `(u, b]`
  have H : ∀ k : ℕ, ∀ u ∈ Set.Icc a b,
      (Z.filter (fun z => u < z)).card = k →
      |∫ x in u..b, hh x| ≤ ((Z.filter (fun z => u < z)).card : ℝ) * Real.pi + Real.pi := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
      intro u hu hk
      by_cases hne : (Z.filter (fun z => u < z)).Nonempty
      · set z := (Z.filter (fun z => u < z)).min' hne with hzdef
        have hz : z ∈ Z.filter (fun z => u < z) := Finset.min'_mem _ hne
        have hzmin : ∀ w ∈ Z.filter (fun z => u < z), z ≤ w :=
          fun w hw => Finset.min'_le _ w hw
        have huz : u < z := (Finset.mem_filter.mp hz).2
        have hzZ : z ∈ Z := (Finset.mem_filter.mp hz).1
        have hzab : z ∈ Set.Icc a b := hsub z hzZ
        have hsub' : Z.filter (fun w => z < w) ⊆ (Z.filter (fun w => u < w)).erase z := by
          intro w hw
          rw [Finset.mem_filter] at hw
          refine Finset.mem_erase.mpr ⟨?_, Finset.mem_filter.mpr ⟨hw.1, ?_⟩⟩
          · exact ne_of_gt hw.2
          · exact lt_trans huz hw.2
        have hcard_le : (Z.filter (fun w => z < w)).card ≤ (Z.filter (fun w => u < w)).card - 1 := by
          calc (Z.filter (fun w => z < w)).card ≤ ((Z.filter (fun w => u < w)).erase z).card :=
                Finset.card_le_card hsub'
            _ = (Z.filter (fun w => u < w)).card - 1 := Finset.card_erase_of_mem hz
        have hcard_lt : (Z.filter (fun w => z < w)).card < k := by
          rw [← hk]
          have : 0 < (Z.filter (fun w => u < w)).card := Finset.card_pos.mpr ⟨z, hz⟩
          omega
        have hcard_succ : (Z.filter (fun w => z < w)).card + 1 ≤ (Z.filter (fun w => u < w)).card := by
          have : 0 < (Z.filter (fun w => u < w)).card := Finset.card_pos.mpr ⟨z, hz⟩
          omega
        have hno1 : ∀ σ : ℝ, u < σ → σ < z → (G σ).re ≠ 0 := by
          intro σ h1 h2 hc
          have hmem : σ ∈ Z.filter (fun w => u < w) :=
            Finset.mem_filter.mpr ⟨hZ σ (le_trans hu.1 h1.le) (le_trans h2.le hzab.2) hc, h1⟩
          have := hzmin σ hmem
          linarith
        have hpart1 : |∫ x in u..z, hh x| ≤ Real.pi := by
          rw [hPsi_sub u z hu.1 huz.le hzab.2]
          exact key u z hu.1 huz.le hzab.2 hno1
        have hpart2 : |∫ x in z..b, hh x| ≤ ((Z.filter (fun w => z < w)).card : ℝ) * Real.pi + Real.pi :=
          ih _ hcard_lt z hzab rfl
        have hsplit1 : ∫ x in u..b, hh x = (∫ x in u..z, hh x) + (∫ x in z..b, hh x) := by
          exact (intervalIntegral.integral_add_adjacent_intervals (f := hh) (μ := volume)
            (hint u z hu.1 huz.le hzab.2) (hint z b hzab.1 hzab.2 le_rfl)).symm
        rw [hsplit1]
        calc |(∫ x in u..z, hh x) + (∫ x in z..b, hh x)|
            ≤ |∫ x in u..z, hh x| + |∫ x in z..b, hh x| := abs_add_le _ _
          _ ≤ Real.pi + (((Z.filter (fun w => z < w)).card : ℝ) * Real.pi + Real.pi) :=
              add_le_add hpart1 hpart2
          _ ≤ ((Z.filter (fun w => u < w)).card : ℝ) * Real.pi + Real.pi := by
              have hc' : ((Z.filter (fun w => z < w)).card : ℝ) + 1 ≤
                  ((Z.filter (fun w => u < w)).card : ℝ) := by exact_mod_cast hcard_succ
              nlinarith [Real.pi_pos]
      · have hempty : Z.filter (fun z => u < z) = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
        have hno1 : ∀ σ : ℝ, u < σ → σ < b → (G σ).re ≠ 0 := by
          intro σ h1 h2 hc
          have hmem : σ ∈ Z.filter (fun w => u < w) :=
            Finset.mem_filter.mpr ⟨hZ σ (le_trans hu.1 h1.le) h2.le hc, h1⟩
          rw [hempty] at hmem
          simp at hmem
        have hpart : |∫ x in u..b, hh x| ≤ Real.pi := by
          rw [hPsi_sub u b hu.1 hu.2 le_rfl]
          exact key u b hu.1 hu.2 le_rfl hno1
        have hgoal2 : ((Z.filter (fun z => u < z)).card : ℝ) * Real.pi + Real.pi = Real.pi := by
          rw [hempty]; simp
        rw [hgoal2]
        exact hpart
  have hfin := H (Z.filter (fun z => a < z)).card a ⟨le_rfl, hab⟩ rfl
  have hcard_le : (Z.filter (fun z => a < z)).card ≤ Z.card := Finset.card_filter_le _ _
  have hgoal : |∫ x in a..b, hh x| ≤ (Z.card + 1) * Real.pi := by
    refine hfin.trans ?_
    have hc' : ((Z.filter (fun z => a < z)).card : ℝ) ≤ (Z.card : ℝ) := by exact_mod_cast hcard_le
    nlinarith [Real.pi_pos]
  have hcongr : ∫ σ in a..b, (logDeriv g ((σ : ℂ) + (T : ℂ) * Complex.I)).im
      = ∫ σ in a..b, hh σ := by
    apply intervalIntegral.integral_congr
    intro σ _
    exact (hh_eq σ).symm
  rwa [hcongr]

/-- If an entire function has an isolated zero at `ρ`, then the imaginary part of its
logarithmic derivative stays bounded along the horizontal direction through `ρ`. -/
private theorem exists_bound_im_logDeriv_near_zero {f : ℂ → ℂ} (hdf : Differentiable ℂ f) (ρ : ℂ)
    (hρne : ¬ Filter.Eventually (fun z : ℂ => f z = 0) (nhds ρ)) (hfρ : f ρ = 0) :
    ∃ η C : ℝ, 0 < η ∧ 0 < C ∧ ∀ σ : ℝ, 0 < |σ| → |σ| < η →
      |(logDeriv f (ρ + (σ : ℂ))).im| ≤ C := by
  classical
  have hfan : AnalyticAt ℂ f ρ := hdf.analyticAt ρ
  obtain ⟨n, g, hg_an, hg_ne0, hg_eq⟩ := hfan.exists_eventuallyEq_pow_smul_nonzero_iff.mpr hρne
  have hgder_an : AnalyticAt ℂ (deriv g) ρ := AnalyticAt.deriv hg_an
  have hlogg_cont : ContinuousAt (fun z : ℂ => logDeriv g z) ρ :=
    hgder_an.continuousAt.div hg_an.continuousAt hg_ne0
  have hg_diff_ev : ∀ᶠ z in 𝓝 ρ, DifferentiableAt ℂ g z := by
    rcases hg_an with ⟨pg, hpg⟩
    exact hpg.eventually_differentiableAt
  let C : ℝ := ‖logDeriv g ρ‖ + 1
  have hCpos : 0 < C := by positivity
  have hev : ∀ᶠ z in 𝓝 ρ, f z = (z - ρ) ^ n • g z ∧ g z ≠ 0 ∧ DifferentiableAt ℂ g z ∧
      ‖logDeriv g z‖ ≤ C := by
    have h1 : ∀ᶠ z in 𝓝 ρ, ‖logDeriv g z - logDeriv g ρ‖ < 1 := by
      have h2 : ∀ᶠ z in 𝓝 ρ, logDeriv g z ∈ Metric.ball (logDeriv g ρ) 1 :=
        hlogg_cont.eventually (Metric.ball_mem_nhds _ (by norm_num))
      filter_upwards [h2] with z hz
      simpa [Metric.mem_ball, dist_eq_norm] using hz
    filter_upwards [hg_eq, hg_an.continuousAt.eventually_ne hg_ne0, hg_diff_ev, h1] with z hA hB hC' hD
    refine ⟨hA, hB, hC', ?_⟩
    calc ‖logDeriv g z‖ = ‖logDeriv g ρ + (logDeriv g z - logDeriv g ρ)‖ := by ring_nf
      _ ≤ ‖logDeriv g ρ‖ + ‖logDeriv g z - logDeriv g ρ‖ := norm_add_le _ _
      _ ≤ ‖logDeriv g ρ‖ + 1 := by linarith
  obtain ⟨δ, hδpos, hδball⟩ := Metric.eventually_nhds_iff.mp hev
  refine ⟨δ, C, hδpos, hCpos, ?_⟩
  intro σ hσ0 hσδ
  have hσne : σ ≠ 0 := abs_pos.mp hσ0
  have hdist : dist (ρ + (σ : ℂ)) ρ = |σ| := by
    rw [dist_eq_norm, add_sub_cancel_left, Complex.norm_real, Real.norm_eq_abs]
  have hmem : Metric.ball ρ δ ∈ 𝓝 (ρ + (σ : ℂ)) :=
    Metric.isOpen_ball.mem_nhds (by rw [Metric.mem_ball, hdist]; exact hσδ)
  have hnear : f =ᶠ[𝓝 (ρ + (σ : ℂ))] (fun w : ℂ => (w - ρ) ^ n * g w) := by
    filter_upwards [hmem] with w hw
    have hQ := hδball hw
    simpa [smul_eq_mul] using hQ.1
  have hP := hδball (by rw [hdist]; exact hσδ)
  obtain ⟨hfeq, hgz0, hgdz, hlogg⟩ := hP
  have hlog_eq : logDeriv f (ρ + (σ : ℂ)) =
      logDeriv (fun w : ℂ => (w - ρ) ^ n * g w) (ρ + (σ : ℂ)) :=
    (logDeriv_congr_nhds hnear).self_of_nhds
  rw [hlog_eq, logDeriv_mul]
  · have hpow : logDeriv (fun w : ℂ => (w - ρ) ^ n) (ρ + (σ : ℂ)) = (n : ℂ) * ((σ : ℂ))⁻¹ := by
      have h1 := logDeriv_fun_pow (f := fun w : ℂ => w - ρ) (x := ρ + (σ : ℂ))
        ((differentiableAt_id (x := ρ + (σ : ℂ))).sub_const ρ) n
      rw [h1]
      congr 1
      rw [logDeriv_apply, deriv_sub_const, deriv_id'', one_div]
      rw [add_sub_cancel_left]
    rw [hpow]
    have him : (((n : ℂ) * ((σ : ℂ))⁻¹ + logDeriv g (ρ + (σ : ℂ))).im)
        = (logDeriv g (ρ + (σ : ℂ))).im := by
      rw [Complex.add_im]
      have h2 : (((n : ℂ) * ((σ : ℂ))⁻¹).im) = 0 := by
        have h3 : ((σ : ℂ))⁻¹ = (((σ⁻¹ : ℝ)) : ℂ) := by
          rw [← Complex.ofReal_inv]
        rw [h3]
        simp
      rw [h2, zero_add]
    rw [him]
    calc |(logDeriv g (ρ + (σ : ℂ))).im| ≤ ‖logDeriv g (ρ + (σ : ℂ))‖ := Complex.abs_im_le_norm _
      _ ≤ C := hlogg
  · have : ((ρ + (σ : ℂ)) - ρ) ^ n ≠ 0 := by
      rw [add_sub_cancel_left]
      exact pow_ne_zero n (by exact_mod_cast hσne)
    simpa using this
  · exact hgz0
  · exact (by fun_prop : DifferentiableAt ℂ (fun w : ℂ => (w - ρ) ^ n) (ρ + (σ : ℂ)))
  · exact hgdz

/-- The L-function of a non-trivial character is not locally zero at any point. -/
private lemma not_eventually_zero_LFunction {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (hχ : χ ≠ 1) (ρ : ℂ) :
    ¬ Filter.Eventually (fun z : ℂ => DirichletCharacter.LFunction χ z = 0) (𝓝 ρ) := by
  intro h
  have hdiff : Differentiable ℂ (DirichletCharacter.LFunction χ) :=
    DirichletCharacter.differentiable_LFunction hχ
  have hzero : DirichletCharacter.LFunction χ = fun _ : ℂ => (0 : ℂ) := by
    funext x
    have heq := AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq
      (f := DirichletCharacter.LFunction χ) (g := fun _ : ℂ => (0 : ℂ)) (U := Set.univ)
      (fun z _ => hdiff.analyticAt z) (fun z _ => analyticAt_const) isPreconnected_univ
      (Set.mem_univ ρ) h
    exact heq (Set.mem_univ x)
  have h2 : DirichletCharacter.LFunction χ 2 ≠ 0 := by
    have h1 : ‖DirichletCharacter.LFunction χ (2 : ℂ) - 1‖ ≤ 13 / 20 :=
      norm_LFunction_sub_one_le χ (by norm_num : (2 : ℝ) ≤ (2 : ℂ).re)
    intro hc
    rw [hc] at h1
    norm_num at h1
  exact h2 (by rw [hzero])

/-- Pointwise boundedness of `Im logDeriv L` along the horizontal segment `[1/2, 2]`. -/
private lemma im_logDeriv_bounded_on_segment {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (hχ : χ ≠ 1) (T : ℝ) (Z : Finset ℝ)
    (hZ : ∀ σ : ℝ, σ ∈ Set.Icc (1 / 2) 2 →
        (DirichletCharacter.LFunction χ ((σ : ℂ) + (T : ℂ) * Complex.I)).re = 0 → σ ∈ Z) :
    ∃ C : ℝ, ∀ σ : ℝ, 1 / 2 ≤ σ → σ ≤ 2 →
      |(logDeriv (DirichletCharacter.LFunction χ) ((σ : ℂ) + (T : ℂ) * Complex.I)).im| ≤ C := by
  have hdiff : Differentiable ℂ (DirichletCharacter.LFunction χ) :=
    DirichletCharacter.differentiable_LFunction hχ
  -- local boundedness at every point of `ℝ`
  have hloc : ∀ σ₀ : ℝ, ∃ ε : ℝ, 0 < ε ∧ ∃ C : ℝ, ∀ σ : ℝ, |σ - σ₀| < ε →
      |(logDeriv (DirichletCharacter.LFunction χ) ((σ : ℂ) + (T : ℂ) * Complex.I)).im| ≤ C := by
    intro σ₀
    by_cases h0 : DirichletCharacter.LFunction χ ((σ₀ : ℂ) + (T : ℂ) * Complex.I) = 0
    · obtain ⟨η, C, hη, hC, hb⟩ := exists_bound_im_logDeriv_near_zero hdiff
        ((σ₀ : ℂ) + (T : ℂ) * Complex.I) (not_eventually_zero_LFunction χ hχ _) h0
      refine ⟨η, hη, C, fun σ hσ => ?_⟩
      by_cases hσeq : σ = σ₀
      · have hzero : logDeriv (DirichletCharacter.LFunction χ)
            ((σ : ℂ) + (T : ℂ) * Complex.I) = 0 := by
          rw [logDeriv_apply, hσeq, h0, div_zero]
        rw [hzero]
        simpa using hC.le
      · have h1 := hb (σ - σ₀) (by rw [abs_pos]; exact sub_ne_zero.mpr hσeq) hσ
        convert h1 using 2
        push_cast
        ring
    · have hcont : ContinuousAt (fun σ : ℝ =>
          (logDeriv (DirichletCharacter.LFunction χ) ((σ : ℂ) + (T : ℂ) * Complex.I)).im) σ₀ := by
        have hld0 : ContinuousAt (fun z : ℂ => logDeriv (DirichletCharacter.LFunction χ) z)
            ((σ₀ : ℂ) + (T : ℂ) * Complex.I) :=
          (hdiff.deriv.continuous.continuousAt).div hdiff.continuous.continuousAt h0
        have hld : ContinuousAt (fun z : ℂ => (logDeriv (DirichletCharacter.LFunction χ) z).im)
            ((σ₀ : ℂ) + (T : ℂ) * Complex.I) :=
          Complex.continuous_im.continuousAt.comp hld0
        have hcur : ContinuousAt (fun σ : ℝ => ((σ : ℂ) + (T : ℂ) * Complex.I)) σ₀ := by fun_prop
        exact ContinuousAt.comp (x := σ₀) (f := fun σ : ℝ => ((σ : ℂ) + (T : ℂ) * Complex.I))
          (g := fun z : ℂ => (logDeriv (DirichletCharacter.LFunction χ) z).im) hld hcur
      obtain ⟨δ, hδpos, hδ⟩ := Metric.continuousAt_iff.mp hcont 1 (by norm_num)
      set C₀ : ℝ := |(logDeriv (DirichletCharacter.LFunction χ) ((σ₀ : ℂ) + (T : ℂ) * Complex.I)).im| + 1 with hC₀def
      refine ⟨δ, hδpos, C₀, ?_⟩
      intro σ hσ
      have h1 := hδ (by rw [Real.dist_eq]; exact hσ)
      rw [Real.dist_eq] at h1
      have h3 : |(logDeriv (DirichletCharacter.LFunction χ) ((σ : ℂ) + (T : ℂ) * Complex.I)).im|
          - |(logDeriv (DirichletCharacter.LFunction χ) ((σ₀ : ℂ) + (T : ℂ) * Complex.I)).im|
          ≤ |(logDeriv (DirichletCharacter.LFunction χ) ((σ : ℂ) + (T : ℂ) * Complex.I)).im
            - (logDeriv (DirichletCharacter.LFunction χ) ((σ₀ : ℂ) + (T : ℂ) * Complex.I)).im| :=
        abs_sub_abs_le_abs_sub _ _
      rw [hC₀def]
      linarith
  choose ε hεpos C hC using hloc
  have hcover : Set.Icc (1 / 2 : ℝ) 2 ⊆ ⋃ σ₀ : ℝ, Metric.ball σ₀ (ε σ₀) := by
    intro σ _
    exact Set.mem_iUnion.mpr ⟨σ, by rw [Metric.mem_ball, dist_self]; exact hεpos σ⟩
  obtain ⟨t, ht⟩ := isCompact_Icc.elim_finite_subcover (fun σ₀ : ℝ => Metric.ball σ₀ (ε σ₀))
    (fun _ => Metric.isOpen_ball) hcover
  have htne : t.Nonempty := by
    rcases Set.mem_iUnion₂.mp (ht (show (1 : ℝ) ∈ Set.Icc (1 / 2) 2 by norm_num)) with ⟨σ₀, hσ₀, _⟩
    exact ⟨σ₀, hσ₀⟩
  refine ⟨max (t.sup' htne C) 0, fun σ h1 h2 => ?_⟩
  rcases Set.mem_iUnion₂.mp (ht ⟨h1, h2⟩) with ⟨σ₀, hσ₀t, hσ₀ball⟩
  rw [Metric.mem_ball, Real.dist_eq] at hσ₀ball
  have h1 : |(logDeriv (DirichletCharacter.LFunction χ) ((σ : ℂ) + (T : ℂ) * Complex.I)).im| ≤ C σ₀ :=
    hC σ₀ σ hσ₀ball
  exact h1.trans (le_trans (Finset.le_sup' C hσ₀t) (le_max_left _ _))


/-- **The integrated argument of a Dirichlet L-function along a horizontal segment is
`O(log (N T))`.**  This is the classical bound `S(T,χ) = O(log (qT))` for the argument of `L`
on the critical line, in the form needed for an explicit Riemann–von Mangoldt formula.
Proved via Backlund's trick: the number of zeros of `σ ↦ Re [L(σ+iT,χ)]` on `[1/2,2]` is
controlled by Jensen's inequality applied to the entire function
`F(s) = (L(s+iT,χ) + L(s-iT,χ⁻¹))/2` (commons lemma `reZeros_finset_log_bound`), and the
integral of `Im logDeriv L` along the segment is bounded by `π` times that zero count. -/
theorem LFunction_horizontal_argument_variation_bound {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1) (hχprim : χ.IsPrimitive) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T →
      |∫ σ : ℝ in (1/2)..2,
        (logDeriv (DirichletCharacter.LFunction χ) (σ + (T : ℂ) * Complex.I)).im| ≤
        C * Real.log (N * (T + 3)) := by
  obtain ⟨CZ, hCZpos, hZb⟩ := reZeros_finset_log_bound χ hχ hχprim
  refine ⟨Real.pi * (CZ + 1), by positivity, fun T hT => ?_⟩
  obtain ⟨Z, hZsub, hZzero, hZcard⟩ := hZb T hT
  have hbdd := im_logDeriv_bounded_on_segment χ hχ T Z hZzero
  have hmain := abs_integral_im_logDeriv_horizontal_le_card (DirichletCharacter.LFunction χ)
    (DirichletCharacter.differentiable_LFunction hχ) (T := T) (a := 1/2) (b := 2)
    (by norm_num) Z hZsub (fun σ h1 h2 => hZzero σ ⟨h1, h2⟩) hbdd
  have hlog1 : (1 : ℝ) ≤ Real.log ((N : ℝ) * (T + 3)) := by
    rw [← Real.log_exp 1]
    apply Real.log_le_log (Real.exp_pos 1)
    have hN : (1 : ℝ) ≤ (N : ℝ) := by
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne N)
    calc Real.exp 1 ≤ 3 := Real.exp_one_lt_three.le
      _ ≤ (N : ℝ) * (T + 3) := by nlinarith
  have hcard : (Z.card : ℝ) ≤ CZ * Real.log ((N : ℝ) * (T + 3)) := hZcard
  calc |∫ σ : ℝ in (1 / 2)..2,
        (logDeriv (DirichletCharacter.LFunction χ) (σ + (T : ℂ) * Complex.I)).im|
      ≤ (Z.card + 1) * Real.pi := hmain
    _ ≤ (CZ * Real.log ((N : ℝ) * (T + 3)) + 1) * Real.pi := by
        nlinarith [Real.pi_pos, hcard]
    _ ≤ (Real.pi * (CZ + 1)) * Real.log ((N : ℝ) * (T + 3)) := by
        nlinarith [Real.pi_pos, hlog1]

end Commons.NumberTheory.DirichletCharacter
