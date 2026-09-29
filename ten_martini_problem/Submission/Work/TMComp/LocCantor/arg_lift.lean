import Mathlib

open Set Filter
open scoped Topology

namespace Work.TMComp.LocCantor

noncomputable section

/-- Two complex numbers with the same exponential and distance `< 2 * π` are equal. -/
lemma exp_eq_of_norm_sub_lt {z w : ℂ} (h : Complex.exp z = Complex.exp w)
    (hlt : ‖z - w‖ < 2 * Real.pi) : z = w := by
  have h1 : Complex.exp (z - w) = 1 := Complex.exp_eq_exp_iff_exp_sub_eq_one.mp h
  obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.mp h1
  have him : (z - w).im = (n : ℝ) * (2 * Real.pi) := by
    rw [hn]
    simp [Complex.mul_im]
  have hπ : (0 : ℝ) < 2 * Real.pi := by positivity
  have hble : |(z - w).im| ≤ ‖z - w‖ := Complex.abs_im_le_norm _
  rw [him, abs_mul, abs_of_pos hπ] at hble
  have h4 : |(n : ℝ)| < 1 := by
    have h3 : |(n : ℝ)| * (2 * Real.pi) < 2 * Real.pi := by linarith
    rw [← div_self hπ.ne']
    exact (lt_div_iff₀ hπ).mpr h3
  have h4i : ((|n| : ℤ) : ℝ) < 1 := by simpa [Int.cast_abs] using h4
  have h5 : (|n| : ℤ) < 1 := by exact_mod_cast h4i
  have hn0 : n = 0 := Int.abs_lt_one_iff.mp h5
  have hz : z - w = 0 := by rw [hn, hn0]; simp
  exact sub_eq_zero.mp hz

/-- Two continuous complex-valued functions with the same exponential on an open
preconnected set differ by a constant there. -/
lemma eq_add_const_of_exp_eq {U : Set ℝ} (hUo : IsOpen U) (hUpc : IsPreconnected U)
    (hUn : U.Nonempty) {u v : ℝ → ℂ} (hu : ContinuousOn u U) (hv : ContinuousOn v U)
    (h : ∀ x ∈ U, Complex.exp (u x) = Complex.exp (v x)) :
    ∃ c : ℂ, ∀ x ∈ U, u x = v x + c := by
  obtain ⟨x₀, hx₀⟩ := hUn
  refine ⟨u x₀ - v x₀, ?_⟩
  have hWcont : ContinuousOn (fun x => u x - v x) U := hu.sub hv
  have hloc : ∀ x ∈ U, ∃ ε > 0, ∀ y ∈ U, |y - x| < ε → u y - v y = u x - v x := by
    intro x hx
    obtain ⟨ε₁, hε₁pos, hε₁sub⟩ : ∃ ε > 0, ∀ y, |y - x| < ε → y ∈ U := by
      rcases Metric.mem_nhds_iff.mp (hUo.mem_nhds hx) with ⟨r, hrpos, hrsub⟩
      exact ⟨r, hrpos, fun y hy => hrsub (by rw [Metric.mem_ball, Real.dist_eq]; exact hy)⟩
    have hcont : ContinuousAt (fun y => u y - v y) x :=
      (hWcont x hx).continuousAt (hUo.mem_nhds hx)
    rcases Metric.continuousAt_iff.mp hcont (2 * Real.pi) (by positivity) with
      ⟨ε₂, hε₂pos, hε₂⟩
    refine ⟨min ε₁ ε₂, lt_min hε₁pos hε₂pos, fun y hyU hy => ?_⟩
    have hy2 : |y - x| < ε₂ := lt_of_lt_of_le hy (min_le_right _ _)
    have hlt : ‖(u y - v y) - (u x - v x)‖ < 2 * Real.pi := by
      have hylt := hε₂ (x := y) (by rw [Real.dist_eq]; exact hy2)
      rwa [dist_eq_norm] at hylt
    have hey : Complex.exp (u y - v y) = Complex.exp (u x - v x) := by
      rw [Complex.exp_sub, Complex.exp_sub, h y hyU, h x hx,
        div_self (Complex.exp_ne_zero (v y)), div_self (Complex.exp_ne_zero (v x))]
    exact exp_eq_of_norm_sub_lt hey hlt
  haveI : PreconnectedSpace ↥U := Subtype.preconnectedSpace hUpc
  have hlc : IsLocallyConstant (fun x : ↥U => u x - v x) := by
    rw [IsLocallyConstant.iff_eventually_eq]
    intro x
    obtain ⟨ε, hεpos, hε⟩ := hloc (x : ℝ) x.2
    have hball : {y : ↥U | (y : ℝ) ∈ Metric.ball (x : ℝ) ε} ∈ 𝓝 x :=
      (continuous_subtype_val.continuousAt).preimage_mem_nhds (Metric.ball_mem_nhds _ hεpos)
    filter_upwards [hball] with y hy
    exact hε y y.2 (by rwa [Metric.mem_ball, Real.dist_eq] at hy)
  intro x hx
  have hc := IsLocallyConstant.apply_eq_of_isPreconnected hlc isPreconnected_univ
    (Set.mem_univ (⟨x, hx⟩ : ↥U)) (Set.mem_univ (⟨x₀, hx₀⟩ : ↥U))
  have hc' : u x - v x = u x₀ - v x₀ := hc
  rw [← hc']
  ring

/-- A continuous function `u` with `exp ∘ u` real analytic and non-vanishing is real analytic. -/
lemma analyticAt_of_exp_eq {F u : ℝ → ℂ} {x₀ : ℝ}
    (hu : Continuous u) (hF : AnalyticOnNhd ℝ F univ) (hFne : F x₀ ≠ 0)
    (h : ∀ x, Complex.exp (u x) = F x) : AnalyticAt ℝ u x₀ := by
  have hFat : AnalyticAt ℝ F x₀ := hF x₀ (mem_univ x₀)
  have hFcont : Continuous F := hF.continuous
  set c : ℂ := (‖F x₀‖ : ℂ) / F x₀ with hcdef
  have hcne : c ≠ 0 := by
    rw [hcdef]
    exact div_ne_zero (Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hFne)) hFne
  have hcx₀ : c * F x₀ = (‖F x₀‖ : ℂ) := by
    rw [hcdef]
    exact div_mul_cancel₀ _ hFne
  have hcmem : c * F x₀ ∈ Complex.slitPlane := by
    rw [hcx₀]
    exact Or.inl (by simpa using norm_pos_iff.mpr hFne)
  let L : ℂ → ℂ := fun w => Complex.log (c * w) - Complex.log c
  have hexpL : ∀ w : ℂ, w ≠ 0 → Complex.exp (L w) = w := by
    intro w hw
    change Complex.exp (Complex.log (c * w) - Complex.log c) = w
    rw [Complex.exp_sub, Complex.exp_log (mul_ne_zero hcne hw), Complex.exp_log hcne]
    field_simp
  have hLana : AnalyticAt ℝ L (F x₀) := by
    have hlog : AnalyticAt ℂ Complex.log (c * F x₀) := analyticAt_clog hcmem
    have hmul : AnalyticAt ℝ (fun w : ℂ => c * w) (F x₀) :=
      (analyticAt_const (v := c)).mul analyticAt_id
    have h1 : AnalyticAt ℝ (Complex.log ∘ (fun w : ℂ => c * w)) (F x₀) :=
      hlog.restrictScalars.comp hmul
    have h2 : AnalyticAt ℝ (fun w : ℂ => Complex.log (c * w) - Complex.log c) (F x₀) :=
      h1.sub analyticAt_const
    exact h2
  have hLFana : AnalyticAt ℝ (fun x => L (F x)) x₀ := hLana.comp hFat
  have hmem_nhds : {x : ℝ | c * F x ∈ Complex.slitPlane} ∈ 𝓝 x₀ :=
    (continuousAt_const.mul hFcont.continuousAt).preimage_mem_nhds
      (Complex.isOpen_slitPlane.mem_nhds hcmem)
  obtain ⟨ε, hεpos, hεsub⟩ := Metric.mem_nhds_iff.mp hmem_nhds
  set U : Set ℝ := Ioo (x₀ - ε) (x₀ + ε) with hUdef
  have hx₀U : x₀ ∈ U := by rw [hUdef]; exact ⟨by linarith, by linarith⟩
  have hUo : IsOpen U := by rw [hUdef]; exact isOpen_Ioo
  have hUpc : IsPreconnected U := by rw [hUdef]; exact isPreconnected_Ioo
  have hUn : U.Nonempty := ⟨x₀, hx₀U⟩
  have hmemU : ∀ x ∈ U, c * F x ∈ Complex.slitPlane := by
    intro x hx
    rw [hUdef] at hx
    refine hεsub (by
      rw [Metric.mem_ball, Real.dist_eq, abs_lt]
      exact ⟨by linarith [hx.1], by linarith [hx.2]⟩)
  have hLcont : ContinuousOn (fun x => L (F x)) U := by
    have hcf : ContinuousOn (fun x => c * F x) U :=
      (continuous_const.mul hFcont).continuousOn
    have hlog : ContinuousOn (fun x => Complex.log (c * F x)) U := hcf.clog hmemU
    have hsub : ContinuousOn (fun x => Complex.log (c * F x) - Complex.log c) U :=
      hlog.sub continuousOn_const
    exact hsub
  obtain ⟨c', hc'⟩ := eq_add_const_of_exp_eq hUo hUpc hUn hu.continuousOn hLcont
    (fun x hx => by
      rw [h x, hexpL (F x) (by rw [← h x]; exact Complex.exp_ne_zero _)])
  have hev : (fun x => L (F x) + c') =ᶠ[𝓝 x₀] u := by
    filter_upwards [hUo.mem_nhds hx₀U] with x hx
    exact (hc' x hx).symm
  exact (hLFana.add (analyticAt_const (v := c'))).congr hev

/-- A continuous `u` whose exponential is `1`-periodic has `im (u (x+1)) - im (u x)` constant
and equal to an integer multiple of `2π`. -/
lemma exists_int_of_exp_periodic_aux (u : ℝ → ℂ) (hu : Continuous u)
    (hper : ∀ x, Complex.exp (u (x + 1)) = Complex.exp (u x)) :
    ∃ k : ℤ, ∀ x, (u (x + 1)).im = (u x).im + (k : ℝ) * (2 * Real.pi) := by
  have hv : Continuous (fun x : ℝ => u (x + 1) - u x) :=
    (hu.comp (continuous_id.add continuous_const)).sub hu
  have hexp1 : ∀ x, Complex.exp (u (x + 1) - u x) = 1 := by
    intro x
    rw [Complex.exp_sub, hper x, div_self (Complex.exp_ne_zero _)]
  have hlc : IsLocallyConstant (fun x : ℝ => u (x + 1) - u x) := by
    rw [IsLocallyConstant.iff_eventually_eq]
    intro x
    rcases Metric.continuousAt_iff.mp hv.continuousAt (2 * Real.pi) (by positivity) with
      ⟨ε, hεpos, hε⟩
    filter_upwards [Metric.ball_mem_nhds x hεpos] with y hy
    have hb : ‖(u (y + 1) - u y) - (u (x + 1) - u x)‖ < 2 * Real.pi := by
      have hylt := hε (x := y) hy
      rwa [dist_eq_norm] at hylt
    exact exp_eq_of_norm_sub_lt (by rw [hexp1 y, hexp1 x]) hb
  have hconst : ∀ x, u (x + 1) - u x = u (1 + 1) - u 1 := fun x =>
    IsLocallyConstant.apply_eq_of_isPreconnected hlc (isPreconnected_uIcc (a := x) (b := 1))
      left_mem_uIcc right_mem_uIcc
  have hcexp : Complex.exp (u (1 + 1) - u 1) = 1 := hexp1 1
  obtain ⟨k, hk⟩ := Complex.exp_eq_one_iff.mp hcexp
  refine ⟨k, fun x => ?_⟩
  have hcim : (u (1 + 1) - u 1).im = (k : ℝ) * (2 * Real.pi) := by
    rw [hk]
    simp [Complex.mul_im]
  have him := congrArg Complex.im (hconst x)
  rw [Complex.sub_im, hcim] at him
  linarith

/-- Complexification of a real-analytic pair. -/
lemma analyticAt_ofReal_comp {g : ℝ → ℝ} {x : ℝ} (h : AnalyticAt ℝ g x) :
    AnalyticAt ℝ (fun y => (g y : ℂ)) x := by
  have h1 : AnalyticAt ℝ (fun y : ℝ => (y : ℂ)) (g x) := Complex.ofRealCLM.analyticAt (g x)
  exact h1.comp h

lemma analyticOnNhd_complexify (f : ℝ → ℝ × ℝ)
    (h1 : AnalyticOnNhd ℝ (fun x => (f x).1) univ)
    (h2 : AnalyticOnNhd ℝ (fun x => (f x).2) univ) :
    AnalyticOnNhd ℝ (fun x => ((f x).1 : ℂ) + ((f x).2 : ℂ) * Complex.I) univ := by
  intro x hx
  have h1x := analyticAt_ofReal_comp (h1 x hx)
  have h2x := analyticAt_ofReal_comp (h2 x hx)
  exact h1x.add (h2x.mul analyticAt_const)

theorem arg_lift (f : ℝ → ℝ × ℝ)
    (h1 : AnalyticOnNhd ℝ (fun x => (f x).1) univ)
    (h2 : AnalyticOnNhd ℝ (fun x => (f x).2) univ)
    (hper : ∀ x, f (x + 1) = f x) (hne : ∀ x, f x ≠ 0) :
    ∃ (k : ℤ) (η : ℝ → ℝ), AnalyticOnNhd ℝ η univ ∧ (∀ x, η (x + 1) = η x + (k : ℝ)) ∧
      ∀ x, ∃ r : ℝ, 0 < r ∧ (f x).1 = r * Real.cos (2 * Real.pi * η x) ∧
        (f x).2 = r * Real.sin (2 * Real.pi * η x) := by
  set F : ℝ → ℂ := fun x => ((f x).1 : ℂ) + ((f x).2 : ℂ) * Complex.I with hFdef
  have hFanal : AnalyticOnNhd ℝ F univ := by
    rw [hFdef]
    exact analyticOnNhd_complexify f h1 h2
  have hFcont : Continuous F := hFanal.continuous
  have hFne : ∀ x, F x ≠ 0 := by
    intro x hx
    refine hne x (Prod.ext ?_ ?_)
    · have h := congrArg Complex.re hx
      simpa [hFdef] using h
    · have h := congrArg Complex.im hx
      simpa [hFdef] using h
  have hFper : ∀ x, F (x + 1) = F x := by
    intro x
    simp only [hFdef]
    rw [hper x]
  have hSConn : IsSimplyConnected (univ : Set ℝ) :=
    (Homeomorph.Set.univ ℝ).toHomotopyEquiv.simplyConnectedSpace
  obtain ⟨u, hucont, huexp⟩ := Complex.exists_continuousOn_eqOn_exp_comp hSConn isOpen_univ
    hFcont.continuousOn (by rintro ⟨x, -, hx⟩; exact hFne x hx)
  have hu : Continuous u := continuousOn_univ.mp hucont
  have hueq : ∀ x, Complex.exp (u x) = F x := fun x => huexp (x := x) (mem_univ x)
  have huanal : AnalyticOnNhd ℝ u univ := fun x _ =>
    analyticAt_of_exp_eq hu hFanal (hFne x) hueq
  obtain ⟨k, hk⟩ := exists_int_of_exp_periodic_aux u hu
    (fun x => by rw [hueq (x + 1), hueq x, hFper x])
  refine ⟨k, fun x => (u x).im / (2 * Real.pi), ?_, ?_, ?_⟩
  · intro x hx
    have h1 : AnalyticAt ℝ (fun w : ℂ => w.im) (u x) := Complex.imCLM.analyticAt (u x)
    have him : AnalyticAt ℝ (fun y => (u y).im) x := h1.comp (huanal x hx)
    have hmul : AnalyticAt ℝ (fun y => (u y).im * (2 * Real.pi)⁻¹) x :=
      him.mul (analyticAt_const (v := (2 * Real.pi)⁻¹))
    refine hmul.congr ?_
    filter_upwards with y
    rw [div_eq_mul_inv]
  · intro x
    have h2π : (2 * Real.pi) ≠ 0 := by positivity
    have hmain : (u (x + 1)).im / (2 * Real.pi) = (u x).im / (2 * Real.pi) + (k : ℝ) := by
      rw [hk x, add_div, mul_div_assoc, div_self h2π, mul_one]
    exact hmain
  · intro x
    change ∃ r : ℝ, 0 < r ∧
      (f x).1 = r * Real.cos (2 * Real.pi * ((u x).im / (2 * Real.pi))) ∧
      (f x).2 = r * Real.sin (2 * Real.pi * ((u x).im / (2 * Real.pi)))
    refine ⟨Real.exp ((u x).re), Real.exp_pos _, ?_, ?_⟩
    · have hx1 : (f x).1 = (F x).re := by
        simp [hFdef, Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
          Complex.I_re, mul_zero, add_zero]
      have hid : 2 * Real.pi * ((u x).im / (2 * Real.pi)) = (u x).im := by field_simp
      rw [hx1, hid, ← hueq x, Complex.exp_re]
    · have hx2 : (f x).2 = (F x).im := by
        simp [hFdef, Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
          Complex.I_im, mul_one, zero_add]
      have hid : 2 * Real.pi * ((u x).im / (2 * Real.pi)) = (u x).im := by field_simp
      rw [hx2, hid, ← hueq x, Complex.exp_im]

end

end Work.TMComp.LocCantor
