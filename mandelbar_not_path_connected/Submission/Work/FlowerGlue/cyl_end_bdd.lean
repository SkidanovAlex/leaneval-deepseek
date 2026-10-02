import Mathlib
import Submission.Work.FlowerGlue.cyl_prelim
import Submission.Work.FlowerGlue.cusp_away
import Submission.Work.FlowerGlue.analyticAt_of_bdd_punctured
import Submission.Work.FlowerGlue.int_continuous_const

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.FlowerGlue

open Complex Filter Function Function.Periodic
open scoped Real Topology

noncomputable section

/-! ## Elementary facts about the coordinate `e z = exp (2 π I z)` of the cylinder `ℂ / ℤ` -/

theorem e_cont : Continuous e := by
  have h : e = Function.Periodic.qParam 1 := funext fun z => e_eq_qParam z
  rw [h]; exact Function.Periodic.continuous_qParam

theorem e_differentiable : Differentiable ℂ e := by
  have h : e = Function.Periodic.qParam 1 := funext fun z => e_eq_qParam z
  rw [h]; exact Function.Periodic.differentiable_qParam

theorem e_zero : e 0 = 1 := by simp [e]

theorem e_neg (z : ℂ) : e (-z) = (e z)⁻¹ := by
  have h : e (-z) * e z = 1 := by rw [← e_add, neg_add_cancel, e_zero]
  exact eq_inv_of_mul_eq_one_left h

/-- `e` converts integer multiplication of the argument into an integer power. -/
theorem e_zpow (m : ℤ) (z : ℂ) : e ((m : ℂ) * z) = (e z) ^ m := by
  have h : (e z) ^ m = Complex.exp ((m : ℂ) * (2 * (Real.pi : ℂ) * Complex.I * z)) := by
    rw [e, ← Complex.exp_int_mul]
  rw [h, e]
  congr 1
  ring

theorem e_intCast (n : ℤ) : e (n : ℂ) = 1 := by
  have h := e_zpow n 1
  rw [mul_one, e_one, one_zpow] at h
  exact h

theorem e_sub (a b : ℂ) : e (a - b) = e a / e b := by
  conv_lhs => rw [sub_eq_add_neg]
  rw [e_add, e_neg, div_eq_mul_inv]

theorem norm_e_lt_exp_iff (Y : ℝ) (z : ℂ) :
    ‖e z‖ < Real.exp (-2 * Real.pi * Y) ↔ Y < z.im := by
  have h1 := Function.Periodic.norm_qParam_lt_iff (h := 1) (by norm_num) Y z
  rw [show -2 * Real.pi * Y / 1 = -2 * Real.pi * Y from by ring] at h1
  rwa [e_eq_qParam]

/-! ## The cusp function of `e ∘ T` -/

theorem eT_periodic {T : ℂ → ℂ} (hper : ∀ ζ : ℂ, T (ζ + 1) = T ζ + 1) :
    Function.Periodic (fun ζ => e (T ζ)) 1 := by
  intro ζ
  show e (T (ζ + 1)) = e (T ζ)
  rw [hper ζ, e_add, e_one, mul_one]

/-- The cusp function of `e ∘ T` evaluated at `e ζ` is `e (T ζ)`. -/
theorem cuspFunction_e_T {T : ℂ → ℂ} (hper : ∀ ζ : ℂ, T (ζ + 1) = T ζ + 1) (ζ : ℂ) :
    Function.Periodic.cuspFunction 1 (fun ζ => e (T ζ)) (e ζ) = e (T ζ) := by
  have h := Function.Periodic.eq_cuspFunction (h := 1) (f := fun ζ => e (T ζ)) one_ne_zero
    (eT_periodic hper) ζ
  simpa [e_eq_qParam] using h

/-- The cusp function of `e ∘ T` is holomorphic away from `0`. -/
theorem cuspFunction_e_T_diff {T : ℂ → ℂ} (hT : Differentiable ℂ T)
    (hper : ∀ ζ : ℂ, T (ζ + 1) = T ζ + 1) :
    ∀ q : ℂ, q ≠ 0 →
      DifferentiableAt ℂ (Function.Periodic.cuspFunction 1 (fun ζ => e (T ζ))) q := by
  intro q hq
  have hdiff : DifferentiableAt ℂ (fun ζ => e (T ζ)) (Function.Periodic.invQParam 1 q) :=
    e_differentiable.differentiableAt.comp _ (hT _)
  have h := Function.Periodic.differentiableAt_cuspFunction (h := 1) (f := fun ζ => e (T ζ))
    one_ne_zero (eT_periodic hper) (z := Function.Periodic.invQParam 1 q) hdiff
  rwa [Function.Periodic.qParam_right_inv one_ne_zero hq] at h

/-! ## Extracting an explicit radius from an `∀ᶠ` statement near `0` -/

theorem exists_radius_of_eventually_nhdsNE {p : ℂ → Prop} (h : ∀ᶠ q in 𝓝[≠] (0 : ℂ), p q) :
    ∃ ρ > 0, ∀ q : ℂ, q ≠ 0 → ‖q‖ < ρ → p q := by
  rw [eventually_nhdsWithin_iff] at h
  obtain ⟨ρ, hρ, hp⟩ := Metric.eventually_nhds_iff.mp h
  exact ⟨ρ, hρ, fun q hq hqρ => hp (by rwa [dist_zero_right]) hq⟩

/-! ## The order of a meromorphic function at `0` -/

/-- A meromorphic function at `0` which does not vanish in a punctured neighbourhood can be
written there as `q ^ m * u q` with `m : ℤ` and `u` analytic with `u 0 ≠ 0`. -/
theorem exists_int_zpow_mul_of_meromorphicAt {f : ℂ → ℂ} (hm : MeromorphicAt f 0)
    (hne : ∀ᶠ q in 𝓝[≠] (0 : ℂ), f q ≠ 0) :
    ∃ m : ℤ, ∃ u : ℂ → ℂ, AnalyticAt ℂ u 0 ∧ u 0 ≠ 0 ∧
      ∀ᶠ q in 𝓝[≠] (0 : ℂ), f q = q ^ m * u q := by
  have htop : meromorphicOrderAt f 0 ≠ ⊤ :=
    (meromorphicOrderAt_ne_top_iff_eventually_ne_zero hm).mpr hne
  obtain ⟨m, hm'⟩ := WithTop.ne_top_iff_exists.mp htop
  obtain ⟨u, hu_an, hu0, hfac⟩ := (meromorphicOrderAt_eq_int_iff hm).mp hm'.symm
  refine ⟨m, u, hu_an, hu0, ?_⟩
  filter_upwards [hfac] with q hq
  simpa using hq

/-! ## The upper half-plane is preconnected -/

theorem isPreconnected_im_gt (Y : ℝ) : IsPreconnected {ζ : ℂ | Y < ζ.im} :=
  (convex_halfSpace_im_gt Y).isPreconnected

/-! ## The log/monodromy lemma -/

/-- **Log-branch / monodromy step.** Suppose `exp (2 π I L ζ) = u (e ζ)` on the half-plane
`im ζ > Y`, where `u` is analytic and nonzero at `0`.  Then, on a (possibly larger) half-plane,
`L` equals an integer plus the principal logarithm of `u ∘ e`, divided by `2 π I`.

Indeed `q ↦ log (u q / u 0)` is a holomorphic logarithm of `u / u 0` near `0`, so
`L ζ - (log (u 0) + log (u (e ζ) / u 0)) / (2 π I)` is a continuous `ℤ`-valued function of `ζ`
on a half-plane; half-planes are preconnected, so it is constant (this is where the monodromy
of the logarithm around the omitted point `0` is killed). -/
theorem exists_int_exp_repr {L u : ℂ → ℂ} {Y : ℝ} (hL : Continuous L)
    (hu : AnalyticAt ℂ u 0) (hu0 : u 0 ≠ 0)
    (hid : ∀ ζ : ℂ, Y < ζ.im → Complex.exp (2 * Real.pi * Complex.I * L ζ) = u (e ζ)) :
    ∃ Y' : ℝ, Y ≤ Y' ∧ ∃ n : ℤ, ∀ ζ : ℂ, Y' < ζ.im →
      L ζ = (Complex.log (u 0) + Complex.log (u (e ζ) / u 0)) / (2 * Real.pi * Complex.I) + n := by
  have hℓ_an : AnalyticAt ℂ (fun q => Complex.log (u q / u 0)) 0 := by
    refine AnalyticAt.clog ?_ ?_
    · exact hu.div analyticAt_const hu0
    · rw [div_self hu0]
      exact Complex.mem_slitPlane_iff.mpr (Or.inl (by norm_num))
  have hg_ne : ∀ᶠ q in 𝓝 (0 : ℂ), u q / u 0 ≠ 0 := by
    have h1 : Tendsto (fun q => u q / u 0) (𝓝 (0 : ℂ)) (𝓝 (u 0 / u 0)) :=
      hu.continuousAt.tendsto.div_const (u 0)
    rw [div_self hu0] at h1
    exact h1.eventually_ne (by norm_num)
  have hcomb : ∀ᶠ q in 𝓝 (0 : ℂ),
      (u q / u 0 ≠ 0) ∧ ContinuousAt (fun q => Complex.log (u q / u 0)) q := by
    filter_upwards [hg_ne, hℓ_an.eventually_analyticAt] with q hne hana
    exact ⟨hne, hana.continuousAt⟩
  obtain ⟨r, hr, hrr⟩ := Metric.eventually_nhds_iff.mp hcomb
  set Yr : ℝ := -(Real.log r) / (2 * Real.pi) with hYr
  set Y' : ℝ := max Y Yr with hY'
  set k : ℂ → ℂ := fun ζ => L ζ - (Complex.log (u 0) + Complex.log (u (e ζ) / u 0))
      / (2 * Real.pi * Complex.I) with hk
  have hexpr : Real.exp (-2 * Real.pi * Yr) = r := by
    rw [hYr, show -2 * Real.pi * (-(Real.log r) / (2 * Real.pi)) = Real.log r from by field_simp,
      Real.exp_log hr]
  have hke : ∀ ζ : ℂ, Y' < ζ.im → dist (e ζ) 0 < r := by
    intro ζ hζ
    rw [dist_zero_right]
    have : Yr < ζ.im := lt_of_le_of_lt (le_max_right Y Yr) hζ
    have h := (norm_e_lt_exp_iff Yr ζ).mpr this
    rwa [hexpr] at h
  have hk_cont : ContinuousOn k {ζ : ℂ | Y' < ζ.im} := by
    intro ζ hζ
    have h1 : ContinuousAt L ζ := hL.continuousAt
    have h2 : ContinuousAt (fun ζ => Complex.log (u (e ζ) / u 0)) ζ :=
      ((hrr (hke ζ hζ)).2).comp e_cont.continuousAt
    have h3 : ContinuousAt (fun ζ => (Complex.log (u 0) + Complex.log (u (e ζ) / u 0))
        / (2 * Real.pi * Complex.I)) ζ :=
      (continuousAt_const.add h2).div_const _
    exact (h1.sub h3).continuousWithinAt
  have hk_int : ∀ ζ ∈ {ζ : ℂ | Y' < ζ.im}, ∃ n : ℤ, k ζ = n := by
    intro ζ hζ
    have hY_lt : Y < ζ.im := lt_of_le_of_lt (le_max_left Y Yr) hζ
    have hw : Complex.exp (Complex.log (u (e ζ) / u 0)) = u (e ζ) / u 0 :=
      Complex.exp_log (hrr (hke ζ hζ)).1
    have hexp : Complex.exp (2 * Real.pi * Complex.I * L ζ)
        = Complex.exp (Complex.log (u 0) + Complex.log (u (e ζ) / u 0)) := by
      rw [hid ζ hY_lt, Complex.exp_add, Complex.exp_log hu0, hw]
      field_simp
    obtain ⟨n, hn⟩ := Complex.exp_eq_exp_iff_exists_int.mp hexp
    refine ⟨n, ?_⟩
    rw [hk]
    simp only
    have key : L ζ = (Complex.log (u 0) + Complex.log (u (e ζ) / u 0))
        / (2 * (Real.pi : ℂ) * Complex.I) + (n : ℂ) := by
      field_simp at hn ⊢
      linear_combination hn
    rw [key]
    ring
  obtain ⟨n, hn⟩ := hk_int ((Y' + 1) * Complex.I) (by simp)
  refine ⟨Y', le_max_left Y Yr, n, fun ζ hζ => ?_⟩
  have hζ0 : Y' < ((Y' + 1) * Complex.I).im := by simp
  have hconst := int_continuous_const (isPreconnected_im_gt Y') hk_cont hk_int hζ hζ0
  have hkz : L ζ - (Complex.log (u 0) + Complex.log (u (e ζ) / u 0)) / (2 * Real.pi * Complex.I)
      = (n : ℂ) := by
    have h1 : k ζ = (n : ℂ) := by rw [hconst, hn]
    simpa only [hk] using h1
  linear_combination hkz

/-! ## Order data for the cusp function `H` of `e ∘ T` -/

/-- `H (e ζ) = e (T ζ)`, `H` is holomorphic away from `0`, avoids a punctured neighbourhood of
`e (T 0)`, hence is meromorphic at `0`, and `H q / q` can be written `q ^ m * u q` with `u`
analytic and nonzero at `0`. -/
theorem cyl_order_data {T : ℂ → ℂ} (hT : Differentiable ℂ T) (hinj : Function.Injective T)
    (hper : ∀ ζ : ℂ, T (ζ + 1) = T ζ + 1) :
    ∃ (m : ℤ) (u : ℂ → ℂ), AnalyticAt ℂ u 0 ∧ u 0 ≠ 0 ∧
      (∀ᶠ q in 𝓝[≠] (0 : ℂ),
        Function.Periodic.cuspFunction 1 (fun ζ => e (T ζ)) q / q = q ^ m * u q) := by
  obtain ⟨δ, hδpos, ρ, hρpos, hρ⟩ := cusp_away hT hinj hper
  set H : ℂ → ℂ := Function.Periodic.cuspFunction 1 (fun ζ => e (T ζ)) with hH
  set ea : ℂ := e (T 0) with hea
  have hH_diff : ∀ q : ℂ, q ≠ 0 → DifferentiableAt ℂ H q := cuspFunction_e_T_diff hT hper
  have hH_e : ∀ ζ : ℂ, H (e ζ) = e (T ζ) := cuspFunction_e_T hper
  have hne_ea : ∀ q : ℂ, q ≠ 0 → ‖q‖ < ρ → H q - ea ≠ 0 := by
    intro q hq hqρ hzero
    have hle := hρ q hq hqρ
    rw [hzero, norm_zero] at hle
    linarith
  have hR_diff : DifferentiableOn ℂ (fun q => (H q - ea)⁻¹) (Metric.ball 0 ρ \ {0}) := by
    intro q hq
    have hq1 : ‖q‖ < ρ := by
      have := hq.1
      rwa [Metric.mem_ball, dist_zero_right] at this
    exact (((hH_diff q hq.2).sub_const ea).inv (hne_ea q hq.2 hq1)).differentiableWithinAt
  have hR_bdd : BddAbove (norm ∘ (fun q => (H q - ea)⁻¹) '' (Metric.ball 0 ρ \ {0})) := by
    refine ⟨δ⁻¹, ?_⟩
    rintro y ⟨q, hq, rfl⟩
    have hq1 : ‖q‖ < ρ := by
      have := hq.1
      rwa [Metric.mem_ball, dist_zero_right] at this
    have hle := hρ q hq.2 hq1
    have hpos : 0 < ‖H q - ea‖ := lt_of_lt_of_le hδpos hle
    simp only [Function.comp_apply, norm_inv]
    exact (inv_le_inv₀ hpos hδpos).mpr hle
  obtain ⟨F, hF_an, hF_eq⟩ := analyticAt_of_bdd_punctured hρpos hR_diff hR_bdd
  obtain ⟨ρ₁, hρ₁pos, hρ₁⟩ := exists_radius_of_eventually_nhdsNE hF_eq
  have hH_mero : MeromorphicAt H 0 := by
    have h1 : MeromorphicAt (fun q => ea + (F q)⁻¹) 0 :=
      (MeromorphicAt.const ea 0).add (hF_an.meromorphicAt.inv)
    refine h1.congr ?_
    filter_upwards [nhdsWithin_le_nhds (Metric.ball_mem_nhds (0 : ℂ) (lt_min hρpos hρ₁pos)),
      self_mem_nhdsWithin] with q hball hq0
    rw [Metric.mem_ball, dist_zero_right] at hball
    have hne := hne_ea q hq0 (lt_of_lt_of_le hball (min_le_left _ _))
    have hqF := hρ₁ q hq0 (lt_of_lt_of_le hball (min_le_right _ _))
    rw [hqF, inv_inv]
    ring
  have hP_mero : MeromorphicAt (fun q => H q / q) 0 := hH_mero.div (MeromorphicAt.id 0)
  have hP_ne : ∀ᶠ q in 𝓝[≠] (0 : ℂ), H q / q ≠ 0 := by
    filter_upwards [self_mem_nhdsWithin] with q hq0
    have hq_eq : q = e (Function.Periodic.invQParam 1 q) := by
      rw [e_eq_qParam]
      exact (Function.Periodic.qParam_right_inv one_ne_zero hq0).symm
    rw [hq_eq, hH_e]
    exact div_ne_zero (e_ne_zero _) (e_ne_zero _)
  obtain ⟨m, u, hu_an, hu0, hfac⟩ := exists_int_zpow_mul_of_meromorphicAt hP_mero hP_ne
  exact ⟨m, u, hu_an, hu0, hfac⟩

/-- **C3** of `Submission/Work/NOTES_LEAD_mandelbar_gaps2.md` §1.1. If `T : ℂ → ℂ` is entire, injective and `1`-equivariant, then `T - id` is bounded at the upper end of the cylinder `ℂ/ℤ`, i.e. for large `im ζ`. The full proof plan (cusp function `cuspFunction 1 (e ∘ T)`, the omitted-tube bounds `cyl_omit`/`exp_sep` from `Submission.Work.FlowerGlue.cyl_prelim`, removable singularity, meromorphic order, and a log-branch argument forcing the order to be `0`) is in §1.1 of that note. -/
theorem cyl_end_bdd {T : ℂ → ℂ} (hT : Differentiable ℂ T) (hinj : Function.Injective T)
    (hper : ∀ ζ : ℂ, T (ζ + 1) = T ζ + 1) :
    ∃ Y M : ℝ, ∀ ζ : ℂ, Y < ζ.im → ‖T ζ - ζ‖ ≤ M := by
  obtain ⟨m, u, hu_an, hu0, hfac⟩ := cyl_order_data hT hinj hper
  have hH_e : ∀ ζ : ℂ, Function.Periodic.cuspFunction 1 (fun ζ => e (T ζ)) (e ζ) = e (T ζ) :=
    cuspFunction_e_T hper
  obtain ⟨ρ₂, hρ₂pos, hρ₂⟩ := exists_radius_of_eventually_nhdsNE hfac
  set Y : ℝ := -(Real.log ρ₂) / (2 * Real.pi) with hY
  have hexpY : Real.exp (-2 * Real.pi * Y) = ρ₂ := by
    rw [hY, show -2 * Real.pi * (-(Real.log ρ₂) / (2 * Real.pi)) = Real.log ρ₂ from by field_simp,
      Real.exp_log hρ₂pos]
  set L : ℂ → ℂ := fun ζ => T ζ - ζ - (m : ℂ) * ζ with hLdef
  have hid : ∀ ζ : ℂ, Y < ζ.im → Complex.exp (2 * Real.pi * Complex.I * L ζ) = u (e ζ) := by
    intro ζ hζ
    have hlt : ‖e ζ‖ < ρ₂ := by
      have h := (norm_e_lt_exp_iff Y ζ).mpr hζ
      rwa [hexpY] at h
    have hfac_q : Function.Periodic.cuspFunction 1 (fun ζ => e (T ζ)) (e ζ) / (e ζ)
        = (e ζ) ^ m * u (e ζ) := hρ₂ (e ζ) (e_ne_zero ζ) hlt
    show e (T ζ - ζ - (m : ℂ) * ζ) = u (e ζ)
    rw [e_sub, e_sub, ← hH_e ζ, e_zpow, hfac_q]
    exact mul_div_cancel_left₀ _ (zpow_ne_zero m (e_ne_zero ζ))
  have hL_cont : Continuous L :=
    (hT.continuous.sub continuous_id).sub (continuous_const.mul continuous_id)
  obtain ⟨Y₁, _hY₁, n₁, hrepr₁⟩ :=
    exists_int_exp_repr (L := L) (u := u) (Y := Y) hL_cont hu_an hu0 hid
  have hshift : ∀ ζ : ℂ, Y₁ < ζ.im → L (ζ + 1) = L ζ := by
    intro ζ hζ
    have hζ' : Y₁ < (ζ + 1).im := by simpa using hζ
    rw [hrepr₁ (ζ + 1) hζ', hrepr₁ ζ hζ]
    rw [show e (ζ + 1) = e ζ from by rw [e_add, e_one, mul_one]]
  have hm0 : m = 0 := by
    have hζ₀ : Y₁ < ((Y₁ + 1) * Complex.I).im := by simp
    have h0 := hshift ((Y₁ + 1) * Complex.I) hζ₀
    have hlin : L (((Y₁ + 1) * Complex.I) + 1) - L ((Y₁ + 1) * Complex.I) = -(m : ℂ) := by
      rw [hLdef]
      simp only
      rw [hper]
      ring
    rw [h0, sub_self] at hlin
    have hmz : (m : ℂ) = 0 := by simpa using hlin
    exact Int.cast_eq_zero.mp hmz
  have hid0 : ∀ ζ : ℂ, Y < ζ.im → Complex.exp (2 * Real.pi * Complex.I * (T ζ - ζ)) = u (e ζ) := by
    intro ζ hζ
    have h := hid ζ hζ
    simpa [hLdef, hm0] using h
  obtain ⟨Y₂, _hY₂, n₂, hrepr₂⟩ := exists_int_exp_repr (L := fun ζ => T ζ - ζ) (u := u) (Y := Y)
    (hT.continuous.sub continuous_id) hu_an hu0 hid0
  have hg_tend : Tendsto (fun q => u q / u 0) (𝓝 (0 : ℂ)) (𝓝 1) := by
    have h1 : Tendsto (fun q => u q / u 0) (𝓝 (0 : ℂ)) (𝓝 (u 0 / u 0)) :=
      hu_an.continuousAt.tendsto.div_const (u 0)
    rwa [div_self hu0] at h1
  have hball_ev : ∀ᶠ q in 𝓝 (0 : ℂ), u q / u 0 ∈ Metric.ball 1 (1 / 2) :=
    hg_tend.eventually (Metric.ball_mem_nhds 1 (by norm_num))
  obtain ⟨ρ₃, hρ₃pos, hρ₃⟩ := Metric.eventually_nhds_iff.mp hball_ev
  set Y₃ : ℝ := -(Real.log ρ₃) / (2 * Real.pi) with hY₃
  have hexpY₃ : Real.exp (-2 * Real.pi * Y₃) = ρ₃ := by
    rw [hY₃, show -2 * Real.pi * (-(Real.log ρ₃) / (2 * Real.pi)) = Real.log ρ₃ from by field_simp,
      Real.exp_log hρ₃pos]
  have hlog_bound : ∀ ζ : ℂ, Y₃ < ζ.im → ‖Complex.log (u (e ζ) / u 0)‖ ≤ 3 / 4 := by
    intro ζ hζ
    have hlt : ‖e ζ‖ < ρ₃ := by
      have h := (norm_e_lt_exp_iff Y₃ ζ).mpr hζ
      rwa [hexpY₃] at h
    have hmem := hρ₃ (by rwa [dist_zero_right] : dist (e ζ) 0 < ρ₃)
    rw [Metric.mem_ball, dist_eq_norm] at hmem
    have hle : ‖u (e ζ) / u 0 - 1‖ ≤ 1 / 2 := le_of_lt hmem
    have h := Complex.norm_log_one_add_half_le_self (z := u (e ζ) / u 0 - 1) hle
    have hone : (1 : ℂ) + (u (e ζ) / u 0 - 1) = u (e ζ) / u 0 := by ring
    rw [hone] at h
    linarith
  have hden : ‖(2 * (Real.pi : ℂ) * Complex.I)‖ = 2 * Real.pi := by
    rw [norm_mul, norm_mul, Complex.norm_I, mul_one]
    norm_num
  refine ⟨max Y₂ Y₃, (‖Complex.log (u 0)‖ + 1) / (2 * Real.pi) + ‖(n₂ : ℂ)‖, fun ζ hζ => ?_⟩
  have hζ₂ : Y₂ < ζ.im := lt_of_le_of_lt (le_max_left _ _) hζ
  have hζ₃ : Y₃ < ζ.im := lt_of_le_of_lt (le_max_right _ _) hζ
  have hrepr := hrepr₂ ζ hζ₂
  have hlog := hlog_bound ζ hζ₃
  have hpi : (0 : ℝ) < 2 * Real.pi := by positivity
  calc ‖T ζ - ζ‖
      = ‖(Complex.log (u 0) + Complex.log (u (e ζ) / u 0)) / (2 * Real.pi * Complex.I)
          + (n₂ : ℂ)‖ := by rw [hrepr]
    _ ≤ ‖(Complex.log (u 0) + Complex.log (u (e ζ) / u 0)) / (2 * Real.pi * Complex.I)‖
          + ‖(n₂ : ℂ)‖ := norm_add_le _ _
    _ = ‖Complex.log (u 0) + Complex.log (u (e ζ) / u 0)‖ / (2 * Real.pi) + ‖(n₂ : ℂ)‖ := by
        rw [norm_div, hden]
    _ ≤ (‖Complex.log (u 0)‖ + 3 / 4) / (2 * Real.pi) + ‖(n₂ : ℂ)‖ := by
        refine add_le_add ?_ le_rfl
        refine div_le_div_of_nonneg_right ?_ hpi.le
        linarith [norm_add_le (Complex.log (u 0)) (Complex.log (u (e ζ) / u 0))]
    _ ≤ (‖Complex.log (u 0)‖ + 1) / (2 * Real.pi) + ‖(n₂ : ℂ)‖ := by
        refine add_le_add ?_ le_rfl
        refine div_le_div_of_nonneg_right ?_ hpi.le
        linarith

end

end Work.FlowerGlue
