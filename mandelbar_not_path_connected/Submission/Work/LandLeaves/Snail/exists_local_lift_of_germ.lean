import Mathlib

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.LandLeaves.Snail

open Filter
open scoped Topology

/-- The normalised ratio `f (exp Z) / exp Z / λ`, whose exponential equals `f (exp Z) / exp Z`. -/
private noncomputable def germPhi (f : ℂ → ℂ) (lam : ℂ) (Z : ℂ) : ℂ :=
  f (Complex.exp Z) / Complex.exp Z / lam

/-- The local lift of a germ with non-zero multiplier:
`germLift f λ Z = Z + log λ + log (f (exp Z) / (λ · exp Z))`. -/
private noncomputable def germLift (f : ℂ → ℂ) (lam : ℂ) (Z : ℂ) : ℂ :=
  Z + (Complex.log lam + Complex.log (germPhi f lam Z))

theorem exists_local_lift_of_germ {f : ℂ → ℂ} {lam : ℂ}
    (hf : AnalyticAt ℂ f 0) (hfix : f 0 = 0) (hder : deriv f 0 = lam) (hne : lam ≠ 0) :
    ∃ (F : ℂ → ℂ) (X : ℝ), (∀ Z : ℂ, Z.re < X → Complex.exp (F Z) = f (Complex.exp Z)) ∧
      DifferentiableOn ℂ F {Z : ℂ | Z.re < X} ∧
      Set.InjOn F {Z : ℂ | Z.re < X} ∧
      Filter.Tendsto (fun Z : ℂ => F Z - Z) (Filter.comap Complex.re Filter.atBot)
        (nhds (Complex.log lam)) := by
  classical
  -- ## Derivative facts at `0`
  have hsd : HasStrictDerivAt f lam 0 := by
    simpa only [hder] using hf.hasStrictDerivAt
  have htend : Filter.Tendsto (fun w : ℂ => f w / w) (nhdsWithin (0 : ℂ) {(0 : ℂ)}ᶜ)
      (nhds lam) := by
    have h := hsd.hasDerivAt.tendsto_slope
    refine h.congr' ?_
    filter_upwards with w
    rw [slope, hfix]
    simp [div_eq_mul_inv, mul_comm]
  have hlam_pos : 0 < ‖lam‖ := norm_pos_iff.mpr hne
  have hlam2 : 0 < ‖lam‖ / 2 := half_pos hlam_pos
  -- ## The three radii
  obtain ⟨rc, hrcpos, hrc⟩ :
      ∃ r > 0, ∀ w : ℂ, w ≠ 0 → ‖w‖ < r → ‖f w / w - lam‖ < ‖lam‖ / 2 := by
    have hev : ∀ᶠ w in nhdsWithin (0 : ℂ) {(0 : ℂ)}ᶜ, ‖f w / w - lam‖ < ‖lam‖ / 2 := by
      refine (htend.eventually (Metric.ball_mem_nhds lam hlam2)).mono ?_
      intro w hw
      simpa [Metric.mem_ball, dist_eq_norm] using hw
    rw [eventually_nhdsWithin_iff] at hev
    rw [Metric.eventually_nhds_iff] at hev
    obtain ⟨r, hr, hh⟩ := hev
    exact ⟨r, hr, fun w hwne hw => hh (by simpa [dist_eq_norm] using hw) (by simpa using hwne)⟩
  obtain ⟨rd, hrdpos, hrd⟩ : ∃ r > 0, ∀ w : ℂ, ‖w‖ < r → DifferentiableAt ℂ f w := by
    have h : ∀ᶠ w in nhds (0 : ℂ), AnalyticAt ℂ f w := by
      have h := (hf.analyticWithinAt (s := Set.univ)).eventually_analyticWithinAt
      simpa using h
    have h2 : ∀ᶠ w in nhds (0 : ℂ), DifferentiableAt ℂ f w :=
      h.mono fun w hw => hw.differentiableAt
    rw [Metric.eventually_nhds_iff] at h2
    obtain ⟨ε, hε, hh⟩ := h2
    exact ⟨ε, hε, fun w hw => hh (by simpa [dist_eq_norm] using hw)⟩
  obtain ⟨ri, hripos, hri⟩ : ∃ r > 0, Set.InjOn f (Metric.ball (0 : ℂ) r) := by
    have hev := hsd.eventually_left_inverse hne
    rw [Metric.eventually_nhds_iff] at hev
    obtain ⟨ε, hε, hh⟩ := hev
    refine ⟨ε, hε, ?_⟩
    intro x hx y hy hxy
    have hx' : HasStrictDerivAt.localInverse f lam 0 hsd hne (f x) = x :=
      hh (by simpa [dist_eq_norm] using hx)
    have hy' : HasStrictDerivAt.localInverse f lam 0 hsd hne (f y) = y :=
      hh (by simpa [dist_eq_norm] using hy)
    rw [← hx', ← hy', hxy]
  -- ## Combine the radii
  set R : ℝ := min rc (min rd ri) with hRdef
  have hRpos : 0 < R := by rw [hRdef]; exact lt_min hrcpos (lt_min hrdpos hripos)
  have hRc : R ≤ rc := by rw [hRdef]; exact min_le_left _ _
  have hRd : R ≤ rd := by rw [hRdef]; exact le_trans (min_le_right _ _) (min_le_left _ _)
  have hRi : R ≤ ri := by rw [hRdef]; exact le_trans (min_le_right _ _) (min_le_right _ _)
  -- ## Pointwise facts on the half plane `{re < log R}`
  have hexpn : ∀ Z : ℂ, Z.re < Real.log R → ‖Complex.exp Z‖ < R := by
    intro Z hZ
    have h1 : Real.exp Z.re < Real.exp (Real.log R) := Real.exp_lt_exp.mpr hZ
    rw [Real.exp_log hRpos] at h1
    simpa [Complex.norm_exp] using h1
  have hclos : ∀ Z : ℂ, Z.re < Real.log R →
      ‖f (Complex.exp Z) / Complex.exp Z - lam‖ < ‖lam‖ / 2 := by
    intro Z hZ
    exact hrc (Complex.exp Z) (Complex.exp_ne_zero Z)
      (lt_of_lt_of_le (hexpn Z hZ) hRc)
  have hphi1 : ∀ Z : ℂ, Z.re < Real.log R → ‖germPhi f lam Z - 1‖ < (1 : ℝ) / 2 := by
    intro Z hZ
    have hcl := hclos Z hZ
    have heq : germPhi f lam Z - 1 = (f (Complex.exp Z) / Complex.exp Z - lam) / lam := by
      simp only [germPhi]
      field_simp
    rw [heq, norm_div, div_lt_iff₀ hlam_pos]
    linarith
  have hphi_ne : ∀ Z : ℂ, Z.re < Real.log R → germPhi f lam Z ≠ 0 := by
    intro Z hZ h0
    have h1 := hphi1 Z hZ
    rw [h0] at h1
    norm_num at h1
  have hphi_slit : ∀ Z : ℂ, Z.re < Real.log R → germPhi f lam Z ∈ Complex.slitPlane := by
    intro Z hZ
    have h1 := hphi1 Z hZ
    have h2 := Complex.re_le_norm ((1 : ℂ) - germPhi f lam Z)
    rw [Complex.sub_re, Complex.one_re, norm_sub_rev] at h2
    rw [Complex.mem_slitPlane_iff]
    left
    linarith
  -- ## The lift identity
  have hexp_id : ∀ Z : ℂ, Z.re < Real.log R →
      Complex.exp (germLift f lam Z) = f (Complex.exp Z) := by
    intro Z hZ
    have hphi := hphi_ne Z hZ
    simp only [germLift]
    rw [Complex.exp_add, Complex.exp_add, Complex.exp_log hne, Complex.exp_log hphi]
    simp only [germPhi]
    have hu : Complex.exp Z ≠ 0 := Complex.exp_ne_zero Z
    field_simp
  -- ## The lift is differentiable on the half plane
  have hdiff : DifferentiableOn ℂ (germLift f lam) {Z : ℂ | Z.re < Real.log R} := by
    intro Z hZ
    have hfe : DifferentiableWithinAt ℂ (fun Z : ℂ => f (Complex.exp Z))
        {Z : ℂ | Z.re < Real.log R} Z :=
      (hrd (Complex.exp Z) (lt_of_lt_of_le (hexpn Z hZ) hRd)).comp_differentiableWithinAt Z
        Complex.differentiableAt_exp.differentiableWithinAt
    have hexpd : DifferentiableWithinAt ℂ (fun Z : ℂ => Complex.exp Z)
        {Z : ℂ | Z.re < Real.log R} Z := Complex.differentiableAt_exp.differentiableWithinAt
    have hdiv : DifferentiableWithinAt ℂ (fun Z : ℂ => f (Complex.exp Z) / Complex.exp Z)
        {Z : ℂ | Z.re < Real.log R} Z := hfe.div hexpd (Complex.exp_ne_zero Z)
    have hdiv2 : DifferentiableWithinAt ℂ (germPhi f lam) {Z : ℂ | Z.re < Real.log R} Z :=
      hdiv.div (differentiableWithinAt_const lam) hne
    have hlogc : DifferentiableWithinAt ℂ (fun Z : ℂ => Complex.log (germPhi f lam Z))
        {Z : ℂ | Z.re < Real.log R} Z :=
      (Complex.differentiableAt_log (hphi_slit Z hZ)).comp_differentiableWithinAt Z hdiv2
    exact differentiableWithinAt_id.add
      ((differentiableWithinAt_const (Complex.log lam)).add hlogc)
  -- ## The lift is injective on the half plane
  have hinj : Set.InjOn (germLift f lam) {Z : ℂ | Z.re < Real.log R} := by
    intro Z1 hZ1 Z2 hZ2 heq
    have hfexp : f (Complex.exp Z1) = f (Complex.exp Z2) := by
      rw [← hexp_id Z1 hZ1, heq, hexp_id Z2 hZ2]
    have hmem1 : Complex.exp Z1 ∈ Metric.ball (0 : ℂ) R := by
      rw [Metric.mem_ball, dist_eq_norm, sub_zero]; exact hexpn Z1 hZ1
    have hmem2 : Complex.exp Z2 ∈ Metric.ball (0 : ℂ) R := by
      rw [Metric.mem_ball, dist_eq_norm, sub_zero]; exact hexpn Z2 hZ2
    have hexpeq : Complex.exp Z1 = Complex.exp Z2 :=
      hri (Metric.ball_subset_ball hRi hmem1) (Metric.ball_subset_ball hRi hmem2) hfexp
    have hΦ : germPhi f lam Z1 = germPhi f lam Z2 :=
      congrArg (fun w => f w / w / lam) hexpeq
    simp only [germLift] at heq
    rw [hΦ] at heq
    exact add_right_cancel heq
  -- ## The drift tends to `log λ`
  have htendsto : Filter.Tendsto (fun Z : ℂ => germLift f lam Z - Z)
      (Filter.comap Complex.re Filter.atBot) (nhds (Complex.log lam)) := by
    have hrec : Filter.Tendsto Complex.re (Filter.comap Complex.re Filter.atBot)
        Filter.atBot := Filter.tendsto_comap
    have h1 : Filter.Tendsto (fun Z : ℂ => Real.exp Z.re) (Filter.comap Complex.re Filter.atBot)
        (nhds 0) := Real.tendsto_exp_atBot.comp hrec
    have hexp0 : Filter.Tendsto Complex.exp (Filter.comap Complex.re Filter.atBot) (nhds 0) := by
      rw [tendsto_zero_iff_norm_tendsto_zero]
      simpa [Complex.norm_exp] using h1
    have hexp0' : Filter.Tendsto Complex.exp (Filter.comap Complex.re Filter.atBot)
        (nhdsWithin (0 : ℂ) {(0 : ℂ)}ᶜ) := by
      rw [tendsto_nhdsWithin_iff]
      exact ⟨hexp0, Eventually.of_forall (fun Z => Complex.exp_ne_zero Z)⟩
    have hψexp : Filter.Tendsto (fun Z : ℂ => f (Complex.exp Z) / Complex.exp Z)
        (Filter.comap Complex.re Filter.atBot) (nhds lam) := htend.comp hexp0'
    have hφtend : Filter.Tendsto (fun Z : ℂ => f (Complex.exp Z) / Complex.exp Z / lam)
        (Filter.comap Complex.re Filter.atBot) (nhds 1) := by
      have hh := hψexp.div tendsto_const_nhds hne
      have hh' : Filter.Tendsto (fun Z : ℂ => f (Complex.exp Z) / Complex.exp Z / lam)
          (Filter.comap Complex.re Filter.atBot) (nhds (lam / lam)) := hh
      simpa [div_self hne] using hh'
    have hlog1 : ContinuousAt Complex.log 1 := by
      have hmem : (1 : ℂ) ∈ Complex.slitPlane := by
        rw [Complex.mem_slitPlane_iff]; left; norm_num
      exact (Complex.differentiableAt_log hmem).continuousAt
    have hlogtend : Filter.Tendsto
        (fun Z : ℂ => Complex.log (f (Complex.exp Z) / Complex.exp Z / lam))
        (Filter.comap Complex.re Filter.atBot) (nhds 0) := by
      have hh := hlog1.tendsto.comp hφtend
      have hh' : Filter.Tendsto
          (fun Z : ℂ => Complex.log (f (Complex.exp Z) / Complex.exp Z / lam))
          (Filter.comap Complex.re Filter.atBot) (nhds (Complex.log 1)) := hh
      simpa [Complex.log_one] using hh'
    have hfinal := hlogtend.const_add (Complex.log lam)
    refine Filter.Tendsto.congr' (Eventually.of_forall (fun Z => ?_)) (by simpa using hfinal)
    simp only [germLift, germPhi, add_sub_cancel_left]
  exact ⟨germLift f lam, Real.log R, hexp_id, hdiff, hinj, htendsto⟩

end Work.LandLeaves.Snail
