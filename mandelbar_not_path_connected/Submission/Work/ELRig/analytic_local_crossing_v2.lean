/-
# Local structure of a real-analytic map `ℝ → ℂ` with nonvanishing derivative at `0`

`Work.ELRig.analytic_local_crossing_v2`: if `f : ℝ → ℂ` is analytic at `0`, `f 0 = 0` and
`deriv f 0 ≠ 0`, then near `0` the modulus `t ↦ ‖f t‖` is strictly increasing on `[0, δ]`,
strictly decreasing on `[-δ, 0]`, and every level `μ ∈ (0, μ₀)` is attained exactly once on
each side.

The proof is the honest Taylor/mean-value argument:

* `analytic_local_expansion` extracts, for any `η > 0`, a `δ > 0` with the first order
  estimates `‖f t - f'(0) t‖ ≤ η |t|` and `‖f' t - f'(0)‖ ≤ η` for `|t| < δ`
  (`AnalyticAt.differentiableAt` for the first, `AnalyticAt.contDiffAt` and continuity of
  `deriv` for the second).
* `normSq_deriv_pos` turns those two estimates into the sign of the derivative of
  `t ↦ ‖f t‖ ^ 2` on the two sides of `0`, via `HasDerivAt.norm_sq`.
* `strictMonoOn_of_deriv_pos` / `strictAntiOn_of_deriv_neg` give the monotonicity of
  `t ↦ ‖f t‖ ^ 2`, and `Real.sqrt_lt_sqrt` transfers it to `t ↦ ‖f t‖`.
* `unique_level_bijection` is the intermediate value theorem: each level below the minimum
  of the two endpoint values is attained exactly once on each side.
-/
import Mathlib

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


set_option linter.unusedVariables false

noncomputable section

namespace Work.ELRig

/-- First order (two-sided) expansion of a map `f : ℝ → ℂ` analytic at `0` with `f 0 = 0`:
for every `η > 0` there is `δ > 0` such that for `|t| < δ` both `f t` is `η`-close to
`f'(0) · t` and `f' t` is `η`-close to `f'(0)`. -/
lemma analytic_local_expansion {f : ℝ → ℂ} (han : AnalyticAt ℝ f 0) (h0 : f 0 = 0)
    (η : ℝ) (hη : 0 < η) :
    ∃ δ > 0, (∀ t : ℝ, |t| < δ → ‖f t - deriv f 0 * (t : ℂ)‖ ≤ η * |t|) ∧
      (∀ t : ℝ, |t| < δ → ‖deriv f t - deriv f 0‖ ≤ η) := by
  have hf0 : DifferentiableAt ℝ f 0 := han.differentiableAt
  have hd0 : HasDerivAt f (deriv f 0) 0 := hf0.hasDerivAt
  rw [hasDerivAt_iff_isLittleO_nhds_zero] at hd0
  rw [Asymptotics.isLittleO_iff] at hd0
  have hb1 : ∀ᶠ t in nhds (0:ℝ), ‖f t - deriv f 0 * (t:ℂ)‖ ≤ η * |t| := by
    have := hd0 hη
    filter_upwards [this] with t ht
    simpa [h0, Real.norm_eq_abs, Complex.real_smul, mul_comm] using ht
  obtain ⟨δ1, hδ1, hb1'⟩ := Metric.eventually_nhds_iff.mp hb1
  have hC1 : ContDiffAt ℝ 1 f 0 := (han.contDiffAt (n := ⊤)).of_le le_top
  have hcont : ContinuousAt (deriv f) 0 := (hC1.derivWithin (m := 0) (by simp)).continuousAt
  have hb2 : ∀ᶠ t in nhds (0:ℝ), ‖deriv f t - deriv f 0‖ ≤ η := by
    have := Metric.tendsto_nhds.mp hcont η hη
    filter_upwards [this] with t ht
    rw [dist_eq_norm] at ht
    exact le_of_lt ht
  obtain ⟨δ2, hδ2, hb2'⟩ := Metric.eventually_nhds_iff.mp hb2
  refine ⟨min δ1 δ2, lt_min hδ1 hδ2, ?_, ?_⟩
  · intro t ht
    apply hb1'
    rw [dist_eq_norm, Real.norm_eq_abs, sub_zero]
    exact lt_of_lt_of_le ht (min_le_left _ _)
  · intro t ht
    apply hb2'
    rw [dist_eq_norm, Real.norm_eq_abs, sub_zero]
    exact lt_of_lt_of_le ht (min_le_right _ _)

/-- A map analytic at `0` is differentiable at every point of a suitable ball around `0`. -/
lemma analytic_local_diffOn {f : ℝ → ℂ} (han : AnalyticAt ℝ f 0) :
    ∃ r > 0, ∀ t : ℝ, |t| < r → DifferentiableAt ℝ f t := by
  obtain ⟨r, hr, ha⟩ := han.exists_ball_analyticOnNhd
  refine ⟨r, hr, fun t ht => ?_⟩
  have hmem : t ∈ Metric.ball (0:ℝ) r := by
    simp only [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs]
    exact ht
  exact (ha t hmem).differentiableAt

/-- Sign of the derivative of `t ↦ ‖f t‖ ^ 2` on the two sides of `0`, from first order
estimates for `f` and `f'` around the nonvanishing value `a`. -/
lemma normSq_deriv_pos {f : ℝ → ℂ} {a : ℂ} {δ η : ℝ}
    (hδ : 0 < δ) (hη : 0 < η)
    (hineq : 2 * ‖a‖ * η + η ^ 2 < ‖a‖ ^ 2)
    (hdiff : ∀ t : ℝ, |t| < δ → DifferentiableAt ℝ f t)
    (h1 : ∀ t : ℝ, |t| < δ → ‖f t - a * (t : ℂ)‖ ≤ η * |t|)
    (h2 : ∀ t : ℝ, |t| < δ → ‖deriv f t - a‖ ≤ η) :
    (∀ t ∈ Set.Ioo (0 : ℝ) δ, 0 < deriv (fun s : ℝ => ‖f s‖ ^ 2) t) ∧
    (∀ t ∈ Set.Ioo (-δ) (0 : ℝ), deriv (fun s : ℝ => ‖f s‖ ^ 2) t < 0) := by
  have hderiv : ∀ t, |t| < δ →
      deriv (fun s : ℝ => ‖f s‖ ^ 2) t = 2 * inner ℝ (f t) (deriv f t) := by
    intro t ht
    exact ((hdiff t ht).hasDerivAt.norm_sq).deriv
  have hcore : ∀ t, |t| < δ →
      |inner ℝ (f t) (deriv f t) - t * ‖a‖ ^ 2|
        ≤ (2 * ‖a‖ * η + η ^ 2) * |t| := by
    intro t ht
    set E : ℂ := f t - a * (t : ℂ) with hE
    set e : ℂ := deriv f t - a with he
    have hft : f t = a * (t : ℂ) + E := by rw [hE]; ring
    have hdt : deriv f t = a + e := by rw [he]; ring
    have hEbound : ‖E‖ ≤ η * |t| := by rw [hE]; exact h1 t ht
    have hebound : ‖e‖ ≤ η := by rw [he]; exact h2 t ht
    have hsmul : a * (t : ℂ) = t • a := by rw [Complex.real_smul, mul_comm]
    have hkey : inner ℝ (f t) (deriv f t)
        = t * ‖a‖ ^ 2 + inner ℝ (a * (t : ℂ)) e + inner ℝ E a + inner ℝ E e := by
      have hself : inner ℝ (a * (t : ℂ)) a = t * ‖a‖ ^ 2 := by
        rw [hsmul, real_inner_smul_left, real_inner_self_eq_norm_sq]
      rw [hft, hdt, inner_add_left, inner_add_right, inner_add_right, hself]
      ring
    have hAB : |inner ℝ (a * (t : ℂ)) e| ≤ ‖a‖ * |t| * η := by
      have h1' : ‖a * (t : ℂ)‖ = ‖a‖ * |t| := by rw [norm_mul]; simp
      calc |inner ℝ (a * (t : ℂ)) e| ≤ ‖a * (t : ℂ)‖ * ‖e‖ := abs_real_inner_le_norm _ _
        _ = ‖a‖ * |t| * ‖e‖ := by rw [h1']
        _ ≤ ‖a‖ * |t| * η := mul_le_mul_of_nonneg_left hebound (by positivity)
    have hB : |inner ℝ E a| ≤ η * |t| * ‖a‖ := by
      calc |inner ℝ E a| ≤ ‖E‖ * ‖a‖ := abs_real_inner_le_norm _ _
        _ ≤ η * |t| * ‖a‖ := mul_le_mul_of_nonneg_right hEbound (norm_nonneg a)
    have hC : |inner ℝ E e| ≤ η * |t| * η := by
      calc |inner ℝ E e| ≤ ‖E‖ * ‖e‖ := abs_real_inner_le_norm _ _
        _ ≤ η * |t| * η := mul_le_mul hEbound hebound (norm_nonneg _) (by positivity)
    have hsum : |inner ℝ (a * (t : ℂ)) e + inner ℝ E a + inner ℝ E e|
        ≤ (2 * ‖a‖ * η + η ^ 2) * |t| := by
      refine (abs_add_three _ _ _).trans ?_
      have hthis : ‖a‖ * |t| * η + η * |t| * ‖a‖ + η * |t| * η
          = (2 * ‖a‖ * η + η ^ 2) * |t| := by ring
      linarith [hAB, hB, hC, hthis.le, hthis.ge]
    have hfin : inner ℝ (f t) (deriv f t) - t * ‖a‖ ^ 2
        = inner ℝ (a * (t : ℂ)) e + inner ℝ E a + inner ℝ E e := by
      rw [hkey]; ring
    rw [hfin]; exact hsum
  constructor
  · intro t ht
    have htabs : |t| < δ := by rw [abs_of_pos ht.1]; exact ht.2
    rw [hderiv t htabs]
    have hlow := (abs_le.mp (hcore t htabs)).1
    have hpos : 0 < inner ℝ (f t) (deriv f t) := by
      rw [abs_of_pos ht.1] at hlow
      nlinarith [hineq, ht.1, hlow]
    linarith
  · intro t ht
    have htabs : |t| < δ := by rw [abs_of_neg ht.2]; linarith [ht.1]
    rw [hderiv t htabs]
    have hup := (abs_le.mp (hcore t htabs)).2
    have hneg : inner ℝ (f t) (deriv f t) < 0 := by
      rw [abs_of_neg ht.2] at hup
      nlinarith [hineq, ht.2, hup]
    linarith

/-- Intermediate value theorem: a continuous `φ` that is strictly increasing on `[0, δ]` and
strictly decreasing on `[-δ, 0]` with `φ 0 = 0` attains every level `μ ∈ (0, μ₀)` exactly once
on each side, provided `μ₀` is at most the two endpoint values. -/
lemma unique_level_bijection {φ : ℝ → ℝ} {δ μ₀ : ℝ} (hδ : 0 < δ)
    (hcont : ContinuousOn φ (Set.Icc (-δ) δ))
    (hmono : StrictMonoOn φ (Set.Icc 0 δ))
    (hanti : StrictAntiOn φ (Set.Icc (-δ) 0))
    (h0 : φ 0 = 0)
    (hμ : 0 < μ₀) (hpos : μ₀ ≤ φ δ) (hneg : μ₀ ≤ φ (-δ)) :
    (∀ μ ∈ Set.Ioo (0 : ℝ) μ₀, ∃! t : ℝ, t ∈ Set.Ioo (0 : ℝ) δ ∧ φ t = μ) ∧
    (∀ μ ∈ Set.Ioo (0 : ℝ) μ₀, ∃! t : ℝ, t ∈ Set.Ioo (-δ) 0 ∧ φ t = μ) := by
  have hcontP : ContinuousOn φ (Set.Icc (0:ℝ) δ) :=
    hcont.mono (Set.Icc_subset_Icc (by linarith) le_rfl)
  have hcontN : ContinuousOn φ (Set.Icc (-δ) (0:ℝ)) :=
    hcont.mono (Set.Icc_subset_Icc le_rfl (by linarith))
  constructor
  · intro μ hμmem
    have hlt : μ < φ δ := lt_of_lt_of_le hμmem.2 hpos
    obtain ⟨t0, ht0mem, ht0eq⟩ := (intermediate_value_Ioo (le_of_lt hδ) hcontP)
        (show μ ∈ Set.Ioo (φ 0) (φ δ) by rw [h0]; exact ⟨hμmem.1, hlt⟩)
    refine ⟨t0, ⟨ht0mem, ht0eq⟩, fun y hy => ?_⟩
    rcases lt_trichotomy y t0 with h | h | h
    · have hlt2 := hmono ⟨le_of_lt hy.1.1, le_of_lt hy.1.2⟩
        ⟨le_of_lt ht0mem.1, le_of_lt ht0mem.2⟩ h
      rw [hy.2, ht0eq] at hlt2
      exact absurd hlt2 (lt_irrefl μ)
    · exact h
    · have hlt2 := hmono ⟨le_of_lt ht0mem.1, le_of_lt ht0mem.2⟩
        ⟨le_of_lt hy.1.1, le_of_lt hy.1.2⟩ h
      rw [hy.2, ht0eq] at hlt2
      exact absurd hlt2 (lt_irrefl μ)
  · intro μ hμmem
    have hlt : μ < φ (-δ) := lt_of_lt_of_le hμmem.2 hneg
    obtain ⟨t0, ht0mem, ht0eq⟩ := (intermediate_value_Ioo' (by linarith : (-δ:ℝ) ≤ 0) hcontN)
        (show μ ∈ Set.Ioo (φ 0) (φ (-δ)) by rw [h0]; exact ⟨hμmem.1, hlt⟩)
    refine ⟨t0, ⟨ht0mem, ht0eq⟩, fun y hy => ?_⟩
    rcases lt_trichotomy y t0 with h | h | h
    · have hlt2 := hanti ⟨le_of_lt hy.1.1, le_of_lt hy.1.2⟩
        ⟨le_of_lt ht0mem.1, le_of_lt ht0mem.2⟩ h
      rw [hy.2, ht0eq] at hlt2
      exact absurd hlt2 (lt_irrefl μ)
    · exact h
    · have hlt2 := hanti ⟨le_of_lt ht0mem.1, le_of_lt ht0mem.2⟩
        ⟨le_of_lt hy.1.1, le_of_lt hy.1.2⟩ h
      rw [hy.2, ht0eq] at hlt2
      exact absurd hlt2 (lt_irrefl μ)

theorem analytic_local_crossing_v2 {f : ℝ → ℂ} (han : AnalyticAt ℝ f 0) (h0 : f 0 = 0)
    (hd : deriv f 0 ≠ 0) :
    ∃ δ > 0, ∃ μ₀ > 0,
      StrictMonoOn (fun t : ℝ => ‖f t‖) (Set.Icc 0 δ) ∧
      StrictAntiOn (fun t : ℝ => ‖f t‖) (Set.Icc (-δ) 0) ∧
      (∀ μ ∈ Set.Ioo (0 : ℝ) μ₀, ∃! t : ℝ, t ∈ Set.Ioo (0 : ℝ) δ ∧ ‖f t‖ = μ) ∧
      (∀ μ ∈ Set.Ioo (0 : ℝ) μ₀, ∃! t : ℝ, t ∈ Set.Ioo (-δ) 0 ∧ ‖f t‖ = μ) := by
  have ha : 0 < ‖deriv f 0‖ := norm_pos_iff.mpr hd
  obtain ⟨r, hr, hrdiff⟩ := analytic_local_diffOn han
  obtain ⟨δ0, hδ0, h1, h2⟩ := analytic_local_expansion han h0 (‖deriv f 0‖ / 8)
    (div_pos ha (by norm_num))
  set δ := min δ0 (r/2) with hδdef
  have hδpos : 0 < δ := lt_min hδ0 (by positivity)
  have hδr : δ < r := lt_of_le_of_lt (min_le_right _ _) (by linarith)
  have hdiff : ∀ t, |t| < δ → DifferentiableAt ℝ f t :=
    fun t ht => hrdiff t (lt_trans ht hδr)
  have h1' : ∀ t, |t| < δ → ‖f t - deriv f 0 * (t:ℂ)‖ ≤ (‖deriv f 0‖/8) * |t| :=
    fun t ht => h1 t (lt_of_lt_of_le ht (min_le_left _ _))
  have h2' : ∀ t, |t| < δ → ‖deriv f t - deriv f 0‖ ≤ ‖deriv f 0‖/8 :=
    fun t ht => h2 t (lt_of_lt_of_le ht (min_le_left _ _))
  have hineq : 2 * ‖deriv f 0‖ * (‖deriv f 0‖/8) + (‖deriv f 0‖/8)^2 < ‖deriv f 0‖^2 := by
    nlinarith [ha]
  obtain ⟨hposd, hnegd⟩ := normSq_deriv_pos hδpos (div_pos ha (by norm_num)) hineq hdiff h1' h2'
  have hcont : ContinuousOn (fun t : ℝ => ‖f t‖) (Set.Icc (-δ) δ) := by
    have hc : ContinuousOn f (Set.Icc (-δ) δ) := fun x hx =>
      (hrdiff x (lt_of_le_of_lt (abs_le.mpr ⟨hx.1, hx.2⟩) hδr)).continuousAt.continuousWithinAt
    exact hc.norm
  have hcontSq : ContinuousOn (fun t : ℝ => ‖f t‖^2) (Set.Icc (-δ) δ) := hcont.pow 2
  have hmonoSq : StrictMonoOn (fun t : ℝ => ‖f t‖^2) (Set.Icc 0 δ) := by
    apply strictMonoOn_of_deriv_pos (convex_Icc 0 δ)
      (hcontSq.mono (Set.Icc_subset_Icc (by linarith) le_rfl))
    intro x hx
    rw [interior_Icc] at hx
    exact hposd x hx
  have hantiSq : StrictAntiOn (fun t : ℝ => ‖f t‖^2) (Set.Icc (-δ) 0) := by
    apply strictAntiOn_of_deriv_neg (convex_Icc (-δ) 0)
      (hcontSq.mono (Set.Icc_subset_Icc le_rfl (by linarith)))
    intro x hx
    rw [interior_Icc] at hx
    exact hnegd x hx
  have hmono : StrictMonoOn (fun t : ℝ => ‖f t‖) (Set.Icc 0 δ) := by
    intro x hx y hy hxy
    change ‖f x‖ < ‖f y‖
    have hsq : ‖f x‖^2 < ‖f y‖^2 := hmonoSq hx hy hxy
    rw [← Real.sqrt_sq (norm_nonneg (f x)), ← Real.sqrt_sq (norm_nonneg (f y))]
    exact Real.sqrt_lt_sqrt (by positivity) hsq
  have hanti : StrictAntiOn (fun t : ℝ => ‖f t‖) (Set.Icc (-δ) 0) := by
    intro x hx y hy hxy
    change ‖f y‖ < ‖f x‖
    have hsq : ‖f y‖^2 < ‖f x‖^2 := hantiSq hx hy hxy
    rw [← Real.sqrt_sq (norm_nonneg (f y)), ← Real.sqrt_sq (norm_nonneg (f x))]
    exact Real.sqrt_lt_sqrt (by positivity) hsq
  have hf0norm : ‖f 0‖ = 0 := by rw [h0]; simp
  have hδnorm : 0 < ‖f δ‖ := by
    have h := hmono ⟨le_refl 0, hδpos.le⟩ ⟨hδpos.le, le_refl δ⟩ hδpos
    simpa [hf0norm] using h
  have hndnorm : 0 < ‖f (-δ)‖ := by
    have h := hanti ⟨le_refl (-δ), by linarith⟩ ⟨by linarith, le_refl 0⟩ (by linarith : -δ < 0)
    simpa [hf0norm] using h
  refine ⟨δ, hδpos, min ‖f δ‖ ‖f (-δ)‖, lt_min hδnorm hndnorm, hmono, hanti, ?_, ?_⟩
  · intro μ hμ
    exact (unique_level_bijection hδpos hcont hmono hanti (by simp [h0]) (lt_min hδnorm hndnorm)
      (min_le_left _ _) (min_le_right _ _)).1 μ hμ
  · intro μ hμ
    exact (unique_level_bijection hδpos hcont hmono hanti (by simp [h0]) (lt_min hδnorm hndnorm)
      (min_le_left _ _) (min_le_right _ _)).2 μ hμ

end Work.ELRig
