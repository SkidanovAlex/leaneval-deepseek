import Mathlib

/-!
# A smooth "squash" of the real line

For real numbers `θ < L` we construct a `C^∞` function `g : ℝ → ℝ` which

* is the identity on `(-∞, θ]`,
* is strictly increasing with everywhere strictly positive derivative,
* is bounded above by `L`, with `g s < L` for every `s`, and satisfies
  `g s → L` as `s → +∞`.

The construction is elementary.  Let `ψ₀ : ℝ → ℝ` be the `C^∞` function

`ψ₀ u = (1 - smoothTransition u) + smoothTransition u * exp (-u)`,

which equals `1` on `(-∞,0]`, is positive everywhere and decays like `exp (-u)`
at `+∞` (so it is integrable on `(0,∞)`, with positive integral `A`).  Its
derivative-free version is "close to a step"; the squash is obtained by
integrating a rescaling of it:

`g s = θ + ∫ t in 0..(s-θ), ψ₀ (ρ * t)` where `ρ = A / (L - θ)`.

Then `g` is the identity for `s ≤ θ` (because `ψ₀ = 1` on `(-∞,0]`), is smooth
(the primitive of a smooth function), strictly increasing, and tends to `L`
because `ρ * ∫₀^∞ ψ₀ = A / ρ = L - θ`.
-/

open MeasureTheory Real Filter Set

namespace Work.Noncompact.CompressionTube

noncomputable section

/-- The auxiliary smooth "step density": `1` on `(-∞,0]`, positive everywhere and
decaying like `exp (-u)` at `+∞`. -/
def squashDensity (u : ℝ) : ℝ :=
  (1 - Real.smoothTransition u) + Real.smoothTransition u * Real.exp (-u)

lemma squashDensity_contDiff : ContDiff ℝ ((⊤ : ℕ∞)) squashDensity := by
  unfold squashDensity
  apply ContDiff.add
  · exact (contDiff_const.sub (Real.smoothTransition.contDiff (n := ⊤)))
  · exact ((Real.smoothTransition.contDiff (n := ⊤)).mul
      (by fun_prop : ContDiff ℝ ((⊤ : ℕ∞)) (fun u : ℝ => Real.exp (-u))))

lemma squashDensity_eq_one_of_nonpos {u : ℝ} (h : u ≤ 0) : squashDensity u = 1 := by
  unfold squashDensity; rw [Real.smoothTransition.zero_of_nonpos h]; ring

lemma squashDensity_integrableOn : IntegrableOn squashDensity (Ioi 0) := by
  apply integrable_of_isBigO_exp_neg (a := 0) (b := 1) (by norm_num)
  · exact squashDensity_contDiff.continuous.continuousOn
  · rw [Asymptotics.isBigO_iff]
    refine ⟨1, ?_⟩
    filter_upwards [eventually_ge_atTop (1:ℝ)] with u hu
    simp only [one_mul, Real.norm_eq_abs]
    rw [abs_of_pos (by unfold squashDensity; rw [Real.smoothTransition.one_of_one_le hu]; positivity),
        abs_of_pos (Real.exp_pos _)]
    have h1 : -1 * u = -u := by ring
    rw [h1]
    unfold squashDensity
    rw [Real.smoothTransition.one_of_one_le hu]
    simp

lemma squashDensity_ge_exp_of_nonneg {u : ℝ} (h : 0 ≤ u) :
    Real.exp (-u) ≤ squashDensity u := by
  have hT0 : 0 ≤ Real.smoothTransition u := Real.smoothTransition.nonneg u
  have hT1 : Real.smoothTransition u ≤ 1 := Real.smoothTransition.le_one u
  have he : Real.exp (-u) ≤ 1 := by rw [Real.exp_le_one_iff]; linarith
  unfold squashDensity
  nlinarith [hT0, hT1, he, Real.exp_pos (-u)]

lemma squashDensity_pos (u : ℝ) : 0 < squashDensity u := by
  by_cases h : u ≤ 0
  · rw [squashDensity_eq_one_of_nonpos h]; norm_num
  · exact lt_of_lt_of_le (Real.exp_pos (-u))
      (squashDensity_ge_exp_of_nonneg (le_of_lt (not_le.mp h)))

lemma squashDensity_integral_pos : 0 < ∫ x in Ioi (0:ℝ), squashDensity x := by
  have hexp : IntegrableOn (fun x : ℝ => Real.exp (-x)) (Ioi 0) := by
    have := exp_neg_integrableOn_Ioi (0:ℝ) (b := 1) (by norm_num)
    simpa using this
  have hle : (1:ℝ) ≤ ∫ x in Ioi (0:ℝ), squashDensity x := by
    calc (1:ℝ) = ∫ x in Ioi (0:ℝ), Real.exp (-x) := integral_exp_neg_Ioi_zero.symm
      _ ≤ ∫ x in Ioi (0:ℝ), squashDensity x :=
        setIntegral_mono_on hexp squashDensity_integrableOn measurableSet_Ioi
          (fun x hx => squashDensity_ge_exp_of_nonneg (le_of_lt hx))
  linarith

theorem exists_smooth_squash (θ L : ℝ) (hθL : θ < L) :
    ∃ g : ℝ → ℝ,
      ContDiff ℝ ((⊤ : ℕ∞)) g ∧ StrictMono g ∧ (∀ s : ℝ, 0 < deriv g s) ∧
      (∀ s : ℝ, s ≤ θ → g s = s) ∧ (∀ s : ℝ, g s < L) ∧
      Filter.Tendsto g Filter.atTop (nhds L) := by
  set c : ℝ := L - θ with hc_def
  have hcpos : 0 < c := by rw [hc_def]; linarith
  set A : ℝ := ∫ x in Ioi (0:ℝ), squashDensity x with hA_def
  have hApos : 0 < A := squashDensity_integral_pos
  have hAne : A ≠ 0 := ne_of_gt hApos
  set rho : ℝ := A / c with hrho_def
  have hrho_pos : 0 < rho := by rw [hrho_def]; exact div_pos hApos hcpos
  set ψ : ℝ → ℝ := fun t => squashDensity (rho * t) with hψ_def
  have hψ_cont : ContDiff ℝ ((⊤:ℕ∞)) ψ := squashDensity_contDiff.comp (by fun_prop)
  have hψ_pos : ∀ t, 0 < ψ t := fun t => squashDensity_pos _
  have hψ_int : IntegrableOn ψ (Ioi 0) := by
    rw [hψ_def]
    rw [integrableOn_Ioi_comp_mul_left_iff squashDensity 0 hrho_pos]
    simpa using squashDensity_integrableOn
  have hψ_int_val : ∫ x in Ioi (0:ℝ), ψ x = c := by
    rw [hψ_def]
    have h2 : ∫ x in Ioi (0:ℝ), squashDensity (rho * x) =
        rho⁻¹ • ∫ x in Ioi (rho * 0), squashDensity x :=
      integral_comp_mul_left_Ioi squashDensity 0 hrho_pos
    rw [h2, mul_zero, smul_eq_mul]
    rw [← hA_def]
    rw [hrho_def, inv_div]
    exact div_mul_cancel₀ c hAne
  set G : ℝ → ℝ := fun u => ∫ t in 0..u, ψ t with hG_def
  set gg : ℝ → ℝ := fun s => θ + G (s - θ) with hgg_def
  have hG_deriv : deriv G = ψ := by
    funext u
    rw [hG_def]
    exact Continuous.deriv_integral ψ hψ_cont.continuous 0 u
  have hG_diff : Differentiable ℝ G := by
    intro u
    rw [hG_def]
    exact (hψ_cont.continuous.integral_hasStrictDerivAt 0 u).hasDerivAt.differentiableAt
  have hG_cont : ContDiff ℝ ((⊤:ℕ∞)) G := by
    rw [contDiff_infty_iff_deriv]
    exact ⟨hG_diff, by rw [hG_deriv]; exact hψ_cont⟩
  have hgg_cont : ContDiff ℝ ((⊤:ℕ∞)) gg := by
    rw [hgg_def]
    exact contDiff_const.add
      (hG_cont.comp (by fun_prop : ContDiff ℝ ((⊤:ℕ∞)) (fun s : ℝ => s - θ)))
  have hgg_deriv : ∀ s, deriv gg s = ψ (s - θ) := by
    intro s
    rw [hgg_def]
    have hinner : HasDerivAt (fun s : ℝ => s - θ) 1 s := by
      simpa using (hasDerivAt_id s).sub_const θ
    have hG_ha : HasDerivAt G (ψ (s - θ)) (s - θ) := by
      rw [hG_def]
      exact (hψ_cont.continuous.integral_hasStrictDerivAt 0 (s - θ)).hasDerivAt
    have houter : HasDerivAt (fun u : ℝ => θ + G u) (ψ (s - θ)) (s - θ) :=
      hG_ha.const_add θ
    have hd := (houter.comp s hinner).deriv
    simpa only [Function.comp_def, mul_one] using hd
  have hG_eq_self : ∀ u, u ≤ 0 → G u = u := by
    intro u hu
    rw [hG_def]
    change (∫ t in 0..u, ψ t) = u
    rw [intervalIntegral.integral_symm u 0]
    have hcongr : ∫ t in u..0, ψ t = ∫ t in u..0, (1:ℝ) := by
      apply intervalIntegral.integral_congr
      intro x hx
      have hx0 : x ≤ 0 := by rw [uIcc_of_le hu] at hx; exact hx.2
      change squashDensity (rho * x) = 1
      rw [squashDensity_eq_one_of_nonpos (mul_nonpos_of_nonneg_of_nonpos hrho_pos.le hx0)]
    rw [hcongr, intervalIntegral.integral_const]
    ring
  have hgg_eq_self : ∀ s, s ≤ θ → gg s = s := by
    intro s hs
    have hu : s - θ ≤ 0 := by linarith
    have h1 : gg s = θ + G (s - θ) := by rw [hgg_def]
    rw [h1, hG_eq_self (s - θ) hu]
    ring
  have hG_le_c : ∀ u : ℝ, G u ≤ c := by
    intro u
    rw [hG_def]
    change (∫ t in 0..u, ψ t) ≤ c
    by_cases hu : 0 ≤ u
    · have h := intervalIntegral.integral_Ioi_sub_Ioi hψ_int hu
      rw [hψ_int_val] at h
      rw [← h]
      have hnn : 0 ≤ ∫ x in Ioi u, ψ x :=
        setIntegral_nonneg measurableSet_Ioi (fun x _ => le_of_lt (hψ_pos x))
      linarith
    · have hu' : u < 0 := not_le.mp hu
      rw [intervalIntegral.integral_symm u 0]
      have hnn : 0 ≤ ∫ x in u..0, ψ x :=
        intervalIntegral.integral_nonneg hu'.le (fun x _ => le_of_lt (hψ_pos x))
      linarith
  have hgg_le_L : ∀ t, gg t ≤ L := by
    intro t
    have h1 : gg t = θ + G (t - θ) := by rw [hgg_def]
    have hL : θ + c = L := by rw [hc_def]; ring
    rw [h1, ← hL]
    linarith [hG_le_c (t - θ)]
  have hgg_strict : StrictMono gg :=
    strictMono_of_deriv_pos (fun s => by rw [hgg_deriv s]; exact hψ_pos _)
  have hgg_lt_L : ∀ s, gg s < L := by
    intro s
    exact lt_of_lt_of_le (hgg_strict (lt_add_one s)) (hgg_le_L (s + 1))
  have hgg_deriv_pos : ∀ s, 0 < deriv gg s := fun s => by
    rw [hgg_deriv s]; exact hψ_pos _
  have hG_tendsto : Filter.Tendsto G Filter.atTop (nhds c) := by
    rw [hG_def]
    have h := MeasureTheory.intervalIntegral_tendsto_integral_Ioi (f := ψ) (b := id)
      (l := Filter.atTop) 0 hψ_int Filter.tendsto_id
    rw [hψ_int_val] at h
    exact h
  have hgg_tendsto : Filter.Tendsto gg Filter.atTop (nhds L) := by
    have hL : θ + c = L := by rw [hc_def]; ring
    have h1 : Filter.Tendsto (fun u : ℝ => θ + G u) Filter.atTop (nhds (θ + c)) :=
      hG_tendsto.const_add θ
    have h2 : Filter.Tendsto (fun s : ℝ => s - θ) Filter.atTop Filter.atTop := by
      simpa [sub_eq_add_neg] using
        tendsto_atTop_add_const_right Filter.atTop (-θ) Filter.tendsto_id
    have h3 : Filter.Tendsto gg Filter.atTop (nhds (θ + c)) := by
      rw [hgg_def]; exact h1.comp h2
    rwa [hL] at h3
  exact ⟨gg, hgg_cont, hgg_strict, hgg_deriv_pos, hgg_eq_self, hgg_lt_L, hgg_tendsto⟩

end

end Work.Noncompact.CompressionTube
