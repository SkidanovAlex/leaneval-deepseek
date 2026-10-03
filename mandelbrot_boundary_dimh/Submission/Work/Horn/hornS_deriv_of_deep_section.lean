import Mathlib
import Submission.Work.Horn.horn_chart
import Submission.Work.Horn.hornS_germ
import Submission.Work.Horn.circleIntegral_logDeriv_hornS
import Submission.Work.Horn.no_extension_of_logDeriv_period

/-!
# The derivative at `0` of the descended horn section

If `s` is a holomorphic, `T`-equivariant section of `E` over a `T`-invariant strip-like domain `D`
(`{Im < -η} ⊆ D ⊆ {Im ≤ η}`) and `E w - w → cl` at the lower end, then the descended section
`Ŝ = hornS s` extends analytically to `u = 0` with `Ŝ 0 = 0` and `Ŝ'(0) = π cl`.

The mathematical content is that the section `s` is asymptotic to `w - cl` at the lower end.
If not, there are points `w n ∈ D` with `Im w n → -∞`, `‖s (w n) - (w n - cl)‖ ≥ ε` and
`Im (s (w n)) ≥ R` (otherwise the asymptotic of `E` applies at `s (w n) = E⁻¹ (w n)`).  Setting
`u n = exp (-2πi w n) → 0` this forces `‖Ŝ (u n)‖ = exp (2π Im (s (w n))) ≥ exp (2πR) > 0`, so the
(removable-singularity) extension `G` of `Ŝ = hornS s` at `0` satisfies `G 0 ≠ 0`.  But `Ŝ` has no
analytic extension with a nonzero value at `0`: its logarithmic derivative has circle integral
`2πi` on every small circle, while any zero-free analytic function has log derivative integral `0`.
-/

namespace Work.Horn

noncomputable section
open MandelDim Filter Topology Metric Set
open scoped Topology

/-- The value of the descended section at `u ≠ 0`, in terms of the standard lift. -/
theorem hornS_eq_lift (s : ℂ → ℂ) {u : ℂ} (hu : u ≠ 0) :
    hornS s u = MandelDim.piExp (-(s (hornS_lift u))) := by
  rw [hornS_lift, hornS_of_ne s hu]

/-- Norm of the descended section at `u ≠ 0`. -/
theorem norm_hornS (s : ℂ → ℂ) {u : ℂ} (hu : u ≠ 0) :
    ‖hornS s u‖ = Real.exp (2 * Real.pi * (s (hornS_lift u)).im) := by
  rw [hornS_eq_lift s hu, norm_piExp]
  congr 1
  rw [Complex.neg_im]
  ring

/-- The core of the argument, taking the analytic fact that `hornS s` has no analytic extension to
`0` with a nonzero value as a hypothesis (it is proved separately, via the circle integral of the
logarithmic derivative). -/
theorem hornS_deriv_of_deep_section_aux {E s : ℂ → ℂ} {D : Set ℂ} {cl : ℂ} {η : ℝ}
    (hnoext : ∀ G : ℂ → ℂ, AnalyticAt ℂ G 0 →
      (∀ᶠ u : ℂ in nhdsWithin (0 : ℂ) ({(0 : ℂ)}ᶜ), G u = hornS s u) → G 0 = 0)
    (hDo : IsOpen D) (hT : MandelDim.IsTInvariant D) (hs : DifferentiableOn ℂ s D)
    (heq : ∀ w ∈ D, s (w + 1) = s w + 1)
    (hsm : ∀ w ∈ D, s w ∈ D)
    (hEs : ∀ w ∈ D, E (s w) = w)
    (hlo : {w : ℂ | w.im < -η} ⊆ D) (hhi : ∀ w ∈ D, w.im ≤ η)
    (hasym : ∀ ε > 0, ∃ R : ℝ, ∀ w : ℂ, w.im < R → ‖E w - w - cl‖ < ε) :
    AnalyticAt ℂ (hornS s) 0 ∧ hornS s 0 = 0 ∧
      deriv (hornS s) 0 = MandelDim.piExp cl := by
  have h2pi : (0 : ℝ) < 2 * Real.pi := by positivity
  -- ## Step 1: the section is asymptotic to `w - cl` at the lower end
  have hasymp : ∀ ε > 0, ∃ R : ℝ, ∀ w ∈ D, w.im < R → ‖s w - (w - cl)‖ < ε := by
    intro ε hε
    obtain ⟨R₀, hR₀⟩ := hasym ε hε
    by_contra hcon
    push_neg at hcon
    -- bad points arbitrarily deep
    choose w hwD hwim hwbad using fun n : ℕ => hcon (-((n : ℝ) + η + 1))
    have hdeep : ∀ n : ℕ, (w n).im < -η := by
      intro n
      have h := hwim n
      have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
      linarith
    -- consequently `s (w n)` stays in the strip `{R₀ ≤ Im ≤ η}`
    have hsd : ∀ n : ℕ, R₀ ≤ (s (w n)).im := by
      intro n
      by_contra hlt
      rw [not_le] at hlt
      have h1 : ‖E (s (w n)) - s (w n) - cl‖ < ε := hR₀ (s (w n)) hlt
      rw [hEs (w n) (hwD n)] at h1
      have h2 : ‖w n - s (w n) - cl‖ = ‖s (w n) - (w n - cl)‖ := by
        rw [← norm_neg]
        congr 1
        ring
      rw [h2] at h1
      linarith [h1, hwbad n]
    -- the pulled-back sequence in the `u`-chart
    set u : ℕ → ℂ := fun n => Complex.exp (-(2 * Real.pi * Complex.I) * w n) with hu_def
    have hu_ne : ∀ n, u n ≠ 0 := fun n => Complex.exp_ne_zero _
    have hu_inv : ∀ n, u n = 1 / MandelDim.piExp (w n) := by
      intro n
      have h : u n = (MandelDim.piExp (w n))⁻¹ := by
        rw [hu_def, MandelDim.piExp, ← Complex.exp_neg]
        ring_nf
      simpa [one_div] using h
    have hu_norm : ∀ n, ‖u n‖ = Real.exp (2 * Real.pi * (w n).im) := by
      intro n
      rw [hu_inv n, norm_div, norm_one, norm_piExp, one_div, ← Real.exp_neg]
      congr 1
      ring
    -- `Ŝ` is bounded away from `0` along this sequence
    have hseq : ∀ n, Real.exp (2 * Real.pi * R₀) ≤ ‖hornS s (u n)‖ := by
      intro n
      have hlift : ∃ k : ℤ, hornS_lift (u n) = w n + k := by
        have h1 : MandelDim.piExp (hornS_lift (u n)) = MandelDim.piExp (w n) := by
          rw [piExp_hornS_lift (hu_ne n), hu_inv n]
          simp only [one_div, inv_inv]
        exact MandelDim.piExp_eq_iff.mp h1
      obtain ⟨k, hk⟩ := hlift
      have hsmem : s (hornS_lift (u n)) = s (w n) + k := by
        rw [hk]
        exact section_add_int hT heq (hwD n) k
      have him : R₀ ≤ (s (hornS_lift (u n))).im := by
        rw [hsmem]
        simpa using hsd n
      rw [norm_hornS s (hu_ne n), Real.exp_le_exp]
      exact mul_le_mul_of_nonneg_left him h2pi.le
    -- ## Step 2: `hornS s` extends analytically to `0` (removable singularity)
    set ρ : ℝ := Real.exp (-(2 * Real.pi) * η) with hρdef
    have hρpos : 0 < ρ := Real.exp_pos _
    have hdiff : DifferentiableOn ℂ (hornS s) (Metric.ball 0 ρ \ {(0 : ℂ)}) := by
      intro z hz
      have hz' : z ∈ Metric.ball 0 ρ := hz.1
      rw [Metric.mem_ball, dist_eq_norm, sub_zero] at hz'
      exact (hornS_differentiableAt hDo hT heq hs (mem_hornDl'_of_norm_lt hlo hz')
        (by simpa using hz.2)).differentiableWithinAt
    have hbdd : BddAbove (norm ∘ (hornS s) '' (Metric.ball 0 ρ \ {(0 : ℂ)})) := by
      refine ⟨Real.exp (2 * Real.pi * η), ?_⟩
      rintro y ⟨z, hz, rfl⟩
      simp only [Function.comp_apply]
      have hz0 : z ≠ 0 := by simpa using hz.2
      have hz' : z ∈ Metric.ball 0 ρ := hz.1
      rw [Metric.mem_ball, dist_eq_norm, sub_zero] at hz'
      have hzn : ‖z‖ < ρ := hz'
      have hlog : Real.log ‖z‖ < -(2 * Real.pi) * η := by
        have hpos : (0 : ℝ) < ‖z‖ := norm_pos_iff.mpr hz0
        have h := Real.log_lt_log hpos (by rwa [hρdef] at hzn)
        rwa [Real.log_exp] at h
      have hmem : hornS_lift z ∈ D := by
        apply hlo
        have him : (hornS_lift z).im = Real.log ‖z‖ / (2 * Real.pi) := by
          simp [hornS_lift, log_div_im]
        show (hornS_lift z).im < -η
        rw [him]
        have hlt : Real.log ‖z‖ / (2 * Real.pi) < (-(2 * Real.pi) * η) / (2 * Real.pi) :=
          div_lt_div_of_pos_right hlog h2pi
        rwa [neg_mul, neg_div, mul_div_cancel_left₀ η (ne_of_gt h2pi)] at hlt
      have him := hhi (s (hornS_lift z)) (hsm _ hmem)
      rw [norm_hornS s hz0, Real.exp_le_exp]
      exact mul_le_mul_of_nonneg_left him h2pi.le
    set G : ℂ → ℂ := Function.update (hornS s) 0
      ((nhdsWithin (0 : ℂ) ({(0 : ℂ)}ᶜ)).limUnder (hornS s)) with hGdef
    have hGdiff : DifferentiableOn ℂ G (Metric.ball 0 ρ) := by
      rw [hGdef]
      exact Complex.differentiableOn_update_limUnder_of_bddAbove (Metric.ball_mem_nhds 0 hρpos)
        hdiff hbdd
    have hGan : AnalyticAt ℂ G 0 := hGdiff.analyticAt (Metric.ball_mem_nhds 0 hρpos)
    have hGeq : ∀ᶠ u : ℂ in nhdsWithin (0 : ℂ) ({(0 : ℂ)}ᶜ), G u = hornS s u := by
      filter_upwards [self_mem_nhdsWithin] with z hz
      rw [hGdef]
      exact Function.update_of_ne (by simpa using hz) _ _
    have hGcont : Tendsto (hornS s) (nhdsWithin (0 : ℂ) ({(0 : ℂ)}ᶜ)) (𝓝 (G 0)) := by
      have h1 : Tendsto G (nhdsWithin (0 : ℂ) ({(0 : ℂ)}ᶜ)) (𝓝 (G 0)) :=
        ((hGdiff.differentiableAt (Metric.ball_mem_nhds 0 hρpos)).continuousAt.tendsto).mono_left
          nhdsWithin_le_nhds
      exact h1.congr' hGeq
    -- the extension is nonzero at `0`
    have hG0ne : G 0 ≠ 0 := by
      intro hzero
      have hc : (0 : ℝ) < Real.exp (2 * Real.pi * R₀) := Real.exp_pos _
      have hev : ∀ᶠ z : ℂ in nhdsWithin (0 : ℂ) ({(0 : ℂ)}ᶜ),
          ‖hornS s z - G 0‖ < Real.exp (2 * Real.pi * R₀) / 2 := by
        have h0 := (Metric.tendsto_nhds.mp hGcont) (Real.exp (2 * Real.pi * R₀) / 2) (by positivity)
        filter_upwards [h0] with z hz
        rwa [dist_eq_norm] at hz
      obtain ⟨δ, hδpos, hδsub⟩ := Metric.mem_nhdsWithin_iff.mp hev
      -- find a sequence point close to `0`
      have hex : ∃ n : ℕ, ‖u n‖ < δ := by
        have ht : ∀ᶠ n : ℕ in atTop, ‖u n‖ < δ := by
          filter_upwards [eventually_ge_atTop (Nat.ceil (-Real.log δ / (2 * Real.pi) - η))]
            with n hn
          calc ‖u n‖ = Real.exp (2 * Real.pi * (w n).im) := hu_norm n
            _ ≤ Real.exp (2 * Real.pi * (-((n : ℝ) + η + 1))) := by
                rw [Real.exp_le_exp]
                nlinarith [hwim n, h2pi]
            _ < δ := by
                refine (Real.lt_log_iff_exp_lt hδpos).mp ?_
                have hn2 : -Real.log δ / (2 * Real.pi) - η ≤ (n : ℝ) :=
                  le_trans (Nat.le_ceil _) (by exact_mod_cast hn)
                have hn3 : -Real.log δ / (2 * Real.pi) ≤ (n : ℝ) + η := by linarith [hn2]
                have hn4 : -Real.log δ ≤ 2 * Real.pi * ((n : ℝ) + η) := by
                  have h := (div_le_iff₀ h2pi).mp hn3
                  linarith [h]
                linarith [hn4, h2pi]
        exact ht.exists
      obtain ⟨n, hn⟩ := hex
      have hlt := hδsub ⟨by rw [Metric.mem_ball, dist_eq_norm, sub_zero]; exact hn,
        by simpa using hu_ne n⟩
      have hlt2 : ‖hornS s (u n)‖ < Real.exp (2 * Real.pi * R₀) / 2 := by
        simpa [hzero] using hlt
      linarith [hseq n, hlt2]
    exact absurd (hnoext G hGan hGeq) hG0ne
  -- ## Step 3: the germ, so `Ŝ` is analytic at `0`
  have hgerm : Tendsto (fun u : ℂ => hornS s u / u)
      (nhdsWithin (0 : ℂ) ({(0 : ℂ)}ᶜ)) (𝓝 (MandelDim.piExp cl)) :=
    hornS_germ hlo hasymp
  refine ⟨hornS_analyticAt_zero hDo hT heq hs hlo hgerm, hornS_zero s, ?_⟩
  -- ## Step 4: the derivative
  have hslope : Tendsto (slope (hornS s) 0) (nhdsWithin (0 : ℂ) ({(0 : ℂ)}ᶜ))
      (𝓝 (MandelDim.piExp cl)) := by
    refine hgerm.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with z hz
    rw [slope_def_field, hornS_zero]
    simp
  exact (hasDerivAt_iff_tendsto_slope.mpr hslope).deriv

/-- **`Ŝ'(0) = π cl` for a section of the horn map at the lower end.**

If `s` is holomorphic and `T`-equivariant on an open `T`-invariant `D` containing the lower
half-plane `{Im < -η}` and contained in `{Im ≤ η}`, if `E ∘ s = id` on `D` and `E w - w → cl` as
`Im w → -∞`, then the descended section `Ŝ = hornS s` is analytic at `0` with `Ŝ 0 = 0` and
`Ŝ'(0) = π cl`. -/
theorem hornS_deriv_of_deep_section {E s : ℂ → ℂ} {D : Set ℂ} {cl : ℂ} {η : ℝ}
    (hDo : IsOpen D) (hT : MandelDim.IsTInvariant D) (hs : DifferentiableOn ℂ s D)
    (heq : ∀ w ∈ D, s (w + 1) = s w + 1)
    (hsm : ∀ w ∈ D, s w ∈ D)
    (hEs : ∀ w ∈ D, E (s w) = w)
    (hlo : {w : ℂ | w.im < -η} ⊆ D) (hhi : ∀ w ∈ D, w.im ≤ η)
    (hasym : ∀ ε > 0, ∃ R : ℝ, ∀ w : ℂ, w.im < R → ‖E w - w - cl‖ < ε) :
    AnalyticAt ℂ (Work.Horn.hornS s) 0 ∧ Work.Horn.hornS s 0 = 0 ∧
      deriv (Work.Horn.hornS s) 0 = MandelDim.piExp cl := by
  have hnoext : ∀ G : ℂ → ℂ, AnalyticAt ℂ G 0 →
      (∀ᶠ u : ℂ in nhdsWithin (0 : ℂ) ({(0 : ℂ)}ᶜ), G u = hornS s u) → G 0 = 0 := by
    intro G hGan hGeq
    refine no_extension_of_logDeriv_period (V := hornS s) (ρ := Real.exp (-(2 * Real.pi) * η))
      (Real.exp_pos _) ?_ ?_ G hGan hGeq
    · intro u hu0 hu
      exact hornS_differentiableAt hDo hT heq hs (mem_hornDl'_of_norm_lt hlo hu)
        (norm_ne_zero_iff.mp (ne_of_gt hu0))
    · intro r hr0 hr
      exact circleIntegral_logDeriv_hornS hDo hT hs heq hlo r hr0 hr
  exact hornS_deriv_of_deep_section_aux hnoext hDo hT hs heq hsm hEs hlo hhi hasym

end

end Work.Horn
