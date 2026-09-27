import Mathlib
import Submission.Commons.Analysis.Complex.infDist_zero_compl_image_le_one
import Submission.Commons.Analysis.Complex.Analytic.deriv_ne_zero_of_injOn

open scoped Topology
open Metric Set

namespace Commons.Analysis.Complex.Koebe

/-- **Grönwall-type growth bound.**  If `H : ℝ → ℂ` is continuous on `[0,a]`, differentiable on
`[0,a)` with `H 0 = 0`, and `‖H' t‖ ≤ (‖H t‖ + 1) / (c (1 - t))` for `t ∈ [0,a)`, then
`‖H a‖ + 1 ≤ ((1 + a)/(1 - a)) ^ (1/c)`.

This is proved by the time change `s ↦ 1 - exp (-(c s))`, which turns the variable-coefficient
differential inequality into the constant-coefficient one `‖S'(s)‖ ≤ ‖S s‖ + 1`, to which the
standard Grönwall inequality applies. -/
theorem growth_of_deriv_bound {c : ℝ} (hc : 0 < c) {H H' : ℝ → ℂ} {a : ℝ}
    (ha0 : 0 ≤ a) (ha1 : a < 1) (hH0 : H 0 = 0)
    (hcont : ContinuousOn H (Set.Icc 0 a))
    (hderiv : ∀ t ∈ Set.Ico 0 a, HasDerivAt H (H' t) t)
    (hbound : ∀ t ∈ Set.Ico 0 a, ‖H' t‖ ≤ (‖H t‖ + 1) / (c * (1 - t))) :
    ‖H a‖ + 1 ≤ ((1 + a) / (1 - a)) ^ (1 / c) := by
  have h1a : 0 < 1 - a := by linarith
  set b : ℝ := -(1 / c) * Real.log (1 - a) with hbdef
  have hb0 : 0 ≤ b := by
    rw [hbdef]
    have hlog : Real.log (1 - a) ≤ 0 := Real.log_nonpos h1a.le (by linarith)
    have hpos : 0 ≤ 1 / c := by positivity
    nlinarith [mul_nonpos_of_nonneg_of_nonpos hpos hlog]
  have hexpb : Real.exp (-(c * b)) = 1 - a := by
    have hcb : c * b = -Real.log (1 - a) := by rw [hbdef]; field_simp
    rw [show -(c * b) = Real.log (1 - a) by rw [hcb]; ring, Real.exp_log h1a]
  set ψ : ℝ → ℝ := fun s => 1 - Real.exp (-(c * s)) with hψdef
  have hψ0 : ψ 0 = 0 := by simp [hψdef]
  have hψb : ψ b = a := by simp only [hψdef, hexpb]; ring
  have hψmem : ∀ s ∈ Set.Icc 0 b, ψ s ∈ Set.Icc 0 a := by
    intro s hs
    rw [mem_Icc] at hs ⊢
    refine ⟨?_, ?_⟩
    · rw [hψdef]
      have h : Real.exp (-(c * s)) ≤ 1 := by
        rw [Real.exp_le_one_iff]; nlinarith [hs.1, hc]
      linarith
    · have h : Real.exp (-(c * b)) ≤ Real.exp (-(c * s)) :=
        Real.exp_le_exp.mpr (by nlinarith [hs.2, hc])
      rw [hψdef]; linarith [h, hexpb]
  have hψcont : ContinuousOn ψ (Set.Icc 0 b) := by rw [hψdef]; fun_prop
  have hψderiv : ∀ s, HasDerivAt ψ (c * Real.exp (-(c * s))) s := by
    intro s
    have h1 : HasDerivAt (fun s : ℝ => -(c * s)) (-c) s := by
      simpa using (hasDerivAt_id s).const_mul (-c)
    have h2 : HasDerivAt (fun s : ℝ => Real.exp (-(c * s))) (Real.exp (-(c * s)) * (-c)) s := h1.exp
    have h3 : HasDerivAt (fun s : ℝ => 1 - Real.exp (-(c * s))) (0 - Real.exp (-(c * s)) * (-c)) s :=
      (hasDerivAt_const s (1 : ℝ)).sub h2
    have h4 : (0 - Real.exp (-(c * s)) * (-c)) = c * Real.exp (-(c * s)) := by ring
    rw [hψdef, ← h4]
    exact h3
  have hψmem' : ∀ s ∈ Set.Ico 0 b, ψ s ∈ Set.Ico 0 a := by
    intro s hs
    rw [mem_Ico] at hs ⊢
    refine ⟨(hψmem s ⟨hs.1, le_of_lt hs.2⟩).1, ?_⟩
    have h : Real.exp (-(c * b)) < Real.exp (-(c * s)) :=
      Real.exp_lt_exp.mpr (by nlinarith [hs.2, hc])
    rw [hψdef]; linarith [h, hexpb]
  have hScont : ContinuousOn (H ∘ ψ) (Set.Icc 0 b) :=
    hcont.comp hψcont (fun s hs => hψmem s hs)
  have hSderiv : ∀ s ∈ Set.Ico 0 b,
      HasDerivWithinAt (H ∘ ψ) ((c * Real.exp (-(c * s))) • H' (ψ s)) (Set.Ici s) s := by
    intro s hs
    exact (HasDerivAt.scomp s (hderiv (ψ s) (hψmem' s hs)) (hψderiv s)).hasDerivWithinAt
  have hSbound : ∀ s ∈ Set.Ico 0 b,
      ‖(c * Real.exp (-(c * s))) • H' (ψ s)‖ ≤ 1 * ‖(H ∘ ψ) s‖ + 1 := by
    intro s hs
    have hpsimem : ψ s ∈ Set.Ico 0 a := hψmem' s hs
    have hbnd := hbound (ψ s) hpsimem
    have hone : 1 - ψ s = Real.exp (-(c * s)) := by rw [hψdef]; ring
    have hcs : c * (1 - ψ s) = c * Real.exp (-(c * s)) := by rw [hone]
    rw [hcs] at hbnd
    have hpos : 0 < c * Real.exp (-(c * s)) := by positivity
    have hnorm : ‖(c * Real.exp (-(c * s))) • H' (ψ s)‖
        = (c * Real.exp (-(c * s))) * ‖H' (ψ s)‖ := by
      rw [norm_smul, Real.norm_of_nonneg (le_of_lt hpos)]
    rw [hnorm]
    calc (c * Real.exp (-(c * s))) * ‖H' (ψ s)‖
        ≤ (c * Real.exp (-(c * s))) * ((‖H (ψ s)‖ + 1) / (c * Real.exp (-(c * s)))) :=
          mul_le_mul_of_nonneg_left hbnd (le_of_lt hpos)
      _ = ‖H (ψ s)‖ + 1 := by field_simp
      _ = 1 * ‖(H ∘ ψ) s‖ + 1 := by simp [Function.comp, one_mul]
  have hS'a : ‖(H ∘ ψ) 0‖ ≤ (0 : ℝ) := by
    have : (H ∘ ψ) 0 = 0 := by simp [Function.comp, hψ0, hH0]
    rw [this]; norm_num
  have hgron := norm_le_gronwallBound_of_norm_deriv_right_le
    (f := H ∘ ψ) (f' := fun s => (c * Real.exp (-(c * s))) • H' (ψ s))
    (δ := 0) (K := 1) (ε := 1) (a := 0) (b := b) hScont hSderiv hS'a hSbound
  have hb_mem : b ∈ Set.Icc (0 : ℝ) b := ⟨hb0, le_refl b⟩
  have hfin := hgron b hb_mem
  have hgb : gronwallBound 0 1 1 (b - 0) = Real.exp b - 1 := by
    rw [gronwallBound_of_K_ne_0 (by norm_num : (1 : ℝ) ≠ 0), sub_zero]; ring_nf
  rw [hgb] at hfin
  have hSb : (H ∘ ψ) b = H a := by rw [Function.comp, hψb]
  rw [hSb] at hfin
  have hexpeq : Real.exp b = (1 - a) ^ (-(1 / c)) := by
    rw [hbdef, Real.rpow_def_of_pos h1a]; congr 1; ring
  rw [hexpeq] at hfin
  have hPa : (0 : ℝ) < 1 + a := by linarith
  have hX : (1 : ℝ) ≤ (1 + a) ^ (1 / c) := Real.one_le_rpow (by linarith) (by positivity)
  have hYnn : 0 ≤ (1 - a) ^ (-(1 / c)) := Real.rpow_nonneg h1a.le _
  have hdiv : ((1 + a) / (1 - a)) ^ (1 / c) = (1 + a) ^ (1 / c) * (1 - a) ^ (-(1 / c)) := by
    rw [Real.div_rpow hPa.le h1a.le, div_eq_mul_inv, ← Real.rpow_neg h1a.le]
  calc ‖H a‖ + 1 ≤ (1 - a) ^ (-(1 / c)) := by linarith [hfin]
    _ = 1 * (1 - a) ^ (-(1 / c)) := by ring
    _ ≤ (1 + a) ^ (1 / c) * (1 - a) ^ (-(1 / c)) := mul_le_mul_of_nonneg_right hX hYnn
    _ = ((1 + a) / (1 - a)) ^ (1 / c) := hdiv.symm


/-- The image of an injective analytic function on the unit disc is not all of `ℂ`.
Indeed, otherwise the set-theoretic inverse would be a bounded entire function (analytic by the
inverse function theorem, since the derivative does not vanish), contradicting Liouville. -/
theorem image_ne_univ_of_analytic_injOn {f : ℂ → ℂ}
    (hf : ∀ z ∈ Metric.ball (0 : ℂ) 1, AnalyticAt ℂ f z)
    (hinj : Set.InjOn f (Metric.ball (0 : ℂ) 1)) :
    f '' (Metric.ball (0 : ℂ) 1) ≠ Set.univ := by
  classical
  intro hS
  let g : ℂ → ℂ := fun w =>
    if h : ∃ z ∈ Metric.ball (0 : ℂ) 1, f z = w then h.choose else 0
  have hg_spec : ∀ w, g w ∈ Metric.ball (0 : ℂ) 1 ∧ f (g w) = w := by
    intro w
    have hex : ∃ z ∈ Metric.ball (0 : ℂ) 1, f z = w := by
      have : w ∈ f '' Metric.ball (0 : ℂ) 1 := by rw [hS]; exact Set.mem_univ w
      simpa [Set.mem_image] using this
    have hgw : g w = Classical.choose hex := by simp only [g]; rw [dif_pos hex]
    rw [hgw]; exact Classical.choose_spec hex
  have hgd : Differentiable ℂ g := by
    intro w0
    obtain ⟨hgwball, hgwval⟩ := hg_spec w0
    set z0 : ℂ := g w0 with hz0def
    have hz0mem : z0 ∈ Metric.ball (0 : ℂ) 1 := hgwball
    have hfz0 : AnalyticAt ℂ f z0 := hf z0 hz0mem
    have hz0norm : ‖z0‖ < 1 := by
      rw [Metric.mem_ball, dist_eq_norm, sub_zero] at hz0mem; exact hz0mem
    have hr : 0 < 1 - ‖z0‖ := by linarith
    have hsub : Metric.ball z0 (1 - ‖z0‖) ⊆ Metric.ball (0 : ℂ) 1 := by
      intro a ha
      rw [Metric.mem_ball] at ha ⊢
      have h0z0 : dist z0 (0 : ℂ) = ‖z0‖ := by rw [dist_eq_norm, sub_zero]
      linarith [dist_triangle a z0 (0 : ℂ), h0z0]
    have hdne : deriv f z0 ≠ 0 :=
      Commons.Analysis.Complex.Analytic.deriv_ne_zero_of_injOn hr hfz0
        (fun a ha b hb hab => hinj (hsub ha) (hsub hb) hab)
    have hev : (g ∘ f) =ᶠ[𝓝 z0] id := by
      filter_upwards [Metric.isOpen_ball.mem_nhds hz0mem] with z hz
      simp only [Function.comp_apply, id]
      obtain ⟨hgzball, hgzval⟩ := hg_spec (f z)
      exact hinj hgzball hz hgzval
    have hAnal : AnalyticAt ℂ (g ∘ f) z0 := analyticAt_id.congr hev.symm
    have hAnalg : AnalyticAt ℂ g (f z0) :=
      (analyticAt_comp_iff_of_deriv_ne_zero hfz0 hdne).mp hAnal
    rw [← hgwval]
    exact hAnalg.differentiableAt
  have hgbdd : Bornology.IsBounded (Set.range g) := by
    have hb : Bornology.IsBounded (Metric.closedBall (0 : ℂ) 1) := Metric.isBounded_closedBall
    refine hb.subset ?_
    rintro y ⟨w, rfl⟩
    rw [Metric.mem_closedBall, dist_eq_norm, sub_zero]
    have := (hg_spec w).1
    rw [Metric.mem_ball, dist_eq_norm, sub_zero] at this
    linarith
  obtain ⟨c0, hc0⟩ := hgd.exists_const_forall_eq_of_bounded hgbdd
  have h0 : f c0 = (0 : ℂ) := by
    have := (hg_spec 0).2
    rwa [hc0 0] at this
  have h1' : f c0 = (1 : ℂ) := by
    have := (hg_spec 1).2
    rwa [hc0 1] at this
  exact zero_ne_one (h0.symm.trans h1')

/-- **Growth estimate from the Koebe (one-quarter) property.**
If every normalised univalent function on the unit disc has an image containing the disc of
radius `c`, then every normalised univalent `f` grows at most like `((1+|z|)/(1-|z|))^{1/c}`. -/
theorem growth_bound {c : ℝ} (hc : 0 < c)
    (hkoebe : ∀ f : ℂ → ℂ, (∀ z ∈ Metric.ball (0 : ℂ) 1, AnalyticAt ℂ f z) →
      Set.InjOn f (Metric.ball (0 : ℂ) 1) → f 0 = 0 → deriv f 0 = 1 →
      ∀ w : ℂ, w ∉ f '' (Metric.ball (0 : ℂ) 1) → c ≤ ‖w‖)
    {f : ℂ → ℂ} (hf : ∀ z ∈ Metric.ball (0 : ℂ) 1, AnalyticAt ℂ f z)
    (hinj : Set.InjOn f (Metric.ball (0 : ℂ) 1)) (h0 : f 0 = 0) (h1 : deriv f 0 = 1) :
    ∀ z ∈ Metric.ball (0 : ℂ) 1, ‖f z‖ + 1 ≤ ((1 + ‖z‖) / (1 - ‖z‖)) ^ (1 / c) := by
  -- the image is not all of `ℂ`
  have hcompl_ne : ((f '' Metric.ball (0 : ℂ) 1)ᶜ).Nonempty := by
    rw [Set.nonempty_compl]
    exact image_ne_univ_of_analytic_injOn hf hinj
  -- local Koebe-transform derivative bound
  have hderiv_bound : ∀ w ∈ Metric.ball (0 : ℂ) 1,
      (1 - ‖w‖) * ‖deriv f w‖ ≤ (‖f w‖ + 1) / c := by
    intro w hw
    by_cases hdw : deriv f w = 0
    · rw [hdw, norm_zero, mul_zero]; positivity
    · set ρ : ℝ := ‖w‖ with hρdef
      have hρlt : ρ < 1 := by rw [hρdef]; simpa [Metric.mem_ball, dist_eq_norm] using hw
      set s : ℝ := 1 - ρ with hsdef
      have hs_pos : 0 < s := by rw [hsdef]; linarith
      have hsC : (s : ℂ) ≠ 0 := by exact_mod_cast hs_pos.ne'
      set z0 : ℂ := (s : ℂ) * deriv f w with hz0def
      have hz0ne : z0 ≠ 0 := by rw [hz0def]; exact mul_ne_zero hsC hdw
      set G : ℂ → ℂ := fun ζ => (f (w + (s : ℂ) * ζ) - f w) * z0⁻¹ with hGdef
      have harg_mem : ∀ ζ : ℂ, ‖ζ‖ < 1 → w + (s : ℂ) * ζ ∈ Metric.ball (0 : ℂ) 1 := by
        intro ζ hζn
        rw [Metric.mem_ball, dist_eq_norm, sub_zero]
        calc ‖w + (s : ℂ) * ζ‖ ≤ ‖w‖ + ‖(s : ℂ) * ζ‖ := norm_add_le _ _
          _ = ρ + s * ‖ζ‖ := by rw [norm_mul, Complex.norm_of_nonneg hs_pos.le, hρdef]
          _ < ρ + s := by nlinarith [hζn, hs_pos]
          _ = 1 := by rw [hsdef]; ring
      have hG_analytic : ∀ ζ ∈ Metric.ball (0 : ℂ) 1, AnalyticAt ℂ G ζ := by
        intro ζ hζ
        have hζn : ‖ζ‖ < 1 := by simpa [Metric.mem_ball, dist_eq_norm] using hζ
        have hfw : AnalyticAt ℂ f (w + (s : ℂ) * ζ) := hf _ (harg_mem ζ hζn)
        rw [hGdef]
        fun_prop
      have hG0 : G 0 = 0 := by rw [hGdef]; simp
      have hG1 : deriv G 0 = 1 := by
        have haff : HasDerivAt (fun ζ : ℂ => w + (s : ℂ) * ζ) (s : ℂ) 0 := by
          simpa using ((hasDerivAt_id (0 : ℂ)).const_mul (s : ℂ)).const_add w
        have hfd : HasDerivAt f (deriv f w) (w + (s : ℂ) * (0 : ℂ)) := by
          simpa using (hf w hw).hasStrictDerivAt.hasDerivAt
        have h1' := HasDerivAt.scomp (0 : ℂ) hfd haff
        have h2' := h1'.sub_const (f w)
        rw [smul_eq_mul] at h2'
        have h3' := h2'.mul_const (z0⁻¹)
        rw [mul_inv_cancel₀ hz0ne] at h3'
        rw [hGdef]
        simpa [Function.comp_def] using h3'.deriv
      have hG_inj : Set.InjOn G (Metric.ball (0 : ℂ) 1) := by
        intro ζ1 hζ1 ζ2 hζ2 heq
        have hζ1n : ‖ζ1‖ < 1 := by simpa [Metric.mem_ball, dist_eq_norm] using hζ1
        have hζ2n : ‖ζ2‖ < 1 := by simpa [Metric.mem_ball, dist_eq_norm] using hζ2
        have hvaleq : f (w + (s : ℂ) * ζ1) = f (w + (s : ℂ) * ζ2) := by
          have h := heq
          rw [hGdef] at h
          have h' := mul_right_cancel₀ (inv_ne_zero hz0ne) h
          linear_combination h'
        have hz := hinj (harg_mem ζ1 hζ1n) (harg_mem ζ2 hζ2n) hvaleq
        have : (s : ℂ) * ζ1 = (s : ℂ) * ζ2 := by
          simpa using (add_left_cancel hz)
        exact mul_left_cancel₀ hsC this
      have hkey : ∀ v : ℂ, v ∉ f '' Metric.ball (0 : ℂ) 1 → c * s * ‖deriv f w‖ ≤ ‖v - f w‖ := by
        intro v hv
        set u : ℂ := (v - f w) * z0⁻¹ with hudef
        have hu : u ∉ G '' Metric.ball (0 : ℂ) 1 := by
          rintro ⟨ζ, hζ, hζeq⟩
          have hζn : ‖ζ‖ < 1 := by simpa [Metric.mem_ball, dist_eq_norm] using hζ
          have hval : f (w + (s : ℂ) * ζ) = v := by
            have h := hζeq
            rw [hGdef, hudef] at h
            have h' := mul_right_cancel₀ (inv_ne_zero hz0ne) h
            linear_combination h'
          exact hv ⟨w + (s : ℂ) * ζ, harg_mem ζ hζn, hval⟩
        have hcu := hkoebe G hG_analytic hG_inj hG0 hG1 u hu
        have hnormu : ‖u‖ = ‖v - f w‖ / (s * ‖deriv f w‖) := by
          rw [hudef, norm_mul, norm_inv, hz0def, norm_mul,
            Complex.norm_of_nonneg hs_pos.le, div_eq_mul_inv]
        rw [hnormu] at hcu
        rw [le_div_iff₀ (by positivity : 0 < s * ‖deriv f w‖)] at hcu
        nlinarith [hcu]
      have hlow : c * s * ‖deriv f w‖ ≤ Metric.infDist (f w) ((f '' Metric.ball (0 : ℂ) 1)ᶜ) := by
        rw [Metric.le_infDist (x := f w) hcompl_ne]
        intro v hv
        simpa [dist_eq_norm, norm_sub_rev] using hkey v hv
      have hup : Metric.infDist (f w) ((f '' Metric.ball (0 : ℂ) 1)ᶜ) ≤ 1 + ‖f w‖ := by
        have h := Metric.infDist_le_infDist_add_dist (x := f w) (y := (0 : ℂ))
          (s := (f '' Metric.ball (0 : ℂ) 1)ᶜ)
        have hR := Commons.Analysis.Complex.infDist_zero_compl_image_le_one hf hinj h0 h1
        have hd : dist (f w) (0 : ℂ) = ‖f w‖ := by rw [dist_eq_norm, sub_zero]
        linarith [h, hR, hd]
      have hfin : c * s * ‖deriv f w‖ ≤ 1 + ‖f w‖ := le_trans hlow hup
      have hseq : s = 1 - ‖w‖ := by rw [hsdef, hρdef]
      rw [le_div_iff₀ hc]
      nlinarith [hfin, hseq]
  -- growth along a ray
  intro z hz
  have hzn : ‖z‖ < 1 := by simpa [Metric.mem_ball, dist_eq_norm] using hz
  rcases eq_or_ne z 0 with rfl | hzne
  · simp [h0]
  · have hzpos : 0 < ‖z‖ := norm_pos_iff.mpr hzne
    set u : ℂ := ((‖z‖⁻¹ : ℝ) : ℂ) * z with hudef
    have hun : ‖u‖ = 1 := by
      rw [hudef, norm_mul, Complex.norm_of_nonneg (inv_nonneg.mpr (norm_nonneg z)),
        inv_mul_cancel₀ (ne_of_gt hzpos)]
    set H : ℝ → ℂ := fun t => f ((t : ℂ) * u) with hHdef
    set H' : ℝ → ℂ := fun t => u * deriv f ((t : ℂ) * u) with hH'def
    have hHpt_mem : ∀ t : ℝ, 0 ≤ t → t < 1 → (t : ℂ) * u ∈ Metric.ball (0 : ℂ) 1 := by
      intro t ht0 htlt
      have hpt_norm : ‖(t : ℂ) * u‖ = t := by
        rw [norm_mul, Complex.norm_of_nonneg ht0, hun, mul_one]
      rw [Metric.mem_ball, dist_eq_norm, sub_zero, hpt_norm]; exact htlt
    have hH0 : H 0 = 0 := by rw [hHdef]; simp [h0]
    have hHcont : ContinuousOn H (Set.Icc 0 ‖z‖) := by
      rw [hHdef]
      refine ContinuousOn.comp (fun x hx => (hf x hx).continuousAt.continuousWithinAt)
        (by fun_prop) ?_
      intro t ht
      rw [Set.mem_Icc] at ht
      exact hHpt_mem t ht.1 (lt_of_le_of_lt ht.2 hzn)
    have hHderiv : ∀ t ∈ Set.Ico 0 ‖z‖, HasDerivAt H (H' t) t := by
      intro t ht
      rw [Set.mem_Ico] at ht
      have hpt_mem := hHpt_mem t ht.1 (lt_trans ht.2 hzn)
      have hfd : HasDerivAt f (deriv f ((t : ℂ) * u)) ((t : ℂ) * u) :=
        (hf _ hpt_mem).hasStrictDerivAt.hasDerivAt
      have hphi : HasDerivAt (fun t : ℝ => (t : ℂ) * u) u t := by
        have h1' : HasDerivAt (fun y : ℝ => (y : ℂ)) (1 : ℂ) t := (hasDerivAt_id (t : ℂ)).comp_ofReal
        simpa using h1'.mul_const u
      have := HasDerivAt.scomp t hfd hphi
      rw [hHdef, hH'def]
      simpa [Function.comp_def] using this
    have hHbound : ∀ t ∈ Set.Ico 0 ‖z‖, ‖H' t‖ ≤ (‖H t‖ + 1) / (c * (1 - t)) := by
      intro t ht
      rw [Set.mem_Ico] at ht
      have h1t : 0 < 1 - t := by linarith [ht.2, hzn]
      have hpt_norm : ‖(t : ℂ) * u‖ = t := by
        rw [norm_mul, Complex.norm_of_nonneg ht.1, hun, mul_one]
      have hpt_mem := hHpt_mem t ht.1 (lt_trans ht.2 hzn)
      have hb := hderiv_bound ((t : ℂ) * u) hpt_mem
      rw [hpt_norm] at hb
      have hH'n : ‖H' t‖ = ‖deriv f ((t : ℂ) * u)‖ := by rw [hH'def, norm_mul, hun, one_mul]
      have hb' := (le_div_iff₀ hc).mp hb
      rw [hH'n, hHdef]
      rw [le_div_iff₀ (by positivity : 0 < c * (1 - t))]
      nlinarith [hb', h1t, hc]
    have hmain := growth_of_deriv_bound hc (le_of_lt hzpos) hzn hH0 hHcont hHderiv hHbound
    have hHz : H ‖z‖ = f z := by
      rw [hHdef, hudef]
      have hcz : (‖z‖ : ℂ) * ((‖z‖⁻¹ : ℝ) : ℂ) = 1 := by
        rw [← Complex.ofReal_mul, mul_inv_cancel₀ (ne_of_gt hzpos), Complex.ofReal_one]
      calc f ((‖z‖ : ℂ) * (((‖z‖⁻¹ : ℝ) : ℂ) * z))
          = f (((‖z‖ : ℂ) * ((‖z‖⁻¹ : ℝ) : ℂ)) * z) := by rw [mul_assoc]
        _ = f z := by rw [hcz, one_mul]
    rwa [hHz] at hmain

end Commons.Analysis.Complex.Koebe
