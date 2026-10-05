import Mathlib
import Submission.Work.RPB.B5.noL_defs
import Submission.Work.RPB.B5.signedArea_scale_shift
import Submission.Work.RPB.B5.noL_fsh_geom

open scoped ContDiff

namespace Work.RPB.B5

/-!
# The far flux integrand of the collar `Γc`

On the far region `σ ≥ 2δ` the collar `GAM` is the rescaled curve family
`(rd σ) · CI.c 0 (t + phc δ k σ)`; here we compute the flux integrand
`ω_ℂ (∂_σ Γ, ∂_t Γ)` there and show that it is identically `1`.

The chain of facts is

* on the region `σ > δ` the collar is exactly the far shape
  `fsh CI δ k τ σ t = (rd σ) · CI.c (rpf δ σ · τ) (t + phc δ k σ)` (the blend cutoff
  `blf` is `1` there and the normalisation `lam` is `1` by `noL_fsh_geom`);
* for `σ ≥ 2δ` one has `rpf δ σ = 0` and `phc δ k σ = -π/2 - 2πk`, so the `σ`-derivative is
  `(deriv rd σ) · exp ((t + phc δ k σ) I)` and the `t`-derivative is
  `(rd σ) · (exp ((t + phc δ k σ) I) · I)`;
* `ω_ℂ (x · E) (y · (E · I)) = x y` whenever `‖E‖ = 1`, and `deriv rd σ · rd σ = 1`
  because `rd σ = √(2 + 2σ)`.

Hence the flux integrand is `1`, which is what makes `AcF` have derivative `1` in `t`.
-/

noncomputable section

/-! ## 1. The cutoffs at their thresholds -/

/-- `blf δ σ = 1` for `σ ≥ δ`. -/
lemma fluxAux_blf_eq_one {δ σ : ℝ} (hδ : 0 < δ) (h : δ ≤ σ) : blf δ σ = 1 := by
  unfold blf
  apply stp_one
  have h2 : 0 < δ / 2 := by linarith
  rw [le_div_iff₀ h2]
  linarith

/-- `rpf δ σ = 0` for `σ ≥ 2δ`. -/
lemma fluxAux_rpf_eq_zero {δ σ : ℝ} (hδ : 0 < δ) (h : 2 * δ ≤ σ) : rpf δ σ = 0 := by
  unfold rpf
  have h1 : stp ((σ - δ) / δ) = 1 := by
    apply stp_one
    rw [le_div_iff₀ hδ]
    linarith
  rw [h1]
  ring

/-- `phc δ k σ = -π/2 - 2πk` for `σ ≥ 2δ`. -/
lemma fluxAux_phc_eq {δ σ : ℝ} (hδ : 0 < δ) (k : ℤ) (h : 2 * δ ≤ σ) :
    phc δ k σ = -(Real.pi / 2) - 2 * Real.pi * k := by
  unfold phc
  have h1 : stp ((σ - δ) / δ) = 1 := by
    apply stp_one
    rw [le_div_iff₀ hδ]
    linarith
  rw [h1, mul_one]

/-! ## 2. The radius `rd` -/

/-- `rd σ = √(2 + 2σ)` is positive. -/
lemma fluxAux_rd_pos {σ : ℝ} (hσ : -1 < σ) : 0 < rd σ := by
  unfold rd
  apply Real.sqrt_pos.2
  linarith

/-- `HasDerivAt rd (1 / rd σ) σ`. -/
lemma fluxAux_hasDerivAt_rd {σ : ℝ} (hσ : -1 < σ) : HasDerivAt rd (1 / rd σ) σ := by
  have hne : (2 : ℝ) + 2 * σ ≠ 0 := by linarith
  have hρ : HasDerivAt (fun s : ℝ => 2 + 2 * s) (0 + 2 * 1) σ :=
    (hasDerivAt_const (𝕜 := ℝ) σ (2 : ℝ)).add ((hasDerivAt_id σ).const_mul (2 : ℝ))
  have h3 : HasDerivAt (fun s : ℝ => rd s) ((0 + 2 * 1) / (2 * Real.sqrt (2 + 2 * σ))) σ :=
    hρ.sqrt hne
  have hval : (0 + 2 * 1) / (2 * Real.sqrt (2 + 2 * σ)) = 1 / rd σ := by
    unfold rd
    have hs : Real.sqrt (2 + 2 * σ) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 (by linarith))
    field_simp
    ring
  exact h3.congr_deriv hval

/-- `deriv rd σ = 1 / rd σ`. -/
lemma fluxAux_deriv_rd {σ : ℝ} (hσ : -1 < σ) : deriv rd σ = 1 / rd σ :=
  (fluxAux_hasDerivAt_rd hσ).deriv

/-! ## 3. The far form of the collar on `σ > δ` -/

/-- On `δ < σ` the collar is the far shape: the blend cutoff is `1`, so the near shape drops out,
and the normalisation `lam` is `1` by `noL_fsh_geom`. -/
lemma fluxAux_GAM_eq_far (CI : Work.RPV.CurveIsotopy) (W : ℝ → ℝ → ℝ → Work.RPV.PS)
    (ρh : ℝ → ℝ → ℝ → ℝ) {δ : ℝ} (hδ : 0 < δ) (k : ℤ) {τ : ℝ}
    (hτ : τ ∈ Set.Icc (0 : ℝ) 1) {σ t : ℝ} (hσ : δ < σ) :
    GAM CI W ρh δ k τ σ t = (rd σ : ℂ) * CI.c (rpf δ σ * τ) (t + phc δ k σ) := by
  have hσ0 : (0 : ℝ) < σ := by linarith
  have hblf : blf δ σ = 1 := fluxAux_blf_eq_one hδ (le_of_lt hσ)
  have hsh0t : ∀ u : ℝ, sh0 CI W ρh δ k τ σ u = fsh CI δ k τ σ u := by
    intro u
    rw [sh0, hblf]
    simp only [Complex.ofReal_one, sub_self, zero_mul, one_mul, zero_add]
  have hsh0 : sh0 CI W ρh δ k τ σ = fsh CI δ k τ σ := funext hsh0t
  have hlam : lam CI W ρh δ k τ σ = 1 := by
    have harS : arS CI W ρh δ k τ σ = 2 * Real.pi * (1 + σ) := by
      rw [arS, hsh0]
      exact (noL_fsh_geom CI hδ k τ hτ σ (le_of_lt hσ0)).1
    rw [lam, harS]
    have hne : (2 : ℝ) * Real.pi * (1 + σ) ≠ 0 := by
      have h1 : (0 : ℝ) < 1 + σ := by linarith
      have h2 : (0 : ℝ) < 2 * Real.pi := by positivity
      exact ne_of_gt (mul_pos h2 h1)
    rw [div_self hne, Real.sqrt_one]
  rw [GAM, ite_eq_right (not_le.mpr hσ0), cpos, hlam]
  rw [hsh0t, fsh]
  simp only [Complex.ofReal_one, one_mul]

/-! ## 4. The two derivatives at the far end -/

/-- `HasDerivAt rpf 0 σ` for `σ ≥ 2δ`: `rpf` is constant (`0`) on `[2δ, ∞)`. -/
lemma fluxAux_hasDerivAt_rpf {δ σ : ℝ} (hδ : 0 < δ) (h : 2 * δ ≤ σ) :
    HasDerivAt (fun s : ℝ => rpf δ s) 0 σ := by
  have hd : DifferentiableAt ℝ (fun s : ℝ => rpf δ s) σ := by
    have hC : ContDiff ℝ ∞ (fun s : ℝ => rpf δ s) := by
      have hfun : (fun s : ℝ => rpf δ s)
          = fun s : ℝ => 1 - Real.smoothTransition ((s - δ) / δ) := by
        funext s
        rw [rpf, stp]
      rw [hfun]
      exact contDiff_const.sub
        (Real.smoothTransition.contDiff.comp ((contDiff_id.sub contDiff_const).div_const δ))
    exact hC.contDiffAt.differentiableAt (by simp)
  have hz : deriv (fun s : ℝ => rpf δ s) σ = 0 := by
    refine HasDerivWithinAt.deriv_eq_zero
      ((hasDerivWithinAt_const (c := (0 : ℝ)) (s := Set.Ici σ) (x := σ)).congr
        (fun y hy => fluxAux_rpf_eq_zero hδ (le_trans h hy))
        (fluxAux_rpf_eq_zero hδ h))
      (uniqueDiffWithinAt_Ici σ)
  exact (hd.hasDerivAt).congr_deriv hz

/-- `HasDerivAt phc 0 σ` for `σ ≥ 2δ`. -/
lemma fluxAux_hasDerivAt_phc {δ σ : ℝ} (hδ : 0 < δ) (k : ℤ) (h : 2 * δ ≤ σ) :
    HasDerivAt (fun s : ℝ => phc δ k s) 0 σ := by
  have hd : DifferentiableAt ℝ (fun s : ℝ => phc δ k s) σ := by
    have hC : ContDiff ℝ ∞ (fun s : ℝ => phc δ k s) := by
      have hfun : (fun s : ℝ => phc δ k s)
          = fun s : ℝ => (-(Real.pi / 2) - 2 * Real.pi * k) *
              Real.smoothTransition ((s - δ) / δ) := by
        funext s
        rw [phc, stp]
      rw [hfun]
      exact contDiff_const.mul
        (Real.smoothTransition.contDiff.comp ((contDiff_id.sub contDiff_const).div_const δ))
    exact hC.contDiffAt.differentiableAt (by simp)
  have hz : deriv (fun s : ℝ => phc δ k s) σ = 0 := by
    refine HasDerivWithinAt.deriv_eq_zero
      ((hasDerivWithinAt_const (c := (-(Real.pi / 2) - 2 * Real.pi * k))
        (s := Set.Ici σ) (x := σ)).congr
        (fun y hy => fluxAux_phc_eq hδ k (le_trans h hy))
        (fluxAux_phc_eq hδ k h))
      (uniqueDiffWithinAt_Ici σ)
  exact (hd.hasDerivAt).congr_deriv hz

/-- The `σ`-derivative of the far shape.  Both `rpf` and `phc` have vanishing derivative at
`σ ≥ 2δ`, so the chain rule in the second variable of `CI.c` contributes nothing. -/
lemma fluxAux_sigma_deriv (CI : Work.RPV.CurveIsotopy) {δ : ℝ} (hδ : 0 < δ) (k : ℤ)
    {σ τ t : ℝ} (hσ : 2 * δ ≤ σ) :
    deriv (fun s : ℝ => (rd s : ℂ) * CI.c (rpf δ s * τ) (t + phc δ k s)) σ
      = ((deriv rd σ : ℝ) : ℂ) *
          Complex.exp (((t + phc δ k σ : ℝ) : ℂ) * Complex.I) := by
  have hne : (-1 : ℝ) < σ := by linarith
  have hrpf := fluxAux_hasDerivAt_rpf (δ := δ) hδ hσ
  have hphc := fluxAux_hasDerivAt_phc (δ := δ) hδ k hσ
  have hpair : HasDerivAt (fun s : ℝ => (rpf δ s * τ, t + phc δ k s)) ((0 : ℝ), 0) σ :=
    ((hrpf.mul_const τ).congr_deriv (by ring)).prodMk (hphc.const_add t)
  have hJ : HasFDerivAt (fun y : ℝ × ℝ => CI.c y.1 y.2)
      (fderiv ℝ (fun y : ℝ × ℝ => CI.c y.1 y.2) (rpf δ σ * τ, t + phc δ k σ))
      (rpf δ σ * τ, t + phc δ k σ) :=
    ((CI.smooth.differentiable (by simp)).differentiableAt).hasFDerivAt
  have hcomp := hJ.comp_hasDerivAt σ hpair
  have hinner : HasDerivAt (fun s : ℝ => CI.c (rpf δ s * τ) (t + phc δ k s)) 0 σ := by
    have h' : HasDerivAt ((fun y : ℝ × ℝ => CI.c y.1 y.2) ∘
        fun s : ℝ => (rpf δ s * τ, t + phc δ k s)) 0 σ :=
      hcomp.congr_deriv (map_zero _)
    have hfun : ((fun y : ℝ × ℝ => CI.c y.1 y.2) ∘
          fun s : ℝ => (rpf δ s * τ, t + phc δ k s))
        = fun s : ℝ => CI.c (rpf δ s * τ) (t + phc δ k s) := by
      funext s
      rfl
    rw [hfun] at h'
    exact h'
  have hdrd : HasDerivAt (fun s : ℝ => (rd s : ℂ)) ((deriv rd σ : ℝ) : ℂ) σ := by
    have h1 : HasDerivAt (fun s : ℝ => rd s) (deriv rd σ) σ :=
      (fluxAux_hasDerivAt_rd hne).congr_deriv (fluxAux_deriv_rd hne).symm
    exact Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt σ h1
  have hout : HasDerivAt (fun s : ℝ => (rd s : ℂ) * CI.c (rpf δ s * τ) (t + phc δ k s))
      (((deriv rd σ : ℝ) : ℂ) * CI.c (rpf δ σ * τ) (t + phc δ k σ)) σ := by
    have h := hdrd.mul hinner
    rw [mul_zero, add_zero] at h
    exact h
  have hval : ((deriv rd σ : ℝ) : ℂ) * CI.c (rpf δ σ * τ) (t + phc δ k σ)
      = ((deriv rd σ : ℝ) : ℂ) *
          Complex.exp (((t + phc δ k σ : ℝ) : ℂ) * Complex.I) := by
    rw [fluxAux_rpf_eq_zero hδ hσ, zero_mul, CI.start]
  rw [hout.deriv, hval]

/-- The `t`-derivative of the `τ = 0` slice of the far shape. -/
lemma fluxAux_t_deriv (CI : Work.RPV.CurveIsotopy) (δ : ℝ) (k : ℤ) (σ t : ℝ) :
    deriv (fun s : ℝ => (rd σ : ℂ) * CI.c 0 (s + phc δ k σ)) t
      = (rd σ : ℂ) *
          (Complex.exp (((t + phc δ k σ : ℝ) : ℂ) * Complex.I) * Complex.I) := by
  have hfam : (fun s : ℝ => (rd σ : ℂ) * CI.c 0 (s + phc δ k σ))
      = fun s : ℝ =>
          (rd σ : ℂ) * Complex.exp (((s + phc δ k σ : ℝ) : ℂ) * Complex.I) := by
    funext s
    rw [CI.start]
  rw [hfam]
  have hlin : HasDerivAt (fun s : ℝ => ((s + phc δ k σ : ℝ) : ℂ) * Complex.I) Complex.I t := by
    have h := (((hasDerivAt_id t).add_const (phc δ k σ)).ofReal_comp).mul_const Complex.I
    simpa using h
  have hexp : HasDerivAt (fun s : ℝ => Complex.exp (((s + phc δ k σ : ℝ) : ℂ) * Complex.I))
      (Complex.exp (((t + phc δ k σ : ℝ) : ℂ) * Complex.I) * Complex.I) t := by
    have h := (Complex.hasDerivAt_exp (((t + phc δ k σ : ℝ) : ℂ) * Complex.I)).comp t hlin
    have hfun : (Complex.exp ∘ fun s : ℝ => ((s + phc δ k σ : ℝ) : ℂ) * Complex.I)
        = fun s : ℝ => Complex.exp (((s + phc δ k σ : ℝ) : ℂ) * Complex.I) := by
      funext s
      rfl
    rw [hfun] at h
    exact h
  rw [(hexp.const_mul ((rd σ : ℂ))).deriv]

/-! ## 5. The flux integrand -/

/-- `ω_ℂ (x · E) (y · (E · I)) = x y` whenever `‖E‖ = 1`. -/
lemma fluxAux_omegaC_far (x y : ℝ) (E : ℂ) (hE : ‖E‖ = 1) :
    Work.RPV.ωC ((x : ℂ) * E) ((y : ℂ) * (E * Complex.I)) = x * y := by
  unfold Work.RPV.ωC
  have hc : (starRingEnd ℂ) E * E = 1 := by
    rw [Complex.conj_mul', hE]
    norm_num
  rw [map_mul, Complex.conj_ofReal]
  have hre : (↑x * (starRingEnd ℂ) E * (↑y * (E * Complex.I))).im
      = (↑x * ↑y * ((starRingEnd ℂ) E * E) * Complex.I).im := by
    congr 1
    ring
  rw [hre, hc, mul_one, Complex.mul_I_im]
  simp

end

theorem noL_far_flux (CI : Work.RPV.CurveIsotopy) (W : ℝ → ℝ → ℝ → Work.RPV.PS)
    (ρh : ℝ → ℝ → ℝ → ℝ) {δ : ℝ} (hδ : 0 < δ) (k : ℤ) :
    ∀ τ ∈ Set.Icc (0 : ℝ) 1, ∀ σ : ℝ, 2 * δ ≤ σ → ∀ t : ℝ,
      Work.RPV.ωC (deriv (fun s : ℝ => Work.RPB.B5.GAM CI W ρh δ k τ s t) σ)
          (deriv (fun s : ℝ => Work.RPB.B5.GAM CI W ρh δ k τ σ s) t) = 1 := by
  intro τ hτ σ hσ t
  have hδσ : δ < σ := by linarith
  -- the `σ`-derivative of the collar at the far end
  have hA : deriv (fun s : ℝ => GAM CI W ρh δ k τ s t) σ
      = ((deriv rd σ : ℝ) : ℂ) *
          Complex.exp (((t + phc δ k σ : ℝ) : ℂ) * Complex.I) := by
    have hev : Filter.EventuallyEq (nhds σ) (fun s : ℝ => GAM CI W ρh δ k τ s t)
        (fun s : ℝ => (rd s : ℂ) * CI.c (rpf δ s * τ) (t + phc δ k s)) :=
      Filter.eventually_of_mem (isOpen_Ioi.mem_nhds hδσ)
        (fun s hs => fluxAux_GAM_eq_far CI W ρh hδ k hτ (σ := s) (t := t) hs)
    rw [hev.deriv_eq]
    exact fluxAux_sigma_deriv CI hδ k hσ
  -- the `t`-derivative of the collar at the far end
  have hB : deriv (fun s : ℝ => GAM CI W ρh δ k τ σ s) t
      = (rd σ : ℂ) *
          (Complex.exp (((t + phc δ k σ : ℝ) : ℂ) * Complex.I) * Complex.I) := by
    have hfam : (fun s : ℝ => GAM CI W ρh δ k τ σ s)
        = fun s : ℝ => (rd σ : ℂ) * CI.c 0 (s + phc δ k σ) := by
      funext s
      rw [fluxAux_GAM_eq_far CI W ρh hδ k hτ (σ := σ) (t := s) hδσ,
        fluxAux_rpf_eq_zero hδ hσ, zero_mul]
    rw [hfam]
    exact fluxAux_t_deriv CI δ k σ t
  rw [hA, hB]
  have hnorm : ‖Complex.exp (((t + phc δ k σ : ℝ) : ℂ) * Complex.I)‖ = 1 :=
    Complex.norm_exp_ofReal_mul_I (t + phc δ k σ)
  rw [fluxAux_omegaC_far (deriv rd σ) (rd σ)
    (Complex.exp (((t + phc δ k σ : ℝ) : ℂ) * Complex.I)) hnorm]
  rw [fluxAux_deriv_rd (σ := σ) (by linarith : (-1 : ℝ) < σ)]
  exact one_div_mul_cancel (ne_of_gt (fluxAux_rd_pos (by linarith : (-1 : ℝ) < σ)))

end Work.RPB.B5
