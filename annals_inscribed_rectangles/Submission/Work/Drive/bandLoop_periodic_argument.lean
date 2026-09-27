import Mathlib
import Submission.Work.Drive.chordWideAnnulusDescent
import Submission.Work.Drive.exists_capAngle_periodic
import Submission.Work.Drive.directionStabilization

namespace Work.Drive

open scoped ContDiff Topology
open Filter
open Work.Drive.Neutral

noncomputable section

/-!
# The direction datum of the band at the seam, and its periodic argument

`Work.Drive.directionStabilization_of_nullhomotopic` needs, for the descended chord data `(M, W)` of
`Work.Drive.chordWideAnnulusDescent` and a level `τ₁ < 0`, a *continuous unit-valued extension*
`G` over the disc `‖x‖ ≤ 1/4` of the loop `x ↦ c · conj (w_h (x,τ₁))` — equivalently, the
*winding-zero* condition `deg w_h = ε − m = 0` of `PLANE_CHART_FINAL.md` §9.1.  This file produces that
extension from the geometric input `Work.Drive.WrapData γ` (plus the Umlaufsatz), so that the plane
chart's direction-datum stabiliser becomes unconditional.

## The two steps

**Step 1 (this file, the identification and the square-root).**  At the seam `τ = 0` and on the unit
circle the descent data *is* the diagonal data of the symmetric chord family:
`M (x,0) = dataMid γ x 0 = symmC (curve γ σ)` and `W (x,0) = dchW γ (x,0) = 2 · symmWC γ σ 0`
(the second is the derivative at `0` of `dchW_smul`, `s • dchW γ (x,s) = dataChord γ x s`).  Hence

> `w_h (e^{iσ}, 0)² = symmE γ σ 0 · (star (symmD γ σ 0))²  =  circleOf (Θ σ)`,

`Θ` the `2π`-periodic cap angle of the **proved** `Work.Drive.exists_capAngle_periodic`.  So
`σ ↦ w_h (e^{iσ},0) / exp (π i Θ σ)` is continuous and takes values in `{1, −1}`, hence (the domain
being connected) is a *constant* `ε₀ ∈ {±1}`, and `θ σ := −π Θ σ + arg (c · ε₀)` is a continuous
`2π`-periodic argument of the seam loop `σ ↦ c · conj (w_h (e^{iσ},0))`.  **No degree theory is used.**

**Step 2 (next file).**  The loop and the target loop at `(r,τ) = (1/4, τ₁)` are joined by a
non-vanishing homotopy through the annulus `1/4 ≤ r ≤ 1`, `τ₁ ≤ τ ≤ 0` (the non-vanishing being two
clauses of `chordWideAnnulusDescent`), so `Work.Drive.periodic_argument_of_homotopy` transports the
periodic argument to the target loop, which then gives `G` by a radial extension.

This step also removes the last *mathematical* content of §9.1: what remains there is bookkeeping.
-/

variable {γ : Circle → ℝ × ℝ}

/-- **The midpoint data at the seam.**  At `τ = 0` and on the unit circle the descent of the chord
midpoint is the position vector of the corresponding curve point. -/
lemma dataMid_exp_zero (γ : Circle → ℝ × ℝ) (σ : ℝ) :
    dataMid γ (Complex.exp ((σ : ℂ) * Complex.I)) 0 = symmC (curve γ σ) := by
  have h : curvePtAt γ (Complex.exp ((σ : ℂ) * Complex.I)) 0 = symmC (curve γ σ) := by
    rw [curvePtAt_exp, sClamp_zero, add_zero]
  rw [dataMid, endPlus, endMinus, neg_zero, h]
  field_simp
  ring

/-- **The halving data at the seam.**  At `τ = 0` and on the unit circle the descent of the chord
halving is twice the divided difference of the symmetric family, i.e. twice the tangent. -/
lemma dchW_exp_zero (γ : Circle → ℝ × ℝ)
    (hγ : Manifold.IsSmoothEmbedding (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 1)))
      (modelWithCornersSelf ℝ (ℝ × ℝ)) ((⊤ : ℕ∞) : WithTop ℕ∞) γ) (σ : ℝ) :
    dchW γ (Complex.exp ((σ : ℂ) * Complex.I), 0) = (2 : ℂ) * symmWC γ σ 0 := by
  set x : ℂ := Complex.exp ((σ : ℂ) * Complex.I) with hx
  have hx0 : x ≠ 0 := by rw [hx]; exact Complex.exp_ne_zero _
  -- continuity of both sides at `s = 0`
  have hopen : {p : ℂ × ℝ | p.1 ≠ 0} ∈ 𝓝 (x, 0) := by
    have hset : {p : ℂ × ℝ | p.1 ≠ 0} = (fun p : ℂ × ℝ => p.1) ⁻¹' ({0}ᶜ : Set ℂ) := rfl
    rw [hset]
    exact (isClosed_singleton.isOpen_compl.preimage continuous_fst).mem_nhds (by simpa using hx0)
  have hsm : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (dchW γ) (x, 0) :=
    ((contDiffOn_dchW (γ := γ) hγ).contDiffWithinAt (by simp [hx0])).contDiffAt hopen
  have hcont1 : ContinuousAt (fun s : ℝ => dchW γ (x, s)) 0 :=
    hsm.continuousAt.comp (continuousAt_const.prodMk continuousAt_id)
  have hcont2 : ContinuousAt (fun s : ℝ => (2 : ℂ) * symmWC γ σ (sClamp s)) 0 := by
    have h1 : Continuous fun s : ℝ => symmWC γ σ (sClamp s) :=
      (contDiff_symmWC (γ := γ) hγ).continuous.comp
        (continuous_const.prodMk contDiff_sClamp.continuous)
    exact continuousAt_const.mul h1.continuousAt
  -- the two sides agree off `{0}`
  have heq : (fun s : ℝ => dchW γ (x, s)) =ᶠ[𝓝[≠] (0 : ℝ)]
      (fun s : ℝ => (2 : ℂ) * symmWC γ σ (sClamp s)) := by
    show ∀ᶠ s in 𝓝[≠] (0 : ℝ), dchW γ (x, s) = (2 : ℂ) * symmWC γ σ (sClamp s)
    rw [eventually_nhdsWithin_iff]
    filter_upwards [Metric.ball_mem_nhds (0 : ℝ) (by positivity : (0 : ℝ) < Real.pi / 2)]
      with s hs hsne
    have hsabs : |s| < Real.pi / 2 := by
      have h := Metric.mem_ball.mp hs
      simpa [Real.dist_eq] using h
    have hclamp : sClamp s = s := sClamp_eq_self hsabs.le
    have hsC : ((s : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hsne
    have hkey : dchW γ (x, s) = (s⁻¹ : ℝ) • dataChord γ x s := by
      calc dchW γ (x, s) = s⁻¹ • (s • dchW γ (x, s)) := by
            rw [smul_smul, inv_mul_cancel₀ hsne, one_smul]
        _ = s⁻¹ • dataChord γ x s := by rw [dchW_smul γ hγ hx0 s]
    have hchord : dataChord γ x s = symmChordC γ σ (sClamp s) := by
      have h1 : curvePtAt γ x s = symmC (curve γ (σ + sClamp s)) := by rw [hx, curvePtAt_exp]
      have h2 : curvePtAt γ x (-s) = symmC (curve γ (σ - sClamp s)) := by
        rw [hx, curvePtAt_exp, sClamp_odd,
          show σ + -sClamp s = σ - sClamp s from by ring]
      rw [dataChord, endPlus, endMinus, h1, h2, symmChordC, chordC_eq_symmC, symmC_sub, curve]
      rfl
    rw [hkey, hchord, hclamp, symmChordC_eq_smul_symmWC (γ := γ) hγ σ s, Complex.real_smul,
      Complex.ofReal_inv, Complex.ofReal_mul]
    field_simp
    norm_num
    ring

  -- conclude by uniqueness of limits
  have h1 : Tendsto (fun s : ℝ => dchW γ (x, s)) (𝓝[≠] (0 : ℝ)) (𝓝 (dchW γ (x, 0))) :=
    hcont1.mono_left nhdsWithin_le_nhds
  have h2 : Tendsto (fun s : ℝ => (2 : ℂ) * symmWC γ σ (sClamp s)) (𝓝[≠] (0 : ℝ))
      (𝓝 ((2 : ℂ) * symmWC γ σ (sClamp 0))) := hcont2.mono_left nhdsWithin_le_nhds
  have h3 : Tendsto (fun s : ℝ => (2 : ℂ) * symmWC γ σ (sClamp s)) (𝓝[≠] (0 : ℝ))
      (𝓝 (dchW γ (x, 0))) := h1.congr' heq
  have h4 := tendsto_nhds_unique h3 h2
  rw [sClamp_zero] at h4
  exact h4


/-- **`exp (i · arg z) = z` for a unit complex number.** -/
lemma exp_arg_of_norm_one {z : ℂ} (hz : ‖z‖ = 1) :
    Complex.exp (((z.arg : ℝ) : ℂ) * Complex.I) = z := by
  have h := Complex.norm_mul_exp_arg_mul_I z
  rw [hz, Complex.ofReal_one, one_mul] at h
  exact h

/-- **A continuous map into `{1, −1}` is locally constant.** -/
lemma isLocallyConstant_of_pm_one {f : ℝ → ℂ} (hf : Continuous f)
    (h : ∀ x : ℝ, f x = 1 ∨ f x = -1) : IsLocallyConstant f := by
  intro s
  rw [isOpen_iff_mem_nhds]
  intro x hx
  rw [Set.mem_preimage] at hx
  obtain ⟨ε, hε, hεU⟩ := Metric.continuousAt_iff.mp hf.continuousAt 1 (by norm_num)
  refine Filter.mem_of_superset (Metric.ball_mem_nhds x hε) fun y hy => ?_
  rw [Set.mem_preimage]
  have hd : dist (f y) (f x) < 1 := hεU hy
  rcases h y with hy1 | hy1 <;> rcases h x with hx1 | hx1
  · simpa [hy1, hx1] using hx
  · exfalso
    have h2 : dist (1 : ℂ) (-1) = 2 := by
      rw [dist_eq_norm, show (1 : ℂ) - (-1) = (2 : ℂ) by norm_num]
      norm_num
    rw [hy1, hx1, h2] at hd
    norm_num at hd
  · exfalso
    have h2 : dist (-1 : ℂ) 1 = 2 := by
      rw [dist_eq_norm, show (-1 : ℂ) - 1 = -(2 : ℂ) by norm_num, norm_neg]
      norm_num
    rw [hy1, hx1, h2] at hd
    norm_num at hd
  · simpa [hy1, hx1] using hx


/-- **Continuity of the seam direction datum.** -/
lemma dirDatum_seam_continuous {M W : ℂ × ℝ → ℂ}
    (hMsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) M)
    (hWsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) W)
    (hMne : ∀ x : ℂ, ‖x‖ = 1 → M (x, 0) ≠ 0)
    (hWne : ∀ x : ℂ, ‖x‖ = 1 → W (x, 0) ≠ 0) :
    Continuous fun σ : ℝ => dirDatum M W (Complex.exp ((σ : ℂ) * Complex.I), 0) := by
  have hx : ∀ σ : ℝ, ‖Complex.exp ((σ : ℂ) * Complex.I)‖ = 1 := by
    intro σ
    rw [Complex.norm_exp]
    simp
  have harg : Continuous fun σ : ℝ => (Complex.exp ((σ : ℂ) * Complex.I), (0 : ℝ)) :=
    (Complex.continuous_exp.comp
      ((Complex.ofRealCLM.continuous.comp continuous_id).mul continuous_const)).prodMk
      continuous_const
  have hMc : Continuous fun σ : ℝ => M (Complex.exp ((σ : ℂ) * Complex.I), 0) :=
    hMsm.continuous.comp harg
  have hWc : Continuous fun σ : ℝ => W (Complex.exp ((σ : ℂ) * Complex.I), 0) :=
    hWsm.continuous.comp harg
  have hMn : ∀ σ : ℝ, ((‖M (Complex.exp ((σ : ℂ) * Complex.I), 0)‖ : ℝ) : ℂ) ≠ 0 := fun σ =>
    Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr (hMne _ (hx σ)))
  have hWn : ∀ σ : ℝ, ((‖W (Complex.exp ((σ : ℂ) * Complex.I), 0)‖ : ℝ) : ℂ) ≠ 0 := fun σ =>
    Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr (hWne _ (hx σ)))
  have h1 : Continuous fun σ : ℝ => M (Complex.exp ((σ : ℂ) * Complex.I), 0)
      / ((‖M (Complex.exp ((σ : ℂ) * Complex.I), 0)‖ : ℝ) : ℂ) :=
    hMc.div (Complex.ofRealCLM.continuous.comp hMc.norm) hMn
  have h2 : Continuous fun σ : ℝ => W (Complex.exp ((σ : ℂ) * Complex.I), 0)
      / ((‖W (Complex.exp ((σ : ℂ) * Complex.I), 0)‖ : ℝ) : ℂ) :=
    hWc.div (Complex.ofRealCLM.continuous.comp hWc.norm) hWn
  exact h2.mul (continuous_star.comp h1)

/-- **The direction datum at the seam is the diagonal datum of the strip.**  At `τ = 0` and on the
unit circle the *square* of the direction datum of the descent data is the squared unit direction of
the symmetric chord family: `symmE γ σ 0 · (star (symmD γ σ 0))²`, whose argument is the proved
`2π`-periodic cap angle `Θ` (`Work.Drive.exists_capAngle_periodic`). -/
theorem dirDatum_seam_sq (γ : Circle → ℝ × ℝ)
    (hγ : Manifold.IsSmoothEmbedding (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 1)))
      (modelWithCornersSelf ℝ (ℝ × ℝ)) ((⊤ : ℕ∞) : WithTop ℕ∞) γ)
    {M W : ℂ × ℝ → ℂ}
    (hMval : ∀ x : ℂ, ‖x‖ = 1 → M (x, 0) = dataMid γ x 0)
    (hWval : ∀ x : ℂ, ‖x‖ = 1 → W (x, 0) = dchW γ (x, 0))
    (hMne : ∀ x : ℂ, ‖x‖ = 1 → M (x, 0) ≠ 0)
    (hWne : ∀ x : ℂ, ‖x‖ = 1 → W (x, 0) ≠ 0)
    (σ : ℝ) :
    (dirDatum M W (Complex.exp ((σ : ℂ) * Complex.I), 0)) ^ 2
      = symmE γ σ 0 * (star (symmD γ σ 0)) ^ 2 := by
  set x : ℂ := Complex.exp ((σ : ℂ) * Complex.I) with hx
  have hx1 : ‖x‖ = 1 := by rw [hx, Complex.norm_exp]; simp
  have hM : M (x, 0) = symmC (curve γ σ) := by rw [hMval x hx1, dataMid_exp_zero]
  have hW : W (x, 0) = (2 : ℂ) * symmC (deriv (curve γ) σ) := by
    rw [hWval x hx1, dchW_exp_zero γ hγ σ, symmWC_zero (γ := γ) hγ σ]
  have hMn : M (x, 0) ≠ 0 := hMne x hx1
  have hWn : W (x, 0) ≠ 0 := hWne x hx1
  have hcn : symmC (curve γ σ) ≠ 0 := by rwa [← hM]
  have hdn : symmC (deriv (curve γ) σ) ≠ 0 := by
    intro hzero
    exact hWn (by rw [hW, hzero, mul_zero])
  have hMunit : M (x, 0) / ((‖M (x, 0)‖ : ℝ) : ℂ) = symmD γ σ 0 := by
    rw [hM, symmD_zero_eq]
  have hWunit : W (x, 0) / ((‖W (x, 0)‖ : ℝ) : ℂ)
      = symmWC γ σ 0 / ((‖symmWC γ σ 0‖ : ℝ) : ℂ) := by
    rw [hW, symmWC_zero (γ := γ) hγ σ]
    exact div_norm_ofReal_mul_const 2 (by norm_num) (symmC (deriv (curve γ) σ))
  have hwn : symmWC γ σ 0 ≠ 0 := symmWC_zero_ne_zero (γ := γ) hγ σ
  rw [dirDatum, hMunit, hWunit, mul_pow, symmE, div_eq_mul_inv, ← Complex.ofReal_inv,
    div_eq_mul_inv, one_mul]

/-- **The seam loop has a continuous `2π`-periodic argument.**  For the descent data of
`Work.Drive.chordWideAnnulusDescent` (whose value clauses are the two hypotheses `hMval`, `hWval`),
the geometric input `Work.Drive.WrapData γ` (plus the Umlaufsatz) produces a continuous `2π`-periodic
real argument of the loop `σ ↦ c · conj (w_h (e^{iσ}, 0))` — the winding-zero condition of §9.1 at the
seam, proved *without* degree theory (the square of the loop is `circleOf ∘ Θ` with `Θ` periodic, so
the quotient is a continuous `{±1}`-valued function on the connected `ℝ`, hence constant). -/
theorem seam_periodic_argument (γ : Circle → ℝ × ℝ)
    (hγ : Manifold.IsSmoothEmbedding (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 1)))
      (modelWithCornersSelf ℝ (ℝ × ℝ)) ((⊤ : ℕ∞) : WithTop ℕ∞) γ)
    (hγne : ∀ x : Circle, γ x ≠ 0) (hU : Submission.Drive.UmlaufProp) (hWrap : WrapData γ)
    {M W : ℂ × ℝ → ℂ}
    (hMsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) M)
    (hWsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) W)
    (hMval : ∀ x : ℂ, ‖x‖ = 1 → M (x, 0) = dataMid γ x 0)
    (hWval : ∀ x : ℂ, ‖x‖ = 1 → W (x, 0) = dchW γ (x, 0))
    (hMne : ∀ x : ℂ, ‖x‖ = 1 → M (x, 0) ≠ 0)
    (hWne : ∀ x : ℂ, ‖x‖ = 1 → W (x, 0) ≠ 0)
    {c : ℂ} (hc : ‖c‖ = 1) :
    ∃ θ : ℝ → ℝ, Continuous θ ∧ Function.Periodic θ (2 * Real.pi) ∧
      ∀ σ : ℝ, Complex.exp (((θ σ : ℝ) : ℂ) * Complex.I)
        = c * star (dirDatum M W (Complex.exp ((σ : ℂ) * Complex.I), 0)) := by
  obtain ⟨Θ, hΘsm, hΘper, hΘeq⟩ := exists_capAngle_periodic γ hγ hγne hU hWrap
  have hΘc : Continuous Θ := hΘsm.continuous
  have hΘp : Function.Periodic Θ (2 * Real.pi) := fun t => hΘper t
  -- the square of the loop is `circleOf ∘ Θ`
  have hsq : ∀ σ : ℝ, (dirDatum M W (Complex.exp ((σ : ℂ) * Complex.I), 0)) ^ 2
      = Complex.exp (((2 * Real.pi * Θ σ : ℝ) : ℂ) * Complex.I) := by
    intro σ
    rw [dirDatum_seam_sq γ hγ hMval hWval hMne hWne σ, ← hΘeq σ, circleOf_coe_eq_exp]
  -- the quotient is a continuous `{±1}`-valued function
  set h : ℝ → ℂ := fun σ => dirDatum M W (Complex.exp ((σ : ℂ) * Complex.I), 0)
      / Complex.exp (((Real.pi * Θ σ : ℝ) : ℂ) * Complex.I) with hh
  have hhcont : Continuous h := by
    rw [hh]
    exact (dirDatum_seam_continuous hMsm hWsm hMne hWne).div
      (Complex.continuous_exp.comp
        ((Complex.ofRealCLM.continuous.comp (continuous_const.mul hΘc)).mul continuous_const))
      (fun σ => Complex.exp_ne_zero _)
  have hhsq : ∀ σ : ℝ, h σ ^ 2 = 1 := by
    intro σ
    have hden : Complex.exp (((Real.pi * Θ σ : ℝ) : ℂ) * Complex.I) ≠ 0 :=
      Complex.exp_ne_zero _
    have h2 : (Complex.exp (((Real.pi * Θ σ : ℝ) : ℂ) * Complex.I)) ^ 2
        = Complex.exp (((2 * Real.pi * Θ σ : ℝ) : ℂ) * Complex.I) := by
      rw [sq, ← Complex.exp_add]
      congr 1
      push_cast
      ring
    have hval : h σ = dirDatum M W (Complex.exp ((σ : ℂ) * Complex.I), 0)
        / Complex.exp (((Real.pi * Θ σ : ℝ) : ℂ) * Complex.I) := rfl
    rw [hval, div_pow, h2, hsq σ, div_self (Complex.exp_ne_zero _)]
  have hhpm : ∀ σ : ℝ, h σ = 1 ∨ h σ = -1 := fun σ => sq_eq_one_iff.mp (hhsq σ)
  have hhlc : IsLocallyConstant h := isLocallyConstant_of_pm_one hhcont hhpm
  have hconst : ∀ σ : ℝ, h σ = h 0 := fun σ =>
    hhlc.apply_eq_of_isPreconnected isPreconnected_univ (Set.mem_univ σ) (Set.mem_univ 0)
  have hh0 : h 0 = 1 ∨ h 0 = -1 := hhpm 0
  have hnorm0 : ‖h 0‖ = 1 := by
    rcases hh0 with h1 | h1 <;> rw [h1] <;> norm_num
  have hstar0 : star (h 0) = h 0 := by
    rcases hh0 with h1 | h1 <;> rw [h1] <;> simp
  -- the value of the loop at every `σ`
  have hval : ∀ σ : ℝ, dirDatum M W (Complex.exp ((σ : ℂ) * Complex.I), 0)
      = h 0 * Complex.exp (((Real.pi * Θ σ : ℝ) : ℂ) * Complex.I) := by
    intro σ
    have h1 : h σ = h 0 := hconst σ
    rw [hh] at h1
    have hden : Complex.exp (((Real.pi * Θ σ : ℝ) : ℂ) * Complex.I) ≠ 0 :=
      Complex.exp_ne_zero _
    rw [div_eq_iff hden] at h1
    exact h1
  refine ⟨fun σ => -(Real.pi * Θ σ) + Complex.arg (c * h 0), ?_, ?_, ?_⟩
  · exact (((continuous_const : Continuous fun _ : ℝ => Real.pi).mul hΘc).neg).add
      (continuous_const : Continuous fun _ : ℝ => (c * h 0).arg)
  · intro σ
    simp only [hΘp σ]
  · intro σ
    have hz : ‖c * h 0‖ = 1 := by rw [norm_mul, hc, hnorm0, one_mul]
    have hstar : star (Complex.exp (((Real.pi * Θ σ : ℝ) : ℂ) * Complex.I))
        = Complex.exp (((-(Real.pi * Θ σ) : ℝ) : ℂ) * Complex.I) := by
      simp only [Complex.star_def]
      rw [(Complex.exp_conj (((Real.pi * Θ σ : ℝ) : ℂ) * Complex.I)).symm]
      congr 1
      simp only [map_mul, Complex.conj_ofReal, Complex.conj_I]
      rw [Complex.ofReal_neg]
      ring
    calc Complex.exp (((-(Real.pi * Θ σ) + Complex.arg (c * h 0) : ℝ) : ℂ) * Complex.I)
        = Complex.exp (((-(Real.pi * Θ σ) : ℝ) : ℂ) * Complex.I)
            * Complex.exp ((((c * h 0).arg : ℝ) : ℂ) * Complex.I) := by
          rw [← Complex.exp_add]
          congr 1
          push_cast
          ring
      _ = Complex.exp (((-(Real.pi * Θ σ) : ℝ) : ℂ) * Complex.I) * (c * h 0) := by
          rw [exp_arg_of_norm_one hz]
      _ = c * (h 0 * Complex.exp (((-(Real.pi * Θ σ) : ℝ) : ℂ) * Complex.I)) := by ring
      _ = c * star (dirDatum M W (Complex.exp ((σ : ℂ) * Complex.I), 0)) := by
          rw [hval σ, star_mul, hstar, hstar0]
          ring

end

end Work.Drive
