import Mathlib
import Submission.Work.L62.lowcyl
import Submission.Work.L62.avail_down

namespace Work.L62LD

open MandelDim Set Filter Topology
open scoped Topology

noncomputable section

variable {g₀ : ℂ → ℂ} {D : Set ℂ}

/-! ## The reflected pushdown of a lower section

`H ζ = τ₀ (pushdown σ (τ₀ ζ))` (and `H 0 = 0`) is the reflection of the pushed-down lower section
`pushdown σ` across the puncture `0` of the cylinder.  This file proves the properties of `H` that
the L62 head proof needs, directly from the section axioms (`hσd`, `hσmem`, `hσsec`, `hσT`,
`hσasymp`), without going through the sibling files `Work.L62.reflected_pushdown_deriv` /
`Work.L62.reflected_pushdown_diffOn_mapsTo` / `Work.L62.low_descent`. -/

/-- The reflected pushdown of a lift `σ`: `H ζ = τ₀ (pushdown σ (τ₀ ζ))`, `H 0 = 0`. -/
def reflPushdown (σ : ℂ → ℂ) : ℂ → ℂ := fun ζ =>
  if ζ = 0 then 0 else MandelDim.tau0 (MandelDim.pushdown σ (MandelDim.tau0 ζ))

/-- The principal lift `u ζ = log (τ₀ ζ)/(2πi)` of the reflected coordinate: `u ζ → -i∞` as
`ζ → 0`. -/
def uLow (ζ : ℂ) : ℂ := Complex.log (MandelDim.tau0 ζ) / (2 * Real.pi * Complex.I)

/-! ## Algebra of `τ₀` -/

/-- `τ₀ (a * b) = -(τ₀ a * τ₀ b)`: `τ₀ w = -1/w` reverses products up to a sign. -/
lemma tau0_mul (a b : ℂ) :
    MandelDim.tau0 (a * b) = -(MandelDim.tau0 a * MandelDim.tau0 b) := by
  simp only [MandelDim.tau0, div_eq_mul_inv, mul_inv_rev]
  ring

/-- `τ₀ (π (w + β)) = τ₀ (π w) · π (-β)`: a shift by `β` in the lift becomes a multiplication by
`π (-β)` in the cylinder. -/
lemma tau0_piExp_add (w β : ℂ) :
    MandelDim.tau0 (MandelDim.piExp (w + β)) =
      MandelDim.tau0 (MandelDim.piExp w) * MandelDim.piExp (-β) := by
  rw [Work.Repel.PushdownHolo.piExp_mul w β, tau0_mul, Work.L62.ad_tau0_piExp β]
  ring

/-! ## The derivative of the reflected pushdown at the puncture

The content is a pure limit computation: for `ζ → 0` (`ζ ≠ 0`) with `u = uLow ζ` one has
`ζ⁻¹ = -π u` and `pushdown σ (τ₀ ζ) = π (σ u)`, hence
`ζ⁻¹ · H ζ = π (u - σ u) → π (cl - β)`.  No differentiability of `σ` is used, only the drift
`σ u - u → β - cl` at the lower end. -/

/-- Imaginary part of the principal lift: `(log (τ₀ z)/(2πi)).im = -log‖τ₀ z‖/(2π)`. -/
lemma im_uLow (z : ℂ) :
    (uLow z).im = -(Real.log ‖MandelDim.tau0 z‖) / (2 * Real.pi) := by
  show (Complex.log (MandelDim.tau0 z) / (2 * Real.pi * Complex.I)).im = _
  rw [Complex.div_im, Complex.log_re, Complex.log_im]
  have h1 : (2 * (Real.pi : ℂ) * Complex.I).re = 0 := by simp
  have h2 : (2 * (Real.pi : ℂ) * Complex.I).im = 2 * Real.pi := by simp
  have h3 : Complex.normSq ((2 : ℂ) * ↑Real.pi * Complex.I) = (2 * Real.pi) ^ 2 := by
    rw [show ((2 : ℂ) * ↑Real.pi * Complex.I) = ↑(2 * Real.pi) * Complex.I by push_cast; ring]
    rw [Complex.normSq_apply]
    simp
    ring
  rw [h1, h2, h3]
  field_simp
  ring

/-- The principal lift of `τ₀ ζ` runs to the *lower* end of the cylinder as `ζ → 0`. -/
lemma tendsto_uLow_lowerEnd : Tendsto uLow (𝓝[≠] (0 : ℂ)) MandelDim.lowerEnd := by
  rw [MandelDim.lowerEnd, Filter.tendsto_comap_iff, Filter.tendsto_atBot]
  intro c
  rw [eventually_nhdsWithin_iff, Metric.eventually_nhds_iff]
  refine ⟨Real.exp (2 * Real.pi * c), Real.exp_pos _, fun ζ hζ hζne => ?_⟩
  simp only [Function.comp_apply]
  have hτ : ‖MandelDim.tau0 ζ‖ = 1 / ‖ζ‖ := Work.L62.norm_tau0 ζ
  rw [im_uLow, hτ, one_div, Real.log_inv, neg_neg]
  have hζ' : ‖ζ‖ < Real.exp (2 * Real.pi * c) := by
    rw [dist_eq_norm, sub_zero] at hζ
    exact hζ
  have hlog : Real.log ‖ζ‖ < 2 * Real.pi * c := by
    have h := Real.log_lt_log (norm_pos_iff.mpr hζne) hζ'
    rwa [Real.log_exp] at h
  have h2π : (0 : ℝ) < 2 * Real.pi := by positivity
  rw [div_le_iff₀ h2π]
  linarith

/-- Pointwise slope identity: for `ζ ≠ 0` and `u = uLow ζ`,
`ζ⁻¹ · τ₀ (pushdown σ (τ₀ ζ)) = π (u - σ u)`. -/
lemma slope_reflPushdown {σ : ℂ → ℂ} {ζ : ℂ} (hζ : ζ ≠ 0) :
    ζ⁻¹ * MandelDim.tau0 (MandelDim.pushdown σ (MandelDim.tau0 ζ)) =
      MandelDim.piExp (uLow ζ - σ (uLow ζ)) := by
  have ht : MandelDim.tau0 ζ ≠ 0 := Work.L62.tau0_ne_zero hζ
  have hpiu : MandelDim.piExp (uLow ζ) = MandelDim.tau0 ζ := by
    show MandelDim.piExp (Complex.log (MandelDim.tau0 ζ) / (2 * Real.pi * Complex.I)) = _
    exact Work.Horn.MandelDim.piExp_log_div _ ht
  -- `ζ⁻¹ = -π u`
  have hζinv : ζ⁻¹ = -(MandelDim.piExp (uLow ζ)) := by
    have h1 : MandelDim.piExp (uLow ζ) = -ζ⁻¹ := by
      rw [hpiu]
      simp only [MandelDim.tau0, div_eq_mul_inv, neg_mul, one_mul]
    rw [h1, neg_neg]
  -- the pushdown is `π ∘ σ ∘ u`
  have hpush : MandelDim.pushdown σ (MandelDim.tau0 ζ) = MandelDim.piExp (σ (uLow ζ)) := by
    rw [Work.Horn.MandelDim.pushdown_of_ne σ ht]
    rfl
  rw [hpush, hζinv, Work.L62.ad_tau0_piExp, neg_mul_neg,
    ← Work.Repel.PushdownHolo.piExp_mul]
  congr 1

/-- **Derivative at the puncture of the reflected pushdown.**  If `σ` has lower-end drift
`β - cl`, then `H = reflPushdown σ` is differentiable at `0` with derivative `π (cl - β)`. -/
theorem reflPushdown_deriv {β cl : ℂ} {σ : ℂ → ℂ}
    (hasymp : Filter.Tendsto (fun w => σ w - w - (β - cl)) MandelDim.lowerEnd (nhds 0)) :
    HasDerivAt (reflPushdown σ) (MandelDim.piExp (cl - β)) 0 := by
  have hF0 : reflPushdown σ 0 = 0 := by
    simp only [reflPushdown]
    simp
  rw [hasDerivAt_iff_tendsto_slope]
  -- the drift, transported to `ζ → 0`
  have hu : Tendsto uLow (𝓝[≠] (0 : ℂ)) MandelDim.lowerEnd := tendsto_uLow_lowerEnd
  have hdrift : Tendsto (fun ζ : ℂ => σ (uLow ζ) - uLow ζ - (β - cl))
      (𝓝[≠] (0 : ℂ)) (𝓝 0) := hasymp.comp hu
  -- `u ζ - σ (u ζ) - (cl - β) → 0`
  have h0 : Tendsto (fun ζ : ℂ => uLow ζ - σ (uLow ζ) - (cl - β))
      (𝓝[≠] (0 : ℂ)) (𝓝 0) := by
    have h : (fun ζ : ℂ => -(σ (uLow ζ) - uLow ζ - (β - cl)))
        = fun ζ : ℂ => uLow ζ - σ (uLow ζ) - (cl - β) := by
      funext ζ
      ring
    rw [← h]
    simpa using hdrift.neg
  have h1 : Tendsto (fun ζ : ℂ => (cl - β) + (uLow ζ - σ (uLow ζ) - (cl - β)))
      (𝓝[≠] (0 : ℂ)) (𝓝 (cl - β)) := by
    simpa using Tendsto.const_add (cl - β) h0
  -- hence `π (u ζ - σ (u ζ)) → π (cl - β)`
  have hπ : Tendsto (fun ζ : ℂ => MandelDim.piExp (uLow ζ - σ (uLow ζ)))
      (𝓝[≠] (0 : ℂ)) (𝓝 (MandelDim.piExp (cl - β))) := by
    have hcont : Continuous MandelDim.piExp := by
      unfold MandelDim.piExp
      fun_prop
    have h4 : Tendsto (fun ζ : ℂ => MandelDim.piExp
        ((cl - β) + (uLow ζ - σ (uLow ζ) - (cl - β))))
        (𝓝[≠] (0 : ℂ)) (𝓝 (MandelDim.piExp (cl - β))) :=
      (hcont.tendsto (cl - β)).comp h1
    refine h4.congr (fun ζ => ?_)
    congr 1
    ring
  -- the slope of `H` at `0` is eventually `ζ ↦ π (u ζ - σ (u ζ))`
  have hev : slope (reflPushdown σ) 0 =ᶠ[𝓝[≠] (0 : ℂ)]
      fun ζ : ℂ => MandelDim.piExp (uLow ζ - σ (uLow ζ)) := by
    filter_upwards [self_mem_nhdsWithin] with ζ hζ
    have hζ' : ζ ≠ 0 := by simpa using hζ
    have hval : reflPushdown σ ζ
        = MandelDim.tau0 (MandelDim.pushdown σ (MandelDim.tau0 ζ)) := by
      simp only [reflPushdown]
      exact ite_eq_right hζ'
    simp only [slope, hF0, vsub_eq_sub, sub_zero, smul_eq_mul, hval]
    exact slope_reflPushdown hζ'
  exact hπ.congr' hev.symm

/-! ## Holomorphy and self-map property of the reflected pushdown -/

/-- **The reflected pushdown of a lift over the lower horn is holomorphic on the lower cylinder
(away from the puncture) and a self-map of it.** -/
theorem reflPushdown_diffOn_mapsTo (d : MandelDim.ParabData g₀ D)
    (hd : MandelDim.HornData d) {σ : ℂ → ℂ}
    (hσd : DifferentiableOn ℂ σ hd.Bl)
    (hσmem : ∀ y ∈ hd.Bl, σ y ∈ hd.Bl)
    (hσT : ∀ y ∈ hd.Bl, σ (y + 1) = σ y + 1) :
    DifferentiableOn ℂ (reflPushdown σ) (Work.L62.lowOmega d hd \ {0}) ∧
      Set.MapsTo (reflPushdown σ) (Work.L62.lowOmega d hd) (Work.L62.lowOmega d hd) := by
  classical
  -- `pushdown σ` is holomorphic on `π '' hd.Bl` and `π`-intertwines `σ` there
  have hpd : DifferentiableOn ℂ (MandelDim.pushdown σ) (MandelDim.piExp '' hd.Bl) :=
    Work.Repel.pushdown_holo ⟨hd.Bl_T, hσT⟩ hσd
  have hpdval : ∀ w ∈ hd.Bl,
      MandelDim.pushdown σ (MandelDim.piExp w) = MandelDim.piExp (σ w) :=
    fun w hw => Work.Horn.MandelDim.pushdown_piExp hd.Bl_T (fun y hy _ => hσT y hy) hw
  have hpi_open : IsOpen (MandelDim.piExp '' hd.Bl) := Work.L62.ad_isOpen_piExp_image hd.Bl_open
  -- membership: a non-zero point of `lowOmega` has `τ₀`-image in `π '' hd.Bl`
  have htau : ∀ ζ : ℂ, ζ ∈ Work.L62.lowOmega d hd → ζ ≠ 0 →
      MandelDim.tau0 ζ ∈ MandelDim.piExp '' hd.Bl := by
    intro ζ hζ hζ0
    rw [Work.L62.lowOmega] at hζ
    rcases hζ with h | ⟨x, hxmem, hxζ⟩
    · exact absurd h hζ0
    · rw [← hxζ, Work.L62.tau0_tau0]
      exact hxmem
  refine ⟨?_, ?_⟩
  · -- complex differentiability on `lowOmega \ {0}`
    intro ζ hζ
    have hζ0 : ζ ≠ 0 := by simpa using hζ.2
    have hmem := htau ζ hζ.1 hζ0
    have hP : DifferentiableAt ℂ (MandelDim.pushdown σ) (MandelDim.tau0 ζ) :=
      (hpd (MandelDim.tau0 ζ) hmem).differentiableAt (hpi_open.mem_nhds hmem)
    have hne : MandelDim.pushdown σ (MandelDim.tau0 ζ) ≠ 0 := by
      obtain ⟨w, hw, hwπ⟩ := hmem
      rw [← hwπ, hpdval w hw]
      exact Work.Horn.MandelDim.piExp_ne_zero (σ w)
    have h0 : DifferentiableAt ℂ
        (fun ζ : ℂ => MandelDim.tau0 (MandelDim.pushdown σ (MandelDim.tau0 ζ))) ζ :=
      (Work.L62.differentiableAt_tau0 hne).comp ζ
        (hP.comp ζ (Work.L62.differentiableAt_tau0 hζ0))
    have hev : reflPushdown σ
        =ᶠ[𝓝 ζ] (fun ζ : ℂ => MandelDim.tau0 (MandelDim.pushdown σ (MandelDim.tau0 ζ))) := by
      filter_upwards [isOpen_compl_singleton.mem_nhds (by simpa using hζ0)] with w hw
      simp only [reflPushdown]
      exact ite_eq_right (by simpa using hw)
    exact (hev.differentiableAt_iff.mpr h0).differentiableWithinAt
  · -- the self-map property
    intro ζ hζ
    by_cases hζ0 : ζ = 0
    · simp only [reflPushdown]
      rw [ite_eq_left hζ0]
      exact Work.L62.zero_mem_lowOmega d hd
    · have hval : reflPushdown σ ζ
          = MandelDim.tau0 (MandelDim.pushdown σ (MandelDim.tau0 ζ)) := by
        simp only [reflPushdown]
        exact ite_eq_right hζ0
      obtain ⟨w, hw, hwπ⟩ := htau ζ hζ hζ0
      rw [hval, ← hwπ, hpdval w hw, Work.L62.lowOmega_eq_image_qlow]
      exact Or.inr ⟨σ w, hσmem w hw, by rw [Work.L62.qlow_eq_tau0]⟩

/-- **The reflected pushdown of a lower section, on the lower cylinder.**  If `σ` is a section of
`ĥ = d.E - β` over the lower horn mapping the horn into itself and `T`-equivariantly, then
`reflPushdown σ` maps the cylinder point `qlow w = τ₀ (π w)` to `qlow (σ w)`. -/
lemma reflPushdown_qlow {σ : ℂ → ℂ} (d : MandelDim.ParabData g₀ D) (hd : MandelDim.HornData d)
    (hσT : ∀ y ∈ hd.Bl, σ (y + 1) = σ y + 1) {w : ℂ} (hw : w ∈ hd.Bl) :
    reflPushdown σ (Work.L62.qlow w) = Work.L62.qlow (σ w) := by
  have hne : Work.L62.qlow w ≠ 0 := Work.L62.qlow_ne_zero w
  have hτ : MandelDim.tau0 (Work.L62.qlow w) = MandelDim.piExp w := by
    rw [Work.L62.qlow_eq_tau0, Work.L62.tau0_tau0]
  have hpush : MandelDim.pushdown σ (MandelDim.piExp w) = MandelDim.piExp (σ w) :=
    Work.Horn.MandelDim.pushdown_piExp hd.Bl_T (fun y hy _ => hσT y hy) hw
  have hval : reflPushdown σ (Work.L62.qlow w)
      = MandelDim.tau0 (MandelDim.pushdown σ (MandelDim.tau0 (Work.L62.qlow w))) := by
    simp only [reflPushdown]
    exact ite_eq_right hne
  rw [hval, hτ, hpush, Work.L62.qlow_eq_tau0]

-- NOTE for the prover: `Submission/Work/L62/reflected_pushdown_deriv.lean` and
-- `Submission/Work/L62/reflected_pushdown_diffOn_mapsTo.lean` contain `sorry`s, and hence so does
-- everything that uses them, in particular `Work.L62.low_descent` (`#print axioms` shows
-- `sorryAx`).  Do NOT use any of those three: their statements must be re-proved here (the
-- holomorphy/self-map part away from `0` is `Work.Repel.PushdownHolo.pushdown_holo` applied to
-- `σ`, then `τ₀` on both sides; the derivative at `0` is the direct computation in the doc string;
-- the `τ₀`-relation is the argument at the end of `Work.L62.low_descent`'s proof, which you may
-- copy).
/-- **The reflected pushdown of a lower section, in the form the L62 head proof needs.**  Let
`σ : ℂ → ℂ` be a holomorphic section of `ĥ = d.E - β` over the lower horn `hd.Bl`
(`d.E (σ y) - β = y` for `y ∈ hd.Bl`), mapping `hd.Bl` into itself, `T`-equivariant there and
normalised at the lower end (`σ w - w - (β - cl) → 0`).  Let
`H ζ = if ζ = 0 then 0 else τ₀ (pushdown σ (τ₀ ζ))` be its reflected pushdown (`τ₀ z = -1/z`,
`pushdown σ η = π (σ (log η / 2πi))`, `π = piExp`, and `lowOmega d hd = {0} ∪ τ₀ (π '' hd.Bl)`).

Conclusion: `H` fixes `0`, is holomorphic on `lowOmega d hd`, maps it into itself, is injective
there, has derivative `π (cl - β)` at `0`, satisfies the section relation
`τ₀ (pushdown d.E (τ₀ (H ζ))) = π (-β) · ζ`, and the lift/link identity `H (qlow w) = qlow (σ w)`
for `w ∈ hd.Bl` (`qlow w = τ₀ (π w)`). -/
theorem refl_pushdown {g₀ : ℂ → ℂ} {D : Set ℂ} (d : MandelDim.ParabData g₀ D)
    (hd : MandelDim.HornData d) {β cl : ℂ}
    (hcl : Filter.Tendsto (fun w => d.E w - w) MandelDim.lowerEnd (nhds cl))
    {σ : ℂ → ℂ} (hσd : DifferentiableOn ℂ σ hd.Bl)
    (hσmem : ∀ y ∈ hd.Bl, σ y ∈ hd.Bl)
    (hσsec : ∀ y ∈ hd.Bl, d.E (σ y) - β = y)
    (hσT : ∀ y ∈ hd.Bl, σ (y + 1) = σ y + 1)
    (hσasymp : Filter.Tendsto (fun w => σ w - w - (β - cl)) MandelDim.lowerEnd (nhds 0))
    {H : ℂ → ℂ}
    (hHdef : ∀ ζ : ℂ, H ζ = if ζ = 0 then 0 else
      MandelDim.tau0 (MandelDim.pushdown σ (MandelDim.tau0 ζ))) :
    H 0 = 0 ∧ HasDerivAt H (MandelDim.piExp (cl - β)) 0 ∧
    DifferentiableOn ℂ H (Work.L62.lowOmega d hd) ∧
    Set.MapsTo H (Work.L62.lowOmega d hd) (Work.L62.lowOmega d hd) ∧
    Set.InjOn H (Work.L62.lowOmega d hd) ∧
    (∀ ζ ∈ Work.L62.lowOmega d hd, ζ ≠ 0 → H ζ ≠ 0) ∧
    (∀ ζ ∈ Work.L62.lowOmega d hd,
      MandelDim.tau0 (MandelDim.pushdown d.E (MandelDim.tau0 (H ζ))) =
        MandelDim.piExp (-β) * ζ) ∧
    (∀ w ∈ hd.Bl, H (Work.L62.qlow w) = Work.L62.qlow (σ w)) := by
  classical
  have hHF : H = reflPushdown σ := funext fun ζ => hHdef ζ
  have hfix : reflPushdown σ 0 = 0 := by
    simp only [reflPushdown]
    simp
  have hderiv : HasDerivAt (reflPushdown σ) (MandelDim.piExp (cl - β)) 0 :=
    reflPushdown_deriv hσasymp
  have hdmo := reflPushdown_diffOn_mapsTo d hd hσd hσmem hσT
  have hdiff : DifferentiableOn ℂ (reflPushdown σ) (Work.L62.lowOmega d hd) := by
    intro ζ hζ
    by_cases hζ0 : ζ = 0
    · subst hζ0
      exact hderiv.differentiableAt.differentiableWithinAt
    · have hmem : ζ ∈ Work.L62.lowOmega d hd \ {0} := ⟨hζ, hζ0⟩
      have hopen : IsOpen (Work.L62.lowOmega d hd \ {0}) :=
        (Work.L62.isOpen_lowOmega d hd).sdiff isClosed_singleton
      exact ((hdmo.1 ζ hmem).differentiableAt (hopen.mem_nhds hmem)).differentiableWithinAt
  have hmaps : Set.MapsTo (reflPushdown σ) (Work.L62.lowOmega d hd) (Work.L62.lowOmega d hd) :=
    hdmo.2
  have hlink : ∀ w ∈ hd.Bl, reflPushdown σ (Work.L62.qlow w) = Work.L62.qlow (σ w) :=
    fun w hw => reflPushdown_qlow d hd hσT hw
  have hnz : ∀ ζ ∈ Work.L62.lowOmega d hd, ζ ≠ 0 → reflPushdown σ ζ ≠ 0 := by
    intro ζ hζ hζ0
    rw [Work.L62.mem_lowOmega_iff d hd] at hζ
    rcases hζ with h | ⟨w, hw, hwq⟩
    · exact absurd h hζ0
    · rw [← hwq, hlink w hw]
      exact Work.L62.qlow_ne_zero (σ w)
  -- the section relation `τ₀ (pushdown d.E (τ₀ (H ζ))) = π (-β) · ζ`
  have hrel : ∀ ζ ∈ Work.L62.lowOmega d hd,
      MandelDim.tau0 (MandelDim.pushdown d.E (MandelDim.tau0 (reflPushdown σ ζ))) =
        MandelDim.piExp (-β) * ζ := by
    intro ζ hζ
    rw [Work.L62.mem_lowOmega_iff d hd] at hζ
    rcases hζ with rfl | ⟨w, hw, hwq⟩
    · simp [hfix, MandelDim.tau0, Work.Horn.MandelDim.pushdown_zero]
    · have hval : reflPushdown σ ζ = Work.L62.qlow (σ w) := by
        rw [← hwq]
        exact hlink w hw
      have hτ : MandelDim.tau0 (reflPushdown σ ζ) = MandelDim.piExp (σ w) := by
        rw [hval, Work.L62.qlow_eq_tau0, Work.L62.tau0_tau0]
      have hσw : σ w ∈ hd.Bl := hσmem w hw
      have hEqv : d.E (σ w) = w + β := by
        have h := hσsec w hw
        linear_combination h
      have hpushE : MandelDim.pushdown d.E (MandelDim.piExp (σ w)) =
          MandelDim.piExp (w + β) := by
        rw [Work.Horn.MandelDim.pushdown_piExp hd.Bl_T
          (fun y hy _ => Work.L62.E_add_one_Bl d hd hy) hσw, hEqv]
      rw [hτ, hpushE, ← hwq, Work.L62.qlow_eq_tau0, mul_comm]
      exact tau0_piExp_add w β
  have hinj : Set.InjOn (reflPushdown σ) (Work.L62.lowOmega d hd) := by
    intro ζ₁ h₁ ζ₂ h₂ heq
    have h1 := hrel ζ₁ h₁
    have h2 := hrel ζ₂ h₂
    rw [heq] at h1
    exact mul_left_cancel₀ (Work.Horn.MandelDim.piExp_ne_zero (-β)) (h1.symm.trans h2)
  rw [hHF]
  exact ⟨hfix, hderiv, hdiff, hmaps, hinj, hnz, hrel, hlink⟩

end

end Work.L62LD
