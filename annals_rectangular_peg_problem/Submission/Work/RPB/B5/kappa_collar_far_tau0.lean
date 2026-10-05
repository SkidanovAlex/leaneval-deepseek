import Mathlib
import Submission.Work.RPB.B5.kappaDefs
import Submission.Work.RPB.B5.kappa_shape_basic
import Submission.Work.RPB.B5.kA0_spec
import Submission.Work.RPB.B5.ktarg_signedArea
import Submission.Work.RPB.B5.kappa_tau0
import Submission.Work.RPB.B5.noL_far_flux
import Submission.Work.RPB.B5.signedArea_circle_scaled
import Submission.Work.RPV.levelPt_omega
import Submission.Work.RPB.B5.kcf_kac_far
import Submission.Work.RPB.B5.kcf_tau0_slice
import Submission.Work.RPB.B5.kcf_kac_tau0

/-!
# B5: the far end and the `τ = 0` slice of the `κ`-parametrised collar

This module proves `Work.RPB.B5.kappa_collar_far_tau0`, the two "explicit" conjuncts of the collar
existence theorem `collar_exists_kappa` (statements (6) and (7) of that file), uniformly in the
scale `δ ∈ (0, δ₀)`:

* **far end** (for `σ ≥ 2δ`): the collar curve is the exact circle of radius `√(2+2σ)`,
  `kgam CI W ρh δ k τ σ t = (√(2+2σ) : ℂ) · exp ((t - π/2) · I)`, and the phase is `kac = t`;
* **`τ = 0` slice**: for every `σ ≥ 0` the point
  `levelPt (kgam … 0 σ t) σ (kac … 0 σ t)` lies in the zero section `{p = 0} (statements (7)).

The `τ = 0` part rests on the fact that at `τ = 0` the glued shape *is* the target circle
(`ksb_kshape_zero_slice` for `σ ≥ 0`, and the `τ = 0` chart identity of `kappa_tau0` — where the
clamped level `kclamp δ σ = σ` and `kphc δ k σ = 0` — for `σ ∈ (-δ/4, 0)`), so that

* `karS 0 σ = signedArea (ktarg δ k σ) = 2π(1+σ)` and hence `kg 0 σ = 1`
  (`kcf_tau0_slice`), i.e. the collar is the target circle itself;
* the flux integrand is identically `1` on the circle family (`kcf_flux_ktarg`), whence
  `kac 0 σ t = kA0 0 σ + ∫₀ᵗ 1 = t + kphc δ k σ + π/2 + 2πk` (`kcf_kac_tau0`).

With `u = (√(2+2σ)) e^{iθ}`, `θ = t + kphc δ k σ` and `a = θ + π/2 + 2πk` one has
`‖u‖² = 2 + 2σ`, so the second coordinate of `levelPt u σ a` vanishes, and
`e^{-ia} u = (√(2+2σ)) · e^{-i(π/2 + 2πk)} = -(√(2+2σ)) · I`, so its real part vanishes as well.

The scale threshold is `δ₀ = min δ₁ 1`, where `δ₁ ≤ κ` comes from `kappa_tau0` (the range on which
the `τ = 0` chart is the standard circle) and `1` only enters to keep `2 + 2σ > 0` on the window
`σ ∈ (-δ/4, 0)`.

The file also records the two elementary complex-exponential facts used in the `τ = 0` computation
(`kcf_exp_neg`, `kcf_exp_mul_re`) and the far-end value of the collar (`kcf_kgam_far`).
-/

set_option autoImplicit false

noncomputable section

namespace Work.RPB.B5

/-! ## Elementary complex exponentials -/

/-- `exp (-(π/2 + 2πk) I) = -I`: the residue `2πk` is absorbed by `Complex.exp_int_mul_two_pi_mul_I`
and `exp (-(π/2) I) = conj I = -I`. -/
theorem kcf_exp_neg (k : ℤ) :
    Complex.exp (((-(Real.pi / 2 + 2 * Real.pi * (k : ℝ)) : ℝ) : ℂ) * Complex.I) = -Complex.I := by
  have hsplit : (((-(Real.pi / 2 + 2 * Real.pi * (k : ℝ)) : ℝ) : ℂ) * Complex.I)
      = (((-(Real.pi / 2) : ℝ) : ℂ) * Complex.I)
        + (((-(2 * Real.pi * (k : ℝ)) : ℝ) : ℂ) * Complex.I) := by
    push_cast; ring
  rw [hsplit, Complex.exp_add]
  have hk : (((-(2 * Real.pi * (k : ℝ)) : ℝ) : ℂ) * Complex.I)
      = ((-k : ℤ) : ℂ) * (2 * Real.pi * Complex.I) := by
    push_cast; ring
  rw [hk, Complex.exp_int_mul_two_pi_mul_I, mul_one]
  rw [show Complex.exp (((-(Real.pi / 2) : ℝ) : ℂ) * Complex.I) = -Complex.I from by
    rw [show (((-(Real.pi / 2) : ℝ) : ℂ) * Complex.I)
        = -(((Real.pi / 2 : ℝ) : ℂ) * Complex.I) by push_cast; ring]
    rw [Complex.exp_neg]
    rw [show (((Real.pi / 2 : ℝ) : ℂ) * Complex.I) = ((Real.pi : ℂ) / 2 * Complex.I) by
      push_cast; ring]
    rw [Complex.exp_pi_div_two_mul_I, Complex.inv_I]]

/-- The real part of `e^{-iA} · (R e^{iθ})` is `R · Re (e^{i(θ-A)})`. -/
theorem kcf_exp_mul_re (R θ A : ℝ) :
    (Complex.exp (-(A : ℂ) * Complex.I) * ((R : ℂ) * Complex.exp ((θ : ℂ) * Complex.I))).re
      = R * (Complex.exp (((θ - A : ℝ) : ℂ) * Complex.I)).re := by
  have h1 : Complex.exp (-(A : ℂ) * Complex.I) * ((R : ℂ) * Complex.exp ((θ : ℂ) * Complex.I))
      = (R : ℂ) * (Complex.exp (-(A : ℂ) * Complex.I) * Complex.exp ((θ : ℂ) * Complex.I)) := by
    ring
  rw [h1, ← Complex.exp_add]
  have h2 : -(A : ℂ) * Complex.I + (θ : ℂ) * Complex.I = (((θ - A : ℝ)) : ℂ) * Complex.I := by
    push_cast; ring
  rw [h2, Complex.mul_re]
  simp

/-! ## The flux of the target circle family is `1` -/

/-- `ω_ℂ` is additive in its first argument. -/
theorem kcf_omegaC_add_left (a b c : ℂ) :
    Work.RPV.ωC (a + b) c = Work.RPV.ωC a c + Work.RPV.ωC b c := by
  unfold Work.RPV.ωC
  rw [map_add, add_mul, Complex.add_im]

/-- `ω_ℂ (α z) (β w) = α β ω_ℂ z w` for real `α`, `β`. -/
theorem kcf_omegaC_smul_mul (α β : ℝ) (z w : ℂ) :
    Work.RPV.ωC ((α : ℂ) * z) ((β : ℂ) * w) = α * β * Work.RPV.ωC z w := by
  have h1 : (starRingEnd ℂ) ((α : ℂ) * z) * ((β : ℂ) * w)
      = ((α * β : ℝ) : ℂ) * ((starRingEnd ℂ) z * w) := by
    rw [map_mul, Complex.conj_ofReal, Complex.ofReal_mul]
    ring
  unfold Work.RPV.ωC
  rw [h1, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero]

/-- **The flux of the target circle family is `1`.**  Writing `ktarg δ k σ t = r(σ) e^{i(t+φ(σ))}`
with `r = krd` and `φ = kphc`, one has `∂_σ ktarg = (r' + i r φ') e^{iθ}` and
`∂_t ktarg = i r e^{iθ}`, and the `φ'` term contributes only to the real part of
`conj(∂_σ)·∂_t = i r r' + r² φ'`; hence the pairing is `r r' = 1` because `r² = 2 + 2σ`.

(The statement is phrased with `targ`/`rd`/`phc` — the definitionally identical "no-`L`" copies of
`ktarg`/`krd`/`kphc` — and transferred to `ktarg` by a `show`.) -/
theorem kcf_flux_ktarg_aux (δ : ℝ) (k : ℤ) :
    ∀ σ : ℝ, 0 ≤ σ → ∀ u : ℝ,
      Work.RPV.ωC (deriv (fun s : ℝ => Work.RPB.B5.ktarg δ k s u) σ)
        (deriv (fun s : ℝ => Work.RPB.B5.ktarg δ k σ s) u) = 1 := by
  show ∀ σ : ℝ, 0 ≤ σ → ∀ u : ℝ,
      Work.RPV.ωC (deriv (fun s : ℝ => Work.RPB.B5.targ δ k s u) σ)
        (deriv (fun s : ℝ => Work.RPB.B5.targ δ k σ s) u) = 1
  intro σ hσ u
  have h2p : 0 < 2 + 2 * σ := by linarith
  have hrd_pos : 0 < Work.RPB.B5.rd σ := by
    rw [show Work.RPB.B5.rd σ = Real.sqrt (2 + 2 * σ) from rfl]
    exact Real.sqrt_pos.mpr h2p
  have hrd_ne : Work.RPB.B5.rd σ ≠ 0 := ne_of_gt hrd_pos
  have hrd_d : HasDerivAt (fun s : ℝ => Work.RPB.B5.rd s) (1 / Work.RPB.B5.rd σ) σ := by
    have hg : HasDerivAt (fun s : ℝ => 2 + 2 * s) (0 + 2 * 1) σ :=
      (hasDerivAt_const (x := σ) (c := (2 : ℝ))).add ((hasDerivAt_id σ).const_mul (2 : ℝ))
    have hs := hg.sqrt (by linarith : (2 + 2 * σ) ≠ 0)
    have hval : (0 + 2 * 1) / (2 * Real.sqrt (2 + 2 * σ)) = 1 / Work.RPB.B5.rd σ := by
      rw [show Work.RPB.B5.rd σ = Real.sqrt (2 + 2 * σ) from rfl]
      rw [show (0 + 2 * 1 : ℝ) = 2 from by norm_num]
      rw [div_eq_div_iff (by positivity) (by positivity)]
      ring
    exact hs.congr_deriv hval
  have hphc_d : HasDerivAt (fun s : ℝ => Work.RPB.B5.phc δ k s)
      (deriv (fun s : ℝ => Work.RPB.B5.phc δ k s) σ) σ := by
    have hC : ContDiff ℝ 1 (fun s : ℝ => Work.RPB.B5.phc δ k s) := by
      unfold Work.RPB.B5.phc Work.RPB.B5.stp
      exact contDiff_const.mul
        (Real.smoothTransition.contDiff.comp ((contDiff_id.sub contDiff_const).div_const δ))
    exact (hC.contDiffAt.differentiableAt (by simp)).hasDerivAt
  have hE_d : HasDerivAt
      (fun s : ℝ => Complex.exp (((u : ℂ) + (Work.RPB.B5.phc δ k s : ℂ)) * Complex.I))
      (Complex.exp (((u : ℂ) + (Work.RPB.B5.phc δ k σ : ℂ)) * Complex.I)
        * (((deriv (fun s : ℝ => Work.RPB.B5.phc δ k s) σ : ℝ)) : ℂ) * Complex.I) σ := by
    have h1 : HasDerivAt (fun s : ℝ => ((u : ℂ) + (Work.RPB.B5.phc δ k s : ℂ)) * Complex.I)
        ((((deriv (fun s : ℝ => Work.RPB.B5.phc δ k s) σ : ℝ)) : ℂ) * Complex.I) σ :=
      (hphc_d.ofReal_comp.const_add (u : ℂ)).mul_const Complex.I
    simpa only [mul_assoc] using h1.cexp
  have hA := hrd_d.ofReal_comp.mul hE_d
  have hB : HasDerivAt
      (fun s : ℝ => (Work.RPB.B5.rd σ : ℂ) *
        Complex.exp (((s : ℂ) + (Work.RPB.B5.phc δ k σ : ℂ)) * Complex.I))
      ((Work.RPB.B5.rd σ : ℂ) *
        (Complex.exp (((u : ℂ) + (Work.RPB.B5.phc δ k σ : ℂ)) * Complex.I) * Complex.I)) u := by
    have h1 : HasDerivAt (fun s : ℝ => ((s : ℂ) + (Work.RPB.B5.phc δ k σ : ℂ)) * Complex.I)
        ((1 : ℂ) * Complex.I) u :=
      (((hasDerivAt_id u).ofReal_comp).add_const ((Work.RPB.B5.phc δ k σ : ℝ) : ℂ)).mul_const
        Complex.I
    have h3 : HasDerivAt (fun s : ℝ => ((s : ℂ) + (Work.RPB.B5.phc δ k σ : ℂ)) * Complex.I)
        Complex.I u := by simpa using h1
    have h4 : HasDerivAt
        (fun s : ℝ => Complex.exp (((s : ℂ) + (Work.RPB.B5.phc δ k σ : ℂ)) * Complex.I))
        (Complex.exp (((u : ℂ) + (Work.RPB.B5.phc δ k σ : ℂ)) * Complex.I) * Complex.I) u := by
      simpa using h3.cexp
    exact h4.const_mul ((Work.RPB.B5.rd σ : ℂ))
  show Work.RPV.ωC
      (deriv (((fun y : ℝ => ((Work.RPB.B5.rd y : ℝ) : ℂ)) *
          fun s : ℝ => Complex.exp (((u : ℂ) + (Work.RPB.B5.phc δ k s : ℂ)) * Complex.I))) σ)
      (deriv (fun s : ℝ => (Work.RPB.B5.rd σ : ℂ) *
        Complex.exp (((s : ℂ) + (Work.RPB.B5.phc δ k σ : ℂ)) * Complex.I)) u) = 1
  rw [hA.deriv, hB.deriv]
  set q : ℝ := deriv (fun s : ℝ => Work.RPB.B5.phc δ k s) σ
  set E : ℂ := Complex.exp (((u : ℂ) + (Work.RPB.B5.phc δ k σ : ℂ)) * Complex.I)
  have h2 : (Work.RPB.B5.rd σ : ℂ) * (E * (q : ℂ) * Complex.I)
      = ((Work.RPB.B5.rd σ * q : ℝ) : ℂ) * (E * Complex.I) := by
    rw [Complex.ofReal_mul]; ring
  rw [h2, kcf_omegaC_add_left, kcf_omegaC_smul_mul, kcf_omegaC_smul_mul, Work.RPV.ωC_self, mul_zero,
    add_zero, Work.RPV.ωC_mul_I]
  have hEnorm : ‖E‖ = 1 := by
    rw [show E = Complex.exp ((((u + Work.RPB.B5.phc δ k σ : ℝ)) : ℂ) * Complex.I) from by
      rw [Complex.ofReal_add]]
    exact Complex.norm_exp_ofReal_mul_I (u + Work.RPB.B5.phc δ k σ)
  rw [hEnorm, one_pow, mul_one]
  exact one_div_mul_cancel hrd_ne

/-! ## The far end of the collar -/

/-- For `σ ≥ 2δ` (and `τ ∈ [0,1]`) the collar curve is the exact circle of radius `√(2+2σ)`. -/
theorem kcf_kgam_far (CI : Work.RPV.CurveIsotopy) (W : ℝ → ℝ → ℝ → Work.RPV.PS)
    (ρh : ℝ → ℝ → ℝ → ℝ) {δ : ℝ} (hδ : 0 < δ) (k : ℤ) {τ : ℝ} (hτ : τ ∈ Set.Icc (0 : ℝ) 1)
    {σ : ℝ} (hσ : 2 * δ ≤ σ) (t : ℝ) :
    Work.RPB.B5.kgam CI W ρh δ k τ σ t
      = (Real.sqrt (2 + 2 * σ) : ℂ) * Complex.exp ((t - Real.pi / 2) * Complex.I) := by
  have h1 : Work.RPB.B5.kg CI W ρh δ k τ σ = 1 :=
    ksb_kg_far CI W ρh hδ k hτ (by linarith)
  have h2 : Work.RPB.B5.kgam CI W ρh δ k τ σ t = Work.RPB.B5.kshape CI W ρh δ k τ σ t := by
    rw [ksb_kgam_apply, h1, ksb_kdiagM_one]
  rw [h2]
  exact ksb_kshape_far CI W ρh δ k hδ hσ

/-! ## The level point of the `τ = 0` slice lies in the zero section -/

/-- At `τ = 0`, on the target circle `ktarg δ k σ ·`, the level point of level `σ` and phase
`t + kphc δ k σ + π/2 + 2πk` lies in the zero section. -/
theorem kcf_levelPt_zero (δ : ℝ) (k : ℤ) {σ t : ℝ} (hσ : 0 ≤ σ) :
    (Work.RPV.levelPt (ktarg δ k σ t) σ
      (t + kphc δ k σ + Real.pi / 2 + 2 * Real.pi * (k : ℝ))).2 = 0 := by
  set a : ℝ := t + kphc δ k σ + Real.pi / 2 + 2 * Real.pi * (k : ℝ) with hadef
  set θ : ℝ := t + kphc δ k σ with hθdef
  have hθa : θ - a = -(Real.pi / 2 + 2 * Real.pi * (k : ℝ)) := by rw [hadef, hθdef]; ring
  have hu : ktarg δ k σ t = (krd σ : ℂ) * Complex.exp ((θ : ℂ) * Complex.I) := by
    rw [hθdef]
    unfold ktarg
    rw [← Complex.ofReal_add]
  have hnorm : ‖ktarg δ k σ t‖ ^ 2 = 2 + 2 * σ := by
    rw [hu, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one,
      show ‖(krd σ : ℂ)‖ ^ 2 = (krd σ) ^ 2 by rw [Complex.sq_norm, Complex.normSq_ofReal, sq]]
    exact ksb_krd_sq σ (by linarith)
  have hn : ‖ktarg δ k σ t‖ ^ 2 / 2 - σ - 1 = 0 := by rw [hnorm]; ring
  have hr : (Complex.exp (-(a : ℂ) * Complex.I) * ktarg δ k σ t).re = 0 := by
    rw [hu, kcf_exp_mul_re (krd σ) θ a, hθa, kcf_exp_neg k]
    simp
  show ((Complex.exp (-(a : ℂ) * Complex.I) * ktarg δ k σ t).re,
        ‖ktarg δ k σ t‖ ^ 2 / 2 - σ - 1) = 0
  rw [hr, hn]
  rfl

/-! ## The theorem -/

theorem kappa_collar_far_tau0 (CI : Work.RPV.CurveIsotopy) (a : ℝ → ℝ → ℝ → ℝ)
    (ha : Work.RPB.IsChordPhase CI.c a)
    (ρ₀ : ℝ) (hρ₀ : 0 < ρ₀) (W : ℝ → ℝ → ℝ → Work.RPV.PS) (ρh : ℝ → ℝ → ℝ → ℝ)
    (κ : ℝ) (hκ : 0 < κ)
    (hW : ContDiffOn ℝ 12 (fun z : ℝ × (ℝ × ℝ) => W z.1 z.2.1 z.2.2)
      (Set.Icc (0 : ℝ) 1 ×ˢ Set.univ ×ˢ Set.Ioo (-ρ₀) ρ₀))
    (hWchord : ∀ τ ∈ Set.Icc (0 : ℝ) 1, ∀ t : ℝ, ∀ r ∈ Set.Ioc (0 : ℝ) (Real.pi / 2),
      W τ t (r ^ 2) = Work.RPB.chordSurf CI.c a τ t r)
    (hWper : ∀ τ t ρ, W τ (t + 2 * Real.pi) ρ = Work.RPV.Tk 1 (W τ t ρ))
    (hρh : ContDiffOn ℝ 12 (fun z : ℝ × (ℝ × ℝ) => ρh z.1 z.2.1 z.2.2)
      (Set.Icc (0 : ℝ) 1 ×ˢ Set.univ ×ˢ Set.Ioo (-κ) κ))
    (hρh0 : ∀ τ ∈ Set.Icc (0 : ℝ) 1, ∀ t : ℝ, ρh τ t 0 = 0)
    (hρhv : ∀ τ ∈ Set.Icc (0 : ℝ) 1, ∀ t : ℝ, ∀ σ ∈ Set.Ioo (-κ) κ,
      ρh τ t σ ∈ Set.Ioo (-ρ₀) ρ₀)
    (hρhl : ∀ τ ∈ Set.Icc (0 : ℝ) 1, ∀ t : ℝ, ∀ σ ∈ Set.Ioo (-κ) κ,
      Work.RPV.K0 (W τ t (ρh τ t σ)) + 1 = -σ)
    (hρhper : ∀ τ t σ, ρh τ (t + 2 * Real.pi) σ = ρh τ t σ)
    (k : ℤ) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ δ₀ ≤ κ ∧
      ∀ δ ∈ Set.Ioo (0 : ℝ) δ₀,
        (∀ τ ∈ Set.Icc (0 : ℝ) 1, ∀ σ : ℝ, 2 * δ ≤ σ → ∀ t : ℝ,
          Work.RPB.B5.kgam CI W ρh δ k τ σ t
              = (Real.sqrt (2 + 2 * σ) : ℂ) * Complex.exp ((t - Real.pi / 2) * Complex.I) ∧
          Work.RPB.B5.kac CI W ρh δ k τ σ t = t) ∧
        (∀ σ : ℝ, 0 ≤ σ → ∀ t : ℝ,
          (Work.RPV.levelPt (Work.RPB.B5.kgam CI W ρh δ k 0 σ t) σ
            (Work.RPB.B5.kac CI W ρh δ k 0 σ t)).2 = 0) := by
  -- the `τ = 0` chart identity for small negative levels, and the threshold `δ₁ ≤ κ` for it
  obtain ⟨k', _hk', δ₁, hδ₁pos, hδ₁κ, hcirc₁, _, _⟩ :=
    kappa_tau0 CI a ha ρ₀ hρ₀ W ρh κ hκ hW hWchord hρh hρh0 hρhv hρhl
  refine ⟨min δ₁ 1, lt_min hδ₁pos one_pos, le_trans (min_le_left _ _) hδ₁κ, ?_⟩
  intro δ hδ
  obtain ⟨hδpos, hδlt⟩ := hδ
  have hδδ₁ : δ < δ₁ := lt_of_lt_of_le hδlt (min_le_left _ _)
  have hδ1 : δ < 1 := lt_of_lt_of_le hδlt (min_le_right _ _)
  -- the chart identity on `(-δ, 0)`
  have hcirc : ∀ σ ∈ Set.Ioo (-δ) 0, ∀ u : ℝ,
      Work.RPV.uproj (W 0 u (ρh 0 u σ))
        = (Real.sqrt (2 + 2 * σ) : ℂ) * Complex.exp (u * Complex.I) :=
    fun σ hσ u => (hcirc₁ u σ ⟨by linarith [hσ.1, hδδ₁], hσ.2⟩).1
  -- the three inputs of the `τ = 0` computation
  have hsl := kcf_tau0_slice CI W ρh hδpos hδ1.le k hcirc
  have hflux := kcf_flux_ktarg_aux δ k
  have hkac0 := kcf_kac_tau0 CI W ρh hδpos k hsl hflux
  constructor
  · -- the far end: the exact circle and the phase `t`
    intro τ hτ σ hσ t
    exact ⟨kcf_kgam_far CI W ρh hδpos k hτ hσ t, kcf_kac_far CI W ρh hδpos k τ hτ σ hσ t⟩
  · -- the `τ = 0` slice lies in the zero section
    intro σ hσ t
    rw [hsl σ (by linarith) t, hkac0 σ hσ t]
    exact kcf_levelPt_zero δ k hσ

end Work.RPB.B5
