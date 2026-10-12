import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixB1.WindowedD1
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB1.WinPair.Defs` — the windowed pairing chain, definitions

Target of this little chapter: `Work.BoseFixB1.winPairForm_eq_pairSum`, the general-window
pairing identity

  `winPairForm s h χ Ψ = (2π)^{-3} ∫_q pairW (wScaled s (g₀ v h)) q · ((s³)^{-1} winPairR s χ Ψ q)`.

The corpus's chain (`Submission.Work.SmallBoxD1Integral.q4PairWord_eq_re_pairSum` and its
dependencies) proves this for the *single* window `χ = chiScale s`, which is **supported inside
the box** `acube s`.  For a general smooth window that support property fails, and the corpus's
route breaks at exactly one place: the relative-coordinate density is then only the
**box-restricted** density

  `winDens χ s Φ i j u = ∫_z χ_B(z+u)·χ_B(z)·Q_{ij}(z+u,z) dz`,   `χ_B := χ·1_{acube s}`,

which is *not* smooth (moving-domain kinks), so the target's `q`-integrand needs the decay
estimate `|𝓕 (winDens) (q)| ≤ C ∏ᵢ (1+|qᵢ|)^{-2}` (`WinPair/Decay`) for its integrability.

## Contents

* `winChi s χ` — the box-restricted window `χ·1_{acube s}`;
* `winModeC s χ p` — the mean-free complex windowed mode `χ e^{-i⟪p,·⟫} − s^{-3}∫_{acube s}`;
  its real and imaginary parts are exactly `WindowedD1.winModeRe s χ p` / `winModeIm s χ p`
  (`winModeC_re` / `winModeC_im`), which ties the target's `winPairR` to the corpus's
  `pairSlot`/`pairMean` machinery;
* `winDens s χ Φ i j`, `winDensSum s χ Φ` — the box-restricted pair density of the relative
  coordinate, per pair and summed over `pairSet`.
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped Topology Real BigOperators ENNReal

namespace Work.BoseFixB1

open _root_.BoseGases Submission.BoseGases

local notation "E3" => EuclideanSpace ℝ (Fin 3)

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## 0 Elementary complex helpers -/

/-- `e^{-iθ} = cos θ − i sin θ`. -/
lemma exp_neg_I_eq (θ : ℝ) :
    Complex.exp (-(Complex.I * (θ : ℂ)))
      = (Real.cos θ : ℂ) - Complex.I * (Real.sin θ : ℂ) := by
  have h : -(Complex.I * (θ : ℂ)) = ((-θ : ℝ) : ℂ) * Complex.I := by push_cast; ring
  rw [h, Complex.exp_ofReal_mul_I]
  simp [Real.cos_neg, Real.sin_neg]
  ring

lemma exp_neg_I_re (θ : ℝ) : (Complex.exp (-(Complex.I * (θ : ℂ)))).re = Real.cos θ := by
  have h : -(Complex.I * (θ : ℂ)) = ((-θ : ℝ) : ℂ) * Complex.I := by push_cast; ring
  rw [h, Complex.exp_ofReal_mul_I]
  simp [Complex.cos_ofReal_re, Complex.sin_ofReal_re, Real.cos_neg]

lemma exp_neg_I_im (θ : ℝ) : (Complex.exp (-(Complex.I * (θ : ℂ)))).im = - Real.sin θ := by
  have h : -(Complex.I * (θ : ℂ)) = ((-θ : ℝ) : ℂ) * Complex.I := by push_cast; ring
  rw [h, Complex.exp_ofReal_mul_I]
  simp [Complex.cos_ofReal_re, Complex.sin_ofReal_re, Real.sin_neg]

/-- `conj e^{-iθ} = e^{iθ} = e^{-i(-θ)}`. -/
lemma conj_exp_neg_I (θ : ℝ) :
    (starRingEnd ℂ) (Complex.exp (-(Complex.I * (θ : ℂ))))
      = Complex.exp (-(Complex.I * ((-θ : ℝ) : ℂ))) := by
  rw [← Complex.exp_conj]
  congr 1
  rw [map_neg, map_mul, Complex.conj_I, Complex.conj_ofReal]
  push_cast
  ring

lemma ofReal_mul_re (r : ℝ) (z : ℂ) : ((r : ℂ) * z).re = r * z.re := by
  rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]

lemma ofReal_mul_im (r : ℝ) (z : ℂ) : ((r : ℂ) * z).im = r * z.im := by
  rw [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero]

/-! ## 1 The box-restricted window -/

/-- The box-restricted window `χ_B := χ·1_{acube s}`.

Every object of the windowed pairing chain only ever sees the window *on the box*
(`winPairForm` through `χ(x_i)χ(x_j)` with `x ∈ abox`, `winPairR` through the modes' box
integrals and pointwise values on `abox`), but the *domain* of the relative-coordinate integral
sees `χ` at the box boundary; restricting the window to the box makes that domain restriction
automatic, which is what allows the corpus's substitution argument (`pairWord_subst`) to be
replayed verbatim. -/
noncomputable def winChi (s : ℝ) (χ : E3 → ℝ) : E3 → ℝ := Set.indicator (acube s) χ

lemma winChi_of_mem {s : ℝ} {χ : E3 → ℝ} {z : E3} (hz : z ∈ acube s) :
    winChi s χ z = χ z := Set.indicator_of_mem hz χ

lemma winChi_eq_zero {s : ℝ} {χ : E3 → ℝ} {z : E3} (hz : z ∉ acube s) :
    winChi s χ z = 0 := Set.indicator_of_notMem hz χ

lemma abs_winChi_le {s : ℝ} {χ : E3 → ℝ} {C : ℝ} (hC : ∀ z, |χ z| ≤ C) (z : E3) :
    |winChi s χ z| ≤ C := by
  by_cases hz : z ∈ acube s
  · rw [winChi_of_mem hz]; exact hC z
  · rw [winChi_eq_zero hz, abs_zero]; exact le_trans (abs_nonneg (χ 0)) (hC 0)

lemma winChi_support {s : ℝ} {χ : E3 → ℝ} {z : E3} (hz : winChi s χ z ≠ 0) :
    z ∈ acube s := by
  by_contra h
  exact hz (winChi_eq_zero h)

lemma measurable_winChi {s : ℝ} {χ : E3 → ℝ} (hχ : Measurable χ) :
    Measurable (winChi s χ) := hχ.indicator (acube_measurable s)

/-! ## 2 The mean-free complex windowed mode -/

/-- The `χ`-mean `∫_{acube s}χ(y)e^{-i⟪p,y⟫}dy` of the windowed exponential. -/
noncomputable def winChat (s : ℝ) (χ : E3 → ℝ) (p : E3) : ℂ :=
  ∫ w in acube s, (χ w : ℂ) * Complex.exp (-(Complex.I * ((inner ℝ p w : ℝ) : ℂ)))

/-- The mean-free complex windowed mode
`winModeC s χ p z = χ(z)e^{-i⟪p,z⟫} − s^{-3}∫_{acube s}χ(w)e^{-i⟪p,w⟫}dw`
(the generalisation of `SmallBoxPairMode.qMode s p` from `χ = chiScale s`). -/
noncomputable def winModeC (s : ℝ) (χ : E3 → ℝ) (p : E3) : E3 → ℂ :=
  fun z => (χ z : ℂ) * Complex.exp (-(Complex.I * ((inner ℝ p z : ℝ) : ℂ)))
    - (((s ^ 3)⁻¹ : ℝ) : ℂ) * winChat s χ p

lemma winModeC_apply (s : ℝ) (χ : E3 → ℝ) (p z : E3) :
    winModeC s χ p z = (χ z : ℂ) * Complex.exp (-(Complex.I * ((inner ℝ p z : ℝ) : ℂ)))
      - (((s ^ 3)⁻¹ : ℝ) : ℂ) *
          ∫ w in acube s, (χ w : ℂ) * Complex.exp (-(Complex.I * ((inner ℝ p w : ℝ) : ℂ))) := by
  rw [winModeC, winChat]

/-- The `winChat` integrand is continuous on the compact box (integrability helper). -/
lemma integrableOn_winChat_integrand {s : ℝ} (hs : 0 < s) {χ : E3 → ℝ} (hχ : Continuous χ)
    (p : E3) :
    IntegrableOn (fun w : E3 =>
      (χ w : ℂ) * Complex.exp (-(Complex.I * ((inner ℝ p w : ℝ) : ℂ)))) (acube s) volume :=
  ContinuousOn.integrableOn_compact (acube_compact hs)
    ((Complex.continuous_ofReal.comp hχ |>.mul
      (Complex.continuous_exp.comp (Continuous.neg (Continuous.mul continuous_const
        (Complex.continuous_ofReal.comp
          (continuous_inner.comp (continuous_const.prodMk continuous_id))))))).continuousOn)

/-- The complex mode's real part in terms of `winChat`. -/
lemma winModeC_re_apply {s : ℝ} {χ : E3 → ℝ} (p z : E3) :
    (winModeC s χ p z).re
      = χ z * Real.cos (inner ℝ p z) - (s ^ 3)⁻¹ * (winChat s χ p).re := by
  rw [winModeC_apply, Complex.sub_re, ofReal_mul_re, exp_neg_I_re, ofReal_mul_re, winChat]

/-- The complex mode's imaginary part in terms of `winChat`. -/
lemma winModeC_im_apply {s : ℝ} {χ : E3 → ℝ} (p z : E3) :
    (winModeC s χ p z).im
      = - (χ z * Real.sin (inner ℝ p z)) - (s ^ 3)⁻¹ * (winChat s χ p).im := by
  rw [winModeC_apply, Complex.sub_im, ofReal_mul_im, exp_neg_I_im, ofReal_mul_im, winChat]
  ring

/-- `winChat`'s real part. -/
lemma winChat_re {s : ℝ} (hs : 0 < s) {χ : E3 → ℝ} (hχ : Continuous χ) (p : E3) :
    (winChat s χ p).re = ∫ w in acube s, χ w * Real.cos (inner ℝ p w) := by
  have hint := integrableOn_winChat_integrand hs hχ p
  rw [winChat]
  have h1 : (∫ w in acube s,
        ((χ w : ℂ) * Complex.exp (-(Complex.I * ((inner ℝ p w : ℝ) : ℂ))))).re
      = ∫ w in acube s,
          ((χ w : ℂ) * Complex.exp (-(Complex.I * ((inner ℝ p w : ℝ) : ℂ)))).re :=
    (Complex.reCLM.integral_comp_comm (μ := (volume : Measure E3).restrict (acube s))
      (φ := fun w : E3 => (χ w : ℂ) *
        Complex.exp (-(Complex.I * ((inner ℝ p w : ℝ) : ℂ)))) hint).symm
  rw [h1]
  refine setIntegral_congr_fun (acube_measurable s) fun w _ => ?_
  rw [ofReal_mul_re, exp_neg_I_re]

/-- `winChat`'s imaginary part. -/
lemma winChat_im {s : ℝ} (hs : 0 < s) {χ : E3 → ℝ} (hχ : Continuous χ) (p : E3) :
    (winChat s χ p).im = - ∫ w in acube s, χ w * Real.sin (inner ℝ p w) := by
  have hint := integrableOn_winChat_integrand hs hχ p
  rw [winChat]
  have h1 : (∫ w in acube s,
        ((χ w : ℂ) * Complex.exp (-(Complex.I * ((inner ℝ p w : ℝ) : ℂ))))).im
      = ∫ w in acube s,
          ((χ w : ℂ) * Complex.exp (-(Complex.I * ((inner ℝ p w : ℝ) : ℂ)))).im :=
    (Complex.imCLM.integral_comp_comm (μ := (volume : Measure E3).restrict (acube s))
      (φ := fun w : E3 => (χ w : ℂ) *
        Complex.exp (-(Complex.I * ((inner ℝ p w : ℝ) : ℂ)))) hint).symm
  rw [h1]
  rw [show (∫ w in acube s,
        ((χ w : ℂ) * Complex.exp (-(Complex.I * ((inner ℝ p w : ℝ) : ℂ)))).im)
      = ∫ w in acube s, -(χ w * Real.sin (inner ℝ p w)) from
    setIntegral_congr_fun (acube_measurable s) fun w _ => by
      rw [ofReal_mul_im, exp_neg_I_im]
      ring]
  rw [MeasureTheory.integral_neg]

/-- **Real part of the complex windowed mode is `winModeRe`.** -/
lemma winModeC_re (s : ℝ) (χ : E3 → ℝ) (hs : 0 < s) (hχ : Continuous χ) (p : E3) :
    (fun z => (winModeC s χ p z).re) = winModeRe s χ p := by
  funext z
  rw [winModeC_re_apply, winChat_re hs hχ, winModeRe]

/-- **Imaginary part of the complex windowed mode is `winModeIm`.** -/
lemma winModeC_im (s : ℝ) (χ : E3 → ℝ) (hs : 0 < s) (hχ : Continuous χ) (p : E3) :
    (fun z => (winModeC s χ p z).im) = winModeIm s χ p := by
  funext z
  rw [winModeC_im_apply, winChat_im hs hχ, winModeIm]
  ring_nf

/-- The complex mode is the real/imaginary assembly of `winModeRe`/`winModeIm`. -/
lemma winModeC_eq_re_add_im (s : ℝ) (χ : E3 → ℝ) (hs : 0 < s) (hχ : Continuous χ) (p z : E3) :
    winModeC s χ p z
      = ((winModeRe s χ p z : ℝ) : ℂ) + Complex.I * ((winModeIm s χ p z : ℝ) : ℂ) := by
  have h1 := congrFun (winModeC_re s χ hs hχ p) z
  have h2 := congrFun (winModeC_im s χ hs hχ p) z
  have h3 := Complex.re_add_im (winModeC s χ p z)
  rw [h1, h2] at h3
  rw [← h3]
  ring

/-- `winModeC` is continuous for a continuous window (the box mean is a constant). -/
lemma continuous_winModeC {s : ℝ} {χ : E3 → ℝ} (hχ : Continuous χ) (p : E3) :
    Continuous (winModeC s χ p) := by
  rw [show winModeC s χ p = fun z : E3 => (χ z : ℂ) *
      Complex.exp (-(Complex.I * ((inner ℝ p z : ℝ) : ℂ)))
        - (((s ^ 3)⁻¹ : ℝ) : ℂ) * winChat s χ p from
    funext fun z => winModeC_apply s χ p z]
  refine Continuous.sub ?_ continuous_const
  exact (Complex.continuous_ofReal.comp hχ).mul
    (Complex.continuous_exp.comp (Continuous.neg (Continuous.mul continuous_const
      (Complex.continuous_ofReal.comp
        (continuous_inner.comp (continuous_const.prodMk continuous_id))))))

/-- The windowed mode is mean-free over the box. -/
lemma winModeC_mean_zero {s : ℝ} (hs : 0 < s) {χ : E3 → ℝ} (hχ : Continuous χ) (p : E3) :
    ∫ z in acube s, winModeC s χ p z = 0 := by
  have hm : Integrable (fun z : E3 =>
      (χ z : ℂ) * Complex.exp (-(Complex.I * ((inner ℝ p z : ℝ) : ℂ))))
      ((volume : Measure E3).restrict (acube s)) :=
    integrableOn_winChat_integrand hs hχ p
  haveI : IsFiniteMeasure ((volume : Measure E3).restrict (acube s)) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact acube_lt_top s hs.le⟩
  have hc : Integrable (fun _ : E3 => (((s ^ 3)⁻¹ : ℝ) : ℂ) * winChat s χ p)
      ((volume : Measure E3).restrict (acube s)) := integrable_const _
  rw [show winModeC s χ p = fun z : E3 => (χ z : ℂ) *
      Complex.exp (-(Complex.I * ((inner ℝ p z : ℝ) : ℂ)))
        - (((s ^ 3)⁻¹ : ℝ) : ℂ) * winChat s χ p from
    funext fun z => winModeC_apply s χ p z]
  rw [MeasureTheory.integral_sub hm hc]
  have h2 : (∫ z in acube s, (χ z : ℂ) * Complex.exp (-(Complex.I * ((inner ℝ p z : ℝ) : ℂ))))
      = winChat s χ p := by rw [winChat]
  rw [MeasureTheory.integral_const_mul, h2]
  have hvol : (∫ (a : E3) in acube s, winChat s χ p) = (s ^ 3 : ℝ) • winChat s χ p := by
    rw [MeasureTheory.integral_const, real_volume_acube s hs.le]
  rw [hvol, Complex.real_smul, Complex.ofReal_pow]
  have h3 : (((s ^ 3)⁻¹ : ℝ) : ℂ) * ((s : ℂ) ^ 3) = 1 := by
    rw [Complex.ofReal_inv, Complex.ofReal_pow]
    exact inv_mul_cancel₀ (pow_ne_zero 3 (Complex.ofReal_ne_zero.mpr (ne_of_gt hs)))
  rw [← mul_assoc, h3, one_mul, sub_self]

/-- The exponential of the reflected momentum: `e^{−i⟨−p,y⟩} = \\overline{e^{−i⟨p,y⟩}}`. -/
lemma exp_neg_inner_neg (p y : E3) :
    Complex.exp (-(Complex.I * ((inner ℝ (-p) y : ℝ) : ℂ)))
      = star (Complex.exp (-(Complex.I * ((inner ℝ p y : ℝ) : ℂ)))) := by
  rw [Complex.star_def, ← Complex.exp_conj]
  congr 1
  rw [map_neg, map_mul, Complex.conj_ofReal, Complex.conj_I]
  rw [show inner ℝ (-p) y = - inner ℝ p y from inner_neg_left p y]
  push_cast
  ring

/-- `winChat s χ (−p) = \\overline{winChat s χ p}`. -/
lemma winChat_neg (s : ℝ) (χ : E3 → ℝ) (p : E3) :
    winChat s χ (-p) = star (winChat s χ p) := by
  have hpt : (fun y : E3 => (χ y : ℂ) * Complex.exp (-(Complex.I * ((inner ℝ (-p) y : ℝ) : ℂ))))
      = fun y : E3 => star ((χ y : ℂ) *
          Complex.exp (-(Complex.I * ((inner ℝ p y : ℝ) : ℂ)))) := by
    funext y
    rw [exp_neg_inner_neg, star_mul, Complex.star_def, Complex.conj_ofReal]
    ring
  rw [winChat, winChat, hpt, Complex.star_def, integral_conj]

/-- **Conjugation symmetry: the `−p` mode is the complex conjugate of the `p` mode.** -/
lemma winModeC_neg_conj (s : ℝ) (χ : E3 → ℝ) (p z : E3) :
    winModeC s χ (-p) z = star (winModeC s χ p z) := by
  have hc : winChat s χ (-p) = star (winChat s χ p) := winChat_neg s χ p
  set k : ℂ := (((s ^ 3)⁻¹ : ℝ) : ℂ) with hkdef
  have hku : ∀ w : ℂ, star (k * w) = k * star w := fun w => by
    rw [star_mul, show star k = k from by rw [hkdef, Complex.star_def, Complex.conj_ofReal]]
    ring
  have hχ : ∀ w : ℂ, star ((χ z : ℂ) * w) = (χ z : ℂ) * star w := fun w => by
    rw [star_mul, show star ((χ z : ℂ)) = (χ z : ℂ) from by
      rw [Complex.star_def, Complex.conj_ofReal]]
    ring
  have h1 : winModeC s χ p z
      = (χ z : ℂ) * Complex.exp (-(Complex.I * ((inner ℝ p z : ℝ) : ℂ))) - k * winChat s χ p := by
    rw [winModeC_apply, winChat, ← hkdef]
  have h2 : winModeC s χ (-p) z
      = (χ z : ℂ) * Complex.exp (-(Complex.I * ((inner ℝ (-p) z : ℝ) : ℂ)))
        - k * winChat s χ (-p) := by
    rw [winModeC_apply, winChat, ← hkdef]
  rw [h1, h2, hc, exp_neg_inner_neg, star_sub, hχ, hku]

/-- `winModeC` at the momentum `-p` in terms of the real/imaginary parts at `p`. -/
lemma winModeC_neg (s : ℝ) (χ : E3 → ℝ) (hs : 0 < s) (hχ : Continuous χ) (p z : E3) :
    winModeC s χ (-p) z
      = ((winModeRe s χ p z : ℝ) : ℂ) - Complex.I * ((winModeIm s χ p z : ℝ) : ℂ) := by
  rw [winModeC_neg_conj, winModeC_eq_re_add_im s χ hs hχ, Complex.star_def, map_add, map_mul,
    Complex.conj_I, Complex.conj_ofReal, Complex.conj_ofReal]
  ring

/-! ## 3 The box-restricted pair density -/

/-- The (box-restricted) pair density of the relative coordinate `u = x_i − x_j`:
`∫_z χ_B(z+u)χ_B(z)·Q_{ij}(z+u,z)dz` with `χ_B = χ·1_{acube s}` and `Q_{ij}` the peeled pair
fibre.  The restriction to the box is automatic through `χ_B`. -/
noncomputable def winDens {N : ℕ} (s : ℝ) (χ : E3 → ℝ) (Φ : X (N + 2) → ℝ)
    (i j : Fin (N + 2)) (u : E3) : ℝ :=
  ∫ z, winChi s χ (z + u) * winChi s χ z * pairFibreFun s Φ i j (z + u) z

/-- The sum of the pair densities over `pairSet`. -/
noncomputable def winDensSum {N : ℕ} (s : ℝ) (χ : E3 → ℝ) (Φ : X (N + 2) → ℝ) : E3 → ℝ :=
  fun u => ∑ q ∈ pairSet (N + 2), winDens s χ Φ q.1 q.2 u

end Work.BoseFixB1
