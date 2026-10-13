/-
Copyright: work module for the Elgindi finite-time singularity project.

# `FTS_EllLimOK.Decay.DecayTools` — slices, Lipschitz bounds and localised integral bounds

The decay lemma `Work.FTS_EllLimOK.Decay.decay_of_hkMem0_jetBound` proves that an `ℋ⁰`-function
`Ψ` whose jet is bounded on the open quadrant tends to `0` along every `z → +∞` at an interior
angle `θ ∈ (0,π/2)`.  The argument is a localisation one: a value `|Ψ z θ| ≥ ε` at a large `z`
forces the *weighted* `L²`-energy `∫_θ HkIntegrand α 0 Ψ` to stay `≥ c > 0` on the whole window
`[z, z+1]`, contradicting the finiteness of the outer `z`-integral.

This module collects the elementary ingredients of that argument, in reusable form:

* the collapse of the `k = 0` integrand, `HkIntegrand_zero_eq`, and the lower bound
  `1 ≤ w(z)/sin(2θ)^{η/2}` on the domain (`one_le_w_div_sin`);
* the identification of the slice derivatives with `pz`/`pth` for a function that is `C²` at a
  point (`deriv_slice_z_of_contDiffAt`, `deriv_slice_th_of_contDiffAt`);
* the mean-value bounds `abs_slice_z_sub_le` (`|Ψ z' θ - Ψ z θ| ≤ (C/z)(z'-z)` from
  `|D_zΨ| ≤ C`) and `abs_slice_th_sub_le` (`|Ψ z θ' - Ψ z θ| ≤ (C/s)|θ' - θ|` on a `θ`-interval
  where `sin(2θ) ≥ s`, from `|D_θΨ| ≤ C`);
* the two "integral versus local lower bound" lemmas `integral_Ioi_ge_of_lower_bound` and
  `thetaIntegral_ge_of_lower_bound`.

Everything here is `sorry`-free.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Submission.Work.FTS_EllLimOK.BoxReg
import Submission.Work.Spaces.CurrySmooth
import Submission.Work.FTS.EllipticEst.OpenQDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS_EllLimOK.Decay

set_option autoImplicit false

/-! ## The `k = 0` angular integrand -/

/-- **The `k = 0` integrand is a single square.**  For `k = 0` the second (mixed) sum inside
`HkIntegrand` is empty (its condition is `1 ≤ i` with `i = 0`), so only the `D_z`-slot survives. -/
theorem HkIntegrand_zero_eq (α : ℝ) (Ψ : ℝ → ℝ → ℝ) (z θ : ℝ) :
    Work.Spaces.HkIntegrand α 0 Ψ z θ
      = (Ψ z θ * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 := by
  simp [Work.Spaces.HkIntegrand]

/-- **The weight factor is `≥ 1` on `z ≥ 1`.**  `w z = (1+z)²/z² ≥ 1` for `z > 0` and
`sin(2θ)^{η/2} ≤ 1` for `θ ∈ (0,π/2)`, so their quotient is `≥ 1`. -/
theorem one_le_w_div_sin {z θ : ℝ} (hz : 1 ≤ z) (hθ : θ ∈ Set.Ioo (0 : ℝ) (π / 2)) :
    1 ≤ Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2) := by
  have hzpos : 0 < z := by linarith
  have h2θpos : 0 < 2 * θ := by linarith [hθ.1]
  have h2θlt : 2 * θ < Real.pi := by linarith [hθ.2]
  have hs : 0 < Real.sin (2 * θ) := Real.sin_pos_of_pos_of_lt_pi h2θpos h2θlt
  rw [one_le_div (Real.rpow_pos_of_pos hs _)]
  have h1 : (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2) ≤ 1 :=
    Real.rpow_le_one (le_of_lt hs) (Real.sin_le_one _)
      (by norm_num [Work.Spaces.eta])
  have h2 : 1 ≤ Work.Spaces.w z := by
    have hz2 : 0 < z ^ 2 := by positivity
    rw [Work.Spaces.w, one_le_div hz2]
    nlinarith
  linarith

/-! ## Slice derivatives at a `C²`-point -/

/-- The `z`-slice of a function that is jointly `C²` at `(z,θ)` has derivative `∂_z` there. -/
theorem deriv_slice_z_of_contDiffAt {G : ℝ → ℝ → ℝ} {z θ : ℝ}
    (h : ContDiffAt ℝ 2 (Function.uncurry G) (z, θ)) :
    deriv (fun z' => G z' θ) z = Work.Spaces.pz G z θ := by
  have hd : DifferentiableAt ℝ (Function.uncurry G) (z, θ) := h.differentiableAt (by norm_num)
  rw [show (fun z' => G z' θ) = fun z' => Function.uncurry G (z', θ) from rfl,
    Work.Spaces.deriv_slice_fst (Function.uncurry G) z θ hd, Work.Spaces.pz_eq_fderiv hd]

/-- The `θ`-slice of a function that is jointly `C²` at `(z,θ)` has derivative `∂_θ` there. -/
theorem deriv_slice_th_of_contDiffAt {G : ℝ → ℝ → ℝ} {z θ : ℝ}
    (h : ContDiffAt ℝ 2 (Function.uncurry G) (z, θ)) :
    deriv (fun θ' => G z θ') θ = Work.Spaces.pth G z θ := by
  have hd : DifferentiableAt ℝ (Function.uncurry G) (z, θ) := h.differentiableAt (by norm_num)
  rw [show (fun θ' => G z θ') = fun θ' => Function.uncurry G (z, θ') from rfl,
    Work.Spaces.deriv_slice_snd (Function.uncurry G) z θ hd, Work.Spaces.pth_eq_fderiv hd]

/-! ## The two mean-value bounds -/

/-- **The `z`-Lipschitz bound.**  If `|D_zΨ| = |z ∂_zΨ| ≤ C` with `C > 0` on the open quadrant,
then for `0 < z ≤ z'` and `θ ∈ (0,π/2)`,
`|Ψ z' θ - Ψ z θ| ≤ (C/z)·(z' - z)`.

Indeed `|∂_zΨ t θ| ≤ C/t ≤ C/z` for `t ∈ [z,z']`, and the mean value theorem on the convex set
`[z,z']` gives the claim (the slices are differentiable by `BoxReg`). -/
theorem abs_slice_z_sub_le {Ψ : ℝ → ℝ → ℝ} (hbox : BoxReg Ψ) {C z z' θ : ℝ}
    (hDz : ∀ z θ : ℝ, (z, θ) ∈ Work.FTS.EllipticEst.Q0 →
      |Work.Spaces.mixed 1 0 Ψ z θ| ≤ C)
    (hC : 0 < C) (hz : 0 < z) (hzz' : z ≤ z') (hθ : θ ∈ Set.Ioo (0 : ℝ) (π / 2)) :
    |Ψ z' θ - Ψ z θ| ≤ C / z * (z' - z) := by
  have hdiff : ∀ t ∈ Set.Icc z z', DifferentiableAt ℝ (fun t => Ψ t θ) t := by
    intro t ht
    have ht0 : 0 < t := lt_of_lt_of_le hz ht.1
    exact Work.Spaces.differentiableAt_curry_left
      ((hbox.contDiffAt ⟨Set.mem_Ioi.mpr ht0, hθ⟩).differentiableAt (by norm_num))
  have hbound : ∀ t ∈ Set.Icc z z', |deriv (fun t => Ψ t θ) t| ≤ C / z := by
    intro t ht
    have ht0 : 0 < t := lt_of_lt_of_le hz ht.1
    have h2θpos : 0 < 2 * θ := by linarith [hθ.1]
    have h2θlt : 2 * θ < Real.pi := by linarith [hθ.2]
    have hs : 0 < Real.sin (2 * θ) := Real.sin_pos_of_pos_of_lt_pi h2θpos h2θlt
    rw [deriv_slice_z_of_contDiffAt ((hbox.contDiffAt ⟨Set.mem_Ioi.mpr ht0, hθ⟩))]
    have hmix : Work.Spaces.mixed 1 0 Ψ t θ = t * Work.Spaces.pz Ψ t θ := rfl
    have hDz' := hDz t θ (Work.FTS.EllipticEst.mem_Q0.mpr ⟨ht0, hθ.1, hθ.2⟩)
    rw [hmix, abs_mul, abs_of_pos ht0] at hDz'
    have hpz : |Work.Spaces.pz Ψ t θ| ≤ C / t := by
      rw [le_div_iff₀ ht0]
      linarith
    have hCt : C / t ≤ C / z := div_le_div_of_nonneg_left (le_of_lt hC) hz ht.1
    linarith
  have h := Convex.norm_image_sub_le_of_norm_deriv_le (s := Set.Icc z z') (f := fun t => Ψ t θ)
    (C := C / z) hdiff hbound (convex_Icc z z') (left_mem_Icc.mpr hzz') (right_mem_Icc.mpr hzz')
  simpa [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hzz')] using h

/-- **The `θ`-Lipschitz bound.**  If `|D_θΨ| = |sin(2θ) ∂_θΨ| ≤ C` with `C > 0` on the open
quadrant and `sin(2θ) ≥ s > 0` on the interval `[a,b] ⊆ (0,π/2)`, then for `z > 0` and
`θ, θ' ∈ [a,b]`, `|Ψ z θ' - Ψ z θ| ≤ (C/s)·|θ' - θ|`. -/
theorem abs_slice_th_sub_le {Ψ : ℝ → ℝ → ℝ} (hbox : BoxReg Ψ) {C s a b z : ℝ}
    (hDth : ∀ z θ : ℝ, (z, θ) ∈ Work.FTS.EllipticEst.Q0 →
      |Work.Spaces.mixed 0 1 Ψ z θ| ≤ C)
    (hC : 0 < C) (hz : 0 < z) (ha : 0 < a) (hb : b < π / 2)
    (hs : ∀ θ ∈ Set.Icc a b, s ≤ Real.sin (2 * θ)) (hs0 : 0 < s)
    {θ θ' : ℝ} (hθ : θ ∈ Set.Icc a b) (hθ' : θ' ∈ Set.Icc a b) :
    |Ψ z θ' - Ψ z θ| ≤ C / s * |θ' - θ| := by
  have hab : a ≤ b := le_trans hθ.1 hθ.2
  have hdiff : ∀ t ∈ Set.Icc a b, DifferentiableAt ℝ (fun θ' => Ψ z θ') t := by
    intro t ht
    have ht0 : 0 < t := lt_of_lt_of_le ha ht.1
    have htlt : t < π / 2 := lt_of_le_of_lt ht.2 hb
    exact Work.Spaces.differentiableAt_curry_right
      ((hbox.contDiffAt ⟨Set.mem_Ioi.mpr hz, ⟨ht0, htlt⟩⟩).differentiableAt (by norm_num))
  have hbound : ∀ t ∈ Set.Icc a b, |deriv (fun θ' => Ψ z θ') t| ≤ C / s := by
    intro t ht
    have ht0 : 0 < t := lt_of_lt_of_le ha ht.1
    have htlt : t < π / 2 := lt_of_le_of_lt ht.2 hb
    have hsin : 0 < Real.sin (2 * t) :=
      Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
    rw [deriv_slice_th_of_contDiffAt (hbox.contDiffAt ⟨Set.mem_Ioi.mpr hz, ⟨ht0, htlt⟩⟩)]
    have hmix : Work.Spaces.mixed 0 1 Ψ z t = Real.sin (2 * t) * Work.Spaces.pth Ψ z t := rfl
    have hDth' := hDth z t (Work.FTS.EllipticEst.mem_Q0.mpr ⟨hz, ht0, htlt⟩)
    rw [hmix, abs_mul, abs_of_pos hsin] at hDth'
    have hpth : |Work.Spaces.pth Ψ z t| ≤ C / Real.sin (2 * t) := by
      rw [le_div_iff₀ hsin]
      linarith
    have hle : C / Real.sin (2 * t) ≤ C / s :=
      div_le_div_of_nonneg_left (le_of_lt hC) hs0 (hs t ht)
    linarith
  have h := Convex.norm_image_sub_le_of_norm_deriv_le (s := Set.Icc a b) (f := fun t => Ψ z t)
    (C := C / s) hdiff hbound (convex_Icc a b) hθ hθ'
  simpa [Real.norm_eq_abs] using h

/-! ## Localised lower bounds for the integrals -/

/-- **A local lower bound upgrades to a lower bound of the half-line integral.**  If `g ≥ 0`
everywhere, `g` is integrable on `(Z,∞)` and `g ≥ c` on the window `[z, z+1]` with `Z ≤ z`, then
`c ≤ ∫_{Z}^{∞} g`. -/
theorem integral_Ioi_ge_of_lower_bound {g : ℝ → ℝ} {Z z c : ℝ} (hz : Z ≤ z)
    (hgint : MeasureTheory.IntegrableOn g (Set.Ioi Z) volume)
    (hnonneg : ∀ t, 0 ≤ g t) (hlow : ∀ t ∈ Set.Icc z (z + 1), c ≤ g t) :
    c ≤ ∫ t in Set.Ioi Z, g t := by
  have hz1 : z ≤ z + 1 := by linarith
  have hsub : Set.Ioc z (z + 1) ⊆ Set.Ioi Z := fun t ht => lt_of_le_of_lt hz ht.1
  have hgIoc : MeasureTheory.IntegrableOn g (Set.Ioc z (z + 1)) := hgint.mono_set hsub
  have hgInt : IntervalIntegrable g volume z (z + 1) := by
    rw [intervalIntegrable_iff, Set.uIoc_of_le hz1]
    exact hgIoc
  have hmono : (∫ t in z..(z + 1), (fun _ : ℝ => c) t) ≤ ∫ t in z..(z + 1), g t :=
    intervalIntegral.integral_mono_on hz1 intervalIntegrable_const hgInt hlow
  have hconst : (∫ t in z..(z + 1), (fun _ : ℝ => c) t) = c := by
    rw [intervalIntegral.integral_const, smul_eq_mul]
    ring
  have htail : (∫ t in z..(z + 1), g t) ≤ ∫ t in Set.Ioi Z, g t := by
    rw [intervalIntegral.integral_of_le hz1]
    exact setIntegral_mono_set hgint (ae_of_all _ hnonneg) (ae_of_all _ hsub)
  linarith

/-- **A local lower bound upgrades to a lower bound of the angular integral.**  If `f ≥ 0` on
`Iθ`, `f` is integrable there and `f ≥ c` on `[a,b] ⊆ Iθ`, then `c·(b - a) ≤ ∫_{Iθ} f`. -/
theorem thetaIntegral_ge_of_lower_bound {f : ℝ → ℝ} {a b c : ℝ} (hab : a ≤ b)
    (hsub : Set.Ioc a b ⊆ Work.Spaces.Iθ) (hint : MeasureTheory.IntegrableOn f Work.Spaces.Iθ)
    (hnonneg : ∀ θ, 0 ≤ f θ) (hlow : ∀ θ ∈ Set.Icc a b, c ≤ f θ) :
    c * (b - a) ≤ ∫ θ in Work.Spaces.Iθ, f θ := by
  have hloc : MeasureTheory.IntegrableOn f (Set.Ioc a b) :=
    hint.mono_set (fun θ hθ => hsub hθ)
  have hInt : IntervalIntegrable f volume a b := by
    rw [intervalIntegrable_iff, Set.uIoc_of_le hab]
    exact hloc
  have hmono : (∫ θ in a..b, (fun _ : ℝ => c) θ) ≤ ∫ θ in a..b, f θ :=
    intervalIntegral.integral_mono_on hab intervalIntegrable_const hInt hlow
  have hconst : (∫ θ in a..b, (fun _ : ℝ => c) θ) = c * (b - a) := by
    rw [intervalIntegral.integral_const, smul_eq_mul]
    ring
  have htail : (∫ θ in a..b, f θ) ≤ ∫ θ in Work.Spaces.Iθ, f θ := by
    rw [intervalIntegral.integral_of_le hab]
    exact setIntegral_mono_set hint (ae_of_all _ hnonneg) (ae_of_all _ fun θ hθ => hsub hθ)
  linarith

end Work.FTS_EllLimOK.Decay
