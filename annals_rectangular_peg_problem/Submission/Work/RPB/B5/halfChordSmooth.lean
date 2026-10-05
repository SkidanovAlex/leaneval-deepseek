import Mathlib
import Submission.Work.RPB.Defs
import Submission.Work.RPA3.contDiff_param_intervalIntegral

/-!
# `B5.halfChordSmooth`: the half chord `(c(t+r) - c(t-r))/(2r)` extends smoothly across `r = 0`

For a curve family `c : ℝ → ℝ → ℂ` that is `C^∞` in `(τ,t)` and `2π`-periodic in `t`, the half
chord
`halfChord c τ t r = (c τ (t+r) - c τ (t-r)) / (2r)`
is smooth in `(τ,t,r)` for `r ≠ 0`, even and `2π`-periodic in `t`, and its limit as `r → 0` is
`c'(t)`.  The difference quotient is written `(c(t+r) - c(t-r))/(2r)`, so it is exactly the *even*
quotient; consequently `r ↦ halfChord c τ t r` has only even Taylor terms at `r = 0` and extends to a
smooth function of `(τ,t,r)` on all of `ℝ`.

The extension is realised here through the "average of the derivative" formula
`halfChord c τ t r = (1/2) ∫_0^1 (c'(t + s r) + c'(t - s r)) ds`
(substitute `u = s r` and integrate the derivative of `u ↦ c(t+u) - c(t-u)`), which is manifestly
smooth in `(τ,t,r)` once `(τ,t) ↦ c'(t)` is smooth — and the latter is the partial derivative of the
jointly smooth `c`, hence smooth by differentiation under the integral / `fderiv` regularity.

## Contents

* `pDeriv c τ t`: the partial derivative `∂c/∂t`, i.e. `c'(t)`, as a function of `(τ,t)`;
* `halfChordExt c τ t r`: the smooth extension `(1/2) ∫_0^1 (pDeriv c τ (t+sr) + pDeriv c τ (t-sr))`;
* the bridge `pDeriv_eq_deriv`;
* the chain rule `deriv_chordVec`;
* smoothness, evenness, `2π`-periodicity, the value at `r = 0` and the agreement with `halfChord`
  for `r ≠ 0` of the extension;
* the assembly `halfChordSmooth`.
-/

namespace Work.RPB.B5

open scoped ContDiff
open MeasureTheory intervalIntegral

set_option autoImplicit false

noncomputable section

/-- The partial derivative `∂c/∂t (τ,t) = c'(t)` of the curve family, seen as a function of `(τ,t)`.
It is defined through `fderiv`, which makes its smoothness immediate from that of `c`. -/
def pDeriv (c : ℝ → ℝ → ℂ) (τ t : ℝ) : ℂ :=
  fderiv ℝ (fun z : ℝ × ℝ => c z.1 z.2) (τ, t) ((0 : ℝ), (1 : ℝ))

/-- The smooth even extension of the half chord to `r = 0`, given by the average of the derivative:
`(1/2) ∫_0^1 (c'(t + s r) + c'(t - s r)) ds`. -/
def halfChordExt (c : ℝ → ℝ → ℂ) (τ t r : ℝ) : ℂ :=
  (1/2) * ∫ s in (0 : ℝ)..1, (pDeriv c τ (t + s * r) + pDeriv c τ (t - s * r))

/-- `(τ,t) ↦ pDeriv c τ t` is `C^∞` when `c` is jointly `C^∞`. -/
lemma contDiff_pDeriv (c : ℝ → ℝ → ℂ)
    (hcs : ContDiff ℝ ∞ (fun z : ℝ × ℝ => c z.1 z.2)) :
    ContDiff ℝ ∞ (fun z : ℝ × ℝ => pDeriv c z.1 z.2) := by
  unfold pDeriv
  fun_prop

/-- The bridge between `pDeriv` and the one-dimensional `deriv`: `pDeriv c τ t = deriv (c τ) t`. -/
lemma pDeriv_eq_deriv (c : ℝ → ℝ → ℂ)
    (hcs : ContDiff ℝ ∞ (fun z : ℝ × ℝ => c z.1 z.2)) (τ t : ℝ) :
    pDeriv c τ t = deriv (c τ) t := by
  unfold pDeriv
  have hdiff : DifferentiableAt ℝ (fun z : ℝ × ℝ => c z.1 z.2) (τ, t) :=
    (hcs.differentiable (by simp)).differentiableAt
  have hcomp : HasFDerivAt (fun s' : ℝ => (fun z : ℝ × ℝ => c z.1 z.2) (τ, s'))
      ((fderiv ℝ (fun z : ℝ × ℝ => c z.1 z.2) (τ, t)).comp (ContinuousLinearMap.inr ℝ ℝ ℝ)) t :=
    (hdiff.hasFDerivAt).comp t (hasFDerivAt_prodMk_right τ t)
  rw [show deriv (c τ) t = deriv (fun s' : ℝ => (fun z : ℝ × ℝ => c z.1 z.2) (τ, s')) t from rfl]
  rw [(hcomp.hasDerivAt).deriv]
  simp [ContinuousLinearMap.comp_apply, ContinuousLinearMap.inr_apply]

/-- Chain rule for the chord vector: the derivative of `u ↦ c τ (t+u) - c τ (t-u)` is
`c'(t+u) + c'(t-u)`. -/
lemma deriv_chordVec (c : ℝ → ℝ → ℂ)
    (hcs : ContDiff ℝ ∞ (fun z : ℝ × ℝ => c z.1 z.2)) (τ t u : ℝ) :
    deriv (fun y => c τ (t + y) - c τ (t - y)) u = deriv (c τ) (t + u) + deriv (c τ) (t - u) := by
  have hcτ : ContDiff ℝ ∞ (c τ) := by
    have h1 : ContDiff ℝ ∞ (fun y : ℝ => (τ, y)) := by fun_prop
    convert hcs.comp h1 using 1
    ext y
    rfl
  have hcτ' : ∀ y, HasDerivAt (c τ) (deriv (c τ) y) y :=
    fun y => (hcτ.differentiable (by simp) y).hasDerivAt
  have hA : HasDerivAt (fun y => c τ (t + y)) (deriv (c τ) (t + u)) u :=
    (hcτ' (t + u)).comp_const_add t u
  have hB : HasDerivAt (fun y => c τ (t - y)) (- deriv (c τ) (t - u)) u := by
    have hinner : HasDerivAt (fun y : ℝ => t - y) (-1) u := by
      simpa only [id_eq] using (hasDerivAt_id u).const_sub t
    have h := (hcτ' (t - u)).scomp u hinner
    have hfun : (c τ ∘ HSub.hSub t) = (fun y : ℝ => c τ (t - y)) := by funext y; rfl
    rw [hfun] at h
    have hd : (-1 : ℝ) • deriv (c τ) (t - u) = - deriv (c τ) (t - u) := by simp
    rwa [hd] at h
  have hsub : HasDerivAt ((fun y : ℝ => c τ (t + y)) - (fun y : ℝ => c τ (t - y)))
      (deriv (c τ) (t + u) - (- deriv (c τ) (t - u))) u := hA.sub hB
  rw [show (fun y : ℝ => c τ (t + y) - c τ (t - y))
        = (fun y : ℝ => c τ (t + y)) - (fun y : ℝ => c τ (t - y)) from rfl, hsub.deriv]
  ring

/-- The extension `halfChordExt c` is jointly `C^∞` in `(τ,t,r)`. -/
lemma contDiff_halfChordExt (c : ℝ → ℝ → ℂ)
    (hcs : ContDiff ℝ ∞ (fun z : ℝ × ℝ => c z.1 z.2)) :
    ContDiff ℝ ∞ (fun z : ℝ × (ℝ × ℝ) => halfChordExt c z.1 z.2.1 z.2.2) := by
  unfold halfChordExt pDeriv
  have hG : ContDiff ℝ ∞ (fun w : (ℝ × (ℝ × ℝ)) × ℝ =>
      (fderiv ℝ (fun z : ℝ × ℝ => c z.1 z.2) (w.1.1, w.1.2.1 + w.2 * w.1.2.2) ((0:ℝ),(1:ℝ))
        + fderiv ℝ (fun z : ℝ × ℝ => c z.1 z.2) (w.1.1, w.1.2.1 - w.2 * w.1.2.2) ((0:ℝ),(1:ℝ)))) := by
    fun_prop
  have hint := Work.RPA3.contDiff_param_intervalIntegral (X := ℝ × (ℝ × ℝ)) (F := ℂ) (⊤ : ℕ∞)
    (fun z s => fderiv ℝ (fun z : ℝ × ℝ => c z.1 z.2) (z.1, z.2.1 + s * z.2.2) ((0:ℝ),(1:ℝ))
        + fderiv ℝ (fun z : ℝ × ℝ => c z.1 z.2) (z.1, z.2.1 - s * z.2.2) ((0:ℝ),(1:ℝ))) hG 0 1
  simpa [smul_eq_mul] using hint.const_smul ((1/2 : ℂ))

/-- The value of the extension at `r = 0` is the derivative `c'(t)`. -/
lemma halfChordExt_zero (c : ℝ → ℝ → ℂ)
    (hcs : ContDiff ℝ ∞ (fun z : ℝ × ℝ => c z.1 z.2)) (τ t : ℝ) :
    halfChordExt c τ t 0 = deriv (c τ) t := by
  unfold halfChordExt
  simp only [mul_zero, add_zero, sub_zero]
  rw [intervalIntegral.integral_const]
  simp only [sub_zero, one_smul]
  rw [pDeriv_eq_deriv c hcs τ t]
  ring

/-- The extension is even in `r`. -/
lemma halfChordExt_neg (c : ℝ → ℝ → ℂ) (τ t r : ℝ) :
    halfChordExt c τ t (-r) = halfChordExt c τ t r := by
  unfold halfChordExt
  congr 1
  refine intervalIntegral.integral_congr (fun s _ => ?_)
  have h1 : t + s * (-r) = t - s * r := by ring
  have h2 : t - s * (-r) = t + s * r := by ring
  rw [h1, h2, add_comm]

/-- The extension is `2π`-periodic in `t`. -/
lemma halfChordExt_periodic (c : ℝ → ℝ → ℂ)
    (hcs : ContDiff ℝ ∞ (fun z : ℝ × ℝ => c z.1 z.2))
    (hper : ∀ τ t, c τ (t + 2 * Real.pi) = c τ t) (τ t r : ℝ) :
    halfChordExt c τ (t + 2 * Real.pi) r = halfChordExt c τ t r := by
  have hperD : ∀ y, pDeriv c τ (y + 2 * Real.pi) = pDeriv c τ y := by
    intro y
    rw [pDeriv_eq_deriv c hcs τ (y + 2 * Real.pi), pDeriv_eq_deriv c hcs τ y]
    rw [← deriv_comp_add_const (c τ) (2 * Real.pi) y]
    congr 1
    funext z
    exact hper τ z
  unfold halfChordExt
  congr 1
  refine intervalIntegral.integral_congr (fun s _ => ?_)
  have h1 : t + 2 * Real.pi + s * r = (t + s * r) + 2 * Real.pi := by ring
  have h2 : t + 2 * Real.pi - s * r = (t - s * r) + 2 * Real.pi := by ring
  rw [h1, h2, hperD (t + s * r), hperD (t - s * r)]

/-- Real-scalar algebra at the end of `halfChordExt_eq`: the half of the averaged derivative
`r⁻¹ • g` equals the divisor form `g / (2r)`. -/
lemma smul_half_div (g : ℂ) (r : ℝ) (hr : r ≠ 0) :
    (1/2 : ℂ) * ((r⁻¹ : ℝ) • g) = g / ((2:ℂ) * (r:ℂ)) := by
  rw [Algebra.smul_def]
  change (1/2 : ℂ) * (((r⁻¹ : ℝ) : ℂ) * g) = g / ((2:ℂ) * (r:ℂ))
  rw [Complex.ofReal_inv, div_eq_mul_inv]
  have hr' : (r:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hr
  field_simp

/-- Away from `r = 0` the extension agrees with the half chord.  This is the fundamental theorem of
calculus applied to `u ↦ c τ (t+u) - c τ (t-u)`. -/
lemma halfChordExt_eq (c : ℝ → ℝ → ℂ)
    (hcs : ContDiff ℝ ∞ (fun z : ℝ × ℝ => c z.1 z.2)) (τ t r : ℝ) (hr : r ≠ 0) :
    halfChordExt c τ t r = Work.RPB.halfChord c τ t r := by
  unfold halfChordExt Work.RPB.halfChord
  -- replace the averaged derivative by the derivative of the chord vector
  have hA : ∫ s in (0:ℝ)..1, (pDeriv c τ (t + s*r) + pDeriv c τ (t - s*r))
      = ∫ s in (0:ℝ)..1, deriv (fun y => c τ (t + y) - c τ (t - y)) (s*r) := by
    refine intervalIntegral.integral_congr (fun s _ => ?_)
    rw [pDeriv_eq_deriv c hcs τ (t + s*r), pDeriv_eq_deriv c hcs τ (t - s*r)]
    rw [deriv_chordVec c hcs τ t (s*r)]
  have hphi_smooth : ContDiff ℝ ∞ (fun y => c τ (t + y) - c τ (t - y)) := by fun_prop
  -- substitution `s ↦ s * r`
  have hB : ∫ s in (0:ℝ)..1, deriv (fun y => c τ (t + y) - c τ (t - y)) (s*r)
      = r⁻¹ • ∫ y in (0:ℝ)..r, deriv (fun y => c τ (t + y) - c τ (t - y)) y := by
    have h := intervalIntegral.integral_comp_mul_right
      (f := fun y => deriv (fun y => c τ (t + y) - c τ (t - y)) y)
      (a := (0:ℝ)) (b := 1) (c := r) hr
    simpa using h
  -- fundamental theorem of calculus
  have hC : ∫ y in (0:ℝ)..r, deriv (fun y => c τ (t + y) - c τ (t - y)) y
      = (c τ (t + r) - c τ (t - r)) - (c τ (t + 0) - c τ (t - 0)) := by
    have h := intervalIntegral.integral_deriv_eq_sub
      (f := fun y => c τ (t + y) - c τ (t - y))
      (fun x _ => hphi_smooth.differentiable (by simp) x)
      ((hphi_smooth.continuous_deriv (by norm_num)).intervalIntegrable 0 r)
    simpa using h
  rw [hA, hB, hC]
  simp only [add_zero, sub_zero, sub_self]
  exact smul_half_div _ r hr

/-- **The half chord extends smoothly across `r = 0`.**  For a curve family `c` that is `C^∞` in
`(τ,t)` and `2π`-periodic in `t`, there is a jointly `C^∞` function `hc` of `(τ,t,r)` which is even
in `r`, `2π`-periodic in `t`, takes the value `c'(t)` at `r = 0`, and agrees with
`halfChord c τ t r = (c τ (t+r) - c τ (t-r))/(2r)` for `r ≠ 0`. -/
theorem halfChordSmooth (c : ℝ → ℝ → ℂ)
    (hcs : ContDiff ℝ (((⊤ : ℕ∞) : WithTop ℕ∞)) (fun z : ℝ × ℝ => c z.1 z.2))
    (hper : ∀ τ t, c τ (t + 2 * Real.pi) = c τ t) :
    ∃ hc : ℝ → ℝ → ℝ → ℂ,
      ContDiff ℝ (((⊤ : ℕ∞) : WithTop ℕ∞)) (fun z : ℝ × (ℝ × ℝ) => hc z.1 z.2.1 z.2.2) ∧
      (∀ τ t r, hc τ t (-r) = hc τ t r) ∧
      (∀ τ t r, hc τ (t + 2 * Real.pi) r = hc τ t r) ∧
      (∀ τ t, hc τ t 0 = deriv (c τ) t) ∧
      (∀ τ t r, r ≠ 0 → hc τ t r = Work.RPB.halfChord c τ t r) := by
  refine ⟨halfChordExt c, contDiff_halfChordExt c hcs, ?_, ?_, ?_, ?_⟩
  · exact fun τ t r => halfChordExt_neg c τ t r
  · exact fun τ t r => halfChordExt_periodic c hcs hper τ t r
  · exact fun τ t => halfChordExt_zero c hcs τ t
  · exact fun τ t r hr => halfChordExt_eq c hcs τ t r hr

end

end Work.RPB.B5
