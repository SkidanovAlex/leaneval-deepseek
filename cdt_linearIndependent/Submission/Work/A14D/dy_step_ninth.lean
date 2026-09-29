import Mathlib
import Submission.Work.A14.defs
import Submission.Work.A14D.chainZDefs

namespace Work.A14D

open Complex Metric Filter
open scoped Topology

/-! ## Auxiliary lemmas for the `∂_y`-step at `1/9`

`Dy F = ∂_y F = (1/y')·F'` with `y = z²/(z−1)`, `y' = (z²−2z)/(z−1)²`, so that
`Dy F z = deriv F z * ((z−1)²/(z²−2z))`.

Three ingredients:

* the pointwise derivative of the model function
  `w ↦ A w·log(w − 1/9) + G w/(w − 1/9)^m` at a point where `w − 1/9` lies in the slit plane;
* clearing the `(z − 1/9)`-denominators after multiplying by `1/y'`;
* the resulting witness `G'` is holomorphic on the whole disc `ball (1/9) δ`
  when `δ ≤ 1/20`.
-/

/-- Pointwise derivative of the log-structure model `A·log(· − 1/9) + G/(· − 1/9)^m`: on the slit
plane the principal `Complex.log` has derivative `1/(· − 1/9)`, so the product rule gives the
logarithmic part, and the quotient rule gives the polar part. -/
lemma dy_step_ninth_log_deriv {m : ℕ} {A G : ℂ → ℂ} {z : ℂ}
    (hz : z - ninth ∈ Complex.slitPlane)
    (hA : HasDerivAt A (deriv A z) z) (hG : HasDerivAt G (deriv G z) z) :
    HasDerivAt (fun w : ℂ => A w * Complex.log (w - ninth) + G w / (w - ninth) ^ m)
      (deriv A z * Complex.log (z - ninth) + A z * (1 / (z - ninth))
        + (deriv G z / (z - ninth) ^ m - (m : ℂ) * G z / (z - ninth) ^ (m + 1))) z := by
  have hu : z - ninth ≠ 0 := by
    intro h0
    rw [h0, Complex.mem_slitPlane_iff] at hz
    simp at hz
  have hlog : HasDerivAt (fun w : ℂ => Complex.log (w - ninth)) (1 / (z - ninth)) z := by
    have hinner : HasDerivAt (fun w : ℂ => w - ninth) 1 z := (hasDerivAt_id' z).sub_const ninth
    have hh := (Complex.hasDerivAt_log hz).comp z hinner
    simpa [Function.comp_def, one_div, mul_one] using hh
  have hLogp : HasDerivAt (fun w : ℂ => A w * Complex.log (w - ninth))
      (deriv A z * Complex.log (z - ninth) + A z * (1 / (z - ninth))) z :=
    hA.mul hlog
  have hGp : HasDerivAt (fun w : ℂ => G w / (w - ninth) ^ m)
      (deriv G z / (z - ninth) ^ m - (m : ℂ) * G z / (z - ninth) ^ (m + 1)) z := by
    have hp : HasDerivAt (fun w : ℂ => (w - ninth) ^ (-(m : ℤ)))
        (((-(m : ℤ) : ℤ) : ℂ) * (z - ninth) ^ (-(m : ℤ) - 1)) z := by
      have hh := (hasDerivAt_zpow (-(m : ℤ)) (z - ninth) (Or.inl hu)).comp z
        ((hasDerivAt_id' z).sub_const ninth)
      simpa only [Function.comp_def, mul_one] using hh
    have hmul := hG.mul hp
    have hdval : deriv G z * (z - ninth) ^ (-(m : ℤ))
          + G z * (((-(m : ℤ) : ℤ) : ℂ) * (z - ninth) ^ (-(m : ℤ) - 1))
        = deriv G z / (z - ninth) ^ m - (m : ℂ) * G z / (z - ninth) ^ (m + 1) := by
      rw [zpow_neg, zpow_natCast,
        show (-(m : ℤ) - 1) = -((m + 1 : ℕ) : ℤ) by push_cast; ring, zpow_neg, zpow_natCast]
      push_cast
      ring
    have hfun : (G * fun w : ℂ => (w - ninth) ^ (-(m : ℤ)))
        = fun w : ℂ => G w / (w - ninth) ^ m := by
      funext w
      simp only [Pi.mul_apply]
      rw [zpow_neg, zpow_natCast]
      rfl
    rw [hfun] at hmul
    rw [hdval] at hmul
    exact hmul
  exact hLogp.add hGp

/-- Clearing the `(· − 1/9)`-denominators in one `∂_y`-step: after multiplying
`deriv A z·log + A/(·−1/9) + (G'/(·−1/9)^m − m·G/(·−1/9)^(m+1))` by `1/y'(z)` one may write the
non-logarithmic part over the common denominator `(·−1/9)^(m+1)`. -/
lemma dy_step_ninth_algebra {m : ℕ} (u a a' g g' : ℂ) (hu : u ≠ 0) :
    a' * Complex.log u + a * (1 / u) + (g' / u ^ m - (m : ℂ) * g / u ^ (m + 1))
      = a' * Complex.log u + (a * u ^ m + g' * u - (m : ℂ) * g) / u ^ (m + 1) := by
  rw [pow_succ]
  field_simp
  ring

/-- The witness `G'(z) = ((z−1)²/(z²−2z))·(A z·(z − 1/9)^m + deriv G z·(z − 1/9) − m·G z)` of the
`∂_y`-step is holomorphic on the whole disc: for `δ ≤ 1/20` the disc avoids `0`, `1`, `2`, so
`(z−1)²/(z²−2z)` is holomorphic there and `deriv G` is holomorphic there since `G` is. -/
lemma dy_step_ninth_witness_holo {δ : ℝ} (hδ : δ ≤ 1 / 20) {m : ℕ} {A G : ℂ → ℂ}
    (hA : DifferentiableOn ℂ A (Metric.ball ninth δ))
    (hG : DifferentiableOn ℂ G (Metric.ball ninth δ)) :
    DifferentiableOn ℂ (fun z : ℂ => (z - 1) ^ 2 / (z ^ 2 - 2 * z)
      * (A z * (z - ninth) ^ m + deriv G z * (z - ninth) - (m : ℂ) * G z))
      (Metric.ball ninth δ) := by
  have hball : IsOpen (Metric.ball ninth δ) := Metric.isOpen_ball
  have hrho : DifferentiableOn ℂ (fun z : ℂ => (z - 1) ^ 2 / (z ^ 2 - 2 * z))
      (Metric.ball ninth δ) := by
    refine DifferentiableOn.div ?_ ?_ ?_
    · exact (differentiableOn_id.sub (differentiableOn_const 1)).pow 2
    · exact (differentiableOn_id.pow 2).sub ((differentiableOn_const 2).mul differentiableOn_id)
    · intro z hz
      exact sq_sub_two_ne_zero_of_mem_ball_ninth hδ hz
  refine hrho.mul ?_
  refine ((hA.mul ((differentiableOn_id.sub (differentiableOn_const ninth)).pow m)).add
    (((hG.deriv hball).mul (differentiableOn_id.sub (differentiableOn_const ninth))))).sub
    ((differentiableOn_const (m : ℂ)).mul hG)

/-- One step of `∂_y = (1/y')·d/dz` on the upper half disc at `1/9`.

Setting: `δ ≤ 1/20` keeps `0`, `1`, `2` out of `Metric.ball ninth δ`, so the factor
`(z-1)²/(z²-2z)` of `Dy` is holomorphic on the disc, and `halfU δ = ball ninth δ ∩ {Im > 0}` is an
open subset of the disc on which `z - ninth ≠ 0` and `z - ninth ∈ Complex.slitPlane`
(`Im (z - ninth) = Im z > 0`), so `Complex.log (· - ninth)` is holomorphic there with derivative
`1/(· - ninth)`.

Claim: if `A`, `G` are holomorphic on `Metric.ball ninth δ` and on `halfU δ` the function `F` agrees
with `A · log (· - 1/9) + G / (· - 1/9)^m`, then `Dy F` agrees on `halfU δ` with
`(Dy A) · log (· - 1/9) + G' / (· - 1/9)^(m+1)` for some `G'` holomorphic on the whole disc.

Suggested witness:
`G' := fun z => (z-1)^2/(z^2-2*z) * (A z * (z - ninth)^m + deriv G z * (z - ninth) - (m:ℂ) * G z)`.
On `halfU δ` the pointwise identity `F z = model z` holds on a whole neighbourhood of `z`
(`halfU δ` is open), so `deriv F z = deriv model z` by `Filter.EventuallyEq.deriv_eq`; no global
differentiability of `F` is needed. -/
theorem dy_step_ninth {δ : ℝ} (hδ : δ ≤ 1 / 20) {m : ℕ} {F A G : ℂ → ℂ}
    (hA : DifferentiableOn ℂ A (Metric.ball ninth δ))
    (hG : DifferentiableOn ℂ G (Metric.ball ninth δ))
    (h : ∀ z ∈ halfU δ, F z = A z * Complex.log (z - ninth) + G z / (z - ninth) ^ m) :
    ∃ G' : ℂ → ℂ, DifferentiableOn ℂ G' (Metric.ball ninth δ) ∧
      ∀ z ∈ halfU δ, Dy F z = Dy A z * Complex.log (z - ninth) + G' z / (z - ninth) ^ (m + 1) := by
  classical
  have hball : IsOpen (Metric.ball ninth δ) := Metric.isOpen_ball
  refine ⟨fun z => ((z - 1) ^ 2 / (z ^ 2 - 2 * z)) *
      (A z * (z - ninth) ^ m + deriv G z * (z - ninth) - (m : ℂ) * G z),
    dy_step_ninth_witness_holo hδ hA hG, ?_⟩
  intro z hz
  obtain ⟨hzball, hzim⟩ := hz
  have hzim' : 0 < z.im := hzim
  have hninth_im : ninth.im = 0 := by simp [ninth]
  -- `z - 1/9` has positive imaginary part, so `z ≠ 1/9` and `log (· - 1/9)` is holomorphic at `z`
  have hu : z - ninth ≠ 0 := by
    intro h0
    have h1 : z = ninth := sub_eq_zero.mp h0
    rw [h1, hninth_im] at hzim'
    exact lt_irrefl 0 hzim'
  have hsl : z - ninth ∈ Complex.slitPlane := by
    refine Complex.mem_slitPlane_iff.mpr (Or.inr ?_)
    simp only [Complex.sub_im, hninth_im, sub_zero]
    exact ne_of_gt hzim'
  -- `halfU δ` is a neighbourhood of `z`, so `F` and the model function have the same derivative
  have hmem : halfU δ ∈ 𝓝 z := by
    rw [halfU]
    exact Filter.inter_mem (Metric.isOpen_ball.mem_nhds hzball)
      ((isOpen_lt continuous_const Complex.continuous_im).mem_nhds hzim')
  have heq : F =ᶠ[𝓝 z] (fun w : ℂ => A w * Complex.log (w - ninth) + G w / (w - ninth) ^ m) :=
    Filter.eventually_of_mem hmem h
  have hderivF : deriv F z
      = deriv (fun w : ℂ => A w * Complex.log (w - ninth) + G w / (w - ninth) ^ m) z :=
    heq.deriv_eq
  have hAat : HasDerivAt A (deriv A z) z :=
    (hA.differentiableAt (hball.mem_nhds hzball)).hasDerivAt
  have hGat : HasDerivAt G (deriv G z) z :=
    (hG.differentiableAt (hball.mem_nhds hzball)).hasDerivAt
  have hH := dy_step_ninth_log_deriv (m := m) hsl hAat hGat
  have hAlg := dy_step_ninth_algebra (m := m) (z - ninth) (A z) (deriv A z) (G z) (deriv G z) hu
  rw [Dy, Dy, hderivF, hH.deriv, hAlg]
  ring

end Work.A14D
