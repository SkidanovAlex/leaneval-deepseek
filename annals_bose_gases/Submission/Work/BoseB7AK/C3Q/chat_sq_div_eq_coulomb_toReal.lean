import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Fourier.FourierTransform
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseB7AK.C3Q.coulomb_W1fun_le
import Submission.Work.BoseB7AK.C3Q.lintegral_chat_sq_div_eq
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseB7AK.C3Q

open MeasureTheory
open scoped Real FourierTransform ENNReal

/-- **`chat` only sees the a.e. class of `W`.**  `Work.BoseFixR.chat W p` is the real part
of the integral `∫ y, e^{−i⟪p,y⟫} W(y) dy` (`Submission.BoseGases.kinFT`), hence depends on
`W` only through its values a.e. -/
lemma chat_congr_ae {W W' : EuclideanSpace ℝ (Fin 3) → ℝ} (h : W =ᵐ[volume] W')
    (p : EuclideanSpace ℝ (Fin 3)) :
    Work.BoseFixR.chat W p = Work.BoseFixR.chat W' p := by
  have h1 : (fun y : EuclideanSpace ℝ (Fin 3) =>
        Complex.exp (-(Complex.I * (inner ℝ p y : ℂ))) * ((W y : ℝ) : ℂ))
      =ᵐ[volume] (fun y : EuclideanSpace ℝ (Fin 3) =>
        Complex.exp (-(Complex.I * (inner ℝ p y : ℂ))) * ((W' y : ℝ) : ℂ)) :=
    h.mono (fun y hy => by simp only [hy])
  simp only [Work.BoseFixR.chat, Submission.BoseGases.kinFT]
  exact congrArg Complex.re (integral_congr_ae h1)

/-- **The real-space form of the Fourier–Coulomb (Newtonian energy) identity, with the
position-space double integral kept as an `ENNReal` (`∫⁻`) lintegral.**

Intended use: `Work.BoseB7AK.C3Q.I2_integral_bound` needs
`(2π)⁻³ ∫ p, Ŵ₁(p)²/(2‖p‖²)` rewritten in x-space, where `W = W₁ = wScaled ℓ (g₀)` is
integrable and **even** (it is `g₀/(χ⋆χ)(·/ℓ)`, both factors even) while `0 ≤ W` holds
only **a.e.** (never pointwise — `g₀ = v(1−ω)` is only a.e. nonnegative).  The x-side is
only available as an `∫⁻` (with its `.toReal`).

ROUTE (all ingredients already in the corpus/workspace):

* `Work.BoseB7AK.C3Q.lintegral_chat_sq_div_eq` (already proved, sorry-free) gives, for `W`
  with `Integrable W`, `∀ x, 0 ≤ W x` pointwise and `∀ x, W (-x) = W x`:
  `∫⁻ p, ofReal (Ŵ(p)²/‖p‖²) = ofReal (2π²) * ∫⁻ x, ∫⁻ y, ofReal (W x * W y / ‖x−y‖)`,
  where `Ŵ = Work.BoseFixR.chat W`.
* Only the a.e. class of an *even* `W` matters here: `W⁺ := fun x => max (W x) 0` is even
  (because `W` is), `0 ≤ W⁺` pointwise, `W⁺ =ᵐ W` (the set `{W < 0}` is null) and
  `Integrable W⁺`.  `Work.BoseFixR.chat` sees only the a.e. class
  (`∀ p, chat W⁺ p = chat W p`, by `integral_congr_ae`), and the iterated lintegral of
  `ofReal (W x * W y / ‖x − y‖)` too (for a.e. `x` the `y`-slices agree a.e., so
  `lintegral_congr_ae` twice).  Apply the corpus identity to `W⁺`.
* `MeasureTheory.integral_eq_lintegral_of_nonneg_ae` turns the momentum-space Bochner
  integral into the `.toReal` of the `∫⁻`; the integrand `Ŵ(p)²/(2‖p‖²)` is pointwise `≥ 0`
  and `AEStronglyMeasurable` because `chat W` is continuous for `W ∈ L¹`
  (route: `VectorFourier.fourierIntegral_continuous`; the workspace also carries a private
  `continuous_chat` in `Submission/Work/BoseBogFS/chat_W1fun_pos_near_zero.lean`).
* `ENNReal.ofReal_mul` splits `ofReal (a/(2b)) = ofReal (1/2) * ofReal (a/b)` for `a ≥ 0`
  (both sides are `0` when `b = 0`), `ENNReal.toReal_mul` pulls out the constants, and
  `(2π)⁻³ · (1/2) · 2π² = 1/(8π)`.
-/
theorem chat_sq_div_eq_coulomb_toReal {W : EuclideanSpace ℝ (Fin 3) → ℝ}
    (hW : MeasureTheory.Integrable W) (hW0 : ∀ᵐ x, 0 ≤ W x)
    (hWe : ∀ x, W (-x) = W x) :
    ((2 * Real.pi) ^ 3)⁻¹
        * (∫ p, (Work.BoseFixR.chat W p) ^ 2 / (2 * ‖p‖ ^ 2))
      = (1 / (8 * Real.pi))
        * (∫⁻ x, ∫⁻ y, ENNReal.ofReal (W x * W y / ‖x - y‖)).toReal := by
  set Y : ℝ≥0∞ := ∫⁻ x, ∫⁻ y, ENNReal.ofReal (W x * W y / ‖x - y‖) with hY
  -- the pointwise nonnegative representative `W⁺ = max W 0` of the a.e. class of `W`
  set Wp : EuclideanSpace ℝ (Fin 3) → ℝ := fun x => max (W x) 0 with hWp
  have hWp0 : ∀ x, 0 ≤ Wp x := by intro x; rw [hWp]; exact le_max_right _ _
  have hWpe : ∀ x, Wp (-x) = Wp x := by intro x; rw [hWp]; simp only [hWe x]
  have hae : Wp =ᵐ[volume] W :=
    hW0.mono (fun x hx => by rw [hWp]; exact max_eq_left hx)
  have hWpI : MeasureTheory.Integrable Wp := hW.congr hae.symm
  -- `chat` only sees the a.e. class
  have hchat : ∀ p, Work.BoseFixR.chat Wp p = Work.BoseFixR.chat W p :=
    fun p => chat_congr_ae hae p
  -- the x-space double integral only sees the a.e. class, in the `y`-slot …
  have hstep1 : (∫⁻ x, ∫⁻ y, ENNReal.ofReal (Wp x * Wp y / ‖x - y‖))
      = (∫⁻ x, ∫⁻ y, ENNReal.ofReal (Wp x * W y / ‖x - y‖)) := by
    apply lintegral_congr_ae
    filter_upwards with x
    apply lintegral_congr_ae
    filter_upwards [hae] with y hy
    rw [hy]
  -- … and then, for a.e. `x`, in the `x`-slot
  have hstep2 : (∫⁻ x, ∫⁻ y, ENNReal.ofReal (Wp x * W y / ‖x - y‖))
      = (∫⁻ x, ∫⁻ y, ENNReal.ofReal (W x * W y / ‖x - y‖)) := by
    apply lintegral_congr_ae
    filter_upwards [hae] with x hx
    rw [hx]
  have hdoub : (∫⁻ x, ∫⁻ y, ENNReal.ofReal (Wp x * Wp y / ‖x - y‖)) = Y :=
    (hstep1.trans hstep2).trans hY.symm
  -- the corpus identity, applied to the pointwise nonnegative representative
  have hmain : (∫⁻ p, ENNReal.ofReal ((Work.BoseFixR.chat Wp p) ^ 2 / ‖p‖ ^ 2))
      = ENNReal.ofReal (2 * Real.pi ^ 2) * Y := by
    rw [Work.BoseB7AK.C3Q.lintegral_chat_sq_div_eq hWpI hWp0 hWpe, hdoub]
  have hZ : (∫⁻ p, ENNReal.ofReal ((Work.BoseFixR.chat W p) ^ 2 / ‖p‖ ^ 2))
      = ENNReal.ofReal (2 * Real.pi ^ 2) * Y := by
    rw [← hmain]
    exact lintegral_congr (fun p => by rw [hchat p])
  -- split off the `1/2` sitting in the denominator
  have h2 : (∫⁻ p, ENNReal.ofReal ((Work.BoseFixR.chat W p) ^ 2 / (2 * ‖p‖ ^ 2)))
      = ENNReal.ofReal (1 / 2)
          * ∫⁻ p, ENNReal.ofReal ((Work.BoseFixR.chat W p) ^ 2 / ‖p‖ ^ 2) := by
    have hpt : ∀ p : EuclideanSpace ℝ (Fin 3),
        ENNReal.ofReal ((Work.BoseFixR.chat W p) ^ 2 / (2 * ‖p‖ ^ 2))
          = ENNReal.ofReal (1 / 2)
              * ENNReal.ofReal ((Work.BoseFixR.chat W p) ^ 2 / ‖p‖ ^ 2) := by
      intro p
      rw [← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 1 / 2)]
      congr 1
      field_simp
    rw [lintegral_congr hpt]
    exact MeasureTheory.lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
  -- `chat W` is continuous for `W ∈ L¹`, hence the momentum integrand is a.e. measurable
  have hcont : Continuous (Work.BoseFixR.chat W) := by
    have hf : MeasureTheory.Integrable
        (fun y : EuclideanSpace ℝ (Fin 3) => ((W y : ℝ) : ℂ)) := hW.ofReal
    have hF : Continuous (𝓕 (fun y : EuclideanSpace ℝ (Fin 3) => ((W y : ℝ) : ℂ))) :=
      VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
        (innerSL ℝ).continuous₂ hf
    have hcomp : Continuous (fun k : EuclideanSpace ℝ (Fin 3) =>
        (𝓕 (fun y : EuclideanSpace ℝ (Fin 3) => ((W y : ℝ) : ℂ)))
          ((2 * Real.pi)⁻¹ • k)) :=
      hF.comp (continuous_const_smul ((2 * Real.pi)⁻¹))
    have key : Work.BoseFixR.chat W
        = fun k : EuclideanSpace ℝ (Fin 3) =>
            (𝓕 (fun y : EuclideanSpace ℝ (Fin 3) => ((W y : ℝ) : ℂ))
              ((2 * Real.pi)⁻¹ • k)).re := by
      funext k
      simp only [Work.BoseFixR.chat]
      rw [Work.SmallBoxBridge.Resolve.kinFT_eq_fourier]
    rw [key]
    exact Complex.continuous_re.comp hcomp
  -- the momentum-space Bochner integral is the `.toReal` of its `∫⁻`
  have hInt : (∫ p, (Work.BoseFixR.chat W p) ^ 2 / (2 * ‖p‖ ^ 2))
      = (ENNReal.ofReal (1 / 2) * (ENNReal.ofReal (2 * Real.pi ^ 2) * Y)).toReal := by
    have h0 : 0 ≤ᵐ[volume] fun p : EuclideanSpace ℝ (Fin 3) =>
        (Work.BoseFixR.chat W p) ^ 2 / (2 * ‖p‖ ^ 2) :=
      Filter.Eventually.of_forall (fun p => div_nonneg (sq_nonneg _) (by positivity))
    have hm : AEStronglyMeasurable (fun p : EuclideanSpace ℝ (Fin 3) =>
        (Work.BoseFixR.chat W p) ^ 2 / (2 * ‖p‖ ^ 2)) volume := by
      have hnum : AEMeasurable (fun p : EuclideanSpace ℝ (Fin 3) =>
          (Work.BoseFixR.chat W p) ^ 2) volume := (hcont.pow 2).aemeasurable
      have hden : AEMeasurable (fun p : EuclideanSpace ℝ (Fin 3) => 2 * ‖p‖ ^ 2) volume :=
        (by fun_prop : Continuous fun p : EuclideanSpace ℝ (Fin 3) => 2 * ‖p‖ ^ 2).aemeasurable
      exact (hnum.div hden).aestronglyMeasurable
    rw [MeasureTheory.integral_eq_lintegral_of_nonneg_ae h0 hm, h2, hZ]
  -- constants: `(2π)⁻³ · (1/2) · 2π² = 1/(8π)`
  rw [hInt, ENNReal.toReal_mul, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (by norm_num : (0 : ℝ) ≤ 1 / 2),
    ENNReal.toReal_ofReal (by positivity : (0 : ℝ) ≤ 2 * Real.pi ^ 2)]
  have hconst : ((2 * Real.pi) ^ 3)⁻¹ * ((1 / 2) * (2 * Real.pi ^ 2)) = 1 / (8 * Real.pi) := by
    have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
    field_simp
    ring
  rw [← hconst]
  ring

end Work.BoseB7AK.C3Q
