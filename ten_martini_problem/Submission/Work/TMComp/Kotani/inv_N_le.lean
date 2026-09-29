import Mathlib
import Submission.Work.TMComp.Kotani.Objects
import Submission.Work.TMComp.Kotani.mfun_props
import Submission.Work.TMComp.Kotani.mfun_im_shift
import Submission.Work.TMComp.Kotani.two_ell

/-!
# (L3): `∫₀¹ 1/N₁ ≤ 2ℓ/ε` and `∫₀¹ 1/N₂ ≤ 2ℓ/ε`

Notation: `ε = Im E > 0`, `m := mfun α lam E ·`, `p := pSec α lam E · = -1/m`, and
`ℓ := ell α lam E = ∫₀¹ log ‖m(x)‖ dx`.

Both halves of the statement are consequences of the pointwise log inequality
(`Real.le_log_one_add_of_nonneg`)

  `2t/(t+2) ≤ log(1+t)   (t ≥ 0)`,

applied with `t = ε/im p(x) > 0`, together with (L2) (`two_ell`):

  `2ℓ = ∫₀¹ log(1 + ε/im p(x)) dx`.

On the one hand (`N1_shift`) `N₁(x+α) = im p(x) + ε/2`, and `N₁` is `1`-periodic
(`N1_period`), so

  `∫₀¹ 1/N₁ = ∫₀¹ 1/N₁(x+α) = ∫₀¹ 2/(2 im p(x)+ε)`;

on the other hand (`N2_eq`) `N₂(y) = im p(α-y) + ε/2`, so (after the change of variable
`y ↦ α-y` and the `1`-periodicity of `x ↦ im p(x)`)

  `∫₀¹ 1/N₂ = ∫₀¹ 2/(2 im p(x)+ε)`.

Multiplying the pointwise inequality `2/(2 im p+ε) ≤ (1/ε) log(1+ε/im p)` by `dx` and
integrating gives `∫₀¹ 2/(2 im p+ε) ≤ (1/ε)·∫₀¹ log(1+ε/im p) = 2ℓ/ε`.
-/

open MeasureTheory Filter Topology Set
open LeanEval.Analysis.TenMartini

noncomputable section

namespace Work.TMComp.Kotani

open Work.TMContract

/-! ## Elementary pointwise identities for the sections -/

/-- For `w : ℂ`, the imaginary part of `1/conj w` is `w.im / ‖w‖²`. -/
theorem star_im_inv_star (w : ℂ) : (1 / star w).im = w.im / ‖w‖ ^ 2 := by
  rw [one_div, Complex.star_def, ← Complex.conj_inv]
  rw [Complex.conj_im, Complex.inv_im, Complex.normSq_eq_norm_sq]
  ring

/-- `im σ(y) = im p(α-y)`: the imaginary part of the reflected section `σ = 1/conj(m(α-·))`
is the imaginary part of `p = -1/m` at the reflected phase. -/
theorem sigSec_im (α lam : ℝ) (E : ℂ) (hE : 0 < E.im) (y : ℝ) :
    (sigSec α lam E y).im = (pSec α lam E (α - y)).im := by
  rw [sigSec, star_im_inv_star, pSec_im α lam E hE (α - y)]

/-- `N₁(x+α) = im p(x) + ε/2`. -/
theorem N1_shift (α lam : ℝ) (E : ℂ) (hE : 0 < E.im) (x : ℝ) :
    N1 α lam E (x + α) = (pSec α lam E x).im + E.im / 2 := by
  rw [N1, mfun_im_shift α lam E hE x, ← pSec_im α lam E hE x]
  ring

/-- `N₁` is `1`-periodic in the phase. -/
theorem N1_period (α lam : ℝ) (E : ℂ) (x : ℝ) :
    N1 α lam E (x + 1) = N1 α lam E x := by
  rw [N1, N1, MfunProbs.mfun_period]

/-- `N₂(y) = im p(α-y) + ε/2`. -/
theorem N2_eq (α lam : ℝ) (E : ℂ) (hE : 0 < E.im) (y : ℝ) :
    N2 α lam E y = (pSec α lam E (α - y)).im + E.im / 2 := by
  rw [N2, sigSec_im α lam E hE y]

/-- `p = -1/m` is `1`-periodic in the phase. -/
theorem pSec_period (α lam : ℝ) (E : ℂ) (x : ℝ) :
    pSec α lam E (x + 1) = pSec α lam E x := by
  rw [pSec, pSec, MfunProbs.mfun_period]

/-! ## The pointwise log inequality -/

/-- `2/(2p+e) ≤ (1/e)·log(1+e/p)` for `e > 0`, `p > 0`, obtained from
`Real.le_log_one_add_of_nonneg` with `t = e/p`. -/
theorem two_div_le_log {e p : ℝ} (he : 0 < e) (hp : 0 < p) :
    2 / (2 * p + e) ≤ (1 / e) * Real.log (1 + e / p) := by
  have ht : 0 ≤ e / p := by positivity
  have h := Real.le_log_one_add_of_nonneg (x := e / p) ht
  have hineq : (1 / e) * (2 * (e / p) / (e / p + 2)) ≤ (1 / e) * Real.log (1 + e / p) :=
    mul_le_mul_of_nonneg_left h (by positivity)
  have heq : (1 / e) * (2 * (e / p) / (e / p + 2)) = 2 / (2 * p + e) := by
    field_simp
    ring
  rwa [heq] at hineq

/-! ## The common integral bound -/

/-- **Core estimate.** `∫₀¹ 2/(2 im p(x)+ε) dx ≤ 2ℓ/ε`.

Pointwise, `2/(2 im p(x)+ε) ≤ (1/ε) log(1 + ε/im p(x))`; integrating and using (L2)
(`two_ell`) gives the claim. -/
theorem inv_N_le_core (α lam : ℝ) (E : ℂ) (hE : 0 < E.im) :
    (∫ x in (0 : ℝ)..1, 2 / (2 * (pSec α lam E x).im + E.im))
      ≤ 2 * ell α lam E / E.im := by
  -- continuity of `x ↦ mfun α lam E x`
  have hm : Continuous (fun x : ℝ => mfun α lam E x) := by
    have hc := MfunProbs.mfun_continuousOn α lam
    have h2 : Continuous (fun x : ℝ => (E, x)) := continuous_const.prodMk continuous_id
    have hcomp := hc.comp_continuous h2 (fun x => hE)
    simpa [Function.comp_def] using hcomp
  have hm0 : ∀ x : ℝ, mfun α lam E x ≠ 0 := fun x h => by
    have := MfunProbs.mfun_im_pos α lam hE x
    rw [h] at this; simp at this
  have hp : Continuous (fun x : ℝ => pSec α lam E x) := by
    have hfun : (fun x : ℝ => pSec α lam E x)
        = fun x => (-1 : ℂ) * (mfun α lam E x)⁻¹ := by
      funext x; rw [pSec, div_eq_mul_inv]
    rw [hfun]
    exact continuous_const.mul (hm.inv₀ hm0)
  have hP : Continuous (fun x : ℝ => (pSec α lam E x).im) := Complex.continuous_im.comp hp
  have hPpos : ∀ x : ℝ, 0 < (pSec α lam E x).im := fun x => by
    rw [pSec_im α lam E hE x]
    exact div_pos (MfunProbs.mfun_im_pos α lam hE x) (pow_pos (norm_pos_iff.mpr (hm0 x)) 2)
  -- the two integrands
  have hden : Continuous (fun x : ℝ => 2 * (pSec α lam E x).im + E.im) :=
    (continuous_const.mul hP).add continuous_const
  have hden0 : ∀ x : ℝ, 2 * (pSec α lam E x).im + E.im ≠ 0 := by
    intro x
    exact ne_of_gt (by have h1 := hPpos x; linarith [hE])
  have hf : Continuous (fun x : ℝ => 2 / (2 * (pSec α lam E x).im + E.im)) :=
    continuous_const.div hden hden0
  have harg : Continuous (fun x : ℝ => 1 + E.im / (pSec α lam E x).im) :=
    continuous_const.add (continuous_const.div hP (fun x => ne_of_gt (hPpos x)))
  have hlog : Continuous (fun x : ℝ => Real.log (1 + E.im / (pSec α lam E x).im)) := by
    apply Real.continuousOn_log.comp_continuous harg
    intro x
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
    exact ne_of_gt (by
      have h1 := hPpos x
      have h2 : 0 < E.im / (pSec α lam E x).im := div_pos hE h1
      linarith)
  have hg : Continuous (fun x : ℝ =>
      (1 / E.im) * Real.log (1 + E.im / (pSec α lam E x).im)) :=
    continuous_const.mul hlog
  -- pointwise comparison and integration
  have hmono : (∫ x in (0 : ℝ)..1, 2 / (2 * (pSec α lam E x).im + E.im))
      ≤ ∫ x in (0 : ℝ)..1,
          (1 / E.im) * Real.log (1 + E.im / (pSec α lam E x).im) := by
    apply intervalIntegral.integral_mono_on (a := (0 : ℝ)) (b := 1) zero_le_one
      (hf.intervalIntegrable 0 1) (hg.intervalIntegrable 0 1)
    intro x _
    exact two_div_le_log hE (hPpos x)
  calc (∫ x in (0 : ℝ)..1, 2 / (2 * (pSec α lam E x).im + E.im))
      ≤ ∫ x in (0 : ℝ)..1,
          (1 / E.im) * Real.log (1 + E.im / (pSec α lam E x).im) := hmono
    _ = (1 / E.im) * ∫ x in (0 : ℝ)..1, Real.log (1 + E.im / (pSec α lam E x).im) :=
        intervalIntegral.integral_const_mul _ _
    _ = (1 / E.im) * (2 * ell α lam E) := by rw [← two_ell α lam E hE]
    _ = 2 * ell α lam E / E.im := by ring

/-! ## Identification of the two integrals -/

/-- `∫₀¹ 1/N₁ = ∫₀¹ 2/(2 im p+ε)`, by `1`-periodicity of `N₁` and `N₁(x+α) = im p(x)+ε/2`. -/
theorem N1_integral (α lam : ℝ) (E : ℂ) (hE : 0 < E.im) :
    (∫ x in (0 : ℝ)..1, 1 / N1 α lam E x)
      = ∫ x in (0 : ℝ)..1, 2 / (2 * (pSec α lam E x).im + E.im) := by
  have hper : Function.Periodic (fun x : ℝ => 1 / N1 α lam E x) 1 := fun x => by
    show 1 / N1 α lam E (x + 1) = 1 / N1 α lam E x
    rw [N1_period]
  have hshift : (∫ x in (0 : ℝ)..1, 1 / N1 α lam E (x + α))
      = ∫ x in (0 : ℝ)..1, 1 / N1 α lam E x := by
    rw [intervalIntegral.integral_comp_add_right (fun x : ℝ => 1 / N1 α lam E x) α]
    have hp := hper.intervalIntegral_add_eq α 0
    simpa [zero_add, add_comm] using hp
  rw [← hshift]
  apply intervalIntegral.integral_congr
  intro x _
  show 1 / N1 α lam E (x + α) = 2 / (2 * (pSec α lam E x).im + E.im)
  rw [N1_shift α lam E hE x]
  field_simp

/-- `∫₀¹ 1/N₂ = ∫₀¹ 2/(2 im p+ε)`, by `N₂(y) = im p(α-y)+ε/2`, the change of variable
`y ↦ α-y` and the `1`-periodicity of `x ↦ im p(x)`. -/
theorem N2_integral (α lam : ℝ) (E : ℂ) (hE : 0 < E.im) :
    (∫ y in (0 : ℝ)..1, 1 / N2 α lam E y)
      = ∫ x in (0 : ℝ)..1, 2 / (2 * (pSec α lam E x).im + E.im) := by
  have hpt : (fun y : ℝ => 1 / N2 α lam E y)
      = fun y => 2 / (2 * (pSec α lam E (α - y)).im + E.im) := by
    funext y
    rw [N2_eq α lam E hE y]
    field_simp
  rw [hpt]
  have hgper : Function.Periodic (fun u : ℝ => 2 / (2 * (pSec α lam E u).im + E.im)) 1 :=
    fun u => by
      show 2 / (2 * (pSec α lam E (u + 1)).im + E.im)
        = 2 / (2 * (pSec α lam E u).im + E.im)
      rw [pSec_period]
  rw [intervalIntegral.integral_comp_sub_left
        (fun u : ℝ => 2 / (2 * (pSec α lam E u).im + E.im)) α]
  have hp := hgper.intervalIntegral_add_eq (α - 1) 0
  simpa using hp

/-! ## The target lemma (L3) -/

theorem inv_N_le (α lam : ℝ) (E : ℂ) (hE : 0 < E.im) :
    (∫ x in (0 : ℝ)..1, 1 / Work.TMComp.Kotani.N1 α lam E x)
        ≤ 2 * Work.TMComp.Kotani.ell α lam E / E.im ∧
      (∫ y in (0 : ℝ)..1, 1 / Work.TMComp.Kotani.N2 α lam E y)
        ≤ 2 * Work.TMComp.Kotani.ell α lam E / E.im := by
  have hcore := inv_N_le_core α lam E hE
  constructor
  · rw [N1_integral α lam E hE]; exact hcore
  · rw [N2_integral α lam E hE]; exact hcore

end Work.TMComp.Kotani
