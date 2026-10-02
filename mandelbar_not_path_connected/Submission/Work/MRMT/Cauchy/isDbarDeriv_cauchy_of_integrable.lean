import Mathlib
import Submission.Work.MRMT.Cauchy.Defs
import Submission.Work.MRMT.Basic
import Submission.Work.MRMT.Cauchy.integrable_prod_mul_div_sub
import Submission.Work.MRMT.Cauchy.locallyIntegrable_cauchyTransform
import Submission.Work.MRMT.Cauchy.integral_dzbar_div_sub_eq_pi_mul

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


noncomputable section

open MeasureTheory Complex Function Filter
open scoped Distributions Topology ENNReal

namespace Work.MRMT.Cauchy

/-! ## Glue for the Fubini step

The main identity `∫ z, C ω z * ∂̄φ z = -∫ z, ω z * φ z` is obtained by Fubini from the
double integral of `(ζ, z) ↦ ω ζ * ∂̄φ z / (ζ - z)`: integrating in `z` first produces the
pointwise Cauchy–Pompeiu identity `∫ z, ∂̄φ z / (ζ - z) = π * φ ζ`, and the outer integral
against `ω` produces `π * ∫ ω φ`, which is then multiplied by `cauchyConst = -1/π`.

The lemmas below isolate the parts of that argument that do not depend on the two analytic
inputs (the pointwise Cauchy–Pompeiu identity, and absolute convergence of the double
integral). -/

/-- **Fubini step.** If the double integral `(ζ, z) ↦ ω ζ * ∂̄φ z / (ζ - z)` is absolutely
convergent and the fibre integral `∫ z, ∂̄φ z / (ζ - z)` equals `π * φ ζ`, then
`∫ z, C ω z * ∂̄φ z = - ∫ z, ω z * φ z`, and the left integrand is integrable. -/
theorem cauchyTransform_mul_dzbar_of (ω : ℂ → ℂ) (φ : 𝓓(⊤, ℂ))
    (h : MeasureTheory.Integrable
      (fun p : ℂ × ℂ => ω p.1 * Work.MRMT.dzbar (φ : ℂ → ℂ) p.2 / (p.1 - p.2))
      (MeasureTheory.volume.prod MeasureTheory.volume))
    (hid : ∀ ζ : ℂ,
      ∫ z, Work.MRMT.dzbar (φ : ℂ → ℂ) z / (ζ - z) = (Real.pi : ℂ) * (φ : ℂ → ℂ) ζ) :
    MeasureTheory.Integrable
        (fun z => Work.MRMT.cauchyTransform ω z * Work.MRMT.dzbar (φ : ℂ → ℂ) z) ∧
      ∫ z, Work.MRMT.cauchyTransform ω z * Work.MRMT.dzbar (φ : ℂ → ℂ) z
        = -∫ z, ω z * (φ : ℂ → ℂ) z := by
  have h' : MeasureTheory.Integrable
      (uncurry (fun ζ z : ℂ => ω ζ * Work.MRMT.dzbar (φ : ℂ → ℂ) z / (ζ - z)))
      (MeasureTheory.volume.prod MeasureTheory.volume) := h
  have hswap := MeasureTheory.integral_integral_swap h'
  have hinner1 : ∀ ζ : ℂ, (∫ z, ω ζ * Work.MRMT.dzbar (φ : ℂ → ℂ) z / (ζ - z))
      = ω ζ * ((Real.pi : ℂ) * (φ : ℂ → ℂ) ζ) := by
    intro ζ
    rw [show (∫ z, ω ζ * Work.MRMT.dzbar (φ : ℂ → ℂ) z / (ζ - z))
        = ∫ z, ω ζ * (Work.MRMT.dzbar (φ : ℂ → ℂ) z / (ζ - z)) from
      integral_congr_ae (Eventually.of_forall fun z => mul_div_assoc _ _ _)]
    rw [integral_const_mul, hid ζ]
  have hinner2 : ∀ z : ℂ, (∫ ζ, ω ζ * Work.MRMT.dzbar (φ : ℂ → ℂ) z / (ζ - z))
      = (∫ ζ, ω ζ / (ζ - z)) * Work.MRMT.dzbar (φ : ℂ → ℂ) z := by
    intro z
    rw [show (∫ ζ, ω ζ * Work.MRMT.dzbar (φ : ℂ → ℂ) z / (ζ - z))
        = ∫ ζ, (ω ζ / (ζ - z)) * Work.MRMT.dzbar (φ : ℂ → ℂ) z from
      integral_congr_ae (Eventually.of_forall fun ζ => by ring)]
    rw [integral_mul_const]
  have hkey : (∫ z, (∫ ζ, ω ζ / (ζ - z)) * Work.MRMT.dzbar (φ : ℂ → ℂ) z)
      = (Real.pi : ℂ) * ∫ z, ω z * (φ : ℂ → ℂ) z := by
    rw [show (∫ z, (∫ ζ, ω ζ / (ζ - z)) * Work.MRMT.dzbar (φ : ℂ → ℂ) z)
        = ∫ z, ∫ ζ, ω ζ * Work.MRMT.dzbar (φ : ℂ → ℂ) z / (ζ - z) from
      integral_congr_ae (Eventually.of_forall fun z => (hinner2 z).symm)]
    rw [← hswap]
    rw [show (∫ ζ, ∫ z, ω ζ * Work.MRMT.dzbar (φ : ℂ → ℂ) z / (ζ - z))
        = ∫ ζ, ω ζ * ((Real.pi : ℂ) * (φ : ℂ → ℂ) ζ) from
      integral_congr_ae (Eventually.of_forall fun ζ => hinner1 ζ)]
    rw [show (∫ ζ, ω ζ * ((Real.pi : ℂ) * (φ : ℂ → ℂ) ζ))
        = ∫ ζ, (Real.pi : ℂ) * (ω ζ * (φ : ℂ → ℂ) ζ) from
      integral_congr_ae (Eventually.of_forall fun ζ => by ring)]
    rw [integral_const_mul]
  have hInt : MeasureTheory.Integrable
      (fun z => (∫ ζ, ω ζ / (ζ - z)) * Work.MRMT.dzbar (φ : ℂ → ℂ) z) :=
    h'.integral_prod_right.congr (Eventually.of_forall fun z => hinner2 z)
  have hInt2 : MeasureTheory.Integrable
      (fun z => Work.MRMT.cauchyTransform ω z * Work.MRMT.dzbar (φ : ℂ → ℂ) z) :=
    (hInt.const_mul cauchyConst).congr (Eventually.of_forall fun z => by
      simp only [Work.MRMT.cauchyTransform]; ring)
  have hmain : (∫ z, Work.MRMT.cauchyTransform ω z * Work.MRMT.dzbar (φ : ℂ → ℂ) z)
      = cauchyConst * ∫ z, (∫ ζ, ω ζ / (ζ - z)) * Work.MRMT.dzbar (φ : ℂ → ℂ) z := by
    rw [← integral_const_mul]
    exact integral_congr_ae (Eventually.of_forall fun z => by
      simp only [Work.MRMT.cauchyTransform]; ring)
  have hpi : (Real.pi : ℂ) ≠ 0 := fun h => Real.pi_ne_zero (Complex.ofReal_inj.mp h)
  have hcp : cauchyConst * (Real.pi : ℂ) = -1 := by
    have := inv_mul_cancel₀ hpi
    simp only [Work.MRMT.cauchyConst] at *
    rw [neg_mul, this]
  refine ⟨hInt2, ?_⟩
  rw [hmain, hkey, ← mul_assoc, hcp, neg_one_mul]

/-- `∂̄` of a test function is again smooth. -/
theorem contDiff_dzbar_testFunction (φ : 𝓓(⊤, ℂ)) :
    ContDiff ℝ (⊤ : ℕ∞) (fun z : ℂ => Work.MRMT.dzbar (φ : ℂ → ℂ) z) := by
  have hfd : ContDiff ℝ (⊤ : ℕ∞) (fun z : ℂ => fderiv ℝ (φ : ℂ → ℂ) z) := by
    have hm : ContDiff ℝ (⊤ : ℕ∞) (uncurry (fun _ : ℂ => (φ : ℂ → ℂ))) :=
      φ.contDiff.comp contDiff_snd
    exact hm.fderiv contDiff_id (by simp)
  have h1 : ContDiff ℝ (⊤ : ℕ∞) (fun z : ℂ => fderiv ℝ (φ : ℂ → ℂ) z 1) :=
    hfd.clm_apply contDiff_const
  have hI : ContDiff ℝ (⊤ : ℕ∞) (fun z : ℂ => fderiv ℝ (φ : ℂ → ℂ) z Complex.I) :=
    hfd.clm_apply contDiff_const
  have hIc : ContDiff ℝ (⊤ : ℕ∞) (fun z : ℂ => Complex.I * fderiv ℝ (φ : ℂ → ℂ) z Complex.I) :=
    (contDiff_const (c := Complex.I)).mul hI
  have hmain := (h1.add hIc).div_const 2
  simpa only [Work.MRMT.dzbar] using hmain

/-- `∂̄` of a test function again has compact support. -/
theorem hasCompactSupport_dzbar_testFunction (φ : 𝓓(⊤, ℂ)) :
    HasCompactSupport (fun z : ℂ => Work.MRMT.dzbar (φ : ℂ → ℂ) z) := by
  have h1 : HasCompactSupport (fun z : ℂ => fderiv ℝ (φ : ℂ → ℂ) z 1) :=
    φ.hasCompactSupport.fderiv_apply (𝕜 := ℝ) (1 : ℂ)
  have h2 : HasCompactSupport (fun z : ℂ => fderiv ℝ (φ : ℂ → ℂ) z Complex.I) :=
    φ.hasCompactSupport.fderiv_apply (𝕜 := ℝ) Complex.I
  have h2c : HasCompactSupport (fun z : ℂ => Complex.I * fderiv ℝ (φ : ℂ → ℂ) z Complex.I) :=
    HasCompactSupport.smul_left (f := fun _ : ℂ => Complex.I) h2
  have hsum : HasCompactSupport
      (fun z : ℂ => fderiv ℝ (φ : ℂ → ℂ) z 1 + Complex.I * fderiv ℝ (φ : ℂ → ℂ) z Complex.I) :=
    h1.add h2c
  have hmain : HasCompactSupport
      ((fun z : ℂ => z / 2) ∘ fun z : ℂ =>
        fderiv ℝ (φ : ℂ → ℂ) z 1 + Complex.I * fderiv ℝ (φ : ℂ → ℂ) z Complex.I) :=
    hsum.comp_left (g := fun z : ℂ => z / 2) (by simp)
  have heq : ((fun z : ℂ => z / 2) ∘ fun z : ℂ =>
        fderiv ℝ (φ : ℂ → ℂ) z 1 + Complex.I * fderiv ℝ (φ : ℂ → ℂ) z Complex.I)
      = fun z => Work.MRMT.dzbar (φ : ℂ → ℂ) z := by
    funext z
    simp only [Function.comp_apply, Work.MRMT.dzbar, div_eq_mul_inv]
  rwa [heq] at hmain

/-- A test function is bounded, hence `ω * φ` is integrable for integrable `ω`. -/
theorem integrable_mul_testFunction (ω : ℂ → ℂ)
    (hω : MeasureTheory.Integrable ω MeasureTheory.volume) (φ : 𝓓(⊤, ℂ)) :
    MeasureTheory.Integrable (fun z => ω z * (φ : ℂ → ℂ) z) := by
  have hbdd : ∃ C, ∀ z : ℂ, ‖(φ : ℂ → ℂ) z‖ ≤ C := by
    obtain ⟨C, hC⟩ := IsCompact.exists_bound_of_continuousOn (f := (φ : ℂ → ℂ))
      φ.hasCompactSupport.isCompact φ.continuous.continuousOn
    exact ⟨max C 0, fun z => by
      by_cases hz : z ∈ tsupport (φ : ℂ → ℂ)
      · exact (hC z hz).trans (le_max_left _ _)
      · rw [image_eq_zero_of_notMem_tsupport hz, norm_zero]
        exact le_max_right _ _⟩
  obtain ⟨C, hC⟩ := hbdd
  refine MeasureTheory.Integrable.mono' (f := fun z : ℂ => ω z * (φ : ℂ → ℂ) z)
    (g := fun z : ℂ => C * ‖ω z‖) (hω.norm.const_mul C)
    (hω.aestronglyMeasurable.mul φ.continuous.aestronglyMeasurable) ?_
  filter_upwards with z
  show ‖ω z * (φ : ℂ → ℂ) z‖ ≤ C * ‖ω z‖
  rw [norm_mul]
  calc ‖ω z‖ * ‖(φ : ℂ → ℂ) z‖ ≤ ‖ω z‖ * C := mul_le_mul_of_nonneg_left (hC z) (norm_nonneg (ω z))
    _ = C * ‖ω z‖ := mul_comm _ _

/-! ## The main statement -/

/-- **The Cauchy transform inverts `∂̄` : `∂̄ (C ω) = ω` for integrable `ω`.**

This is the non-degenerate form of `Work.MRMT.Cauchy.isDbarDeriv_cauchy`, whose hypothesis
`ContDiff ℝ ⊤ ω` is *real analyticity* (`⊤ = ω` in `ℕ∞ω`), which together with compact support
forces `ω = 0`, making that statement vacuous.  Here no regularity is needed beyond
integrability (a compactly supported smooth `ω` is integrable, giving the intended corollary).

Hints for the prover.
* `LocallyIntegrable ω` follows from `hω : Integrable ω volume`.
* `LocallyIntegrable (cauchyTransform ω)`: `‖C ω z‖ ≤ ‖cauchyConst‖ ∫ ‖ω ζ‖/‖ζ - z‖ dζ`, and by
  Tonelli `∫_{‖z‖<R} ‖C ω z‖ dz ≤ ‖cauchyConst‖ · 6πR · ∫ ‖ω‖` — split `‖ζ‖ ≤ 2R` (bound
  `∫_{‖w‖<3R} 1/‖w‖ = 6πR`) and `‖ζ‖ > 2R` (bound `πR`).
* Fix a test function `φ : 𝓓(⊤, ℂ)`.  The identity `∫ z, C ω z * ∂̄φ z = -∫ z, ω z * φ z`
  is Fubini (`MeasureTheory.integral_integral_swap`; the absolute bound
  `∫∫ ‖ω ζ‖ ‖∂̄φ z‖ / ‖ζ - z‖ < ∞` uses that `∂̄φ` has compact support) combined with the
  pointwise `z`-integral `∫ z, dzbar (φ : ℂ → ℂ) z / (ζ - z) = π * φ ζ`, which is
  `Work.MRMT.Cauchy.integral_dzbar_div_eq_neg_pi_mul` translated by `ζ`.
* **Base identity** `∫ z, dzbar (ψ : ℂ → ℂ) z / z = -π * ψ 0` for smooth compactly supported
  `ψ`: set `g ε z = ψ z * (star z) / (‖z‖^2 + ε^2)` (smooth, compactly supported, `ε > 0`).
  `Work.MRMT.Sobolev.integral_dzbar_eq_zero_of_contDiff g ε ...` gives `∫ ∂̄(g ε) = 0`, while
  `∂̄(g ε) = ∂̄ψ · z̄/(‖z‖²+ε²) + ψ · ε²/(‖z‖²+ε²)²` (product rule `Work.MRMT.Sobolev.dzbar_mul`
  plus `∂̄(z̄/(‖z‖²+ε²)) = ε²/(‖z‖²+ε²)²`).  Letting `ε → 0⁺`: the first term tends to
  `∫ ∂̄ψ/z` (dominated convergence, `‖z̄/(‖z‖²+ε²)‖ ≤ 1/‖z‖`), the second to `π ψ 0`
  (substitute `z = ε w`, dominated convergence, `∫_ℂ 1/(1+‖w‖²)² dw = π`). -/
theorem isDbarDeriv_cauchy_of_integrable (ω : ℂ → ℂ) (hω : MeasureTheory.Integrable ω MeasureTheory.volume) :
    Work.MRMT.IsDbarDeriv (Work.MRMT.cauchyTransform ω) ω := by
  have hloc : MeasureTheory.LocallyIntegrable (Work.MRMT.cauchyTransform ω) MeasureTheory.volume :=
    locallyIntegrable_cauchyTransform ω hω
  refine ⟨hloc, hω.locallyIntegrable, fun φ => ?_⟩
  have hprod : MeasureTheory.Integrable
      (fun p : ℂ × ℂ => ω p.1 * Work.MRMT.dzbar (φ : ℂ → ℂ) p.2 / (p.1 - p.2))
      (MeasureTheory.volume.prod MeasureTheory.volume) :=
    integrable_prod_mul_div_sub ω hω (fun z => Work.MRMT.dzbar (φ : ℂ → ℂ) z)
      (contDiff_dzbar_testFunction φ) (hasCompactSupport_dzbar_testFunction φ)
  have hid : ∀ ζ : ℂ,
      ∫ z, Work.MRMT.dzbar (φ : ℂ → ℂ) z / (ζ - z) = (Real.pi : ℂ) * (φ : ℂ → ℂ) ζ := fun ζ =>
    integral_dzbar_div_sub_eq_pi_mul (φ : ℂ → ℂ) φ.contDiff φ.hasCompactSupport ζ
  obtain ⟨h1, h2⟩ := cauchyTransform_mul_dzbar_of ω φ hprod hid
  exact ⟨h1, integrable_mul_testFunction ω hω φ, h2⟩

end Work.MRMT.Cauchy
