import Submission.FUP.DbarAdjOp

open MeasureTheory Metric Filter Function
open scoped ENNReal BigOperators ContDiff

set_option autoImplicit false
set_option maxHeartbeats 2000000

/-!
# Cutting off by a smooth compactly supported function

The Friedrichs step of the Hörmander project (`Submission/FUP/Friedrichs.lean`) reduces an
arbitrary element of `Dom S ⊓ Dom T†` to a compactly supported one by multiplying with a smooth
cutoff `χ_R`.  This module collects the pointwise algebraic ingredients of the *product rules*;
the integral-level statements are recorded in the roadmap and are proved next.

## The three product rules

Let `χ : ℂᵈ → ℝ` be smooth with compact support, `χ_ℂ = toC χ = fun z => (χ z : ℂ)` its
complexification.  On representatives:

1. **`ϑ_φ`-side** (`dbarAdjWeak_mul`).  If `y ∈ Dom ϑ_φ` with `ϑ_φ y = z`, then `χ y ∈ Dom ϑ_φ`
   with `ϑ_φ (χ y) = χ z - ∑_j (∂_j χ_ℂ) y_j`.
   Proof: test the defining relation against `g := χ_ℂ * f`; the Leibniz rule gives
   `∂̄_j (χ_ℂ f) = (∂̄_j χ_ℂ) f + χ_ℂ ∂̄_j f`; the extra term is
   `∫ f · (∑_j (∂̄_j χ_ℂ) conj (y_j))`, which is `⟪w, f⟫` for
   `w = ∑_j (∂_j χ_ℂ) y_j` because `conj (∂_j χ_ℂ) = ∂̄_j χ_ℂ` for real `χ`
   (`conj_partialZ_toC` below).

2. **`(0,1) → (0,2)` side** (`dbarWeak2_mul`).  If `DbarWeak2 φ x ζ` then
   `DbarWeak2 φ (χ x) (χ ζ + e)` with `e_{jk} = (∂̄_k χ_ℂ) x_j - (∂̄_j χ_ℂ) x_k`.
   Proof: test against the test form `χΨ` (which is smooth with compact support), and use
   `ϑ₂ (χΨ) = χ ϑ₂Ψ + (∂χ-terms)`.

3. **`(0,0) → (0,1)` side** (`dbarWeak_mul`).  If `DbarWeak φ f w` then
   `DbarWeak φ (χ f) (χ w + f * (∂̄ χ_ℂ))`.
   Proof: test against the test form `χψ`, and use `ϑ_φ (χ_ℂ ψ) = χ_ℂ ϑ_φψ - ∑_j (∂_j χ_ℂ) ψ_j`;
   the extra term pairs with `f * (∂̄χ_ℂ)`.
-/

namespace Submission.FUP

variable {d : ℕ}

/-- The complexification of a real function. -/
noncomputable def toC (χ : FormDu d → ℝ) : FormDu d → ℂ := fun z => (χ z : ℂ)

@[simp] lemma toC_apply (χ : FormDu d → ℝ) (z : FormDu d) : toC χ z = (χ z : ℂ) := rfl

lemma contDiff_toC {χ : FormDu d → ℝ} {n : WithTop ℕ∞} (hχ : ContDiff ℝ n χ) :
    ContDiff ℝ n (toC χ) := Complex.ofRealCLM.contDiff.comp hχ

@[simp] lemma toC_ofReal_re (χ : FormDu d → ℝ) (z : FormDu d) : (toC χ z).re = χ z := rfl

/-- Conjugation of the Wirtinger derivative of a real function: `conj (∂_j χ_ℂ) = ∂̄_j χ_ℂ`. -/
lemma conj_partialZ_toC (χ : FormDu d → ℝ) (j : Fin d) (z : FormDu d) :
    star (partialZ j (toC χ) z) = partialZbar j (toC χ) z := by
  have h := partialZbar_star j (toC χ)
  have h2 : (fun w => star (toC χ w)) = toC χ := by
    funext w; simp [toC]
  rw [h2] at h
  exact (congrFun h z).symm

/-- The `L²(μ_φ)` inner product of two classes is the integral of the pointwise inner products. -/
lemma inner_toLp_eq_integral {φ : FormDu d → ℝ} {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [CompleteSpace E] {a b : FormDu d → E}
    (ha : MemLp a 2 (wtMeasure φ)) (hb : MemLp b 2 (wtMeasure φ)) :
    inner ℂ (ha.toLp a) (hb.toLp b) = ∫ w, inner ℂ (a w) (b w) ∂(wtMeasure φ) := by
  rw [MeasureTheory.L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [MemLp.coeFn_toLp ha, MemLp.coeFn_toLp hb] with w h1 h2
  rw [h1, h2]

lemma integrable_inner_toLp {φ : FormDu d → ℝ} {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [CompleteSpace E] {a b : FormDu d → E}
    (ha : MemLp a 2 (wtMeasure φ)) (hb : MemLp b 2 (wtMeasure φ)) :
    Integrable (fun w => inner ℂ (a w) (b w)) (wtMeasure φ) :=
  (MeasureTheory.L2.integrable_inner (ha.toLp a) (hb.toLp b)).congr
    (by filter_upwards [MemLp.coeFn_toLp ha, MemLp.coeFn_toLp hb] with w h1 h2
        rw [h1, h2])

section Mul

/-- **The product rule for `ϑ_φ`.**  If `y ∈ Dom ϑ_φ` with `ϑ_φ y = z`, then `χ y ∈ Dom ϑ_φ` with
`ϑ_φ (χ y) = χ z - ∑_j (∂_j χ_ℂ) y_j` (`χ` real, smooth, compactly supported). -/
theorem dbarAdjWeak_mul {φ : FormDu d → ℝ} (hφ : ContDiff ℝ 1 φ) {y : H2 φ} {z : H1 φ}
    (hz : dbarAdjWeak φ y z)
    {χ : FormDu d → ℝ} (hχ : ContDiff ℝ ∞ χ) (hsχ : HasCompactSupport χ)
    (hyχ : MemLp (fun w => toC χ w • (y : FormDu d → FormSpace d) w) 2 (wtMeasure φ))
    (hzχ : MemLp (fun w => toC χ w * (z : FormDu d → ℂ) w) 2 (wtMeasure φ))
    (hw : MemLp (fun w => ∑ j : Fin d, partialZ j (toC χ) w
              * (y : FormDu d → FormSpace d) w j) 2 (wtMeasure φ)) :
    dbarAdjWeak φ (hyχ.toLp fun w => toC χ w • (y : FormDu d → FormSpace d) w)
      (hzχ.toLp (fun w => toC χ w * (z : FormDu d → ℂ) w)
        - hw.toLp (fun w => ∑ j : Fin d, partialZ j (toC χ) w
            * (y : FormDu d → FormSpace d) w j)) := by
  intro f h1 h2 hf hwf
  haveI : IsFiniteMeasureOnCompacts (wtMeasure φ) :=
    isFiniteMeasureOnCompacts_wtMeasure hφ.continuous
  -- the test function `g = χ_ℂ f`
  set g : FormDu d → ℂ := fun w => toC χ w * f w with hgdef
  have hg1 : ContDiff ℝ ∞ g := by rw [hgdef]; exact (contDiff_toC hχ).mul h1
  have hsχC : HasCompactSupport (toC χ) :=
    hsχ.comp_left (g := fun r : ℝ => (r : ℂ)) (by simp)
  have hgs : HasCompactSupport g := by
    rw [hgdef]; exact hsχC.mul_right
  have hgm : MemLp g 2 (wtMeasure φ) :=
    memLp_wtMeasure_of_contDiff_hasCompactSupport hφ.continuous hg1 hgs
  have hgm' : MemLp (dbarFormFun g) 2 (wtMeasure φ) :=
    memLp_wtMeasure_of_contDiff_hasCompactSupport hφ.continuous (contDiff_dbarFormFun hg1)
      (hasCompactSupport_dbarFormFun hgs)
  have hrel := hz g hg1 hgs hgm hgm'
  rw [← Lp.toLp_coeFn z (Lp.memLp z), ← Lp.toLp_coeFn y (Lp.memLp y)] at hrel
  rw [inner_toLp_eq_integral (Lp.memLp z) hgm, inner_toLp_eq_integral (Lp.memLp y) hgm']
    at hrel
  -- convert the goal to integrals
  rw [inner_sub_left, inner_toLp_eq_integral hzχ hf,
    inner_toLp_eq_integral hw hf, inner_toLp_eq_integral hyχ hwf]
  -- pointwise identities
  have e1 : ∀ w, inner ℂ ((fun w : FormDu d => toC χ w * (z : FormDu d → ℂ) w) w) (f w)
      = inner ℂ (z w) (g w) := by
    intro w
    simp only [hgdef, RCLike.inner_apply, map_mul, toC_apply, Complex.conj_ofReal]
    ring
  have e2 : ∀ w, inner ℂ ((fun w : FormDu d => ∑ j : Fin d, partialZ j (toC χ) w
        * (y : FormDu d → FormSpace d) w j) w) (f w)
      = f w * star (∑ j : Fin d, partialZ j (toC χ) w
          * (y : FormDu d → FormSpace d) w j) := by
    intro w; exact RCLike.inner_apply _ _
  have e3 : ∀ w, f w * star (∑ j : Fin d, partialZ j (toC χ) w
          * (y : FormDu d → FormSpace d) w j)
      = inner ℂ ((y : FormDu d → FormSpace d) w) (dbarFormFun g w)
        - inner ℂ ((fun w : FormDu d => toC χ w • (y : FormDu d → FormSpace d) w) w)
            (dbarFormFun f w) := by
    intro w
    have hdχ : DifferentiableAt ℝ (toC χ) w := (contDiff_toC hχ).differentiable (by norm_num) w
    have hdf : DifferentiableAt ℝ f w := h1.differentiable (by norm_num) w
    have hstar : ∀ v : FormDu d, star ((χ v : ℝ) : ℂ) = ((χ v : ℝ) : ℂ) := fun v => by
      rw [Complex.star_def, Complex.conj_ofReal]
    have hg' : ∀ j : Fin d, (dbarFormFun g w).ofLp j
        = toC χ w * partialZbar j f w + f w * partialZbar j (toC χ) w := by
      intro j
      have h : (dbarFormFun g w).ofLp j = partialZbar j (fun v => toC χ v * f v) w := by
        simp only [hgdef, dbarFormFun_apply]
      rw [h, partialZbar_mul hdχ hdf j]
    rw [PiLp.inner_apply, PiLp.inner_apply, ← Finset.sum_sub_distrib, star_sum,
      Finset.mul_sum]
    simp only [hg', WithLp.ofLp_smul, Pi.smul_apply, smul_eq_mul, RCLike.inner_apply,
      dbarFormFun_apply, star_mul, map_mul, toC_apply, hstar, conj_partialZ_toC,
      starRingEnd_apply]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  -- integrability
  have hI1 : Integrable (fun w => inner ℂ (z w) (g w)) (wtMeasure φ) :=
    integrable_inner_toLp (Lp.memLp z) hgm
  have hI2 : Integrable (fun w => inner ℂ ((y : FormDu d → FormSpace d) w) (dbarFormFun g w))
      (wtMeasure φ) := integrable_inner_toLp (Lp.memLp y) hgm'
  have hI3 : Integrable (fun w => inner ℂ
      ((fun w : FormDu d => toC χ w • (y : FormDu d → FormSpace d) w) w) (dbarFormFun f w))
      (wtMeasure φ) := integrable_inner_toLp hyχ hwf
  -- rewrite the goal using the pointwise identities
  rw [show (∫ w, inner ℂ ((fun w : FormDu d => toC χ w * (z : FormDu d → ℂ) w) w) (f w)
        ∂(wtMeasure φ)) = ∫ w, inner ℂ (z w) (g w) ∂(wtMeasure φ) from
      integral_congr_ae (Eventually.of_forall e1)]
  rw [show (∫ w, inner ℂ ((fun w : FormDu d => ∑ j : Fin d, partialZ j (toC χ) w
          * (y : FormDu d → FormSpace d) w j) w) (f w) ∂(wtMeasure φ))
        = ∫ w, (inner ℂ ((y : FormDu d → FormSpace d) w) (dbarFormFun g w)
            - inner ℂ ((fun w : FormDu d => toC χ w • (y : FormDu d → FormSpace d) w) w)
                (dbarFormFun f w)) ∂(wtMeasure φ) from
      integral_congr_ae (Eventually.of_forall fun w => (e2 w).trans (e3 w))]
  rw [integral_sub hI2 hI3, ← hrel]
  ring

end Mul

end Submission.FUP
