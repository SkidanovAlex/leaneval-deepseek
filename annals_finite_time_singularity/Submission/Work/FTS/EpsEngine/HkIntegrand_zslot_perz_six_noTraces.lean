/-
Copyright: work module for the Elgindi finite-time singularity project.

# The per-`z` bound for a weighted `D_z`-slot of the level-`8` `ℋ`-integrand, no traces

`Work.FTS.EpsEngine.HkIntegrand_zslot_perz_six_noTraces`: for a datum `f` of class `C^∞` on the
open quadrant, honestly in `ℋ⁸` (`HkMem α 8 f`) — and with **no** boundary-trace hypothesis — each
single weighted radial slot of the `ℋ⁶`-integrand,

  `∫_θ (D_z^i f(z,θ) · w(z)/sin(2θ)^{η/2})² dθ`,   `w(z) = (1+z)²/z²`, `η = 99/100`,

is bounded at *every* `z ∈ [0,∞)` by `C (1 + w(z)²) (1 + ‖f‖_{ℋ⁸})²`, with a universal constant `C`
(here `C = 3`) independent of `α ∈ (0,1]`, of the slot `i ≤ 6` and of the datum.

This is the level-`8`/`i ≤ 6` instance of the verbatim argument of
`Work.FTS.EpsEngine.HkIntegrand_zslot_perz_le_noTraces` (itself the trace-free form of
`Work.FTS.StrongEps.E5Aux.HkIntegrand_zslot_perz_le`); the level occurs only in the numerals, and
the trace hypothesis of the `E5Aux` version is spurious (see `EpsEngine/NOTES_HtrUnused.md`).

## Proof

* `z = 0` is trivial: `w 0 = 0`, so the slot vanishes.
* For `z > 0` the key is the one-dimensional **window form of the radial Hardy inequality**
  `Work.FTS.StrongEps.E5Aux.zslot_window_perz`: applied to the `θ`-slice
  `h := x ↦ D_z^i f(x,θ)` on the window `[z, 2R₀]` (with `R₀ = max z 2`) it gives
  `h(z)² ≤ 2∫_z^{2R₀}(x h'(x) w(x))² + (2/R₀)∫_{R₀}^{2R₀} h²`, and `x h'(x) = D_z^{i+1}f(x,θ)`
  (definitional, since `D_z^{i+1} = D_z ∘ D_z^i`).  Multiplying by
  `(w(z)/sin(2θ)^{η/2})²` turns the two window integrands — after the `rpow` bookkeeping
  `Work.FTS.H2.div_rpow_sq`, `(a/x^{c/2})² = a²x^{-c}` — exactly into the `D_z^{i+1}` resp. `D_z^i`
  slots of the `ℋ⁸`-integrand (the second uses `w(x) ≥ 1`), so both window integrals are dominated
  by `∫_{Iz} HkIntegrand α 8 f · θ`; `i + 1 ≤ 7 ≤ 8` is what makes the first one legal.
* Integrating the resulting a.e.-in-`θ` pointwise bound over `θ ∈ Iθ` against the Tonelli identity
  `Work.FTS.EpsEngine.sda_HkSqSwap_open8` (`∫_θ ∫_z HkIntegrand = HkSq α 8 f`) gives
  `∫_θ slot² ≤ 3 w(z)² ℋ⁸`, and `ℋ⁸ = ‖f‖_{ℋ⁸}²`, `w(z)² ≤ 1 + w(z)²` finish it.

Everything here is `sorry`-free and rests on `[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.FTS.EpsEngine.SixNoTracesAux
import Submission.Work.FTS.StrongEps.E5Aux.zslot_window_perz
import Submission.Work.FTS.EllipticEst.AeSlotOneAe.Interp.TkA_slotIntegrable
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.Spaces.HkSq_terms
import Submission.Work.Spaces.aesm_HkIntegrand_quad

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EpsEngine

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false
set_option maxHeartbeats 1200000

theorem HkIntegrand_zslot_perz_six_noTraces :
    ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ), α ∈ Set.Ioc 0 1 → ∀ {f : ℝ → ℝ → ℝ},
      Work.FTS.EllipticEst.SmoothOpen f → Work.Spaces.HkMem α 8 f →
      ∀ i : ℕ, i ≤ 6 → ∀ z ∈ Work.Spaces.Iz,
      (∫ θ in Work.Spaces.Iθ, (Work.Spaces.DzIter i f z θ
          * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
        ≤ C * (1 + (Work.Spaces.w z) ^ 2) * (1 + Work.Spaces.HkNorm α 8 f) ^ 2 := by
  refine ⟨3, by norm_num, ?_⟩
  intro α hα f hF hmem i hi z hz
  rcases eq_or_lt_of_le (Set.mem_Ici.mp hz) with hz0 | hzpos
  · -- ### `z = 0`: the radial weight vanishes
    subst hz0
    have hw0 : Work.Spaces.w 0 = 0 := by rw [Work.Spaces.w]; norm_num
    have hzero : (fun θ : ℝ => (Work.Spaces.DzIter i f 0 θ
        * (Work.Spaces.w 0 / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
        = fun _ : ℝ => (0 : ℝ) := by
      funext θ
      rw [hw0, zero_div, mul_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0)]
    rw [hzero]
    have h1 : (∫ _θ in Work.Spaces.Iθ, (0 : ℝ)) = 0 := by simp
    rw [h1]
    have h2 : 0 ≤ (1 + Work.Spaces.HkNorm α 8 f) ^ 2 := sq_nonneg _
    have h3 : 0 ≤ (1 : ℝ) + (Work.Spaces.w 0) ^ 2 := by rw [hw0]; norm_num
    nlinarith [h2, h3]
  · -- ### `z > 0`: the window bound at every angle, then integrate in `θ`
    have hR : z ≤ max z 2 := le_max_left z 2
    have hRpos : 0 < max z 2 := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 2) (le_max_right z 2)
    have h2max : (2 : ℝ) ≤ max z 2 := le_max_right z 2
    obtain ⟨hswap, hGint, hGslice⟩ := sda_HkSqSwap_open8 α f hF hmem
    -- almost every angle is interior
    have haeθ : ∀ᵐ σ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
        σ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) := by
      rw [MeasureTheory.ae_restrict_iff' (s := Work.Spaces.Iθ) measurableSet_Icc]
      filter_upwards [MeasureTheory.Ioo_ae_eq_Icc (μ := MeasureTheory.volume) (a := (0 : ℝ))
        (b := Real.pi / 2)] with σ h
      exact fun hmem' => h.mpr hmem'
    -- the a.e. pointwise bound
    have hle : (fun σ : ℝ => (Work.Spaces.DzIter i f z σ
          * (Work.Spaces.w z / (Real.sin (2 * σ)) ^ (Work.Spaces.eta / 2))) ^ 2)
        ≤ᵐ[MeasureTheory.volume.restrict Work.Spaces.Iθ]
        (fun σ : ℝ => (Work.Spaces.w z) ^ 2 * (2 + 2 / max z 2)
          * (∫ s in Work.Spaces.Iz, Work.Spaces.HkIntegrand α 8 f s σ)) := by
      filter_upwards [hGslice, haeθ] with σ hσint hσθ
      exact Work.FTS.StrongEps.E5Aux.zslot_window_perz α hF 8 i (by omega) hzpos hR hσθ hσint
    -- integrability of the two sides
    have hLI : MeasureTheory.Integrable (fun σ : ℝ => (Work.Spaces.DzIter i f z σ
        * (Work.Spaces.w z / (Real.sin (2 * σ)) ^ (Work.Spaces.eta / 2))) ^ 2)
        (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
      Work.FTS.EllipticEst.integrableOn_zSummand α 8 hF hmem i (by omega)
        (Set.mem_Ici.mpr hzpos.le)
    have hRI : MeasureTheory.Integrable (fun σ : ℝ => (Work.Spaces.w z) ^ 2 * (2 + 2 / max z 2)
        * (∫ s in Work.Spaces.Iz, Work.Spaces.HkIntegrand α 8 f s σ))
        (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
      hGint.const_mul ((Work.Spaces.w z) ^ 2 * (2 + 2 / max z 2))
    -- the integral bound
    have hmain : (∫ θ in Work.Spaces.Iθ, (Work.Spaces.DzIter i f z θ
          * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
        ≤ (Work.Spaces.w z) ^ 2 * (2 + 2 / max z 2) * Work.Spaces.HkSq α 8 f := by
      have h1 := MeasureTheory.integral_mono_ae hLI hRI hle
      rw [MeasureTheory.integral_const_mul, hswap] at h1
      exact h1
    -- the coefficient is at most `3`
    have hcoef : 2 + 2 / max z 2 ≤ 3 := by
      have h : 2 / max z 2 ≤ 1 := by
        rw [div_le_one hRpos]
        exact h2max
      linarith
    have hHknn : 0 ≤ Work.Spaces.HkSq α 8 f := Work.Spaces.HkSq_nonneg α 8 f
    have hXnn : 0 ≤ Work.Spaces.HkNorm α 8 f := Work.Spaces.HkNorm_nonneg α 8 f
    have hXsq : Work.Spaces.HkSq α 8 f
        ≤ (1 + Work.Spaces.HkNorm α 8 f) ^ 2 := by
      have h4 : Work.Spaces.HkNorm α 8 f = Real.sqrt (Work.Spaces.HkSq α 8 f) := rfl
      rw [h4]
      nlinarith [Real.sq_sqrt hHknn, hXnn, hHknn]
    calc (∫ θ in Work.Spaces.Iθ, (Work.Spaces.DzIter i f z θ
            * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
        ≤ (Work.Spaces.w z) ^ 2 * (2 + 2 / max z 2) * Work.Spaces.HkSq α 8 f := hmain
      _ ≤ (Work.Spaces.w z) ^ 2 * 3 * Work.Spaces.HkSq α 8 f := by
          have h := mul_le_mul_of_nonneg_right hcoef hHknn
          nlinarith [h, sq_nonneg (Work.Spaces.w z)]
      _ ≤ 3 * (1 + (Work.Spaces.w z) ^ 2)
            * (1 + Work.Spaces.HkNorm α 8 f) ^ 2 := by
          have hstep : (Work.Spaces.w z) ^ 2 * Work.Spaces.HkSq α 8 f
              ≤ (1 + (Work.Spaces.w z) ^ 2)
                * (1 + Work.Spaces.HkNorm α 8 f) ^ 2 :=
            mul_le_mul (by linarith [sq_nonneg (Work.Spaces.w z)]) hXsq hHknn
              (by linarith [sq_nonneg (Work.Spaces.w z)])
          nlinarith [mul_le_mul_of_nonneg_left hstep (by norm_num : (0 : ℝ) ≤ 3)]

end Work.FTS.EpsEngine
