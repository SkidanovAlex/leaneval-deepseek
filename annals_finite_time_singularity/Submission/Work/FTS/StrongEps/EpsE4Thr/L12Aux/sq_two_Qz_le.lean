import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.StrongEps.EpsE4Thr.L12Aux.Defs
import Submission.Work.FTS.StrongEps.classC_mixed_sup_le_four
import Submission.Work.Spaces.cs_integral
import Submission.Work.FTS.EllipticEst.OpenQDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.EpsE4Thr.L12Aux

set_option linter.unusedVariables false

/-! ## Two elementary pointwise identities for the weighted slices

The Cauchy–Schwarz argument is run on the *weighted* slices
`U θ = D_z^k x (z,θ) · w z / sin(2θ)^{η/2}`, whose a.e. strong measurability and whose square
integrability are supplied by the `HkMem`-machinery of `Work.FTS.EllipticEst.OpenQDefs`
(`SmoothOpen.aesm_slice_summand`, `integrableOn_zSummand`).  The price is that the integrals
`∫_{Iθ} U²`, `∫_{Iθ} U·V` have to be converted back into `(w z)²·Pz` resp. `(w z)²·Qz`, which
needs the two `Real.rpow` identities below. -/

/-- **The square of `c / sin(2θ)^{η/2}`**, in endpoint-safe form (`sin(2θ) = 0` is allowed:
both sides vanish there). -/
theorem div_rpow_half_sq (c s : ℝ) (hs : 0 ≤ s) :
    (c / s ^ (Work.Spaces.eta / 2)) ^ 2 = c ^ 2 * s ^ (-(Work.Spaces.eta)) := by
  rcases eq_or_lt_of_le hs with h | h
  · rw [← h]
    simp [Real.zero_rpow (by norm_num [Work.Spaces.eta] : -(Work.Spaces.eta) ≠ 0),
      Real.zero_rpow (by norm_num [Work.Spaces.eta] : Work.Spaces.eta / 2 ≠ 0)]
  · have hsq : (s ^ (Work.Spaces.eta / 2)) ^ 2 = s ^ Work.Spaces.eta := by
      rw [sq, ← Real.rpow_add h]
      ring_nf
    rw [div_pow, hsq, Real.rpow_neg h.le]
    field_simp

/-- **The product of two consecutive weighted slices.**  For `θ ∈ Iθ`,
`(D_z^k x·w/s^{η/2})·(D_z^{k+1} x·w/s^{η/2}) = (w z)²·D_z^k x·D_z^{k+1} x·s^{-η}` with
`s = sin(2θ)` — the `sin(2θ)^{-η}`-weighted correlation integrand of `Qz`, times `(w z)²`. -/
theorem summand_prod_eq (x : Work.FTS.Galerkin.Fn) (k : ℕ) {z θ : ℝ}
    (hθ : θ ∈ Work.Spaces.Iθ) :
    (Work.Spaces.DzIter k x z θ
        * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)))
      * (Work.Spaces.DzIter (k + 1) x z θ
        * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)))
      = (Work.Spaces.w z) ^ 2 * (Work.Spaces.DzIter k x z θ
        * Work.Spaces.DzIter (k + 1) x z θ * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) := by
  have hs := sin_two_nonneg_of_mem_Iθ hθ
  rw [show (Work.Spaces.DzIter k x z θ
        * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)))
      * (Work.Spaces.DzIter (k + 1) x z θ
        * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)))
      = Work.Spaces.DzIter k x z θ * Work.Spaces.DzIter (k + 1) x z θ
        * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)) ^ 2 from by ring,
    div_rpow_half_sq (Work.Spaces.w z) (Real.sin (2 * θ)) hs]
  ring

/-- **Cauchy–Schwarz for the angular correlation `Qz`.**

`Pz x k z = ∫_{Iθ} (D_z^k x (z,θ))² sin(2θ)^{-η} dθ` and
`Qz x k z = ∫_{Iθ} D_z^k x (z,θ) · D_z^{k+1} x (z,θ) sin(2θ)^{-η} dθ`
(see `Submission.Work.FTS.StrongEps.EpsE4Thr.L12Aux.Defs`).

For `ClassC α x`, `α ∈ (0,1]`, `k ≤ 3` and `z > 0`,

  `(2 · Qz x k z)^2 ≤ 4 · Pz x k z · Pz x (k+1) z`,

i.e. `|z (Pz x k)' z| ≤ 2 √(Pz x k z · Pz x (k+1) z)` (combine with `hasDerivAt_Pz`).

Proof route: `2 * Qz x k z = ∫ θ in Iθ, (2 * DzIter k x z θ * DzIter (k+1) x z θ)
* sin(2θ)^{-η}`, and the integrand factors as
`(√2 * DzIter k x z θ * sin(2θ)^{-η/2}) * (√2 * DzIter (k+1) x z θ * sin(2θ)^{-η/2})`.
Apply `Work.Spaces.cs_integral` (or `MeasureTheory.integral_mul_le_Lp_mul_Lq_of_nonneg`); the
required `MemLp 2` of both factors follows from the uniform bound
`|DzIter j x z θ| ≤ C₀` on the open quadrant (`Work.FTS.StrongEps.classC_mixed_sup_le_four`
with `j ≤ 4`, so `k, k+1 ≤ 4`) and the integrability of `sin(2θ)^{-η}` on `Iθ` (`η < 1`,
`Work.Spaces.sin_two_rpow` with `p = -η`).  Use `Real.rpow_add`/`Real.rpow_neg`
(`(sin(2θ)^{-η/2})² = sin(2θ)^{-η}`) and `L12Aux.summand_sq_eq` as needed. -/
theorem sq_two_Qz_le {α : ℝ} (hα : α ∈ Set.Ioc 0 1) {x : Work.FTS.Galerkin.Fn}
    (hx : Work.FTS.ClassC.ClassC α x) {k : ℕ} (hk : k ≤ 3) {z : ℝ} (hz : 0 < z) :
    (2 * Qz x k z) ^ 2 ≤ 4 * Pz x k z * Pz x (k + 1) z := by
  -- the two weighted angular slices
  set U : ℝ → ℝ := fun θ => Work.Spaces.DzIter k x z θ
    * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)) with hU
  set V : ℝ → ℝ := fun θ => Work.Spaces.DzIter (k + 1) x z θ
    * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)) with hV
  -- they are square-integrable on `Iθ`
  have hUaesm : AEStronglyMeasurable U (volume.restrict Work.Spaces.Iθ) := by
    rw [hU]
    exact hx.reg.aesm_slice_summand k hz
  have hVaesm : AEStronglyMeasurable V (volume.restrict Work.Spaces.Iθ) := by
    rw [hV]
    exact hx.reg.aesm_slice_summand (k + 1) hz
  have hUint : Integrable (fun θ => U θ ^ 2) (volume.restrict Work.Spaces.Iθ) := by
    rw [hU]
    exact Work.FTS.EllipticEst.integrableOn_zSummand α 7 hx.reg hx.mem k (by omega)
      (Set.mem_Ici.mpr hz.le)
  have hVint : Integrable (fun θ => V θ ^ 2) (volume.restrict Work.Spaces.Iθ) := by
    rw [hV]
    exact Work.FTS.EllipticEst.integrableOn_zSummand α 7 hx.reg hx.mem (k + 1) (by omega)
      (Set.mem_Ici.mpr hz.le)
  have hUmem : MemLp U 2 (volume.restrict Work.Spaces.Iθ) :=
    (MeasureTheory.memLp_two_iff_integrable_sq hUaesm).2 hUint
  have hVmem : MemLp V 2 (volume.restrict Work.Spaces.Iθ) :=
    (MeasureTheory.memLp_two_iff_integrable_sq hVaesm).2 hVint
  -- Cauchy–Schwarz
  have hcs := Work.Spaces.cs_integral (s := Work.Spaces.Iθ) hUmem hVmem
  have hIθ : MeasurableSet Work.Spaces.Iθ := by
    rw [Work.Spaces.Iθ]; exact measurableSet_Icc
  -- the three integrals
  have eUV : (∫ θ in Work.Spaces.Iθ, U θ * V θ)
      = (Work.Spaces.w z) ^ 2 * Qz x k z :=
    calc (∫ θ in Work.Spaces.Iθ, U θ * V θ)
        = ∫ θ in Work.Spaces.Iθ, (Work.Spaces.w z) ^ 2 *
            (Work.Spaces.DzIter k x z θ * Work.Spaces.DzIter (k + 1) x z θ
              * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) := by
          refine MeasureTheory.setIntegral_congr_fun hIθ (fun θ hθ => ?_)
          rw [hU, hV]
          exact summand_prod_eq x k hθ
      _ = (Work.Spaces.w z) ^ 2 * Qz x k z := by
          rw [MeasureTheory.integral_const_mul]
          rfl
  have eU2 : (∫ θ in Work.Spaces.Iθ, U θ ^ 2) = (Work.Spaces.w z) ^ 2 * Pz x k z :=
    calc (∫ θ in Work.Spaces.Iθ, U θ ^ 2)
        = ∫ θ in Work.Spaces.Iθ, (Work.Spaces.w z) ^ 2 *
            ((Work.Spaces.DzIter k x z θ) ^ 2
              * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) := by
          refine MeasureTheory.setIntegral_congr_fun hIθ (fun θ hθ => ?_)
          rw [hU, summand_sq_eq x k hθ]
          ring
      _ = (Work.Spaces.w z) ^ 2 * Pz x k z := by
          rw [MeasureTheory.integral_const_mul]
          rfl
  have eV2 : (∫ θ in Work.Spaces.Iθ, V θ ^ 2) = (Work.Spaces.w z) ^ 2 * Pz x (k + 1) z :=
    calc (∫ θ in Work.Spaces.Iθ, V θ ^ 2)
        = ∫ θ in Work.Spaces.Iθ, (Work.Spaces.w z) ^ 2 *
            ((Work.Spaces.DzIter (k + 1) x z θ) ^ 2
              * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) := by
          refine MeasureTheory.setIntegral_congr_fun hIθ (fun θ hθ => ?_)
          rw [hV, summand_sq_eq x (k + 1) hθ]
          ring
      _ = (Work.Spaces.w z) ^ 2 * Pz x (k + 1) z := by
          rw [MeasureTheory.integral_const_mul]
          rfl
  -- cancel the positive factor `(w z)^4`
  have hw : (0 : ℝ) < (Work.Spaces.w z) ^ 2 := by
    rw [Work.Spaces.w]
    positivity
  have hkey : (Qz x k z) ^ 2 ≤ Pz x k z * Pz x (k + 1) z := by
    rw [eUV, eU2, eV2] at hcs
    have h3 : ((Work.Spaces.w z) ^ 2) ^ 2 * (Qz x k z) ^ 2
        ≤ ((Work.Spaces.w z) ^ 2) ^ 2 * (Pz x k z * Pz x (k + 1) z) := by
      nlinarith [hcs]
    exact le_of_mul_le_mul_left h3 (pow_pos hw 2)
  have h4 : (2 * Qz x k z) ^ 2 = 4 * (Qz x k z) ^ 2 := by ring
  rw [h4]
  nlinarith [hkey]

end Work.FTS.StrongEps.EpsE4Thr.L12Aux
