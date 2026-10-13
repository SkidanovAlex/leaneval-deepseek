/-
Copyright: work module for the Elgindi finite-time singularity project.

# `PkgJets.pinHardy` — the angular Hardy inequality behind the pinning estimate

The pinning estimate `PkgJets.pinningBound` reduces, through the reconstruction
`∂_θ(cos θ·Ψ) = cos θ · Vop Ψ`, to the following one-dimensional weighted Hardy inequality:
with `A := cos θ·Ψ`, `A' := cos θ·Vop Ψ`, `ν := sin(2θ)^{-η}`,

`∫_θ A²·W₁ ≤ K · ∫_θ (A')²·W₂`,   `W₁ = ν/cos⁴θ`, `W₂ = ν/cos²θ`,

for `A` whose `π/2`-boundary value vanishes (`cos θ·Ψ → 0`, the *pinning*).  The proof is the
classical proof of the weighted Hardy inequality: integrate `(A²Λ)' = 2AA'Λ + A²W₁` by parts
against the primitive `Λ` of `W₁` (here the primitive `pinL x` based at the *regular* end `x`, so
that the boundary term at `x` vanishes exactly), then Cauchy–Schwarz, with the two *pointwise /
quantitative* inputs

* `Λ(θ)² ≤ C₁·W₁(θ)·W₂(θ)` (`cosWeightPrim_sq_le`), which makes the Cauchy–Schwarz factor
  `∫ (A')²Λ²/W₁` comparable with `∫ (A')²W₂`;
* `(∫_T^{π/2} cos²s·sin(2s)^η ds)·Λ(T) ≤ C₂` (`cosWeightTail_le`), which bounds the boundary term
  at the singular end `π/2` using the *vanishing* of `A` there (the pinning, through the a-priori
  bound `A(T)² ≤ 2A(T')² + 2(∫_T^{T'}cos·V)² → 2(∫_T^{T'}cos·V)²`).

The two inputs are stated here as *hypotheses* `hLamB`, `hTailB`, so that this module is
independent of the two numerical lemmas; `PkgJets.pinningBound` instantiates them.
-/
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Submission.Work.FTS_EllLimOK.PkgJets.pinBase
import Submission.Work.Spaces.cs_integral
import Submission.Work.FTS_EllLimOK.Reconstruct
import Submission.Work.FTS.EllipticEst.OpenQDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS_EllLimOK.PkgJets

set_option autoImplicit false
set_option maxHeartbeats 1600000
/-! ## Elementary comparison of the two primitives -/

/-- The primitive based at `x ≥ 0` is dominated by the primitive based at `0`. -/
theorem pinL_le_wLam {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) (hy : y ∈ Set.Ioo 0 (π / 2)) :
    pinL x y ≤ wLam y := by
  have hint : IntegrableOn wOne (Set.Icc 0 y) := integrableOn_wOne_Icc hy
  have h1 : IntervalIntegrable wOne volume (0 : ℝ) x := by
    refine ⟨hint.mono_set ?_, hint.mono_set ?_⟩
    · intro t ht; exact ⟨ht.1.le, le_trans ht.2 hxy⟩
    · rintro t ⟨h1, h2⟩; exact absurd h1 (not_lt.mpr (le_trans h2 hx))
  have h2 : IntervalIntegrable wOne volume x y := by
    refine ⟨hint.mono_set ?_, hint.mono_set ?_⟩
    · intro t ht; exact ⟨le_trans hx ht.1.le, ht.2⟩
    · rintro t ⟨h1, h2⟩; exact absurd h1 (not_lt.mpr (le_trans h2 hxy))
  have hadd := intervalIntegral.integral_add_adjacent_intervals h1 h2
  have hnn : 0 ≤ ∫ s in (0 : ℝ)..x, wOne s :=
    intervalIntegral.integral_nonneg hx
      (fun u hu => wOne_nonneg ⟨hu.1, le_trans (le_trans hu.2 hxy) hy.2.le⟩)
  rw [pinL, wLam, ← hadd]
  linarith

/-- Cauchy–Schwarz on a subinterval of the open quadrant, for continuous functions. -/
theorem cs_subinterval {u v : ℝ → ℝ} {a b : ℝ} (hab : a < b)
    (hu : ContinuousOn u (Set.Icc a b)) (hv : ContinuousOn v (Set.Icc a b)) :
    (∫ t in a..b, u t * v t) ^ 2 ≤ (∫ t in a..b, u t ^ 2) * (∫ t in a..b, v t ^ 2) := by
  have hmu : MemLp u 2 (volume.restrict (Set.Icc a b)) := by
    rw [MeasureTheory.memLp_two_iff_integrable_sq (hu.aestronglyMeasurable measurableSet_Icc)]
    exact (hu.pow 2).integrableOn_compact isCompact_Icc
  have hmv : MemLp v 2 (volume.restrict (Set.Icc a b)) := by
    rw [MeasureTheory.memLp_two_iff_integrable_sq (hv.aestronglyMeasurable measurableSet_Icc)]
    exact (hv.pow 2).integrableOn_compact isCompact_Icc
  have hcs := Work.Spaces.cs_integral hmu hmv
  have h1 : (∫ t in a..b, u t * v t) = ∫ t in Set.Icc a b, u t * v t := by
    rw [intervalIntegral.integral_of_le hab.le]
    exact MeasureTheory.setIntegral_congr_set (MeasureTheory.Ioc_ae_eq_Icc (μ := volume))
  have h2 : (∫ t in a..b, u t ^ 2) = ∫ t in Set.Icc a b, u t ^ 2 := by
    rw [intervalIntegral.integral_of_le hab.le]
    exact MeasureTheory.setIntegral_congr_set (MeasureTheory.Ioc_ae_eq_Icc (μ := volume))
  have h3 : (∫ t in a..b, v t ^ 2) = ∫ t in Set.Icc a b, v t ^ 2 := by
    rw [intervalIntegral.integral_of_le hab.le]
    exact MeasureTheory.setIntegral_congr_set (MeasureTheory.Ioc_ae_eq_Icc (μ := volume))
  rw [h1, h2, h3]
  exact hcs

/-! ## The boundary term at the singular end -/

/-- Auxiliary: the Cauchy–Schwarz step on a subinterval `[y,y']` of the open quadrant,
`(∫ cos·V)² ≤ (∫ cos²·sin(2·)^η)·(∫ V²·ν)`. -/
theorem cs_cosV_sq {Ψ : ℝ → ℝ → ℝ} {z : ℝ} (hsm : Work.FTS.EllipticEst.SmoothOpen Ψ)
    (hz : 0 < z) {y y' : ℝ} (hy : 0 < y) (hy' : y' < π / 2) (hyy' : y < y') :
    (∫ t in y..y', Real.cos t * pinV Ψ z t) ^ 2
      ≤ (∫ t in y..y', (Real.cos t) ^ 2 * (Real.sin (2 * t)) ^ (Work.Spaces.eta))
        * (∫ t in y..y', (pinV Ψ z t) ^ 2 * wNu t) := by
  have hsubIcc : Set.Icc y y' ⊆ Set.Ioo 0 (π / 2) := fun t ht =>
    ⟨lt_of_lt_of_le hy ht.1, lt_of_le_of_lt ht.2 hy'⟩
  have hsin : ContinuousOn (fun t : ℝ => Real.sin (2 * t)) (Set.Icc y y') :=
    (Real.continuous_sin.comp (continuous_const.mul continuous_id)).continuousOn
  have hu : ContinuousOn (fun t : ℝ => Real.cos t * (Real.sin (2 * t)) ^ (Work.Spaces.eta / 2))
      (Set.Icc y y') :=
    (Real.continuous_cos.continuousOn).mul
      (hsin.rpow_const (fun t ht => Or.inl (ne_of_gt (sin_two_pos_of_mem_Ioo (hsubIcc ht)))))
  have hv : ContinuousOn (fun t : ℝ => pinV Ψ z t * (Real.sin (2 * t)) ^ (-(Work.Spaces.eta / 2)))
      (Set.Icc y y') :=
    (continuousOn_pinV hsm hz (fun t ht => hsubIcc ht)).mul
      (hsin.rpow_const (fun t ht => Or.inl (ne_of_gt (sin_two_pos_of_mem_Ioo (hsubIcc ht)))))
  have hcs := cs_subinterval hyy' hu hv
  have e1 : (∫ t in y..y', (Real.cos t * (Real.sin (2 * t)) ^ (Work.Spaces.eta / 2))
        * (pinV Ψ z t * (Real.sin (2 * t)) ^ (-(Work.Spaces.eta / 2))))
      = ∫ t in y..y', Real.cos t * pinV Ψ z t := by
    refine intervalIntegral.integral_congr fun t ht => ?_
    have htI : t ∈ Set.Icc y y' := Set.uIcc_of_le hyy'.le ▸ ht
    have hpos : 0 < Real.sin (2 * t) := sin_two_pos_of_mem_Ioo (hsubIcc htI)
    have hrp : (Real.sin (2 * t)) ^ (Work.Spaces.eta / 2)
        * (Real.sin (2 * t)) ^ (-(Work.Spaces.eta / 2)) = 1 := by
      rw [← Real.rpow_add hpos, show Work.Spaces.eta / 2 + (-(Work.Spaces.eta / 2)) = 0 by ring,
        Real.rpow_zero]
    calc Real.cos t * (Real.sin (2 * t)) ^ (Work.Spaces.eta / 2)
          * (pinV Ψ z t * (Real.sin (2 * t)) ^ (-(Work.Spaces.eta / 2)))
        = Real.cos t * pinV Ψ z t * ((Real.sin (2 * t)) ^ (Work.Spaces.eta / 2)
            * (Real.sin (2 * t)) ^ (-(Work.Spaces.eta / 2))) := by ring
      _ = Real.cos t * pinV Ψ z t := by rw [hrp, mul_one]
  have e2 : (∫ t in y..y', (Real.cos t * (Real.sin (2 * t)) ^ (Work.Spaces.eta / 2)) ^ 2)
      = ∫ t in y..y', (Real.cos t) ^ 2 * (Real.sin (2 * t)) ^ (Work.Spaces.eta) := by
    refine intervalIntegral.integral_congr fun t ht => ?_
    have htI : t ∈ Set.Icc y y' := Set.uIcc_of_le hyy'.le ▸ ht
    have hpos : 0 < Real.sin (2 * t) := sin_two_pos_of_mem_Ioo (hsubIcc htI)
    have h1 : (Real.sin (2 * t) ^ (Work.Spaces.eta / 2)) ^ 2
        = Real.sin (2 * t) ^ Work.Spaces.eta := by
      rw [sq, ← Real.rpow_add hpos (Work.Spaces.eta / 2) (Work.Spaces.eta / 2),
        show Work.Spaces.eta / 2 + Work.Spaces.eta / 2 = Work.Spaces.eta by ring]
    simp only [mul_pow]
    rw [h1]
  have e3 : (∫ t in y..y', (pinV Ψ z t * (Real.sin (2 * t)) ^ (-(Work.Spaces.eta / 2))) ^ 2)
      = ∫ t in y..y', (pinV Ψ z t) ^ 2 * wNu t := by
    refine intervalIntegral.integral_congr fun t ht => ?_
    have htI : t ∈ Set.Icc y y' := Set.uIcc_of_le hyy'.le ▸ ht
    have hpos : 0 < Real.sin (2 * t) := sin_two_pos_of_mem_Ioo (hsubIcc htI)
    have h1 : (Real.sin (2 * t) ^ (-(Work.Spaces.eta / 2))) ^ 2
        = Real.sin (2 * t) ^ (-(Work.Spaces.eta)) := by
      rw [sq, ← Real.rpow_add hpos (-(Work.Spaces.eta / 2)) (-(Work.Spaces.eta / 2)),
        show -(Work.Spaces.eta / 2) + (-(Work.Spaces.eta / 2)) = -(Work.Spaces.eta) by ring]
    simp only [mul_pow, wNu]
    rw [h1]
  rw [e1, e2, e3] at hcs
  exact hcs

end Work.FTS_EllLimOK.PkgJets
