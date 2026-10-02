import Mathlib
import Submission.Work.MRMT.Basic
import Submission.Work.MRMT.Wirtinger.dz_comp
import Submission.Work.MRMT.Wirtinger.dzbar_comp

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# Translating the weak Wirtinger relation

`weak_relation_at_translate`: if the weak (distributional) relations
`∫ D ψ = -∫ φ ∂ψ` and `∫ E ψ = -∫ φ ∂̄ψ` hold for every `C¹` test function `ψ` whose
support lies in `Metric.ball 0 R`, then they also hold, translated by `z`, for a `C¹` test
function `η` whose `z`-translate `w ↦ η (w - z)` has support in that ball.

The proof is the change of variables `w = z + u` (invariance of Lebesgue measure under
translation, `MeasureTheory.integral_add_left_eq_self`) together with the chain rule for
`dz`/`dzbar` along the translation `w ↦ w - z`
(`Work.MRMT.Wirtinger.dz_comp`, `Work.MRMT.Wirtinger.dzbar_comp`).
-/

open MeasureTheory Complex Function Filter
open scoped Distributions Topology ENNReal

namespace Work.MRMT.Found

/-! ## Wirtinger derivatives of a translate

For a function `f` and a shift `c`, `t ↦ f (t - c)` has the same `dz`/`dzbar` as `f`,
evaluated at `t - c`: the translation `t ↦ t - c` is a real-affine map with `∂ = 1` and
`∂̄ = 0`, so the chain rule collapses. -/

private lemma hasFDerivAt_sub_const_id (c w : ℂ) :
    HasFDerivAt (fun t : ℂ => t - c) (ContinuousLinearMap.id ℝ ℂ) w := by
  simpa using (hasFDerivAt_id w).sub_const c

private lemma dz_sub_const_eq (c w : ℂ) : Work.MRMT.dz (fun t : ℂ => t - c) w = 1 := by
  simp only [Work.MRMT.dz, (hasFDerivAt_sub_const_id c w).fderiv, ContinuousLinearMap.id_apply]
  norm_num [Complex.I_mul_I]

private lemma dzbar_sub_const_eq (c w : ℂ) : Work.MRMT.dzbar (fun t : ℂ => t - c) w = 0 := by
  simp only [Work.MRMT.dzbar, (hasFDerivAt_sub_const_id c w).fderiv,
    ContinuousLinearMap.id_apply]
  norm_num [Complex.I_mul_I]

private lemma dz_shift (f : ℂ → ℂ) (c : ℂ) (hf : Differentiable ℝ f) (w : ℂ) :
    Work.MRMT.dz (fun t => f (t - c)) w = Work.MRMT.dz f (w - c) := by
  have hT : DifferentiableAt ℝ (fun t : ℂ => t - c) w := differentiableAt_id.sub_const c
  have hf' : DifferentiableAt ℝ f (w - c) := hf.differentiableAt
  rw [show (fun t : ℂ => f (t - c)) = (f ∘ fun t : ℂ => t - c) from rfl]
  rw [Work.MRMT.Wirtinger.dz_comp (f := fun t : ℂ => t - c) (g := f) (z := w) hf' hT,
    dz_sub_const_eq c w, dzbar_sub_const_eq c w]
  simp

private lemma dzbar_shift (f : ℂ → ℂ) (c : ℂ) (hf : Differentiable ℝ f) (w : ℂ) :
    Work.MRMT.dzbar (fun t => f (t - c)) w = Work.MRMT.dzbar f (w - c) := by
  have hT : DifferentiableAt ℝ (fun t : ℂ => t - c) w := differentiableAt_id.sub_const c
  have hf' : DifferentiableAt ℝ f (w - c) := hf.differentiableAt
  rw [show (fun t : ℂ => f (t - c)) = (f ∘ fun t : ℂ => t - c) from rfl]
  rw [Work.MRMT.Wirtinger.dzbar_comp (f := fun t : ℂ => t - c) (g := f) (z := w) hf' hT,
    dz_sub_const_eq c w, dzbar_sub_const_eq c w]
  simp

/-! ## The translation lemma -/

theorem weak_relation_at_translate {φ D E : ℂ → ℂ} {R : ℝ}
    (hweak : ∀ ψ : ℂ → ℂ, ContDiff ℝ 1 ψ → HasCompactSupport ψ → tsupport ψ ⊆ Metric.ball 0 R →
      (∫ z, D z * ψ z = -∫ z, φ z * Work.MRMT.dz ψ z) ∧
      (∫ z, E z * ψ z = -∫ z, φ z * Work.MRMT.dzbar ψ z))
    {η : ℂ → ℂ} (hη : ContDiff ℝ 1 η) (hηs : HasCompactSupport η) (z : ℂ)
    (hsub : tsupport (fun w => η (w - z)) ⊆ Metric.ball 0 R) :
    (∫ u, φ (z + u) * Work.MRMT.dz η u = -∫ u, D (z + u) * η u) ∧
    (∫ u, φ (z + u) * Work.MRMT.dzbar η u = -∫ u, E (z + u) * η u) := by
  -- the test function obtained by translating `η` back by `z`
  set ψ : ℂ → ℂ := fun w => η (w - z) with hψdef
  have hψc : ContDiff ℝ 1 ψ := by
    rw [hψdef]; exact hη.comp (contDiff_id.sub contDiff_const)
  have hψs : HasCompactSupport ψ := by
    have h := hηs.comp_homeomorph (Homeomorph.subRight z)
    rw [hψdef]
    simpa [Function.comp_def] using h
  have hsub' : tsupport ψ ⊆ Metric.ball 0 R := by rw [hψdef]; exact hsub
  obtain ⟨hD, hE⟩ := hweak ψ hψc hψs hsub'
  have hηd : Differentiable ℝ η := hη.differentiable (by norm_num)
  have hz : ∀ w, Work.MRMT.dz ψ w = Work.MRMT.dz η (w - z) := by
    intro w; rw [hψdef]; exact dz_shift η z hηd w
  have hzb : ∀ w, Work.MRMT.dzbar ψ w = Work.MRMT.dzbar η (w - z) := by
    intro w; rw [hψdef]; exact dzbar_shift η z hηd w
  constructor
  · -- `∫ D ψ = -∫ φ ∂ψ`
    have hL : (∫ w, D w * ψ w) = ∫ u, D (z + u) * η u := by
      have h1 : (∫ w, D w * η (w - z)) = ∫ u, (fun v => D v * η (v - z)) (z + u) :=
        (MeasureTheory.integral_add_left_eq_self (fun v => D v * η (v - z)) z).symm
      have h2 : (∫ u, (fun v => D v * η (v - z)) (z + u)) = ∫ u, D (z + u) * η u := by
        refine MeasureTheory.integral_congr_ae (Eventually.of_forall fun u => ?_)
        simp only [add_sub_cancel_left]
      rw [hψdef]; exact h1.trans h2
    have hR : (∫ w, φ w * Work.MRMT.dz ψ w) = ∫ u, φ (z + u) * Work.MRMT.dz η u := by
      have e : (∫ w, φ w * Work.MRMT.dz ψ w) = ∫ w, φ w * Work.MRMT.dz η (w - z) :=
        MeasureTheory.integral_congr_ae (Eventually.of_forall fun w => by simp only [hz w])
      rw [e]
      have h1 : (∫ w, φ w * Work.MRMT.dz η (w - z))
          = ∫ u, (fun v => φ v * Work.MRMT.dz η (v - z)) (z + u) :=
        (MeasureTheory.integral_add_left_eq_self (fun v => φ v * Work.MRMT.dz η (v - z)) z).symm
      have h2 : (∫ u, (fun v => φ v * Work.MRMT.dz η (v - z)) (z + u))
          = ∫ u, φ (z + u) * Work.MRMT.dz η u := by
        refine MeasureTheory.integral_congr_ae (Eventually.of_forall fun u => ?_)
        simp only [add_sub_cancel_left]
      exact h1.trans h2
    rw [hL, hR] at hD
    have hneg := congrArg Neg.neg hD
    simp only [neg_neg] at hneg
    exact hneg.symm
  · -- `∫ E ψ = -∫ φ ∂̄ψ`
    have hL : (∫ w, E w * ψ w) = ∫ u, E (z + u) * η u := by
      have h1 : (∫ w, E w * η (w - z)) = ∫ u, (fun v => E v * η (v - z)) (z + u) :=
        (MeasureTheory.integral_add_left_eq_self (fun v => E v * η (v - z)) z).symm
      have h2 : (∫ u, (fun v => E v * η (v - z)) (z + u)) = ∫ u, E (z + u) * η u := by
        refine MeasureTheory.integral_congr_ae (Eventually.of_forall fun u => ?_)
        simp only [add_sub_cancel_left]
      rw [hψdef]; exact h1.trans h2
    have hR : (∫ w, φ w * Work.MRMT.dzbar ψ w) = ∫ u, φ (z + u) * Work.MRMT.dzbar η u := by
      have e : (∫ w, φ w * Work.MRMT.dzbar ψ w) = ∫ w, φ w * Work.MRMT.dzbar η (w - z) :=
        MeasureTheory.integral_congr_ae (Eventually.of_forall fun w => by simp only [hzb w])
      rw [e]
      have h1 : (∫ w, φ w * Work.MRMT.dzbar η (w - z))
          = ∫ u, (fun v => φ v * Work.MRMT.dzbar η (v - z)) (z + u) :=
        (MeasureTheory.integral_add_left_eq_self (fun v => φ v * Work.MRMT.dzbar η (v - z)) z).symm
      have h2 : (∫ u, (fun v => φ v * Work.MRMT.dzbar η (v - z)) (z + u))
          = ∫ u, φ (z + u) * Work.MRMT.dzbar η u := by
        refine MeasureTheory.integral_congr_ae (Eventually.of_forall fun u => ?_)
        simp only [add_sub_cancel_left]
      exact h1.trans h2
    rw [hL, hR] at hE
    have hneg := congrArg Neg.neg hE
    simp only [neg_neg] at hneg
    exact hneg.symm

end Work.MRMT.Found
