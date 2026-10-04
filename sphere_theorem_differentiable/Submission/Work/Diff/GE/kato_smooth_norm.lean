import Mathlib
import Submission.Work.Diff.GE.kato_defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.GE

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter
open Work.Diff.GE

/-!
# Smoothness and positivity of the smoothed Gram–Schmidt normalisation

This module proves `Work.Diff.GE.kato_smooth_norm`, the regularity statement for the smoothing
device used in the Gram–Schmidt construction of a geodesic orthonormal frame
(`Submission/Work/Diff/GE/kato_defs.lean`).

Recall the definitions: for the Gram function `f = katoGram g V W i` of the pre-normalisation
vector, one sets

`katoNorm g x V W i = f x + (f - f x) * ψ`  and  `katoC g x V W i = (√(katoNorm g x V W i))⁻¹`,

where `ψ = katoBump f x` is a smooth bump which is `1` near `x` and vanishes off `{f > 0}`.

The claims proved here:

* `katoNorm g x V W i > 0` everywhere (a convex combination of `f x > 0` and `f y > 0` on the
  support of `ψ`);
* `katoNorm` and `katoC` are smooth (the latter because `√·` is smooth off `0`, and the inner
  function is strictly positive everywhere);
* `katoC` agrees near `x` with the honest normalisation `(√f)⁻¹` and `katoNorm` agrees near `x`
  with `f`; at `x` itself, `katoNorm g x V W i x = f x` exactly.

The existence of the bump `ψ` (a smooth bump function on the manifold, supported in the open set
`{f > 0}`) is proved here from Mathlib's `SmoothBumpFunction`, so that this module does not depend
on the separate lemma `kato_bump_pos`.
-/

/-- The existence of the smoothing bump of `katoBump`: for a smooth `f : M → ℝ` with `f x > 0`
there is a smooth `ψ : M → ℝ` with values in `[0,1]`, equal to `1` near `x`, and positive only
where `f` is positive. -/
theorem kato_bump_exists
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M] [IsManifold I ∞ M]
    (f : M → ℝ) (x : M) (hf : CMDiff ∞ f) (hpos : 0 < f x) :
    ∃ ψ : M → ℝ,
      CMDiff ∞ ψ ∧ (∀ y, 0 ≤ ψ y) ∧ (∀ y, ψ y ≤ 1) ∧
        (∀ y, 0 < ψ y → 0 < f y) ∧ (ψ =ᶠ[𝓝 x] 1) := by
  have hcont : Continuous f := hf.continuous
  have hmem : {y : M | 0 < f y} ∈ 𝓝 x := (isOpen_lt continuous_const hcont).mem_nhds hpos
  obtain ⟨ψ, hψtsup, -⟩ :=
    (SmoothBumpFunction.nhds_basis_support (I := I) (c := x) hmem).mem_iff.mp Filter.univ_mem
  refine ⟨ψ, ψ.contMDiff, fun y => ψ.nonneg, fun y => ψ.le_one, ?_, ψ.eventuallyEq_one⟩
  intro y hy
  exact hψtsup (subset_closure (by simpa [Function.mem_support] using hy.ne'))

theorem kato_smooth_norm
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M] [IsManifold I ∞ M]
    (g : SMet I M) (x : M) (V W : katoIdx E → Π y : M, TangentSpace I y) (i : katoIdx E)
    (hf : CMDiff ∞ (katoGram g V W i)) (hfx : 0 < katoGram g V W i x) :
    (∀ y, 0 < katoNorm g x V W i y) ∧ CMDiff ∞ (katoNorm g x V W i) ∧
      CMDiff ∞ (katoC g x V W i) ∧
      (katoC g x V W i =ᶠ[𝓝 x] fun y => (Real.sqrt (katoGram g V W i y))⁻¹) ∧
      katoNorm g x V W i x = katoGram g V W i x ∧
      (katoNorm g x V W i =ᶠ[𝓝 x] katoGram g V W i) := by
  obtain ⟨hψsm, hψ0, hψ1, hψpos, hψeq⟩ :=
    katoBump_spec' (I := I) (kato_bump_exists (I := I) (katoGram g V W i) x hf hfx)
  have hNormEq : katoNorm g x V W i =ᶠ[𝓝 x] katoGram g V W i := by
    filter_upwards [hψeq] with y hy
    have hy' : katoBump (I := I) (katoGram g V W i) x y = 1 := by simpa using hy
    rw [katoNorm_apply, hy']
    ring
  have hpos : ∀ y, 0 < katoNorm g x V W i y := by
    intro y
    rw [katoNorm_apply]
    rcases lt_or_eq_of_le (hψ0 y) with h | h
    · have hfy : 0 < katoGram g V W i y := hψpos y h
      have h1 : 0 ≤ katoGram g V W i x * (1 - katoBump (I := I) (katoGram g V W i) x y) :=
        mul_nonneg (le_of_lt hfx) (by linarith [hψ1 y])
      have h2 : 0 < katoGram g V W i y * katoBump (I := I) (katoGram g V W i) x y :=
        mul_pos hfy h
      have he : katoGram g V W i x +
          (katoGram g V W i y - katoGram g V W i x) * katoBump (I := I) (katoGram g V W i) x y
          = katoGram g V W i x * (1 - katoBump (I := I) (katoGram g V W i) x y)
            + katoGram g V W i y * katoBump (I := I) (katoGram g V W i) x y := by ring
      rw [he]; linarith
    · rw [← h, mul_zero, add_zero]; exact hfx
  have hsm : CMDiff ∞ (katoNorm g x V W i) := by
    show ContMDiff I 𝓘(ℝ, ℝ) ∞ (fun y : M => katoGram g V W i x +
      (katoGram g V W i y - katoGram g V W i x) * katoBump (I := I) (katoGram g V W i) x y)
    exact contMDiff_const.add ((hf.sub contMDiff_const).mul hψsm)
  have hc : CMDiff ∞ (katoC g x V W i) := by
    show ∀ y : M, ContMDiffAt I 𝓘(ℝ, ℝ) ∞ (fun y : M => (Real.sqrt (katoNorm g x V W i y))⁻¹) y
    intro y
    have hat : ContMDiffAt I 𝓘(ℝ, ℝ) ∞ (katoNorm g x V W i) y := hsm y
    have hs : ContMDiffAt I 𝓘(ℝ, ℝ) ∞ (fun z : M => Real.sqrt (katoNorm g x V W i z)) y :=
      ContMDiffAt.comp y (contMDiffAt_iff_contDiffAt.mpr (Real.contDiffAt_sqrt (hpos y).ne')) hat
    exact ContMDiffAt.inv₀ hs (Real.sqrt_pos.mpr (hpos y)).ne'
  have hCEq : katoC g x V W i =ᶠ[𝓝 x] fun y => (Real.sqrt (katoGram g V W i y))⁻¹ := by
    filter_upwards [hNormEq] with y hy
    simp only [katoC_apply, hy]
  have hx : katoNorm g x V W i x = katoGram g V W i x := by
    simp [katoNorm_apply]
  exact ⟨hpos, hsm, hc, hCEq, hx, hNormEq⟩

end Work.Diff.GE
