import Mathlib
import Submission.Work.WilC4aP.Basic
import Submission.Work.WilC4aP.analyticAt_Pz_eval

set_option autoImplicit false
noncomputable section
open Classical Topology Filter
open scoped BigOperators

namespace Work.WilC4aP

open Polynomial

/-- Analytic implicit function theorem, in the form needed here: a simple root of the fibre
of a monic polynomial with holomorphic coefficients lifts to a holomorphic root in the base
variable.

PROOF HINT: reduce to the analytic inverse function theorem
(`OpenPartialHomeomorph.hasFPowerSeriesAt_symm`, from Mathlib's `Analysis.Analytic.Inverse`):
apply it to `(z, Y) ↦ (z, Pz P z |>.eval Y)` near `(0, α)`, whose derivative in `Y` is
non-zero, and take the second coordinate of the inverse; the result is holomorphic by
`HasFPowerSeriesAt.analyticAt`. -/
theorem exists_analytic_root_of_simple (P : Polynomial (ℂ → ℂ)) (hmon : P.Monic)
    (han : Work.WilC4aP.HolCoeffs P 0) {α : ℂ} (hα : (Work.WilC4aP.Pz P 0).eval α = 0)
    (hder : (Work.WilC4aP.Pz P 0).derivative.eval α ≠ 0) :
    ∃ (ζ : ℂ → ℂ) (ρ : ℝ), 0 < ρ ∧ AnalyticOnNhd ℂ ζ (Metric.ball 0 ρ) ∧ ζ 0 = α ∧
      ∀ z ∈ Metric.ball (0 : ℂ) ρ, (Work.WilC4aP.Pz P z).eval (ζ z) = 0 := by
  -- The value of the `Y`-derivative at the root.
  set B : ℂ := (Pz P 0).derivative.eval α with hB
  have hBne : B ≠ 0 := by rw [hB]; exact hder
  -- The `Y`-variation of the fibre, as a function of `(z, Y)`.
  set Ψ : ℂ × ℂ → ℂ := fun p => (Pz P p.1).eval p.2 with hΨdef
  have hΨan : AnalyticAt ℂ Ψ (0, α) := by
    rw [hΨdef]; exact analyticAt_Pz_eval P han α
  have hΨdiff : DifferentiableAt ℂ Ψ (0, α) := hΨan.differentiableAt
  -- The partial derivative of `Ψ` in the `Y`-direction is multiplication by `B`.
  have hY : ∀ y : ℂ, (fderiv ℂ Ψ (0, α)) ((0 : ℂ), y) = B * y := by
    intro y
    have hfun : (fun Y : ℂ => Ψ ((0 : ℂ), Y)) = (fun Y : ℂ => (Pz P 0).eval Y) := by
      funext Y; simp [hΨdef]
    have h2 : HasFDerivAt (fun Y : ℂ => ((0 : ℂ), Y)) (ContinuousLinearMap.inr ℂ ℂ ℂ) α :=
      hasFDerivAt_prodMk_right (0 : ℂ) α
    have hc : HasFDerivAt (fun Y : ℂ => Ψ ((0 : ℂ), Y))
        ((fderiv ℂ Ψ (0, α)).comp (ContinuousLinearMap.inr ℂ ℂ ℂ)) α :=
      HasFDerivAt.comp (f := fun Y : ℂ => ((0 : ℂ), Y)) (f' := ContinuousLinearMap.inr ℂ ℂ ℂ)
        (x := α) (g := Ψ) (g' := fderiv ℂ Ψ (0, α)) hΨdiff.hasFDerivAt h2
    have hcomp : fderiv ℂ (fun Y : ℂ => Ψ ((0 : ℂ), Y)) α
        = (fderiv ℂ Ψ (0, α)).comp (ContinuousLinearMap.inr ℂ ℂ ℂ) := by
      simpa using hc.fderiv
    calc (fderiv ℂ Ψ (0, α)) ((0 : ℂ), y)
        = ((fderiv ℂ Ψ (0, α)).comp (ContinuousLinearMap.inr ℂ ℂ ℂ)) y := by simp
      _ = (fderiv ℂ (fun Y : ℂ => Ψ ((0 : ℂ), Y)) α) y := by rw [hcomp]
      _ = (fderiv ℂ (fun Y : ℂ => (Pz P 0).eval Y) α) y := by rw [hfun]
      _ = B * y := by rw [fderiv_eq_deriv_mul]; simp [hB]
  -- So the full derivative of `Ψ` is `A • fst + B • snd`.
  set A : ℂ := (fderiv ℂ Ψ (0, α)) ((1 : ℂ), (0 : ℂ)) with hA
  have hTf : fderiv ℂ Ψ (0, α)
      = A • ContinuousLinearMap.fst ℂ ℂ ℂ + B • ContinuousLinearMap.snd ℂ ℂ ℂ := by
    refine ContinuousLinearMap.ext fun p => ?_
    have hp : p = p.1 • ((1 : ℂ), (0 : ℂ)) + p.2 • ((0 : ℂ), (1 : ℂ)) := by
      refine Prod.ext ?_ ?_ <;> simp
    conv_lhs => rw [hp]
    rw [map_add, map_smul, map_smul, ← hA, hY 1]
    simp
    ring
  -- The map `(z, Y) ↦ (z, Ψ z Y)`.
  set Φ : ℂ × ℂ → ℂ × ℂ := fun p => (p.1, Ψ p) with hΦdef
  have hΦan : AnalyticAt ℂ Φ (0, α) := by
    rw [hΦdef]
    exact ((ContinuousLinearMap.fst ℂ ℂ ℂ).analyticAt (0, α)).prod hΨan
  have hΨstr : HasStrictFDerivAt Ψ
      (A • ContinuousLinearMap.fst ℂ ℂ ℂ + B • ContinuousLinearMap.snd ℂ ℂ ℂ) (0, α) := by
    rw [← hTf]
    exact hΨan.hasStrictFDerivAt
  set T : (ℂ × ℂ) →L[ℂ] (ℂ × ℂ) :=
    (ContinuousLinearMap.fst ℂ ℂ ℂ).prod
      (A • ContinuousLinearMap.fst ℂ ℂ ℂ + B • ContinuousLinearMap.snd ℂ ℂ ℂ) with hT
  have hΦstr : HasStrictFDerivAt Φ T (0, α) := by
    rw [hT, hΦdef]
    exact (hasStrictFDerivAt_fst).prodMk hΨstr
  -- `T` is invertible, with the explicit inverse `T'`.
  set T' : (ℂ × ℂ) →L[ℂ] (ℂ × ℂ) :=
    (ContinuousLinearMap.fst ℂ ℂ ℂ).prod
      (B⁻¹ • ContinuousLinearMap.snd ℂ ℂ ℂ - (B⁻¹ * A) • ContinuousLinearMap.fst ℂ ℂ ℂ)
    with hT'
  have key₁ : ∀ u : ℂ × ℂ, A * u.1 + B * (B⁻¹ * u.2 - B⁻¹ * A * u.1) = u.2 := by
    intro u
    calc A * u.1 + B * (B⁻¹ * u.2 - B⁻¹ * A * u.1)
        = A * u.1 + B * (B⁻¹ * u.2) - B * (B⁻¹ * A * u.1) := by ring
      _ = A * u.1 + (B * B⁻¹) * u.2 - ((B * B⁻¹) * A) * u.1 := by ring
      _ = u.2 := by rw [mul_inv_cancel₀ hBne]; ring
  have key₂ : ∀ u : ℂ × ℂ, B⁻¹ * (A * u.1 + B * u.2) - B⁻¹ * A * u.1 = u.2 := by
    intro u
    calc B⁻¹ * (A * u.1 + B * u.2) - B⁻¹ * A * u.1
        = B⁻¹ * A * u.1 + (B⁻¹ * B) * u.2 - B⁻¹ * A * u.1 := by ring
      _ = u.2 := by rw [inv_mul_cancel₀ hBne]; ring
  have hcomp₁ : T ∘SL T' = ContinuousLinearMap.id ℂ (ℂ × ℂ) := by
    refine ContinuousLinearMap.ext fun u => ?_
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply, hT, hT',
      ContinuousLinearMap.prod_apply, ContinuousLinearMap.add_apply,
      ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply]
    simp
    exact Prod.ext rfl (key₁ u)
  have hcomp₂ : T' ∘SL T = ContinuousLinearMap.id ℂ (ℂ × ℂ) := by
    refine ContinuousLinearMap.ext fun u => ?_
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply, hT, hT',
      ContinuousLinearMap.prod_apply, ContinuousLinearMap.add_apply,
      ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply]
    simp
    exact Prod.ext rfl (key₂ u)
  obtain ⟨e, he⟩ : ∃ e : (ℂ × ℂ) ≃L[ℂ] (ℂ × ℂ), (e : (ℂ × ℂ) →L[ℂ] (ℂ × ℂ)) = T :=
    ⟨ContinuousLinearEquiv.equivOfInverse' T T' hcomp₁ hcomp₂,
      ContinuousLinearEquiv.toContinuousLinearMap_equivOfInverse' T T' hcomp₁ hcomp₂⟩
  have hΦe : HasStrictFDerivAt Φ (e : (ℂ × ℂ) →L[ℂ] (ℂ × ℂ)) (0, α) := by
    rw [he]; exact hΦstr
  -- The local inverse of `Φ` (an analytic inverse function theorem).
  let Fop : OpenPartialHomeomorph (ℂ × ℂ) (ℂ × ℂ) := hΦe.toOpenPartialHomeomorph Φ
  have hsrc : (0, α) ∈ Fop.source := hΦe.mem_toOpenPartialHomeomorph_source
  have hcoe : (Fop : ℂ × ℂ → ℂ × ℂ) = Φ := hΦe.toOpenPartialHomeomorph_coe
  have hval : Fop (0, α) = (0, 0) := by
    rw [hcoe]
    simp [hΦdef, hΨdef, hα]
  have hsymm : AnalyticAt ℂ (Fop.symm : ℂ × ℂ → ℂ × ℂ) (0, 0) := by
    have key := Fop.analyticAt_symm' hsrc (by rw [hcoe]; exact hΦan)
      (by rw [hcoe]; exact hΦe.hasFDerivAt.fderiv)
    rwa [hval] at key
  -- The holomorphic root.
  set G : ℂ → ℂ × ℂ := fun z => Fop.symm (z, 0) with hG
  have hGan : AnalyticAt ℂ G 0 := by
    rw [hG]
    simpa [Function.comp_def] using
      hsymm.comp (f := fun z : ℂ => ((z, 0) : ℂ × ℂ)) (x := (0 : ℂ))
        ((ContinuousLinearMap.inl ℂ ℂ ℂ).analyticAt 0)
  set ζ : ℂ → ℂ := fun z => (G z).2 with hζ
  have hζan : AnalyticAt ℂ ζ 0 := by
    rw [hζ]
    simpa [Function.comp_def] using
      ((ContinuousLinearMap.snd ℂ ℂ ℂ).analyticAt (G 0)).comp hGan
  obtain ⟨r, hr0, hrz⟩ := hζan.exists_ball_analyticOnNhd
  -- Shrink the ball so that `(z, 0)` stays in the target of `Fop`.
  have hopen : IsOpen {z : ℂ | (z, 0) ∈ Fop.target} :=
    Fop.open_target.preimage (by fun_prop)
  have h0open : (0 : ℂ) ∈ {z : ℂ | (z, 0) ∈ Fop.target} := by
    show ((0 : ℂ), (0 : ℂ)) ∈ Fop.target
    rw [← hval]
    exact Fop.map_source hsrc
  obtain ⟨ε, hε0, hε⟩ := Metric.isOpen_iff.mp hopen 0 h0open
  refine ⟨ζ, min r ε, lt_min hr0 hε0,
    hrz.mono (Metric.ball_subset_ball (min_le_left _ _)), ?_, ?_⟩
  · rw [hζ]
    have h1 : Fop.symm ((0 : ℂ), (0 : ℂ)) = (0, α) := by
      have h := Fop.left_inv hsrc
      rwa [hval] at h
    simp [hG, h1]
  · intro z hz
    have hzT : (z, 0) ∈ Fop.target := hε (Metric.ball_subset_ball (min_le_right _ _) hz)
    have h2 := Fop.right_inv hzT
    have h3 : Φ (Fop.symm ((z, 0))) = ((z, 0) : ℂ × ℂ) := by rwa [hcoe] at h2
    have h4 : (Pz P (Fop.symm ((z, 0))).1).eval (Fop.symm ((z, 0))).2 = 0 := by
      have := congrArg Prod.snd h3
      simpa [hΦdef, hΨdef] using this
    have h5 : (Fop.symm ((z, 0))).1 = z := by
      have := congrArg Prod.fst h3
      simpa [hΦdef, hΨdef] using this
    rw [h5] at h4
    simpa [hζ, hG] using h4

end Work.WilC4aP
