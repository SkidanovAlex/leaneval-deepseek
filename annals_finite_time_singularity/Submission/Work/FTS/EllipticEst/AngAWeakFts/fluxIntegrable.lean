/-
Copyright: work module for the Elgindi finite-time singularity project.

# Integrability of the four Hardy fluxes

The Hardy argument for
`∫_{Iθ} f² cos²(2θ) sin(2θ)^{-(2+η)} ≤ (1+η)^{-2} ∫_{Iθ} (f')² sin(2θ)^{-η}`
integrates the identity `Φ' = 2G - 2B - 2(1+η)L` of
`Submission/Work/FTS/EllipticEst/AngAWeakFts/fluxDeriv.lean` over `Iθ`.  For that every one of
the four integrands

* `L = f² cos²(2θ) sin(2θ)^{-(2+η)}`,
* `B = f² sin(2θ)^{-η}`,
* `G = f' f cos(2θ) sin(2θ)^{-(1+η)}`,
* `D = (f')² sin(2θ)^{-η}`

has to be interval integrable on `[0, π/2]`.  This file proves that, in the *weak* class where
`f` is only of class `C²` on the **open** interval `(0, π/2)` (so the endpoint values of `f` and
`deriv f` are not controlled) and the two hypotheses hold there:

* `|f θ| ≤ M sin(2θ)`,
* `|deriv f θ| ≤ M`,

with `0 ≤ M`.  The two bounds give, for `θ ∈ (0, π/2)`, the *single* pointwise domination

  `|L θ|, |B θ|, |G θ|, |D θ| ≤ M² sin(2θ)^{-η}`

(`hardyFtsBounds`), which is integrable on `(0, π/2)` for `η < 1`; a.e. strong measurability on
that open interval follows from continuity (`hardyFtsAesm`).  The reduction to the interval
integral is `intervalIntegrable_of_sin_bound_Ioo`.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Order.CompletePartialOrder
import Submission.Work.FTS.EllipticEst.AngAWeakFts.Defs
import Submission.Work.FTS.H2.STBasic

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.AngAWeakFts

open Work.FTS.EllipticEst.AngAWeak

set_option autoImplicit false

/-! ## Auxiliary lemmas -/

/-- A function which is dominated on the *open* interval `(0, π/2)` by `C · sin(2θ)^p`, with
`p > -1`, is interval integrable on `[0, π/2]`: the majorant is integrable
(`Work.FTS.H2.intervalIntegrable_sin_rpow`) and the two sets differ by a null set. -/
theorem intervalIntegrable_of_sin_bound_Ioo {g : ℝ → ℝ} {C p : ℝ} (hp : -1 < p)
    (hmeas : AEStronglyMeasurable g (volume.restrict (Set.Ioo 0 (π / 2))))
    (h : ∀ θ ∈ Set.Ioo 0 (π / 2), |g θ| ≤ C * (Real.sin (2 * θ)) ^ p) :
    IntervalIntegrable g volume 0 (π / 2) := by
  have hle : (0 : ℝ) ≤ π / 2 := by positivity
  have hae : Set.Ioo (0 : ℝ) (π / 2) =ᵐ[volume] Set.Ioc (0 : ℝ) (π / 2) :=
    MeasureTheory.Ioo_ae_eq_Ioc (μ := volume)
  have hmaj : IntegrableOn (fun θ : ℝ => C * (Real.sin (2 * θ)) ^ p) (Set.Ioo 0 (π / 2)) := by
    have h0 : IntegrableOn (fun θ : ℝ => (Real.sin (2 * θ)) ^ p) (Set.Ioc 0 (π / 2)) :=
      (intervalIntegrable_iff_integrableOn_Ioc_of_le hle).mp
        (Work.FTS.H2.intervalIntegrable_sin_rpow p hp)
    exact IntegrableOn.congr_set_ae (h0.const_mul C) hae
  have hInt : IntegrableOn g (Set.Ioo 0 (π / 2)) :=
    Integrable.mono' hmaj hmeas
      (ae_restrict_of_forall_mem measurableSet_Ioo (fun θ hθ => by
        rw [Real.norm_eq_abs]; exact h θ hθ))
  exact (intervalIntegrable_iff_integrableOn_Ioc_of_le hle).mpr
    (IntegrableOn.congr_set_ae hInt hae.symm)

/-- The four Hardy integrands are a.e. strongly measurable on the open angular interval: each of
them is continuous there (`f` because it is `C²`, `deriv f` because it is `C¹`, and the
`sin(2θ)^{-q}` factors because `sin(2θ) > 0` on the open interval). -/
theorem hardyFtsAesm (η : ℝ) {f : ℝ → ℝ}
    (hf : ContDiffOn ℝ 2 f (Set.Ioo 0 (π / 2))) :
    AEStronglyMeasurable (hardyFtsL η f) (volume.restrict (Set.Ioo 0 (π / 2))) ∧
      AEStronglyMeasurable (hardyFtsB η f) (volume.restrict (Set.Ioo 0 (π / 2))) ∧
      AEStronglyMeasurable (hardyFtsG η f) (volume.restrict (Set.Ioo 0 (π / 2))) ∧
      AEStronglyMeasurable (hardyFtsD η f) (volume.restrict (Set.Ioo 0 (π / 2))) := by
  have hsc : ContinuousOn (fun θ : ℝ => Real.sin (2 * θ)) (Set.Ioo 0 (π / 2)) :=
    (Real.continuous_sin.comp (continuous_const.mul continuous_id)).continuousOn
  have hcc : ContinuousOn (fun θ : ℝ => Real.cos (2 * θ)) (Set.Ioo 0 (π / 2)) :=
    (Real.continuous_cos.comp (continuous_const.mul continuous_id)).continuousOn
  have hfc : ContinuousOn f (Set.Ioo 0 (π / 2)) := hf.continuousOn
  have hdc : ContinuousOn (deriv f) (Set.Ioo 0 (π / 2)) :=
    hf.continuousOn_deriv_of_isOpen isOpen_Ioo (by norm_num)
  have hne : ∀ θ ∈ Set.Ioo 0 (π / 2), Real.sin (2 * θ) ≠ 0 :=
    fun θ hθ => ne_of_gt (hardyFts_sin_pos hθ)
  have hpw : ∀ q : ℝ, ContinuousOn (fun θ : ℝ => (Real.sin (2 * θ)) ^ q) (Set.Ioo 0 (π / 2)) :=
    fun q => hsc.rpow_const (fun θ hθ => Or.inl (hne θ hθ))
  have hLc : ContinuousOn (hardyFtsL η f) (Set.Ioo 0 (π / 2)) := by
    unfold hardyFtsL
    exact ((hfc.pow 2).mul (hcc.pow 2)).mul (hpw (-(2 + η)))
  have hBc : ContinuousOn (hardyFtsB η f) (Set.Ioo 0 (π / 2)) := by
    unfold hardyFtsB
    exact (hfc.pow 2).mul (hpw (-η))
  have hGc : ContinuousOn (hardyFtsG η f) (Set.Ioo 0 (π / 2)) := by
    unfold hardyFtsG
    exact ((hdc.mul hfc).mul hcc).mul (hpw (-(1 + η)))
  have hDc : ContinuousOn (hardyFtsD η f) (Set.Ioo 0 (π / 2)) := by
    unfold hardyFtsD
    exact (hdc.pow 2).mul (hpw (-η))
  exact ⟨hLc.aestronglyMeasurable measurableSet_Ioo,
    hBc.aestronglyMeasurable measurableSet_Ioo,
    hGc.aestronglyMeasurable measurableSet_Ioo,
    hDc.aestronglyMeasurable measurableSet_Ioo⟩

/-- The pointwise domination of the four Hardy integrands by `M² sin(2θ)^{-η}` on the open
angular interval, from `|f θ| ≤ M sin(2θ)` and `|deriv f θ| ≤ M`. -/
theorem hardyFtsBounds (η : ℝ) {f : ℝ → ℝ} {M : ℝ} (hM : 0 ≤ M)
    (hMf : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2), |f θ| ≤ M * Real.sin (2 * θ))
    (hMd : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2), |deriv f θ| ≤ M) :
    ∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
      |hardyFtsL η f θ| ≤ M ^ 2 * (Real.sin (2 * θ)) ^ (-η) ∧
        |hardyFtsB η f θ| ≤ M ^ 2 * (Real.sin (2 * θ)) ^ (-η) ∧
          |hardyFtsG η f θ| ≤ M ^ 2 * (Real.sin (2 * θ)) ^ (-η) ∧
            |hardyFtsD η f θ| ≤ M ^ 2 * (Real.sin (2 * θ)) ^ (-η) := by
  intro θ hθ
  have hs : 0 < Real.sin (2 * θ) := hardyFts_sin_pos hθ
  have hs0 : 0 ≤ Real.sin (2 * θ) := hs.le
  have hfθ : |f θ| ≤ M * Real.sin (2 * θ) := hMf θ hθ
  have hdθ : |deriv f θ| ≤ M := hMd θ hθ
  have hMs : 0 ≤ M * Real.sin (2 * θ) := mul_nonneg hM hs0
  -- squared bounds for `f` and `deriv f`
  have hf2 : (f θ) ^ 2 ≤ (M * Real.sin (2 * θ)) ^ 2 := by
    rw [← sq_abs (f θ)]
    exact pow_le_pow_left₀ (abs_nonneg _) hfθ 2
  have hd2 : (deriv f θ) ^ 2 ≤ M ^ 2 := by
    rw [← sq_abs (deriv f θ)]
    exact pow_le_pow_left₀ (abs_nonneg _) hdθ 2
  have hcos2 : (Real.cos (2 * θ)) ^ 2 ≤ 1 := Real.cos_sq_le_one (2 * θ)
  have hs2 : (Real.sin (2 * θ)) ^ 2 ≤ 1 := Real.sin_sq_le_one (2 * θ)
  -- the two `rpow` identities on the open interval
  have hpow2 : (Real.sin (2 * θ)) ^ (-η)
      = (Real.sin (2 * θ)) ^ 2 * (Real.sin (2 * θ)) ^ (-(2 + η)) := by
    rw [show (-η : ℝ) = (2 : ℝ) + (-(2 + η)) by ring]
    rw [Real.rpow_add hs (2 : ℝ) (-(2 + η)), Real.rpow_two]
  have hpow1 : (Real.sin (2 * θ)) ^ (-η)
      = Real.sin (2 * θ) * (Real.sin (2 * θ)) ^ (-(1 + η)) := by
    rw [show (-η : ℝ) = (1 : ℝ) + (-(1 + η)) by ring]
    rw [Real.rpow_add hs (1 : ℝ) (-(1 + η)), Real.rpow_one]
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- `L = f² cos²(2θ) sin(2θ)^{-(2+η)}`
    have h1 : (f θ) ^ 2 * (Real.cos (2 * θ)) ^ 2
        ≤ (M * Real.sin (2 * θ)) ^ 2 * 1 :=
      mul_le_mul hf2 hcos2 (sq_nonneg _) (sq_nonneg _)
    have h2 : (f θ) ^ 2 * (Real.cos (2 * θ)) ^ 2 * (Real.sin (2 * θ)) ^ (-(2 + η))
        ≤ (M * Real.sin (2 * θ)) ^ 2 * 1 * (Real.sin (2 * θ)) ^ (-(2 + η)) :=
      mul_le_mul_of_nonneg_right h1 (Real.rpow_nonneg hs0 _)
    rw [hardyFtsL, abs_mul, abs_mul, abs_of_nonneg (sq_nonneg (f θ)),
      abs_of_nonneg (sq_nonneg (Real.cos (2 * θ))), abs_of_nonneg (Real.rpow_nonneg hs0 _)]
    calc (f θ) ^ 2 * (Real.cos (2 * θ)) ^ 2 * (Real.sin (2 * θ)) ^ (-(2 + η))
        ≤ (M * Real.sin (2 * θ)) ^ 2 * 1 * (Real.sin (2 * θ)) ^ (-(2 + η)) := h2
      _ = M ^ 2 * ((Real.sin (2 * θ)) ^ 2 * (Real.sin (2 * θ)) ^ (-(2 + η))) := by ring
      _ = M ^ 2 * (Real.sin (2 * θ)) ^ (-η) := by rw [hpow2]
  · -- `B = f² sin(2θ)^{-η}`
    have h1 : (f θ) ^ 2 * (Real.sin (2 * θ)) ^ (-η)
        ≤ (M * Real.sin (2 * θ)) ^ 2 * (Real.sin (2 * θ)) ^ (-η) :=
      mul_le_mul_of_nonneg_right hf2 (Real.rpow_nonneg hs0 _)
    have h3 : (M * Real.sin (2 * θ)) ^ 2 * (Real.sin (2 * θ)) ^ (-η)
        ≤ M ^ 2 * (Real.sin (2 * θ)) ^ (-η) := by
      have h4 : (Real.sin (2 * θ)) ^ 2 * (Real.sin (2 * θ)) ^ (-η)
          ≤ 1 * (Real.sin (2 * θ)) ^ (-η) :=
        mul_le_mul_of_nonneg_right hs2 (Real.rpow_nonneg hs0 _)
      calc (M * Real.sin (2 * θ)) ^ 2 * (Real.sin (2 * θ)) ^ (-η)
          = M ^ 2 * ((Real.sin (2 * θ)) ^ 2 * (Real.sin (2 * θ)) ^ (-η)) := by ring
        _ ≤ M ^ 2 * (1 * (Real.sin (2 * θ)) ^ (-η)) :=
            mul_le_mul_of_nonneg_left h4 (sq_nonneg M)
        _ = M ^ 2 * (Real.sin (2 * θ)) ^ (-η) := by ring
    rw [hardyFtsB, abs_mul, abs_of_nonneg (sq_nonneg (f θ)),
      abs_of_nonneg (Real.rpow_nonneg hs0 _)]
    exact le_trans h1 h3
  · -- `G = f' f cos(2θ) sin(2θ)^{-(1+η)}`
    have hab : |deriv f θ| * |f θ| ≤ M * (M * Real.sin (2 * θ)) :=
      mul_le_mul hdθ hfθ (abs_nonneg _) hM
    have habc : |deriv f θ| * |f θ| * |Real.cos (2 * θ)|
        ≤ M * (M * Real.sin (2 * θ)) * 1 :=
      mul_le_mul hab (Real.abs_cos_le_one (2 * θ)) (abs_nonneg _) (mul_nonneg hM hMs)
    have h1 : |deriv f θ| * |f θ| * |Real.cos (2 * θ)| * (Real.sin (2 * θ)) ^ (-(1 + η))
        ≤ M * (M * Real.sin (2 * θ)) * 1 * (Real.sin (2 * θ)) ^ (-(1 + η)) :=
      mul_le_mul_of_nonneg_right habc (Real.rpow_nonneg hs0 _)
    rw [hardyFtsG, abs_mul, abs_mul, abs_mul, abs_of_nonneg (Real.rpow_nonneg hs0 _)]
    calc |deriv f θ| * |f θ| * |Real.cos (2 * θ)| * (Real.sin (2 * θ)) ^ (-(1 + η))
        ≤ M * (M * Real.sin (2 * θ)) * 1 * (Real.sin (2 * θ)) ^ (-(1 + η)) := h1
      _ = M ^ 2 * (Real.sin (2 * θ) * (Real.sin (2 * θ)) ^ (-(1 + η))) := by ring
      _ = M ^ 2 * (Real.sin (2 * θ)) ^ (-η) := by rw [hpow1]
  · -- `D = (f')² sin(2θ)^{-η}`
    rw [hardyFtsD, abs_mul, abs_of_nonneg (sq_nonneg (deriv f θ)),
      abs_of_nonneg (Real.rpow_nonneg hs0 _)]
    exact mul_le_mul_of_nonneg_right hd2 (Real.rpow_nonneg hs0 _)

/-! ## The target -/

theorem fluxIntegrable (η : ℝ) (hη0 : 0 ≤ η) (hη1 : η < 1) {f : ℝ → ℝ} {M : ℝ}
    (hf : ContDiffOn ℝ 2 f (Set.Ioo 0 (Real.pi / 2))) (hM : 0 ≤ M)
    (hMf : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2), |f θ| ≤ M * Real.sin (2 * θ))
    (hMd : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2), |deriv f θ| ≤ M) :
    IntervalIntegrable (Work.FTS.EllipticEst.AngAWeak.hardyFtsL η f) MeasureTheory.volume
        0 (Real.pi / 2) ∧
      IntervalIntegrable (Work.FTS.EllipticEst.AngAWeak.hardyFtsB η f) MeasureTheory.volume
        0 (Real.pi / 2) ∧
      IntervalIntegrable (Work.FTS.EllipticEst.AngAWeak.hardyFtsG η f) MeasureTheory.volume
        0 (Real.pi / 2) ∧
      IntervalIntegrable (Work.FTS.EllipticEst.AngAWeak.hardyFtsD η f) MeasureTheory.volume
        0 (Real.pi / 2) := by
  obtain ⟨hLm, hBm, hGm, hDm⟩ := hardyFtsAesm η hf
  have hb := hardyFtsBounds η hM hMf hMd
  have hp : (-1 : ℝ) < -η := by linarith
  exact ⟨intervalIntegrable_of_sin_bound_Ioo (C := M ^ 2) (p := -η) hp hLm
      (fun θ hθ => (hb θ hθ).1),
    intervalIntegrable_of_sin_bound_Ioo (C := M ^ 2) (p := -η) hp hBm
      (fun θ hθ => (hb θ hθ).2.1),
    intervalIntegrable_of_sin_bound_Ioo (C := M ^ 2) (p := -η) hp hGm
      (fun θ hθ => (hb θ hθ).2.2.1),
    intervalIntegrable_of_sin_bound_Ioo (C := M ^ 2) (p := -η) hp hDm
      (fun θ hθ => (hb θ hθ).2.2.2)⟩

end Work.FTS.EllipticEst.AngAWeakFts
