import Mathlib
import Submission.Work.WilE3.Taylor.CaseII.ae_regular_level_shear
import Submission.Work.WilE3.Taylor.CaseII.shearMap_hasFDerivAt
import Submission.Work.WilE3.Taylor.CaseII.shearCoord_fderiv_apply

namespace Work.WilE3.Taylor.CaseII

open MeasureTheory

/-- The shear map `H(x,s) = ((s if i = i₀ else -(a x i + b x i * s))_i, φ x)` is critical at
`(x,s)` as soon as the linear map
`ξ ↦ ((dφ_x ξ if i = i₀ else d(a·i + b·i·s)_x ξ))_i` fails to be injective.

This is the analytic heart of `shear_regular_ae`: a nonzero kernel vector `ξ` of that linear map
gives a nonzero kernel vector `(ξ, 0)` of `dH`, because the `i₀`-coordinate of `H` only sees the
`s`-variable. -/
private theorem shearMap_fderiv_det_eq_zero {k : ℕ} (i₀ : Fin k) (x : Fin k → ℝ) (s : ℝ)
    (a b : (Fin k → ℝ) → (Fin k → ℝ)) (φ : (Fin k → ℝ) → ℝ)
    (ha : HasFDerivAt a (fderiv ℝ a x) x) (hb : HasFDerivAt b (fderiv ℝ b x) x)
    (hφ : HasFDerivAt φ (fderiv ℝ φ x) x)
    (hni : ¬ Function.Injective (LinearMap.pi (fun i : Fin k =>
      if i = i₀ then (fderiv ℝ φ x).toLinearMap
      else (fderiv ℝ (fun z => a z i + b z i * s) x).toLinearMap))) :
    (fderiv ℝ (fun p : (Fin k → ℝ) × ℝ =>
        (fun i : Fin k => if i = i₀ then p.2 else -(a p.1 i + b p.1 i * p.2), φ p.1)) (x, s)).det = 0 := by
  rw [Function.Injective] at hni
  push_neg at hni
  obtain ⟨ξ₁, ξ₂, heq, hne⟩ := hni
  set ξ : Fin k → ℝ := ξ₁ - ξ₂ with hξdef
  have hξne : ξ ≠ 0 := by rw [hξdef]; exact sub_ne_zero.mpr hne
  have hMξ : (LinearMap.pi (fun i : Fin k =>
      if i = i₀ then (fderiv ℝ φ x).toLinearMap
      else (fderiv ℝ (fun z => a z i + b z i * s) x).toLinearMap)) ξ = 0 := by
    rw [hξdef, map_sub, heq, sub_self]
  have hcomp : ∀ i : Fin k, i ≠ i₀ → (fderiv ℝ (fun z => a z i + b z i * s) x) ξ = 0 := by
    intro i hi
    have h := congrFun hMξ i
    rw [LinearMap.pi_apply] at h
    simpa [hi] using h
  have hcomp0 : (fderiv ℝ φ x) ξ = 0 := by
    have h := congrFun hMξ i₀
    rw [LinearMap.pi_apply] at h
    simpa using h
  have hH := shearMap_hasFDerivAt i₀ x s a b φ ha hb hφ
  have h1 : (ContinuousLinearMap.pi (fun i : Fin k =>
        if i = i₀ then ContinuousLinearMap.snd ℝ (Fin k → ℝ) ℝ
        else -(((ContinuousLinearMap.proj i).comp (fderiv ℝ a x)).comp
                  (ContinuousLinearMap.fst ℝ (Fin k → ℝ) ℝ)
                + s • ((ContinuousLinearMap.proj i).comp (fderiv ℝ b x)).comp
                  (ContinuousLinearMap.fst ℝ (Fin k → ℝ) ℝ)
                + (b x i) • ContinuousLinearMap.snd ℝ (Fin k → ℝ) ℝ))) (ξ, 0) = 0 := by
    funext i
    rw [ContinuousLinearMap.pi_apply]
    by_cases hi : i = i₀
    · rw [if_pos hi]
      simp
    · rw [if_neg hi, Pi.zero_apply, ContinuousLinearMap.neg_apply, neg_eq_zero]
      have hA : ((ContinuousLinearMap.proj (R := ℝ) i).comp (fderiv ℝ a x)).comp
          (ContinuousLinearMap.fst ℝ (Fin k → ℝ) ℝ) (ξ, 0) = (fderiv ℝ a x) ξ i := by simp
      have hB : ((ContinuousLinearMap.proj (R := ℝ) i).comp (fderiv ℝ b x)).comp
          (ContinuousLinearMap.fst ℝ (Fin k → ℝ) ℝ) (ξ, 0) = (fderiv ℝ b x) ξ i := by simp
      have hS : (ContinuousLinearMap.snd ℝ (Fin k → ℝ) ℝ) (ξ, 0) = (0 : ℝ) := by simp
      simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, hA, hB, hS,
        smul_eq_mul, mul_zero, add_zero]
      rw [mul_comm s, ← shearCoord_fderiv_apply a b x s i ha hb ξ]
      exact hcomp i hi
  have h2 : ((fderiv ℝ φ x).comp (ContinuousLinearMap.fst ℝ (Fin k → ℝ) ℝ)) (ξ, 0) = 0 := by
    rw [ContinuousLinearMap.comp_apply]
    exact hcomp0
  have hzero : (fderiv ℝ (fun p : (Fin k → ℝ) × ℝ =>
        (fun i : Fin k => if i = i₀ then p.2 else -(a p.1 i + b p.1 i * p.2), φ p.1)) (x, s))
        (ξ, 0) = 0 := by
    rw [hH.fderiv, ContinuousLinearMap.prod_apply, h1, h2]
    simp
  have hker : (fderiv ℝ (fun p : (Fin k → ℝ) × ℝ =>
        (fun i : Fin k => if i = i₀ then p.2 else -(a p.1 i + b p.1 i * p.2), φ p.1)) (x, s)).toLinearMap.ker
        ≠ ⊥ := by
    intro hbot
    have hv : (ξ, 0) ∈ (fderiv ℝ (fun p : (Fin k → ℝ) × ℝ =>
        (fun i : Fin k => if i = i₀ then p.2 else -(a p.1 i + b p.1 i * p.2), φ p.1)) (x, s)).toLinearMap.ker := by
      rw [LinearMap.mem_ker]
      exact hzero
    rw [hbot, Submodule.mem_bot] at hv
    exact hξne (congrArg Prod.fst hv)
  have hdet : LinearMap.det (fderiv ℝ (fun p : (Fin k → ℝ) × ℝ =>
        (fun i : Fin k => if i = i₀ then p.2 else -(a p.1 i + b p.1 i * p.2), φ p.1)) (x, s)).toLinearMap = 0 :=
    LinearMap.det_eq_zero_iff_ker_ne_bot.mpr hker
  simpa only [ContinuousLinearMap.det] using hdet

/-- Shear transversality (parametric Sard in shear form).  `H(x,s) = (V(x,s), φ x)` with
`V(x,s)_i = s` for `i = i₀` and `V(x,s)_i = -(a x i + b x i * s)` otherwise, is a square map
`ℝ^k × ℝ → ℝ^k × ℝ`; its critical values are null, and a value `(v,c)` is `H(x,s)` for
`s = v i₀` exactly when `φ x = c` and the shear equations `a x i + b x i * v i₀ + v i = 0`
(`i ≠ i₀`) hold.  Hence for a.e. `(v,c)` every solution is a regular point of the system.

Suggested route (either is fine; the direct one avoids all reindexing):
* direct: apply `MeasureTheory.addHaar_image_eq_zero_of_det_fderivWithin_eq_zero` to
  `H : (Fin k → ℝ) × ℝ → (Fin k → ℝ) × ℝ` on `U ×ˢ Set.univ`.  If `M := LinearMap.pi
  (fun i => if i = i₀ then fderiv ℝ φ x else fderiv ℝ (fun z => a z i + b z i * s) x)` is not
  injective, say `M ξ = 0` with `ξ ≠ 0`, then `(fderiv ℝ H (x,s)) (ξ, 0) = 0` (the `i₀`-coordinate
  of `V` is `s`, independent of `x`), so `(x,s)` is critical; then `vc = H (x, vc.1 i₀)` lies in
  the null image of the critical set since the shear equations give `V (x, vc.1 i₀) = vc.1`.  Finish
  with `MeasureTheory.Measure.ae_ae_of_ae_prod` and `MeasureTheory.Measure.volume_eq_prod`.
* or: derive it from the proved `Work.WilE3.Taylor.CaseII.ae_regular_level_shear` with `e = k-1`,
  `P' = 1` and the reindexing `Fin k ≃ {i // i ≠ i₀} ⊕ {i // i = i₀}` (measure-preserving via
  `MeasurableEquiv.piEquivPiSubtypeProd`). -/
theorem shear_regular_ae {k : ℕ} (i₀ : Fin k) (U : Set (Fin k → ℝ)) (hU : IsOpen U)
    (a b : (Fin k → ℝ) → (Fin k → ℝ)) (φ : (Fin k → ℝ) → ℝ)
    (ha : ContDiffOn ℝ 1 a U) (hb : ContDiffOn ℝ 1 b U) (hφ : ContDiffOn ℝ 1 φ U) :
    ∀ᵐ vc : (Fin k → ℝ) × ℝ, ∀ x ∈ U,
      (∀ i : Fin k, i ≠ i₀ → a x i + b x i * vc.1 i₀ + vc.1 i = 0) → φ x = vc.2 →
      Function.Injective (LinearMap.pi (fun i : Fin k =>
        if i = i₀ then (fderiv ℝ φ x).toLinearMap
        else (fderiv ℝ (fun z => a z i + b z i * vc.1 i₀) x).toLinearMap)) := by
  haveI hH1 : Measure.IsAddLeftInvariant (volume : Measure ((Fin k → ℝ) × ℝ)) :=
    Measure.prod.instIsAddLeftInvariant
  haveI hH2 : Measure.IsAddHaarMeasure (volume : Measure ((Fin k → ℝ) × ℝ)) := ⟨⟩
  have hdiff : ∀ x ∈ U, HasFDerivAt a (fderiv ℝ a x) x ∧ HasFDerivAt b (fderiv ℝ b x) x ∧
      HasFDerivAt φ (fderiv ℝ φ x) x := by
    intro x hx
    exact ⟨((ha.contDiffAt (hU.mem_nhds hx)).differentiableAt one_ne_zero).hasFDerivAt,
           ((hb.contDiffAt (hU.mem_nhds hx)).differentiableAt one_ne_zero).hasFDerivAt,
           ((hφ.contDiffAt (hU.mem_nhds hx)).differentiableAt one_ne_zero).hasFDerivAt⟩
  set H : (Fin k → ℝ) × ℝ → (Fin k → ℝ) × ℝ :=
      fun p : (Fin k → ℝ) × ℝ =>
        (fun i : Fin k => if i = i₀ then p.2 else -(a p.1 i + b p.1 i * p.2), φ p.1)
    with hHdef
  set s : Set ((Fin k → ℝ) × ℝ) := {p | p.1 ∈ U ∧ (fderiv ℝ H p).det = 0} with hsdef
  have hf' : ∀ p ∈ s, HasFDerivWithinAt H (fderiv ℝ H p) s p := by
    rintro ⟨x', s'⟩ hp
    have hpU : x' ∈ U := hp.1
    have h := shearMap_hasFDerivAt i₀ x' s' a b φ (hdiff x' hpU).1 (hdiff x' hpU).2.1
      (hdiff x' hpU).2.2
    rw [hHdef]
    rw [h.fderiv]
    exact h.hasFDerivWithinAt
  have hdet' : ∀ p ∈ s, (fderiv ℝ H p).det = 0 := fun p hp => hp.2
  have hSard : (volume : Measure ((Fin k → ℝ) × ℝ)) (H '' s) = 0 :=
    addHaar_image_eq_zero_of_det_fderivWithin_eq_zero (volume : Measure ((Fin k → ℝ) × ℝ)) hf' hdet'
  set B : Set ((Fin k → ℝ) × ℝ) := {vc | ∃ x ∈ U,
      (∀ i : Fin k, i ≠ i₀ → a x i + b x i * vc.1 i₀ + vc.1 i = 0) ∧ φ x = vc.2 ∧
      ¬ Function.Injective (LinearMap.pi (fun i : Fin k =>
        if i = i₀ then (fderiv ℝ φ x).toLinearMap
        else (fderiv ℝ (fun z => a z i + b z i * vc.1 i₀) x).toLinearMap))} with hBdef
  have hBsub : B ⊆ H '' s := by
    rintro vc ⟨x, hxU, heqs, hφx, hni⟩
    refine ⟨(x, vc.1 i₀), ⟨hxU, ?_⟩, ?_⟩
    · rw [hHdef]
      exact shearMap_fderiv_det_eq_zero i₀ x (vc.1 i₀) a b φ
        (hdiff x hxU).1 (hdiff x hxU).2.1 (hdiff x hxU).2.2 hni
    · have hHapp : H (x, vc.1 i₀) = vc := by
        rw [hHdef]
        refine Prod.ext ?_ ?_
        · funext i
          by_cases hi : i = i₀
          · subst hi; simp
          · simp only [hi, if_false]
            have h := heqs i hi
            linarith
        · simpa using hφx
      exact hHapp
  have hBnull : (volume : Measure ((Fin k → ℝ) × ℝ)) B = 0 := measure_mono_null hBsub hSard
  rw [MeasureTheory.ae_iff]
  refine measure_mono_null ?_ hBnull
  intro vc hvc
  rw [hBdef]
  push_neg at hvc
  exact hvc

end Work.WilE3.Taylor.CaseII
