import Mathlib.Tactic.Have
import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
import Submission.Work.BoseFixR.LatGreen.RadialSmoothCosDecaySchwartz
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

open MeasureTheory
open scoped Real FourierTransform ContDiff

namespace Work.BoseBogFS

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-- The explicit-constant form of `Work.BoseBogFS.radialComplexDecayAEMeas`: the *same*
statement with the constant `(8π(R+1)+8)·(∫r|ρ r|)·(2π)²·(∫(1+‖η‖)‖𝓕(G:ℂ)η‖)` exposed.
Proof: replay the proof of `Work.BoseBogFS.radialComplexDecayAEMeas` (same file tree, fully
proved) keeping the witness instead of packing it into `∃ C`; its final `calc` already ends at
that exact expression, and the `Φ` it builds is `𝓕 (fun x => (G x : ℂ))` by
`SchwartzMap.fourier_coe`. -/
theorem decay_radial_complex_explicit {ρ : ℝ → ℝ} {G : EuclideanSpace ℝ (Fin 3) → ℝ} {R : ℝ}
    (hR : 0 < R) (hρR : ∀ r : ℝ, R ≤ r → ρ r = 0)
    (hρm : MeasureTheory.AEStronglyMeasurable ρ (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))))
    (hρint : MeasureTheory.IntegrableOn (fun r : ℝ => r * |ρ r|) (Set.Ioi (0 : ℝ)))
    (hG : ∀ n : ℕ, ContDiff ℝ n G) (hGsupp : HasCompactSupport G) :
    ∀ q : EuclideanSpace ℝ (Fin 3),
      ‖∫ x : EuclideanSpace ℝ (Fin 3),
          (((ρ ‖x‖ : ℝ) : ℂ) * ((G x : ℝ) : ℂ)
            * Complex.exp (-(Complex.I * (inner ℝ q x : ℂ))))‖
        ≤ ((8 * Real.pi * (R + 1) + 8) * (∫ r in Set.Ioi (0 : ℝ), r * |ρ r|)
            * (2 * Real.pi) ^ 2
            * (∫ η : EuclideanSpace ℝ (Fin 3),
                (1 + ‖η‖) * ‖FourierTransform.fourier
                  (fun x : EuclideanSpace ℝ (Fin 3) => (G x : ℂ)) η‖)) / (1 + ‖q‖) := by
  have hGtop : ContDiff ℝ ∞ G := contDiff_infty.mpr hG
  have hGcsupp : HasCompactSupport (fun x : E3 => (G x : ℂ)) :=
    hGsupp.comp_left (g := fun r : ℝ => (r : ℂ)) (by simp)
  have hGcdiff : ContDiff ℝ ∞ (fun x : E3 => (G x : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp hGtop
  let Fs : SchwartzMap E3 ℂ := HasCompactSupport.toSchwartzMap hGcsupp hGcdiff
  have hFs : (Fs : E3 → ℂ) = fun x : E3 => (G x : ℂ) := rfl
  let Φ : SchwartzMap E3 ℂ := 𝓕 Fs
  have hΦcoe : (Φ : E3 → ℂ) = 𝓕 (fun x : E3 => (G x : ℂ)) := by
    rw [show (Φ : E3 → ℂ) = 𝓕 (Fs : E3 → ℂ) from SchwartzMap.fourier_coe Fs, hFs]
  have hΦint : Integrable (fun η : E3 => (Φ : E3 → ℂ) η) :=
    SchwartzMap.integrable (μ := volume) Φ
  have hΦmom : Integrable (fun η : E3 => (1 + ‖η‖) * ‖(Φ : E3 → ℂ) η‖) := by
    have h0 := SchwartzMap.integrable (μ := volume) Φ
    have h1 := SchwartzMap.integrable_pow_mul (μ := volume) Φ 1
    have heq : (fun η : E3 => (1 + ‖η‖) * ‖(Φ : E3 → ℂ) η‖)
        = fun η : E3 => ‖(Φ : E3 → ℂ) η‖ + ‖η‖ ^ 1 * ‖(Φ : E3 → ℂ) η‖ := by
      funext η; ring
    rw [heq]
    exact h0.norm.add h1
  have hΦinv : ∀ x : E3, (G x : ℂ) = ∫ η : E3, 𝐞 (inner ℝ η x) • (Φ : E3 → ℂ) η := by
    intro x
    have hcont : Continuous (fun x : E3 => (G x : ℂ)) :=
      Complex.continuous_ofReal.comp hGtop.continuous
    have hint1 : Integrable (fun x : E3 => (G x : ℂ)) := by
      have h := SchwartzMap.integrable (μ := volume) Fs
      rwa [hFs] at h
    have hint2 : Integrable (𝓕 (fun x : E3 => (G x : ℂ))) := by
      rw [← hΦcoe]
      exact hΦint
    have hfun : 𝓕⁻ (𝓕 (fun x : E3 => (G x : ℂ))) = (fun x : E3 => (G x : ℂ)) :=
      Continuous.fourierInv_fourier_eq hcont hint1 hint2
    rw [← congrFun hfun x, Real.fourierInv_eq]
    simp [hΦcoe]
  obtain ⟨hWint, hdec⟩ :=
    Work.BoseFixR.LatGreen.radialWeight_fourier_decay_explicit hR hρR hρm hρint
  have hWintc : Integrable (fun x : E3 => ((ρ ‖x‖ : ℝ) : ℂ)) := hWint.ofReal
  set L : ℝ := ∫ r in Set.Ioi (0 : ℝ), r * |ρ r| with hL
  have hLnn : 0 ≤ L := by
    rw [hL]
    exact setIntegral_nonneg measurableSet_Ioi (fun r hr => mul_nonneg hr.le (abs_nonneg _))
  set M : ℝ := ∫ η : E3, (1 + ‖η‖) * ‖(Φ : E3 → ℂ) η‖ with hM
  have hMcoe : M = ∫ η : E3, (1 + ‖η‖) * ‖𝓕 (fun x : E3 => (G x : ℂ)) η‖ := by
    rw [hM]
    refine integral_congr_ae (Filter.Eventually.of_forall fun η => ?_)
    rw [hΦcoe]
  have hKnn : 0 ≤ (8 * Real.pi * (R + 1) + 8) * L :=
    mul_nonneg (by positivity) hLnn
  intro q
  set ν : E3 := (2 * Real.pi)⁻¹ • q with hν
  have hchar : ∀ x : E3,
      Complex.exp (-(Complex.I * (inner ℝ q x : ℂ)))
        = (Real.fourierChar (-(inner ℝ ν x)) : ℂ) := by
    intro x
    rw [hν, Real.fourierChar_apply]
    have h2π : (2 * Real.pi) * (inner ℝ ((2 * Real.pi)⁻¹ • q) x) = inner ℝ q x := by
      rw [real_inner_smul_left]
      field_simp
    have harg : (2 * Real.pi) * (-(inner ℝ ((2 * Real.pi)⁻¹ • q) x)) = -(inner ℝ q x) := by
      rw [mul_neg, h2π]
    rw [harg]
    congr 1
    push_cast
    ring
  have hfub := Work.BoseFixR.LatGreen.fubini_mul_fourierChar
    (W := fun x : E3 => ((ρ ‖x‖ : ℝ) : ℂ))
    (Ψ := fun x : E3 => ((G x : ℝ) : ℂ))
    (G := fun η : E3 => (Φ : E3 → ℂ) η)
    hWintc hΦint hΦinv ν
  have hEq : (∫ x : E3,
        ((ρ ‖x‖ : ℝ) : ℂ) * ((G x : ℝ) : ℂ)
          * (Real.fourierChar (-(inner ℝ ν x)) : ℂ))
      = ∫ η : E3,
          (Φ : E3 → ℂ) η * 𝓕 (fun x : E3 => ((ρ ‖x‖ : ℝ) : ℂ)) (ν - η) :=
    hfub
  have hstream : (fun x : E3 =>
        ((ρ ‖x‖ : ℝ) : ℂ) * ((G x : ℝ) : ℂ)
          * Complex.exp (-(Complex.I * (inner ℝ q x : ℂ))))
      = (fun x : E3 =>
        ((ρ ‖x‖ : ℝ) : ℂ) * ((G x : ℝ) : ℂ)
          * (Real.fourierChar (-(inner ℝ ν x)) : ℂ)) := by
    funext x
    rw [hchar x]
  have hEq' : (∫ x : E3,
        ((ρ ‖x‖ : ℝ) : ℂ) * ((G x : ℝ) : ℂ)
          * Complex.exp (-(Complex.I * (inner ℝ q x : ℂ))))
      = ∫ η : E3,
          (Φ : E3 → ℂ) η * 𝓕 (fun x : E3 => ((ρ ‖x‖ : ℝ) : ℂ)) (ν - η) := by
    rw [hstream]
    exact hEq
  rw [hEq']
  have hmid : Integrable (fun η : E3 =>
      ‖(Φ : E3 → ℂ) η‖ * ((8 * Real.pi * (R + 1) + 8) * L / (1 + ‖ν - η‖))) := by
    have hb : Integrable (fun η : E3 =>
        ‖(Φ : E3 → ℂ) η‖ * ((8 * Real.pi * (R + 1) + 8) * L)) :=
      hΦint.norm.mul_const _
    refine hb.mono' ?_ ?_
    · exact hΦint.norm.aestronglyMeasurable.mul
        (Continuous.aestronglyMeasurable
          (continuous_const.div (by fun_prop) (fun η => by positivity)))
    · filter_upwards with η
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
      exact div_le_self hKnn (by have h := norm_nonneg (ν - η); linarith)
  calc ‖∫ η : E3,
          (Φ : E3 → ℂ) η * 𝓕 (fun x : E3 => ((ρ ‖x‖ : ℝ) : ℂ)) (ν - η)‖
      ≤ ∫ η : E3,
          ‖(Φ : E3 → ℂ) η * 𝓕 (fun x : E3 => ((ρ ‖x‖ : ℝ) : ℂ)) (ν - η)‖ :=
        norm_integral_le_integral_norm _
    _ = ∫ η : E3,
          ‖(Φ : E3 → ℂ) η‖ * ‖𝓕 (fun x : E3 => ((ρ ‖x‖ : ℝ) : ℂ)) (ν - η)‖ := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun η => ?_)
        exact norm_mul _ _
    _ ≤ ∫ η : E3,
          ‖(Φ : E3 → ℂ) η‖ * ((8 * Real.pi * (R + 1) + 8) * L / (1 + ‖ν - η‖)) := by
        refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun η => ?_) hmid ?_
        · exact mul_nonneg (norm_nonneg _) (norm_nonneg _)
        · filter_upwards with η
          exact mul_le_mul_of_nonneg_left (hdec (ν - η)) (norm_nonneg _)
    _ = (8 * Real.pi * (R + 1) + 8) * L
          * ∫ η : E3, ‖(Φ : E3 → ℂ) η‖ / (1 + ‖ν - η‖) := by
        rw [show (fun η : E3 =>
              ‖(Φ : E3 → ℂ) η‖ * ((8 * Real.pi * (R + 1) + 8) * L / (1 + ‖ν - η‖)))
            = (fun η : E3 =>
              ((8 * Real.pi * (R + 1) + 8) * L)
                * (‖(Φ : E3 → ℂ) η‖ / (1 + ‖ν - η‖))) from by
            funext η; rw [div_eq_mul_inv]; ring]
        exact integral_const_mul _ _
    _ ≤ (8 * Real.pi * (R + 1) + 8) * L
          * ((2 * Real.pi) ^ 2 * M / (1 + ‖q‖)) := by
        refine mul_le_mul_of_nonneg_left ?_ hKnn
        rw [hM, hν]
        exact Work.BoseFixR.LatGreen.InvOneAddNormSubIntegralLe hΦint hΦmom q
    _ = ((8 * Real.pi * (R + 1) + 8) * L * (2 * Real.pi) ^ 2 * M) / (1 + ‖q‖) := by ring
    _ = ((8 * Real.pi * (R + 1) + 8) * (∫ r in Set.Ioi (0 : ℝ), r * |ρ r|)
          * (2 * Real.pi) ^ 2
          * (∫ η : E3, (1 + ‖η‖) * ‖𝓕 (fun x : E3 => (G x : ℂ)) η‖)) / (1 + ‖q‖) := by
        rw [hL, hMcoe]

end Work.BoseBogFS
