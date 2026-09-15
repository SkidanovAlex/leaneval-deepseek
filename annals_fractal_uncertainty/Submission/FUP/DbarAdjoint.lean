import Submission.FUP.DbarWeighted
import Mathlib.Analysis.Calculus.FDeriv.Star

open MeasureTheory

set_option autoImplicit false
variable {d : ℕ}
local notation "ℂᵈ" => (Fin d → ℂ)

/-!
# The formal adjoint of `∂̄`

For a smooth real weight `φ : ℂᵈ → ℝ` and a smooth compactly supported `(0,1)`-form
`u : ℂᵈ → (Fin d → ℂ)`, the `L²`-adjoint of `∂̄` with respect to the weighted pairing
`⟨f, u⟩_φ = ∫ ∑_j f (z) conj (u z j) e^{-φ z}` is

  `ϑ_φ u = - ∑_j (∂_j u_j - u_j ∂_j φ)`,

i.e. `ϑ_φ u = - e^{φ} ∑_j ∂_j (e^{-φ} u_j)`.  The identity proved here is

  `∫ (∑_j (∂̄_j g) conj (u_j)) e^{-φ} = ∫ g conj (ϑ_φ u) e^{-φ}`

for every smooth compactly supported `g`.  It is the first step of the proof of Hörmander's
`∂̄`-theorem (Cohen's `thm:hormander_delbar`), feeding into the Bochner–Kodaira/Kohn–Morrey
estimate `∫ κ |u|² e^{-φ} ≤ ‖∂̄u‖²_φ + ‖ϑ_φu‖²_φ`.
-/

namespace Submission.FUP

private lemma star_half_sub (x y : ℂ) :
    star ((x - Complex.I * y) / 2) = (star x + Complex.I * star y) / 2 := by
  simp only [Complex.star_def]
  rw [map_div₀ (starRingEnd ℂ), map_sub, map_mul, Complex.conj_I]
  simp only [map_ofNat]
  ring

private lemma star_half_add (x y : ℂ) :
    star ((x + Complex.I * y) / 2) = (star x - Complex.I * star y) / 2 := by
  simp only [Complex.star_def]
  rw [map_div₀ (starRingEnd ℂ), map_add, map_mul, Complex.conj_I]
  simp only [map_ofNat]
  ring

section Conj

/-- Conjugation turns `∂̄_j` into `∂_j`: `∂̄_j (conj ∘ f) = conj ∘ (∂_j f)`. -/
theorem partialZbar_star (j : Fin d) (f : ℂᵈ → ℂ) :
    partialZbar j (fun z => star (f z)) = fun z => star (partialZ j f z) := by
  funext z
  have hfd : fderiv ℝ (fun y : ℂᵈ => star (f y)) z
      = ((starL' ℝ : ℂ ≃L[ℝ] ℂ) : ℂ →L[ℝ] ℂ) ∘L fderiv ℝ f z := by
    rw [fderiv_star]
  simp only [partialZbar, partialZ, hfd, ContinuousLinearMap.comp_apply,
    ContinuousLinearEquiv.coe_coe, starL'_apply]
  rw [star_half_sub]

/-- Conjugation turns `∂_j` into `∂̄_j`: `∂_j (conj ∘ f) = conj ∘ (∂̄_j f)`. -/
theorem partialZ_star (j : Fin d) (f : ℂᵈ → ℂ) :
    partialZ j (fun z => star (f z)) = fun z => star (partialZbar j f z) := by
  funext z
  have hfd : fderiv ℝ (fun y : ℂᵈ => star (f y)) z
      = ((starL' ℝ : ℂ ≃L[ℝ] ℂ) : ℂ →L[ℝ] ℂ) ∘L fderiv ℝ f z := by
    rw [fderiv_star]
  simp only [partialZ, partialZbar, hfd, ContinuousLinearMap.comp_apply,
    ContinuousLinearEquiv.coe_coe, starL'_apply]
  rw [star_half_add]

/-- For a real-valued `φ` the function `z ↦ (φ z : ℂ)` is conjugation invariant, hence
`∂̄_j φ = conj (∂_j φ)`. -/
theorem partialZbar_ofReal (j : Fin d) (φ : ℂᵈ → ℝ) :
    partialZbar j (fun z => ((φ z : ℝ) : ℂ))
      = fun z => star (partialZ j (fun z => ((φ z : ℝ) : ℂ)) z) := by
  have h := partialZbar_star j (fun z : ℂᵈ => ((φ z : ℝ) : ℂ))
  have h2 : (fun z : ℂᵈ => star (((fun z : ℂᵈ => ((φ z : ℝ) : ℂ)) z)))
      = fun z : ℂᵈ => ((φ z : ℝ) : ℂ) := by
    funext z; simp
  rw [h2] at h
  exact h

end Conj

section Continuous

lemma continuous_partialZ {f : ℂᵈ → ℂ} (hf : ContDiff ℝ 1 f) (j : Fin d) :
    Continuous (fun z => partialZ j f z) := by
  have hd : Continuous (fderiv ℝ f) := hf.continuous_fderiv (by norm_num)
  have hA : Continuous (fun z : ℂᵈ => fderiv ℝ f z (Pi.single j 1)) :=
    hd.clm_apply continuous_const
  have hB : Continuous (fun z : ℂᵈ => fderiv ℝ f z (Pi.single j Complex.I)) :=
    hd.clm_apply continuous_const
  have h : Continuous (fun z : ℂᵈ =>
      (fderiv ℝ f z (Pi.single j 1) - Complex.I * fderiv ℝ f z (Pi.single j Complex.I)) / 2) :=
    (hA.sub (continuous_const.mul hB)).div_const 2
  convert h using 1
  funext z; rw [partialZ]

lemma continuous_partialZbar {f : ℂᵈ → ℂ} (hf : ContDiff ℝ 1 f) (j : Fin d) :
    Continuous (fun z => partialZbar j f z) := by
  have hd : Continuous (fderiv ℝ f) := hf.continuous_fderiv (by norm_num)
  have hA : Continuous (fun z : ℂᵈ => fderiv ℝ f z (Pi.single j 1)) :=
    hd.clm_apply continuous_const
  have hB : Continuous (fun z : ℂᵈ => fderiv ℝ f z (Pi.single j Complex.I)) :=
    hd.clm_apply continuous_const
  have h : Continuous (fun z : ℂᵈ =>
      (fderiv ℝ f z (Pi.single j 1) + Complex.I * fderiv ℝ f z (Pi.single j Complex.I)) / 2) :=
    (hA.add (continuous_const.mul hB)).div_const 2
  convert h using 1
  funext z; rw [partialZbar]

private lemma integrable_mul_exp {f : ℂᵈ → ℂ} {φ : ℂᵈ → ℝ} (hf : Continuous f)
    (hcs : HasCompactSupport f) (hφ : ContDiff ℝ 1 fun w => ((φ w : ℝ) : ℂ)) :
    Integrable (fun z => f z * Complex.exp (-(((φ z : ℝ) : ℂ)))) :=
  (hf.mul (Complex.continuous_exp.comp hφ.continuous.neg)).integrable_of_hasCompactSupport
    (hcs.mul_right (f' := fun z => Complex.exp (-(((φ z : ℝ) : ℂ)))))

end Continuous

/-- The formal adjoint `ϑ_φ` of `∂̄` with respect to the weight `e^{-φ}`:
`ϑ_φ u = - ∑_j (∂_j u_j - u_j ∂_j φ) = - e^{φ} ∑_j ∂_j (e^{-φ} u_j)`. -/
noncomputable def dbarAdjoint (φ : ℂᵈ → ℝ) (u : ℂᵈ → (Fin d → ℂ)) : ℂᵈ → ℂ :=
  fun z => -(∑ j, (partialZ j (fun w => u w j) z
    - u z j * partialZ j (fun w => ((φ w : ℝ) : ℂ)) z))

/-- The `j`-th summand of the adjoint identity. -/
theorem integral_dbar_mul_adjoint_j {g uj : ℂᵈ → ℂ} {φ : ℂᵈ → ℝ}
    (hg : ContDiff ℝ 1 g) (hu : ContDiff ℝ 1 uj)
    (hφ : ContDiff ℝ 1 fun w => ((φ w : ℝ) : ℂ))
    (hsg : HasCompactSupport g) (hsu : HasCompactSupport uj) (j : Fin d) :
    (∫ z, partialZbar j g z * star (uj z) * Complex.exp (-(((φ z : ℝ) : ℂ))))
      = - (∫ z, g z * star (partialZ j uj z - uj z * partialZ j (fun w => ((φ w : ℝ) : ℂ)) z)
          * Complex.exp (-(((φ z : ℝ) : ℂ)))) := by
  have hu' : ContDiff ℝ 1 (fun z => star (uj z)) := by
    have h1 : ContDiff ℝ 1 (fun z : ℂᵈ => (starRingEnd ℂ) (uj z)) :=
      (Complex.conjCLE.contDiff (n := 1)).comp hu
    simpa [Function.comp_def] using h1
  have hsu' : HasCompactSupport (fun z => star (uj z)) := hsu.comp_left (by simp)
  have hIBP := integral_dbar_mul_weighted_eq_neg (F := g) (G := fun z => star (uj z))
    (ψ := fun z => ((φ z : ℝ) : ℂ)) hg hu' hφ hsg hsu' j
  have h1 : partialZbar j (fun z => star (uj z))
      = fun z => star (partialZ j uj z) := partialZbar_star j uj
  have h2 : partialZbar j (fun z => ((φ z : ℝ) : ℂ))
      = fun z => star (partialZ j (fun w => ((φ w : ℝ) : ℂ)) z) := partialZbar_ofReal j φ
  have hA1 : (∫ z, g z * partialZbar j (fun z => star (uj z)) z
        * Complex.exp (-(((φ z : ℝ) : ℂ))))
      = ∫ z, g z * star (partialZ j uj z) * Complex.exp (-(((φ z : ℝ) : ℂ))) := by
    refine integral_congr_ae (μ := volume) (Filter.Eventually.of_forall fun z => ?_)
    simp only [h1]
  have hA2 : (∫ z, g z * star (uj z) * partialZbar j (fun z => ((φ z : ℝ) : ℂ)) z
        * Complex.exp (-(((φ z : ℝ) : ℂ))))
      = ∫ z, g z * star (uj z * partialZ j (fun w => ((φ w : ℝ) : ℂ)) z)
          * Complex.exp (-(((φ z : ℝ) : ℂ))) := by
    refine integral_congr_ae (μ := volume) (Filter.Eventually.of_forall fun z => ?_)
    simp only [h2, star_mul]
    ring
  have hXint : Integrable (fun z => g z * star (partialZ j uj z)
      * Complex.exp (-(((φ z : ℝ) : ℂ)))) :=
    integrable_mul_exp (f := fun z => g z * star (partialZ j uj z))
      (hg.continuous.mul (continuous_partialZ hu j).star)
      (hsg.mul_right (f' := fun z => star (partialZ j uj z))) hφ
  have hYint : Integrable (fun z => g z * star (uj z * partialZ j (fun w => ((φ w : ℝ) : ℂ)) z)
      * Complex.exp (-(((φ z : ℝ) : ℂ)))) :=
    integrable_mul_exp (f := fun z => g z * star (uj z * partialZ j (fun w => ((φ w : ℝ) : ℂ)) z))
      (hg.continuous.mul (hu.continuous.mul (continuous_partialZ hφ j)).star)
      (hsg.mul_right (f' := fun z => star (uj z * partialZ j (fun w => ((φ w : ℝ) : ℂ)) z))) hφ
  have hd : (∫ z, g z * star (partialZ j uj z) * Complex.exp (-(((φ z : ℝ) : ℂ))))
      - (∫ z, g z * star (uj z * partialZ j (fun w => ((φ w : ℝ) : ℂ)) z)
          * Complex.exp (-(((φ z : ℝ) : ℂ))))
      = ∫ z, g z * star (partialZ j uj z - uj z * partialZ j (fun w => ((φ w : ℝ) : ℂ)) z)
          * Complex.exp (-(((φ z : ℝ) : ℂ))) := by
    rw [← integral_sub hXint hYint]
    refine integral_congr_ae (μ := volume) (Filter.Eventually.of_forall fun z => ?_)
    show g z * star (partialZ j uj z) * Complex.exp (-(((φ z : ℝ) : ℂ)))
        - g z * star (uj z * partialZ j (fun w => ((φ w : ℝ) : ℂ)) z)
          * Complex.exp (-(((φ z : ℝ) : ℂ)))
      = g z * star (partialZ j uj z - uj z * partialZ j (fun w => ((φ w : ℝ) : ℂ)) z)
          * Complex.exp (-(((φ z : ℝ) : ℂ)))
    rw [star_sub]
    ring
  calc (∫ z, partialZbar j g z * star (uj z) * Complex.exp (-(((φ z : ℝ) : ℂ))))
      = - (∫ z, g z * partialZbar j (fun z => star (uj z)) z
            * Complex.exp (-(((φ z : ℝ) : ℂ))))
        + (∫ z, g z * star (uj z) * partialZbar j (fun z => ((φ z : ℝ) : ℂ)) z
            * Complex.exp (-(((φ z : ℝ) : ℂ)))) := hIBP
    _ = - (∫ z, g z * star (partialZ j uj z) * Complex.exp (-(((φ z : ℝ) : ℂ))))
        + (∫ z, g z * star (uj z * partialZ j (fun w => ((φ w : ℝ) : ℂ)) z)
            * Complex.exp (-(((φ z : ℝ) : ℂ)))) := by rw [hA1, hA2]
    _ = - (∫ z, g z * star (partialZ j uj z - uj z * partialZ j (fun w => ((φ w : ℝ) : ℂ)) z)
            * Complex.exp (-(((φ z : ℝ) : ℂ)))) := by
        rw [← hd]; ring

/-- **The adjoint identity for `∂̄`.**  For smooth compactly supported `g` and a smooth
compactly supported `(0,1)`-form `u` and a smooth real weight `φ`,

  `∫ (∑_j (∂̄_j g) conj (u_j)) e^{-φ} = ∫ g conj (ϑ_φ u) e^{-φ}`.

(Stated with `Complex.exp (-(φ z))`; use `Complex.ofReal_exp` for the real exponential form.) -/
theorem integral_dbar_mul_adjoint {g : ℂᵈ → ℂ} {u : ℂᵈ → (Fin d → ℂ)} {φ : ℂᵈ → ℝ}
    (hg : ContDiff ℝ 1 g) (hu : ∀ j, ContDiff ℝ 1 (fun w => u w j))
    (hφ : ContDiff ℝ 1 fun w => ((φ w : ℝ) : ℂ))
    (hsg : HasCompactSupport g) (hsu : ∀ j, HasCompactSupport (fun w => u w j)) :
    (∫ z, (∑ j, partialZbar j g z * star (u z j)) * Complex.exp (-(((φ z : ℝ) : ℂ))))
      = ∫ z, g z * star (dbarAdjoint φ u z) * Complex.exp (-(((φ z : ℝ) : ℂ))) := by
  have hintL : ∀ j : Fin d, Integrable (fun z => partialZbar j g z * star (u z j)
      * Complex.exp (-(((φ z : ℝ) : ℂ)))) := by
    intro j
    refine integrable_mul_exp (f := fun z => partialZbar j g z * star (u z j)) ?_ ?_ hφ
    · exact (continuous_partialZbar hg j).mul (hu j).continuous.star
    · exact ((hsu j).comp_left (by simp)).mul_left (f := fun z => partialZbar j g z)
  have hInt2 : ∀ j : Fin d, Integrable (fun z => g z * star (partialZ j (fun w => u w j) z
      - u z j * partialZ j (fun w => ((φ w : ℝ) : ℂ)) z)
      * Complex.exp (-(((φ z : ℝ) : ℂ)))) := by
    intro j
    refine integrable_mul_exp (f := fun z => g z * star (partialZ j (fun w => u w j) z
      - u z j * partialZ j (fun w => ((φ w : ℝ) : ℂ)) z)) ?_ ?_ hφ
    · exact hg.continuous.mul ((continuous_partialZ (hu j) j).sub
        ((hu j).continuous.mul (continuous_partialZ hφ j))).star
    · exact hsg.mul_right (f' := fun z => star (partialZ j (fun w => u w j) z
        - u z j * partialZ j (fun w => ((φ w : ℝ) : ℂ)) z))
  have hL : (∫ z, (∑ j, partialZbar j g z * star (u z j)) * Complex.exp (-(((φ z : ℝ) : ℂ))))
      = ∑ j, ∫ z, partialZbar j g z * star (u z j) * Complex.exp (-(((φ z : ℝ) : ℂ))) := by
    have h1 : (∫ z, (∑ j, partialZbar j g z * star (u z j))
          * Complex.exp (-(((φ z : ℝ) : ℂ))))
        = ∫ z, ∑ j, partialZbar j g z * star (u z j) * Complex.exp (-(((φ z : ℝ) : ℂ))) := by
      refine integral_congr_ae (μ := volume) (Filter.Eventually.of_forall fun z => ?_)
      exact Finset.sum_mul _ _ _
    rw [h1, integral_finsetSum Finset.univ (fun j _ => hintL j)]
  have hR : ∑ j, ∫ z, partialZbar j g z * star (u z j) * Complex.exp (-(((φ z : ℝ) : ℂ)))
      = - ∑ j, ∫ z, g z * star (partialZ j (fun w => u w j) z
            - u z j * partialZ j (fun w => ((φ w : ℝ) : ℂ)) z)
          * Complex.exp (-(((φ z : ℝ) : ℂ))) := by
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl (fun j _ =>
      integral_dbar_mul_adjoint_j hg (hu j) hφ hsg (hsu j) j)
  have hS : ∑ j, ∫ z, g z * star (partialZ j (fun w => u w j) z
          - u z j * partialZ j (fun w => ((φ w : ℝ) : ℂ)) z)
        * Complex.exp (-(((φ z : ℝ) : ℂ)))
      = ∫ z, ∑ j, g z * star (partialZ j (fun w => u w j) z
          - u z j * partialZ j (fun w => ((φ w : ℝ) : ℂ)) z)
        * Complex.exp (-(((φ z : ℝ) : ℂ))) :=
    (integral_finsetSum Finset.univ (fun j _ => hInt2 j)).symm
  calc (∫ z, (∑ j, partialZbar j g z * star (u z j)) * Complex.exp (-(((φ z : ℝ) : ℂ))))
      = ∑ j, ∫ z, partialZbar j g z * star (u z j)
          * Complex.exp (-(((φ z : ℝ) : ℂ))) := hL
    _ = - ∑ j, ∫ z, g z * star (partialZ j (fun w => u w j) z
            - u z j * partialZ j (fun w => ((φ w : ℝ) : ℂ)) z)
          * Complex.exp (-(((φ z : ℝ) : ℂ))) := hR
    _ = - ∫ z, ∑ j, g z * star (partialZ j (fun w => u w j) z
            - u z j * partialZ j (fun w => ((φ w : ℝ) : ℂ)) z)
          * Complex.exp (-(((φ z : ℝ) : ℂ))) := by rw [hS]
    _ = ∫ z, -(∑ j, g z * star (partialZ j (fun w => u w j) z
            - u z j * partialZ j (fun w => ((φ w : ℝ) : ℂ)) z)
          * Complex.exp (-(((φ z : ℝ) : ℂ)))) := by rw [← integral_neg]
    _ = ∫ z, g z * star (dbarAdjoint φ u z) * Complex.exp (-(((φ z : ℝ) : ℂ))) := by
        refine integral_congr_ae (μ := volume) (Filter.Eventually.of_forall fun z => ?_)
        have hsum : ∑ j, g z * star (partialZ j (fun w => u w j) z
              - u z j * partialZ j (fun w => ((φ w : ℝ) : ℂ)) z)
            * Complex.exp (-(((φ z : ℝ) : ℂ)))
            = g z * (∑ j, star (partialZ j (fun w => u w j) z
              - u z j * partialZ j (fun w => ((φ w : ℝ) : ℂ)) z))
              * Complex.exp (-(((φ z : ℝ) : ℂ))) := by
          rw [← Finset.sum_mul, ← Finset.mul_sum]
        simp only [dbarAdjoint, star_neg, star_sum]
        rw [hsum]
        ring

end Submission.FUP
