import Mathlib
import Submission.Work.Asymptotics.PropagateDefs
import Submission.Work.Kernels.SlashDefs
import Submission.Work.Asymptotics.T2op_kernelTransform

namespace Work.CKFinal

open MeasureTheory UpperHalfPlane ModularForm ModularGroup Matrix
open scoped MatrixGroups ModularForm Manifold Bundle Topology

open Work.Asymptotics

/-- Linearity of a three-term combination under Bochner integration: for integrable
`g₀ g₁ g₂` and arbitrary complex constants, the integral of
`g₂·c₂ - 2·(g₁·c₁) + g₀·c₀` splits into the corresponding combination of the three
integrals. -/
lemma integral_comb {g0 g1 g2 : ℝ → ℂ} {s : Set ℝ} {c0 c1 c2 : ℂ}
    (h0 : MeasureTheory.IntegrableOn g0 s) (h1 : MeasureTheory.IntegrableOn g1 s)
    (h2 : MeasureTheory.IntegrableOn g2 s) :
    (∫ t in s, (g2 t * c2 - 2 * (g1 t * c1) + g0 t * c0))
      = (∫ t in s, g2 t) * c2 - 2 * ((∫ t in s, g1 t) * c1) + (∫ t in s, g0 t) * c0 := by
  have i2 : MeasureTheory.IntegrableOn (fun t : ℝ => g2 t * c2) s := h2.mul_const c2
  have i1 : MeasureTheory.IntegrableOn (fun t : ℝ => (2 : ℂ) * (g1 t * c1)) s :=
    (h1.mul_const c1).const_mul 2
  have i0 : MeasureTheory.IntegrableOn (fun t : ℝ => g0 t * c0) s := h0.mul_const c0
  have e2 : (∫ t in s, g2 t * c2) = (∫ t in s, g2 t) * c2 :=
    MeasureTheory.integral_mul_const c2 g2
  have e1 : (∫ t in s, g1 t * c1) = (∫ t in s, g1 t) * c1 :=
    MeasureTheory.integral_mul_const c1 g1
  have e0 : (∫ t in s, g0 t * c0) = (∫ t in s, g0 t) * c0 :=
    MeasureTheory.integral_mul_const c0 g0
  have hcm : (∫ t in s, (2 : ℂ) * (g1 t * c1)) = 2 * (∫ t in s, g1 t * c1) :=
    MeasureTheory.integral_const_mul 2 (fun t : ℝ => g1 t * c1)
  have step1 : (∫ t in s, (g2 t * c2 - 2 * (g1 t * c1) + g0 t * c0))
      = (∫ t in s, (g2 t * c2 - 2 * (g1 t * c1))) + (∫ t in s, g0 t * c0) := by
    have h := MeasureTheory.integral_add
      (f := fun t : ℝ => g2 t * c2 - 2 * (g1 t * c1)) (g := fun t : ℝ => g0 t * c0)
      (i2.sub i1) i0
    simpa using h
  have step2 : (∫ t in s, (g2 t * c2 - 2 * (g1 t * c1)))
      = (∫ t in s, g2 t * c2) - (∫ t in s, (2 : ℂ) * (g1 t * c1)) := by
    have h := MeasureTheory.integral_sub (f := fun t : ℝ => g2 t * c2)
      (g := fun t : ℝ => (2 : ℂ) * (g1 t * c1)) i2 i1
    simpa using h
  rw [step1, step2, hcm, e2, e1, e0]

/-- **Linearity of `S(T-I)²` under Bochner integration.**  If the three integrands obtained from
`f` by evaluating at the three points `S•τ, S•(τ+1), S•(τ+2)` are Bochner integrable on `s` and the
`S(T-I)²`-defect of `f · t` vanishes pointwise at `τ`, then the defect of the Bochner integral
`σ ↦ ∫ t in s, f σ t` vanishes at `τ`. -/
theorem S2op_integral_eq_zero {k : ℤ} {f : UpperHalfPlane → ℝ → ℂ} {s : Set ℝ}
    {τ : UpperHalfPlane}
    (h0 : MeasureTheory.IntegrableOn (fun t : ℝ => f (ModularGroup.S • τ) t) s)
    (h1 : MeasureTheory.IntegrableOn (fun t : ℝ => f (ModularGroup.S • ((1 : ℝ) +ᵥ τ)) t) s)
    (h2 : MeasureTheory.IntegrableOn (fun t : ℝ => f (ModularGroup.S • ((2 : ℝ) +ᵥ τ)) t) s)
    (hpt : ∀ t : ℝ, Work.Asymptotics.S2op k (fun σ : UpperHalfPlane => f σ t) τ = 0) :
    Work.Asymptotics.S2op k (fun σ : UpperHalfPlane => ∫ t in s, f σ t) τ = 0 := by
  have hfun : ∀ t : ℝ,
      f (ModularGroup.S • ((2 : ℝ) +ᵥ τ)) t * ((((2 : ℝ) +ᵥ τ : ℍ) : ℂ) ^ (-k))
        - 2 * (f (ModularGroup.S • ((1 : ℝ) +ᵥ τ)) t * ((((1 : ℝ) +ᵥ τ : ℍ) : ℂ) ^ (-k)))
        + f (ModularGroup.S • τ) t * ((τ : ℂ) ^ (-k)) = 0 := by
    intro t
    have h := hpt t
    rw [S2op_apply_eq] at h
    simp only [Work.Kernels.slash_S_apply] at h
    simpa using h
  have hz : (∫ t in s, (f (ModularGroup.S • ((2 : ℝ) +ᵥ τ)) t * ((((2 : ℝ) +ᵥ τ : ℍ) : ℂ) ^ (-k))
        - 2 * (f (ModularGroup.S • ((1 : ℝ) +ᵥ τ)) t * ((((1 : ℝ) +ᵥ τ : ℍ) : ℂ) ^ (-k)))
        + f (ModularGroup.S • τ) t * ((τ : ℂ) ^ (-k)))) = 0 := by
    rw [show (fun t : ℝ => f (ModularGroup.S • ((2 : ℝ) +ᵥ τ)) t * ((((2 : ℝ) +ᵥ τ : ℍ) : ℂ) ^ (-k))
          - 2 * (f (ModularGroup.S • ((1 : ℝ) +ᵥ τ)) t * ((((1 : ℝ) +ᵥ τ : ℍ) : ℂ) ^ (-k)))
          + f (ModularGroup.S • τ) t * ((τ : ℂ) ^ (-k))) = (fun _ : ℝ => (0 : ℂ)) from
        funext hfun]
    simp
  rw [S2op_apply_eq]
  simp only [Work.Kernels.slash_S_apply]
  exact (integral_comb (g0 := fun t : ℝ => f (ModularGroup.S • τ) t)
      (g1 := fun t : ℝ => f (ModularGroup.S • ((1 : ℝ) +ᵥ τ)) t)
      (g2 := fun t : ℝ => f (ModularGroup.S • ((2 : ℝ) +ᵥ τ)) t)
      (c0 := (τ : ℂ) ^ (-k)) (c1 := ((((1 : ℝ) +ᵥ τ : ℍ)) : ℂ) ^ (-k))
      (c2 := ((((2 : ℝ) +ᵥ τ : ℍ)) : ℂ) ^ (-k)) h0 h1 h2).symm.trans hz

end Work.CKFinal
