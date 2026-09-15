import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Calculus.FDeriv.RestrictScalars
import Mathlib.Analysis.InnerProductSpace.Basic

/-!
# Complex differentiability from the vanishing of the Wirtinger derivatives

For a real-differentiable function `f : (Fin d → ℂ) → ℂ`, we show that if the Wirtinger
`∂̄` derivatives vanish in each coordinate, then `f` is complex differentiable.

The proof is in three steps:
* `smul_eq_re_smul_add_im_smul_I`: decompose complex scalar multiplication into real and
  imaginary parts;
* `exists_complexLinear_of_map_smul_I`: a real-linear map commuting with multiplication by `I`
  is complex linear;
* `map_smul_I_of_basis`: the `∂̄`-condition at the level of the standard coordinate vectors
  implies that the real derivative commutes with multiplication by `I`.
-/

open Complex

namespace Commons.Analysis.Complex

/-- Complex scalar multiplication can be decomposed into real and imaginary parts:
`c • x = c.re • x + c.im • (I • x)`. -/
theorem smul_eq_re_smul_add_im_smul_I {E : Type*} [AddCommGroup E] [Module ℂ E] (c : ℂ) (x : E) :
    c • x = (c.re : ℝ) • x + (c.im : ℝ) • (Complex.I • x) := by
  conv_lhs => rw [← Complex.re_add_im c]
  rw [add_smul, mul_smul, Complex.coe_smul, Complex.coe_smul]

/-- A continuous real-linear map between complex normed spaces that commutes with multiplication
by `I` is complex linear. -/
lemma exists_complexLinear_of_map_smul_I {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] (ℓ : E →L[ℝ] F)
    (h : ∀ v, ℓ (Complex.I • v) = Complex.I • ℓ v) :
    ∃ ℓ' : E →L[ℂ] F, ℓ'.restrictScalars ℝ = ℓ := by
  refine ⟨{ toFun := ℓ, map_add' := fun x y => map_add ℓ x y, map_smul' := ?_, cont := ℓ.continuous }, ?_⟩
  · intro c x
    change ℓ (c • x) = c • ℓ x
    rw [smul_eq_re_smul_add_im_smul_I c x, map_add, ℓ.map_smul, ℓ.map_smul, h x,
      smul_eq_re_smul_add_im_smul_I c (ℓ x)]
  · rfl

/-- If a real-linear functional on `Fin d → ℂ` satisfies the Wirtinger `∂̄`-condition on the
standard coordinate vectors, then it commutes with multiplication by `I`. -/
lemma map_smul_I_of_basis {d : ℕ} {L : (Fin d → ℂ) →L[ℝ] ℂ}
    (hL : ∀ j, L (Pi.single j 1) + Complex.I * L (Pi.single j Complex.I) = 0) :
    ∀ v, L (Complex.I • v) = Complex.I • L v := by
  intro v
  have hLI : ∀ j, L (Pi.single j Complex.I) = Complex.I * L (Pi.single j 1) := by
    intro j
    have h1 : Complex.I * L (Pi.single j Complex.I) = - L (Pi.single j 1) := by
      linear_combination (hL j)
    have hI : (-Complex.I) * Complex.I = 1 := by
      rw [neg_mul, Complex.I_mul_I, neg_neg]
    calc L (Pi.single j Complex.I)
        = 1 * L (Pi.single j Complex.I) := (one_mul _).symm
      _ = ((-Complex.I) * Complex.I) * L (Pi.single j Complex.I) := by rw [hI]
      _ = (-Complex.I) * (Complex.I * L (Pi.single j Complex.I)) := by rw [mul_assoc]
      _ = (-Complex.I) * (- L (Pi.single j 1)) := by rw [h1]
      _ = Complex.I * L (Pi.single j 1) := by ring
  let b : Module.Basis (Σ _ : Fin d, Fin 2) ℝ (Fin d → ℂ) := Pi.basis (fun _ => Complex.basisOneI)
  have hsub : Set.range ⇑b ⊆ (Set.range (fun j : Fin d => Pi.single j (1:ℂ)) ∪
      Set.range (fun j : Fin d => Pi.single j Complex.I) : Set (Fin d → ℂ)) := by
    rintro y ⟨ji, rfl⟩
    obtain ⟨j, k⟩ := ji
    rw [Pi.basis_apply]
    fin_cases k
    · left; exact ⟨j, by simp⟩
    · right; exact ⟨j, by simp⟩
  have hspan : Submodule.span ℝ (Set.range (fun j : Fin d => Pi.single j (1:ℂ)) ∪
      Set.range (fun j : Fin d => Pi.single j Complex.I)) = ⊤ := by
    have hle : (⊤ : Submodule ℝ (Fin d → ℂ)) ≤ Submodule.span ℝ
        (Set.range (fun j : Fin d => Pi.single j (1:ℂ)) ∪
          Set.range (fun j : Fin d => Pi.single j Complex.I)) := by
      rw [← b.span_eq]
      exact Submodule.span_mono hsub
    exact top_le_iff.mp hle
  let f1 : (Fin d → ℂ) →ₗ[ℝ] ℂ := L.toLinearMap.comp (Algebra.lsmul ℝ ℝ (Fin d → ℂ) Complex.I)
  let f2 : (Fin d → ℂ) →ₗ[ℝ] ℂ := (Algebra.lsmul ℝ ℝ ℂ Complex.I).comp L.toLinearMap
  have key : f1 = f2 := by
    apply LinearMap.ext_on hspan
    intro x hx
    rcases hx with ⟨j, rfl⟩ | ⟨j, rfl⟩
    · change L (Complex.I • Pi.single j (1:ℂ)) = Complex.I • L (Pi.single j (1:ℂ))
      rw [← Pi.single_smul (f := fun _ : Fin d => ℂ) j Complex.I (1:ℂ), smul_eq_mul, mul_one,
        hLI j, smul_eq_mul]
    · change L (Complex.I • Pi.single j Complex.I) = Complex.I • L (Pi.single j Complex.I)
      rw [← Pi.single_smul (f := fun _ : Fin d => ℂ) j Complex.I Complex.I, smul_eq_mul,
        Complex.I_mul_I, Pi.single_neg, map_neg, hLI j, smul_eq_mul, ← mul_assoc, Complex.I_mul_I]
      ring
  have hv : f1 v = f2 v := LinearMap.congr_fun key v
  change L (Complex.I • v) = Complex.I • L v
  simp only [f1, f2, LinearMap.comp_apply, Algebra.lsmul_apply] at hv
  exact hv

/-- A real-differentiable function on `Fin d → ℂ` whose Wirtinger `∂̄`-derivatives vanish in
every coordinate is complex differentiable. -/
theorem differentiable_complex_of_dbar_eq_zero {d : ℕ} {f : (Fin d → ℂ) → ℂ}
    (hf : Differentiable ℝ f)
    (h : ∀ (j : Fin d) (z : Fin d → ℂ),
      fderiv ℝ f z (Pi.single j (1 : ℂ)) + Complex.I * fderiv ℝ f z (Pi.single j Complex.I) = 0) :
    Differentiable ℂ f := by
  intro x
  rw [differentiableAt_iff_restrictScalars ℝ (hf x)]
  obtain ⟨g', hg'⟩ :=
    exists_complexLinear_of_map_smul_I (fderiv ℝ f x) (map_smul_I_of_basis (fun j => h j x))
  exact ⟨g', hg'⟩

end Commons.Analysis.Complex