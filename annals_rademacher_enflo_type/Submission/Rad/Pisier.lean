import Mathlib
import Submission.Rad.Theta
set_option autoImplicit false
open Function MeasureTheory ProbabilityTheory Measure
open scoped ENNReal
noncomputable section
namespace RadType
open RademacherEnfloType

/-- The unnormalized weight `∏_j (1 + cos θ ξ_j)`. -/
def biasW2 (θ : ℝ) {n : ℕ} (ξ : Ω n) : ℝ :=
  ∏ j : Fin n, (1 + Real.cos θ * ((ξ j : C) : ℝ))

lemma biasW_eq_biasW2 (θ : ℝ) {n : ℕ} (ξ : Ω n) : biasW θ ξ = biasW2 θ ξ / (2 : ℝ) ^ n := by
  unfold biasW biasW2
  rw [Finset.prod_div_distrib]
  congr 1
  simp

/-- `biasW2` is smooth in `θ`. -/
lemma biasW2_hasDerivAt (θ : ℝ) {n : ℕ} (ξ : Ω n) :
    HasDerivAt (fun t : ℝ => biasW2 t ξ)
      (∑ j : Fin n, ((((Finset.univ : Finset (Fin n)).erase j).prod
          (fun k : Fin n => (1 + Real.cos θ * ((ξ k : C) : ℝ)))) *
        (-Real.sin θ * ((ξ j : C) : ℝ)))) θ := by
  classical
  have hcoord : ∀ j : Fin n, HasDerivAt
      (fun t : ℝ => (1 + Real.cos t * ((ξ j : C) : ℝ))) (-Real.sin θ * ((ξ j : C) : ℝ)) θ := by
    intro j
    have hc : HasDerivAt (fun t : ℝ => Real.cos t * ((ξ j : C) : ℝ))
        (-(Real.sin θ) * ((ξ j : C) : ℝ)) θ := by
      simpa [mul_comm] using (Real.hasDerivAt_cos θ).mul_const (((ξ j : C) : ℝ))
    simpa using hc.const_add (1 : ℝ)
  have hfun : (fun t : ℝ => biasW2 t ξ) =
      (∏ j : Fin n, (fun t : ℝ => 1 + Real.cos t * ((ξ j : C) : ℝ))) := by
    funext t
    simp [biasW2, Finset.prod_apply]
  rw [hfun]
  simpa [mul_comm, mul_left_comm, mul_assoc] using
    (HasDerivAt.finsetProd (𝕜 := ℝ) (x := θ) (u := (Finset.univ : Finset (Fin n)))
      (f := fun (j : Fin n) (t : ℝ) => 1 + Real.cos t * ((ξ j : C) : ℝ))
      (f' := fun j : Fin n => -Real.sin θ * ((ξ j : C) : ℝ))
      (by intro j hj; simpa using hcoord j))

/-- The derivative of the biased weight. -/
def biasWderiv (θ : ℝ) {n : ℕ} (ξ : Ω n) : ℝ :=
  (∑ j : Fin n, ((((Finset.univ : Finset (Fin n)).erase j).prod
          (fun k : Fin n => (1 + Real.cos θ * ((ξ k : C) : ℝ)))) *
        (-Real.sin θ * ((ξ j : C) : ℝ)))) / (2 : ℝ) ^ n

/-- `biasW` is smooth in `θ`. -/
lemma biasW_hasDerivAt (θ : ℝ) {n : ℕ} (ξ : Ω n) :
    HasDerivAt (fun t : ℝ => biasW t ξ) (biasWderiv θ ξ) θ := by
  unfold biasWderiv
  have h1 := biasW2_hasDerivAt θ ξ
  have hrel : (fun t : ℝ => biasW t ξ) = fun t : ℝ => biasW2 t ξ / (2 : ℝ) ^ n := by
    funext t
    exact biasW_eq_biasW2 t ξ
  rw [hrel]
  simpa [div_eq_mul_inv] using h1.div_const ((2 : ℝ) ^ n)

/-- The heat semigroup (real-valued) is smooth in `θ`. -/
lemma heat_hasDerivAt_real {n : ℕ} (f : Ω n → ℝ) (x : Ω n) (θ : ℝ) :
    HasDerivAt (fun t : ℝ => heat t f x)
      (∑ ξ : Ω n, (biasWderiv θ ξ) * f (mulΩ x ξ)) θ := by
  classical
  unfold heat
  change HasDerivAt (fun t : ℝ => ∑ ξ : Ω n, (biasW t ξ) * f (mulΩ x ξ))
      (∑ ξ : Ω n, (biasWderiv θ ξ) * f (mulΩ x ξ)) θ
  have hsum : ∀ ξ : Ω n, HasDerivAt
      (fun t : ℝ => (biasW t ξ) * f (mulΩ x ξ)) ((biasWderiv θ ξ) * f (mulΩ x ξ)) θ := by
    intro ξ
    simpa using (biasW_hasDerivAt θ ξ).mul_const (f (mulΩ x ξ))
  have hfun : (fun t : ℝ => ∑ ξ : Ω n, (biasW t ξ) * f (mulΩ x ξ)) =
      ∑ ξ : Ω n, (fun t : ℝ => (biasW t ξ) * f (mulΩ x ξ)) := by
    funext t
    simp
  rw [hfun]
  simpa using (HasDerivAt.sum (u := Finset.univ) (by
    intro ξ hξ
    exact hsum ξ))

end RadType
end
