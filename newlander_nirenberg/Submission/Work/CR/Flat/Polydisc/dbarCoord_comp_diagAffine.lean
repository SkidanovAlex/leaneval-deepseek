import Mathlib
import Submission.Work.CR.Flat.Polydisc

namespace Work.CR.Flat.Polydisc

/-- The real-linear part of the diagonal affine map `z ↦ (i ↦ b i + (a i : ℂ) * z i)`:
the continuous `ℝ`-linear map `w ↦ (i ↦ (a i : ℂ) * w i)`. -/
noncomputable def diagLin {n : ℕ} (a : Fin n → ℝ) :
    (Fin n → ℂ) →L[ℝ] (Fin n → ℂ) :=
  ContinuousLinearMap.pi fun i =>
    (ContinuousLinearMap.mul ℝ ℂ (a i : ℂ)).comp (ContinuousLinearMap.proj i)

lemma diagLin_apply {n : ℕ} (a : Fin n → ℝ) (w : Fin n → ℂ) :
    diagLin a w = fun i => (a i : ℂ) * w i := by
  funext i
  simp [diagLin]

/-- The diagonal affine map `z ↦ (i ↦ b i + (a i : ℂ) * z i)` has derivative
`diagLin a` at every point. -/
lemma hasFDerivAt_diagAffine {n : ℕ} (a : Fin n → ℝ) (b : Fin n → ℂ) (z : Fin n → ℂ) :
    HasFDerivAt (fun z' : Fin n → ℂ => fun i => b i + (a i : ℂ) * z' i) (diagLin a) z := by
  refine hasFDerivAt_pi.2 fun i => ?_
  have hL : (ContinuousLinearMap.mul ℝ ℂ (a i : ℂ)).comp
      (ContinuousLinearMap.proj (R := ℝ) i : (Fin n → ℂ) →L[ℝ] ℂ)
      = (ContinuousLinearMap.mul ℝ ℂ (a i : ℂ)).comp (ContinuousLinearMap.proj i) := rfl
  rw [hL]
  simpa using (((ContinuousLinearMap.mul ℝ ℂ (a i : ℂ)).comp
    (ContinuousLinearMap.proj (R := ℝ) i : (Fin n → ℂ) →L[ℝ] ℂ)).hasFDerivAt.const_add (b i))

/-- `diagLin a` acts on the `j`-th real unit vector by the real scalar `a j`. -/
lemma diagLin_single_one {n : ℕ} (a : Fin n → ℝ) (j : Fin n) :
    diagLin a (Pi.single j (1 : ℂ)) = a j • (Pi.single j (1 : ℂ) : Fin n → ℂ) := by
  ext i
  simp only [diagLin_apply, Pi.smul_apply]
  by_cases h : i = j
  · subst h; simp
  · rw [Pi.single_eq_of_ne h]; simp

/-- `diagLin a` acts on the `j`-th imaginary unit vector by the real scalar `a j`. -/
lemma diagLin_single_I {n : ℕ} (a : Fin n → ℝ) (j : Fin n) :
    diagLin a (Pi.single j Complex.I) = a j • (Pi.single j Complex.I : Fin n → ℂ) := by
  ext i
  simp only [diagLin_apply, Pi.smul_apply]
  by_cases h : i = j
  · subst h; simp
  · rw [Pi.single_eq_of_ne h]; simp

/-- Chain rule for the flat `∂̄`-operator under a diagonal affine map
`z ↦ (i ↦ b i + (a i : ℂ) * z i)`: differentiating a function `U` along the `(0,1)`
direction of the `j`-th coordinate after the substitution gives `(a j : ℂ)` times the
`∂̄_j`-derivative of `U` at the image point. -/
theorem dbarCoord_comp_diagAffine {n : ℕ} (a : Fin n → ℝ) (b : Fin n → ℂ) (j : Fin n)
    {U : (Fin n → ℂ) → ℂ} {z : Fin n → ℂ}
    (hU : DifferentiableAt ℝ U (fun i => b i + (a i : ℂ) * z i)) :
    Work.CR.Flat.dbarCoord j (fun z' => U (fun i => b i + (a i : ℂ) * z' i)) z
      = (a j : ℂ) * Work.CR.Flat.dbarCoord j U (fun i => b i + (a i : ℂ) * z i) := by
  -- Chain rule: the derivative of `U ∘ φ` is `dU(φ z) ∘ dφ`, where `dφ = diagLin a`.
  have hcomp : fderiv ℝ (fun z' => U (fun i => b i + (a i : ℂ) * z' i)) z
      = (fderiv ℝ U (fun i => b i + (a i : ℂ) * z i)).comp (diagLin a) :=
    (hU.hasFDerivAt.comp z (hasFDerivAt_diagAffine a b z)).fderiv
  unfold Work.CR.Flat.dbarCoord
  rw [hcomp]
  simp only [ContinuousLinearMap.comp_apply]
  -- Evaluate on the two vectors spanning the `(0,1)` direction of the `j`-th coordinate.
  rw [diagLin_single_one, diagLin_single_I, map_smul, map_smul, Complex.real_smul,
    Complex.real_smul]
  ring

end Work.CR.Flat.Polydisc
