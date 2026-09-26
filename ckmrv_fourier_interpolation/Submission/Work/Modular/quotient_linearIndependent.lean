import Mathlib
import Submission.Work.Modular.GroupAlgebra

namespace Work.Modular

open Work.Modular
open scoped MonoidAlgebra

/-- The images of `1, T, TS, S, ST, STS` in `ℂ[Γ]/I` are linearly independent. -/
theorem quotient_linearIndependent :
    LinearIndependent ℂ (fun i : Fin 6 => Submodule.mkQ idealI (basisElem i)) := by
  -- The first row of `σ (basisElem i)` is the `i`-th standard basis vector.
  have hrow : ∀ i : Fin 6, (sigmaAlg (basisElem i)) 0 = Pi.single i 1 := by
    intro i
    fin_cases i <;>
      ext j <;>
      fin_cases j <;>
      simp [basisElem, map_mul, sigmaAlg_tR, sigmaAlg_sR,
            Matrix.mul_apply, sigmaS, sigmaT, Fin.sum_univ_six]
  -- The first row of `(σ(T) - 1) ^ 2` vanishes.
  have hA : ((sigmaT - 1 : Matrix (Fin 6) (Fin 6) ℂ) ^ 2) 0 = 0 := by
    ext j; fin_cases j <;>
      simp [pow_two, Matrix.mul_apply, Matrix.sub_apply, sigmaT, Fin.sum_univ_six] <;> norm_num
  -- The first row of `σ(S) * (σ(T) - 1) ^ 2` vanishes.
  have hSA : (sigmaS * (sigmaT - 1 : Matrix (Fin 6) (Fin 6) ℂ) ^ 2) 0 = 0 := by
    ext j; fin_cases j <;>
      simp [pow_two, Matrix.mul_apply, Matrix.sub_apply, sigmaS, sigmaT, Fin.sum_univ_six] <;> norm_num
  -- A matrix whose first row vanishes stays with vanishing first row after right multiplication.
  have hrow0 : ∀ {A : Matrix (Fin 6) (Fin 6) ℂ}, A 0 = 0 →
      ∀ M : Matrix (Fin 6) (Fin 6) ℂ, (A * M) 0 = 0 := by
    intro A hAzero M
    ext j
    rw [Matrix.mul_apply]
    apply Finset.sum_eq_zero
    intro k _
    rw [congr_fun hAzero k, Pi.zero_apply, zero_mul]
  -- The first row of `σ` vanishes on the right ideal `I`.
  have hideal : ∀ r ∈ idealI, (sigmaAlg r) 0 = 0 := by
    intro r hr
    unfold idealI at hr
    refine Submodule.span_induction (p := fun r _ => (sigmaAlg r) 0 = 0) ?_ ?_ ?_ ?_ hr
    · intro x hx
      rcases hx with ⟨r', rfl⟩ | ⟨r', rfl⟩
      · have hx' : sigmaAlg ((tR - 1) ^ 2 * r') = (sigmaT - 1) ^ 2 * sigmaAlg r' := by
          rw [map_mul, map_pow, map_sub, map_one, sigmaAlg_tR]
        rw [hx']
        exact hrow0 hA _
      · have hx' : sigmaAlg (sR * (tR - 1) ^ 2 * r') =
            sigmaS * ((sigmaT - 1) ^ 2) * sigmaAlg r' := by
          rw [map_mul, map_mul, map_pow, map_sub, map_one, sigmaAlg_sR, sigmaAlg_tR]
        rw [hx']
        exact hrow0 hSA _
    · rw [map_zero]
      rfl
    · intro x y hx hy hpx hpy
      ext j
      rw [map_add, Matrix.add_apply, congr_fun hpx j, congr_fun hpy j, Pi.zero_apply, zero_add]
    · intro a x hx hpx
      ext j
      rw [map_smul, Matrix.smul_apply, congr_fun hpx j, Pi.zero_apply, smul_zero]
  rw [Fintype.linearIndependent_iff]
  intro g hg j
  have h1 : Submodule.mkQ idealI (∑ i, g i • basisElem i) = 0 := by
    rw [map_sum]
    simp only [map_smul]
    exact hg
  have hx : (∑ i, g i • basisElem i) ∈ idealI := by
    rw [Submodule.mkQ_apply] at h1
    exact (Submodule.Quotient.mk_eq_zero idealI).mp h1
  have h0 : (sigmaAlg (∑ i, g i • basisElem i)) 0 j = 0 := congr_fun (hideal _ hx) j
  have hval : (sigmaAlg (∑ i, g i • basisElem i)) 0 j = g j := by
    rw [map_sum]
    simp only [map_smul, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, hrow, Pi.single_apply,
      mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  rw [← hval]; exact h0

end Work.Modular
