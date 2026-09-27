import Mathlib
import Submission.Work.Mostow.linPartAux
import Submission.Work.Mostow.Margulis.ComplexifyOrth

namespace Work.Mostow

/-- If `μ` is an eigenvalue of the complexification `cAct R` of the real linear isometry `R`, then `μ` is a root of the characteristic polynomial of the complexified matrix `Rmat n R` of `R`. -/
theorem cAct_eigen_root_charpoly (n : ℕ) (R : Submission.Mostow.E n ≃ₗᵢ[ℝ] Submission.Mostow.E n) (μ : ℂ)
    (hμ : Module.End.HasEigenvalue
      (Work.Mostow.Margulis.cAct R : (Submission.Mostow.E n × Submission.Mostow.E n) →ₗ[ℂ] (Submission.Mostow.E n × Submission.Mostow.E n)) μ) :
    (Matrix.charpoly ((Work.Mostow.Rmat n R).map (algebraMap ℝ ℂ))).IsRoot μ := by
  -- Take an eigenvector `(u, w)` of the complexification.
  obtain ⟨x, hxe⟩ := hμ.exists_hasEigenvector
  obtain ⟨hxmem, hxne⟩ := Module.End.hasEigenvector_iff.mp hxe
  have hx := Module.End.mem_eigenspace_iff.mp hxmem
  obtain ⟨u, w⟩ := x
  change Work.Mostow.Margulis.cAct R (u, w) = μ • (u, w) at hx
  rw [Work.Mostow.Margulis.cAct_apply, Work.Mostow.Margulis.csmul_apply] at hx
  have hu : R u = μ.re • u - μ.im • w := congrArg Prod.fst hx
  have hw : R w = μ.im • u + μ.re • w := congrArg Prod.snd hx
  -- The complex vector `z` obtained by combining the coordinates of `u` and `w`.
  let z : Fin n → ℂ := fun j => (u j : ℂ) + Complex.I * (w j : ℂ)
  have hzne : z ≠ 0 := by
    intro hz
    have hzu : u = 0 := by
      apply WithLp.ofLp_injective
      funext j
      have h := congrFun hz j
      simp only [z, Pi.zero_apply] at h
      have hre := congrArg Complex.re h
      simpa using hre
    have hzw : w = 0 := by
      apply WithLp.ofLp_injective
      funext j
      have h := congrFun hz j
      simp only [z, Pi.zero_apply] at h
      have him := congrArg Complex.im h
      simpa using him
    exact hxne (by rw [hzu, hzw]; rfl)
  -- `z` is an eigenvector of the complexified matrix with eigenvalue `μ`.
  have hzEig : ((Work.Mostow.Rmat n R).map (algebraMap ℝ ℂ)).mulVecLin z = μ • z := by
    rw [Matrix.mulVecLin_apply]
    funext i
    change Matrix.mulVec ((Work.Mostow.Rmat n R).map (algebraMap ℝ ℂ))
        (fun j => (u j : ℂ) + Complex.I * (w j : ℂ)) i
      = μ * ((u i : ℂ) + Complex.I * (w i : ℂ))
    have hmv : Matrix.mulVec ((Work.Mostow.Rmat n R).map (algebraMap ℝ ℂ))
        (fun j => (u j : ℂ) + Complex.I * (w j : ℂ)) i
        = ((R u) i : ℂ) + Complex.I * ((R w) i : ℂ) := by
      rw [Matrix.mulVec, dotProduct]
      simp only [Matrix.map_apply, Complex.coe_algebraMap]
      have hterm : ∀ j : Fin n,
          ((Work.Mostow.Rmat n R i j : ℝ) : ℂ) * ((u j : ℂ) + Complex.I * (w j : ℂ))
            = ((Work.Mostow.Rmat n R i j * u j : ℝ) : ℂ)
                + Complex.I * ((Work.Mostow.Rmat n R i j * w j : ℝ) : ℂ) := by
        intro j
        push_cast
        ring
      have hsum : (∑ j : Fin n,
            ((Work.Mostow.Rmat n R i j : ℝ) : ℂ) * ((u j : ℂ) + Complex.I * (w j : ℂ)))
          = ∑ j : Fin n, (((Work.Mostow.Rmat n R i j * u j : ℝ) : ℂ)
                + Complex.I * ((Work.Mostow.Rmat n R i j * w j : ℝ) : ℂ)) :=
        Finset.sum_congr rfl (fun j _ => hterm j)
      rw [hsum, Finset.sum_add_distrib, ← Complex.ofReal_sum, ← Finset.mul_sum, ← Complex.ofReal_sum]
      rw [Work.Mostow.Rmat_apply, Work.Mostow.Rmat_apply]
    rw [hmv]
    have h1 : (R u) i = μ.re * u i - μ.im * w i := by
      rw [hu]
      simp only [WithLp.ofLp_sub, WithLp.ofLp_smul, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    have h2 : (R w) i = μ.im * u i + μ.re * w i := by
      rw [hw]
      simp only [WithLp.ofLp_add, WithLp.ofLp_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    have hcx : μ * ((u i : ℂ) + Complex.I * (w i : ℂ))
        = ((μ.re * u i - μ.im * w i : ℝ) : ℂ)
            + Complex.I * ((μ.im * u i + μ.re * w i : ℝ) : ℂ) := by
      apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im] <;> try ring
    rw [h1, h2, hcx]
  -- conclude via `charpoly_mulVecLin` and `hasEigenvalue_iff_isRoot_charpoly`.
  rw [← Matrix.charpoly_mulVecLin ((Work.Mostow.Rmat n R).map (algebraMap ℝ ℂ))]
  rw [← Module.End.hasEigenvalue_iff_isRoot_charpoly
        (((Work.Mostow.Rmat n R).map (algebraMap ℝ ℂ)).mulVecLin) μ]
  exact Module.End.hasEigenvalue_of_hasEigenvector
    (Module.End.hasEigenvector_iff.mpr ⟨Module.End.mem_eigenspace_iff.mpr hzEig, hzne⟩)

end Work.Mostow
