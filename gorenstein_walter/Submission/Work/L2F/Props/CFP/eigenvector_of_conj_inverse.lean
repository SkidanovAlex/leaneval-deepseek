import Mathlib

open scoped Matrix

-- The skeleton file nests `Work.L2F.Props.CFP` twice (a stub-generator artefact);
-- silence the resulting duplicate-namespace linter warning.
set_option linter.dupNamespace false

namespace Work.L2F.Props.CFP

namespace Work.L2F.Props.CFP

/-- `X T = ε (T X⁻¹)` together with an eigenvector `v` of `X` with eigenvalue `c`
(so that `X v = c v`) forces the vector `T v` to be an eigenvector of `X` with
eigenvalue `ε c⁻¹`. -/
theorem eigenvector_of_conj_inverse (F : Type*) [Field F] (T : GL (Fin 2) F)
    (X : Matrix.SpecialLinearGroup (Fin 2) F) (v : Fin 2 → F) (c eps : F)
    (hXv : Matrix.mulVec (X : Matrix (Fin 2) (Fin 2) F) v = c • v)
    (hrel : (X : Matrix (Fin 2) (Fin 2) F) * (T : Matrix (Fin 2) (Fin 2) F)
      = eps • ((T : Matrix (Fin 2) (Fin 2) F) * ((X⁻¹ : Matrix.SpecialLinearGroup (Fin 2) F)
          : Matrix (Fin 2) (Fin 2) F))) :
    Matrix.mulVec (X : Matrix (Fin 2) (Fin 2) F)
        (Matrix.mulVec (T : Matrix (Fin 2) (Fin 2) F) v)
      = (eps * c⁻¹) • Matrix.mulVec (T : Matrix (Fin 2) (Fin 2) F) v := by
  -- Write `Y` for the matrix underlying `X⁻¹` (which is `adjugate X`, since `det X = 1`).
  set Y : Matrix (Fin 2) (Fin 2) F :=
    ((X⁻¹ : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) with hYdef
  -- `Y` is a left inverse of `X`.
  have hYX : Y * (X : Matrix (Fin 2) (Fin 2) F) = 1 := by
    rw [hYdef, Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_mul,
      Matrix.SpecialLinearGroup.det_coe, one_smul]
  -- Key point: `Y v = c⁻¹ • v`.  Indeed `X v = c v`, so applying `Y` gives
  -- `v = c • (Y v)`; if `c ≠ 0` this yields the claim, while if `c = 0` it forces `v = 0`.
  have hYv : Y *ᵥ v = c⁻¹ • v := by
    have h2 : c • (Y *ᵥ v) = v := by
      calc c • (Y *ᵥ v) = Y *ᵥ (c • v) := (Matrix.mulVec_smul Y c v).symm
        _ = Y *ᵥ (X *ᵥ v) := by rw [hXv]
        _ = (Y * (X : Matrix (Fin 2) (Fin 2) F)) *ᵥ v :=
              Matrix.mulVec_mulVec v Y (X : Matrix (Fin 2) (Fin 2) F)
        _ = v := by rw [hYX, Matrix.one_mulVec]
    rcases eq_or_ne c 0 with hc | hc
    · subst hc
      have hv0 : v = 0 := by
        have := h2
        rw [zero_smul] at this
        exact this.symm
      rw [hv0]
      simp
    · have h3 : c⁻¹ • v = Y *ᵥ v := by
        calc c⁻¹ • v = c⁻¹ • (c • (Y *ᵥ v)) := by rw [h2]
          _ = (c⁻¹ * c) • (Y *ᵥ v) := by rw [smul_smul]
          _ = Y *ᵥ v := by rw [inv_mul_cancel₀ hc, one_smul]
      exact h3.symm
  -- Now multiply the relation `X T = ε • (T Y)` by `v`.
  calc (X : Matrix (Fin 2) (Fin 2) F) *ᵥ ((T : Matrix (Fin 2) (Fin 2) F) *ᵥ v)
      = ((X : Matrix (Fin 2) (Fin 2) F) * (T : Matrix (Fin 2) (Fin 2) F)) *ᵥ v :=
          Matrix.mulVec_mulVec v _ _
    _ = (eps • ((T : Matrix (Fin 2) (Fin 2) F) * Y)) *ᵥ v := by rw [hrel]
    _ = eps • (((T : Matrix (Fin 2) (Fin 2) F) * Y) *ᵥ v) := Matrix.smul_mulVec eps _ _
    _ = eps • ((T : Matrix (Fin 2) (Fin 2) F) *ᵥ (Y *ᵥ v)) := by rw [Matrix.mulVec_mulVec]
    _ = eps • ((T : Matrix (Fin 2) (Fin 2) F) *ᵥ (c⁻¹ • v)) := by rw [hYv]
    _ = eps • (c⁻¹ • ((T : Matrix (Fin 2) (Fin 2) F) *ᵥ v)) := by rw [Matrix.mulVec_smul]
    _ = (eps * c⁻¹) • ((T : Matrix (Fin 2) (Fin 2) F) *ᵥ v) := by rw [smul_smul]

end Work.L2F.Props.CFP

/-- The same statement, exposed under the name `Work.L2F.Props.CFP.eigenvector_of_conj_inverse`
used by the requester (the module's main proof sits in the doubly nested namespace
`Work.L2F.Props.CFP.Work.L2F.Props.CFP`, the skeleton's original layout). -/
theorem eigenvector_of_conj_inverse (F : Type*) [Field F] (T : GL (Fin 2) F)
    (X : Matrix.SpecialLinearGroup (Fin 2) F) (v : Fin 2 → F) (c eps : F)
    (hXv : Matrix.mulVec (X : Matrix (Fin 2) (Fin 2) F) v = c • v)
    (hrel : (X : Matrix (Fin 2) (Fin 2) F) * (T : Matrix (Fin 2) (Fin 2) F)
      = eps • ((T : Matrix (Fin 2) (Fin 2) F) * ((X⁻¹ : Matrix.SpecialLinearGroup (Fin 2) F)
          : Matrix (Fin 2) (Fin 2) F))) :
    Matrix.mulVec (X : Matrix (Fin 2) (Fin 2) F)
        (Matrix.mulVec (T : Matrix (Fin 2) (Fin 2) F) v)
      = (eps * c⁻¹) • Matrix.mulVec (T : Matrix (Fin 2) (Fin 2) F) v :=
  _root_.Work.L2F.Props.CFP.Work.L2F.Props.CFP.eigenvector_of_conj_inverse
    F T X v c eps hXv hrel

end Work.L2F.Props.CFP
