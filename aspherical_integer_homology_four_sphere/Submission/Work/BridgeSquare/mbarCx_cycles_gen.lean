import Mathlib
import Submission.Work.BridgeSquare.Data

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.BridgeSquare

noncomputable section

open Work.Certificates
open Work.HomologyIso.Gen (mbarDim mbarB mbarZ mbarBd mbarRho mbarH mbarSDR mbarCx mbarSDR_check)

/-- Semantics of `SOp.toLin` as a matrix–vector product: the linear map attached to a sparse
operator applied to a vector is the product of its matrix with that vector. -/
theorem toLin_eq_mulVec {n m : ℕ} (A : SOp n m) (v : Fin m → ℤ) :
    A.toLin v = Matrix.mulVec A.toMatrix v := by
  rw [SOp.toLin, Matrix.toLin'_apply]

/-- `bdryGen k` and `mbarZ k` differ by the boundary `mbarBd k * bdryWit k`
(the matrix form of `Gen.bdryGen*_hom`). -/
theorem bdryGen_sub_mbarZ (k : ℕ) (hk : 1 ≤ k ∧ k ≤ 3) :
    (bdryGen k).toMatrix - (mbarZ k).toMatrix = (mbarBd k).toMatrix * (bdryWit k).toMatrix := by
  have h := SOp.eqb_sound (bdryGen_hom k hk)
  simpa only [SOp.toMatrix_sub, SOp.toMatrix_mul] using h

/-- **The SDR identity for a single degree.**  If `z` is a cycle in degree `j + 1` and `g` is a
family of generators homologous to the SDR section `mbarZ (j+1)` (`g - mbarZ = mbarBd * wit`),
then `z` is a `ℤ`-linear combination of the columns of `g` plus a boundary in degree `j + 2`. -/
theorem cycles_step (j : ℕ) (hj : j < 5)
    (z : Fin (mbarDim (j+1)) → ℤ) (hz : (mbarBd j).toLin z = 0)
    (g : SOp (mbarDim (j+1)) (mbarB (j+1)))
    (wit : SOp (mbarDim (j+2)) (mbarB (j+1)))
    (hg : g.toMatrix - (mbarZ (j+1)).toMatrix = (mbarBd (j+1)).toMatrix * wit.toMatrix) :
    ∃ (a : Fin (mbarB (j+1)) → ℤ) (w : Fin (mbarDim (j+2)) → ℤ),
      z = g.toLin a + (mbarBd (j+1)).toLin w := by
  -- The `1 - Zρ = ∂h + h∂` equation in degree `j`.
  have h4 := (Work.Certificates.SDR.check_implies mbarSDR mbarSDR_check j hj).2.2.2
  have h4' : 1 - (mbarZ (j+1)).toMatrix * (mbarRho (j+1)).toMatrix
      = (mbarBd (j+1)).toMatrix * (mbarH (j+1)).toMatrix
        + (mbarH j).toMatrix * (mbarBd j).toMatrix := h4
  -- Apply it to the cycle `z`.
  have h4z := congrArg (fun M : Matrix (Fin (mbarDim (j+1))) (Fin (mbarDim (j+1))) ℤ =>
      Matrix.mulVec M z) h4'
  simp only [Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.add_mulVec,
    ← Matrix.mulVec_mulVec] at h4z
  simp only [← toLin_eq_mulVec] at h4z
  -- The `h∂` term vanishes because `z` is a cycle.
  have hA : z = (mbarZ (j+1)).toLin ((mbarRho (j+1)).toLin z)
      + (mbarBd (j+1)).toLin ((mbarH (j+1)).toLin z) := by
    simp only [hz, map_zero, add_zero] at h4z
    rw [sub_eq_iff_eq_add'] at h4z
    exact h4z
  -- `g` differs from `mbarZ` by the boundary `mbarBd * wit`.
  have hB : g.toLin ((mbarRho (j+1)).toLin z)
      = (mbarZ (j+1)).toLin ((mbarRho (j+1)).toLin z)
        + (mbarBd (j+1)).toLin (wit.toLin ((mbarRho (j+1)).toLin z)) := by
    have hb := congrArg (fun M : Matrix (Fin (mbarDim (j+1))) (Fin (mbarB (j+1))) ℤ =>
        Matrix.mulVec M ((mbarRho (j+1)).toLin z)) hg
    simp only [Matrix.sub_mulVec, ← Matrix.mulVec_mulVec] at hb
    simp only [← toLin_eq_mulVec] at hb
    rw [sub_eq_iff_eq_add'] at hb
    exact hb
  -- Assemble: `a := ρ z` and `w := h z - wit a`.
  refine ⟨(mbarRho (j+1)).toLin z,
    (mbarH (j+1)).toLin z - wit.toLin ((mbarRho (j+1)).toLin z), ?_⟩
  calc z = (mbarZ (j+1)).toLin ((mbarRho (j+1)).toLin z)
        + (mbarBd (j+1)).toLin ((mbarH (j+1)).toLin z) := hA
    _ = g.toLin ((mbarRho (j+1)).toLin z)
        + (mbarBd (j+1)).toLin ((mbarH (j+1)).toLin z
            - wit.toLin ((mbarRho (j+1)).toLin z)) := by
          rw [hB, map_sub]; abel

theorem mbarCx_cycles_gen (k : ℕ) (hk : k = 1 ∨ k = 2 ∨ k = 3)
    (z : Fin (Work.HomologyIso.Gen.mbarDim k) → ℤ)
    (hz : (Work.BridgeSquare.bdryGenBd k).toLin z = 0) :
    ∃ (a : Fin (Work.HomologyIso.Gen.mbarB k) → ℤ)
      (w : Fin (Work.HomologyIso.Gen.mbarDim (k + 1)) → ℤ),
      z = (Work.BridgeSquare.bdryGen k).toLin a
        + (Work.HomologyIso.Gen.mbarBd k).toLin w := by
  rcases hk with rfl | rfl | rfl
  · exact cycles_step 0 (by omega) z hz (bdryGen 1) (bdryWit 1)
      (bdryGen_sub_mbarZ 1 (by omega))
  · exact cycles_step 1 (by omega) z hz (bdryGen 2) (bdryWit 2)
      (bdryGen_sub_mbarZ 2 (by omega))
  · exact cycles_step 2 (by omega) z hz (bdryGen 3) (bdryWit 3)
      (bdryGen_sub_mbarZ 3 (by omega))

end

end Work.BridgeSquare
