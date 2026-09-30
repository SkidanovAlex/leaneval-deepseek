import Mathlib
import Submission.Work.HomologyMV.LinAlg

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.HomologyMV

/-!
# The cokernel in normal form

This file proves `coker_toLin_iso_int_of_normalForm`: the cokernel of an `(m+1) × m` integer matrix
`A` whose range becomes the range of the standard inclusion `inclMat m = [1_m ; 0]` under a
unimodular change of basis is `ℤ`.

The proof is concrete.  Let `q : (Fin (m+1) → ℤ) →ₗ[ℤ] ℤ` be the *last coordinate* functional; its
kernel is exactly the range of `inclMat m` (`ker_lastCoord_eq_range_inclMat`).  The change of basis
`U` (with inverse `V`) transports this to the functional `φ = q.comp (toLin' U)`: its kernel is
`range (toLin' A)` and it is surjective — the cokernel of `A` is then
`M ⧸ range A = M ⧸ ker φ ≅ φ.range = ℤ`.
-/

noncomputable section

/-- The last row of `inclMat m` has zero entry everywhere. -/
theorem inclMat_mulVec_last (m : ℕ) (v : Fin m → ℤ) :
    (inclMat m).mulVec v (Fin.last m) = 0 := by
  rw [Matrix.mulVec_apply]
  simp only [dotProduct, Matrix.row, inclMat]
  apply Finset.sum_eq_zero
  intro i _
  simp [ne_of_gt (Fin.isLt i)]

/-- A vector whose last coordinate vanishes is the image under `inclMat m` of its restriction to the
first `m` coordinates. -/
theorem inclMat_mulVec_restrict (m : ℕ) (y : Fin (m + 1) → ℤ) (hy : y (Fin.last m) = 0) :
    (inclMat m).mulVec (fun j => y j.castSucc) = y := by
  funext i
  refine Fin.lastCases ?_ ?_ i
  · rw [inclMat_mulVec_last]
    exact hy.symm
  · intro j
    rw [Matrix.mulVec_apply]
    simp only [dotProduct, Matrix.row, inclMat]
    rw [Finset.sum_eq_single j]
    · simp
    · intro b _ hb
      have hbj : ¬ ((↑j : ℕ) = ↑b) := fun h => hb ((Fin.val_eq_val j b).mp h).symm
      simp only [Fin.val_castSucc, hbj, ite_false, zero_mul]
    · intro h
      exact absurd (Finset.mem_univ j) h

/-- The kernel of the last-coordinate functional on `ℤ^{m+1}` is the range of `inclMat m`. -/
theorem ker_lastCoord_eq_range_inclMat (m : ℕ) :
    (LinearMap.proj (Fin.last m) : (Fin (m + 1) → ℤ) →ₗ[ℤ] ℤ).ker
      = (Matrix.toLin' (inclMat m)).range := by
  apply le_antisymm
  · intro y hy
    rw [LinearMap.mem_ker] at hy
    rw [LinearMap.mem_range]
    refine ⟨fun j => y j.castSucc, ?_⟩
    rw [Matrix.toLin'_apply]
    rw [LinearMap.proj_apply] at hy
    exact inclMat_mulVec_restrict m y hy
  · intro y hy
    rw [LinearMap.mem_range] at hy
    obtain ⟨w, hw⟩ := hy
    rw [LinearMap.mem_ker, LinearMap.proj_apply, ← hw, Matrix.toLin'_apply]
    exact inclMat_mulVec_last m w

/-- The cokernel of an `(m+1) × m` integer matrix `A` that becomes the normal form `inclMat m = [1_m ; 0]` after a unimodular change of basis `U` (with inverse `V`) is `ℤ`. This is the certificate behind `H₀(M̂) ≅ coker φ₀ ≅ ℤ`, the alternative to getting `H₀ ≅ ℤ` from connectedness. -/
theorem coker_toLin_iso_int_of_normalForm (m : ℕ) (A : Matrix (Fin (m + 1)) (Fin m) ℤ) (U V : Matrix (Fin (m + 1)) (Fin (m + 1)) ℤ) (hUV : U * V = 1) (hVU : V * U = 1) (hincl : U * A = inclMat m) : Nonempty (((Fin (m + 1) → ℤ) ⧸ (Matrix.toLin' A).range) ≃ₗ[ℤ] ℤ) := by
  set q : (Fin (m + 1) → ℤ) →ₗ[ℤ] ℤ := LinearMap.proj (Fin.last m) with hq
  set φ : (Fin (m + 1) → ℤ) →ₗ[ℤ] ℤ := q.comp (Matrix.toLin' U) with hφ
  have hkerq : q.ker = (Matrix.toLin' (inclMat m)).range := by
    rw [hq]; exact ker_lastCoord_eq_range_inclMat m
  have hker : φ.ker = (Matrix.toLin' A).range := by
    apply le_antisymm
    · intro x hx
      rw [LinearMap.mem_ker] at hx
      have hxq : q (Matrix.toLin' U x) = 0 := by
        simpa only [hφ, LinearMap.comp_apply] using hx
      have hmem : Matrix.toLin' U x ∈ q.ker := hxq
      rw [hkerq, LinearMap.mem_range] at hmem
      obtain ⟨w, hw⟩ := hmem
      rw [LinearMap.mem_range]
      refine ⟨w, ?_⟩
      have hcomb : Matrix.toLin' U (Matrix.toLin' A w) = Matrix.toLin' U x := by
        rw [Matrix.toLin'_apply, Matrix.toLin'_apply, Matrix.mulVec_mulVec, hincl]
        simpa only [Matrix.toLin'_apply] using hw
      exact LinearMap.ker_eq_bot.mp (ker_toLin'_eq_bot_of_mul_eq_one U V hVU) hcomb
    · intro x hx
      rw [LinearMap.mem_range] at hx
      obtain ⟨w, rfl⟩ := hx
      rw [LinearMap.mem_ker]
      have hstep : φ (Matrix.toLin' A w) = q (Matrix.toLin' (inclMat m) w) := by
        simp only [hφ, LinearMap.comp_apply]
        simp only [Matrix.toLin'_apply, Matrix.mulVec_mulVec, hincl]
      rw [hstep]
      have hmem : Matrix.toLin' (inclMat m) w ∈ q.ker := by
        rw [hkerq, LinearMap.mem_range]; exact ⟨w, rfl⟩
      simpa only [LinearMap.mem_ker] using hmem
  have htop : φ.range = ⊤ := by
    rw [LinearMap.range_eq_top]
    intro z
    refine ⟨Matrix.toLin' V (Function.update (0 : Fin (m + 1) → ℤ) (Fin.last m) z), ?_⟩
    have hstep : Matrix.toLin' U (Matrix.toLin' V (Function.update (0 : Fin (m + 1) → ℤ) (Fin.last m) z))
        = Function.update (0 : Fin (m + 1) → ℤ) (Fin.last m) z := by
      simp only [Matrix.toLin'_apply, Matrix.mulVec_mulVec, hUV, Matrix.one_mulVec]
    rw [show φ (Matrix.toLin' V (Function.update (0 : Fin (m + 1) → ℤ) (Fin.last m) z))
          = q (Matrix.toLin' U (Matrix.toLin' V (Function.update (0 : Fin (m + 1) → ℤ) (Fin.last m) z)))
          from by simp only [hφ, LinearMap.comp_apply], hstep, hq, LinearMap.proj_apply]
    exact Function.update_self (Fin.last m) z (0 : Fin (m + 1) → ℤ)
  exact ⟨((Submodule.quotEquivOfEq _ _ hker.symm).trans (LinearMap.quotKerEquivRange φ)).trans
          ((LinearEquiv.ofEq _ _ htop).trans Submodule.topEquiv)⟩

end

end Work.HomologyMV
