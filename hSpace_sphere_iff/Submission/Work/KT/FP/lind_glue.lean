import Mathlib
import Submission.Work.KT.FP.LindDefs

/-!
# `Work.KT.FP.lind_glue` — from the block identity to the index of the linearisation

The two glue steps of `Work.KT.FP.lind_linear`:

* `lind_integrand` — the block identity `(zA + B)·(z⁻¹C + z⁻²D + E) = A` of
  `Work.KT.FP.lind_block_identity`, transported along the reindexing
  `Fin 3 × Fin n ≃ Fin (3n)`, gives the *integrand* of the pencil projection of the linearisation:
  `(z·linAf + linBf)⁻¹·linAf = z⁻¹·C' + z⁻²·D' + E'` on the circle, where `C'`, `D'`, `E'` are the
  reindexed blocks;
* `lindAt_eq_of_proj` — the `K₀` bookkeeping: if the projection is the reindexed `lindC` and the
  class of the latter is `[1_n ⊕ P]`, then `lindAt ρ = cls ⟨n, P⟩`.
-/

namespace Work.KT.FP

open Matrix

noncomputable section

variable (X : Type) [TopologicalSpace X]

/-- **The integrand of the pencil projection of the linearisation.**  On the circle `‖z‖ = ρ`,
`(z·linAf + linBf)⁻¹·linAf` is the `z`-Laurent combination `z⁻¹·C' + z⁻²·D' + E'` of the reindexed
blocks `lindC`, `lindD`, `lindE`. -/
theorem lind_integrand (n : ℕ) (P : Matrix (Fin n) (Fin n) C(X, ℂ)) (hP : P * P = P)
    (hblock : ∀ {z : ℂ}, z ≠ 0 →
      (z • blockMat X n (lindA X n) + blockMat X n (lindB X n P)) *
        (z⁻¹ • blockMat X n (lindC X n P) + (z⁻¹ * z⁻¹) • blockMat X n (lindD X n P)
          + blockMat X n (lindE X n P)) = blockMat X n (lindA X n))
    {ρ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ ≤ 1)
    (hunit : ∀ z : ℂ, ρ ≤ ‖z‖ → ‖z‖ ≤ 1 →
      IsUnit (z • linAf X n 1 + linBf X n 1 (linSample X n P))) :
    ∀ z : ℂ, ‖z‖ = ρ →
      Ring.inverse (z • linAf X n 1 + linBf X n 1 (linSample X n P)) * linAf X n 1
        = z⁻¹ • Matrix.reindex finProdFinEquiv finProdFinEquiv (blockMat X n (lindC X n P))
          + (z⁻¹ * z⁻¹) •
              Matrix.reindex finProdFinEquiv finProdFinEquiv (blockMat X n (lindD X n P))
          + Matrix.reindex finProdFinEquiv finProdFinEquiv (blockMat X n (lindE X n P)) := by
  intro z hz
  have hz0 : z ≠ 0 := by
    intro h
    rw [h, norm_zero] at hz
    linarith
  set Mz : Matrix (Fin ((2 * 1 + 1) * n)) (Fin ((2 * 1 + 1) * n)) C(X, ℂ) :=
    z • linAf X n 1 + linBf X n 1 (linSample X n P) with hMz
  set W : Matrix (Fin ((2 * 1 + 1) * n)) (Fin ((2 * 1 + 1) * n)) C(X, ℂ) :=
    z⁻¹ • Matrix.reindex finProdFinEquiv finProdFinEquiv (blockMat X n (lindC X n P))
      + (z⁻¹ * z⁻¹) • Matrix.reindex finProdFinEquiv finProdFinEquiv (blockMat X n (lindD X n P))
      + Matrix.reindex finProdFinEquiv finProdFinEquiv (blockMat X n (lindE X n P)) with hW
  have hMunit : IsUnit Mz := by
    rw [hMz]
    exact hunit z (le_of_eq hz.symm) (by rw [hz]; exact hρ1)
  have hMW : Mz * W = linAf X n 1 := by
    rw [hMz, hW]
    have h := congrArg (Matrix.reindex finProdFinEquiv finProdFinEquiv) (hblock hz0)
    rw [← reindexMat_mul, reindexMat_add, reindexMat_smul, reindexMat_add, reindexMat_add,
      reindexMat_smul, reindexMat_smul] at h
    simp only [← linAf_eq X n, ← linBf_eq X n P] at h
    exact h
  rw [← hMW, ← Matrix.mul_assoc, Ring.inverse_mul_cancel Mz hMunit, Matrix.one_mul]

/-- **The index of the linearisation.**  If the pencil projection of the linearisation is the
reindexed `lindC` and the class of the latter is `[1_n] + [P]`, then the index
`lindAt X n 1 (linSample X n P) ρ` is `cls ⟨n, P⟩`. -/
theorem lindAt_eq_of_proj [CompactSpace X] [T2Space X] (n : ℕ)
    (P : Matrix (Fin n) (Fin n) C(X, ℂ)) (hP : P * P = P) {ρ : ℝ}
    (hmat : matPProj X ((2 * 1 + 1) * n) (linAf X n 1) (linBf X n 1 (linSample X n P)) ρ
      = Matrix.reindex finProdFinEquiv finProdFinEquiv (blockMat X n (lindC X n P)))
    (hcls : cls (⟨3 * n, Matrix.reindex finProdFinEquiv finProdFinEquiv
        (blockMat X n (lindC X n P))⟩ : Mat C(X, ℂ))
      = cls (Mat.sum (Mat.one C(X, ℂ) n) (⟨n, P⟩ : Mat C(X, ℂ)))) :
    lindAt X n 1 (linSample X n P) ρ = cls (⟨n, P⟩ : Mat C(X, ℂ)) := by
  have hone : (Mat.one C(X, ℂ) n).IsIdem := by
    unfold Mat.IsIdem Mat.one
    exact Matrix.mul_one 1
  have hcls' : cls (⟨(2 * 1 + 1) * n, Matrix.reindex finProdFinEquiv finProdFinEquiv
        (blockMat X n (lindC X n P))⟩ : Mat C(X, ℂ))
      = cls (Mat.sum (Mat.one C(X, ℂ) n) (⟨n, P⟩ : Mat C(X, ℂ))) := hcls
  have hP' : Mat.IsIdem (⟨n, P⟩ : Mat C(X, ℂ)) := hP
  unfold lindAt
  rw [hmat, hcls',
    cls_sum (p := Mat.one C(X, ℂ) n) (q := (⟨n, P⟩ : Mat C(X, ℂ))) hone hP', one_smul]
  abel

end

end Work.KT.FP
