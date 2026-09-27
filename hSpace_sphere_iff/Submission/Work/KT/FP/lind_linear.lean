import Mathlib
import Submission.Work.KT.FP.LindDefs
import Submission.Work.KT.FP.PencilDefs
import Submission.Work.KT.FP.Linsample
import Submission.Work.KT.Fund.Kappa
import Submission.Work.KT.FP.lind_glue
import Submission.Work.KT.FP.lind_block_alt
import Submission.Work.KT.FP.lind_cls_alt
import Submission.Work.KT.FP.lind_circ
import Submission.Work.KT.FP.lind_laurentMap

/-!
# `Work.KT.FP.lind_linear` — the linearisation of the Bott unit `(1 - P) + z·P`

For an idempotent `P` over `C(X, ℂ)` and the Laurent matrix `ℓ = (1 - P) + P·T` of
`Work.KT.FP.linSample`:

* (`laurentMap`) the image of `ℓ` under the Laurent evaluation `laurentMap` is the Bott unit
  `(1 - P) + z·P` over `X × S¹` (`Work.KT.FP.lind_laurentMap`);
* (`lindAt`) the index of the linearisation, computed with the pencil projection of the `d = 2`
  W linearisation of `(1 - P) + z·P`, is `cls ⟨n, P⟩`
  (`Work.KT.FP.lind_integrand` + `Work.KT.FP.lind_circ` + `Work.KT.FP.lind_cls_alt`).
-/

namespace Work.KT.FP

theorem lind_linear (X : Type) [TopologicalSpace X] [CompactSpace X] [T2Space X] (n : ℕ)
    (P : Matrix (Fin n) (Fin n) C(X, ℂ)) (hP : P * P = P) :
    ((linSample X n P).map (Work.KT.laurentMap X)
      = Work.KT.Fund.pullMat X (1 - P)
        + (Work.KT.zUnit X : C(X × Sph ℂ, ℂ)) • Work.KT.Fund.pullMat X P) ∧
    (∀ {ρ : ℝ}, 0 < ρ → ρ ≤ 1 →
      (∀ z : ℂ, ρ ≤ ‖z‖ → ‖z‖ ≤ 1 →
        IsUnit (z • linAf X n 1 + linBf X n 1 (linSample X n P))) →
      lindAt X n 1 (linSample X n P) ρ = cls (⟨n, P⟩ : Mat C(X, ℂ))) := by
  refine ⟨lind_laurentMap X n P, fun {ρ} hρ0 hρ1 hunit => ?_⟩
  have hblock : ∀ {z : ℂ}, z ≠ 0 →
      (z • blockMat X n (lindA X n) + blockMat X n (lindB X n P)) *
        (z⁻¹ • blockMat X n (lindC X n P) + (z⁻¹ * z⁻¹) • blockMat X n (lindD X n P)
          + blockMat X n (lindE X n P)) = blockMat X n (lindA X n) :=
    fun {z} hz => lind_block_identity_alt X n P hP hz
  have hint := lind_integrand X n P hP hblock hρ0 hρ1 hunit
  refine lindAt_eq_of_proj X n P hP ?_ (lind_cls_alt X n P hP)
  exact @lind_circ (Matrix (Fin ((2 * 1 + 1) * n)) (Fin ((2 * 1 + 1) * n)) C(X, ℂ))
    Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra
    (Matrix.instCompleteSpace (Fin ((2 * 1 + 1) * n)) (Fin ((2 * 1 + 1) * n)) C(X, ℂ))
    (linAf X n 1) (linBf X n 1 (linSample X n P))
    (Matrix.reindex finProdFinEquiv finProdFinEquiv (blockMat X n (lindC X n P)))
    (Matrix.reindex finProdFinEquiv finProdFinEquiv (blockMat X n (lindD X n P)))
    (Matrix.reindex finProdFinEquiv finProdFinEquiv (blockMat X n (lindE X n P)))
    ρ hρ0 hint

end Work.KT.FP
