import Mathlib
import Submission.Work.KT.FP.LindDefs
import Submission.Work.KT.Fund.Kappa

namespace Work.KT.FP

noncomputable section

/-!
# `Work.KT.FP.lind_laurentMap` — the image of `linSample X n P` under `laurentMap`

For any `P : Matrix (Fin n) (Fin n) C(X, ℂ)` the Laurent matrix
`linSample X n P = (1 - P) + P·T` (`Work.KT.FP.Linsample`) is mapped by the algebra map
`Work.KT.laurentMap X` (coefficients pulled back along the projection, `T ↦ z`) to the unit
`pullMat X (1 - P) + z • pullMat X P` of `Matrix (Fin n) (Fin n) C(X × S¹, ℂ)`, the unit that
appears in the normalisation clause of `Work.KT.FP.bott_index`.

The proof is entrywise: `laurentMap` is a ring homomorphism, `C a + C b·T` is sent to
`pullAlg a + pullAlg b · z`, and `pullMat` is entrywise `pullAlg` along the projection.
-/

/-- `Work.KT.Fund.pullMat` is entrywise `Work.KT.pullAlg` along the projection `X × S¹ → X`. -/
lemma lind_pullMat_eq_pullAlg (X : Type) [TopologicalSpace X] {n : ℕ}
    (M : Matrix (Fin n) (Fin n) C(X, ℂ)) (i j : Fin n) :
    Work.KT.Fund.pullMat X M i j
      = Work.KT.pullAlg (ContinuousMap.fst : C(X × Sph ℂ, X)) (M i j) := rfl

/-- The value of `Work.KT.laurentMap` on the degree-`≤ 1` Laurent polynomial `C a + C b·T`:

`laurentMap (C a + C b·T) = pullAlg a + pullAlg b · z`.

(The multiplication on `C(X × S¹, ℂ)` is commutative, and `T` is sent to the unit `z`.) -/
lemma lind_laurentMap_C_add_C_mul_T (X : Type) [TopologicalSpace X] (a b : C(X, ℂ)) :
    Work.KT.laurentMap X (LaurentPolynomial.C a + LaurentPolynomial.C b * LaurentPolynomial.T 1)
      = Work.KT.pullAlg (ContinuousMap.fst : C(X × Sph ℂ, X)) a
        + (Work.KT.zUnit X : C(X × Sph ℂ, ℂ))
          * Work.KT.pullAlg (ContinuousMap.fst : C(X × Sph ℂ, X)) b := by
  rw [map_add, map_mul, Work.KT.laurentMap_C, Work.KT.laurentMap_C, Work.KT.laurentMap_T]
  simp only [zpow_one]
  rw [mul_comm]

theorem lind_laurentMap (X : Type) [TopologicalSpace X] (n : ℕ)
    (P : Matrix (Fin n) (Fin n) C(X, ℂ)) :
    (Work.KT.FP.linSample X n P).map (Work.KT.laurentMap X)
      = Work.KT.Fund.pullMat X (1 - P)
        + (Work.KT.zUnit X : C(X × Work.KT.Sph ℂ, ℂ)) • Work.KT.Fund.pullMat X P := by
  ext i j
  simp only [Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply, linSample]
  rw [lind_pullMat_eq_pullAlg, lind_pullMat_eq_pullAlg, lind_laurentMap_C_add_C_mul_T]
  rfl

end

end Work.KT.FP
