import Mathlib
import Submission.Work.Certificates.ChainCx
import Submission.Work.Certificates.SOp.eqb_sound
import Submission.Work.Certificates.SOp.toMatrix_mul

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# Soundness of the boundary check `bdCheck`

`bdCheck dim bd N` decides, sparsely, the chain condition `∂_{k+1} ∘ ∂_{k+2} = 0` in every
degree `k < N`.  This file turns a positive answer into the corresponding *matrix* identities.
The sparse `eqb` tests are compared via normal forms (`SOp.eqb_sound`), and the sparse
composition is translated into matrix multiplication (`SOp.toMatrix_mul`).

The hypothesis `hN : ∀ k, N ≤ k → dim k = 0` is what makes the statement true in degrees `≥ N`:
there the checker is silent, but both matrices are empty (`Matrix (Fin 0) (Fin 0) ℤ`), hence
equal to the zero matrix for trivial reasons.
-/

namespace Work.Certificates.FinChainCx

theorem bdCheck_sound {dim : ℕ → ℕ} {bd : ∀ k, SOp (dim k) (dim (k+1))} {N : ℕ}
    (hN : ∀ k, N ≤ k → dim k = 0) (h : bdCheck dim bd N = true) :
    ∀ k, (bd k).toMatrix * (bd (k+1)).toMatrix = 0 := by
  intro k
  by_cases hk : k < N
  · -- In degrees `< N` the check gives the sparse identity `∂_k ∂_{k+1} = 0`, which we read
    -- off as a matrix identity.
    have h1 : ((bd k).mul (bd (k+1))).eqb (SOp.zero (dim k) (dim (k+2))) = true :=
      (List.all_eq_true.mp h) k (List.mem_range.mpr hk)
    have h2 := SOp.eqb_sound h1
    simpa only [SOp.toMatrix_mul, SOp.toMatrix_zero] using h2
  · -- Beyond degree `N` the checker says nothing, but all matrix sizes are zero there.
    have hk' : N ≤ k := Nat.le_of_not_lt hk
    have hsub : Subsingleton (Matrix (Fin (dim k)) (Fin (dim (k+2))) ℤ) := by
      rw [hN k hk', hN (k+2) (by omega)]
      infer_instance
    exact hsub.elim _ _

end Work.Certificates.FinChainCx
