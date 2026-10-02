import Mathlib
import Submission.Work.Kunneth.Assembly.Defs
import Submission.Work.Kunneth.Assembly.bridge

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3200000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

/-!
# The bridge, summed over the family

`Work.Kunneth.Asm.pullIso_crossH` identifies the pullback along the monoidal comparison of the
simplicial cross product with the space-level cup product.  Summing it over the Leray–Hirsch family
(and matching the degree transports) gives

`pullIso (sqFam xf) = crFam xf`  and  `pullIso (sqFamOdd xf) = crFamOdd xf`.
-/

namespace Work.Kunneth.Asm

open CategoryTheory CategoryTheory.Limits Work.TangentClasses Work.Thom

open scoped LinearAlgebra.Projectivization MonoidalCategory TensorProduct

noncomputable section

/-- `eqToHom` of a degree identity of a cochain complex, applied to an element, is the `Eq.rec`
cast. -/
theorem eqToHom_homology_eq_rec (X : SSet) {n n' : ℕ} (h : n = n')
    (x : ↥((Work.Cohomology.cochainC ℤ X).homology n)) :
    (CategoryTheory.eqToHom (congrArg (fun k => (Work.Cohomology.cochainC ℤ X).homology k) h)) x
      = (h ▸ x) := by
  cases h
  rfl

/-- The pullback along the monoidal comparison commutes with the degree transport. -/
theorem pullIso_eqRec (m : ℕ) (B : Type) [TopologicalSpace B] {p q : ℕ} (h : p = q)
    (x : ↥((Work.Cohomology.cochainC ℤ
      (Work.Kunneth.sProd (ssB B) (ssB (Qb m)))).homology p)) :
    pullIso m B q (h ▸ x) = h ▸ (pullIso m B p x) := by
  cases h
  rfl

theorem pullIso_sqTerm (m : ℕ) (B : Type) [TopologicalSpace B] (k : ℕ)
    (i : {i : Fin m // (i : ℕ) ≤ k}) (x : Coh ℤ (2 * (k - (i : ℕ))) B) :
    pullIso m B (2 * k) (sqTerm m B k i x) = crTerm m B k i x := by
  rw [sqTerm, pullIso_eqRec, pullIso_crossH, crTerm, Work.Whitney.cupChern_def,
    Work.LerayHirsch.eqRec_eq_cohTransport (B := B × Qb m)]
  rw [← Work.Whitney.cohTransport_trans (by omega : 2 * (k - (i : ℕ)) + 2 * (i : ℕ)
    = 2 * ((k - (i : ℕ)) + (i : ℕ))) (by omega : 2 * ((k - (i : ℕ)) + (i : ℕ)) = 2 * k)]

theorem pullIso_sqFam (m : ℕ) (B : Type) [TopologicalSpace B] (k : ℕ)
    (xf : (i : {i : Fin m // (i : ℕ) ≤ k}) → Coh ℤ (2 * (k - (i : ℕ))) B) :
    pullIso m B (2 * k) (sqFam m B k xf) = crFam m B k xf := by
  rw [sqFam, crFam, map_sum]
  exact Finset.sum_congr rfl (fun i _ => pullIso_sqTerm m B k i (xf i))

theorem pullIso_sqTermOdd (m : ℕ) (B : Type) [TopologicalSpace B] (k : ℕ)
    (i : {i : Fin m // (i : ℕ) ≤ k}) (x : Coh ℤ (2 * k + 1 - 2 * (i : ℕ)) B) :
    pullIso m B (2 * k + 1) (sqTermOdd m B k i x) = crTermOdd m B k i x := by
  rw [sqTermOdd, pullIso_eqRec, pullIso_crossH, crTermOdd,
    Work.LerayHirsch.eqRec_eq_cohTransport (B := B × Qb m)]

theorem pullIso_sqFamOdd (m : ℕ) (B : Type) [TopologicalSpace B] (k : ℕ)
    (xf : (i : {i : Fin m // (i : ℕ) ≤ k}) → Coh ℤ (2 * k + 1 - 2 * (i : ℕ)) B) :
    pullIso m B (2 * k + 1) (sqFamOdd m B k xf) = crFamOdd m B k xf := by
  rw [sqFamOdd, crFamOdd, map_sum]
  exact Finset.sum_congr rfl (fun i _ => pullIso_sqTermOdd m B k i (xf i))

end

end Work.Kunneth.Asm
