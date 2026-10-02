import Mathlib
import Submission.Work.Gen.eSymDef
import Submission.Work.LerayHirsch.SplitsOverProj

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3200000

namespace Work.Gen

open Work.TangentClasses Work.Thom

noncomputable section

variable {B : Type} [TopologicalSpace B] {ι : Type} [Fintype ι]

/-- The degree bookkeeping of the `ψ`-existence equation. -/
theorem psiDataDegree (n : ℕ) (hn : 1 ≤ n) : 2 * (1 + (n - 1)) = 2 * n := by omega

/-- The top Leray–Hirsch index. -/
def topIdx (n : ℕ) : {i : Fin (n + 1) // (i : ℕ) ≤ n - 1} :=
  ⟨⟨n - 1, Nat.lt_succ_of_le (Nat.sub_le n 1)⟩, le_rfl⟩

/-- The degree bookkeeping at the top Leray–Hirsch index. -/
theorem topIdx_degree (n : ℕ) : 2 * (n - 1 - (topIdx n : ℕ)) = 2 * 0 := by
  have h : (topIdx n : ℕ) = n - 1 := rfl
  rw [h]
  omega

/-- **The data of the `ψ`-analysis at level `n`** (the family has `n + 1` line bundles, its sum has
rank `n + 1`): a complement `Q` of the tautological line in `π^*W`, the splitting isomorphism
`e : π^*W ≅ ℓ ⊕ Q`, a class `ψ` on `P(W)` with the ψ-existence equation `(A)`, and the Chern-root
relation `(CHERNR)` in Leray–Hirsch form (the hypothesis `hroot` of `cruxUpToConstant_of_root`). -/
structure PsiData (n : ℕ)
    (M : Fin (n + 1) → VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin 1)) ι) where
  /-- the level is positive -/
  hn : 1 ≤ n
  /-- the tautological quotient, i.e. a complement of the tautological line -/
  Q : VectorBundleCore ℂ (Work.LerayHirsch.ProjSpace (Work.LerayHirsch.lineSumCore (n + 1) M))
        (EuclideanSpace ℂ (Fin n))
        (Work.LerayHirsch.lineSumIndex (n + 1) ι × Fin (n + 1))
  /-- the splitting `π^*W ≅ ℓ ⊕ Q` -/
  e : BundleIso
        (bundleComap (Work.LerayHirsch.lineSumCore (n + 1) M)
          (Work.LerayHirsch.projMap (Work.LerayHirsch.lineSumCore (n + 1) M)))
        (Work.Whitney.whitneySum
          (Work.LerayHirsch.tautLine (Work.LerayHirsch.lineSumCore (n + 1) M)) Q)
  /-- the ψ-class -/
  ψ : Coh ℤ (2 * (n - 1))
        (Work.LerayHirsch.ProjSpace (Work.LerayHirsch.lineSumCore (n + 1) M))
  /-- the ψ-existence equation -/
  hψ : chernClass n n Q
      = (CohMap (Work.LerayHirsch.projMap (Work.LerayHirsch.lineSumCore (n + 1) M))
            ℤ (2 * n)).hom
          (chernClass (n + 1) n (Work.LerayHirsch.lineSumCore (n + 1) M))
        + cohTransport (psiDataDegree n hn)
            (Work.Whitney.cupChern 1 (n - 1)
              (Work.LerayHirsch.zeta (Work.LerayHirsch.lineSumCore (n + 1) M)) ψ)
  /-- the Chern-root relation -/
  hrootSpec : Work.LerayHirsch.lhMap (Work.LerayHirsch.lineSumCore (n + 1) M) (n + 1)
      (fun i => ((-1 : ℤ) ^ (n + 1 + (i : ℕ))) • eSym (n + 1) M (n + 1 - (i : ℕ)))
    = Work.LerayHirsch.zetaPow (Work.LerayHirsch.lineSumCore (n + 1) M) (n + 1)

end

end Work.Gen
