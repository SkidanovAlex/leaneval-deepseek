import Mathlib
import Submission.Work.Gen.eSymDef
import Submission.Work.Gen.lineSumCore_top_chern
import Submission.Work.Gen.chernProductSum_line
import Submission.Work.LerayHirsch.LineSum
import Submission.Work.Whitney.chernClass_whitneySum_top

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

namespace Work.Gen

open Work.TangentClasses Work.Thom

noncomputable section

/-- **The split diagonal of the Whitney formula, over a common cover.**  For a complex line bundle
`L` and a `k`-fold direct sum `lineSumCore k M` of complex line bundles over a *common* cover `ι`
of a paracompact Hausdorff base, with `k ≥ 1`:

`c_k((M 0 ⊕ … ⊕ M (k-1)) ⊕ L) = chernProductSum L (lineSumCore k M) k`.

Derivation from `hcrux` (all ingredients are on disk):
* let `N : Fin (k+1) → line` be `Fin.snoc M L` over the cover `ι`; then
  `lineSumCore (k+1) N = whitneySum (lineSumCore k M) L` by `lineSumCore_succ` together with
  `Fin.snoc_comp_castSucc`, `Fin.snoc_last` (and `(k+1)-1 = k`, `Nat.succ_sub_one`);
* `hcrux (k+1) N` reads
  `chernClass (k+1) ((k+1)-1) (whitneySum (lineSumCore k M) L) = eSym (k+1) N ((k+1)-1)`;
* `eSym_succ` (with `dif_pos hk`) expands `eSym (k+1) N k` as
  `eSym k M k + cohTransport _ (cupChern 1 (k-1) (chernClass 1 1 L) (eSym k M (k-1)))`;
* `eSym k M k = chernClass k k (lineSumCore k M)` (`lineSumCore_top_chern`, reversed) and
  `eSym k M (k-1) = chernClass k (k-1) (lineSumCore k M)` (`hcrux k M`);
* `chernProductSum_line` (with `W := lineSumCore k M`, `m := k`, and the same `hk`) identifies
  `chernProductSum L (lineSumCore k M) k` with
  `chernClass k k (lineSumCore k M) + cohTransport _ (cupChern 1 (k-1) (chernClass 1 1 L)
  (chernClass k (k-1) (lineSumCore k M)))`.
All the degree casts are the same `by omega` proofs, so `cohTransport_trans` /
`cohTransport_congr_proof` close the bookkeeping. -/
theorem splitCommonCoverStep
    (hcrux : ∀ (n : ℕ) {B : Type} [TopologicalSpace B] [ParacompactSpace B] [T2Space B]
      {ι : Type} [Fintype ι] (M : Fin n → VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin 1)) ι),
      Work.Thom.chernClass n (n - 1) (Work.LerayHirsch.lineSumCore n M)
        = Work.Gen.eSym n M (n - 1))
    (k : ℕ) (hk : 1 ≤ k)
    {B : Type} [TopologicalSpace B] [ParacompactSpace B] [T2Space B]
    {ι : Type} [Fintype ι]
    (L : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin 1)) ι)
    (M : Fin k → VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin 1)) ι) :
    Work.Thom.chernClass (k + 1) k
        (Work.Whitney.whitneySum (Work.LerayHirsch.lineSumCore k M) L)
      = Work.Whitney.chernProductSum L (Work.LerayHirsch.lineSumCore k M) k := by
  -- the family `M` extended by the line bundle `L`
  let N : Fin (k + 1) → VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin 1)) ι :=
    Fin.snoc (α := fun _ : Fin (k + 1) =>
      VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin 1)) ι) M L
  have hcast : (fun i : Fin k => N (Fin.castSucc i)) = M :=
    funext fun i => Fin.snoc_castSucc (α := fun _ : Fin (k + 1) =>
      VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin 1)) ι) L M i
  have hcast' : (N ∘ Fin.castSucc) = M := hcast
  have hlast : N (Fin.last k) = L :=
    Fin.snoc_last (α := fun _ : Fin (k + 1) =>
      VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin 1)) ι) L M
  -- `hcrux` at `k + 1` and at the family `N`
  have hcore : Work.Thom.chernClass (k + 1) k
        (Work.Whitney.whitneySum (Work.LerayHirsch.lineSumCore k M) L)
      = Work.Gen.eSym (k + 1) N k := by
    have h := hcrux (k + 1) N
    rw [Work.LerayHirsch.lineSumCore_succ] at h
    rw [hcast', hlast] at h
    exact h
  rw [hcore]
  -- expand `eSym (k+1) N k`
  rw [Work.Gen.eSym_succ, hcast, hlast, dif_pos hk]
  -- replace the two `eSym k M`'s by the corresponding Chern classes
  rw [← Work.Gen.lineSumCore_top_chern k M, ← hcrux k M]
  -- collapse the right-hand side
  rw [Work.Gen.chernProductSum_line L (Work.LerayHirsch.lineSumCore k M) k, dif_pos hk]

end

end Work.Gen
