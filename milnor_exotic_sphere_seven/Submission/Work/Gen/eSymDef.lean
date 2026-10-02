import Mathlib
import Submission.Work.LerayHirsch.LineSum
import Submission.Work.Whitney.chernClass_whitneySum_top
import Submission.Work.Cohomology.gradedComm
import Submission.Work.Thom.chernClass_comap

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

variable {B : Type} [TopologicalSpace B] {ι : Type} [Fintype ι]

/-- **The `k`-th elementary symmetric class of a family of line bundles**: for
`M : Fin n → (complex line bundles over B)`, `eSym n M k ∈ H^{2k}(B;ℤ)` is the `k`-th elementary
symmetric function of the first Chern classes `c₁(M i)`, computed with the graded cup product
`Work.Whitney.cupChern`.  Defined by the recursion
`eSym (n+1) M k = eSym n (M ∘ castSucc) k + c₁(M (last n)) ⌣ eSym n (M ∘ castSucc) (k-1)`. -/
noncomputable def eSym :
    (n : ℕ) → (Fin n → VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin 1)) ι) → (k : ℕ) →
      Coh ℤ (2 * k) B
  | 0, _, k =>
      if h : k = 0 then cohTransport (by omega : 0 = 2 * k)
        (Work.Cohomology.oneH ℤ (Work.Whitney.ssB B)) else 0
  | n + 1, M, k =>
      eSym n (fun i => M (Fin.castSucc i)) k +
        (if h : 1 ≤ k then
          cohTransport (by omega : 2 * (1 + (k - 1)) = 2 * k)
            (Work.Whitney.cupChern 1 (k - 1)
              (Work.Thom.chernClass 1 1 (M (Fin.last n)))
              (eSym n (fun i => M (Fin.castSucc i)) (k - 1)))
         else 0)

@[simp] theorem eSym_zero {M : Fin 0 → VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin 1)) ι} :
    eSym 0 M 0 = cohTransport (by omega : 0 = 2 * 0)
      (Work.Cohomology.oneH ℤ (Work.Whitney.ssB B)) := by
  rw [eSym]; simp

theorem eSym_zero_rank {M : Fin 0 → VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin 1)) ι} {k : ℕ}
    (hk : k ≠ 0) : eSym 0 M k = 0 := by
  rw [eSym]; simp [hk]

/-- The recursion of `eSym`, in the successor case. -/
theorem eSym_succ {n : ℕ} (M : Fin (n + 1) → VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin 1)) ι)
    (k : ℕ) :
    eSym (n + 1) M k = eSym n (fun i => M (Fin.castSucc i)) k +
      (if h : 1 ≤ k then
        cohTransport (by omega : 2 * (1 + (k - 1)) = 2 * k)
          (Work.Whitney.cupChern 1 (k - 1)
            (Work.Thom.chernClass 1 1 (M (Fin.last n)))
            (eSym n (fun i => M (Fin.castSucc i)) (k - 1)))
       else 0) := rfl

/-- `eSym` in degree `0` is the unit class. -/
theorem eSym_one_class {n : ℕ} (M : Fin n → VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin 1)) ι) :
    eSym n M 0 = cohTransport (by omega : 0 = 2 * 0)
      (Work.Cohomology.oneH ℤ (Work.Whitney.ssB B)) := by
  induction n with
  | zero => rw [eSym]; simp
  | succ n ih =>
    rw [eSym_succ, ih, dif_neg (by omega : ¬ (1 ≤ 0))]
    simp

end

end Work.Gen
