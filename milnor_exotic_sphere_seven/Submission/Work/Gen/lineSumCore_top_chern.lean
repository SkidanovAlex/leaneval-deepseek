import Mathlib
import Submission.Work.Gen.eSymClass
import Submission.Work.Gen.eSymDef
import Submission.Work.Whitney.chernClass_whitneySum_top
import Submission.Work.LerayHirsch.LineSum
import Submission.Work.Thom.chernClass_zero_eq_oneH

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

/-!
# The top Chern class of a direct sum of line bundles

`Work.Gen.lineSumCore_top_chern`: the top Chern class `c_n` of the `n`-fold direct sum
`Work.LerayHirsch.lineSumCore n A` of complex *line* bundles is the `n`-th elementary symmetric
class `Work.Gen.eSym n A n` of their first Chern classes — which, since there are exactly `n` of
them, is simply the product `c₁(A 0) ⌣ … ⌣ c₁(A (n-1))`.

The proof is the induction on `n` using the multiplicativity of the top Chern class
(`Work.Whitney.chernClass_whitneySum_top`, i.e. `c_{m₁+m₂}(Z₁ ⊕ Z₂) = c_{m₁}(Z₁) ⌣ c_{m₂}(Z₂)`)
together with the recursion of `eSym`: in degree `n+1` in `n+1` variables the *first* term
`eSym n (A ∘ castSucc) (n+1)` vanishes (`Work.Gen.eSymC_above`, transported along
`Work.Gen.eSym_eq_eSymC`), and the second term is the product of the two inductive classes, matched
by the even-degree commutativity `Work.Whitney.ChernRel.cupChern_comm` (the sign `(-1)^{4n}` is
`1`) and the proof-irrelevance of the degree cast.
-/

namespace Work.Gen

open Work.TangentClasses Work.Thom

noncomputable section

/-- The recursion of `eSym`, with the `dif` resolved (for `k ≥ 1`). -/
private theorem eSym_succ_apply_aux {B : Type} [TopologicalSpace B] {ι : Type} [Fintype ι] {n : ℕ}
    (A : Fin (n + 1) → VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin 1)) ι) {k : ℕ} (hk : 1 ≤ k) :
    eSym (n + 1) A k = eSym n (A ∘ Fin.castSucc) k +
      cohTransport (by omega : 2 * (1 + (k - 1)) = 2 * k)
        (Work.Whitney.cupChern 1 (k - 1) (Work.Thom.chernClass 1 1 (A (Fin.last n)))
          (eSym n (A ∘ Fin.castSucc) (k - 1))) := by
  rw [eSym_succ, dif_pos hk]
  rfl

/-- `eSym` vanishes in degrees above the number of variables. -/
private theorem eSym_above_aux {B : Type} [TopologicalSpace B] {ι : Type} [Fintype ι] {n : ℕ}
    (A : Fin n → VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin 1)) ι) {k : ℕ} (hk : n < k) :
    eSym n A k = 0 := by
  rw [eSym_eq_eSymC]
  exact eSymC_above _ hk

theorem lineSumCore_top_chern {P : Type} [TopologicalSpace P] {ι : Type} [Fintype ι] (n : ℕ)
    (A : Fin n → VectorBundleCore ℂ P (EuclideanSpace ℂ (Fin 1)) ι) :
    Work.Thom.chernClass n n (Work.LerayHirsch.lineSumCore n A) = eSym n A n := by
  induction n with
  | zero =>
    rw [Work.LerayHirsch.lineSumCore_zero, eSym_zero]
    rw [Work.Thom.chernClass_zero_eq_oneH]
    congr 1
  | succ n ih =>
    rw [Work.LerayHirsch.lineSumCore_succ, Work.Whitney.chernClass_whitneySum_top]
    rw [ih (A ∘ Fin.castSucc)]
    rw [eSym_succ_apply_aux A (by omega : 1 ≤ n + 1)]
    rw [eSym_above_aux (A ∘ Fin.castSucc) (Nat.lt_succ_self n), zero_add]
    rw [Work.Whitney.ChernRel.cupChern_comm n 1]
    exact Work.LerayHirsch.cohTransport_congr_proof _ _

end

end Work.Gen
