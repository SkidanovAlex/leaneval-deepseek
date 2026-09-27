import Mathlib
import Submission.Work.KT.Defs
import Submission.Work.KT.Basic
import Submission.Work.KT.Rank.mvN_one_rank_v2
import Submission.Work.KT.Rank.rank_eq_of_mvN
import Submission.Work.KT.Rank.rank_sum

namespace Work.KT.D2

open Matrix

/-!
# The rank homomorphism `K₀(ℂ) →ₗ ℤ`

`K₀(ℂ)` is presented as the free abelian group on the square complex matrices modulo
`Work.KT.K0Rel` (block sums, Murray–von Neumann equivalence, and non-idempotents set to zero).
The rank of an idempotent matrix is unchanged by all three relations, hence descends to a
homomorphism `K₀(ℂ) →+ ℤ`.  Since `Matrix.rank 1 = n`, this shows that `K₀(ℂ)` is free on the
class of the identity.

The two facts used about `Matrix.rank` are exactly the two independent consequences of the
relations, proved in the sibling files:

* `Work.KT.Rank.rank_sum` — `rank (p ⊕ q) = rank p + rank q`;
* `Work.KT.Rank.rank_eq_of_mvN` — MvN equivalent idempotents have equal rank.
-/

open Classical in
/-- The rank of an idempotent square complex matrix, and `0` on non-idempotents: the value of the
rank homomorphism on a generator of the free abelian group on matrices. -/
private noncomputable def rankFn (p : Work.KT.Mat ℂ) : ℤ :=
  if p.IsIdem then (p.2.rank : ℤ) else 0

private lemma rankFn_of_idem {p : Work.KT.Mat ℂ} (hp : p.IsIdem) : rankFn p = (p.2.rank : ℤ) := by
  simp [rankFn, hp]

private lemma rankFn_of_not_idem {p : Work.KT.Mat ℂ} (hp : ¬ p.IsIdem) : rankFn p = 0 := by
  simp [rankFn, hp]

/-- The identity matrix is idempotent. -/
private lemma one_isIdem_local (k : ℕ) : (Work.KT.Mat.one ℂ k).IsIdem := by
  unfold Work.KT.Mat.IsIdem Work.KT.Mat.one
  rw [Matrix.one_mul]

/-- The identity matrix of size `k` has rank `k`. -/
private lemma rank_one_local (k : ℕ) : ((Work.KT.Mat.one ℂ k).2).rank = k := by
  unfold Work.KT.Mat.one
  rw [Matrix.rank_one, Fintype.card_fin]

/-- The rank homomorphism on `K₀(ℂ)`: the class of an idempotent complex matrix is sent to its
`Matrix.rank`, so that `K₀(ℂ)` is free on the class of the identity matrix. -/
theorem rankK0 :
    ∃ r : Work.KT.K0 ℂ →+ ℤ,
      (∀ (n : ℕ) (M : Matrix (Fin n) (Fin n) ℂ), M * M = M →
        r (Work.KT.cls (⟨n, M⟩ : Work.KT.Mat ℂ)) = M.rank) ∧
      (∀ (k : ℕ), r (Work.KT.cls (Work.KT.Mat.one ℂ k)) = k) := by
  classical
  -- The rank function respects the three defining relations of `K₀`.
  have hker : Work.KT.K0Rel ℂ ≤ (FreeAbelianGroup.lift rankFn).ker := by
    rw [Work.KT.K0Rel, AddSubgroup.closure_le]
    rintro x ((⟨p, q, hp, hq, rfl⟩ | ⟨p, q, hp, hq, hmv, rfl⟩) | ⟨p, hp, rfl⟩)
    · -- block sums: `rank (p ⊕ q) = rank p + rank q`
      obtain ⟨n, P⟩ := p
      obtain ⟨m, Q⟩ := q
      simp only [SetLike.mem_coe, AddMonoidHom.mem_ker, map_sub, FreeAbelianGroup.lift_apply_of]
      rw [rankFn_of_idem (Mat.sum_idem hp hq), rankFn_of_idem hp, rankFn_of_idem hq,
        Rank.rank_sum n m P Q]
      push_cast
      ring
    · -- Murray–von Neumann equivalence: isomorphic ranges have the same dimension
      obtain ⟨n, P⟩ := p
      obtain ⟨m, Q⟩ := q
      simp only [SetLike.mem_coe, AddMonoidHom.mem_ker, map_sub, FreeAbelianGroup.lift_apply_of]
      rw [rankFn_of_idem hp, rankFn_of_idem hq, Rank.rank_eq_of_mvN P Q hp hq hmv]
      ring
    · -- non-idempotents are sent to `0` by definition
      simp only [SetLike.mem_coe, AddMonoidHom.mem_ker, FreeAbelianGroup.lift_apply_of]
      exact rankFn_of_not_idem hp
  refine ⟨QuotientAddGroup.lift (Work.KT.K0Rel ℂ) (FreeAbelianGroup.lift rankFn) hker, ?_, ?_⟩
  · intro n M hM
    show QuotientAddGroup.lift (Work.KT.K0Rel ℂ) (FreeAbelianGroup.lift rankFn) hker
        (Work.KT.cls (⟨n, M⟩ : Work.KT.Mat ℂ)) = (M.rank : ℤ)
    rw [Work.KT.cls, QuotientAddGroup.lift_mk, FreeAbelianGroup.lift_apply_of,
      rankFn_of_idem (p := (⟨n, M⟩ : Work.KT.Mat ℂ)) hM]
  · intro k
    show QuotientAddGroup.lift (Work.KT.K0Rel ℂ) (FreeAbelianGroup.lift rankFn) hker
        (Work.KT.cls (Work.KT.Mat.one ℂ k)) = (k : ℤ)
    rw [Work.KT.cls, QuotientAddGroup.lift_mk, FreeAbelianGroup.lift_apply_of,
      rankFn_of_idem (one_isIdem_local k), rank_one_local k]

end Work.KT.D2
