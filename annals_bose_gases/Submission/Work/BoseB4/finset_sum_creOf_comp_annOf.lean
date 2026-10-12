import Mathlib.Algebra.Algebra.Basic
import Mathlib.Algebra.Module.BigOperators
import Mathlib.Data.Finsupp.SMul
import Mathlib.Data.Real.Basic
import Submission.Work.BoseB4.AnnOf_creOf_ccr
import Submission.Work.BoseB4.DGamma
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseB4

/-- Bilinearity of composition of endomorphisms against finite linear combinations:
`(∑ i, a i • A i) ∘ (∑ j, b j • B j) = ∑ i, ∑ j, (a i * b j) • (A i ∘ B j)`. -/
lemma sum_smul_comp_sum_smul {M : Type*} [AddCommMonoid M] [Module ℝ M]
    {ι ι' : Type*} [Fintype ι] [Fintype ι']
    (a : ι → ℝ) (A : ι → Module.End ℝ M) (b : ι' → ℝ) (B : ι' → Module.End ℝ M) :
    (∑ i, a i • A i).comp (∑ j, b j • B j)
      = ∑ i, ∑ j, (a i * b j) • (A i).comp (B j) := by
  rw [← Module.End.mul_eq_comp (∑ i, a i • A i) (∑ j, b j • B j)]
  rw [Finset.sum_mul_sum]
  apply Finset.sum_congr rfl; intro i _
  apply Finset.sum_congr rfl; intro j _
  rw [smul_mul_smul, Module.End.mul_eq_comp]

theorem finset_sum_creOf_comp_annOf {ι : Type*} [DecidableEq ι] {m : ℕ}
    (W : ι → Fin m → ℝ) (S : Finset ι) :
    (∑ p ∈ S, (Work.BoseB4.creOf m (W p)).comp (Work.BoseB4.annOf m (W p)))
      = ∑ l : Fin m, ∑ l' : Fin m,
          (∑ p ∈ S, W p l * W p l') • ((Work.BoseB4.cre m l).comp (Work.BoseB4.ann m l')) := by
  have hterm : ∀ p, (creOf m (W p)).comp (annOf m (W p))
      = ∑ l : Fin m, ∑ l' : Fin m,
          (W p l * W p l') • ((cre m l).comp (ann m l')) := by
    intro p
    rw [creOf, annOf, sum_smul_comp_sum_smul]
  calc ∑ p ∈ S, (creOf m (W p)).comp (annOf m (W p))
      = ∑ p ∈ S, ∑ l : Fin m, ∑ l' : Fin m,
          (W p l * W p l') • ((cre m l).comp (ann m l')) :=
        Finset.sum_congr rfl fun p _ => hterm p
    _ = ∑ l : Fin m, ∑ l' : Fin m, ∑ p ∈ S,
          (W p l * W p l') • ((cre m l).comp (ann m l')) := by
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun l _ => Finset.sum_comm
    _ = ∑ l : Fin m, ∑ l' : Fin m,
          (∑ p ∈ S, W p l * W p l') • ((cre m l).comp (ann m l')) :=
        Finset.sum_congr rfl fun l _ =>
          Finset.sum_congr rfl fun l' _ => (Finset.sum_smul).symm

end Work.BoseB4
