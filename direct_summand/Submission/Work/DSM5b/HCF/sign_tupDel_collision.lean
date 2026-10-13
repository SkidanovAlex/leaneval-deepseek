import Mathlib
import Submission.Work.DSM5b.PerfComplexDefs
import Submission.Work.DSM5b.HCF.CycPermDefs
import Submission.Work.DSM5b.HCF.tupDel_cycPerm

/-!
# The sign relation between the two deleted tuples of a collision

Let `v : Fin (n+2) → Fin (n+1)` and let `i₁ < i₂` be two indices with `v i₁ = v i₂`.  Write
`u₁`, `u₂` for the tuples `v` with the `i₁`-th resp. `i₂`-th entry deleted (`Work.DSM5b.tupDel`),
viewed as permutations of `Fin (n+1)` as soon as they are bijective (which is the only case in
which this statement has content, since the hypotheses `hu₁`, `hu₂` say that `u₁` resp. `u₂` *is*
the corresponding deleted tuple).

The two deleted tuples enumerate the same list of values, and differ by the cyclic shift
`av ↦ bv-1 ↦ bv-2 ↦ ⋯ ↦ av+1 ↦ av` (`av = i₁`, `bv = i₂`) of the source indices — the
permutation `Work.DSM5b.HCF.cycPerm`:

  `tupDel i₂ v = tupDel i₁ v ∘ cycPerm i₁ i₂ hlt`   (`Work.DSM5b.HCF.tupDel_cycPerm`).

Since `cycPerm i₁ i₂ hlt` is a cycle on `(bv - av)` indices, its sign is `(-1)^(bv - av - 1)`
(`Work.DSM5b.HCF.sign_cycPerm`), which is exactly the classical simplicial sign relation
`(-1)^(i₂ - i₁ - 1)` between the two face maps.
-/

namespace Work.DSM5b.HCF

open scoped Classical

theorem sign_tupDel_collision {n : ℕ} {v : Fin (n + 2) → Fin (n + 1)}
    {i₁ i₂ : Fin (n + 2)} (hlt : i₁ < i₂) (heq : v i₁ = v i₂)
    (u₁ u₂ : Equiv.Perm (Fin (n + 1)))
    (hu₁ : ∀ k : Fin (n + 1), u₁ k = Work.DSM5b.tupDel i₁ v k)
    (hu₂ : ∀ k : Fin (n + 1), u₂ k = Work.DSM5b.tupDel i₂ v k) :
    Equiv.Perm.sign u₂ = Equiv.Perm.sign u₁ * (-1 : ℤˣ) ^ ((i₂ : ℕ) - (i₁ : ℕ) - 1) := by
  -- `u₂` is the composite of `u₁` with the cyclic shift of the deleted interval
  have hcomp : u₂ = u₁ * cycPerm i₁ i₂ hlt := by
    apply Equiv.ext
    intro k
    show u₂ k = (u₁ * cycPerm i₁ i₂ hlt) k
    rw [Equiv.Perm.mul_apply, hu₁ (cycPerm i₁ i₂ hlt k), hu₂ k]
    exact tupDel_cycPerm hlt heq k
  rw [hcomp, Equiv.Perm.sign_mul, sign_cycPerm]

end Work.DSM5b.HCF
