import Mathlib
import Submission.Work.BMF.recursion.MomVec

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BMF.recursion

/-- The set `Tset p y s Q` of `s`-tuples all of whose entries are `≡ y (mod p)` is the
Cartesian product of the set `{b ∈ [1,Q] : b ≡ y (mod p)}` with itself `s` times, so the
sum of `∏ r, g (t r)` over it factors as the `s`-th power of `∑_{b ≡ y (mod p)} g b`. -/
theorem Tset_prod_sum {Q s : ℕ} (p y : ℕ) (g : Finset.Icc 1 Q → ℂ) :
    ∑ t ∈ Tset p y s Q, ∏ r : Fin s, g (t r)
      = (∑ b ∈ (Finset.univ : Finset (Finset.Icc 1 Q)).filter (fun b => b.1 % p = y % p), g b) ^ s := by
  classical
  have hTset : Tset p y s Q
      = Fintype.piFinset (fun _ : Fin s =>
          (Finset.univ : Finset (Finset.Icc 1 Q)).filter (fun b => b.1 % p = y % p)) := by
    ext t
    simp [Tset, Tails, Fintype.mem_piFinset]
  rw [hTset, Finset.sum_pow']

end Work.BMF.recursion
