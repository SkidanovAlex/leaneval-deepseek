import Mathlib
import Submission.Commons.Algebra.FreeAlgebra.golod_shafarevich_relator_right_mul_finrank_le

namespace Commons.Algebra.FreeAlgebra

open _root_.FreeAlgebra

theorem golod_shafarevich_relator_right_mul_finrank_sum_le
    {K ι σ : Type*} [Field K] [Fintype ι] [DecidableEq ι] [Fintype σ]
    (degRel : σ → ℕ) (rel : σ → FreeAlgebra K ι)
    (hdeg : ∀ r, 2 ≤ degRel r)
    (hhom : ∀ r, rel r ∈ golodShafarevich_gradedPart K ι (degRel r))
    (n : ℕ) (hn : 0 < n) :
    let V := golodShafarevich_gradedPart K ι
    let I := golodShafarevich_twoSidedIdeal K ι σ rel
    let T := Submodule.span K {x | ∃ a ∈ I ⊓ V (n - 1), ∃ i : ι,
      x = a * FreeAlgebra.basisFreeMonoid K ι (FreeMonoid.of i)}
    let S := fun r : σ => Submodule.span K {x | ∃ a ∈ V (n - degRel r), x = a * rel r}
    (∑ r : σ, if degRel r ≤ n then Module.finrank K (Submodule.map T.mkQ (S r)) else 0) ≤
      (∑ r : σ, if degRel r ≤ n then Module.finrank K (Submodule.map I.mkQ (V (n - degRel r))) else 0) := by
  dsimp only
  let V := golodShafarevich_gradedPart K ι
  let I := golodShafarevich_twoSidedIdeal K ι σ rel
  let T := Submodule.span K {x | ∃ a ∈ I ⊓ V (n - 1), ∃ i : ι,
      x = a * FreeAlgebra.basisFreeMonoid K ι (FreeMonoid.of i)}
  let S := fun r : σ => Submodule.span K {x | ∃ a ∈ V (n - degRel r), x = a * rel r}
  classical
  refine Finset.sum_le_sum ?_
  intro r _
  by_cases hrn : degRel r ≤ n
  · simp [hrn]
    exact golod_shafarevich_relator_right_mul_finrank_le (K := K) (ι := ι) (σ := σ)
      degRel rel hdeg hhom n hn r hrn
  · simp [hrn]

end Commons.Algebra.FreeAlgebra
