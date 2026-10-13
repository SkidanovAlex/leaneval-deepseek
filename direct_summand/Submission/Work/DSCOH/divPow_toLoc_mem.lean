import Mathlib
import Submission.Work.DSCOH.Basic

namespace Work.DSCOH

theorem divPow_toLoc_mem {A : Type*} [CommRing A] {n : ℕ}
    {M : Type*} [AddCommGroup M] [Module A M] [Module (Poly A n) M] [IsScalarTower A (Poly A n) M]
    (ℳ : ℕ → Submodule A M) (S : Finset (Fin n)) (k : ℕ) {m : M}
    (hm : m ∈ ℳ (k * S.card)) :
    divPow (M := M) S k (toLoc (M := M) S m) ∈ degZero ℳ S := by
  rw [degZero]
  exact Submodule.mem_iSup_of_mem k (Submodule.mem_map_of_mem hm)

end Work.DSCOH
