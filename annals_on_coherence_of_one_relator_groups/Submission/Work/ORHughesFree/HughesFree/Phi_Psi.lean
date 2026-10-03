import Mathlib
import Submission.Work.ORHughesFree.HughesFree.skewLaurentDecompAux

namespace Work.ORHughesFree.HughesFree

theorem Phi_Psi {K : Type} [Field K] {G : Type} [Group G] {H : Subgroup G} {N : Subgroup H}
    {t : H} (htN : ∀ (k : ℤ) (n : N), t ^ k * (n : H) * t ^ (-k) ∈ N)
    [MulSemiringAction (Multiplicative ℤ) (MonoidAlgebra K N)]
    [SMulCommClass (Multiplicative ℤ) K (MonoidAlgebra K N)]
    (hact : ∀ (k : ℤ) (n : N), (Multiplicative.ofAdd k) • (MonoidAlgebra.single n (1 : K)) =
        MonoidAlgebra.single ⟨t ^ k * (n : H) * t ^ (-k), htN k n⟩ (1 : K))
    (htinf : ∀ k : ℤ, k ≠ 0 → t ^ k ∉ N)
    (hgen : ∀ h : H, ∃ (n : N) (k : ℤ), h = (n : H) * t ^ k)
    (y : MonoidAlgebra K H) :
    Phi htN hact (Psi htN hact htinf hgen y) = y := by
  -- It suffices to check the identity on the group-like generators `single h 1`, since both
  -- `Psi` and `Phi` are `K`-linear.
  refine MonoidAlgebra.induction_on (motive := fun y =>
    Phi htN hact (Psi htN hact htinf hgen y) = y) y ?_ ?_ ?_
  · intro h
    rw [MonoidAlgebra.of_apply, Psi_single]
    show Phi htN hact (psiFun N t hgen h) = MonoidAlgebra.single h 1
    rw [psiFun, Phi_single, genT_ofAdd]
    simp only [inclN, MonoidAlgebra.mapDomainAlgHom_apply, MonoidAlgebra.mapDomain_single]
    rw [MonoidAlgebra.single_mul_single, one_mul]
    congr 1
    exact (npart_mul_kpart N t hgen h).symm
  · intro x y ihx ihy
    simp only [map_add, ihx, ihy]
  · intro c x ih
    simp only [map_smul, ih]

end Work.ORHughesFree.HughesFree
