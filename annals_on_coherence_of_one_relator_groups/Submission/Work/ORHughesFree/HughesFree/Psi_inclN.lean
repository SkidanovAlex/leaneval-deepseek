import Mathlib
import Submission.Work.ORHughesFree.HughesFree.skewLaurentDecompAux

namespace Work.ORHughesFree.HughesFree

theorem Psi_inclN {K : Type} [Field K] {G : Type} [Group G] {H : Subgroup G} {N : Subgroup H}
    {t : H} (htN : ∀ (k : ℤ) (n : N), t ^ k * (n : H) * t ^ (-k) ∈ N)
    [MulSemiringAction (Multiplicative ℤ) (MonoidAlgebra K N)]
    [SMulCommClass (Multiplicative ℤ) K (MonoidAlgebra K N)]
    (hact : ∀ (k : ℤ) (n : N), (Multiplicative.ofAdd k) • (MonoidAlgebra.single n (1 : K)) =
        MonoidAlgebra.single ⟨t ^ k * (n : H) * t ^ (-k), htN k n⟩ (1 : K))
    (htinf : ∀ k : ℤ, k ≠ 0 → t ^ k ∉ N)
    (hgen : ∀ h : H, ∃ (n : N) (k : ℤ), h = (n : H) * t ^ k)
    (b : MonoidAlgebra K N) :
    Psi htN hact htinf hgen (inclN K H N b) = SkewMonoidAlgebra.single 1 b := by
  -- It suffices to check the identity on the group-like generators `single n 1` (`n : N`),
  -- since both `inclN`, `Psi` and `single 1` are `K`-linear.
  refine MonoidAlgebra.induction_on
    (motive := fun x => Psi htN hact htinf hgen (inclN K H N x)
      = SkewMonoidAlgebra.single (1 : Multiplicative ℤ) x) b ?_ ?_ ?_
  · -- the generator `single m 1` maps to `single (m : H) 1`, whose decomposition is `m * t ^ 0`
    intro m
    have hdec : ((npart N t hgen (m : H) : N) : H) * t ^ (kpart N t hgen (m : H))
        = ((m : N) : H) * t ^ (0 : ℤ) := by
      rw [← npart_mul_kpart N t hgen (m : H)]
      simp
    obtain ⟨hk, hn⟩ := decomp_unique htinf hdec
    rw [MonoidAlgebra.of_apply]
    simp only [inclN, MonoidAlgebra.mapDomainAlgHom_apply, MonoidAlgebra.mapDomain_single]
    rw [Psi_single]
    change psiFun N t hgen (m : H)
      = SkewMonoidAlgebra.single (1 : Multiplicative ℤ) (MonoidAlgebra.single m 1)
    rw [psiFun, hk, hn, ofAdd_zero]
  · intro x y ihx ihy
    rw [map_add, map_add, ihx, ihy]
    exact (SkewMonoidAlgebra.single_add 1 x y).symm
  · intro r x ih
    rw [map_smul, map_smul, ih, SkewMonoidAlgebra.smul_single]

end Work.ORHughesFree.HughesFree
