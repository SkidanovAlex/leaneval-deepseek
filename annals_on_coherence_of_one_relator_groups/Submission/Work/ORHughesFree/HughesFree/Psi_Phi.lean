import Mathlib
import Submission.Work.ORHughesFree.HughesFree.skewLaurentDecompAux
import Submission.Work.ORHughesFree.HughesFree.psi_t_pow
import Submission.Work.ORHughesFree.HughesFree.Psi_inclN

namespace Work.ORHughesFree.HughesFree

theorem Psi_Phi {K : Type} [Field K] {G : Type} [Group G] {H : Subgroup G} {N : Subgroup H}
    {t : H} (htN : ∀ (k : ℤ) (n : N), t ^ k * (n : H) * t ^ (-k) ∈ N)
    [MulSemiringAction (Multiplicative ℤ) (MonoidAlgebra K N)]
    [SMulCommClass (Multiplicative ℤ) K (MonoidAlgebra K N)]
    (hact : ∀ (k : ℤ) (n : N), (Multiplicative.ofAdd k) • (MonoidAlgebra.single n (1 : K)) =
        MonoidAlgebra.single ⟨t ^ k * (n : H) * t ^ (-k), htN k n⟩ (1 : K))
    (htinf : ∀ k : ℤ, k ≠ 0 → t ^ k ∉ N)
    (hgen : ∀ h : H, ∃ (n : N) (k : ℤ), h = (n : H) * t ^ k)
    (x : SkewMonoidAlgebra (MonoidAlgebra K N) (Multiplicative ℤ)) :
    Psi htN hact htinf hgen (Phi htN hact x) = x := by
  -- `Psi` sends the group-like generator `genT K t a` back to the variable `single a 1`
  have Psi_genT : ∀ a : Multiplicative ℤ,
      Psi htN hact htinf hgen (genT K t a) = SkewMonoidAlgebra.single a 1 := by
    intro a
    obtain ⟨k, hk⟩ : ∃ k : ℤ, a = Multiplicative.ofAdd k :=
      ⟨Multiplicative.toAdd a, (ofAdd_toAdd a).symm⟩
    rw [hk, genT_ofAdd K t k, Psi_single, psi_t_pow htN hact htinf hgen k]
  -- and on `single a b` the composite `Psi ∘ Phi` is the identity
  have key : ∀ (a : Multiplicative ℤ) (b : MonoidAlgebra K N),
      Psi htN hact htinf hgen (Phi htN hact (SkewMonoidAlgebra.single a b))
        = SkewMonoidAlgebra.single a b := by
    intro a b
    rw [Phi_single, map_mul, Psi_inclN htN hact htinf hgen b, Psi_genT a,
      SkewMonoidAlgebra.single_mul_single]
    simp
  -- both sides are additive, so agreement on the `single a b` suffices
  refine SkewMonoidAlgebra.induction_on x ?_ ?_ ?_
  · simp
  · intro g a; exact key g a
  · intro f g hf hg; simp only [map_add, hf, hg]

end Work.ORHughesFree.HughesFree
