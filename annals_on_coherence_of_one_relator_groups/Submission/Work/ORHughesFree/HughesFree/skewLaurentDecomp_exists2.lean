import Mathlib
import Submission.Work.ORHughesFree.HughesFree
import Submission.Work.ORHughesFree.HughesFree.exists_normal_cyclic_quotient
import Submission.Work.ORHughesFree.HughesFree.skewLaurentDecompAux
import Submission.Work.ORHughesFree.HughesFree.Phi_Psi
import Submission.Work.ORHughesFree.HughesFree.Psi_Phi

namespace Work.ORHughesFree.HughesFree

theorem skewLaurentDecomp_exists2 {K : Type} [Field K] {G : Type} [Group G]
    (H : Subgroup G) (N : Subgroup H) (t : H) (hNnorm : N.Normal)
    (htN : ∀ (k : ℤ) (n : N), t ^ k * (n : H) * t ^ (-k) ∈ N)
    (hgen : ∀ h : H, ∃ (n : N) (k : ℤ), h = (n : H) * t ^ k)
    (htinf : ∀ k : ℤ, k ≠ 0 → t ^ k ∉ N)
    [inst : MulSemiringAction (Multiplicative ℤ) (MonoidAlgebra K N)]
    [SMulCommClass (Multiplicative ℤ) K (MonoidAlgebra K N)]
    (hact : ∀ (k : ℤ) (n : N),
      (Multiplicative.ofAdd k) • (MonoidAlgebra.single n (1 : K)) =
        MonoidAlgebra.single ⟨t ^ k * (n : H) * t ^ (-k), htN k n⟩ (1 : K)) :
    Nonempty (Work.ORHughesFree.SkewLaurentDecomp K G H N) := by
  classical
  -- the group-like unit `t` of `K[H]`
  have h1 : MonoidAlgebra.single t (1 : K) * MonoidAlgebra.single t⁻¹ (1 : K) = 1 := by
    rw [MonoidAlgebra.single_mul_single]
    simp [MonoidAlgebra.one_def]
  have h2 : MonoidAlgebra.single t⁻¹ (1 : K) * MonoidAlgebra.single t (1 : K) = 1 := by
    rw [MonoidAlgebra.single_mul_single]
    simp [MonoidAlgebra.one_def]
  let uT : (MonoidAlgebra K H)ˣ :=
    Units.mk (MonoidAlgebra.single t (1 : K)) (MonoidAlgebra.single t⁻¹ (1 : K)) h1 h2
  -- the ring equivalence `K[N][t^{±1}; τ] ≃+* K[H]`
  let e : SkewMonoidAlgebra (MonoidAlgebra K N) (Multiplicative ℤ) ≃+* MonoidAlgebra K H :=
    { (Phi htN hact).toRingHom with
      invFun := ⇑(Psi htN hact htinf hgen)
      left_inv := fun x => Psi_Phi htN hact htinf hgen x
      right_inv := fun y => Phi_Psi htN hact htinf hgen y }
  have he : e Work.ORHughesFree.skewLaurentT = (uT : MonoidAlgebra K H) := by
    show Phi htN hact
      (SkewMonoidAlgebra.single (Multiplicative.ofAdd (1 : ℤ)) (1 : MonoidAlgebra K N))
      = MonoidAlgebra.single t (1 : K)
    rw [Phi_single, genT_ofAdd]
    simp
  have hiso_single : ∀ b : MonoidAlgebra K N,
      e (SkewMonoidAlgebra.single (1 : Multiplicative ℤ) b) =
        MonoidAlgebra.mapDomainRingHom K (Subgroup.subtype N) b := by
    intro b
    show Phi htN hact (SkewMonoidAlgebra.single (1 : Multiplicative ℤ) b) = _
    rw [Phi_single]
    have h1 : genT K t (1 : Multiplicative ℤ) = 1 := map_one (genT K t)
    rw [h1, mul_one]
    rfl
  exact ⟨{ iso := e
           t := uT
           iso_t := he
           iso_single := hiso_single }⟩

end Work.ORHughesFree.HughesFree
