import Mathlib
import Submission.Work.ORHughesFree.HughesFree
import Submission.Work.ORHughesFree.HughesFree.skewLaurentDecompAux
import Submission.Work.ORHughesFree.HughesFree.skewLaurentDecomp_exists2

namespace Work.ORHughesFree.HughesFree

theorem skewLaurentDecomp_exists2_iso_single {K : Type} [Field K] {G : Type} [Group G]
    (H : Subgroup G) (N : Subgroup H) (t : H) (hNnorm : N.Normal)
    (htN : ∀ (k : ℤ) (n : N), t ^ k * (n : H) * t ^ (-k) ∈ N)
    (hgen : ∀ h : H, ∃ (n : N) (k : ℤ), h = (n : H) * t ^ k)
    (htinf : ∀ k : ℤ, k ≠ 0 → t ^ k ∉ N)
    [inst : MulSemiringAction (Multiplicative ℤ) (MonoidAlgebra K N)]
    [SMulCommClass (Multiplicative ℤ) K (MonoidAlgebra K N)]
    (hact : ∀ (k : ℤ) (n : N),
      (Multiplicative.ofAdd k) • (MonoidAlgebra.single n (1 : K)) =
        MonoidAlgebra.single ⟨t ^ k * (n : H) * t ^ (-k), htN k n⟩ (1 : K)) :
    ∃ d : Work.ORHughesFree.SkewLaurentDecomp K G H N,
      ∀ (a : Multiplicative ℤ) (b : MonoidAlgebra K N),
        d.iso (SkewMonoidAlgebra.single a b) =
          d.inclN b * Work.ORHughesFree.HughesFree.genT K t a := by
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
  -- the ring equivalence `K[N][t^{±1}; τ] ≃+* K[H]`, whose forward map is `Phi`
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
    change Phi htN hact (SkewMonoidAlgebra.single (1 : Multiplicative ℤ) b) =
      MonoidAlgebra.mapDomainRingHom K (Subgroup.subtype N) b
    rw [Phi_single]
    have h1 : genT K t (1 : Multiplicative ℤ) = 1 := map_one (genT K t)
    rw [h1, mul_one]
    rfl
  refine ⟨{ iso := e, t := uT, iso_t := he, iso_single := hiso_single }, ?_⟩
  intro a b
  -- the forward map of `iso` is `Phi`, and `SkewLaurentDecomp.inclN` is `inclN K H N`, so the
  -- claim is exactly `Phi_single`
  change Phi htN hact (SkewMonoidAlgebra.single a b)
    = MonoidAlgebra.mapDomainRingHom K (Subgroup.subtype N) b * genT K t a
  rw [Phi_single]
  rfl

end Work.ORHughesFree.HughesFree
