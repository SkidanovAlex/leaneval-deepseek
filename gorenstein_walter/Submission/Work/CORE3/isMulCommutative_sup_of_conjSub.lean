import Mathlib
import Submission.Work.CORE3.Defs

namespace Work.CORE3

open Subgroup

/-- If two abelian subgroups `P` and `Q` normalize each other and intersect trivially, then the
subgroup they generate is abelian.

Indeed, for `p ∈ P` and `q ∈ Q` the commutator `p * q * p⁻¹ * q⁻¹` lies both in `P`
(since `Q ≤ N(P)`) and in `Q` (since `P ≤ N(Q)`), hence is `1` because `P ⊓ Q = ⊥`.
So `p` and `q` commute; as `P` and `Q` are each commutative and commute elementwise, every
element of `P ⊔ Q` commutes with every element of `P ∪ Q`, and since the latter generates
`P ⊔ Q` the whole of `P ⊔ Q` is commutative. -/
theorem isMulCommutative_sup_of_le_normalizer {G : Type*} [Group G] (P Q : Subgroup G)
    (hP : IsMulCommutative P) (hQ : IsMulCommutative Q)
    (hPn : Q ≤ Subgroup.normalizer (P : Set G))
    (hQn : P ≤ Subgroup.normalizer (Q : Set G))
    (hinf : P ⊓ Q = ⊥) :
    IsMulCommutative (P ⊔ Q : Subgroup G) := by
  have hcross : ∀ p ∈ P, ∀ q ∈ Q, p * q = q * p := by
    intro p hp q hq
    have hcQ : p * q * p⁻¹ * q⁻¹ ∈ Q := by
      have h1 : p * q * p⁻¹ ∈ Q := (Subgroup.le_normalizer_iff.mp hQn) p hp q hq
      exact Q.mul_mem h1 (Q.inv_mem hq)
    have hcP : p * q * p⁻¹ * q⁻¹ ∈ P := by
      have h1 : q * p⁻¹ * q⁻¹ ∈ P := (Subgroup.le_normalizer_iff.mp hPn) q hq p⁻¹ (P.inv_mem hp)
      have h2 : p * (q * p⁻¹ * q⁻¹) ∈ P := P.mul_mem hp h1
      simpa only [mul_assoc] using h2
    have hmem : p * q * p⁻¹ * q⁻¹ ∈ (⊥ : Subgroup G) := by
      rw [← hinf]; exact ⟨hcP, hcQ⟩
    rw [Subgroup.mem_bot] at hmem
    have h1 : (p * q) * (q * p)⁻¹ = 1 := by
      rw [mul_inv_rev]
      calc (p * q) * (p⁻¹ * q⁻¹) = p * q * p⁻¹ * q⁻¹ := by group
        _ = 1 := hmem
    exact mul_inv_eq_one.mp h1
  have hPleC : P ≤ Subgroup.centralizer ((P : Set G) ∪ (Q : Set G)) := by
    intro p hp
    rw [Subgroup.mem_centralizer_iff]
    rintro t (ht | ht)
    · exact setLike_mul_comm ht hp
    · exact (hcross p hp t ht).symm
  have hQleC : Q ≤ Subgroup.centralizer ((P : Set G) ∪ (Q : Set G)) := by
    intro q hq
    rw [Subgroup.mem_centralizer_iff]
    rintro t (ht | ht)
    · exact hcross t ht q hq
    · exact setLike_mul_comm ht hq
  have hSle : (P ⊔ Q : Subgroup G) ≤ Subgroup.centralizer ((P : Set G) ∪ (Q : Set G)) :=
    sup_le hPleC hQleC
  refine IsMulCommutative.of_setLike_mul_comm ?_
  intro x hx y hy
  have hxC : x ∈ Subgroup.centralizer ((P : Set G) ∪ (Q : Set G)) := hSle hx
  rw [Subgroup.mem_centralizer_iff] at hxC
  have hSx : (P ⊔ Q : Subgroup G) ≤ Subgroup.centralizer ({x} : Set G) := by
    rw [Subgroup.sup_eq_closure, Subgroup.closure_le]
    intro t ht
    change t ∈ Subgroup.centralizer ({x} : Set G)
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    rw [Set.mem_singleton_iff] at hz
    subst hz
    exact (hxC t ht).symm
  have hyx := hSx hy
  rw [Subgroup.mem_centralizer_iff] at hyx
  exact hyx x (Set.mem_singleton x)

theorem isMulCommutative_sup_of_conjSub {G : Type*} [Group G] {P : Subgroup G} {g : G}
    (hP : IsMulCommutative P)
    (hPn : Work.GW2.conjSub g P ≤ Subgroup.normalizer (P : Set G))
    (hQn : P ≤ Subgroup.normalizer (Work.GW2.conjSub g P : Set G))
    (hinf : P ⊓ Work.GW2.conjSub g P = ⊥) :
    IsMulCommutative (P ⊔ Work.GW2.conjSub g P : Subgroup G) :=
  isMulCommutative_sup_of_le_normalizer P (Work.GW2.conjSub g P) hP
    (Subgroup.map_isMulCommutative P (MulAut.conj g).toMonoidHom) hPn hQn hinf

end Work.CORE3
