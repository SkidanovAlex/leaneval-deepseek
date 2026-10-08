import Mathlib
import Submission.Work.CORE4.Case2PerXBound9

namespace Work.CORE4

open Subgroup
open scoped Pointwise

/-!
# `Work.CORE4.SupProjPrimeOrder`

Let `P, E ≤ G` be subgroups whose elements commute pairwise (`hcomm`), `p` a prime with
`Nat.card P = p`, and `X ≤ P ⊔ E` a subgroup with `Nat.card X = p` and `X ≠ P`.  Then there is a
subgroup `K ≤ E` with `Nat.card K = p` and `P ⊔ X = P ⊔ K`.

## Mathematical proof

Fix `a ∈ X`, `a ≠ 1`.  Since `|X| = p` is prime, `orderOf a = p` and `X = ⟨a⟩ = zpowers a`.

Because every element of `P` commutes with every element of `E`, we have `P ≤ N_G(E)`, so every
element of `P ⊔ E = P · E` is a product; write `a = p₀ · e₀` with `p₀ ∈ P`, `e₀ ∈ E`.

* `e₀ ≠ 1`: otherwise `a = p₀ ∈ P`, so `X = ⟨a⟩ ≤ P` and, since `|X| = |P| = p`, `X = P`,
  contradicting `X ≠ P`.
* `e₀ ^ p = 1`: indeed `a ^ p = 1` and, as `p₀` and `e₀` commute,
  `(p₀ e₀) ^ p = p₀ ^ p · e₀ ^ p` with `p₀ ^ p = 1` because `orderOf p₀ ∣ Nat.card P = p`.

Hence `orderOf e₀ ∣ p` and `orderOf e₀ ≠ 1`, so `orderOf e₀ = p`.  Taking `K := ⟨e₀⟩ ≤ E` we get
`Nat.card K = p`, and

* `X = ⟨a⟩ ≤ P ⊔ K` because `a = p₀ e₀` with `p₀ ∈ P`, `e₀ ∈ K`;
* `K = ⟨e₀⟩ ≤ P ⊔ X` because `e₀ = p₀⁻¹ · a` with `p₀⁻¹ ∈ P`, `a ∈ X`.

Therefore `P ⊔ X = P ⊔ K`, and `K` is the required subgroup. -/

/-- **Projection of a prime-order subgroup onto the commuting factor.**  If the subgroups `P` and
`E` commute elementwise, `p` is prime, `Nat.card P = p`, and `X ≤ P ⊔ E` is a subgroup of order `p`
different from `P`, then `X` admits a conjugate-in-`E` description: there is `K ≤ E` of order `p`
with `P ⊔ X = P ⊔ K`. -/
theorem SupProjPrimeOrder {G : Type} [Group G] [Finite G] {P E X : Subgroup G}
    (hcomm : ∀ x ∈ P, ∀ y ∈ E, x * y = y * x)
    {p : ℕ} (hpp : p.Prime) (hPcard : Nat.card P = p)
    (hX : X ≤ P ⊔ E) (hXne : X ≠ P) (hXcard : Nat.card X = p) :
    ∃ K : Subgroup G, K ≤ E ∧ Nat.card K = p ∧ P ⊔ X = P ⊔ K := by
  classical
  obtain ⟨a, ha_ne⟩ : ∃ a : X, a ≠ 1 := by
    have hnt : Nontrivial X := by
      rw [← Finite.one_lt_card_iff_nontrivial, hXcard]; exact hpp.one_lt
    exact @exists_ne X hnt 1
  have haG_ne : (a : G) ≠ 1 := fun h => ha_ne (Subtype.ext h)
  -- `a` generates `X` and has order `p`
  have hord_a : orderOf (a : G) = p := by
    have hdvd : orderOf (a : G) ∣ p := by
      rw [← hXcard]; exact X.orderOf_dvd_natCard a.2
    rcases (Nat.dvd_prime hpp).mp hdvd with h | h
    · exact absurd (orderOf_eq_one_iff.mp h) haG_ne
    · exact h
  have ha_pow : (a : G) ^ p = 1 := orderOf_dvd_iff_pow_eq_one.mp (by rw [hord_a])
  have hXeq : X = Subgroup.zpowers (a : G) := by
    symm
    refine Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr a.2) ?_
    rw [Nat.card_zpowers, hord_a, hXcard]
  -- every element of `P` normalizes `E`
  have hPcent : P ≤ Subgroup.centralizer (E : Set G) := fun x hx =>
    Subgroup.mem_centralizer_iff.mpr (fun y hy => (hcomm x hx y hy).symm)
  have hLE : P ≤ Subgroup.normalizer (E : Set G) :=
    le_trans hPcent (Subgroup.centralizer_le_normalizer (E : Set G))
  -- decompose `a = p₀ * e₀`
  have hmul : ((P ⊔ E : Subgroup G) : Set G) = (P : Set G) * (E : Set G) :=
    Subgroup.coe_mul_of_left_le_normalizer_right P E hLE
  have ha_sup : (a : G) ∈ ((P ⊔ E : Subgroup G) : Set G) := hX a.2
  rw [hmul] at ha_sup
  obtain ⟨p₀, hp₀, e₀, he₀, hpe⟩ := Set.mem_mul.mp ha_sup
  -- the `E`-component is nontrivial
  have he₀_ne : e₀ ≠ 1 := by
    intro he
    have haP : (a : G) ∈ P := by rw [← hpe, he, mul_one]; exact hp₀
    have hXle : X ≤ P := by rw [hXeq]; exact Subgroup.zpowers_le.mpr haP
    exact hXne (Subgroup.eq_of_le_of_card_ge hXle (by rw [hPcard, hXcard]))
  have hp₀_pow : p₀ ^ p = 1 := by
    have h := Subgroup.orderOf_dvd_natCard P hp₀
    rw [hPcard] at h
    exact orderOf_dvd_iff_pow_eq_one.mp h
  have he₀_pow : e₀ ^ p = 1 := by
    have h := Commute.mul_pow (hcomm p₀ hp₀ e₀ he₀) p
    rw [hpe, ha_pow, hp₀_pow, one_mul] at h
    exact h.symm
  have hord_e₀ : orderOf e₀ = p := by
    have hdvd : orderOf e₀ ∣ p := orderOf_dvd_iff_pow_eq_one.mpr he₀_pow
    rcases (Nat.dvd_prime hpp).mp hdvd with h | h
    · exact absurd (orderOf_eq_one_iff.mp h) he₀_ne
    · exact h
  refine ⟨Subgroup.zpowers e₀, Subgroup.zpowers_le.mpr he₀, ?_, ?_⟩
  · rw [Nat.card_zpowers, hord_e₀]
  · apply le_antisymm
    · apply sup_le le_sup_left
      rw [hXeq]
      refine Subgroup.zpowers_le.mpr ?_
      rw [show (a : G) = p₀ * e₀ from hpe.symm]
      exact (P ⊔ Subgroup.zpowers e₀).mul_mem (Subgroup.mem_sup_left hp₀)
        (Subgroup.mem_sup_right (Subgroup.mem_zpowers e₀))
    · apply sup_le le_sup_left
      refine Subgroup.zpowers_le.mpr ?_
      have he : e₀ = p₀⁻¹ * (a : G) := by rw [← hpe]; group
      rw [he]
      exact (P ⊔ X).mul_mem (Subgroup.mem_sup_left (P.inv_mem hp₀)) (Subgroup.mem_sup_right a.2)

end Work.CORE4
