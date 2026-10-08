import Mathlib
import Submission.Work.CORE3.Defs

namespace Work.CORE3.FreeAux

/-- If `P ≤ D` are subgroups of a finite group `G` with `|D| = 2 * |P|`, then every
element `d ∈ D \ P` has even order.  Indeed `P` has index `2` in `D`, so `d ^ 2 ∈ P`,
while `d ∉ P`; if `orderOf d` were odd then `d = (d ^ 2) ^ ((orderOf d + 1) / 2) ∈ P`,
a contradiction. -/
theorem EvenOrderOfIndexTwo {G : Type} [Group G] [Finite G] {P D : Subgroup G}
    (hPle : P ≤ D) (hcard : Nat.card D = 2 * Nat.card P) {d : G} (hdD : d ∈ D)
    (hdP : d ∉ P) : Even (orderOf d) := by
  -- `P` has index `2` inside the subgroup `D`.
  have hrel : P.relIndex D = 2 := by
    have h1 := Subgroup.relIndex_mul_card (H := P) (K := D)
    rw [inf_of_le_left hPle, hcard] at h1
    exact Nat.eq_of_mul_eq_mul_right Nat.card_pos h1
  have hindex : (P.subgroupOf D).index = 2 := hrel
  -- Hence the square of any element of `D` lies in `P`; in particular `d ^ 2 ∈ P`.
  have hsq : d * d ∈ P := by
    have hmem : (⟨d, hdD⟩ : D) * ⟨d, hdD⟩ ∈ P.subgroupOf D :=
      Subgroup.mul_self_mem_of_index_two hindex ⟨d, hdD⟩
    rwa [Subgroup.mem_subgroupOf] at hmem
  have hd2 : d ^ 2 ∈ P := by rw [pow_two]; exact hsq
  -- If `orderOf d` were odd, `d` would be a power of `d ^ 2`, hence lie in `P`.
  by_contra hodd
  rw [Nat.not_even_iff_odd] at hodd
  obtain ⟨k, hk⟩ := hodd
  have hpow : (d ^ 2) ^ (k + 1) = d := by
    rw [← pow_mul]
    have hk' : 2 * (k + 1) = orderOf d + 1 := by omega
    rw [hk', pow_succ, pow_orderOf_eq_one, one_mul]
  exact hdP (hpow ▸ Subgroup.pow_mem P hd2 (k + 1))

end Work.CORE3.FreeAux
