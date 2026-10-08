import Mathlib

namespace Work.BG

/-- If `D` is a finite cyclic group (written multiplicatively) and `K ≤ L ≤ D` are subgroups
such that every square of an element of `L` lies in `K`, then `K` has index at most two in `L`.

The proof goes through the quotient `L ⧸ K`: it is a quotient of the cyclic group `L`, hence
cyclic, and by hypothesis every element has square `1`, so its exponent divides `2`.  A finite
cyclic group has cardinality equal to its exponent, whence `L ⧸ K` has at most `2` elements, i.e.
`K` has index at most `2` in `L`. -/
theorem s02_indexSq {D : Type} [CommGroup D] [IsCyclic D] [Finite D]
    (K L : Subgroup D) (hK : K ≤ L) (hsq : ∀ x ∈ L, x ^ 2 ∈ K) :
    (K.subgroupOf L).index ≤ 2 := by
  have _ : K ≤ L := hK
  -- Abbreviation for `K` viewed as a subgroup of `L`.
  let N : Subgroup L := K.subgroupOf L
  -- Every element of the quotient `L ⧸ N` is killed by `2`, since squares of elements of `L`
  -- lie in `K`.
  have hexp : Monoid.exponent (L ⧸ N) ∣ 2 := by
    rw [Monoid.exponent_dvd_iff_forall_pow_eq_one]
    intro q
    obtain ⟨b, rfl⟩ := QuotientGroup.mk'_surjective N q
    rw [← map_pow, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    show b ^ 2 ∈ N
    simp only [N, Subgroup.mem_subgroupOf]
    simpa using hsq (b : D) b.2
  -- `L ⧸ N` is cyclic (a quotient of the cyclic group `L`), and a finite cyclic group has
  -- cardinality equal to its exponent.
  have hcard : Nat.card (L ⧸ N) ≤ 2 := by
    rw [← IsCyclic.exponent_eq_card (α := L ⧸ N)]
    exact Nat.le_of_dvd (by norm_num) hexp
  -- The index of `K.subgroupOf L` is by definition the cardinality of the quotient `L ⧸ N`.
  show (K.subgroupOf L).index ≤ 2
  show Nat.card (L ⧸ N) ≤ 2
  exact hcard

end Work.BG
