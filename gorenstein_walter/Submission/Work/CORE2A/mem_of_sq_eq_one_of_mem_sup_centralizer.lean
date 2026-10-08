import Mathlib
import Submission.Work.CORE2A.Defs

/-!
# CORE2A: involutions of `E ⊔ C_K(E)` with `|C_K(E)|` odd lie in `E`

Let `E ≤ K` be a subgroup of a finite group `K` and let `C = C_K(E)` be its centralizer in `K`.
If `|C|` is odd, then every involution `x` of the join `E ⊔ C` already lies in `E`.

The mathematics is a two-line computation.  Since `C` centralizes `E`, any `x ∈ E ⊔ C` is a
product `x = e · c` with `e ∈ E`, `c ∈ C` (the join is the pointwise product because `C`
normalizes `E`).  Then `x² = (e c)² = e² c²` by commutativity, so `e² c² = 1` gives
`c² = e^{-2} ∈ E`.  Finally `c ∈ C` has odd order `n` (its order divides the odd number `|C|`),
hence `c = c^{n+1} = (c²)^{(n+1)/2} ∈ E` because `c² ∈ E`.  Therefore `x = e c ∈ E`.

Thus the hypothesis `Odd (Nat.card (center E))` is not needed — the statement is true with the
hypothesis present, and it is kept verbatim as requested.

The supporting lemma `mem_sup_of_le_normalizer` is the standard decomposition of the join of a
subgroup with a subgroup of its normalizer.
-/

namespace Work.CORE2A

/-- **Decomposition of a join.**  If `C ≤ N_G(E)`, then every element of `E ⊔ C` is a product
`e * c` with `e ∈ E`, `c ∈ C`.  (For commuting subgroups this is the classical
`E ⊔ C = E · C`.) -/
theorem mem_sup_of_le_normalizer {G : Type} [Group G] (E C : Subgroup G)
    (h : C ≤ Subgroup.normalizer (E : Set G)) {x : G} (hx : x ∈ E ⊔ C) :
    ∃ e ∈ E, ∃ c ∈ C, e * c = x := by
  -- `E` is normal in the join `E ⊔ C`: both `E` and `C` lie in `N_G(E)`.
  have hEnorm : (E.subgroupOf (E ⊔ C)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).mpr
      (sup_le Subgroup.le_normalizer h)
  -- Work inside `↥(E ⊔ C)`, where `E.subgroupOf _ ⊔ C.subgroupOf _ = ⊤`.
  have hxm : (⟨x, hx⟩ : ↥(E ⊔ C)) ∈ E.subgroupOf (E ⊔ C) ⊔ C.subgroupOf (E ⊔ C) := by
    rw [← Subgroup.subgroupOf_sup le_sup_left le_sup_right, Subgroup.subgroupOf_self]
    trivial
  -- A normal factor of a join: membership in `N ⊔ H` is `∃ n ∈ N, ∃ h ∈ H, n * h = x`.
  obtain ⟨y, hy, z, hz, hyz⟩ := (Subgroup.mem_sup_of_normal_left (hs := hEnorm)).mp hxm
  refine ⟨(y : G), Subgroup.mem_subgroupOf.mp hy, (z : G), Subgroup.mem_subgroupOf.mp hz, ?_⟩
  have hh := congrArg (fun w : ↥(E ⊔ C) => (w : G)) hyz
  simpa using hh

set_option linter.unusedVariables false in
theorem mem_of_sq_eq_one_of_mem_sup_centralizer {K : Type} [Group K] [Finite K] (E : Subgroup K)
    (hZodd : Odd (Nat.card (Subgroup.center ↥E)))
    (hCodd : Odd (Nat.card (Subgroup.centralizer (E : Set K))))
    {x : K} (hx : x ∈ E ⊔ Subgroup.centralizer (E : Set K)) (hx2 : x ^ 2 = 1) : x ∈ E := by
  classical
  -- Decompose `x = e * c` with `e ∈ E`, `c ∈ C = C_K(E)` (the centralizer normalizes `E`).
  obtain ⟨e, he, c, hc, hec⟩ :=
    mem_sup_of_le_normalizer E (Subgroup.centralizer (E : Set K))
      (Subgroup.centralizer_le_normalizer (E : Set K)) hx
  -- `e` and `c` commute.
  have hec_comm : e * c = c * e := (Subgroup.mem_centralizer_iff.mp hc) e he
  -- `x² = (e * c)² = e² * c²`.
  have hmul : (e * c) * (e * c) = e ^ 2 * c ^ 2 := by
    calc (e * c) * (e * c) = e * (c * e) * c := by group
      _ = e * (e * c) * c := by rw [← hec_comm]
      _ = e ^ 2 * c ^ 2 := by rw [pow_two, pow_two]; group
  have hx2' : e ^ 2 * c ^ 2 = 1 := by
    rw [← hmul, show (e * c) * (e * c) = x ^ 2 by rw [hec, pow_two]]
    exact hx2
  -- Hence `c² = (e²)⁻¹ ∈ E`.
  have hc2E : c ^ 2 ∈ E := by
    have h2 : c ^ 2 = (e ^ 2)⁻¹ := eq_inv_of_mul_eq_one_right hx2'
    rw [h2]
    exact E.inv_mem (E.pow_mem he 2)
  -- `orderOf c` is odd (it divides the odd number `|C|`).
  have hodd : Odd (orderOf c) := by
    rw [← Nat.not_even_iff_odd, even_iff_two_dvd]
    intro h
    exact (Nat.not_even_iff_odd.mpr hCodd)
      (even_iff_two_dvd.mpr
        (h.trans (Subgroup.orderOf_dvd_natCard (Subgroup.centralizer (E : Set K)) hc)))
  -- In an odd-order group every element is a power of its square: `c = (c²)^m`.
  obtain ⟨m, hm⟩ := exists_pow_eq_pow_two_mul (pow_orderOf_eq_one c) hodd 1
  have hcE : c ∈ E := by
    have h : c = (c ^ 2) ^ m := by
      rw [← pow_mul, ← hm, pow_one]
    rw [h]
    exact E.pow_mem hc2E m
  -- Finally `x = e * c ∈ E`.
  rw [← hec]
  exact E.mul_mem he hcE

end Work.CORE2A
