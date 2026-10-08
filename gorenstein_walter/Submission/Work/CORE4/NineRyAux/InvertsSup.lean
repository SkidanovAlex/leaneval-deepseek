import Mathlib

-- The element-commutator notation `⁅g, h⁆` for group elements lives in the
-- `commutatorElement` scope.
open scoped commutatorElement

set_option linter.unusedVariables false

namespace Work.CORE4.NineRyAux

/-- If `r` is an involution inverting an element `x` of odd order, and `x` lies in
`B ⊔ N` with `r` and `B` normalizing `N`, then `x` lies in `N ⊔ ⁅B, ⟨r⟩⁆`.

The mathematical content: `x * x = ⁅x, r⁆` (since `r x r = x⁻¹` forces `r x⁻¹ r = x`),
and any commutator `⁅g, r'⁆` with `g ∈ B ⊔ N` and `r' ∈ ⟨r⟩` lies in `N ⊔ ⁅B, ⟨r⟩⁆`
because `N` is normalized by `B` and `r`.  Finally, since `orderOf x` is odd, `x` is a
power of `x * x`. -/
theorem InvertsSup {G : Type*} [Group G] {r : G}
    (hr2 : r * r = 1) {B K F : Subgroup G}
    (hBN : B ≤ Subgroup.normalizer ((K ⊔ F : Subgroup G) : Set G))
    (hrN : r ∈ Subgroup.normalizer ((K ⊔ F : Subgroup G) : Set G))
    (hrB : r ∈ Subgroup.normalizer ((B : Subgroup G) : Set G))
    {x : G} (hx : x ∈ B ⊔ (K ⊔ F)) (hinv : r * x * r⁻¹ = x⁻¹) (hxodd : Odd (orderOf x)) :
    x ∈ (K ⊔ F) ⊔ ⁅B, Subgroup.zpowers r⁆ := by
  have hr' : r⁻¹ = r := inv_eq_of_mul_eq_one_right hr2
  -- `r` inverts `x`, hence `r * x⁻¹ * r = x`.
  have hxconj : r * x * r = x⁻¹ := by rw [← hinv, hr']
  have hxinv : r * x⁻¹ * r = x := by
    have h1 : (r * x * r)⁻¹ = x := by rw [hxconj, inv_inv]
    have h2 : (r * x * r)⁻¹ = r * x⁻¹ * r := by
      rw [mul_inv_rev, mul_inv_rev, hr']; simp only [mul_assoc]
    rw [h2] at h1; exact h1
  -- hence `x * x = ⁅x, r⁆`.
  have hx2 : x * x = ⁅x, r⁆ := by
    rw [commutatorElement_def, hr', mul_assoc x r x⁻¹, mul_assoc x (r * x⁻¹) r, hxinv]
  -- `N := K ⊔ F` is normalized by `r`, so `⁅N, ⟨r⟩⁆ ≤ N`.
  have hNcomm : ⁅(K ⊔ F : Subgroup G), Subgroup.zpowers r⁆ ≤ (K ⊔ F) :=
    Subgroup.le_normalizer_iff_commutator_le_left.mp (Subgroup.zpowers_le.mpr hrN)
  -- `⁅B ⊔ N, ⟨r⟩⁆ ≤ N ⊔ ⁅B, ⟨r⟩⁆`.
  have hcomm : ⁅B ⊔ (K ⊔ F), Subgroup.zpowers r⁆ ≤ (K ⊔ F) ⊔ ⁅B, Subgroup.zpowers r⁆ := by
    rw [Subgroup.commutator_le]
    intro g₁ hg₁ g₂ hg₂
    have h : g₁ ∈ ((B ⊔ (K ⊔ F) : Subgroup G) : Set G) := hg₁
    rw [Subgroup.coe_mul_of_left_le_normalizer_right B (K ⊔ F) hBN] at h
    rw [Set.mem_mul] at h
    obtain ⟨b, hb, n, hn, hbn⟩ := h
    rw [← hbn, commutatorElement_mul_left_eq_conj_mul]
    have hnN : ⁅n, g₂⁆ ∈ (K ⊔ F : Subgroup G) :=
      hNcomm (Subgroup.commutator_mem_commutator hn hg₂)
    have hconjN : b * ⁅n, g₂⁆ * b⁻¹ ∈ (K ⊔ F : Subgroup G) :=
      (Subgroup.mem_normalizer_iff.mp (hBN hb) ⁅n, g₂⁆).mp hnN
    have hbC : ⁅b, g₂⁆ ∈ ⁅B, Subgroup.zpowers r⁆ :=
      Subgroup.commutator_mem_commutator hb hg₂
    exact Subgroup.mul_mem_sup hconjN hbC
  have hx2mem : x * x ∈ (K ⊔ F) ⊔ ⁅B, Subgroup.zpowers r⁆ := by
    rw [hx2]
    exact hcomm (Subgroup.commutator_mem_commutator hx (Subgroup.mem_zpowers r))
  -- `orderOf x` is odd, so `x` is a power of `x * x`.
  obtain ⟨k, hk⟩ := hxodd
  have key : (x * x) ^ (k + 1) = x := by
    rw [← pow_two x, ← pow_mul]
    rw [show 2 * (k + 1) = orderOf x + 1 from by rw [hk]; ring]
    rw [pow_succ, pow_orderOf_eq_one, one_mul]
  exact key ▸ Subgroup.pow_mem _ hx2mem (k + 1)

end Work.CORE4.NineRyAux
