import Mathlib
import Submission.Work.BSW.Cases.K4.benderCase2Aux

namespace Work.BSW.Cases.K4

/-- In the Bender `|K| = 4` setting (`Work.BSW.Cases.K4.K4Hyp`) an element `w` of order `4` lying in
`N_G(V)` cannot be inverted by an involution `u ∉ N_G(V)`.

Indeed, put `z = w ^ 2`.  Since `w ∈ N_G(V)` and `orderOf w = 4`, the element `z = w * w` lies in
`V` (the square of an order-`4` normalizer element lands in the Klein four-group), hence centralizes
`V` because `V` is abelian; so `V ≤ C_G(z)`.  Also `u` inverts `w`, so `u` centralises `z = w * w`.
Since `z` is an involution, `C_G(z)` has order `8` while `|V| = 4`, so `V` has index `2` in `C_G(z)`
and is therefore normal there; in particular `u ∈ C_G(z) ⊆ N_G(V)`, contradicting `u ∉ N_G(V)`. -/
theorem not_inverted_of_orderOf_eq_four {G : Type} [Group G] [Finite G]
    (h : Work.BSW.Cases.K4.K4Hyp G) {V : Subgroup G} (hV : Work.BSW.Cases.K4.IsV4 V) {u w : G}
    (huH : u ∉ Subgroup.normalizer (V : Set G)) (hu2 : orderOf u = 2)
    (hwH : w ∈ Subgroup.normalizer (V : Set G)) (hw4 : orderOf w = 4)
    (hinv : u * w * u = w⁻¹) : False := by
  have hw4' : w ^ 4 = 1 := by rw [← hw4]; exact pow_orderOf_eq_one w
  -- `z = w ^ 2` is an involution
  have hz2 : orderOf (w ^ 2) = 2 := by rw [orderOf_pow, hw4]; norm_num
  have hzsq : w ^ 2 * w ^ 2 = 1 := by
    have hh : w ^ (2 + 2 : ℕ) = w ^ 2 * w ^ 2 := pow_add w 2 2
    rw [← hh]
    simpa using hw4'
  have hu2' : u * u = 1 := by rw [← pow_two, ← hu2]; exact pow_orderOf_eq_one u
  -- `u` centralises `w ^ 2`
  have huzu : u * w ^ 2 * u = w ^ 2 := by
    have h1 : u * w ^ 2 * u = (u * w * u) * (u * w * u) := by
      rw [pow_two]
      rw [show u * (w * w) * u = u * w * (u * u) * w * u from by rw [hu2']; group]
      group
    rw [h1, hinv]
    rw [show w⁻¹ * w⁻¹ = (w ^ 2)⁻¹ from by rw [pow_two]; group,
      inv_eq_of_mul_eq_one_right hzsq]
  have hcomm : u * w ^ 2 = w ^ 2 * u := by
    calc u * w ^ 2 = u * w ^ 2 * (u * u) := by rw [hu2', mul_one]
      _ = (u * w ^ 2 * u) * u := by rw [pow_two]; group
      _ = w ^ 2 * u := by rw [huzu]
  have hu_cent : u ∈ cent G (w ^ 2) := Subgroup.mem_centralizer_singleton_iff.mpr hcomm
  -- `V ≤ C_G(w ^ 2)`
  have hw2V : w * w ∈ V := sq_mem_of_orderOf_eq_four_of_mem_normalizer h hV hwH hw4
  have hVle : V ≤ cent G (w ^ 2) := by
    intro v hv
    rw [Subgroup.mem_centralizer_singleton_iff, pow_two]
    exact IsV4.comm hV hv hw2V
  -- `V` has index `2` in `C_G(w ^ 2)`, so `u ∈ C_G(w ^ 2) ⊆ N_G(V)`
  have hcard : 2 * Nat.card ↥V = Nat.card ↥(cent G (w ^ 2)) := by
    rw [hV.1, h.2.1 (w ^ 2) hz2]
  exact huH ((le_normalizer_of_two_mul_card hVle hcard) hu_cent)

end Work.BSW.Cases.K4
