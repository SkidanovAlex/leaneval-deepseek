import Mathlib

namespace Work.BG

/-- **Burnside's fusion lemma** in the special case of an abelian Sylow subgroup.

If `S` is a Sylow `2`-subgroup of a finite group `G` whose elements commute pairwise
(so `S` is abelian, hence `S ≤ Z(S)`), then any two elements `u v ∈ S` that are
conjugate in `G` are already conjugate by an element of the normalizer `N_G(S)`.

The proof is the standard Burnside argument: writing `v = c * u * c⁻¹` for some `c : Gˣ`,
observe that `S` centralizes `u` (and `v`), so the relevant Sylow subgroups lie inside
`C_G(u)`; Sylow conjugacy there produces `n ∈ N_G(S)` conjugating `u` to `v`.
This is exactly Mathlib's `Sylow.conj_eq_normalizer_conj_of_mem_centralizer`. -/
theorem l42NgridFusion {G : Type} [Group G] [Finite G] (S : Sylow 2 G)
    (hab : ∀ x ∈ (S : Subgroup G), ∀ y ∈ (S : Subgroup G), x * y = y * x)
    {u v : G} (hu : u ∈ (S : Subgroup G)) (hv : v ∈ (S : Subgroup G)) (hconj : IsConj u v) :
    ∃ h ∈ Subgroup.normalizer ((S : Subgroup G) : Set G), h * u * h⁻¹ = v := by
  obtain ⟨c, hc⟩ := hconj
  have hcu : (↑c : G) * u = v * ↑c := hc.eq
  have hu_c : u ∈ Subgroup.centralizer ((S : Subgroup G) : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact hab y hy u hu
  have hv_c : v ∈ Subgroup.centralizer ((S : Subgroup G) : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact hab y hy v hv
  obtain ⟨n, hn, heq⟩ :=
    S.conj_eq_normalizer_conj_of_mem_centralizer u (↑c)⁻¹ hu_c (by
      have hvv : ((↑c)⁻¹)⁻¹ * u * (↑c)⁻¹ = v := by
        rw [inv_inv, hcu, mul_assoc, mul_inv_cancel, mul_one]
      rw [hvv]; exact hv_c)
  rw [inv_inv, hcu, mul_assoc, mul_inv_cancel, mul_one] at heq
  exact ⟨n⁻¹, Subgroup.inv_mem _ hn, by rw [inv_inv]; exact heq.symm⟩

end Work.BG
