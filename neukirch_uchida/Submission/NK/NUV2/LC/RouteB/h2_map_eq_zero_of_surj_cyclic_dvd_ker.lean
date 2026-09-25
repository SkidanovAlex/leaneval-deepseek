import Mathlib
import Submission.NK.NUV2.LC.RouteB.h2_map_zmod_p_sq_eq_zero
import Submission.NK.NUV2.LC.RouteB.h2_map_eq_zero_of_surj_cyclic_ker_prime

namespace NK.NUV2.LC.RouteB

open CategoryTheory Representation groupCohomology Rep

/-!
# The inflation `H²(Q, ℤ/p) → H²(G, ℤ/p)` vanishes when `p ∣ |ker|` and `G` is cyclic

Let `φ : G ↠ Q` be a surjective homomorphism of finite cyclic groups and suppose that `p` divides
the order of the kernel.  Then the pullback ("inflation")

`H²(Q, ℤ/p) ⟶ H²(G, ℤ/p)`

with trivial coefficients `ℤ/p` is **zero**.

This generalises `NK.NUV2.LC.RouteB.h2_map_eq_zero_of_surj_cyclic_ker_prime`, which treats the
case `|ker φ| = p`.  The proof is the same cochain computation via the transgression criterion
`NK.Cohomology.mem_coboundaries₂_of_transgression_mem_range`: for a cyclic `G` with generator `g`,
a `2`-cocycle `z` of the trivial `Q`-representation and `M = |Q|`, the transgression of the
pulled-back cocycle is

`∑_{t < |G|} z (φ (g^t), φ g)`,

whose summands are `M`-periodic because `(φ g)^M = 1`.  Since `|G| = |ker φ| · M`, the sum equals
`|ker φ|` times the sum over one period, hence vanishes in characteristic `p` because `p` divides
`|ker φ|`.  Thus the transgression is `0`, and the criterion applies.

## Main result

* `NK.NUV2.LC.RouteB.h2_map_eq_zero_of_surj_cyclic_dvd_ker`
-/

/-- Let `φ : G ↠ Q` be a surjective homomorphism of finite groups with `G` *cyclic* and
`p ∣ Nat.card (ker φ)`.  Then the pullback ("inflation") `H²(Q, Z/p) → H²(G, Z/p)` with trivial
coefficients `Z/p` is zero. -/
theorem h2_map_eq_zero_of_surj_cyclic_dvd_ker (p : ℕ) [Fact p.Prime] {G Q : Type} [Group G]
    [Group Q] [Fintype G] [Fintype Q] (hG : IsCyclic G) (φ : G →* Q)
    (hφ : Function.Surjective φ) (hker : p ∣ Nat.card (MonoidHom.ker φ)) :
    ∀ x : NK.BrauerHasse.H2 p Q, (NK.BrauerHasse.H2.map (p := p) φ).hom x = 0 := by
  intro x
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := G)
  -- Surjectivity of the projection onto the `2`-cocycles.
  obtain ⟨z, hz⟩ := (ModuleCat.epi_iff_surjective
      (groupCohomology.H2π (Rep.trivial (NK.BrauerHasse.Coeff p) Q
        (NK.BrauerHasse.Coeff p)))).mp
    (inferInstance : Epi (groupCohomology.H2π (Rep.trivial (NK.BrauerHasse.Coeff p)
      Q (NK.BrauerHasse.Coeff p)))) x
  rw [← hz]
  -- Compatibility of the projection with the pullback.
  have hcomp : (groupCohomology.map φ (NK.BrauerHasse.trivHom φ) 2)
        (groupCohomology.H2π (Rep.trivial (NK.BrauerHasse.Coeff p) Q
          (NK.BrauerHasse.Coeff p)) z)
      = groupCohomology.H2π (Rep.trivial (NK.BrauerHasse.Coeff p) G (NK.BrauerHasse.Coeff p))
          ((groupCohomology.mapCocycles₂ φ (NK.BrauerHasse.trivHom φ)) z) :=
    groupCohomology.H2π_comp_map_apply φ (NK.BrauerHasse.trivHom φ) z
  rw [NK.BrauerHasse.H2.map, hcomp, groupCohomology.H2π_eq_zero_iff,
    groupCohomology.coe_mapCocycles₂]
  -- The cochain map is the explicit pullback of the cocycle.
  have hval : (groupCohomology.cochainsMap₂ φ (NK.BrauerHasse.trivHom φ)) (⇑z)
      = (⇑(pullbackCocycleOfHom (k := NK.BrauerHasse.Coeff p) φ z) :
          G × G → NK.BrauerHasse.Coeff p) := by
    funext q
    obtain ⟨a, b⟩ := q
    rw [show (groupCohomology.cochainsMap₂ φ (NK.BrauerHasse.trivHom φ)) (⇑z) (a, b)
        = (NK.BrauerHasse.trivHom (p := p) φ).hom (z (φ a, φ b)) from
        cochainsMap₂_apply_ofHom φ (NK.BrauerHasse.trivHom φ) (⇑z) a b]
    rfl
  rw [hval]
  -- The pulled-back cocycle is a coboundary by the transgression criterion.
  refine NK.Cohomology.mem_coboundaries₂_of_transgression_mem_range g hg
    (Rep.trivial (NK.BrauerHasse.Coeff p) G (NK.BrauerHasse.Coeff p))
    (pullbackCocycleOfHom (k := NK.BrauerHasse.Coeff p) φ z) ?_
  -- The cardinality of the kernel is invertible to `0` in the coefficients `Z/p`.
  have hm : ((Nat.card (MonoidHom.ker φ) : NK.BrauerHasse.Coeff p)) = 0 := by
    obtain ⟨c, hc⟩ := hker
    rw [hc, Nat.cast_mul, coeff_natCast_self p, zero_mul]
  -- `|G| = |Q| · |ker φ|`.
  have hcard : Fintype.card G = Fintype.card Q * Nat.card (MonoidHom.ker φ) := by
    have hquot : Nat.card (G ⧸ MonoidHom.ker φ) = Nat.card Q :=
      Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective φ hφ).toEquiv
    have hcard' : Nat.card G = Nat.card Q * Nat.card (MonoidHom.ker φ) := by
      rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (MonoidHom.ker φ), hquot]
    rw [← Nat.card_eq_fintype_card, hcard', Nat.card_eq_fintype_card]
  rw [transgression_pullbackCocycleOfHom_eq_zero (Nat.card (MonoidHom.ker φ)) hm hcard φ g z]
  exact Submodule.zero_mem _

end NK.NUV2.LC.RouteB
