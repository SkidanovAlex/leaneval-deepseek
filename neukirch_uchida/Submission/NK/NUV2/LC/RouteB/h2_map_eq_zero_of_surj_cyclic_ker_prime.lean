import Mathlib
import Submission.NK.NUV2.LC.RouteB.h2_map_zmod_p_sq_eq_zero

namespace NK.NUV2.LC.RouteB

open CategoryTheory Representation groupCohomology Rep

/-!
# The inflation `H²(Q, ℤ/p) → H²(G, ℤ/p)` vanishes for `|ker| = p`

Let `φ : G ↠ Q` be a surjective homomorphism of *finite cyclic* groups whose kernel has exactly `p`
elements (`p` a prime).  The goal of this file is to prove that the pullback ("inflation")

`H²(Q, ℤ/p) → H²(G, ℤ/p)`

with trivial coefficients `ℤ/p` is **zero**.

This generalises `NK.NUV2.LC.RouteB.h2_map_zmod_p_sq_eq_zero`, which treats the special case
`G = ℤ/p²`, `Q = ℤ/p`; the proof there is a cochain computation via the transgression criterion
`NK.Cohomology.mem_coboundaries₂_of_transgression_mem_range`.  The only place where the special
case uses `|G| = p²` is the period computation for the transgression, and it generalises verbatim:
for a cyclic `G` with generator `g`, a `2`-cocycle `z` of the trivial `Q`-representation and
`M = |Q|`, the transgression of the pulled-back cocycle is

`∑_{t < |G|} z (φ (g^t), φ g)`,

whose summands are `M`-periodic because `(φ g)^M = 1`.  Since `|G| = p·M` (the kernel has `p`
elements), the sum is `p` times the sum over one period, hence zero in characteristic `p`.
So the transgression always lies in the range of the norm endomorphism (it is `0`), and the
criterion applies.

## Main result

* `NK.NUV2.LC.RouteB.h2_map_eq_zero_of_surj_cyclic_ker_prime`
-/

section Aux

variable {k : Type} [CommRing k] {G Q : Type} [Group G] [Group Q]

/-- The pullback of a `2`-cocycle of the trivial `Q`-representation to `G` (along a group
homomorphism `φ : G →* Q`) is again a `2`-cocycle.  Since the coefficients are trivial, the
cocycle condition is purely a condition on the group elements and is inherited. -/
lemma pullback_mem_cocycles₂_ofHom (φ : G →* Q)
    (z : groupCohomology.cocycles₂ (Rep.trivial k Q k)) :
    (fun q : G × G => z (φ q.1, φ q.2)) ∈
      groupCohomology.cocycles₂ (Rep.trivial k G k) := by
  rw [groupCohomology.mem_cocycles₂_iff]
  intro a b c
  have h := (groupCohomology.mem_cocycles₂_iff (A := Rep.trivial k Q k) (⇑z)).mp z.2
    (φ a) (φ b) (φ c)
  simp only [map_mul] at h ⊢
  exact h

/-- The pullback of a `2`-cocycle of the trivial `Q`-representation, packaged as a `2`-cocycle of
the trivial `G`-representation. -/
noncomputable def pullbackCocycleOfHom (φ : G →* Q)
    (z : groupCohomology.cocycles₂ (Rep.trivial k Q k)) :
    groupCohomology.cocycles₂ (Rep.trivial k G k) :=
  ⟨fun q => z (φ q.1, φ q.2), pullback_mem_cocycles₂_ofHom φ z⟩

/-- The evaluation of the degree-`2` cochain map of Mathlib's functoriality API. -/
lemma cochainsMap₂_apply_ofHom {A : Rep k Q} {B : Rep k G} (f : G →* Q)
    (φ : Rep.res f A ⟶ B) (z : Q × Q → A) (γ δ : G) :
    (groupCohomology.cochainsMap₂ f φ) z (γ, δ) = φ.hom (z (f γ, f δ)) := rfl

/-- The structural morphism `trivHom` of trivial representations is the identity on coefficients. -/
lemma trivHom_hom_apply (p : ℕ) (φ : G →* Q) (a : NK.BrauerHasse.Coeff p) :
    (NK.BrauerHasse.trivHom (p := p) φ).hom a = a := rfl

variable [Fintype G] [Fintype Q]

/-- **The transgression of a pulled-back `2`-cocycle vanishes.**  The summands are `|Q|`-periodic
because `(φ g)^{|Q|} = 1`, and `|G| = |Q| · p`; the sum is therefore `p` times the sum over one
period, which is zero because the coefficients have characteristic `p`. -/
lemma transgression_pullbackCocycleOfHom_eq_zero (p : ℕ) (hp : (p : k) = 0)
    (hcard : Fintype.card G = Fintype.card Q * p)
    (φ : G →* Q) (g : G) (z : groupCohomology.cocycles₂ (Rep.trivial k Q k)) :
    (∑ t ∈ Finset.range (Fintype.card G),
        (pullbackCocycleOfHom (k := k) φ z) (g ^ t, g)) = 0 := by
  have hper : ∀ t : ℕ, (pullbackCocycleOfHom (k := k) φ z) (g ^ (t + Fintype.card Q), g)
      = (pullbackCocycleOfHom (k := k) φ z) (g ^ t, g) := by
    intro t
    show z (φ (g ^ (t + Fintype.card Q)), φ g) = z (φ (g ^ t), φ g)
    have hpq : (φ g) ^ (Fintype.card Q) = 1 := pow_card_eq_one
    have h1 : φ (g ^ (t + Fintype.card Q)) = φ (g ^ t) := by
      calc φ (g ^ (t + Fintype.card Q)) = φ (g ^ t * g ^ (Fintype.card Q)) := by rw [pow_add]
        _ = φ (g ^ t) * φ (g ^ Fintype.card Q) := by rw [map_mul]
        _ = (φ g) ^ t * (φ g) ^ (Fintype.card Q) := by rw [map_pow, map_pow]
        _ = (φ g) ^ t * 1 := by rw [hpq]
        _ = (φ g) ^ t := by rw [mul_one]
        _ = φ (g ^ t) := by rw [map_pow]
    rw [h1]
  rw [hcard, sum_range_mul_of_periodic (Fintype.card Q) p _ hper]
  have hzero : (p : k) • (∑ t ∈ Finset.range (Fintype.card Q),
      (pullbackCocycleOfHom (k := k) φ z) (g ^ t, g)) = 0 := by
    rw [hp, zero_smul]
  simpa [Nat.cast_smul_eq_nsmul] using hzero

end Aux

/-- Let `φ : G ↠ Q` be a surjective homomorphism of *finite cyclic* groups whose kernel has
exactly `p` elements (`p` a prime).  Then the pullback ("inflation")
`H²(Q, Z/p) → H²(G, Z/p)` with trivial coefficients `Z/p` is zero. -/
theorem h2_map_eq_zero_of_surj_cyclic_ker_prime (p : ℕ) [Fact p.Prime] {G Q : Type} [Group G]
    [Group Q] [Fintype G] [Fintype Q] (hG : IsCyclic G) (φ : G →* Q)
    (hφ : Function.Surjective φ) (hker : Nat.card (MonoidHom.ker φ) = p) :
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
  have hcard : Fintype.card G = Fintype.card Q * p := by
    have hquot : Nat.card (G ⧸ MonoidHom.ker φ) = Nat.card Q :=
      Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective φ hφ).toEquiv
    have hcard' : Nat.card G = Nat.card Q * p := by
      rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (MonoidHom.ker φ), hquot, hker]
    rw [← Nat.card_eq_fintype_card, hcard', Nat.card_eq_fintype_card]
  rw [transgression_pullbackCocycleOfHom_eq_zero p (coeff_natCast_self p) hcard φ g z]
  exact Submodule.zero_mem _

end NK.NUV2.LC.RouteB
