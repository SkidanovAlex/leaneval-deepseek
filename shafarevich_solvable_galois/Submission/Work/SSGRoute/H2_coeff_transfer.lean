import Mathlib
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute

open CategoryTheory

universe u

/-! ## Helper lemmas for the coefficient-ring transfer in degree `2`

Throughout, `A : Rep k G`, `B : Rep k' G` are two representations with the *same* carrier and the
*same* action up to the additive equivalence `e : A.V ≃+ B.V`, which commutes with the action:
`e (A.ρ g a) = B.ρ g (e a)`.

The differentials `d₁₂`, `d₂₃` of the standard complex of inhomogeneous cochains involve only the
action and the additive structure, so `e` induces an additive equivalence of the `2`-cocycles
carrying the `2`-coboundaries onto the `2`-coboundaries.  By `groupCohomology.H2π_eq_zero_iff`
this descends to the second cohomology. -/
namespace H2CoeffTransfer

variable {k k' G : Type u} [CommRing k] [CommRing k'] [Group G]
variable (A : Rep.{u,u,u} k G) (B : Rep.{u,u,u} k' G) (e : A.V ≃+ B.V)

/-- The additive equivalence `e` applied coordinatewise to `G × G`-indexed functions. -/
def eGG : (G × G → A.V) ≃+ (G × G → B.V) := AddEquiv.piCongrRight (fun _ => e)

/-- The additive equivalence `e` applied coordinatewise to `G`-indexed functions. -/
def eG : (G → A.V) ≃+ (G → B.V) := AddEquiv.piCongrRight (fun _ => e)

@[simp] lemma eGG_apply (f : G × G → A.V) (g : G × G) : eGG A B e f g = e (f g) := rfl

@[simp] lemma eG_apply (f : G → A.V) (g : G) : eG A B e f g = e (f g) := rfl

/-- The transfer commutes with the first differential `d₁₂`: `e ∘ d₁₂ = d₁₂ ∘ e`. -/
lemma d12_transfer (he : ∀ (g : G) (a : A.V), e (A.ρ g a) = B.ρ g (e a)) (f : G → A.V) :
    eGG A B e ((groupCohomology.d₁₂ A).hom f) = (groupCohomology.d₁₂ B).hom (eG A B e f) := by
  funext g
  simp only [eGG_apply, eG_apply, groupCohomology.d₁₂_hom_apply, map_add, map_sub]
  rw [he]

/-- `e` carries the `2`-cocycles of `A` onto the `2`-cocycles of `B`. -/
lemma mem_cocycles₂_transfer (he : ∀ (g : G) (a : A.V), e (A.ρ g a) = B.ρ g (e a))
    (f : G × G → A.V) :
    f ∈ groupCohomology.cocycles₂ A ↔ eGG A B e f ∈ groupCohomology.cocycles₂ B := by
  rw [groupCohomology.mem_cocycles₂_iff, groupCohomology.mem_cocycles₂_iff]
  constructor
  · intro h g hh j
    simp only [eGG_apply]
    rw [← map_add, h g hh j, map_add, he]
  · intro h g hh j
    simp only [eGG_apply] at h
    have h1 := h g hh j
    rw [← he] at h1
    simp only [← map_add] at h1
    exact e.injective h1

/-- `e` carries the `2`-coboundaries of `A` onto the `2`-coboundaries of `B`. -/
lemma mem_coboundaries₂_transfer (he : ∀ (g : G) (a : A.V), e (A.ρ g a) = B.ρ g (e a))
    (f : G × G → A.V) :
    f ∈ groupCohomology.coboundaries₂ A ↔ eGG A B e f ∈ groupCohomology.coboundaries₂ B := by
  rw [groupCohomology.coboundaries₂, groupCohomology.coboundaries₂, LinearMap.mem_range,
    LinearMap.mem_range]
  constructor
  · rintro ⟨u, rfl⟩
    exact ⟨eG A B e u, (d12_transfer A B e he u).symm⟩
  · rintro ⟨v, hv⟩
    refine ⟨(eG A B e).symm v, ?_⟩
    apply (eGG A B e).injective
    rw [d12_transfer A B e he, AddEquiv.apply_symm_apply]
    exact hv

/-- The additive equivalence of `2`-cocycle modules induced by `e`. -/
noncomputable def cocEquiv (he : ∀ (g : G) (a : A.V), e (A.ρ g a) = B.ρ g (e a)) :
    groupCohomology.cocycles₂ A ≃+ groupCohomology.cocycles₂ B where
  toFun f := ⟨eGG A B e f, (mem_cocycles₂_transfer A B e he f).mp f.2⟩
  invFun f := ⟨(eGG A B e).symm f, (mem_cocycles₂_transfer A B e he _).mpr (by
    rw [AddEquiv.apply_symm_apply]; exact f.2)⟩
  left_inv f := Subtype.ext ((eGG A B e).symm_apply_apply (f : G × G → A.V))
  right_inv f := Subtype.ext ((eGG A B e).apply_symm_apply (f : G × G → B.V))
  map_add' f g := Subtype.ext ((eGG A B e).map_add (f : G × G → A.V) (g : G × G → A.V))

/-- `cocEquiv` maps the kernel of `H2π A` onto the kernel of `H2π B`. -/
lemma mem_ker_iff (he : ∀ (g : G) (a : A.V), e (A.ρ g a) = B.ρ g (e a))
    (x : groupCohomology.cocycles₂ A) :
    x ∈ (groupCohomology.H2π A).hom.ker ↔
      cocEquiv A B e he x ∈ (groupCohomology.H2π B).hom.ker := by
  rw [LinearMap.mem_ker, LinearMap.mem_ker, groupCohomology.H2π_eq_zero_iff,
    groupCohomology.H2π_eq_zero_iff]
  change ⇑x ∈ groupCohomology.coboundaries₂ A ↔ eGG A B e ⇑x ∈ groupCohomology.coboundaries₂ B
  exact mem_coboundaries₂_transfer A B e he x.1

/-- The kernel of `H2π A` is carried by `cocEquiv` onto the kernel of `H2π B`. -/
lemma map_ker_eq (he : ∀ (g : G) (a : A.V), e (A.ρ g a) = B.ρ g (e a)) :
    AddSubgroup.map (↑(cocEquiv A B e he)) ((groupCohomology.H2π A).hom.ker).toAddSubgroup =
      ((groupCohomology.H2π B).hom.ker).toAddSubgroup := by
  ext x
  constructor
  · intro hx
    rw [AddSubgroup.mem_map] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    exact (mem_ker_iff A B e he y).mp hy
  · intro hx
    rw [AddSubgroup.mem_map]
    refine ⟨(cocEquiv A B e he).symm x, ?_, ?_⟩
    · refine (mem_ker_iff A B e he _).mpr ?_
      rwa [AddEquiv.apply_symm_apply]
    · exact (cocEquiv A B e he).apply_symm_apply x

end H2CoeffTransfer

/-- **Coefficient-ring transfer for `H²`.** Two `G`-representations with the same carrier and the same
action, over two possibly different coefficient rings `k` and `k'` (related by an additive equivalence
`e` commuting with the action), have canonically isomorphic second cohomology `H²(G, ·)`.

This is what lets a class-formation statement proved over `ℤ` (`NK.GlobalCFT.CohomologicalFieldAxiom`,
`NK.CFTLib.fundamentalClassElement`) be read in the `Rep.{0} Coeff G` world (`Coeff = ULift ℤ`) of
`Submission/Work/SSGRoute/PTDefs.lean`; it is used by `Work.SSGRoute.extCor_injective_classesK`.

Route: degree `2` is the case whose low-degree API is in Mathlib —
`groupCohomology.cocycles₂ : Submodule k (G × G → A)` (`= ker (d₂₃ A).hom`),
`groupCohomology.coboundaries₂` (`= range (d₁₂ A).hom`), and
`groupCohomology.H2π : cocycles₂ A ⟶ groupCohomology A 2`, epi with kernel `coboundaries₂ A`
(`groupCohomology.H2π_eq_zero_iff`).  The differentials
`d₁₂ A f g = A.ρ g.1 (f g.2) - f (g.1 * g.2) + f g.1` and `d₂₃` involve no coefficient scalars, so
`f ↦ e ∘ f` is a bijection `cocycles₂ A ≅ cocycles₂ B` carrying `coboundaries₂ A` onto
`coboundaries₂ B`; it induces the quotient isomorphism, and the two `H2π`'s identify
`cocycles₂/coboundaries₂` with `groupCohomology · 2`. -/
theorem H2_coeff_transfer {k k' G : Type u} [CommRing k] [CommRing k'] [Group G]
    (A : Rep.{u,u,u} k G) (B : Rep.{u,u,u} k' G) (e : A.V ≃+ B.V)
    (he : ∀ (g : G) (a : A.V), e (A.ρ g a) = B.ρ g (e a)) :
    Nonempty (groupCohomology A 2 ≃+ groupCohomology B 2) := by
  have hA : Function.Surjective ⇑(groupCohomology.H2π A).hom :=
    (ModuleCat.epi_iff_surjective (groupCohomology.H2π A)).mp inferInstance
  have hB : Function.Surjective ⇑(groupCohomology.H2π B).hom :=
    (ModuleCat.epi_iff_surjective (groupCohomology.H2π B)).mp inferInstance
  exact ⟨(LinearMap.quotKerEquivOfSurjective (groupCohomology.H2π A).hom hA).symm.toAddEquiv.trans
    ((QuotientAddGroup.congr _ _ (H2CoeffTransfer.cocEquiv A B e he)
        (H2CoeffTransfer.map_ker_eq A B e he)).trans
      (LinearMap.quotKerEquivOfSurjective (groupCohomology.H2π B).hom hB).toAddEquiv)⟩

end Work.SSGRoute
