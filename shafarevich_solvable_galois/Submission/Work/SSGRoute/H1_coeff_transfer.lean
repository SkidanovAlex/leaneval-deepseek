import Mathlib
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute

open CategoryTheory

/-! ## Helper lemmas for the coefficient-ring transfer in degree `1`

Throughout, `A : Rep k G`, `B : Rep k' G` are two representations with the *same* carrier and the
*same* action up to the additive equivalence `e : A.V ≃+ B.V`, which commutes with the action:
`e (A.ρ g a) = B.ρ g (e a)`.

The differentials `d₀₁`, `d₁₂` of the standard complex of inhomogeneous cochains involve only the
action and the additive structure, so `e` induces an additive equivalence of the `1`-cocycles
carrying the `1`-coboundaries onto the `1`-coboundaries.  By `groupCohomology.H1π_eq_zero_iff`
this descends to the first cohomology. -/
namespace H1CoeffTransfer

variable {k k' G : Type} [CommRing k] [CommRing k'] [Group G]
variable (A : Rep.{0} k G) (B : Rep.{0} k' G) (e : A.V ≃+ B.V)

/-- The additive equivalence `e` applied coordinatewise to `G`-indexed functions. -/
def eG : (G → A.V) ≃+ (G → B.V) := AddEquiv.piCongrRight (fun _ => e)

/-- The additive equivalence `e` applied coordinatewise to `G × G`-indexed functions. -/
def eGG : (G × G → A.V) ≃+ (G × G → B.V) := AddEquiv.piCongrRight (fun _ => e)

@[simp] lemma eG_apply (f : G → A.V) (g : G) : eG A B e f g = e (f g) := rfl

@[simp] lemma eGG_apply (f : G × G → A.V) (g : G × G) : eGG A B e f g = e (f g) := rfl

/-- The transfer commutes with the zeroth differential `d₀₁`: `e ∘ d₀₁ = d₀₁ ∘ e`. -/
lemma d01_transfer (he : ∀ (g : G) (a : A.V), e (A.ρ g a) = B.ρ g (e a)) (x : A.V) :
    eG A B e ((groupCohomology.d₀₁ A).hom x) = (groupCohomology.d₀₁ B).hom (e x) := by
  funext g
  simp only [eG_apply, groupCohomology.d₀₁_hom_apply, map_sub, he]

/-- The transfer commutes with the first differential `d₁₂`: `e ∘ d₁₂ = d₁₂ ∘ e`. -/
lemma d12_transfer (he : ∀ (g : G) (a : A.V), e (A.ρ g a) = B.ρ g (e a)) (f : G → A.V) :
    eGG A B e ((groupCohomology.d₁₂ A).hom f) = (groupCohomology.d₁₂ B).hom (eG A B e f) := by
  funext g
  simp only [eGG_apply, eG_apply, groupCohomology.d₁₂_hom_apply, map_add, map_sub]
  rw [he]

/-- `e` carries the `1`-cocycles of `A` onto the `1`-cocycles of `B`. -/
lemma mem_cocycles₁_transfer (he : ∀ (g : G) (a : A.V), e (A.ρ g a) = B.ρ g (e a))
    (f : G → A.V) :
    f ∈ groupCohomology.cocycles₁ A ↔ eG A B e f ∈ groupCohomology.cocycles₁ B := by
  rw [groupCohomology.mem_cocycles₁_iff, groupCohomology.mem_cocycles₁_iff]
  constructor
  · intro h g hh
    simp only [eG_apply]
    rw [h g hh, map_add, he]
  · intro h g hh
    have h1 := h g hh
    simp only [eG_apply] at h1
    rw [← he] at h1
    simp only [← map_add] at h1
    exact e.injective h1

/-- `e` carries the `1`-coboundaries of `A` onto the `1`-coboundaries of `B`. -/
lemma mem_coboundaries₁_transfer (he : ∀ (g : G) (a : A.V), e (A.ρ g a) = B.ρ g (e a))
    (f : G → A.V) :
    f ∈ groupCohomology.coboundaries₁ A ↔ eG A B e f ∈ groupCohomology.coboundaries₁ B := by
  rw [groupCohomology.coboundaries₁, groupCohomology.coboundaries₁, LinearMap.mem_range,
    LinearMap.mem_range]
  constructor
  · rintro ⟨u, rfl⟩
    exact ⟨e u, (d01_transfer A B e he u).symm⟩
  · rintro ⟨v, hv⟩
    refine ⟨e.symm v, ?_⟩
    apply (eG A B e).injective
    rw [d01_transfer A B e he, AddEquiv.apply_symm_apply]
    exact hv

/-- The additive equivalence of `1`-cocycle modules induced by `e`. -/
noncomputable def cocEquiv (he : ∀ (g : G) (a : A.V), e (A.ρ g a) = B.ρ g (e a)) :
    groupCohomology.cocycles₁ A ≃+ groupCohomology.cocycles₁ B where
  toFun f := ⟨eG A B e f, (mem_cocycles₁_transfer A B e he f).mp f.2⟩
  invFun f := ⟨(eG A B e).symm f, (mem_cocycles₁_transfer A B e he _).mpr (by
    rw [AddEquiv.apply_symm_apply]; exact f.2)⟩
  left_inv f := Subtype.ext ((eG A B e).symm_apply_apply (f : G → A.V))
  right_inv f := Subtype.ext ((eG A B e).apply_symm_apply (f : G → B.V))
  map_add' f g := Subtype.ext ((eG A B e).map_add (f : G → A.V) (g : G → A.V))

/-- `cocEquiv` maps the kernel of `H1π A` onto the kernel of `H1π B`. -/
lemma mem_ker_iff (he : ∀ (g : G) (a : A.V), e (A.ρ g a) = B.ρ g (e a))
    (x : groupCohomology.cocycles₁ A) :
    x ∈ (groupCohomology.H1π A).hom.ker ↔
      cocEquiv A B e he x ∈ (groupCohomology.H1π B).hom.ker := by
  rw [LinearMap.mem_ker, LinearMap.mem_ker, groupCohomology.H1π_eq_zero_iff,
    groupCohomology.H1π_eq_zero_iff]
  change ⇑x ∈ groupCohomology.coboundaries₁ A ↔ eG A B e ⇑x ∈ groupCohomology.coboundaries₁ B
  exact mem_coboundaries₁_transfer A B e he x.1

/-- The kernel of `H1π A` is carried by `cocEquiv` onto the kernel of `H1π B`. -/
lemma map_ker_eq (he : ∀ (g : G) (a : A.V), e (A.ρ g a) = B.ρ g (e a)) :
    AddSubgroup.map (↑(cocEquiv A B e he)) ((groupCohomology.H1π A).hom.ker).toAddSubgroup =
      ((groupCohomology.H1π B).hom.ker).toAddSubgroup := by
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

end H1CoeffTransfer

/-- **Coefficient-ring transfer for `H¹`.** Two `G`-representations with the same carrier and the
same action, over two possibly different coefficient rings `k` and `k'` (related by an additive
equivalence `e` commuting with the action), have canonically isomorphic first cohomology `H¹(G, ·)`.
Degree-`1` companion of `Work.SSGRoute.H2_coeff_transfer`, proved by the same route: `e` induces an
additive equivalence `cocycles₁ A ≃+ cocycles₁ B` carrying `coboundaries₁ A` onto
`coboundaries₁ B`, and `groupCohomology.H1π` identifies `cocycles₁/coboundaries₁` with
`groupCohomology · 1`. -/
theorem H1_coeff_transfer {k k' G : Type} [CommRing k] [CommRing k'] [Group G]
    (A : Rep.{0} k G) (B : Rep.{0} k' G) (e : A.V ≃+ B.V)
    (he : ∀ (g : G) (a : A.V), e (A.ρ g a) = B.ρ g (e a)) :
    Nonempty (groupCohomology A 1 ≃+ groupCohomology B 1) := by
  have hA : Function.Surjective ⇑(groupCohomology.H1π A).hom :=
    (ModuleCat.epi_iff_surjective (groupCohomology.H1π A)).mp inferInstance
  have hB : Function.Surjective ⇑(groupCohomology.H1π B).hom :=
    (ModuleCat.epi_iff_surjective (groupCohomology.H1π B)).mp inferInstance
  exact ⟨(LinearMap.quotKerEquivOfSurjective (groupCohomology.H1π A).hom hA).symm.toAddEquiv.trans
    ((QuotientAddGroup.congr _ _ (H1CoeffTransfer.cocEquiv A B e he)
        (H1CoeffTransfer.map_ker_eq A B e he)).trans
      (LinearMap.quotKerEquivOfSurjective (groupCohomology.H1π B).hom hB).toAddEquiv)⟩

end Work.SSGRoute
