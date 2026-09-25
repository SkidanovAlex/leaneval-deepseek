import Mathlib
import Submission.Work.CFT.IdeleClassGroup.TateBasic

/-!
# The zeroth Tate cohomology is the invariants modulo the norms

For a finite group `G` and a `ℤ`-representation `A`, the zeroth Tate cohomology
`Ĥ⁰(G, A)` is the homology in degree `0` of the Tate complex.  The Tate complex is obtained
by connecting the inhomogeneous chain complex with the inhomogeneous cochain complex along
the norm map, so its degree `0` homology is the homology of the short complex
`A --N--> A --d₀₁--> Fun(G, A)`, where `N = ∑_{g : G} g` is the norm.  Its homology is
`ker(d₀₁) / im(N)`, and `ker(d₀₁)` is precisely the `G`-invariants while `im(N)` is the
subgroup of norms, giving `Ĥ⁰(G, A) ≃ A^G / N A`.

## Main results

* `Work.CFT.IdeleClassGroup.tateCohomology_zero_iso`
-/

namespace Work.CFT.IdeleClassGroup

open CategoryTheory

variable {G : Type} [Group G] [Fintype G]

/-- The short complex `A --N--> A --d₀₁--> Fun(G, A)` whose homology is `Ĥ⁰(G, A)`. -/
noncomputable def tateZeroComplex (A : Rep ℤ G) : ShortComplex (ModuleCat ℤ) :=
  ShortComplex.mk A.norm.toModuleCatHom (groupCohomology.d₀₁ A) (Rep.norm_comp_d_eq_zero A)

/-- The connecting map `tateNorm` is the norm map, conjugated by the isomorphisms identifying
the `0`-th chains and cochains with `A`. -/
lemma tateNorm_sq (A : Rep ℤ G) :
    (groupHomology.chainsIso₀ A).hom ≫ A.norm.toModuleCatHom =
      A.tateNorm ≫ (groupCohomology.cochainsIso₀ A).hom := by
  simp [Rep.tateNorm]

/-- The comparison isomorphism between the Tate complex in degrees `-1, 0, 1` and the short
complex `A --N--> A --d₀₁--> Fun(G, A)`. -/
noncomputable def tateZeroIso (A : Rep ℤ G) :
    (tateComplex A).sc' (-1) 0 1 ≅ tateZeroComplex A :=
  ShortComplex.isoMk (groupHomology.chainsIso₀ A) (groupCohomology.cochainsIso₀ A)
    (groupCohomology.cochainsIso₁ A)
    (by change (groupHomology.chainsIso₀ A).hom ≫ A.norm.toModuleCatHom =
        A.tateNorm ≫ (groupCohomology.cochainsIso₀ A).hom
        exact tateNorm_sq A)
    (groupCohomology.comp_d₀₁_eq A)

/-- `Ĥ⁰(G, A)` is computed as the homology of the short complex `A --N--> A --d₀₁--> Fun(G, A)`. -/
noncomputable def tateCohomology_zero_iso_shortComplex (A : Rep ℤ G) :
    tateCohomology A 0 ≅ (tateZeroComplex A).homology :=
  (tateComplex A).homologyIsoSc' (-1) 0 1 (by simp) (by simp) ≪≫
    ShortComplex.homologyMapIso (tateZeroIso A)

set_option linter.style.haveILetI false in
/-- **Zeroth Tate cohomology = invariants modulo norms.**  For a `ℤ`-representation `A` of a
finite group `G`, the zeroth Tate cohomology group `Ĥ⁰(G, A)` (Mathlib's
`tateCohomology A 0`, the homology of the Tate complex in degree `0`) is the quotient of the
`G`-invariants by the image of the norm endomorphism `N = ∑_{g : G} g`. -/
lemma tateCohomology_zero_iso {G : Type} [Group G] [Fintype G] (A : Rep ℤ G) :
    Nonempty ((tateCohomology A 0 : Type) ≃+ (invariants A ⧸ norms A)) := by
  -- local instances pinning the `ℤ`-module structures to those carried by the objects
  letI : Module ℤ A.V := A.hV2
  letI : Module ℤ (G → A.V) := (tateZeroComplex A).X₃.isModule
  letI : Module ℤ ↥((tateZeroComplex A).g.hom.ker) := ((tateZeroComplex A).g.hom.ker).module
  letI : Module ℤ (↥((tateZeroComplex A).g.hom.ker) ⧸
      (tateZeroComplex A).moduleCatToCycles.range) :=
    ((tateZeroComplex A).moduleCatLeftHomologyData.H).isModule
  -- the kernel of `d₀₁` is the subgroup of invariants
  have hKmem : ∀ x : A.V, x ∈ (tateZeroComplex A).g.hom.ker ↔ ∀ g : G, A.ρ g x = x := by
    intro x
    rw [show (tateZeroComplex A).g.hom.ker = (groupCohomology.d₀₁ A).hom.ker from rfl,
      groupCohomology.d₀₁_ker_eq_invariants]
    exact Representation.mem_invariants A.ρ x
  -- the underlying linear map of the norm is the norm map of the representation
  have hnorm : ∀ x : A.V, A.norm.toModuleCatHom.hom x = normMap A x := by
    intro x
    have h : A.norm.toModuleCatHom.hom x = A.norm.hom x := rfl
    rw [h, Rep.norm_apply]
    simp only [normMap_apply, Representation.norm]
    rw [LinearMap.sum_apply]
  have hN : ∀ y : ↥(tateZeroComplex A).X₁,
      ((tateZeroComplex A).moduleCatToCycles y).1 = normMap A y := by
    intro y
    have h1 : ((tateZeroComplex A).moduleCatToCycles y).1 =
        A.norm.toModuleCatHom.hom y := rfl
    rw [h1]
    exact hnorm y
  -- the additive map from the cycles to the invariants
  let inc : ↥((tateZeroComplex A).g.hom.ker) →+ ↥(invariants A) :=
    { toFun := fun x => ⟨x.1, (mem_invariants A x.1).mpr ((hKmem x.1).mp x.2)⟩
      map_zero' := Subtype.ext rfl
      map_add' := fun x y => Subtype.ext rfl }
  let Φ : ↥((tateZeroComplex A).g.hom.ker) →+ (↥(invariants A) ⧸ norms A) :=
    (QuotientAddGroup.mk' (norms A)).comp inc
  have hsurj : Function.Surjective Φ := by
    intro z
    obtain ⟨y, rfl⟩ := QuotientAddGroup.mk'_surjective (norms A) z
    refine ⟨⟨y.1, (hKmem y.1).mpr y.2⟩, ?_⟩
    show QuotientAddGroup.mk' (norms A) (inc ⟨y.1, _⟩) = QuotientAddGroup.mk' (norms A) y
    rw [show inc ⟨y.1, _⟩ = y from Subtype.ext rfl]
  -- the kernel of `Φ` is exactly the image of the norm
  have hker : Φ.ker = ((tateZeroComplex A).moduleCatToCycles.range).toAddSubgroup := by
    ext x
    rw [AddMonoidHom.mem_ker, Submodule.mem_toAddSubgroup]
    have hx : Φ x = QuotientAddGroup.mk' (norms A) (inc x) := rfl
    rw [hx, QuotientAddGroup.mk'_apply, QuotientAddGroup.eq_zero_iff, norms,
      AddSubgroup.mem_comap, AddMonoidHom.mem_range, LinearMap.mem_range]
    constructor
    · rintro ⟨y, hy⟩
      exact ⟨y, Subtype.ext (by rw [hN y, hy]; rfl)⟩
    · rintro ⟨y, hy⟩
      refine ⟨y, ?_⟩
      rw [← hN y]
      exact congrArg Subtype.val hy
  have e2 : (↥((tateZeroComplex A).g.hom.ker) ⧸
        ((tateZeroComplex A).moduleCatToCycles.range).toAddSubgroup)
      ≃+ (↥(invariants A) ⧸ norms A) :=
    hker ▸ QuotientAddGroup.quotientKerEquivOfSurjective Φ hsurj
  have e1 := ((tateCohomology_zero_iso_shortComplex A ≪≫ (tateZeroComplex A).moduleCatHomologyIso ≪≫
      eqToIso (ShortComplex.moduleCatLeftHomologyData_H (tateZeroComplex A))).toLinearEquiv.toAddEquiv)
  exact ⟨e1.trans e2⟩

end Work.CFT.IdeleClassGroup
