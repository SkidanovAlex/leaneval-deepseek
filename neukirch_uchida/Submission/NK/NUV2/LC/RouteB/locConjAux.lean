import Mathlib
import Submission.NK.NUV2.LC.RouteB.Defs
import Submission.NK.NUV2.LC.conjTransport

/-!
# Auxiliaries for the conjugation invariance of the localisation at a place

This file contains, sorry-free,

* `NK.NUV2.LC.RouteB.H2_map_conj_eq_id` — **inner automorphisms act trivially on the second
  cohomology with trivial coefficients**: for a group `G`, an element `t : G` and any `p`,
  `H2.map (MulAut.conj t).toMonoidHom = 𝟙 (H2 p G)`.  The proof exhibits the explicit coboundary
  `y(g) = Z(t,g) - Z(tgt⁻¹,t)` for a 2-cocycle `Z`;
* `NK.NUV2.LC.RouteB.OverFinitePrime.instSMul` — the action of `Gal(K'/K)` on the places of `K'`
  over a finite prime of `K`, by transport of the action on valuation subrings (the restriction of a
  conjugate place to `K` is unchanged);
* `NK.NUV2.LC.RouteB.conjLevel_eq_self` — **every finite Galois level is stable under
  conjugation**: `conjLevel σ L = L` for every `σ : Gal(K'/K)`, because `K'/L` is normal.

These are the inputs of the comparison `NK.NUV2.LC.RouteB.loc_smul_eq_zero_iff` (the localisation
at `v • A` vanishes if and only if the localisation at `A` vanishes).
-/

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option linter.unusedVariables false

open CategoryTheory
open scoped Pointwise

namespace NK.NUV2.LC.RouteB

open NK.BrauerHasse

universe u

/-! ## The triviality of the conjugation action on `H²(·, Z/p)` with trivial coefficients -/

/-- The differential `d₁₂` on 1-cochains, for a representation with trivial action. -/
lemma d₁₂_apply_of_isTrivial {k : Type u} [CommRing k] {G : Type u} [Group G]
    (A : Rep k G) [A.IsTrivial] (f : G → A.V) (g h : G) :
    (groupCohomology.d₁₂ A).hom f (g, h) = f h - f (g * h) + f g := by
  rw [groupCohomology.d₁₂_hom_apply]
  rw [show A.ρ g (f h) = f h from Representation.isTrivial_apply A.ρ g (f h)]

/-- The cocycle identity in the form used below: for a 2-cocycle `Z` with trivial coefficients,
`Z(x*y, j) + Z(x,y) = Z(y,j) + Z(x, y*j)`. -/
lemma cocycle_apply {k : Type u} [CommRing k] {G : Type u} [Group G]
    (A : Rep k G) [A.IsTrivial] (z : groupCohomology.cocycles₂ A) (x y j : G) :
    z (x * y, j) + z (x, y) = z (y, j) + z (x, y * j) := by
  have h := (groupCohomology.mem_cocycles₂_iff (A := A) ⇑z).mp z.2 x y j
  rwa [show A.ρ x (z (y, j)) = z (y, j) from Representation.isTrivial_apply A.ρ x (z (y, j))]
    at h

/-- **The explicit coboundary.**  For a group `G`, an element `t : G` and a 2-cocycle `Z` of `G`
with coefficients in a module with trivial action, the 1-cochain
`y(g) = Z(t,g) - Z(tgt⁻¹, t)` satisfies `d₁₂ y = Z - Z ∘ (c_t × c_t)`. -/
lemma d₁₂_cocycle_conj {k : Type u} [CommRing k] {G : Type u} [Group G]
    (A : Rep k G) [A.IsTrivial] (t : G) (z : groupCohomology.cocycles₂ A) :
    (groupCohomology.d₁₂ A).hom (fun g => z (t, g) - z (t * g * t⁻¹, t))
      = (⇑z : G × G → A.V) - (fun q : G × G => z (t * q.1 * t⁻¹, t * q.2 * t⁻¹)) := by
  funext q
  obtain ⟨g, h⟩ := q
  have e1 : z (t, g * h) = z (t * g, h) + z (t, g) - z (g, h) := by
    have h1 := cocycle_apply A z t g h
    rw [eq_sub_iff_add_eq, add_comm (z (t, g * h))]
    exact h1.symm
  have e2 : z (t * g, h) = z (t, h) + z (t * g * t⁻¹, t * h) - z (t * g * t⁻¹, t) := by
    have h2 := cocycle_apply A z (t * g * t⁻¹) t h
    rw [show t * g * t⁻¹ * t = t * g from by group] at h2
    rw [eq_sub_iff_add_eq]
    exact h2
  have e3 : z (t * (g * h) * t⁻¹, t)
      = z (t * h * t⁻¹, t) + z (t * g * t⁻¹, t * h) - z (t * g * t⁻¹, t * h * t⁻¹) := by
    have h3 := cocycle_apply A z (t * g * t⁻¹) (t * h * t⁻¹) t
    rw [show t * g * t⁻¹ * (t * h * t⁻¹) = t * (g * h) * t⁻¹ from by group,
      show t * h * t⁻¹ * t = t * h from by group] at h3
    rw [eq_sub_iff_add_eq]
    exact h3
  rw [d₁₂_apply_of_isTrivial, Pi.sub_apply]
  dsimp only
  rw [e1, e2, e3]
  abel

/-- The value of `mapCocycles₂` on the trivial coefficients: `(Z ∘ (f × f))(g,h) = Z(f g, f h)`. -/
lemma coe_mapCocycles₂_triv {p : ℕ} {G : Type u} [Group G] (f : G →* G)
    (z : groupCohomology.cocycles₂ (Rep.trivial (Coeff.{u} p) G (Coeff.{u} p))) :
    ⇑(groupCohomology.mapCocycles₂ f (trivHom f) z)
      = fun q : G × G => z (f q.1, f q.2) := by
  funext q
  rw [groupCohomology.coe_mapCocycles₂]
  rfl

/-- **Inner automorphisms act trivially on `H²(·, Z/p)` with trivial coefficients.** -/
theorem H2_map_conj_eq_id (p : ℕ) {G : Type u} [Group G] (t : G) :
    H2.map (MulAut.conj t).toMonoidHom = 𝟙 (H2 p G) := by
  classical
  set A : Rep (Coeff.{u} p) G := Rep.trivial (Coeff.{u} p) G (Coeff.{u} p) with hA
  have key : ∀ z : groupCohomology.cocycles₂ A,
      ⇑(groupCohomology.mapCocycles₂ (MulAut.conj t).toMonoidHom
          (trivHom (MulAut.conj t).toMonoidHom) z) - ⇑z
        ∈ groupCohomology.coboundaries₂ A := by
    intro z
    rw [groupCohomology.coboundaries₂, LinearMap.mem_range]
    refine ⟨fun g => z (t * g * t⁻¹, t) - z (t, g), ?_⟩
    have hmain := d₁₂_cocycle_conj A t z
    rw [show (fun g => z (t * g * t⁻¹, t) - z (t, g))
        = -(fun g => z (t, g) - z (t * g * t⁻¹, t)) from by
      funext g; simp only [Pi.neg_apply]; abel]
    rw [map_neg, hmain]
    rw [coe_mapCocycles₂_triv]
    ext q
    obtain ⟨g, h⟩ := q
    simp only [Pi.sub_apply, Pi.neg_apply]
    rw [show (MulEquiv.toMonoidHom (MulAut.conj t)) g = t * g * t⁻¹ from MulAut.conj_apply t g,
      show (MulEquiv.toMonoidHom (MulAut.conj t)) h = t * h * t⁻¹ from MulAut.conj_apply t h]
    exact congrArg ULift.down (by abel)
  rw [H2.map]
  apply (cancel_epi (groupCohomology.H2π A)).mp
  rw [show groupCohomology.H2π A ≫
        groupCohomology.map (MulAut.conj t).toMonoidHom
          (trivHom (MulAut.conj t).toMonoidHom) 2 =
      groupCohomology.mapCocycles₂ (MulAut.conj t).toMonoidHom
        (trivHom (MulAut.conj t).toMonoidHom) ≫ groupCohomology.H2π A from
    groupCohomology.H2π_comp_map _ _,
    Category.comp_id]
  apply ModuleCat.hom_ext
  ext z
  rw [ModuleCat.comp_apply]
  exact (groupCohomology.H2π_eq_iff (A := A) _ z).mpr (key z)

/-! ## The action of `Gal(K'/K)` on the places over a finite prime -/

/-- The action of `Gal(K'/K)` on the places of `K'` over a finite prime of `K`: the conjugate of a
place over a finite prime is again over a finite prime, since conjugation does not change the
restriction to `K`. -/
instance instSMulOverFinitePrime (K K' : Type u) [Field K] [NumberField K] [Field K']
    [Algebra K K'] [IsSepClosure K K'] : SMul Gal(K'/K) (OverFinitePrime K K') where
  smul v A := ⟨v • A.1, by rw [NK.LocalDecomposition.comap_smul]; exact A.2⟩

lemma smul_OverFinitePrime_val {K K' : Type u} [Field K] [NumberField K] [Field K']
    [Algebra K K'] [IsSepClosure K K'] (v : Gal(K'/K)) (A : OverFinitePrime K K') :
    (v • A).1 = v • A.1 := rfl

/-! ## Every finite Galois level is stable under conjugation -/

/-- **Every finite Galois level is `Gal(K'/K)`-stable**: `conjLevel σ L = L` for every
`σ : Gal(K'/K)`, since the fixing subgroup `Gal(K'/L)` is normal in `Gal(K'/K)` (`L/K` is Galois)
and the Galois correspondence is injective on (closed) fixing subgroups. -/
lemma conjLevel_eq_self {K K' : Type} [Field K] [Field K'] [Algebra K K'] [IsSepClosure K K']
    (L : FiniteGaloisIntermediateField K K') (σ : Gal(K'/K)) :
    NK.NUV2.LC.conjLevel σ L = L := by
  apply FiniteGaloisIntermediateField.val_injective
  show L.toIntermediateField.map σ.toAlgHom = L.toIntermediateField
  have hnorm : L.toIntermediateField.fixingSubgroup.Normal := inferInstance
  have hfix : (L.toIntermediateField.map σ.toAlgHom).fixingSubgroup =
      L.toIntermediateField.fixingSubgroup := by
    rw [IsGalois.map_fixingSubgroup]
    show L.toIntermediateField.fixingSubgroup.map (MulAut.conj σ).toMonoidHom
        = L.toIntermediateField.fixingSubgroup
    apply le_antisymm
    · intro x hx
      obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
      show σ * y * σ⁻¹ ∈ L.toIntermediateField.fixingSubgroup
      exact hnorm.conj_mem' y hy σ⁻¹
    · intro x hx
      have h : σ⁻¹ * x * σ ∈ L.toIntermediateField.fixingSubgroup := hnorm.conj_mem' x hx σ
      refine Subgroup.mem_map.mpr ⟨σ⁻¹ * x * σ, h, ?_⟩
      show (MulAut.conj σ) (σ⁻¹ * x * σ) = x
      rw [MulAut.conj_apply]
      group
  rw [← InfiniteGalois.fixedField_fixingSubgroup (L.toIntermediateField.map σ.toAlgHom),
    hfix, InfiniteGalois.fixedField_fixingSubgroup L.toIntermediateField]

end NK.NUV2.LC.RouteB
