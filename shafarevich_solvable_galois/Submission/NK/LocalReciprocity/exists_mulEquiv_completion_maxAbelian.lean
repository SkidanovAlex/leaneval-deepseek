import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Combinatorics.Quiver.ReflQuiver
import Mathlib.FieldTheory.Galois.Profinite
import Mathlib.Topology.Algebra.Category.ProfiniteGrp.Completion
import Submission.NK.LocalReciprocity.exists_levelMap_normGroup_le

universe u v

namespace NK.LocalReciprocity

open scoped Classical commutatorElement
open CategoryTheory

set_option maxHeartbeats 1000000

noncomputable section

variable {F : Type u} {F' : Type v} [Field F] [Field F'] [Algebra F F'] [IsGalois F F']

/-- The underlying group of the profinite completion of `Fˣ`. -/
abbrev unitsCompletion : Type u :=
  ((ProfiniteGrp.ProfiniteCompletion.completion (GrpCat.of Fˣ)).toProfinite.toTop)

/-- The projective limit of the finite Galois levels of `F^{ab}/F`. -/
abbrev levelLimit : Type v :=
  ((ProfiniteGrp.limit (InfiniteGalois.asProfiniteGaloisGroupFunctor F
    (maxAbelianSubext F F'))).toProfinite.toTop)

/-- The component of an element of the profinite completion of `Fˣ` in the finite quotient
`Fˣ ⧸ N`. -/
def completionProj (N : FiniteIndexNormalSubgroup Fˣ) (x : unitsCompletion (F := F)) :
    Fˣ ⧸ N.toSubgroup := x.1 N

@[simp]
theorem completionProj_one (N : FiniteIndexNormalSubgroup Fˣ) :
    completionProj N (1 : unitsCompletion (F := F)) = 1 := rfl

@[simp]
theorem completionProj_mul (N : FiniteIndexNormalSubgroup Fˣ) (x y : unitsCompletion (F := F)) :
    completionProj N (x * y) = completionProj N x * completionProj N y := rfl

/-- The defining property of an element of the profinite completion: the components are compatible
with the maps of the completion diagram. -/
theorem completionProj_compat (x : unitsCompletion (F := F))
    {N₁ N₂ : FiniteIndexNormalSubgroup Fˣ} (f : N₁ ⟶ N₂) :
    (ProfiniteGrp.ProfiniteCompletion.diagram (GrpCat.of Fˣ)).map f (completionProj N₁ x) =
      completionProj N₂ x := x.2 f

variable (D : LocalReciprocityDatum F F')

/-- The norm groups of the levels of `F^{ab}` are monotone: a larger level has a smaller norm
group. -/
theorem normSub_mono {L₁ L₂ : FiniteGaloisIntermediateField F (maxAbelianSubext F F')}
    (h : L₂ ≤ L₁) : normSub D L₁ ≤ normSub D L₂ := by
  have h' : levelMap (L₂ : IntermediateField F (maxAbelianSubext F F')) ≤
      levelMap (L₁ : IntermediateField F (maxAbelianSubext F F')) := levelMap_mono h
  letI : Algebra ↥(levelMap (L₂ : IntermediateField F (maxAbelianSubext F F')))
      ↥(levelMap (L₁ : IntermediateField F (maxAbelianSubext F F'))) :=
    RingHom.toAlgebra (Subsemiring.inclusion h')
  haveI : IsScalarTower F ↥(levelMap (L₂ : IntermediateField F (maxAbelianSubext F F')))
      ↥(levelMap (L₁ : IntermediateField F (maxAbelianSubext F F'))) :=
    IsScalarTower.of_algebraMap_eq (congrFun rfl)
  exact normGroup_le_of_tower

/-- **The Artin map at the infinite abelian level**: the composite of the reciprocity
isomorphisms of all finite abelian levels, read as a homomorphism from the profinite completion
of `Fˣ` to the projective limit of the finite Galois levels of `F^{ab}/F`. -/
def artinHom : unitsCompletion (F := F) →* levelLimit (F := F) (F' := F') where
  toFun x :=
    ⟨fun L => levelMulEquiv D L.unop (completionProj (normSub D L.unop) x),
      fun {L₁ L₂} π => by
        have hle : normSub D L₁.unop ≤ normSub D L₂.unop :=
          normSub_mono D (show L₂.unop ≤ L₁.unop from leOfHom π.unop)
        have hmap :
            (InfiniteGalois.asProfiniteGaloisGroupFunctor F (maxAbelianSubext F F')).map π =
              (CategoryTheory.forget₂ FiniteGrp ProfiniteGrp).map
                ((finGaloisGroupFunctor F (maxAbelianSubext F F')).map π) := rfl
        rw [hmap, levelRestrict_eq_finGaloisGroupFunctor_map]
        beta_reduce
        rw [levelMulEquiv_diagram D π hle]
        rw [completionProj_compat x hle.hom]⟩
  map_one' := by
    apply Subtype.ext
    funext L
    show levelMulEquiv D L.unop (completionProj (normSub D L.unop) 1) = 1
    rw [completionProj_one, map_one]
  map_mul' x y := by
    apply Subtype.ext
    funext L
    show levelMulEquiv D L.unop (completionProj (normSub D L.unop) (x * y)) =
      levelMulEquiv D L.unop (completionProj (normSub D L.unop) x) *
        levelMulEquiv D L.unop (completionProj (normSub D L.unop) y)
    rw [completionProj_mul, map_mul]

/-- The class in `Fˣ ⧸ N(L)` which the reciprocity isomorphism of the level `L` sends to the
`L`-component of an element `g` of the projective limit. -/
def levelComponent (g : levelLimit (F := F) (F' := F'))
    (L : FiniteGaloisIntermediateField F (maxAbelianSubext F F')) :
    Fˣ ⧸ (normSub D L).toSubgroup :=
  (levelMulEquiv D L).symm (InfiniteGalois.proj L g)

/-- The level components of an element of the projective limit are compatible with the maps of the
completion diagram. -/
theorem levelComponent_compat (g : levelLimit (F := F) (F' := F'))
    {L₁ L₂ : (FiniteGaloisIntermediateField F (maxAbelianSubext F F'))ᵒᵖ} (π : L₁ ⟶ L₂)
    (h : normSub D L₁.unop ≤ normSub D L₂.unop) :
    (ProfiniteGrp.ProfiniteCompletion.diagram (GrpCat.of Fˣ)).map h.hom
        (levelComponent D g L₁.unop) =
      levelComponent D g L₂.unop := by
  apply (levelMulEquiv D L₂.unop).injective
  have h₂ : levelMulEquiv D L₂.unop (levelComponent D g L₂.unop) =
      InfiniteGalois.proj L₂.unop g :=
    MulEquiv.apply_symm_apply _ _
  have h₁ : levelMulEquiv D L₁.unop (levelComponent D g L₁.unop) =
      InfiniteGalois.proj L₁.unop g :=
    MulEquiv.apply_symm_apply _ _
  rw [h₂, ← levelMulEquiv_diagram D π h, h₁]
  -- it remains to identify the restricted projection with the projection of the smaller level
  rw [← levelRestrict_eq_finGaloisGroupFunctor_map]
  exact g.2 π

/-- **The Artin map is injective** (conditional on the cofinality of the norm groups, which is
`D.cofinal`): the kernel of the composite `Fˣ^{∧} → Gal(F^{ab}/F)` consists of elements whose
every finite quotient vanishes, and any finite-index subgroup of `Fˣ` contains a norm group. -/
theorem artinHom_injective (hCofinal : ∀ N : FiniteIndexNormalSubgroup Fˣ,
    ∃ L : FiniteGaloisIntermediateField F (maxAbelianSubext F F'),
      normGroup F ↥(levelMap (L : IntermediateField F (maxAbelianSubext F F'))) ≤
        (N : Subgroup Fˣ)) :
    Function.Injective (artinHom D) := by
  intro x y hxy
  apply Subtype.ext
  funext N
  obtain ⟨L, hL⟩ := hCofinal N
  have hL' : normSub D L ≤ N := hL
  have hcomp : completionProj (normSub D L) x = completionProj (normSub D L) y := by
    have h2 := congrFun (congrArg Subtype.val hxy) (Opposite.op L)
    exact (levelMulEquiv D L).injective h2
  show completionProj N x = completionProj N y
  rw [← completionProj_compat x hL'.hom, ← completionProj_compat y hL'.hom, hcomp]

/-- **Compatibility of the level components of an element of the Galois limit, in terms of the
levels themselves**:  if `L₁ ≤ L₂` then the `L₁`-component of `g` is the image of the
`L₂`-component under the canonical map `Fˣ ⧸ N_{L₂} → Fˣ ⧸ N_{L₁}`. -/
private theorem levelComponent_compat_of_le (D : LocalReciprocityDatum F F')
    (g : levelLimit (F := F) (F' := F'))
    {L₁ L₂ : FiniteGaloisIntermediateField F (maxAbelianSubext F F')} (h : L₁ ≤ L₂) :
    (ProfiniteGrp.ProfiniteCompletion.diagram (GrpCat.of Fˣ)).map (normSub_mono D h).hom
      (levelComponent D g L₂) = levelComponent D g L₁ :=
  levelComponent_compat D g h.hom.op (normSub_mono D h)

/-- **The level component of `g` maps to the class of any representative**:  if `a : Fˣ` represents
the `L'`-component of `g` and `L ≤ L'`, then the image of the `L`-component in `Fˣ ⧸ N` is the
class of `a` for every finite-index normal subgroup `N ≥ N_L`. -/
private theorem levelComponent_map_eq_of_le (D : LocalReciprocityDatum F F')
    (g : levelLimit (F := F) (F' := F'))
    {L L' : FiniteGaloisIntermediateField F (maxAbelianSubext F F')} (hLL : L ≤ L')
    (N : FiniteIndexNormalSubgroup Fˣ) (h : normSub D L ≤ N) {a : Fˣ}
    (ha : QuotientGroup.mk a = levelComponent D g L') :
    QuotientGroup.map (normSub D L) N (MonoidHom.id Fˣ) h (levelComponent D g L) =
      QuotientGroup.mk a := by
  have hc : levelComponent D g L = QuotientGroup.mk a := by
    rw [← levelComponent_compat_of_le D g hLL, ← ha]
    rfl
  rw [hc]
  exact QuotientGroup.map_mk _ _ _ _ _

/-- **Surjectivity of the infinite-level Artin map**:  every compatible family of level
automorphisms is the image of an element of the profinite completion of `Fˣ`, the components of
which are assembled from representatives of the level components. -/
private theorem artinHom_surjective_aux (D : LocalReciprocityDatum F F')
    (hCofinal : ∀ N : FiniteIndexNormalSubgroup Fˣ,
      ∃ L : FiniteGaloisIntermediateField F (maxAbelianSubext F F'),
        normGroup F ↥(levelMap (L : IntermediateField F (maxAbelianSubext F F'))) ≤
          (N : Subgroup Fˣ)) :
    Function.Surjective (artinHom D) := by
  classical
  intro g
  choose Lc hLc using hCofinal
  have hLc' : ∀ N : FiniteIndexNormalSubgroup Fˣ, normSub D (Lc N) ≤ N := fun N => hLc N
  let v : (N : FiniteIndexNormalSubgroup Fˣ) → Fˣ ⧸ N.toSubgroup :=
    fun N => QuotientGroup.map (normSub D (Lc N)) N (MonoidHom.id Fˣ) (hLc' N)
      (levelComponent D g (Lc N))
  have hv_compat : ∀ {N₁ N₂ : FiniteIndexNormalSubgroup Fˣ} (f : N₁ ⟶ N₂),
      (ProfiniteGrp.ProfiniteCompletion.diagram (GrpCat.of Fˣ)).map f (v N₁) = v N₂ := by
    intro N₁ N₂ f
    obtain ⟨a, ha⟩ := QuotientGroup.mk_surjective (levelComponent D g (Lc N₁ ⊔ Lc N₂))
    have e₁ : v N₁ = QuotientGroup.mk a :=
      levelComponent_map_eq_of_le D g le_sup_left N₁ (hLc' N₁) ha
    have e₂ : v N₂ = QuotientGroup.mk a :=
      levelComponent_map_eq_of_le D g le_sup_right N₂ (hLc' N₂) ha
    rw [e₁, e₂]
    show QuotientGroup.map N₁ N₂ (MonoidHom.id Fˣ) f.le (QuotientGroup.mk a) = QuotientGroup.mk a
    exact QuotientGroup.map_mk _ _ _ _ _
  have hv_self : ∀ L : FiniteGaloisIntermediateField F (maxAbelianSubext F F'),
      v (normSub D L) = levelComponent D g L := by
    intro L
    obtain ⟨a, ha⟩ := QuotientGroup.mk_surjective (levelComponent D g (Lc (normSub D L) ⊔ L))
    have e₁ : v (normSub D L) = QuotientGroup.mk a :=
      levelComponent_map_eq_of_le D g le_sup_left (normSub D L) (hLc' (normSub D L)) ha
    have e₂ : levelComponent D g L = QuotientGroup.mk a := by
      rw [← levelComponent_compat_of_le D g (le_sup_right : L ≤ Lc (normSub D L) ⊔ L), ← ha]
      rfl
    rw [e₁, e₂]
  let x : unitsCompletion (F := F) := ⟨v, by rintro N₁ N₂ f; exact hv_compat f⟩
  refine ⟨x, ?_⟩
  apply Subtype.ext
  funext L
  show levelMulEquiv D L.unop (completionProj (normSub D L.unop) x) = g.val L
  have hcomp : completionProj (normSub D L.unop) x = levelComponent D g L.unop := hv_self L.unop
  rw [hcomp, levelComponent]
  exact MulEquiv.apply_symm_apply (levelMulEquiv D L.unop) (InfiniteGalois.proj L.unop g)

end

/-- **Infinite-level local reciprocity**, conditional on the reciprocity datum: the profinite
completion of `Fˣ` is the abelianised absolute Galois group `G_F^{ab} = Gal(F^{ab}/F)`, where
`F^{ab} = NK.LocalReciprocity.maxAbelianSubext F F'` is the maximal abelian subextension.

Suggested route.

* *The level isomorphisms.*  Every finite Galois subextension `L ≤ F^{ab}` is abelian over `F`
  (`NK.LocalReciprocity.commutator_gal_maxAbelianSubext`: `Gal(F^{ab}/F)` is abelian), so the
  composite of `D.artin` with the restriction `Gal(F'/F) →* Gal(L/F)` is surjective with kernel
  `normGroup F L` by `D.isLevelIso`.
* *The map.*  By the adjunction `ProfiniteGrp.ProfiniteCompletion.homEquiv` (a homomorphism from
  the profinite completion of `Fˣ` to a profinite group is the same thing as an abstract
  homomorphism from `Fˣ`), applied to `D.artin` composed with the restriction
  `Gal(F'/F) →* Gal(F^{ab}/F)`, one gets a continuous homomorphism
  `Φ : (completion Fˣ) →* Gal(F^{ab}/F)`.  (Watch out: `homEquiv` is universe-monomorphic while
  `Gal(F^{ab}/F)` may live in a larger universe; alternatively build `Φ` directly on the inverse
  limit, using that `Gal(F^{ab}/F)` is the limit of the finite Galois levels, see
  `Mathlib.FieldTheory.Galois.Profinite`.)
* *Surjectivity.*  The image of `Φ` is a closed subgroup of `Gal(F^{ab}/F)` whose projection to
  every finite quotient `Gal(L/F)` is surjective (by the level isomorphisms), hence the whole
  group: a closed subgroup of a profinite group meeting every coset of every open normal subgroup
  is everything.
* *Injectivity.*  A non-trivial element of the completion has non-trivial image in some finite
  quotient `Fˣ ⧸ M` with `M.FiniteIndex`; by `D.cofinal` (restricted to abelian levels) there is a
  finite abelian Galois level `L` with `normGroup F L ≤ M`; since the projection to `Fˣ ⧸ N(L)`
  then factors through `Fˣ ⧸ M` and the level isomorphism is injective there, the composite with
  `Φ` is non-trivial as well. -/
theorem exists_mulEquiv_completion_maxAbelian {F : Type u} {F' : Type v} [Field F] [Field F']
    [Algebra F F'] [IsGalois F F']
    (D : NK.LocalReciprocity.LocalReciprocityDatum F F') :
    Nonempty
      (((ProfiniteGrp.ProfiniteCompletion.completion (GrpCat.of Fˣ)).toProfinite.toTop) ≃*
        ((NK.LocalReciprocity.maxAbelianSubext F F') ≃ₐ[F]
          (NK.LocalReciprocity.maxAbelianSubext F F'))) := by
  classical
  exact ⟨(MulEquiv.ofBijective (artinHom D)
      ⟨artinHom_injective D (exists_levelMap_normGroup_le D),
        artinHom_surjective_aux D (exists_levelMap_normGroup_le D)⟩).trans
    (InfiniteGalois.mulEquivToLimit F (NK.LocalReciprocity.maxAbelianSubext F F')).symm⟩

end NK.LocalReciprocity
