import Mathlib
import Submission.NK.LocalReciprocity.MaxAbelianSetup
import Submission.NK.LocalReciprocity.exists_mulEquiv_completion_maxAbelian

/-!
# Surjectivity of the infinite-level Artin map

The infinite-level Artin map

`artinHom D : (Fˣ)^{∧} ⟶ lim_{L ≤ F^{ab}} Gal(L/F)`

(`NK.LocalReciprocity.artinHom`) is the composite of the level isomorphisms of the reciprocity
datum `D` over all finite Galois levels `L` of the maximal abelian subextension
`F^{ab} = maxAbelianSubext F F'`.  This file proves that it is **surjective**, assuming that the
norm groups `N_{L/F} Lˣ` are cofinal among the finite-index subgroups of `Fˣ` (the existence
theorem of local class field theory, which is the hypothesis `hCofinal`).

This is the `F^{ab}`-half of the isomorphism `κˣ^{∧} ≅ G_κ^{ab}` of infinite-level local
reciprocity; combined with `NK.LocalReciprocity.artinHom_injective` it shows that `artinHom D` is
bijective.

## The argument

The two limits involved are indexed differently: the profinite completion of `Fˣ` is indexed by
*all* finite-index normal subgroups `N ≤ Fˣ`, while the Galois limit is indexed by the finite
Galois levels `L ≤ F^{ab}`.  Surjectivity is therefore proved by constructing, for a given
`g` in the Galois limit, an element `x` of the completion with `artinHom D x = g`:

* for a finite-index normal subgroup `N`, choose a level `Lc N` with `N_{Lc N} ≤ N`
  (cofinality) and set `x N := ` the image of `levelComponent D g (Lc N)` in `Fˣ ⧸ N`;
* this is **well defined** in the sense that the level is immaterial: if `L, L'` are two levels
  with `N_L ≤ N` and `N_{L'} ≤ N`, then both choices give the image of a common representative,
  namely of any lift of the `(L ⊔ L')`-component of `g` — the components of `g` are compatible
  (`levelComponent_compat`), and `QuotientGroup.map` is `QuotientGroup.mk` on representatives;
* the compatibility of `x` along `N₁ ≤ N₂` follows from the same computation, and the identity
  `artinHom D x = g` is the definition of `levelComponent` together with
  `MulEquiv.apply_symm_apply`.

No continuity or compactness is used: the limit is built pointwise.
-/

universe u v

namespace NK.LocalReciprocity

open scoped Classical
open CategoryTheory

noncomputable section

variable {F : Type u} {F' : Type v} [Field F] [Field F'] [Algebra F F'] [IsGalois F F']

/-- **Compatibility of the level components of an element of the Galois limit, in terms of the
levels themselves**:  if `L₁ ≤ L₂` then the `L₁`-component of `g` is the image of the
`L₂`-component under the canonical map `Fˣ ⧸ N_{L₂} → Fˣ ⧸ N_{L₁}`.

This is `levelComponent_compat` with the opposite-category morphism `L₁ ⟶ L₂` made explicit. -/
theorem levelComponent_compat_of_le (D : LocalReciprocityDatum F F')
    (g : levelLimit (F := F) (F' := F'))
    {L₁ L₂ : FiniteGaloisIntermediateField F (maxAbelianSubext F F')} (h : L₁ ≤ L₂) :
    (ProfiniteGrp.ProfiniteCompletion.diagram (GrpCat.of Fˣ)).map (normSub_mono D h).hom
      (levelComponent D g L₂) = levelComponent D g L₁ :=
  levelComponent_compat D g h.hom.op (normSub_mono D h)

/-- **The level component of `g` maps to the class of any representative.**  If `a : Fˣ`
represents the `L'`-component of `g`, then for every finite-index normal subgroup `N` containing
`N_{L/F}` with `L ≤ L'`, the image of the `L`-component of `g` in `Fˣ ⧸ N` is the class of `a`.

(Equivalently: the map `Fˣ ⧸ N_L → Fˣ ⧸ N` is `QuotientGroup.mk` on representatives, and the
`L`-component of `g` is the image of its `L'`-component, which is the class of `a`.) -/
theorem levelComponent_map_eq_of_le (D : LocalReciprocityDatum F F')
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

/-- **Surjectivity of the infinite-level Artin map.**  If the norm groups `N_{L/F} Lˣ` of the
finite Galois levels `L` of `F^{ab} = maxAbelianSubext F F'` are cofinal among the finite-index
subgroups of `Fˣ` (the existence theorem of local class field theory, here the hypothesis
`hCofinal`), then the Artin map `(Fˣ)^{∧} → Gal(F^{ab}/F)` of the reciprocity datum is onto.

Indeed, for a given compatible family `g = (g_L)_L` of level automorphisms, the classes of
representatives of the components `g_L` assemble into an element of the profinite completion,
by cofinality of the norm groups and compatibility of the components. -/
theorem artinHom_surjective {F : Type u} {F' : Type v} [Field F] [Field F'] [Algebra F F']
    [IsGalois F F'] (D : LocalReciprocityDatum F F')
    (hCofinal : ∀ N : FiniteIndexNormalSubgroup Fˣ,
      ∃ L : FiniteGaloisIntermediateField F (maxAbelianSubext F F'),
        normGroup F ↥(levelMap (L : IntermediateField F (maxAbelianSubext F F'))) ≤
          (N : Subgroup Fˣ)) :
    Function.Surjective (artinHom D) := by
  classical
  intro g
  -- For every finite-index normal subgroup `N`, pick a level of `F^{ab}` with `N_L ≤ N`.
  choose Lc hLc using hCofinal
  have hLc' : ∀ N : FiniteIndexNormalSubgroup Fˣ, normSub D (Lc N) ≤ N := fun N => hLc N
  -- The candidate element of the profinite completion, componentwise.
  let v : (N : FiniteIndexNormalSubgroup Fˣ) → Fˣ ⧸ N.toSubgroup :=
    fun N => QuotientGroup.map (normSub D (Lc N)) N (MonoidHom.id Fˣ) (hLc' N)
      (levelComponent D g (Lc N))
  -- Its components are compatible along the maps of the completion diagram.
  have hv_compat : ∀ {N₁ N₂ : FiniteIndexNormalSubgroup Fˣ} (f : N₁ ⟶ N₂),
      (ProfiniteGrp.ProfiniteCompletion.diagram (GrpCat.of Fˣ)).map f (v N₁) = v N₂ := by
    intro N₁ N₂ f
    -- a common representative of the components of both levels
    obtain ⟨a, ha⟩ := QuotientGroup.mk_surjective (levelComponent D g (Lc N₁ ⊔ Lc N₂))
    have e₁ : v N₁ = QuotientGroup.mk a :=
      levelComponent_map_eq_of_le D g le_sup_left N₁ (hLc' N₁) ha
    have e₂ : v N₂ = QuotientGroup.mk a :=
      levelComponent_map_eq_of_le D g le_sup_right N₂ (hLc' N₂) ha
    rw [e₁, e₂]
    show QuotientGroup.map N₁ N₂ (MonoidHom.id Fˣ) f.le (QuotientGroup.mk a) = QuotientGroup.mk a
    exact QuotientGroup.map_mk _ _ _ _ _
  -- On the norm groups themselves, the components are the level components of `g`.
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
  -- `artinHom D x` has the same level components as `g`, hence equals `g`.
  apply Subtype.ext
  funext L
  show levelMulEquiv D L.unop (completionProj (normSub D L.unop) x) = g.val L
  have hcomp : completionProj (normSub D L.unop) x = levelComponent D g L.unop := hv_self L.unop
  rw [hcomp, levelComponent]
  exact MulEquiv.apply_symm_apply (levelMulEquiv D L.unop) (InfiniteGalois.proj L.unop g)

end

end NK.LocalReciprocity
