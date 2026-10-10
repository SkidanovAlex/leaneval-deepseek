import Mathlib.Algebra.Field.ZMod
import Mathlib.FieldTheory.Galois.Profinite
import Mathlib.Topology.Connected.Separation
import Submission.Work.SSGRoute.ZDataMup.mupLocalVocab
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Local constancy descends along an open surjection, and along restriction to `F^{ab}`

Let `F'/F` be Galois and let `A = NK.LocalReciprocity.maxAbelianSubext F F'` be the maximal
abelian subextension, so that `NK.LocalCFT.AbGal F F' = Gal(A/F)` is the abelianised absolute
Galois group.  The restriction

`ρ = AlgEquiv.restrictNormalHom A : Gal(F'/F) →* Gal(A/F)`

is a **surjective open** continuous group homomorphism for the Krull topologies: it is a
continuous surjection from the compact group `Gal(F'/F)` onto the Hausdorff group `Gal(A/F)`,
hence a quotient map, and a quotient map which is a group homomorphism is open
(`MonoidHom.isOpenQuotientMap_of_isQuotientMap`).

Consequently local constancy of a homomorphism into a discrete group descends along any
homeomorphic identification `e : G ≃* Gal(F'/F)`: if `y = y' ∘ (ρ ∘ e)` is locally constant then
so is `y'`.  Indeed, for a surjective open `f`, the fibers of `g` are precisely the images under
`f` of the fibers of `g ∘ f`, so `IsLocallyConstant (g ∘ f)` forces `IsLocallyConstant g`
(`isLocallyConstant_of_comp_open_surjective`).

This is the converse-direction companion of
`Work.SSGRoute.ZDataMup.exists_factor_of_homeomorph`: a locally constant character of `G`
factorises through `AbGal F F'`, and conversely a character of `AbGal F F'` which arises by
pullback from such a factorisation is locally constant.
-/

namespace Work.SSGRoute.ZDataMup

set_option linter.style.haveILetI false

/-- **Local constancy descends along a surjective open map.**  If `f : X → Y` is surjective and
open and `g ∘ f` is locally constant, then `g` is locally constant with respect to the topology of
`Y`: for every subset `s` of the target, `g ⁻¹' s = f '' (f ⁻¹' (g ⁻¹' s))` (uses surjectivity of
`f`), and the right-hand side is open because `f` is open and `g ∘ f` is locally constant. -/
theorem isLocallyConstant_of_comp_open_surjective {X Y Z : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] {f : X → Y} (hf : IsOpenMap f) (hsurj : Function.Surjective f)
    {g : Y → Z} (h : IsLocallyConstant (g ∘ f)) : IsLocallyConstant g := by
  intro s
  have hset : g ⁻¹' s = f '' (f ⁻¹' (g ⁻¹' s)) := by
    ext y
    constructor
    · intro hy
      obtain ⟨x, rfl⟩ := hsurj y
      exact ⟨x, hy, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      exact hx
  rw [hset]
  exact hf _ (h s)

/-- **A `ZMod p`-character of `Gal(F^{ab}/F)` obtained by factoring a locally constant character
of `G` is locally constant.**

Let `e : G ≃* Gal(F'/F)` be a homeomorphism (for the Krull topology on `Gal(F'/F)`) and let
`y : G →* Multiplicative (ZMod p)` be locally constant.  If a character `y'` of
`Gal(F^{ab}/F) = NK.LocalCFT.AbGal F F'` pulls back to `y` along the restriction to the maximal
abelian subextension, then `y'` is locally constant as well. -/
theorem isLocallyConstant_factor_restrictNormalHom {p : ℕ} [Fact p.Prime] {F F' G : Type*}
    [Field F] [Field F'] [Algebra F F'] [IsGalois F F'] [Group G] [TopologicalSpace G]
    (e : G ≃* (F' ≃ₐ[F] F')) (he : IsHomeomorph (⇑e))
    (y : G →* Multiplicative (ZMod p)) (hy : IsLocallyConstant y)
    (y' : NK.LocalCFT.AbGal F F' →* Multiplicative (ZMod p))
    (h : y'.comp ((AlgEquiv.restrictNormalHom
      (NK.LocalReciprocity.maxAbelianSubext F F')).comp e.toMonoidHom) = y) :
    IsLocallyConstant y' := by
  classical
  -- `F^{ab}` is Galois over `F` (it is the fixed field of the commutator subgroup).
  let A : IntermediateField F F' := NK.LocalReciprocity.maxAbelianSubext F F'
  haveI : IsGalois F ↥A := inferInstance
  -- The restriction `ρ : Gal(F'/F) →* Gal(F^{ab}/F)`.
  let ρ : (F' ≃ₐ[F] F') →* (↥A ≃ₐ[F] ↥A) :=
    AlgEquiv.restrictNormalHom (F := F) (K₁ := F') ↥A
  have hsurjρ : Function.Surjective ρ :=
    AlgEquiv.restrictNormalHom_surjective (K₁ := ↥A) (E := F')
  have hcontρ : Continuous ⇑ρ :=
    InfiniteGalois.restrictNormalHom_continuous (k := F) (K := F') A
  -- `ρ` is continuous, surjective, `Gal(F'/F)` is compact and `Gal(F^{ab}/F)` Hausdorff, so `ρ`
  -- is a quotient map, hence (being a group homomorphism) an open map.
  have hopenρ : IsOpenMap ⇑ρ := by
    haveI : CompactSpace (F' ≃ₐ[F] F') := inferInstance
    haveI : T2Space (↥A ≃ₐ[F] ↥A) := inferInstance
    exact (MonoidHom.isOpenQuotientMap_of_isQuotientMap
      (Topology.IsQuotientMap.of_surjective_continuous hsurjρ hcontρ)).isOpenMap
  -- The composite `φ = ρ ∘ e : G →* Gal(F^{ab}/F)` along which `y'` pulls back to `y`.
  let φ : G →* (↥A ≃ₐ[F] ↥A) := ρ.comp e.toMonoidHom
  have hsurjφ : Function.Surjective φ := hsurjρ.comp e.surjective
  have hopenφ : IsOpenMap ⇑φ := by
    rw [show ⇑φ = ⇑ρ ∘ ⇑e from rfl]
    exact hopenρ.comp he.isOpenMap
  have hcomp : y'.comp φ = y := h
  -- `y' ∘ φ = y` is locally constant and `φ` is a surjective open map, so `y'` is locally constant.
  refine isLocallyConstant_of_comp_open_surjective (f := ⇑φ) hopenφ hsurjφ ?_
  show IsLocallyConstant (⇑y' ∘ ⇑φ)
  rw [show ⇑y' ∘ ⇑φ = ⇑(y'.comp φ) from rfl, hcomp]
  exact hy

end Work.SSGRoute.ZDataMup
