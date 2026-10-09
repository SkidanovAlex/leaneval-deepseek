import Mathlib
import Submission.Commons.RepresentationTheory.GroupCohomology.natCard_nsmul_H2_eq_zero

/-!
# A vanishing criterion for maps on `H²` coming from `ℤ`-valued "order" maps

Let `G` be a finite group, `B₁ B₂ : Rep ℤ G` two `ℤ`-linear `G`-representations and let
`ord₁ : B₁ ⟶ trivial` and `ord₂ : B₂ ⟶ trivial` be morphisms to the trivial representation `ℤ`.
Suppose that the induced map `H²(G, B₂) ⟶ H²(G, ℤ)` is injective, and that there is a morphism
`ι : B₁ ⟶ B₂` with

`ι ≫ ord₂ = e • ord₁`

for some multiple `e` of the order `Nat.card G` of `G`. Then `ι` induces the zero map on `H²`:

`groupCohomology.map (MonoidHom.id G) ι 2 = 0`.

This is the algebraic heart of the "monomorphism of valuation" argument in the proof of the
Neukirch–Uchida theorem: `e • ord₁` is multiplication by `e` on the target and hence induces
`e` times the map on `H²(G, ℤ)`, but `Nat.card G` — and therefore `e` — annihilates `H²(G, ℤ)`
(`Commons.RepresentationTheory.GroupCohomology.natCard_nsmul_H2_eq_zero`). Since the map
`H²(G, B₂) ⟶ H²(G, ℤ)` is injective, `ι` must induce zero on `H²`.

## Main result

* `map_eq_zero_of_mono_valuation`
-/

namespace Commons.RepresentationTheory.GroupCohomology

open CategoryTheory

/-- **A morphism that becomes divisible by the group order after applying an order map is zero on
`H²`.**  With `ord₁ : B₁ ⟶ trivial`, `ord₂ : B₂ ⟶ trivial` morphisms to the trivial representation
(thought of as "order/valuation" maps), `ι : B₁ ⟶ B₂` satisfying `ι ≫ ord₂ = e • ord₁`, and
`H²(G, B₂) ⟶ H²(G, ℤ)` injective, the induced map `H²(G, B₁) ⟶ H²(G, B₂)` vanishes, provided
`Nat.card G ∣ e`.

Indeed `map ι 2 ≫ map ord₂ 2 = map (e • ord₁) 2 = e • map ord₁ 2`, and the last map is zero because
`e` is a multiple of `Nat.card G`, which annihilates `H²(G, ℤ)`.  Injectivity of `map ord₂ 2`
(in the form of `Mono`) then forces `map ι 2 = 0`. -/
theorem map_eq_zero_of_mono_valuation
    {G : Type} [Group G] [Fintype G]
    {B₁ B₂ : Rep ℤ G} (ord₁ : B₁ ⟶ Rep.trivial ℤ G ℤ) (ord₂ : B₂ ⟶ Rep.trivial ℤ G ℤ)
    (h₂ : CategoryTheory.Mono (groupCohomology.map (MonoidHom.id G) ord₂ 2))
    (ι : B₁ ⟶ B₂) (e : ℕ) (hι : CategoryTheory.CategoryStruct.comp ι ord₂ = e • ord₁)
    (he : Nat.card G ∣ e) :
    groupCohomology.map (MonoidHom.id G) ι 2 = 0 := by
  -- The order of `G` kills `H²(G, ℤ)`, hence so does any multiple `e` of it.
  have hkill : ∀ y : groupCohomology (Rep.trivial ℤ G ℤ) 2, e • y = 0 := by
    intro y
    obtain ⟨m, hm⟩ := he
    have h1 : Nat.card G • y = 0 := natCard_nsmul_H2_eq_zero _ y
    rw [hm, mul_nsmul, h1, smul_zero]
  -- `groupCohomology` is an additive functor of the representation, so it commutes with `e •`.
  have hstep : groupCohomology.map (MonoidHom.id G) (e • ord₁) 2
      = e • groupCohomology.map (MonoidHom.id G) ord₁ 2 := by
    rw [← groupCohomology.functor_map, Functor.map_nsmul, groupCohomology.functor_map]
    rfl
  have hzero : groupCohomology.map (MonoidHom.id G) (e • ord₁) 2 = 0 := by
    rw [hstep]
    ext x
    simpa using hkill (groupCohomology.map (MonoidHom.id G) ord₁ 2 x)
  -- Functoriality turns the hypothesis `ι ≫ ord₂ = e • ord₁` into an identity of maps on `H²`.
  have hcomp : groupCohomology.map (MonoidHom.id G) ι 2 ≫
      groupCohomology.map (MonoidHom.id G) ord₂ 2
      = groupCohomology.map (MonoidHom.id G) (e • ord₁) 2 := by
    rw [← groupCohomology.map_id_comp, hι]
  -- Cancel the injective map `H²(G, B₂) ⟶ H²(G, ℤ)`.
  rw [← cancel_mono (groupCohomology.map (MonoidHom.id G) ord₂ 2), hcomp, hzero]
  simp

end Commons.RepresentationTheory.GroupCohomology
