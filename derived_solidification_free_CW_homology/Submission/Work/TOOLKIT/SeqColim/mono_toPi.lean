/-
AREA TOOLKIT — `mono_toPi`: the canonical comparison map from an `ℕ`-indexed small coproduct of
cochain complexes of light condensed abelian groups to the corresponding product is a
monomorphism.

The mathematical content is that `LightCondAb` is a Grothendieck abelian category: the coproduct
`∐_n X_n` is the filtered colimit of its finite sub-coproducts `∐_{n ∈ S} X_n` (`S` a finite set),
each of which is a *biproduct*, hence canonically isomorphic to the corresponding finite product
`∏_{n ∈ S} X_n` and therefore mapped monomorphically into `∏_n X_n`.  Since filtered colimits are
exact (AB5), the induced map out of the colimit is again a monomorphism.

The formalisation follows this route: `CategoryTheory.Limits.colim.map_mono'` reduces the
statement to the componentwise monomorphism of a natural transformation `φ` out of the diagram
`liftToFinsetObj (Discrete.functor X)`, and the component of `φ` at a finite set `S` is handled by
`mono_finiteSubcoproductsCocone_comp` (which uses the finite-index input
`Work.TOOLKIT.SeqColim.mono_finite_comparison`).
-/
import Mathlib
import Submission.Work.TOOLKIT.SeqColim.Defs
import Submission.Work.TOOLKIT.SeqColim.mono_finite_comparison

open CategoryTheory Limits

noncomputable section

namespace Work.TOOLKIT.SeqColim

set_option linter.style.haveILetI false

/-! ## Auxiliary facts -/

/-- Two elements of `↥S`, for `S : Finset (Discrete ℕ)`, coincide as soon as their underlying
natural numbers do. -/
private lemma as_eq_iff {S : Finset (Discrete ℕ)} (x y : ↥S) :
    (x : Discrete ℕ).as = (y : Discrete ℕ).as ↔ x = y := by
  constructor
  · intro h
    exact Subtype.ext (by
      rw [← Discrete.mk_as ((x : Discrete ℕ)), ← Discrete.mk_as ((y : Discrete ℕ)), h])
  · intro h; rw [h]

/-- Composing a morphism on the left of a `Pi.lift`: `p ≫ Pi.lift g = Pi.lift (p ≫ g ·)`. -/
private lemma comp_Pi_lift {C : Type*} [Category C] {β : Type*} {f : β → C} [HasProduct f]
    {P Q : C} (p : P ⟶ Q) (g : (b : β) → Q ⟶ f b) :
    p ≫ Pi.lift g = Pi.lift (fun b => p ≫ g b) := by
  apply Pi.hom_ext
  intro b
  rw [Category.assoc, Pi.lift_comp_π, Pi.lift_comp_π]

/-! ## The component of the comparison map at a finite set -/

/-- **Coordinate identity for the finite sub-coproducts.**  The composite of the leg of the
finite-subcoproduct cocone of `X` at `S` with the `t.as`-th coordinate of the coproduct `∐ X` is
the `t`-th coordinate of the finite family `x ↦ X x.as`: the composite picks out the summand
indexed by `t`, and all other summands are killed.

The leg is written as the explicit `Sigma.desc` (which it is by definition), so that the identity
is a computation with `Sigma.ι_comp_desc` and `coord_self`/`coord_eq_zero_of_ne`; the two
occurrences of `coord` must be phrased with the same index type `ℕ` on both sides. -/
lemma finiteSubcoproductsCocone_desc_comp_coord (X : ℕ → Cpx) (S : Finset (Discrete ℕ))
    (t : ↥S) :
    (Limits.Sigma.desc (fun s : ↥S => Sigma.ι X ((s : Discrete ℕ).as)) :
        (∐ fun x : ↥S => X ((x : Discrete ℕ).as)) ⟶ (∐ X)) ≫ coord X ((t : Discrete ℕ).as)
      = coord (fun x : ↥S => X ((x : Discrete ℕ).as)) t := by
  apply Sigma.hom_ext
  intro s
  rw [← Category.assoc, Sigma.ι_comp_desc]
  by_cases h : (s : Discrete ℕ).as = (t : Discrete ℕ).as
  · have hst : s = t := (as_eq_iff s t).mp h
    subst hst
    simp only [coord_self]
  · have hst : s ≠ t := fun h' => h ((as_eq_iff s t).mpr h')
    rw [coord_eq_zero_of_ne _ h, coord_eq_zero_of_ne _ hst]

/-- **The component of the comparison map out of a finite sub-coproduct is a monomorphism.**

Composing the component with the product projection `r := Pi.lift (fun t : ↥S => Pi.π X t.as)`
turns it into the finite comparison map `∏_{x ∈ S} X x.as ⟶ ∏_{x ∈ S} X x.as` of the finite
family `x ↦ X x.as`, which is a monomorphism by `mono_finite_comparison`; a morphism whose
composite with something is a monomorphism is itself a monomorphism. -/
lemma mono_finiteSubcoproductsCocone_comp (X : ℕ → Cpx) (S : Finset (Discrete ℕ)) :
    Mono ((CategoryTheory.Limits.CoproductsFromFiniteFiltered.finiteSubcoproductsCocone X).ι.app S
      ≫ Pi.lift (fun n : ℕ => coord X n)) := by
  show Mono ((Limits.Sigma.desc (fun s : ↥S => Sigma.ι X ((s : Discrete ℕ).as)) :
      (∐ fun x : ↥S => X ((x : Discrete ℕ).as)) ⟶ (∐ X))
      ≫ Pi.lift (fun n : ℕ => coord X n))
  let r : (∏ᶜ X) ⟶ (∏ᶜ fun t : ↥S => X ((t : Discrete ℕ).as)) :=
    Pi.lift (fun t : ↥S => Pi.π X ((t : Discrete ℕ).as))
  haveI hfin : Mono (Pi.lift (fun t : ↥S => coord (fun x : ↥S => X ((x : Discrete ℕ).as)) t)) :=
    mono_finite_comparison (fun x : ↥S => X ((x : Discrete ℕ).as))
  -- `X`'s comparison map followed by the product projection is the comparison map of the
  -- finite family `x ↦ X x.as`
  have hstep : Pi.lift (fun n : ℕ => coord X n) ≫ r
      = Pi.lift (fun t : ↥S => coord X ((t : Discrete ℕ).as)) := by
    show Pi.lift (fun n : ℕ => coord X n) ≫ Pi.lift (fun t : ↥S => Pi.π X ((t : Discrete ℕ).as))
      = Pi.lift (fun t : ↥S => coord X ((t : Discrete ℕ).as))
    rw [comp_Pi_lift]
    apply Pi.hom_ext
    intro t
    simp only [Pi.lift_comp_π]
  -- hence the composite with `r` is that finite comparison map
  have hEq : ((Limits.Sigma.desc (fun s : ↥S => Sigma.ι X ((s : Discrete ℕ).as)) :
      (∐ fun x : ↥S => X ((x : Discrete ℕ).as)) ⟶ (∐ X))
      ≫ Pi.lift (fun n : ℕ => coord X n)) ≫ r
      = Pi.lift (fun t : ↥S => coord (fun x : ↥S => X ((x : Discrete ℕ).as)) t) := by
    rw [Category.assoc, hstep, comp_Pi_lift]
    apply Pi.hom_ext
    intro t
    rw [Pi.lift_comp_π, Pi.lift_comp_π, finiteSubcoproductsCocone_desc_comp_coord]
  haveI : Mono (((Limits.Sigma.desc (fun s : ↥S => Sigma.ι X ((s : Discrete ℕ).as)) :
      (∐ fun x : ↥S => X ((x : Discrete ℕ).as)) ⟶ (∐ X))
      ≫ Pi.lift (fun n : ℕ => coord X n)) ≫ r) := by
    rw [hEq]; exact hfin
  refine ⟨fun {Z} g h hgh => ?_⟩
  have h2 : g ≫ (((Limits.Sigma.desc (fun s : ↥S => Sigma.ι X ((s : Discrete ℕ).as)) :
      (∐ fun x : ↥S => X ((x : Discrete ℕ).as)) ⟶ (∐ X))
      ≫ Pi.lift (fun n : ℕ => coord X n)) ≫ r)
      = h ≫ (((Limits.Sigma.desc (fun s : ↥S => Sigma.ι X ((s : Discrete ℕ).as)) :
      (∐ fun x : ↥S => X ((x : Discrete ℕ).as)) ⟶ (∐ X))
      ≫ Pi.lift (fun n : ℕ => coord X n)) ≫ r) := by
    simp only [← Category.assoc, hgh]
  exact (cancel_mono _).mp h2

/-- The canonical comparison map from a small coproduct to the corresponding product is a
monomorphism, for `ℕ`-indexed families of cochain complexes of light condensed abelian groups.
(Equivalently: a morphism into such a coproduct all of whose coordinates vanish is zero.)

Route.  `Finset (Discrete ℕ)` is filtered and `Cpx` satisfies AB5, so
`(colim : (Finset (Discrete ℕ) ⥤ Cpx) ⥤ Cpx).PreservesMonomorphisms` holds by instance search.
Use Mathlib's `CategoryTheory.Limits.CoproductsFromFiniteFiltered` API:
`liftToFinsetObj (Discrete.functor X) : Finset (Discrete ℕ) ⥤ Cpx` is the diagram of finite
sub-coproducts of `X`, and `finiteSubcoproductsCocone X` is a colimit cocone for it with point
`∐ X` (`isColimitFiniteSubproductsCocone X`).  Define a natural transformation `φ` from that
diagram to the constant diagram at `∏ᶜ X` whose component at `S` is
`Pi.lift (fun n => (finiteSubcoproductsCocone X).ι.app S ≫ coord X n)` (naturality is automatic
because `φ` is the postcomposition of the cocone ` (finiteSubcoproductsCocone X).ι` with the
comparison map, and the compatibility
`(finiteSubcoproductsCocone X).ι.app S ≫ Pi.lift (fun n => coord X n) = φ.app S` is
`Category.comp_id`), show that `φ` is a mono natural transformation (each component is
the composite of the canonical isomorphism `∐_{x ∈ S} X x = ∏_{x ∈ S} X x` for the finite index
type `S` — which is `biproduct.isoCoproduct ≪≫ biproduct.isoProduct` after introducing
`HasFiniteBiproducts Cpx` locally via `HasFiniteBiproducts.of_hasFiniteProducts`, done in
`Work.TOOLKIT.SeqColim.mono_finite_comparison` — with the split
mono `∏_{x ∈ S} X x ⟶ ∏_ℕ X n`, whose retraction is the product projection; this is
`mono_finiteSubcoproductsCocone_comp`), and apply
`CategoryTheory.Limits.colim.map_mono'` with a colimit cocone of the constant diagram at `∏ᶜ X`
(whose point is `∏ᶜ X`; any cocone over a constant diagram is constant). -/
theorem mono_toPi (X : ℕ → Work.TOOLKIT.Cpx) :
    CategoryTheory.Mono (CategoryTheory.Limits.Pi.lift (fun n => Work.TOOLKIT.SeqColim.coord X n)) := by
  haveI : IsConnected (Finset (Discrete ℕ)) := IsFiltered.isConnected _
  haveI hc₁ : IsColimit
      (CategoryTheory.Limits.CoproductsFromFiniteFiltered.finiteSubcoproductsCocone X) :=
    CategoryTheory.Limits.CoproductsFromFiniteFiltered.isColimitFiniteSubproductsCocone X
  -- the natural transformation from the finite sub-coproducts to the product
  let φ : CategoryTheory.Limits.CoproductsFromFiniteFiltered.liftToFinsetObj (Discrete.functor X) ⟶
      (Functor.const (Finset (Discrete ℕ))).obj (∏ᶜ X) :=
    (CategoryTheory.Limits.CoproductsFromFiniteFiltered.finiteSubcoproductsCocone X).ι ≫
      (Functor.const (Finset (Discrete ℕ))).map (Pi.lift (fun n => coord X n))
  -- each component of `φ` is a monomorphism
  have hφ : ∀ S : Finset (Discrete ℕ), Mono (φ.app S) := by
    intro S
    show Mono ((CategoryTheory.Limits.CoproductsFromFiniteFiltered.finiteSubcoproductsCocone X).ι.app S
      ≫ Pi.lift (fun n : ℕ => coord X n))
    exact mono_finiteSubcoproductsCocone_comp X S
  haveI : ∀ S : Finset (Discrete ℕ), Mono (φ.app S) := hφ
  haveI : Mono φ := NatTrans.mono_of_mono_app φ
  -- the comparison map is the map induced on the colimits
  exact colim.map_mono' φ hc₁ (isColimitConstCocone (Finset (Discrete ℕ)) (∏ᶜ X))
    (Pi.lift (fun n : ℕ => coord X n)) (by
      intro S
      exact (Category.comp_id (φ.app S)).symm)

end Work.TOOLKIT.SeqColim
