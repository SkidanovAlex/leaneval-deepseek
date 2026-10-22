/-
AREA RESOL — the canonical comparison map `∐ₙ Xₙ ⟶ ∏ₙ Xₙ` of light condensed abelian groups is a
monomorphism.

This is the "modules" input to the telescope construction of the area (`Work.RESOL.mono_telD`):
a morphism into a small coproduct all of whose coordinates vanish is zero.

The mathematics is that `LightCondAb` is a Grothendieck abelian category (AB5): the coproduct
`∐ₙ Xₙ` is the filtered colimit of its finite sub-coproducts `∐_{n ∈ S} Xₙ` (`S` a finite set),
each of which is a *biproduct*, hence canonically isomorphic to the corresponding finite product
`∏_{n ∈ S} Xₙ` and therefore mapped monomorphically into `∏ₙ Xₙ`.  Since filtered colimits are
exact, the induced map out of the colimit is again a monomorphism.

The formalisation follows this route:
* `mono_finiteComparison`: for a *finite* index type `β`, the coordinate comparison map
  `∐ f ⟶ ∏ f` is the canonical isomorphism between the coproduct and the product coming from the
  biproduct `⨁ f`;
* `mono_finiteSubcoproductsCocone_comp`: the component at a finite set `S` of the comparison map
  out of the finite sub-coproducts is a monomorphism (compose with the product projection onto
  `S` and use the previous point);
* `colim.map_mono'`: `Finset (Discrete ℕ)` is filtered and `LightCondAb` is AB5, so the colimit
  functor preserves monomorphisms, and the comparison map is the map induced on colimits.
-/
import Mathlib
import Submission.Work.RESOL.Telescope

open CategoryTheory Limits LightProfinite LightCondensed
open _root_.LightCondensed

noncomputable section

namespace Work.RESOL

set_option linter.style.haveILetI false

/-! ## Coordinates for an arbitrary index type -/

/-- The `j`-th coordinate of a small coproduct, for an arbitrary index type `J`: the map
`∐ X ⟶ X j` whose `k`-th component is the identity if `k = j` and zero otherwise. -/
def coordJ {C : Type*} [Category C] [HasZeroMorphisms C] {J : Type} (X : J → C)
    [HasCoproduct X] (j : J) : (∐ X) ⟶ X j := by
  classical
  exact Sigma.desc (fun k => if h : k = j then eqToHom (congrArg X h) else 0)

@[simp]
lemma coordJ_self {C : Type*} [Category C] [HasZeroMorphisms C] {J : Type} (X : J → C)
    [HasCoproduct X] (j : J) : Sigma.ι X j ≫ coordJ X j = 𝟙 (X j) := by
  classical
  rw [coordJ, Sigma.ι_comp_desc]
  simp

lemma coordJ_eq_zero_of_ne {C : Type*} [Category C] [HasZeroMorphisms C] {J : Type} (X : J → C)
    [HasCoproduct X] {k j : J} (h : k ≠ j) : Sigma.ι X k ≫ coordJ X j = 0 := by
  classical
  rw [coordJ, Sigma.ι_comp_desc]
  simp [h]

/-- Composing a morphism on the left of a `Pi.lift`: `p ≫ Pi.lift g = Pi.lift (p ≫ g ·)`. -/
lemma comp_Pi_lift {C : Type*} [Category C] {β : Type*} {f : β → C} [HasProduct f]
    {P Q : C} (p : P ⟶ Q) (g : (b : β) → Q ⟶ f b) :
    p ≫ Pi.lift g = Pi.lift (fun b => p ≫ g b) := by
  apply Pi.hom_ext
  intro b
  rw [Category.assoc, Pi.lift_comp_π, Pi.lift_comp_π]

/-- Two elements of `↥S`, for `S : Finset (Discrete ℕ)`, coincide as soon as their underlying
natural numbers do. -/
lemma as_eq_iff {S : Finset (Discrete ℕ)} (x y : ↥S) :
    (x : Discrete ℕ).as = (y : Discrete ℕ).as ↔ x = y := by
  constructor
  · intro h
    exact Subtype.ext (by
      rw [← Discrete.mk_as ((x : Discrete ℕ)), ← Discrete.mk_as ((y : Discrete ℕ)), h])
  · intro h; rw [h]

/-! ## The finite comparison map -/

/-- **The finite comparison map is a monomorphism.**  For a finite index type `β` and a family
`f : β → LightCondAb`, the map `∐ f ⟶ ∏ f` whose `b`-th component is the `b`-th coordinate
`coordJ f b` is a monomorphism.

The comparison map is the structure isomorphism of the biproduct `⨁ f`, composed of
`biproduct.isoCoproduct f` and `biproduct.isoProduct f`; in particular it has an explicit
two-sided inverse, so mono-ness is proved by cancellation instead of by instance search
(which is expensive in this large category). -/
lemma mono_finiteComparison {β : Type} [Fintype β] [DecidableEq β] (f : β → LightCondAb)
    [HasCoproduct f] [HasProduct f] :
    Mono (Pi.lift (fun b => coordJ f b)) := by
  haveI hb : HasBiproduct f := HasBiproduct.of_hasProduct f
  set e : (∐ f) ≅ (∏ᶜ f) := (biproduct.isoCoproduct f).symm ≪≫ biproduct.isoProduct f with he
  have key : Pi.lift (fun b => coordJ f b) = e.hom := by
    rw [he, Iso.trans_hom, Iso.symm_hom]
    apply Pi.hom_ext
    intro b
    rw [Pi.lift_comp_π, Category.assoc, biproduct.isoProduct_hom, Pi.lift_comp_π,
      biproduct.isoCoproduct_inv]
    apply Sigma.hom_ext
    intro c
    rw [coordJ, Sigma.ι_comp_desc, ← Category.assoc, Sigma.ι_comp_desc, biproduct.ι_π]
    by_cases h : c = b
    · subst h; simp
    · simp [h]
  rw [key]
  refine ⟨fun {Z} a b' hab => ?_⟩
  have h : a ≫ e.hom ≫ e.inv = b' ≫ e.hom ≫ e.inv := by
    rw [← Category.assoc, hab, Category.assoc]
  simpa only [Iso.hom_inv_id, Category.comp_id] using h

/-! ## The component of the comparison map at a finite set -/

/-- **Coordinate identity for the finite sub-coproducts.**  The composite of the leg of the
finite-subcoproduct cocone of `X` at `S` with the `t.as`-th coordinate of the coproduct `∐ X` is
the `t`-th coordinate of the finite family `x ↦ X x.as`: the composite picks out the summand
indexed by `t`, and all other summands are killed. -/
lemma finiteSubcoproductsCocone_desc_comp_coord (X : ℕ → LightCondAb) [HasCoproduct X]
    (S : Finset (Discrete ℕ)) (t : ↥S) :
    (Sigma.desc (fun s : ↥S => Sigma.ι X ((s : Discrete ℕ).as)) :
        (∐ fun x : ↥S => X ((x : Discrete ℕ).as)) ⟶ (∐ X)) ≫ coord X ((t : Discrete ℕ).as)
      = coordJ (fun x : ↥S => X ((x : Discrete ℕ).as)) t := by
  apply Sigma.hom_ext
  intro s
  rw [← Category.assoc, Sigma.ι_comp_desc]
  by_cases h : (s : Discrete ℕ).as = (t : Discrete ℕ).as
  · have hst : s = t := (as_eq_iff s t).mp h
    subst hst
    rw [Sigma_ι_coord_self, coordJ_self]
  · have hst : s ≠ t := fun h' => h ((as_eq_iff s t).mpr h')
    rw [coord_eq_zero_of_ne _ h, coordJ_eq_zero_of_ne _ hst]

/-- **The component of the comparison map out of a finite sub-coproduct is a monomorphism.**

Composing the component with the product projection `r := Pi.lift (fun t : ↥S => Pi.π X t.as)`
turns it into the finite comparison map `∐_{x ∈ S} X x.as ⟶ ∏_{x ∈ S} X x.as` of the finite
family `x ↦ X x.as`, which is a monomorphism by `mono_finiteComparison`; a morphism whose
composite with something is a monomorphism is itself a monomorphism. -/
lemma mono_finiteSubcoproductsCocone_comp (X : ℕ → LightCondAb) [HasCoproduct X] [HasProduct X]
    (S : Finset (Discrete ℕ)) :
    Mono ((CoproductsFromFiniteFiltered.finiteSubcoproductsCocone X).ι.app S
      ≫ Pi.lift (fun n : ℕ => coord X n)) := by
  show Mono ((Sigma.desc (fun s : ↥S => Sigma.ι X ((s : Discrete ℕ).as)) :
      (∐ fun x : ↥S => X ((x : Discrete ℕ).as)) ⟶ (∐ X))
      ≫ Pi.lift (fun n : ℕ => coord X n))
  let r : (∏ᶜ X) ⟶ (∏ᶜ fun t : ↥S => X ((t : Discrete ℕ).as)) :=
    Pi.lift (fun t : ↥S => Pi.π X ((t : Discrete ℕ).as))
  haveI hfin : Mono (Pi.lift (fun t : ↥S => coordJ (fun x : ↥S => X ((x : Discrete ℕ).as)) t)) :=
    mono_finiteComparison (fun x : ↥S => X ((x : Discrete ℕ).as))
  have hstep : Pi.lift (fun n : ℕ => coord X n) ≫ r
      = Pi.lift (fun t : ↥S => coord X ((t : Discrete ℕ).as)) := by
    show Pi.lift (fun n : ℕ => coord X n) ≫ Pi.lift (fun t : ↥S => Pi.π X ((t : Discrete ℕ).as))
      = Pi.lift (fun t : ↥S => coord X ((t : Discrete ℕ).as))
    rw [comp_Pi_lift]
    apply Pi.hom_ext
    intro t
    simp only [Pi.lift_comp_π]
  have hEq : ((Sigma.desc (fun s : ↥S => Sigma.ι X ((s : Discrete ℕ).as)) :
      (∐ fun x : ↥S => X ((x : Discrete ℕ).as)) ⟶ (∐ X))
      ≫ Pi.lift (fun n : ℕ => coord X n)) ≫ r
      = Pi.lift (fun t : ↥S => coordJ (fun x : ↥S => X ((x : Discrete ℕ).as)) t) := by
    rw [Category.assoc, hstep, comp_Pi_lift]
    apply Pi.hom_ext
    intro t
    rw [Pi.lift_comp_π, Pi.lift_comp_π, finiteSubcoproductsCocone_desc_comp_coord]
  haveI : Mono (((Sigma.desc (fun s : ↥S => Sigma.ι X ((s : Discrete ℕ).as)) :
      (∐ fun x : ↥S => X ((x : Discrete ℕ).as)) ⟶ (∐ X))
      ≫ Pi.lift (fun n : ℕ => coord X n)) ≫ r) := by
    rw [hEq]; exact hfin
  refine ⟨fun {Z} g h hgh => ?_⟩
  have h2 : g ≫ (((Sigma.desc (fun s : ↥S => Sigma.ι X ((s : Discrete ℕ).as)) :
      (∐ fun x : ↥S => X ((x : Discrete ℕ).as)) ⟶ (∐ X))
      ≫ Pi.lift (fun n : ℕ => coord X n)) ≫ r)
      = h ≫ (((Sigma.desc (fun s : ↥S => Sigma.ι X ((s : Discrete ℕ).as)) :
      (∐ fun x : ↥S => X ((x : Discrete ℕ).as)) ⟶ (∐ X))
      ≫ Pi.lift (fun n : ℕ => coord X n)) ≫ r) := by
    simp only [← Category.assoc, hgh]
  exact (cancel_mono _).mp h2

/-! ## The comparison map -/

/-- The canonical comparison map from a small coproduct of light condensed abelian groups to the
corresponding product is a monomorphism.  Equivalently: a morphism into such a coproduct all of
whose coordinates vanish is zero. -/
theorem mono_lift_coord (X : ℕ → LightCondAb) [HasCoproduct X] [HasProduct X] :
    Mono (Pi.lift (fun n : ℕ => coord X n)) := by
  haveI : IsConnected (Finset (Discrete ℕ)) := IsFiltered.isConnected _
  haveI hc₁ : IsColimit (CoproductsFromFiniteFiltered.finiteSubcoproductsCocone X) :=
    CoproductsFromFiniteFiltered.isColimitFiniteSubproductsCocone X
  -- the natural transformation from the finite sub-coproducts to the product
  let φ : CoproductsFromFiniteFiltered.liftToFinsetObj (Discrete.functor X) ⟶
      (Functor.const (Finset (Discrete ℕ))).obj (∏ᶜ X) :=
    (CoproductsFromFiniteFiltered.finiteSubcoproductsCocone X).ι ≫
      (Functor.const (Finset (Discrete ℕ))).map (Pi.lift (fun n : ℕ => coord X n))
  -- each component of `φ` is a monomorphism
  have hφ : ∀ S : Finset (Discrete ℕ), Mono (φ.app S) := by
    intro S
    show Mono ((CoproductsFromFiniteFiltered.finiteSubcoproductsCocone X).ι.app S
      ≫ Pi.lift (fun n : ℕ => coord X n))
    exact mono_finiteSubcoproductsCocone_comp X S
  haveI : ∀ S : Finset (Discrete ℕ), Mono (φ.app S) := hφ
  haveI : Mono φ := NatTrans.mono_of_mono_app φ
  -- the comparison map is the map induced on the colimits
  exact colim.map_mono' φ hc₁ (isColimitConstCocone (Finset (Discrete ℕ)) (∏ᶜ X))
    (Pi.lift (fun n : ℕ => coord X n)) (by
      intro S
      exact (Category.comp_id (φ.app S)).symm)

/-- The requested statement: `sigmaToPi A` is (by definition) `Pi.lift (fun m => coord A m)`. -/
theorem mono_sigmaToPi_light (A : ℕ → LightCondAb) [CategoryTheory.Limits.HasCoproduct A]
    [CategoryTheory.Limits.HasProduct A] : CategoryTheory.Mono (Work.RESOL.sigmaToPi A) :=
  mono_lift_coord A

end Work.RESOL
