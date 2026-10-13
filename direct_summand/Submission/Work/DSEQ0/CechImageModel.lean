import Mathlib
import Submission.Work.DSMap.Map
import Submission.Work.DSF1.Cech.CechComponents

/-!
# The Čech complex, seen through the images of its tuples

`DSMap.cech A X f U` is Mathlib's Čech complex of the presheaf `𝒪_X` (as a presheaf of
`A`-modules) along the family `U : ι → X.Opens`: in degree `n` it is the product, over *all*
maps `x : Fin (n + 1) → ι`, of the sections of `𝒪_X` on `⋂ₐ U (x a)`.

The term attached to `x` depends only on the *image* of `x`, but not definitionally.  This file
provides:

* `WS U S`, the intersection of the opens `U i` for `i ∈ S`, and `coeff A X f U S`, the
  corresponding module of sections;
* `res`, the restriction map between these modules for `S ⊆ T`;
* `termIso`, the (canonical) identification of the Čech term of `x` with the coefficient module
  of `Set.range x`;
* `comp A X f U n y`, the composite of the projection onto the `y`-th component and that
  identification: a linear map `Č^n ⟶ coeff (Set.range y)`;
* `termIso_conj`: the crucial computation that the Čech differential, *conjugated* by these
  identifications, is the map `res` — i.e. that for tuples with the same image the differential
  acts as the identity.

These are the tools with which the image-size filtration of `Č` is run: the graded pieces are
the "surjection complexes" with *definitionally* constant coefficients, whose vanishing above
the size of the index set is `Work.DSEQ0.surjCech_vanishing`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

open CategoryTheory AlgebraicGeometry Limits Opposite
open scoped Simplicial BigOperators

universe u

namespace Work.DSEQ0

variable {A : Type u} [CommRing A] {X : Scheme.{u}} {ι : Type u} {f : X ⟶ Spec (.of A)}

/-- The intersection of the opens `U i` for `i ∈ S`, as an element of `X.Opens`. -/
noncomputable abbrev WS (U : ι → X.Opens) (S : Set ι) : X.Opens := ⨅ i ∈ S, U i

theorem WS_mono {U : ι → X.Opens} {S T : Set ι} (h : S ⊆ T) : WS U T ≤ WS U S :=
  le_iInf₂ fun i hi => iInf₂_le i (h hi)

theorem WS_anti {U : ι → X.Opens} : Antitone (WS U) := fun _ _ h => WS_mono h

/-- **The open on which the Čech term of the tuple `x` lives is the intersection over the image
of `x`.** -/
theorem pi_comp_eq_WS (U : ι → X.Opens) (n : ℕ) (x : Fin (n + 1) → ι) :
    (∏ᶜ (fun a => U (x a))) = WS U (Set.range x) := by
  have h1 : (∏ᶜ fun a : Fin (n + 1) => U (x a)) = ⨅ a, U (x a) := by
    change limit (Discrete.functor fun a : Fin (n + 1) => U (x a)) = _
    rw [CategoryTheory.Limits.CompleteLattice.limit_eq_iInf]
    exact le_antisymm (le_iInf fun a => iInf_le _ (Discrete.mk a)) (le_iInf fun d => iInf_le _ d.as)
  rw [h1]
  exact le_antisymm
    (le_iInf₂ fun i hi => by obtain ⟨a, rfl⟩ := hi; exact iInf_le _ a)
    (le_iInf fun a => iInf₂_le (x a) (Set.mem_range_self a))

/-- The coefficient module of the Čech complex at an *image set* `S`. -/
noncomputable abbrev coeff (A : Type u) [CommRing A] (X : Scheme.{u}) (f : X ⟶ Spec (.of A))
    {ι : Type u} (U : ι → X.Opens) (S : Set ι) : ModuleCat.{u} A :=
  (DSMap.cechPresheaf A X f).obj (op (WS U S))

/-- The restriction map, in the image-set description: for `S ⊆ T` the open `WS U T` is
contained in `WS U S`, hence the restriction `𝒪(WS U S) ⟶ 𝒪(WS U T)`. -/
noncomputable def res (A : Type u) [CommRing A] (X : Scheme.{u}) (f : X ⟶ Spec (.of A))
    {ι : Type u} (U : ι → X.Opens) (S T : Set ι) (h : S ⊆ T) :
    coeff A X f U S ⟶ coeff A X f U T :=
  (DSMap.cechPresheaf A X f).map (homOfLE (WS_mono h)).op

theorem res_self (A : Type u) [CommRing A] (X : Scheme.{u}) (f : X ⟶ Spec (.of A))
    {ι : Type u} (U : ι → X.Opens) (S : Set ι) (h : S ⊆ S) :
    res A X f U S S h = 𝟙 (coeff A X f U S) := by
  unfold res
  rw [show homOfLE (WS_mono h) = 𝟙 (WS U S) from homOfLE_refl _]
  simp

theorem res_comp (A : Type u) [CommRing A] (X : Scheme.{u}) (f : X ⟶ Spec (.of A))
    {ι : Type u} (U : ι → X.Opens) {S T V : Set ι} (h : S ⊆ T) (h' : T ⊆ V) :
    res A X f U S T h ≫ res A X f U T V h' = res A X f U S V (h.trans h') := by
  unfold res
  rw [← Functor.map_comp]
  congr 1

/-- The identification of the Čech term of the tuple `x` with the coefficient module of its
image. -/
noncomputable def termIso (A : Type u) [CommRing A] (X : Scheme.{u}) (f : X ⟶ Spec (.of A))
    {ι : Type u} (U : ι → X.Opens) (n : ℕ) (x : Fin (n + 1) → ι) :
    (DSMap.cechPresheaf A X f).obj (op (∏ᶜ (fun a => U (x a)))) ≅ coeff A X f U (Set.range x) :=
  (DSMap.cechPresheaf A X f).mapIso ((eqToIso (pi_comp_eq_WS U n x)).symm.op)

/-- The `y`-th component of a cochain of the Čech complex, transported to the coefficient module
of the image of `y`. -/
noncomputable def comp (A : Type u) [CommRing A] (X : Scheme.{u}) (f : X ⟶ Spec (.of A))
    {ι : Type u} (U : ι → X.Opens) (n : ℕ) (y : Fin (n + 1) → ι) :
    (DSMap.cech A X f U).X n ⟶ coeff A X f U (Set.range y) :=
  Pi.π (fun x : Fin (n + 1) → ι =>
      (DSMap.cechPresheaf A X f).obj (op (∏ᶜ (fun a => U (x a))))) y ≫
    (termIso A X f U n y).hom

theorem range_succAbove_subset {n : ℕ} (y : Fin (n + 2) → ι) (k : Fin (n + 2)) :
    Set.range (y ∘ Fin.succAbove k) ⊆ Set.range y :=
  fun _ ⟨a, ha⟩ => ⟨Fin.succAbove k a, ha⟩

/-- **The conjugated component of the Čech differential.**  For `y : Fin (n+2) → ι` and
`k : Fin (n+2)`, the conjugation of the `k`-th Čech component at `y` by the identifications
`termIso` is the map `res` between the coefficient modules of `Set.range (y ∘ δ_k)` and
`Set.range y`.  (This is the statement that the coefficients of the Čech complex are constant on
tuples with the same image.) -/
theorem termIso_conj (A : Type u) [CommRing A] (X : Scheme.{u}) (f : X ⟶ Spec (.of A))
    {ι : Type u} (U : ι → X.Opens) (n : ℕ) (y : Fin (n + 2) → ι) (k : Fin (n + 2)) :
    (termIso A X f U n (y ∘ Fin.succAbove k)).inv ≫
        ((DSMap.cechPresheaf A X f).map
          (((FormalCoproduct.mk ι U).cech.map (SimplexCategory.δ k).op).φ y).op) ≫
        (termIso A X f U (n+1) y).hom
      = res A X f U (Set.range (y ∘ Fin.succAbove k)) (Set.range y)
          (range_succAbove_subset y k) := by
  simp only [termIso, res, Functor.mapIso_hom, Functor.mapIso_inv]
  rw [← Functor.map_comp, ← Functor.map_comp]
  congr 1

end Work.DSEQ0
