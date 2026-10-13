import Mathlib
import Submission.Work.DSF1.Cech.CechComponents

/-!
# The coaugmentation of the Čech complex and the interface for the "unit case"

For a presheaf of modules `Q` on the opens of a scheme `X` and a family of opens
`U : ι → X.Opens`, the Čech complex `cechComplexFunctor U Q` is augmented by the
structure maps `Q(⊤) → Q(U i)`.

If one of the opens is "big enough" (e.g. if `U i₀ = ⊤`), the Čech complex is
acyclic in positive degrees and its `H⁰` is `Q(⊤)`.  We set up the coaugmentation
and state the two consequences that the rest of the development uses.

The precise hypothesis (see `IsIsoDeletion`) is that the restrictions
`Q (E n .obj x) → Q (E (n+1) .obj (insert i₀ x))` are isomorphisms; this holds
when `U i₀ = ⊤`, and it also holds after tensoring a structure sheaf with `R_f`
for `f = f i₀`.
-/

set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 800000

open CategoryTheory AlgebraicGeometry Opposite Limits
open scoped Simplicial BigOperators

universe u

namespace Work.DSF1.Cech

variable {X : Scheme.{u}} {S : Type u} [CommRing S] {ι : Type u} (U : ι → X.Opens)

/-- The Čech nerve of the family `U`. -/
noncomputable abbrev E : SimplicialObject (FormalCoproduct X.Opens) :=
  (FormalCoproduct.mk ι U).cech

/-- The insertion of the index `i₀` at position `0`. -/
noncomputable def insIdx (i₀ : ι) (n : ℕ) (x : (E U).obj (op ⦋n⦌) |>.I) :
    (E U).obj (op ⦋n+1⦌) |>.I :=
  Fin.cons i₀ x

/-- The objects whose product is the degree `n` term of the Čech complex. -/
noncomputable abbrev Eobj (n : ℕ) (x : (E U).obj (op ⦋n⦌) |>.I) : X.Opens :=
  (E U).obj (op ⦋n⦌) |>.obj x

/-- The presheaf value appearing in degree `n`. -/
noncomputable abbrev Qobj (Q : X.Opensᵒᵖ ⥤ ModuleCat S) (n : ℕ)
    (x : (E U).obj (op ⦋n⦌) |>.I) : ModuleCat S :=
  Q.obj (op (Eobj U n x))

/-- The hypothesis of the "unit case": the coface maps of the Čech nerve which insert
the index `i₀` are inverted by the presheaf `Q`.  Concretely, the restriction
`Q (E n .obj x) → Q (E (n+1) .obj (insert i₀ x))` is an isomorphism, and the
"empty" instance `Q(⊤) → Q(U i₀)` (which is the `⊤ = E (-1) .obj` case) is also an
isomorphism. -/
def IsIsoDeletion (Q : X.Opensᵒᵖ ⥤ ModuleCat S) (i₀ : ι) : Prop :=
  IsIso (Q.map (homOfLE (le_top : U i₀ ≤ ⊤)).op) ∧
    ∀ (n : ℕ) (x : (E U).obj (op ⦋n⦌) |>.I),
      IsIso (Q.map (((E U).map (SimplexCategory.δ 0).op).φ (insIdx U i₀ n x)).op)

/-- The coaugmentation `Q(⊤) → Č⁰` of the Čech complex. -/
noncomputable def coaug (Q : X.Opensᵒᵖ ⥤ ModuleCat S) :
    Q.obj (op ⊤) ⟶ ((cechComplexFunctor U).obj Q).X 0 :=
  Pi.lift (fun x => Q.map (homOfLE le_top).op)

end Work.DSF1.Cech
