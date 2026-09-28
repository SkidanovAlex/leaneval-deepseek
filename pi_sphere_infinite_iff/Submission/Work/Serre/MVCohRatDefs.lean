import Mathlib
import Submission.Work.Thom.Cohomology

/-!
# The rational relative Mayer–Vietoris maps

For a space `X`, subsets `A ⊆ X` and an open cover `U ∪ V = X`, the *rational relative
Mayer–Vietoris* long exact sequence reads

`⋯ ⟶ H^n(X,A;ℚ) --F--> H^n(U,U∩A;ℚ) ⊞ H^n(V,V∩A;ℚ) --G--> H^n(U∩V,U∩V∩A;ℚ) --δ--> H^{n+1}(X,A;ℚ) ⟶ ⋯`

This file only *defines* the two maps `F` (`mvF`) and `G` (`mvG`) that occur in it, in the
vocabulary of `Work.Thom.RelCoh` (relative singular cohomology of a pair), so that the exactness
statement (`Work.Serre.relCohMV_les_rat`, proved in `Submission/Work/Serre/MVCohRatLes.lean`) can be
stated without any `Classical.choose` opacity.

The `ℤ`-coefficient version of the whole development exists in the workspace
(`Submission/Work/Cohomology/relCohMV_les.lean`, `relCohMV_honest_les.lean`); the rational version is
what the cup-product arguments of the Serre area (`Work.StemsB.mixedCupC`,
`Work.Serre.ThomCylAt`) use.
-/

open CategoryTheory CategoryTheory.Limits

namespace Work.Serre

noncomputable section

variable (X : TopCat) (A U V : Set X)

/-- The `U`-term of the relative Mayer–Vietoris sequence. -/
abbrev mvCohU (n : ℕ) : ModuleCat ℚ := Work.Thom.RelCoh ℚ n ↥U {x : ↥U | (x : X) ∈ A}

/-- The `V`-term of the relative Mayer–Vietoris sequence. -/
abbrev mvCohV (n : ℕ) : ModuleCat ℚ := Work.Thom.RelCoh ℚ n ↥V {x : ↥V | (x : X) ∈ A}

/-- The `U ∩ V`-term of the relative Mayer–Vietoris sequence. -/
abbrev mvCohUV (n : ℕ) : ModuleCat ℚ :=
  Work.Thom.RelCoh ℚ n ↥(U ∩ V) {x : ↥(U ∩ V) | (x : X) ∈ A}

/-- The restriction of a relative class on `(X,A)` to the pair `(U, U ∩ A)`. -/
def mvRestrU (n : ℕ) : Work.Thom.RelCoh ℚ n X A ⟶ mvCohU X A U n :=
  Work.Thom.relCohMap (⟨Subtype.val, continuous_subtype_val⟩ : C(↥U, X)) _ _
    (fun _ hx => hx) ℚ n

/-- The restriction of a relative class on `(X,A)` to the pair `(V, V ∩ A)`. -/
def mvRestrV (n : ℕ) : Work.Thom.RelCoh ℚ n X A ⟶ mvCohV X A V n :=
  Work.Thom.relCohMap (⟨Subtype.val, continuous_subtype_val⟩ : C(↥V, X)) _ _
    (fun _ hx => hx) ℚ n

/-- The restriction from `(U, U ∩ A)` to `(U ∩ V, U ∩ V ∩ A)`. -/
def mvRestrUVU (n : ℕ) : mvCohU X A U n ⟶ mvCohUV X A U V n :=
  Work.Thom.relCohMap
    (⟨fun x => ⟨x.1, x.2.1⟩, by continuity⟩ : C(↥(U ∩ V), ↥U)) _ _
    (fun _ hx => hx) ℚ n

/-- The restriction from `(V, V ∩ A)` to `(U ∩ V, U ∩ V ∩ A)`. -/
def mvRestrUVV (n : ℕ) : mvCohV X A V n ⟶ mvCohUV X A U V n :=
  Work.Thom.relCohMap
    (⟨fun x => ⟨x.1, x.2.2⟩, by continuity⟩ : C(↥(U ∩ V), ↥V)) _ _
    (fun _ hx => hx) ℚ n

/-- The first map of the relative Mayer–Vietoris sequence, `ω ↦ (ω|_U, ω|_V)`. -/
def mvF (n : ℕ) : Work.Thom.RelCoh ℚ n X A ⟶ (mvCohU X A U n ⊞ mvCohV X A V n) :=
  biprod.lift (mvRestrU X A U n) (mvRestrV X A V n)

/-- The second map of the relative Mayer–Vietoris sequence,
`(ω₁, ω₂) ↦ ω₁|_{U∩V} − ω₂|_{U∩V}`. -/
def mvG (n : ℕ) : (mvCohU X A U n ⊞ mvCohV X A V n) ⟶ mvCohUV X A U V n :=
  ModuleCat.ofHom ((biprod.fst ≫ mvRestrUVU X A U V n).hom
    - (biprod.snd ≫ mvRestrUVV X A U V n).hom)

end

end Work.Serre
