import Mathlib
import Submission.Work.ShafarevichKoch.Cohomology3
import Submission.Work.ConCohomology.Functoriality

/-!
# `Work.ShafarevichKoch.Cohomology3Map` -- coefficient change in degree `3`

`Submission/Work/ConCohomology/Functoriality.lean` gives the coefficient-change maps
`cochain1Map`, `cochain2Map`, `Z1Map`, `Z2Map`, `H1Map`, `H2Map` but stops at degree `2`,
because `ConCohomology` never built the cohomology in degree `3`.  This module completes the
picture for the degree built in `Cohomology3.lean`:

* `cochain3Map`, `cochain3Map_d2Hom` (naturality of `d²`),
* `Z3Map : Z³(G,A) →+ Z³(G,B)`,
* `H3Map : H³(G,A) →+ H³(G,B)`,

so that the long exact sequence of a coefficient sequence can be stated in degrees `0`--`3`
(the `H³`-terms of the sequence are `H3Map S.f`).

## Main declarations

* `Work.ShafarevichKoch.cochain3Map`, `cochain3Map_apply`, `cochain3Map_d2Hom`;
* `Work.ShafarevichKoch.Z3Map`, `Z3Map_coe`;
* `Work.ShafarevichKoch.H3Map`, `H3Map_mk`.
-/

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

open scoped Classical

noncomputable section

namespace Work.ShafarevichKoch

open Work.ConCohomology

section CoeffChange3

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {A B : Type*} [AddCommGroup A] [AddCommGroup B]
variable [DistribMulAction G A] [DistribMulAction G B]
variable [IsDiscreteGModule G A] [IsDiscreteGModule G B]

/-- Postcomposition with an equivariant coefficient map, on `3`-cochains. -/
def cochain3Map (F : EqHom G A B) : Cochain3 G A →+ Cochain3 G B :=
  LocallyConstant.mapAddMonoidHom F.toAddMonoidHom

@[simp] lemma cochain3Map_apply (F : EqHom G A B) (f : Cochain3 G A) (p : G × G × G) :
    cochain3Map F f p = F (f p) := rfl

/-- **Naturality of `d²` under coefficient change**: the square
`C²(A) --d²--> C³(A) --cochain3Map F--> C³(B)` commutes with
`C²(A) --cochain2Map F--> C²(B) --d²--> C³(B)`. -/
lemma cochain3Map_d2Hom (F : EqHom G A B) (u : Cochain2 G A) :
    cochain3Map F (d2Hom G A u) = d2Hom G B (cochain2Map F u) := by
  rw [d2Hom_cochain2Map]
  rfl

/-- **Naturality of `d³` under coefficient change**, at the level of plain functions. -/
lemma d3Fun_comp (F : EqHom G A B) (f : G × G × G → A) :
    d3Fun (G := G) (M := B) (fun q => F (f q)) =
      fun q => F (d3Fun (G := G) (M := A) f q) := by
  funext p
  obtain ⟨σ, τ, ρ, υ⟩ := p
  simp only [d3Fun_apply, EqHom.map_add, EqHom.map_sub, EqHom.map_smul]

/-- Coefficient change on `3`-cocycles. -/
def Z3Map (F : EqHom G A B) : Z3 G A →+ Z3 G B :=
  AddMonoidHom.codRestrict ((cochain3Map F).comp (Z3 G A).subtype) (Z3 G B) fun z => by
    rw [mem_Z3]
    ext p
    obtain ⟨σ, τ, ρ, υ⟩ := p
    show d3Fun (G := G) (M := B) (fun q => F ((z : Cochain3 G A) q)) (σ, τ, ρ, υ) = 0
    have hz : d3Fun (G := G) (M := A) (fun q => (z : Cochain3 G A) q) (σ, τ, ρ, υ) = 0 := by
      have h := congrFun (congrArg (fun w : Cochain4 G A => (w : G × G × G × G → A))
        (mem_Z3.mp z.2)) (σ, τ, ρ, υ)
      simpa using h
    rw [d3Fun_comp]
    show F (d3Fun (G := G) (M := A) (fun q => (z : Cochain3 G A) q) (σ, τ, ρ, υ)) = 0
    rw [hz, map_zero]

@[simp] lemma Z3Map_coe (F : EqHom G A B) (z : Z3 G A) :
    ((Z3Map F z : Z3 G B) : Cochain3 G B) = cochain3Map F (z : Cochain3 G A) := rfl

/-- Coefficient change on `H³`. -/
noncomputable def H3Map (F : EqHom G A B) : H3 G A →+ H3 G B :=
  QuotientAddGroup.map (B3' G A) (B3' G B) (Z3Map F) fun z hz => by
    show Z3Map F z ∈ B3' G B
    rw [mem_B3', B3, AddMonoidHom.mem_range] at hz ⊢
    obtain ⟨u, hu⟩ := hz
    refine ⟨cochain2Map F u, ?_⟩
    rw [Z3Map_coe, ← hu, ← cochain3Map_d2Hom]

@[simp] lemma H3Map_mk (F : EqHom G A B) (z : Z3 G A) :
    H3Map F (H3.mk z) = H3.mk (Z3Map F z) := rfl

end CoeffChange3

end Work.ShafarevichKoch
