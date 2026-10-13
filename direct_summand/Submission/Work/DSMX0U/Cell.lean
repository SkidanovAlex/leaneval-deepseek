import Mathlib
import Submission.Work.DSMap.Mix
import Submission.Work.DSMX0U.Basic

/-!
# DSMX0U — the cell construction: the state of the tower

This file contains the state of the (infinite, downward) **cell construction** which produces a
bounded-above complex of finitely generated free modules quasi-isomorphic to a given complex `C`
whose cohomology is finitely generated and vanishes above a degree.

## Why a tower is needed

A complex with finitely generated cohomology in bounded degrees cannot in general be modelled by a
complex whose terms only carry *two* consecutive degrees of information per cohomology class:
a two-term free presentation `0 → K → F → H^i(C) → 0` exists if and only if
`projective dimension (H^i(C)) ≤ 1`, which fails over a general Noetherian ring (e.g.
`H^0(C) = 𝔽₂` over `A = ℤ[X]`, or `k` over `k[x,y]/(x²,xy,y²)`).  The model must therefore be an
infinite (downward) free resolution, i.e. a tower of cells.

## The state

`Cell A C c₀ q` is the state of the construction *in the interval of degrees `[q - 1, q]`*: the
current term of the model is in cohomological degree `q - 1`, and its predecessor (the next term
up) is in degree `q`.  It carries

* `gen` and `rel`, finitely generated free modules, whose product (the `pairMod`) is the current
  term `G` in degree `q - 1`; the differential `d : G ⟶ Gprev` kills the `gen`-component and sends
  the `rel`-component into `Kprev` along `cov`;
* a map `σ : gen ⟶ Z^(q-1)(C)` from the generators to the cycles of `C` in degree `q - 1`, hitting
  every class of `H^(q-1)(C)` modulo boundaries (`hσ`);
* a map `φ : G ⟶ C^(q-1)` given by `(x, y) ↦ iCycles (σ x) + β y`, where `β` is a lift of
  `φprev ∘ cov` along the differential `C.d (q-1) q`;
* `Gprev`, the term of the model in degree `q`, with `φprev : Gprev ⟶ C^q`;
* `Kprev ⊆ Gprev`, the *excess kernel* of the next level up, covered by `rel` via `cov` (`hcov`).

## Why the parameter is the *upper* degree

The step of the construction (`Work.DSMX0U.stepCell`) replaces `q` by `q - 1` and re-uses the
current term as the new predecessor: the new `φprev` is literally `s.φ`, which has type
`s.G ⟶ C.X (q - 1)`, i.e. exactly the type required of the new `φprev` (`Gprev ⟶ C.X (q - 1)`,
since the new parameter is `q - 1`).  Had the state been parameterised by the *current* degree `d`,
the new `φprev` would have had to map into `C.X ((d - 1) + 1)`, which is only *propositionally*
equal to `C.X d`: the step would then need an `eqToHom`-transport, and every identity about the
tower would become propositional instead of definitional.  With the present convention the step is
a pure structure literal and all the identities of `Work.DSMX0U.tower` hold by `rfl`.

The excess kernel `Cell.K s`, the submodule of cycles of `G` whose image in `H^(q-1)(C)` vanishes,
is the datum that the next level of the tower has to cover: indeed the range of the differential of
the next cell is exactly `Cell.K s`, which is what makes the tower produce the right cohomology.

The base state, the step, and the recursion producing the tower are in
`Submission/Work/DSMX0U/Cells.lean`.
-/

namespace Work.DSMX0U

open CategoryTheory Limits

universe a

variable (A : Type a) [CommRing A]

/-- The element `c₀ 1`, transported to degree `d` (this is only used when the degree `d` is `0`,
where the two degrees coincide). -/
noncomputable def coaugElem {C : CochainComplex (ModuleCat.{a} A) ℤ}
    (c₀ : ModuleCat.of A A ⟶ C.X 0) (d : ℤ) (h : d = 0) : ↥(C.X d) :=
  (eqToHom (congrArg C.X h.symm)).hom (c₀.hom 1)

/-- The quotient map of the cokernel of the boundary map in degree `i`, used to express the
"excess kernel". -/
noncomputable def bdryQ (C : CochainComplex (ModuleCat.{a} A) ℤ) (i : ℤ) :
    ↥(C.X i) →ₗ[A] (↥(C.X i) ⧸ LinearMap.range (C.d (i - 1) i).hom) :=
  Submodule.mkQ _

/-- **The state of the cell construction in degrees `[q - 1, q]`.**  The current term is in
cohomological degree `q - 1`, its predecessor (the term of the model one degree *higher*) is
`Gprev` in degree `q`, and `Kprev` is the excess kernel there which this level has to cover. -/
structure Cell (C : CochainComplex (ModuleCat.{a} A) ℤ) (c₀ : ModuleCat.of A A ⟶ C.X 0)
    (q : ℤ) where
  /-- the generators in degree `q - 1` -/
  gen : ModuleCat.{a} A
  /-- the relations covering the excess kernel of the next level up -/
  rel : ModuleCat.{a} A
  freeGen : Module.Free A gen
  finiteGen : Module.Finite A gen
  freeRel : Module.Free A rel
  finiteRel : Module.Finite A rel
  /-- the generators, mapped to cycles of `C` in degree `q - 1` -/
  σ : gen ⟶ C.cycles (q - 1)
  /-- the generators hit the cohomology (cycles modulo boundaries) -/
  hσ : ∀ z : ↥(C.X (q - 1)), (C.d (q - 1) q).hom z = 0 →
    ∃ g : ↥gen, (C.iCycles (q - 1)).hom (σ.hom g) - z ∈
      LinearMap.range (C.d ((q - 1) - 1) (q - 1)).hom
  /-- the coaugmentation generator, when the current degree is `0` -/
  hcoaugσ : ∀ (h : q - 1 = 0), ∃ g : ↥gen,
    (C.iCycles (q - 1)).hom (σ.hom g) = coaugElem A c₀ (q - 1) h
  /-- the term in degree `q` -/
  Gprev : ModuleCat.{a} A
  /-- the excess kernel of the next level up (covered by `rel`) -/
  Kprev : Submodule A ↥Gprev
  /-- the relations, mapped onto the excess kernel of the next level up -/
  cov : ↥rel →ₗ[A] ↥Kprev
  hcov : Function.Surjective cov
  /-- the next level's map into `C` -/
  φprev : Gprev ⟶ C.X q
  /-- the lift of the chain-map condition on the relations -/
  β : ↥rel →ₗ[A] ↥(C.X (q - 1))
  hβ : ∀ x : ↥rel, (C.d (q - 1) q).hom (β x) = φprev.hom (cov x)

variable {C : CochainComplex (ModuleCat.{a} A) ℤ} {c₀ : ModuleCat.of A A ⟶ C.X 0}
variable {q : ℤ}

/-- The term of the model in degree `q - 1`. -/
noncomputable abbrev Cell.G (s : Cell A C c₀ q) : ModuleCat.{a} A := pairMod A s.gen s.rel

/-- The differential of the model, from degree `q - 1` to degree `q`. -/
noncomputable def Cell.dHom (s : Cell A C c₀ q) : ↥s.gen × ↥s.rel →ₗ[A] ↥s.Gprev :=
  LinearMap.coprod (M := ↥s.gen) (M₂ := ↥s.rel) (M₃ := ↥s.Gprev)
    (0 : ↥s.gen →ₗ[A] ↥s.Gprev) ((s.Kprev).subtype ∘ₗ s.cov)

/-- The differential of the model, as a morphism of modules. -/
noncomputable def Cell.d (s : Cell A C c₀ q) : s.G A ⟶ s.Gprev :=
  ModuleCat.ofHom (s.dHom A)

/-- The map of the model into `C`, in degree `q - 1`. -/
noncomputable def Cell.φHom (s : Cell A C c₀ q) : ↥s.gen × ↥s.rel →ₗ[A] ↥(C.X (q - 1)) :=
  LinearMap.coprod (M := ↥s.gen) (M₂ := ↥s.rel) (M₃ := ↥(C.X (q - 1)))
    ((C.iCycles (q - 1)).hom ∘ₗ s.σ.hom) s.β

/-- The map of the model into `C`, as a morphism of modules. -/
noncomputable def Cell.φ (s : Cell A C c₀ q) : s.G A ⟶ C.X (q - 1) :=
  ModuleCat.ofHom (s.φHom A)

/-- **The excess kernel** in degree `q - 1`: the cycles of `G` whose image in `H^(q-1)(C)`
vanishes.  This is what the next level of the tower covers. -/
noncomputable def Cell.K (s : Cell A C c₀ q) : Submodule A ↥(s.G A) :=
  LinearMap.ker (s.dHom A) ⊓ LinearMap.ker ((bdryQ A C (q - 1)).comp (s.φHom A))

section StepData

variable {C : CochainComplex (ModuleCat.{a} A) ℤ} {c₀ : ModuleCat.of A A ⟶ C.X 0}

/-- **The data produced by one step of the cell construction**: the generators in degree
`(q - 1) - 1` (the current degree of the cell produced by the step, which is one below the given
cell `s : Cell A C c₀ q`) together with the coaugmentation generator when that degree is `0`, and
the relations covering the excess kernel `Cell.K s` of the given cell. -/
structure StepData (s : Cell A C c₀ q) where
  /-- the generators in degree `(q - 1) - 1` -/
  gen : ModuleCat.{a} A
  /-- the relations covering `Cell.K s` -/
  rel : ModuleCat.{a} A
  freeGen : Module.Free A gen
  finiteGen : Module.Finite A gen
  freeRel : Module.Free A rel
  finiteRel : Module.Finite A rel
  /-- the generators, mapped to cycles of `C` -/
  σ : gen ⟶ C.cycles ((q - 1) - 1)
  /-- the generators hit the cohomology (cycles modulo boundaries) -/
  hσ : ∀ z : ↥(C.X ((q - 1) - 1)), (C.d ((q - 1) - 1) (q - 1)).hom z = 0 →
    ∃ g : ↥gen, (C.iCycles ((q - 1) - 1)).hom (σ.hom g) - z ∈
      LinearMap.range (C.d (((q - 1) - 1) - 1) ((q - 1) - 1)).hom
  /-- the coaugmentation generator, when the new degree is `0` -/
  hcoaugσ : ∀ (h : (q - 1) - 1 = 0), ∃ g : ↥gen,
    (C.iCycles ((q - 1) - 1)).hom (σ.hom g) = coaugElem A c₀ ((q - 1) - 1) h
  /-- the relations, mapped onto the excess kernel of level `s` -/
  cov : ↥rel →ₗ[A] ↥(s.K A)
  hcov : Function.Surjective cov
  /-- the lift of the chain-map condition on the relations -/
  β : ↥rel →ₗ[A] ↥(C.X ((q - 1) - 1))
  hβ : ∀ x : ↥rel, (C.d ((q - 1) - 1) (q - 1)).hom (β x) =
    s.φHom A ((cov x : ↥(s.K A)) : ↥(s.G A))

/-- **The step of the cell construction**: the cell in degrees `[(q - 1) - 1, q - 1]` produced
from the cell in degrees `[q - 1, q]` together with its `StepData`.  This is a pure structure
literal: every field of the new cell is literally a field of the old cell or of the step data,
with no transport.

It is marked `@[reducible]` so that the definitional identities between consecutive levels of the
tower (`Work.DSMX0U.tower_Gprev`, `Work.DSMX0U.tower_Kprev`, `Work.DSMX0U.tower_φprev`) hold by
`rfl`. -/
@[reducible]
noncomputable def stepCell (s : Cell A C c₀ q) (sd : StepData A s) :
    Cell A C c₀ (q - 1) where
  gen := sd.gen
  rel := sd.rel
  freeGen := sd.freeGen
  finiteGen := sd.finiteGen
  freeRel := sd.freeRel
  finiteRel := sd.finiteRel
  σ := sd.σ
  hσ := sd.hσ
  hcoaugσ := sd.hcoaugσ
  Gprev := s.G A
  Kprev := s.K A
  cov := sd.cov
  hcov := sd.hcov
  φprev := s.φ A
  β := sd.β
  hβ := sd.hβ

end StepData

end Work.DSMX0U
