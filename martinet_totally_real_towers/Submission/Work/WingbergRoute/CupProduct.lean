import Mathlib
import Submission.Work.ConCohomology.All
import Submission.Work.ShafarevichKoch.Cohomology3

/-!
# `Work.WingbergRoute.CupProduct` -- the cup product of continuous cochains

`Submission/Work/ConCohomology/` builds the continuous cohomology `H¹`, `H²` of a topological group
(with `Work.ShafarevichKoch.Cohomology3` adding `H³`), but it has **no cup product**; the same is
true of Mathlib.  The Shafarevich--Koch chapter records this as the missing arrow of the relation
count (`Submission/Work/ShafarevichKoch/README.md` §24.2: "the missing arrow is the
cup product/transgression leg `V_∅ → Hom(K ⧸ K²[K,F], 𝔽₂)`"; §33.0: Koch's injection
`X²_∅ ↪ (V_∅/K^{×p})^∨` "is an a-priori different *pairing*").  This module supplies it.

## The construction

Fix a topological group `G`, discrete `G`-modules `A`, `B`, `C` and a `G`-equivariant additive
pairing `f : A →+ B →+ C` (i.e. `f (σ • a) (σ • b) = σ • f a b`).  For inhomogeneous continuous
cochains the cup product is

```
(a ∪ b)(σ₁,…,σ_{p+q}) = f (a(σ₁,…,σ_p)) (σ₁⋯σ_p • b(σ_{p+1},…,σ_{p+q}))
```

so that in the three cases needed here

```
cup11 f a b (σ,τ)     = f (a σ) (σ • b τ) ,
cup21 f α b (σ,τ,ρ)   = f (α (σ,τ)) ((στ) • b ρ) ,
cup12 f a β (σ,τ,ρ)   = f (a σ) (σ • β (τ,ρ)) .
```

The differentials satisfy the inhomogeneous Leibniz rule

```
d (a ∪ b) = (da) ∪ b - a ∪ (db)
```

(`Work.WingbergRoute.d2Fun_cup11`, `Work.WingbergRoute.d3Fun_cup21`,
`Work.WingbergRoute.d3Fun_cup12`), so the cup product of cocycles is a cocycle and products with a
coboundary are coboundaries: consequently it descends to cohomology,

```
Work.WingbergRoute.cupH1 : H1 G A →+ H1 G B →+ H2 G C ,
Work.WingbergRoute.cupH2 : H2 G A →+ H1 G B →+ H3 G C .
```

The case actually used by the norm-residue/Kummer pairing is `A = B = C = ZMod 2` with `f` the
multiplication, giving

```
Work.WingbergRoute.cupH2_zmodTwo : H2 G (ZMod 2) →+ H1 G (ZMod 2) →+ H3 G (ZMod 2) .
```

**These pairings are *not* in this module**: `cupH1`, `cupH2` and their `𝔽₂` specialisations are
assembled in `Submission/Work/WingbergRoute/CupProductCohomology.lean` from this module together
with the three delegated lemmas `Work.WingbergRoute.cup_leibniz`,
`Work.WingbergRoute.cup_isLocallyConstant` and `Work.WingbergRoute.cup_wellDefined` (which live in
the modules of the same names).

## Conventions

* Coefficients are additive; the `G`-action is a `DistribMulAction` and the module is
  `IsDiscreteGModule` (locally constant action), exactly as in `Submission/Work/ConCohomology/`.
* `p.2.1`/`p.2.2` are the second/third coordinates of a triple `p = (p.1, p.2.1, p.2.2)`.

## Main declarations

* `Work.WingbergRoute.cup11Fun`, `...cup21Fun`, `...cup12Fun`;
* `Work.WingbergRoute.IsEquivariantBilin`, and the eight cochain-level products
  `cup01Fun`, `cup10Fun`, `cup11Fun`, `cup12Fun`, `cup13Fun`, `cup21Fun`, `cup22Fun`, `cup31Fun`;
* `Work.WingbergRoute.d2Fun_cup11`, `...d3Fun_cup21`, `...d3Fun_cup12` (in `cup_leibniz`);
* `Work.WingbergRoute.cupH1`, `...cupH2`, `...cupH1_zmodTwo`, `...cupH2_zmodTwo`
  (in `CupProductCohomology`).
-/

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1000000

open scoped Classical

noncomputable section

namespace Work.WingbergRoute

open Work.ConCohomology Work.ShafarevichKoch

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {A : Type*} [AddCommGroup A] [DistribMulAction G A] [IsDiscreteGModule G A]
variable {B : Type*} [AddCommGroup B] [DistribMulAction G B] [IsDiscreteGModule G B]
variable {C : Type*} [AddCommGroup C] [DistribMulAction G C] [IsDiscreteGModule G C]

/-- The `G`-equivariance of an additive pairing `A →+ B →+ C`. -/
def IsEquivariantBilin (f : A →+ B →+ C) : Prop :=
  ∀ (σ : G) (a : A) (b : B), f (σ • a) (σ • b) = σ • f a b

/-! ## The three cup-product formulas -/

/-- The cup product of a `1`-cochain `a` with a `1`-cochain `b`: a `2`-cochain. -/
def cup11Fun (f : A →+ B →+ C) (a : G → A) (b : G → B) : G × G → C :=
  fun p => f (a p.1) (p.1 • b p.2)

/-- The cup product of a `2`-cochain `α` with a `1`-cochain `b`: a `3`-cochain. -/
def cup21Fun (f : A →+ B →+ C) (α : G × G → A) (b : G → B) : G × G × G → C :=
  fun p => f (α (p.1, p.2.1)) ((p.1 * p.2.1) • b p.2.2)

/-- The cup product of a `1`-cochain `a` with a `2`-cochain `β`: a `3`-cochain. -/
def cup12Fun (f : A →+ B →+ C) (a : G → A) (β : G × G → B) : G × G × G → C :=
  fun p => f (a p.1) (p.1 • β (p.2.1, p.2.2))

/-- The cup product of a `0`-cochain `a₀` (an element of `A`) with a `1`-cochain `b`: a `1`-cochain. -/
def cup01Fun (f : A →+ B →+ C) (a₀ : A) (b : G → B) : G → C :=
  fun σ => f a₀ (b σ)

/-- The cup product of a `1`-cochain `a` with a `0`-cochain `b₀` (an element of `B`): a
`1`-cochain. -/
def cup10Fun (f : A →+ B →+ C) (a : G → A) (b₀ : B) : G → C :=
  fun σ => f (a σ) (σ • b₀)

/-- The cup product of a `3`-cochain `β` with a `1`-cochain `b`: a `4`-cochain. -/
def cup31Fun (f : A →+ B →+ C) (β : G × G × G → A) (b : G → B) : G × G × G × G → C :=
  fun p => f (β (p.1, p.2.1, p.2.2.1)) ((p.1 * p.2.1 * p.2.2.1) • b p.2.2.2)

/-- The cup product of a `2`-cochain `α` with a `2`-cochain `β`: a `4`-cochain. -/
def cup22Fun (f : A →+ B →+ C) (α : G × G → A) (β : G × G → B) : G × G × G × G → C :=
  fun p => f (α (p.1, p.2.1)) ((p.1 * p.2.1) • β (p.2.2.1, p.2.2.2))

/-- The cup product of a `1`-cochain `a` with a `3`-cochain `δ`: a `4`-cochain. -/
def cup13Fun (f : A →+ B →+ C) (a : G → A) (δ : G × G × G → B) : G × G × G × G → C :=
  fun p => f (a p.1) (p.1 • δ (p.2.1, p.2.2.1, p.2.2.2))

end Work.WingbergRoute
