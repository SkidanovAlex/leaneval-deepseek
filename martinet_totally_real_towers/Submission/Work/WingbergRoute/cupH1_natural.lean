import Mathlib
import Submission.Work.WingbergRoute.CupProductCohomology

/-!
# `Work.WingbergRoute.cupH1_natural` -- naturality of the cup product in the coefficients

The cup product `Work.WingbergRoute.cupH1 f hf : H¹(G,A) →+ H¹(G,B) →+ H²(G,C)` is natural in the
three coefficient modules: an equivariant additive map of triples `F : A → A'`, `F' : B → B'`,
`F'' : C → C'` commuting with a pair of equivariant additive pairings `f`, `f'` induces the
commutative square

```
H¹(G,A) × H¹(G,B) --cupH1 f--> H²(G,C)
    |  H1Map F × H1Map F'            |  H2Map F''
    v                                v
H¹(G,A') × H¹(G,B') --cupH1 f'--> H²(G,C')
```

The proof is the standard descent argument.  On *cochains* the identity is pointwise and purely
formal (`cochain2Map_cup11Co`): for `a : C¹(G,A)` and `b : C¹(G,B)`,

```
F'' (f (a σ) (σ • b τ)) = f' (F (a σ)) (σ • F' (b τ)),
```

using `h : F'' ∘ f = f' ∘ (F, F')` and the equivariance of `F'`.  Since `Z²Map`, `Z¹Map` and
`H²Map` are all defined by applying the coefficient map, this identity of cochains is already the
identity of `2`-cocycles (`Z2Map_cupZ11`), and the statement about `H²` follows by descending
through the two quotients `H¹ = Z¹ ⧸ B¹` (`cupH1_natural`).

## Main declarations

* `Work.WingbergRoute.cochain2Map_cup11Co` (the cochain-level identity);
* `Work.WingbergRoute.Z2Map_cupZ11` (naturality on `2`-cocycles);
* ★ `Work.WingbergRoute.cupH1_natural`.
-/

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

open scoped Classical

noncomputable section

namespace Work.WingbergRoute

open Work.ConCohomology

/-! ### The cochain-level identity -/

/-- **The cup product of `1`-cochains commutes with coefficient change.**  For a compatible triple
of equivariant coefficient maps `F`, `F'`, `F''`, the `2`-cochain `F'' ∘ (a ∪ b)` equals the cup
product of the images of `a` and `b`. -/
lemma cochain2Map_cup11Co {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {A A' B B' C C' : Type*}
    [AddCommGroup A] [DistribMulAction G A] [IsDiscreteGModule G A]
    [AddCommGroup A'] [DistribMulAction G A'] [IsDiscreteGModule G A']
    [AddCommGroup B] [DistribMulAction G B] [IsDiscreteGModule G B]
    [AddCommGroup B'] [DistribMulAction G B'] [IsDiscreteGModule G B']
    [AddCommGroup C] [DistribMulAction G C] [IsDiscreteGModule G C]
    [AddCommGroup C'] [DistribMulAction G C'] [IsDiscreteGModule G C']
    (F : EqHom G A A') (F' : EqHom G B B') (F'' : EqHom G C C')
    (f : A →+ B →+ C) (f' : A' →+ B' →+ C')
    (h : ∀ (a : A) (b : B), F'' (f a b) = f' (F a) (F' b))
    (a : Cochain1 G A) (b : Cochain1 G B) :
    cochain2Map F'' (cup11Co f a b) = cup11Co f' (cochain1Map F a) (cochain1Map F' b) := by
  ext p
  obtain ⟨σ, τ⟩ := p
  simp only [cochain2Map_apply, cup11Co_coe, cochain1Map_apply, cup11Fun]
  rw [h, EqHom.map_smul]

/-! ### Naturality on `2`-cocycles -/

/-- **Naturality of the cup product on `2`-cocycles.**  The coefficient map `F''` carries the cup
product of the `1`-cocycles `a`, `b` to the cup product of the images `Z¹Map F a`,
`Z¹Map F' b`. -/
lemma Z2Map_cupZ11 {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {A A' B B' C C' : Type*}
    [AddCommGroup A] [DistribMulAction G A] [IsDiscreteGModule G A]
    [AddCommGroup A'] [DistribMulAction G A'] [IsDiscreteGModule G A']
    [AddCommGroup B] [DistribMulAction G B] [IsDiscreteGModule G B]
    [AddCommGroup B'] [DistribMulAction G B'] [IsDiscreteGModule G B']
    [AddCommGroup C] [DistribMulAction G C] [IsDiscreteGModule G C]
    [AddCommGroup C'] [DistribMulAction G C'] [IsDiscreteGModule G C']
    (f : A →+ B →+ C) (hf : IsEquivariantBilin (G := G) f)
    (f' : A' →+ B' →+ C') (hf' : IsEquivariantBilin (G := G) f')
    (F : EqHom G A A') (F' : EqHom G B B') (F'' : EqHom G C C')
    (h : ∀ (a : A) (b : B), F'' (f a b) = f' (F a) (F' b))
    (a : Z1 G A) (b : Z1 G B) :
    Z2Map F'' (cupZ11 f hf a b) = cupZ11 f' hf' (Z1Map F a) (Z1Map F' b) := by
  apply Subtype.ext
  rw [Z2Map_coe]
  show cochain2Map F'' (cup11Co f (a : Cochain1 G A) (b : Cochain1 G B)) =
    ((cupZ11 f' hf' (Z1Map F a) (Z1Map F' b) : Z2 G C') : Cochain2 G C')
  rw [cochain2Map_cup11Co F F' F'' f f' h]
  congr 1

/-! ### Naturality on `H¹` -/

/-- **Naturality of the cup product on cocycle classes.**  The `H¹`-statement, verified on the
classes of two `1`-cocycles. -/
lemma cupH1_natural_mk {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {A A' B B' C C' : Type*}
    [AddCommGroup A] [DistribMulAction G A] [Work.ConCohomology.IsDiscreteGModule G A]
    [AddCommGroup A'] [DistribMulAction G A'] [Work.ConCohomology.IsDiscreteGModule G A']
    [AddCommGroup B] [DistribMulAction G B] [Work.ConCohomology.IsDiscreteGModule G B]
    [AddCommGroup B'] [DistribMulAction G B'] [Work.ConCohomology.IsDiscreteGModule G B']
    [AddCommGroup C] [DistribMulAction G C] [Work.ConCohomology.IsDiscreteGModule G C]
    [AddCommGroup C'] [DistribMulAction G C'] [Work.ConCohomology.IsDiscreteGModule G C']
    (F : Work.ConCohomology.EqHom G A A') (F' : Work.ConCohomology.EqHom G B B')
    (F'' : Work.ConCohomology.EqHom G C C')
    (f : A →+ B →+ C) (hf : Work.WingbergRoute.IsEquivariantBilin (G := G) f)
    (f' : A' →+ B' →+ C') (hf' : Work.WingbergRoute.IsEquivariantBilin (G := G) f')
    (h : ∀ (a : A) (b : B), F'' (f a b) = f' (F a) (F' b))
    (a : Work.ConCohomology.Z1 G A) (b : Work.ConCohomology.Z1 G B) :
    Work.ConCohomology.H2Map F'' (Work.WingbergRoute.cupH1 f hf (H1.mk a) (H1.mk b))
      = Work.WingbergRoute.cupH1 f' hf' (Work.ConCohomology.H1Map F (H1.mk a))
          (Work.ConCohomology.H1Map F' (H1.mk b)) := by
  rw [H1Map_mk, H1Map_mk, cupH1_mk_mk, cupH1_mk_mk, H2Map_mk]
  rw [Z2Map_cupZ11 f hf f' hf' F F' F'' h]

theorem cupH1_natural {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {A A' B B' C C' : Type*}
    [AddCommGroup A] [DistribMulAction G A] [Work.ConCohomology.IsDiscreteGModule G A]
    [AddCommGroup A'] [DistribMulAction G A'] [Work.ConCohomology.IsDiscreteGModule G A']
    [AddCommGroup B] [DistribMulAction G B] [Work.ConCohomology.IsDiscreteGModule G B]
    [AddCommGroup B'] [DistribMulAction G B'] [Work.ConCohomology.IsDiscreteGModule G B']
    [AddCommGroup C] [DistribMulAction G C] [Work.ConCohomology.IsDiscreteGModule G C]
    [AddCommGroup C'] [DistribMulAction G C'] [Work.ConCohomology.IsDiscreteGModule G C']
    (F : Work.ConCohomology.EqHom G A A') (F' : Work.ConCohomology.EqHom G B B')
    (F'' : Work.ConCohomology.EqHom G C C')
    (f : A →+ B →+ C) (hf : Work.WingbergRoute.IsEquivariantBilin (G := G) f)
    (f' : A' →+ B' →+ C') (hf' : Work.WingbergRoute.IsEquivariantBilin (G := G) f')
    (h : ∀ (a : A) (b : B), F'' (f a b) = f' (F a) (F' b))
    (x : Work.ConCohomology.H1 G A) (y : Work.ConCohomology.H1 G B) :
    Work.ConCohomology.H2Map F'' (Work.WingbergRoute.cupH1 f hf x y)
      = Work.WingbergRoute.cupH1 f' hf' (Work.ConCohomology.H1Map F x)
          (Work.ConCohomology.H1Map F' y) := by
  refine QuotientAddGroup.induction_on x ?_
  intro a
  refine QuotientAddGroup.induction_on y ?_
  intro b
  exact cupH1_natural_mk F F' F'' f hf f' hf' h a b

end Work.WingbergRoute
