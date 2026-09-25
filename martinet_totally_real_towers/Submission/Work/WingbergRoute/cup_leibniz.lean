import Mathlib
import Submission.Work.WingbergRoute.CupProduct

/-!
# `Work.WingbergRoute.cup_leibniz` -- the Leibniz rule for the cup product of cochains

`Submission/Work/WingbergRoute/CupProduct.lean` defines the cup product of inhomogeneous
continuous cochains (`cup11Fun`, `cup21Fun`, `cup12Fun`, ...) and announces, without proving,
the **Leibniz rule** for its differentials:

```
d (a ∪ b) = (d a) ∪ b ± a ∪ (d b) .
```

This module supplies those three identities (`d2Fun_cup11`, `d3Fun_cup21`, `d3Fun_cup12`) and
packages them as the single statement `Work.WingbergRoute.cup_leibniz`.  They are what makes the
cup product descend to cohomology: on cocycles the right-hand side vanishes, and on a coboundary
in one variable the product is again a coboundary, giving the pairings
`H¹ × H¹ → H²` and `H² × H¹ → H³` of `CupProduct.lean`.

The computations are pure bookkeeping: expand the three differentials
`d¹(σ,τ) = σ•fτ - f(στ) + fσ`, `d²(σ,τ,ρ) = σ•f(τ,ρ) - f(στ,ρ) + f(σ,τρ) - f(σ,τ)`,
`d³(σ,τ,ρ,υ) = σ•f(τ,ρ,υ) - f(στ,ρ,υ) + f(σ,τρ,υ) - f(σ,τ,ρυ) + f(σ,τ,ρ)`, use the additivity of
`f` in each variable, the `G`-equivariance `f (σ•a) (σ•b) = σ • f a b`, and normalise the
`G`-actions with `mul_smul`/`mul_assoc`; `abel` finishes the first identity.

## Main declarations

* `Work.WingbergRoute.d2Fun_cup11`, `...d3Fun_cup21`, `...d3Fun_cup12`;
* `Work.WingbergRoute.cup_leibniz`.
-/

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option linter.style.longLine false
set_option maxHeartbeats 1000000

open scoped Classical

noncomputable section

namespace Work.WingbergRoute

open Work.ConCohomology Work.ShafarevichKoch

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {A : Type*} [AddCommGroup A] [DistribMulAction G A] [IsDiscreteGModule G A]
variable {B : Type*} [AddCommGroup B] [DistribMulAction G B] [IsDiscreteGModule G B]
variable {C : Type*} [AddCommGroup C] [DistribMulAction G C] [IsDiscreteGModule G C]

/-- **Leibniz rule in bidegree `(1,1)`**: `d²(a ∪ b) = (d¹a) ∪ b - a ∪ (d¹b)`. -/
theorem d2Fun_cup11 (f : A →+ B →+ C) (hf : IsEquivariantBilin (G := G) f)
    (a : G → A) (b : G → B) :
    d2Fun (cup11Fun f a b)
      = cup21Fun f (d1Fun (M := A) a) b - cup12Fun f a (d1Fun (M := B) b) := by
  funext p
  obtain ⟨σ, τ, ρ⟩ := p
  simp only [d2Fun_apply, cup11Fun, cup21Fun, cup12Fun, d1Fun_apply, Pi.sub_apply,
    map_add, map_sub, smul_sub, smul_add, AddMonoidHom.add_apply, AddMonoidHom.sub_apply]
  have hfe : ∀ (σ : G) (x : A) (y : B), σ • (f x y) = f (σ • x) (σ • y) :=
    fun σ x y => (hf σ x y).symm
  simp only [hfe, ← mul_smul]
  abel

/-- **Leibniz rule in bidegree `(2,1)`**: `d³(α ∪ b) = (d²α) ∪ b + α ∪ (d¹b)`. -/
theorem d3Fun_cup21 (f : A →+ B →+ C) (hf : IsEquivariantBilin (G := G) f)
    (α : G × G → A) (b : G → B) :
    d3Fun (cup21Fun f α b)
      = cup31Fun f (d2Fun (M := A) α) b + cup22Fun f α (d1Fun (M := B) b) := by
  funext p
  obtain ⟨σ, τ, ρ, υ⟩ := p
  simp only [d3Fun_apply, cup21Fun, cup31Fun, cup22Fun, d2Fun_apply, d1Fun_apply, Pi.add_apply,
    map_add, map_sub, smul_sub, smul_add, AddMonoidHom.add_apply, AddMonoidHom.sub_apply]
  have hfe : ∀ (σ : G) (x : A) (y : B), σ • (f x y) = f (σ • x) (σ • y) :=
    fun σ x y => (hf σ x y).symm
  simp only [hfe, ← mul_smul, mul_assoc]
  abel

/-- **Leibniz rule in bidegree `(1,2)`**: `d³(a ∪ β) = (d¹a) ∪ β - a ∪ (d²β)`. -/
theorem d3Fun_cup12 (f : A →+ B →+ C) (hf : IsEquivariantBilin (G := G) f)
    (a : G → A) (β : G × G → B) :
    d3Fun (cup12Fun f a β)
      = cup22Fun f (d1Fun (M := A) a) β - cup13Fun f a (d2Fun (M := B) β) := by
  funext p
  obtain ⟨σ, τ, ρ, υ⟩ := p
  simp only [d3Fun_apply, cup12Fun, cup22Fun, cup13Fun, d1Fun_apply, d2Fun_apply, Pi.sub_apply,
    map_add, map_sub, smul_sub, smul_add, AddMonoidHom.add_apply, AddMonoidHom.sub_apply]
  have hfe : ∀ (σ : G) (x : A) (y : B), σ • (f x y) = f (σ • x) (σ • y) :=
    fun σ x y => (hf σ x y).symm
  simp only [hfe, ← mul_smul]
  abel

/-- **The Leibniz rule for the cup product of continuous cochains**, in the three bidegrees
`(1,1)`, `(2,1)` and `(1,2)`:

```
d²(a ∪ b) = (d¹a) ∪ b - a ∪ (d¹b) ,
d³(α ∪ b) = (d²α) ∪ b + α ∪ (d¹b) ,
d³(a ∪ β) = (d¹a) ∪ β - a ∪ (d²β) .
```

Consequently the cup product of cocycles is a cocycle and the cup product of a cocycle with a
coboundary is a coboundary; this is what allows `CupProduct.lean` to pass to cohomology. -/
theorem cup_leibniz {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {A : Type*} [AddCommGroup A] [DistribMulAction G A] [Work.ConCohomology.IsDiscreteGModule G A]
    {B : Type*} [AddCommGroup B] [DistribMulAction G B] [Work.ConCohomology.IsDiscreteGModule G B]
    {C : Type*} [AddCommGroup C] [DistribMulAction G C] [Work.ConCohomology.IsDiscreteGModule G C]
    (f : A →+ B →+ C) (hf : Work.WingbergRoute.IsEquivariantBilin (G := G) f) :
    (∀ (a : G → A) (b : G → B),
      Work.ConCohomology.d2Fun (Work.WingbergRoute.cup11Fun f a b) =
        Work.WingbergRoute.cup21Fun f (Work.ConCohomology.d1Fun (M := A) a) b
          - Work.WingbergRoute.cup12Fun f a (Work.ConCohomology.d1Fun (M := B) b)) ∧
    (∀ (α : G × G → A) (b : G → B),
      Work.ShafarevichKoch.d3Fun (Work.WingbergRoute.cup21Fun f α b) =
        Work.WingbergRoute.cup31Fun f (Work.ConCohomology.d2Fun (M := A) α) b
          + Work.WingbergRoute.cup22Fun f α (Work.ConCohomology.d1Fun (M := B) b)) ∧
    (∀ (a : G → A) (β : G × G → B),
      Work.ShafarevichKoch.d3Fun (Work.WingbergRoute.cup12Fun f a β) =
        Work.WingbergRoute.cup22Fun f (Work.ConCohomology.d1Fun (M := A) a) β
          - Work.WingbergRoute.cup13Fun f a (Work.ConCohomology.d2Fun (M := B) β)) :=
  ⟨fun a b => d2Fun_cup11 f hf a b,
   fun α b => d3Fun_cup21 f hf α b,
   fun a β => d3Fun_cup12 f hf a β⟩

end Work.WingbergRoute
