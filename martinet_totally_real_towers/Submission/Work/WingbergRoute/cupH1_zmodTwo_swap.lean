import Mathlib
import Submission.Work.WingbergRoute.CupProductCohomology

/-!
# `Work.WingbergRoute.cupH1_zmodTwo_swap` -- the `𝔽₂` cup product on `H¹` is commutative

`Submission/Work/WingbergRoute/CupProductCohomology.lean` constructs the cup product

```
Work.WingbergRoute.cupH1_zmodTwo : H¹(G,𝔽₂) →+ H¹(G,𝔽₂) →+ H²(G,𝔽₂)
```

for a topological group `G` acting trivially on `𝔽₂`.  This module proves the classical
*graded commutativity* of the cup product in bidegree `(1,1)`: since the coefficient ring `𝔽₂`
has characteristic `2`, the sign `(-1)^{1·1} = -1` of the general Eilenberg--Zilber formula is
invisible, so the cup product on `H¹` is **commutative**:

```
Work.WingbergRoute.cupH1_zmodTwo htriv a b = Work.WingbergRoute.cupH1_zmodTwo htriv b a .
```

## The mathematics of the proof

With a trivial action on `𝔽₂`, a `1`-cocycle `α : Z¹(G,𝔽₂)` is exactly a group homomorphism
`G → (𝔽₂,+)`: the cocycle condition `α(στ) = α σ + σ • α τ` becomes `α(στ) = α σ + α τ`.
For two such cocycles the inhomogeneous cup product is `(α ∪ β)(σ,τ) = α σ · β τ`, and the
`2`-cochain

```
κ σ = α σ · β σ
```

satisfies, by the homomorphism property and characteristic `2`,

```
d¹κ (σ,τ) = σ • κ τ - κ(στ) + κ σ = α σ · β τ - β σ · α τ = (α ∪ β)(σ,τ) - (β ∪ α)(σ,τ) ,
```

i.e. `α ∪ β - β ∪ α` is a coboundary.  Passing to cohomology gives the commutativity.  (The
underlying polynomial identity `x w - z y = -(y w - (x+y)(z+w) + x z)` is the `𝔽₂`-shadow of
the cup-`1` product identity `α ∪ β + β ∪ α = d(α · β)`, whose sign disappears in
characteristic `2`.)

## Main declarations

* `Work.WingbergRoute.zmodTwoMul_apply_eq_mul` (the multiplication pairing, pointwise);
* `Work.WingbergRoute.charTwo_cup11_identity` (the polynomial identity in a ring of char two);
* `Work.WingbergRoute.cup11Fun_swap_eq_d1` (the pointwise cocycle computation);
* ★ `Work.WingbergRoute.cupH1_zmodTwo_swap`.
-/

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

open scoped Classical

noncomputable section

namespace Work.WingbergRoute

open Work.ConCohomology

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable [DistribMulAction G (ZMod 2)] [Work.ConCohomology.IsDiscreteGModule G (ZMod 2)]

/-- The `𝔽₂`-valued multiplication pairing of `CupProductCohomology.lean`, pointwise. -/
@[simp] lemma zmodTwoMul_apply_eq_mul (a b : ZMod 2) : zmodTwoMul a b = a * b := rfl

/-- The polynomial identity behind the commutativity of the cup product: in a commutative ring of
characteristic `2`, and writing `x w - z y` for the difference of the two cup products and
`y w - (x+y)(z+w) + x z` for the negative of the differential of `κ`, the two agree. -/
lemma charTwo_cup11_identity {R : Type*} [CommRing R] [CharP R 2] (x y z w : R) :
    x * w - z * y = -(y * w - (x + y) * (z + w) + x * z) := by
  rw [CharTwo.sub_eq_add, CharTwo.neg_eq, CharTwo.sub_eq_add]
  rw [add_mul, mul_add, mul_add]
  linear_combination (-1 : R) * CharTwo.add_self_eq_zero (y * w) +
    (-1 : R) * CharTwo.add_self_eq_zero (x * z)

/-- **The cocycle computation.**  For two `𝔽₂`-valued `1`-cocycles `α`, `β` (with trivial action)
the difference `α ∪ β - β ∪ α` of the two cup products is the differential of `σ ↦ α σ * β σ`. -/
lemma cup11Fun_swap_eq_d1 (htriv : ∀ (σ : G) (x : ZMod 2), σ • x = x)
    (α β : Z1 G (ZMod 2)) (σ τ : G) :
    (cup11Fun zmodTwoMul (α : G → ZMod 2) (β : G → ZMod 2)) (σ, τ)
      - (cup11Fun zmodTwoMul (β : G → ZMod 2) (α : G → ZMod 2)) (σ, τ)
    = -d1Fun (M := ZMod 2) (fun ρ => (α : G → ZMod 2) ρ * (β : G → ZMod 2) ρ) (σ, τ) := by
  have hα : (α : G → ZMod 2) (σ * τ) = (α : G → ZMod 2) σ + (α : G → ZMod 2) τ := by
    have hc : IsCocycle1 (α : G → ZMod 2) := mem_Z1.mp α.2
    rw [hc σ τ, htriv σ ((α : G → ZMod 2) τ)]
  have hβ : (β : G → ZMod 2) (σ * τ) = (β : G → ZMod 2) σ + (β : G → ZMod 2) τ := by
    have hc : IsCocycle1 (β : G → ZMod 2) := mem_Z1.mp β.2
    rw [hc σ τ, htriv σ ((β : G → ZMod 2) τ)]
  simp only [cup11Fun, d1Fun_apply, zmodTwoMul_apply_eq_mul, htriv, hα, hβ]
  exact charTwo_cup11_identity ((α : G → ZMod 2) σ) ((α : G → ZMod 2) τ)
    ((β : G → ZMod 2) σ) ((β : G → ZMod 2) τ)

/-- **The `𝔽₂` cup product on `H¹` is commutative.**  This is the bidegree `(1,1)` case of the
graded commutativity of the cup product, where the sign `-1` is invisible because the
coefficients have characteristic `2`. -/
theorem cupH1_zmodTwo_swap {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [DistribMulAction G (ZMod 2)] [Work.ConCohomology.IsDiscreteGModule G (ZMod 2)]
    (htriv : ∀ (σ : G) (x : ZMod 2), σ • x = x) (a b : Work.ConCohomology.H1 G (ZMod 2)) :
    Work.WingbergRoute.cupH1_zmodTwo htriv a b = Work.WingbergRoute.cupH1_zmodTwo htriv b a := by
  have key : ∀ α β : Z1 G (ZMod 2),
      H2.mk (cupZ11 zmodTwoMul (isEquivariantBilin_zmodTwoMul htriv) α β)
        = H2.mk (cupZ11 zmodTwoMul (isEquivariantBilin_zmodTwoMul htriv) β α) := by
    intro α β
    refine (H2.mk_eq_mk_iff _ _).mpr ?_
    rw [mem_B2', mem_B2]
    refine ⟨⟨fun σ => (α : G → ZMod 2) σ * (β : G → ZMod 2) σ, ?_⟩, ?_⟩
    · exact (α.1.isLocallyConstant).mul (β.1.isLocallyConstant)
    · ext p
      obtain ⟨σ, τ⟩ := p
      show d1Fun (M := ZMod 2) (fun ρ => (α : G → ZMod 2) ρ * (β : G → ZMod 2) ρ) (σ, τ)
        = (cup11Fun zmodTwoMul (α : G → ZMod 2) (β : G → ZMod 2)) (σ, τ)
            - (cup11Fun zmodTwoMul (β : G → ZMod 2) (α : G → ZMod 2)) (σ, τ)
      rw [cup11Fun_swap_eq_d1 (G := G) htriv α β σ τ, CharTwo.neg_eq]
  have key2 : ∀ α β : Z1 G (ZMod 2),
      (cupH1 zmodTwoMul (isEquivariantBilin_zmodTwoMul htriv) (H1.mk α)) (H1.mk β)
        = (cupH1 zmodTwoMul (isEquivariantBilin_zmodTwoMul htriv) (H1.mk β)) (H1.mk α) := by
    intro α β
    rw [cupH1_mk_mk, cupH1_mk_mk]
    exact key α β
  show (cupH1 zmodTwoMul (isEquivariantBilin_zmodTwoMul htriv) a) b
      = (cupH1 zmodTwoMul (isEquivariantBilin_zmodTwoMul htriv) b) a
  refine QuotientAddGroup.induction_on a (fun α => ?_)
  refine QuotientAddGroup.induction_on b (fun β => ?_)
  exact key2 α β

end Work.WingbergRoute
