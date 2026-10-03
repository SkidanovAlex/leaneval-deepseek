/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# A universe-flexible `K`-linear anti-automorphism, and its use for the mirror in JL §5

The bridges of `Submission/Work/ORBridgeTor/` (`Mirror.lean`, `HSwap.lean`,
`torsionFree_tensor_diagRight.lean`) transport Jaikin-Zapirain--Linton's Lemma 5.1′ and Lemma 5.2
from left modules to right modules by an *antipode* `ι` — a `K`-linear bijective
anti-endomorphism of `S = D(G)` with `ι (gen g) = (gen g)⁻¹`.  They consume
`Work.ORBridgeTor.AntiAut K S`, whose definition pins `K` and `S` to the **same universe**
(`AntiAut (K : Type u) (S : Type u)`), which is inconvenient when `S` is the division closure
`D E φK H : Subring E.U` living in the universe of the envelope `E`.

This file provides

* `Work.ORFinal.AntiAut' K S` — the same notion with `K : Type u` and `S : Type v` independent:
  a `K`-**linear equivalence** `S ≃ₗ[K] S` (not a ring equivalence!) together with the reversal of
  products and preservation of `1`;
* `Work.ORFinal.AntiAut'.toAntiAut` — the conversion to `Work.ORBridgeTor.AntiAut` when `K` and
  `S` do share a universe (which is the situation of `Work.ORFinal.RingDataDiv`, where `K` and the
  group are pinned to one universe by `Work.ORAssembly.LinData.toS`);
* `Work.ORFinal.DAlg` — the division closure `D E φK H` as a `K`-**subalgebra** of `E.U` (the
  bridge's `D` is a `Subring`, so `↥(D E φK H)` carries no `Algebra K` instance; the subalgebra
  structure is needed to state `AntiAut' K ↥(D E φK H)`).

**Warning (why the underlying map is a `LinearEquiv` and not a `RingEquiv`).**  An earlier version
of `AntiAut'` carried `toRingEquiv : S ≃+* S` together with `map_mul'`.  That is a *false*
definition: `toRingEquiv` being multiplicative in the usual direction and `map_mul'` reversing
products forces `f x * f y = f y * f x` for all `x y`, and surjectivity of `f` then forces `S` to
be commutative; `Work.ORBridgeTor.AntiAut` avoids the trap by using a bare `LinearEquiv`.  A
delegated child (`Submission/Work/ORFinal/Antiaut/antiAutOfStar.lean`) found this, with a
machine-checked refutation; the fix below is theirs.
-/
import Submission.Work.ORBridgeTor.Defs
import Submission.Work.ORFinal.AnalyticInput
import Submission.Work.ORBridgeLinnell.Countable

set_option autoImplicit false
set_option linter.unusedVariables false

universe u v

namespace Work.ORFinal

open Work.ORVonNeumann

/-- **The division closure `D E φK H` as a `K`-subalgebra of `U(G)`.**

`Work.ORBridgeLinnell.D E φK H` is a `Subring` of `E.U` which happens to contain the image of the
scalars (`Work.ORBridgeLinnell.algebraMap_mem_D`), so it is a `K`-subalgebra; the subalgebra
structure is what makes `↥(D E φK H)` an `Algebra K E.U`-subalgebra, and hence what makes
`Work.ORFinal.AntiAut' K ↥(…)` well-typed. -/
noncomputable def DAlg (K : Type u) [Field K] {G : Type v} [Group G]
    (E : StarRegularEnvelope G) (φK : K →+* ℂ) [Algebra K E.U] (H : Subgroup G) :
    Subalgebra K E.U where
  carrier := (Work.ORBridgeLinnell.D E φK H : Set E.U)
  mul_mem' := (Work.ORBridgeLinnell.D E φK H).mul_mem
  one_mem' := (Work.ORBridgeLinnell.D E φK H).one_mem
  add_mem' := (Work.ORBridgeLinnell.D E φK H).add_mem
  zero_mem' := (Work.ORBridgeLinnell.D E φK H).zero_mem
  algebraMap_mem' := Work.ORBridgeLinnell.algebraMap_mem_D E φK H

@[simp]
theorem mem_DAlg (K : Type u) [Field K] {G : Type v} [Group G]
    (E : StarRegularEnvelope G) (φK : K →+* ℂ) [Algebra K E.U] (H : Subgroup G) (x : E.U) :
    x ∈ DAlg K E φK H ↔ x ∈ Work.ORBridgeLinnell.D E φK H :=
  Iff.rfl

/-- **A `K`-linear anti-automorphism of a `K`-algebra `S`**, with the coefficient field `K` and `S`
in independent universes.  This is `Work.ORBridgeTor.AntiAut` without the same-universe
restriction; `AntiAut'.toAntiAut` converts back.

The underlying map is a `K`-**linear equivalence** `S ≃ₗ[K] S`, and the multiplicative axiom is
*reversed* (`map_mul'`), so this is an anti-endomorphism and not a ring homomorphism.  (Taking a
`RingEquiv` here would force `S` to be commutative — see the module docstring.) -/
structure AntiAut' (K : Type u) [CommSemiring K] (S : Type v) [Semiring S] [Algebra K S] where
  /-- the underlying `K`-linear equivalence -/
  toLinearEquiv : S ≃ₗ[K] S
  /-- `ι` reverses products -/
  map_mul' : ∀ a b : S, toLinearEquiv (a * b) = toLinearEquiv b * toLinearEquiv a
  /-- `ι` preserves `1` -/
  map_one' : toLinearEquiv 1 = 1

namespace AntiAut'

variable {K : Type u} [CommSemiring K] {S : Type v} [Semiring S] [Algebra K S]

instance instFunLike : FunLike (AntiAut' K S) S S where
  coe f := f.toLinearEquiv
  coe_injective f g h := by
    cases f
    cases g
    congr
    exact LinearEquiv.ext fun x => congrFun h x

@[simp] theorem coe_apply (f : AntiAut' K S) (x : S) : f x = f.toLinearEquiv x := rfl

theorem map_add (f : AntiAut' K S) (a b : S) : f (a + b) = f a + f b :=
  f.toLinearEquiv.map_add a b

theorem map_mul (f : AntiAut' K S) (a b : S) : f (a * b) = f b * f a := f.map_mul' a b

theorem map_one (f : AntiAut' K S) : f 1 = 1 := f.map_one'

theorem map_zero (f : AntiAut' K S) : f 0 = 0 := f.toLinearEquiv.map_zero

theorem map_smul (f : AntiAut' K S) (c : K) (x : S) : f (c • x) = c • f x :=
  f.toLinearEquiv.map_smul c x

theorem injective (f : AntiAut' K S) : Function.Injective f := f.toLinearEquiv.injective

theorem surjective (f : AntiAut' K S) : Function.Surjective f := f.toLinearEquiv.surjective

/-- The identity is a `K`-linear anti-automorphism of a commutative `K`-algebra.  (Recorded only
so that the structure is not obviously empty; the intended instances are `star` maps.) -/
def id (S : Type v) [CommSemiring S] [Algebra K S] : AntiAut' K S where
  toLinearEquiv := LinearEquiv.refl K S
  map_mul' a b := mul_comm a b
  map_one' := rfl

end AntiAut'

namespace AntiAut'

variable {K : Type u} [CommSemiring K] {S : Type u} [Semiring S] [Algebra K S]

/-- **The conversion to `Work.ORBridgeTor.AntiAut`** when `K` and `S` share a universe: the two
structures have literally the same fields. -/
def toAntiAut (f : AntiAut' K S) : Work.ORBridgeTor.AntiAut K S where
  toLinearEquiv := f.toLinearEquiv
  map_mul' := f.map_mul'
  map_one' := f.map_one'

@[simp] theorem toAntiAut_apply (f : AntiAut' K S) (x : S) :
    f.toAntiAut x = f x := rfl

end AntiAut'

end Work.ORFinal
