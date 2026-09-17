import Mathlib.Algebra.Lie.UniversalEnveloping
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Algebra.Lie.SerreConstruction
import Mathlib.Data.Complex.Basic

noncomputable section

/-!
# From modules over the enveloping algebra back to Lie modules

`ChallengeDeps` (module `LeanEval.RepresentationTheory`) supplies the *forward* direction of the
dictionary between Lie modules and modules over the enveloping algebra: a
`LieModule R L M` extends canonically to a `Module (UniversalEnvelopingAlgebra R L) M`
(`lieModuleToEnvelopingModule`, given by lifting `LieModule.toEnd` along the universal property).

This file supplies the *reverse* direction, which the capstone theorem needs in order to turn the
highest-weight construction `Mω = U(e₈) ⧸ J(ω₁+ω₈)` (a module over `U = U(e₈)`) into the
`LieRingModule (LieAlgebra.e₈ ℂ) Mω` / `LieModule ℂ (LieAlgebra.e₈ ℂ) Mω` instances that the
existential statement `e8_irrep_tensor_square_decomp` asks for:

* `toLieRingModule` / `instLieRingModuleE8`: for any module `W` over `U(R,L)` (over `U = U(ℂ,e₈)`
  for the instance), the Lie algebra acts on `W` by left multiplication of the images
  `ι R x` (`x • m := (ι R x) • m`);
* `instLieModuleE8`: when `W` is also a ℂ-module compatibly (`IsScalarTower ℂ U W`), this is a
  ℂ-linear Lie action.

The bridge between the two directions is the identity `ι R ⁅x,y⁆ = ι R x * ι R y - ι R y * ι R x`
in `U(R,L)` (`ι_commutator_eq`), i.e. the fact that `ι` is a Lie homomorphism into the associative
ring `U` equipped with its commutator bracket.  Concretely, the action is a *Lie* action precisely
because of that identity: the Leibniz law `⁅x, ⁅y, m⁆⁆ = ⁅⁅x,y⁆, m⁆ + ⁅y, ⁅x, m⁆⁆` unfolds to
`(ιx·ιy) • m = (ι[x,y]) • m + (ιy·ιx) • m`.

The `LieModule` instance is provided only for the concrete pair `R = ℂ`, `L = LieAlgebra.e₈ ℂ`
(not as a generic `def`), because the type `LieModule R L W` carries `[LieRingModule L W]` as an
implicit instance parameter, which typeclass synthesis can only fill when `R` and `L` are
concrete; the generic *scalar-compatibility lemmas* (`algebraMap_smul_eq`,
`module_smul_comm_scalar`) and the Lie-ring-level construction `toLieRingModule` are proved for
arbitrary `R L W` and reused for the companion `g₂` problem.
-/

open UniversalEnvelopingAlgebra

namespace Submission.Enveloping

attribute [local instance 100] LieRing.ofAssociativeRing

variable {R L : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]

/-- In `U(R,L)`, the commutator of the `ι`-images of `x` and `y` is the `ι`-image of their Lie
bracket: `ι R x * ι R y - ι R y * ι R x = ι R ⁅x, y⁆`.  This is the defining identity of the
enveloping algebra (the universal property of `ι` as a Lie homomorphism into an associative ring
with the commutator Lie bracket). -/
@[simp] theorem ι_commutator_eq (x y : L) :
    ι R x * ι R y - ι R y * ι R x = ι R ⁅x, y⁆ := by
  rw [← Ring.lie_def]
  rw [← LieHom.map_lie (f := ι R)]

/-- The `R`-scalar action on a `U(R,L)`-module `W` agrees with the action of the corresponding
scalar in `U`: `(algebraMap R U c) • m = c • m`. -/
lemma algebraMap_smul_eq {W : Type*} [AddCommGroup W] [Module R W]
    [Module (UniversalEnvelopingAlgebra R L) W]
    [IsScalarTower R (UniversalEnvelopingAlgebra R L) W] (c : R) (m : W) :
    (algebraMap R (UniversalEnvelopingAlgebra R L) c) • m = c • m := by
  calc
    (algebraMap R (UniversalEnvelopingAlgebra R L) c) • m =
        (algebraMap R (UniversalEnvelopingAlgebra R L) c * (1 : UniversalEnvelopingAlgebra R L)) • m := by
      simp
    _ = ((c • (1 : UniversalEnvelopingAlgebra R L)) • m) := by rw [← Algebra.smul_def]
    _ = c • ((1 : UniversalEnvelopingAlgebra R L) • m) := by rw [IsScalarTower.smul_assoc]
    _ = c • m := by simp

/-- Scalars commute past module elements: `u • (c • m) = c • (u • m)` for every `u : U(R,L)`. -/
lemma module_smul_comm_scalar {W : Type*} [AddCommGroup W] [Module R W]
    [Module (UniversalEnvelopingAlgebra R L) W]
    [IsScalarTower R (UniversalEnvelopingAlgebra R L) W]
    (u : UniversalEnvelopingAlgebra R L) (c : R) (m : W) :
    u • (c • m) = c • (u • m) := by
  calc
    u • (c • m) = u • ((algebraMap R (UniversalEnvelopingAlgebra R L) c) • m) := by
      rw [← algebraMap_smul_eq (R := R) (L := L) (c := c) (m := m)]
    _ = (u * algebraMap R (UniversalEnvelopingAlgebra R L) c) • m := by rw [← mul_smul]
    _ = (algebraMap R (UniversalEnvelopingAlgebra R L) c * u) • m := by
      rw [Algebra.commutes]
    _ = (algebraMap R (UniversalEnvelopingAlgebra R L) c) • (u • m) := by rw [mul_smul]
    _ = c • (u • m) := by
      rw [algebraMap_smul_eq (R := R) (L := L) (c := c) (m := u • m)]

/-- The generic construction behind `instLieRingModuleE8`: a module over `U(R,L)` is a Lie module
of `L` with `x • m := (ι R x) • m`.  (Note `W`'s structure must be supplied when invoking this
`def`; the concrete `instLieRingModuleE8` below is the automatically-found instance for e₈.) -/
@[instance_reducible] def toLieRingModule (R L : Type*) [CommRing R] [LieRing L] [LieAlgebra R L]
    (W : Type*) [AddCommGroup W] [Module (UniversalEnvelopingAlgebra R L) W] :
    LieRingModule L W where
  bracket x m := (ι R x) • m
  add_lie x y m := by
    rw [map_add]
    exact add_smul (ι R x) (ι R y) m
  lie_add x m n := by
    exact smul_add (ι R x) m n
  leibniz_lie x y m := by
    calc
      (ι R x) • ((ι R y) • m) = (ι R x * ι R y) • m := by rw [← mul_smul]
      _ = (ι R ⁅x, y⁆ + ι R y * ι R x) • m := by
        congr 1
        rw [← ι_commutator_eq x y]
        abel
      _ = (ι R ⁅x, y⁆) • m + (ι R y * ι R x) • m := by rw [add_smul]
      _ = (ι R ⁅x, y⁆) • m + (ι R y) • ((ι R x) • m) := by rw [mul_smul]

/-- The enveloping algebra of `e₈` over `ℂ`. -/
abbrev U₈ : Type := UniversalEnvelopingAlgebra ℂ (LieAlgebra.e₈ ℂ)

/-- Any module over `U(e₈)` is canonically a Lie module of the Serre-constructed Lie algebra
`e₈ = LieAlgebra.e₈ ℂ`, with the action `x • m := (ι ℂ x) • m` of left multiplication. -/
instance instLieRingModuleE8 {W : Type*} [AddCommGroup W] [Module U₈ W] :
    LieRingModule (LieAlgebra.e₈ ℂ) W :=
  toLieRingModule ℂ (LieAlgebra.e₈ ℂ) W

/-- With a compatible ℂ-module structure, a module over `U(e₈)` is a genuine ℂ-linear Lie module
of `e₈`.  This is the instance that turns the highest-weight module `M(ω₁+ω₈) = U(e₈)/J` into a
Lie module of `LieAlgebra.e₈ ℂ`, the witness `V` of `e8_irrep_tensor_square_decomp`. -/
instance instLieModuleE8 {W : Type*} [AddCommGroup W] [Module ℂ W] [Module U₈ W]
    [IsScalarTower ℂ U₈ W] : LieModule ℂ (LieAlgebra.e₈ ℂ) W where
  smul_lie t x m := by
    change ((ι ℂ (t • x)) • m) = t • ((ι ℂ x) • m)
    have hι : ι ℂ (t • x) = t • (ι ℂ x) := by
      exact map_smul (ι ℂ) t x
    rw [hι]
    exact IsScalarTower.smul_assoc t (ι ℂ x) m
  lie_smul t x m := by
    exact module_smul_comm_scalar (R := ℂ) (L := LieAlgebra.e₈ ℂ) (u := ι ℂ x) (c := t) (m := m)

end Submission.Enveloping
