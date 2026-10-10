import Mathlib
import ChallengeDeps

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme MotivicInvariants Order

/-- `φ` is an isomorphism at `x`: some partial isomorphism representing `φ` has `x` in its source
(the paper's complement of `Ex(φ)`). -/
def IsIsoAt {X Y : Scheme.{0}} [IrreducibleSpace X] [IrreducibleSpace Y]
    (φ : X.BirationalMap Y) (x : X) : Prop :=
  ∃ i : X.PartialIso Y, x ∈ i.source ∧ i.toRationalMap = φ.hom

/-- Codimension-one points of `X` at which `φ` is not an isomorphism (exceptional divisors). -/
def exDiv {X Y : Scheme.{0}} [IrreducibleSpace X] [IrreducibleSpace Y]
    (φ : X.BirationalMap Y) : Set X :=
  {x | coheight x = 1 ∧ ¬ IsIsoAt φ x}

/-- The structure map `𝕜 → κ(x)` for a scheme over `Spec 𝕜`. -/
noncomputable def resMap (𝕜 : Type) [Field 𝕜] (X : Scheme.{0}) [X.Over (Spec (.of 𝕜))] (x : X) :
    𝕜 →+* X.residueField x :=
  ((Scheme.ΓSpecIso (CommRingCat.of 𝕜)).inv ≫ (X ↘ Spec (.of 𝕜)).appTop ≫
    X.presheaf.germ ⊤ x trivial ≫ X.residue x).hom

/-- `κ(x) ≅ κ(z)` as `𝕜`-algebras, i.e. the closures of `x` and `z` are birational over `𝕜`. -/
def ResEquiv (𝕜 : Type) [Field 𝕜] {X Z : Scheme.{0}} [X.Over (Spec (.of 𝕜))]
    [Z.Over (Spec (.of 𝕜))] (x : X) (z : Z) : Prop :=
  ∃ e : X.residueField x ≃+* Z.residueField z, e.toRingHom.comp (resMap 𝕜 X x) = resMap 𝕜 Z z

/-- Number of exceptional divisors of `φ` whose birational class is that of `z`. -/
noncomputable def excCount (𝕜 : Type) [Field 𝕜] {X Y Z : Scheme.{0}} [IrreducibleSpace X]
    [IrreducibleSpace Y] [X.Over (Spec (.of 𝕜))] [Z.Over (Spec (.of 𝕜))] (z : Z)
    (φ : X.BirationalMap Y) : ℕ :=
  Set.ncard {x | x ∈ exDiv φ ∧ ResEquiv 𝕜 x z}

/-- The `[κ(z)]`-coefficient of the Lin–Shinder invariant `c(φ) ∈ ℤ[Bir_{n-1}/𝕜]`. -/
noncomputable def cInv (𝕜 : Type) [Field 𝕜] {X Y Z : Scheme.{0}} [IrreducibleSpace X]
    [IrreducibleSpace Y] [X.Over (Spec (.of 𝕜))] [Y.Over (Spec (.of 𝕜))]
    [Z.Over (Spec (.of 𝕜))] (z : Z) (φ : X.BirationalMap Y) : ℤ :=
  (excCount 𝕜 z φ.symm : ℤ) - excCount 𝕜 z φ
