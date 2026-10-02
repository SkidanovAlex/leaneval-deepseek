import Mathlib

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The vocabulary of the rational Hurewicz chapter: torsion and "isomorphism mod torsion"

Area **RATHUREWICZ** (`Submission/Work/RatHurewicz/`), whose target is the drive's contract
`Work.Drive.RationalHurewiczStable` (`Submission/Work/Drive/RationalHurewicz.lean`).

This first module is *algebraic* and has no topological input: it fixes the notion of a *torsion
element* of a group (an element with a positive power equal to `1`, additively an element with a
non-zero integer multiple equal to `0`) and the notion of a homomorphism that is an *isomorphism
modulo torsion* — a homomorphism whose kernel consists of torsion elements and whose cokernel is
torsion.  The latter is the form in which the rational Hurewicz theorem is used by the consumers of
this area (THOM, STEMS): `f` is an isomorphism modulo torsion exactly when `f ⊗ ℚ` is bijective,
and the kernel/cokernel formulation avoids the workspace's competing `ℤ`-module structures on the
homology objects (see `Submission/Work/Stems/PLAN.md` §9.1).

Nothing here mentions homotopy or homology: the topological content of the chapter is in
`Work.RatHurewicz.RelHomotopy`, `Work.RatHurewicz.Excision` and `Work.RatHurewicz.SerreHurewicz`;
the algebraic API of this module (in particular the *five lemma mod torsion* of
`Submission/Work/RatHurewicz/TorsionAPI.lean`) is what every exact-sequence chase below uses.
-/

namespace Work.RatHurewicz

noncomputable section

/-- **A torsion element of a group**: an element some positive power of which is `1`. -/
def IsTorsionElt {G : Type*} [Group G] (g : G) : Prop := ∃ N : ℕ, 0 < N ∧ g ^ N = 1

/-- **A torsion element of an additive commutative group**: an element with a non-zero natural
multiple equal to `0`. -/
def IsTorsionEltAdd {A : Type*} [AddCommGroup A] (a : A) : Prop := ∃ N : ℕ, 0 < N ∧ N • a = 0

/-- **A torsion group**. -/
def IsTorsionGroup (G : Type*) [Group G] : Prop := ∀ g : G, IsTorsionElt g

/-- **A torsion additive group**. -/
def IsTorsionGroupAdd (A : Type*) [AddCommGroup A] : Prop := ∀ a : A, IsTorsionEltAdd a

/-- **A homomorphism that is an isomorphism modulo torsion** (multiplicative form): its kernel is
contained in the torsion elements, and every element of the target has a non-zero power in the
image.  Equivalently `f ⊗ ℚ` is an isomorphism. -/
def IsModTorsionHom {G H : Type*} [CommGroup G] [CommGroup H] (f : G →* H) : Prop :=
  (∀ g : G, f g = 1 → IsTorsionElt g) ∧ (∀ h : H, ∃ N : ℕ, 0 < N ∧ ∃ g : G, f g = h ^ N)

/-- **A homomorphism that is an isomorphism modulo torsion** (additive form): its kernel consists
of torsion elements and its cokernel is torsion. -/
def IsModTorsionIso {A B : Type*} [AddCommGroup A] [AddCommGroup B] (f : A →+ B) : Prop :=
  (∀ a : A, f a = 0 → IsTorsionEltAdd a) ∧ (∀ b : B, ∃ N : ℕ, 0 < N ∧ ∃ a : A, f a = N • b)

end

end Work.RatHurewicz
