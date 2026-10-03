/-
# Node N4: virtual torsion-freeness and local indicability

This is the definitional core of the subproject `Work.ORLocInd`, one of the areas needed by the
formalisation of Jaikin-Zapirain--Linton, *On the coherence of one-relator groups and their group
algebras* (Annals of Math. 201 (3) 2025).

The paper uses two properties of one-relator groups:

* **virtual torsion-freeness** (Fischer--Karrass--Solitar, 1972): every one-relator group has a
  torsion-free subgroup of finite index;
* **local indicability of torsion-free subgroups** (Brodskii 1980; Howie 2000, Corollary 3.2):
  every torsion-free subgroup of a one-relator group is locally indicable.

The definitions below are the vocabulary of that area.  The main results are in
`Submission/Work/ORLocInd/Main.lean`.

Conventions established here (they matter for the rest of the subproject):

* `Group.LocallyIndicable G` is stated exactly as in the route design: every nontrivial finitely
  generated subgroup of `G` admits a surjection onto `Multiplicative ℤ`.
* `Work.ORLocInd.IsTorsionFree G` means *`G` has no nontrivial element of finite order*.  Note that
  this is **weaker** than Mathlib's `IsMulTorsionFree`, which asks instead that all power maps
  `x ↦ x ^ n` (`n ≠ 0`) be injective; `IsMulTorsionFree` implies `IsTorsionFree`
  (`IsTorsionFree.of_isMulTorsionFree`), but not conversely (the Klein bottle group
  `⟨a, b | a ^ 2 = b ^ 2⟩` is torsion-free, is a one-relator group, yet `x ↦ x ^ 2` is not
  injective in it).  `IsTorsionFree` is the notion used by FKS/Brodskii, and it is the notion for
  which "virtually torsion-free" is true for one-relator groups; the statement with
  `IsMulTorsionFree` would be *false* (it fails already for `ℤ`).
* A `RootPresentation G` is a presentation `⟨X | u ^ l⟩` of `G` with `l ≥ 1` and `u` not a proper
  power: the presentation shape in which the Magnus--Karrass--Solitar torsion theory is available.
-/
import ChallengeDeps
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.GroupTheory.Index
import Mathlib.GroupTheory.Schreier
import Mathlib.GroupTheory.Torsion
import Mathlib.GroupTheory.FreeGroup.NielsenSchreier
import Mathlib.GroupTheory.FreeGroup.CyclicallyReduced
import Mathlib.GroupTheory.PresentedGroup
import Mathlib.GroupTheory.HNNExtension
import Mathlib.GroupTheory.Coprod.Basic
import Mathlib.Algebra.Group.Subgroup.Basic

set_option autoImplicit false

universe u

namespace Work.ORLocInd

/-! ### Local indicability -/

/-- A group is *indicable* if it admits a surjective homomorphism onto the infinite cyclic group,
written multiplicatively as `Multiplicative ℤ`. -/
def Group.Indicable (G : Type*) [Group G] : Prop :=
  ∃ f : G →* Multiplicative ℤ, Function.Surjective f

/-- A group is *locally indicable* if all of its nontrivial finitely generated subgroups are
indicable.  This is verbatim the definition used in the route design (node N4). -/
def Group.LocallyIndicable (G : Type*) [Group G] : Prop :=
  ∀ H : Subgroup G, H.FG → H ≠ ⊥ → ∃ f : H →* Multiplicative ℤ, Function.Surjective f

/-- `Group.LocallyIndicable` phrased with `Group.Indicable`. -/
theorem Group.locallyIndicable_iff (G : Type*) [Group G] :
    Group.LocallyIndicable G ↔ ∀ H : Subgroup G, H.FG → H ≠ ⊥ → Group.Indicable H :=
  Iff.rfl

/-! ### Torsion-freeness and its virtual forms -/

/-- A group is *torsion-free* if its only element of finite order is the identity.

This is the group-theoretic notion used by FKS and Brodskii; it is weaker than Mathlib's
`IsMulTorsionFree` (see the module docstring). -/
def IsTorsionFree (G : Type*) [Group G] : Prop := ∀ g : G, IsOfFinOrder g → g = 1

/-- A group is *virtually torsion-free* if it has a normal torsion-free subgroup of finite index. -/
def VirtuallyTorsionFree (G : Type*) [Group G] : Prop :=
  ∃ G' : Subgroup G, G'.Normal ∧ G'.FiniteIndex ∧ IsTorsionFree G'

/-- A group is *virtually locally indicable* if it has a normal locally indicable subgroup of
finite index. -/
def VirtuallyLocallyIndicable (G : Type*) [Group G] : Prop :=
  ∃ G' : Subgroup G, G'.Normal ∧ G'.FiniteIndex ∧ Group.LocallyIndicable G'

/-- **Brodskii's theorem** (Brodskii 1984; Howie 2000, Corollary 3.2) in the form used by the paper:
every torsion-free subgroup of a one-relator group is locally indicable. -/
def BrodskiiHowieInput (G : Type*) [Group G] : Prop :=
  ∀ H : Subgroup G, IsTorsionFree H → Group.LocallyIndicable H

/-! ### Proper powers and root presentations -/

/-- `w` is a *proper power* if `w = v ^ m` for some `v ≠ 1` and `m ≥ 2`. -/
def IsProperPower {G : Type*} [Group G] (w : G) : Prop :=
  ∃ (v : G) (_ : v ≠ 1) (m : ℕ), 2 ≤ m ∧ w = v ^ m

/-- A *root presentation* of a group `G` is a one-relator presentation `⟨X | u ^ l⟩` in which
`u` is not a proper power and `l ≥ 1`.

Every one-relator group admits one: if the defining relator is a proper power, replace it by a root
of maximal exponent; if the defining relator is not a proper power, take `l = 1`.  This is the
presentation shape in which the Magnus--Karrass--Solitar torsion theorem applies. -/
structure RootPresentation (G : Type u) [Group G] where
  /-- the generating set -/
  α : Type u
  /-- the root of the defining relator -/
  u : FreeGroup α
  /-- the exponent of the defining relator -/
  l : ℕ
  /-- the exponent is positive -/
  one_le_l : 1 ≤ l
  /-- the root is not a proper power in the free group -/
  not_properPower : ¬ IsProperPower u
  /-- `G` is the presented group `⟨X | u ^ l⟩` -/
  equiv : PresentedGroup ({u ^ l} : Set (FreeGroup α)) ≃* G

namespace RootPresentation

variable {G : Type u} [Group G]

/-- The image in `G` of the root `u` of a root presentation. -/
def rootElem (P : RootPresentation G) : G :=
  P.equiv (PresentedGroup.mk ({P.u ^ P.l} : Set (FreeGroup P.α)) P.u)

/-- The defining relator of a root presentation is trivial in `G`. -/
@[simp]
theorem rootElem_pow (P : RootPresentation G) : P.rootElem ^ P.l = 1 := by
  have h : P.rootElem ^ P.l
      = P.equiv (PresentedGroup.mk ({P.u ^ P.l} : Set (FreeGroup P.α)) (P.u ^ P.l)) := by
    rw [rootElem, ← map_pow, ← map_pow]
  rw [h, PresentedGroup.one_of_mem (Set.mem_singleton _), map_one]

/-- A root presentation exhibits `G` as a one-relator group, in the sense of `Group.OneRelator`. -/
theorem toOneRelator (P : RootPresentation G) : Group.OneRelator G :=
  ⟨P.α, P.u ^ P.l, ⟨P.equiv⟩⟩

end RootPresentation

/-! ### The Magnus--Karrass--Solitar torsion theory and the FKS finite quotient -/

/-- The Magnus--Karrass--Solitar torsion theory attached to a root presentation `⟨X | u ^ l⟩`:
the root has order exactly `l` in `G`, and every torsion element of `G` is conjugate into the
cyclic subgroup generated by the root. -/
structure TorsionTheory {G : Type u} [Group G] (P : RootPresentation G) : Prop where
  /-- the root has order exactly `l` -/
  orderOf_root : orderOf P.rootElem = P.l
  /-- every element of finite order is conjugate into `⟨u⟩` -/
  torsion_conj : ∀ g : G, IsOfFinOrder g → ∃ (k : ℕ) (c : G), g = c * P.rootElem ^ k * c⁻¹

/-- The *root presentation* `⟨α | u ^ l⟩` with root `u` and exponent `l`. -/
def rootPresentation {α : Type u} (u : FreeGroup α) (l : ℕ) (hl : 1 ≤ l)
    (hu : ¬ IsProperPower u) :
    RootPresentation (PresentedGroup ({u ^ l} : Set (FreeGroup α))) where
  α := α
  u := u
  l := l
  one_le_l := hl
  not_properPower := hu
  equiv := MulEquiv.refl _

@[simp]
theorem rootPresentation_rootElem {α : Type u} (u : FreeGroup α) (l : ℕ) (hl : 1 ≤ l)
    (hu : ¬ IsProperPower u) :
    (rootPresentation u l hl hu).rootElem
      = PresentedGroup.mk ({u ^ l} : Set (FreeGroup α)) u := rfl

/-- **Fischer--Karrass--Solitar, 1972**: a one-relator group `⟨X | u ^ l⟩` with `u` not a proper
power has a finite quotient in which the image of `u` has order exactly `l`.

(The construction of this quotient is by induction on the Magnus--Moldavanskii hierarchy; this is
the input that node N2 supplies to node N4.) -/
def HasFKSTorsionQuotient {G : Type u} [Group G] (P : RootPresentation G) : Prop :=
  ∃ (Q : Type u) (_ : Group Q) (_ : Finite Q) (φ : G →* Q), orderOf (φ P.rootElem) = P.l

/-- The combined FKS/KMS input for the virtual torsion-freeness of a one-relator group. -/
def HasTorsionInput (G : Type u) [Group G] : Prop :=
  ∃ (P : RootPresentation G), TorsionTheory P ∧ HasFKSTorsionQuotient P

/-- The two literature inputs of node N4 bundled together: the Fischer--Karrass--Solitar /
Magnus--Karrass--Solitar input (`HasTorsionInput`) and Brodskii's theorem (`BrodskiiHowieInput`).

For a one-relator group `G`, these two hypotheses are supplied by the literature: the first by
FKS72 together with the KMS torsion theorem, the second by Brodskii (1980/1984), see also
Howie, *A short proof of a theorem of Brodskii*, Corollary 3.2. -/
def OneRelatorInput (G : Type u) [Group G] : Prop :=
  HasTorsionInput G ∧ BrodskiiHowieInput G

/-! ### The literature inputs of node N4, in structural form

The two theorems of the scope of this node are proved from the following inputs.  Each of them is a
*structural* statement, not a restatement of the theorem being proved:

* `HNNVirtualTorsionFree` is the general group-theoretic HNN step used in the FKS induction over the
  Magnus--Moldavanskii hierarchy (an HNN extension of a virtually torsion-free group along associated
  subgroups is virtually torsion-free);
* `BrodskiiTorsionFreeOneRelator` is Brodskii's theorem in its own right (Brodskii 1984; Howie 2000,
  Theorem 3.1): the *torsion-free* one-relator groups are locally indicable;
* `FKSStructure` is the structural half of Fischer--Karrass--Solitar 1972 used in Howie's
  Corollary 3.2, see `Submission.Work.ORLocInd.Brodskii.Cor32`.
-/

/-- **The HNN step of the Fischer--Karrass--Solitar proof (FKS 1972).**  An HNN extension of a
virtually torsion-free group along associated subgroups is virtually torsion-free.

This is the induction step in the proof that one-relator groups are virtually torsion-free: the
Magnus--Moldavanskii hierarchy (node N2) presents a one-relator group as a tower of HNN extensions
over free Magnus subgroups, and this step propagates virtual torsion-freeness up the tower.  The
special case in which the compatible finite quotient is available is proved unconditionally in
`Submission.Work.ORLocInd.HNN.virtuallyTorsionFree_hnnExtension_of_quotient`. -/
structure HNNVirtualTorsionFree : Prop where
  step : ∀ (H : Type u) [Group H], VirtuallyTorsionFree H →
    ∀ (A B : Subgroup H) (φ : A ≃* B), VirtuallyTorsionFree (HNNExtension H A B φ)

/-- **Brodskii's theorem** (Brodskii 1984; Howie 2000, Theorem 3.1): every torsion-free one-relator
group is locally indicable.

This is a theorem about one-relator groups that are *torsion-free*, i.e. the case excluded from the
main assertion of this node.  It is the base case of the local-indicability argument, and the input
that `Submission.Work.ORLocInd.Brodskii.Cor32` extends to torsion-free *subgroups* of arbitrary
one-relator groups by Howie's argument. -/
structure BrodskiiTorsionFreeOneRelator : Prop where
  locallyIndicable : ∀ (G : Type u) [Group G], Group.OneRelator G → IsTorsionFree G →
    Group.LocallyIndicable G

/-- The structural content of Fischer--Karrass--Solitar 1972 used in Howie's proof of
Corollary 3.2: a one-relator group `G = ⟨X | r ^ m⟩` (`m ≥ 2`, `r` not a proper power) maps onto
the corresponding torsion-free one-relator group `Q = ⟨X | r⟩` with kernel `N` a free product of
finite cyclic groups.

The two fields record exactly the two facts about this decomposition that Howie's argument uses:

* subgroups of `N` that are torsion-free are locally indicable (a torsion-free subgroup of a free
  product of cyclic groups is free, by the Kurosh subgroup theorem),
* `Q` is a torsion-free one-relator group (so is locally indicable by `BrodskiiTorsionFreeOneRelator`).
-/
def FKSStructure (G : Type u) [Group G] : Prop :=
  ∃ (Q : Type u) (_ : Group Q) (π : G →* Q),
    (∀ K : Subgroup π.ker, IsTorsionFree K → Group.LocallyIndicable K) ∧
    Group.OneRelator Q ∧ IsTorsionFree Q

end Work.ORLocInd
