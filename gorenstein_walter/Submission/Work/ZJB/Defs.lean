import Submission.Work.GLUE.ZjA

/-!
# ZJB — control of strong fusion by `N_G(Z(J(P)))` (Glauberman 1968, Theorem B)

Area **ZJB** of the Gorenstein–Walter development (route Bender 1981 + Bender–Glauberman 1981).

Requester: the lead.  Deliverable, verbatim:

> `ZJBProp`.  Inputs by name: `ZJAProp`, `PStableProp`, `DihOrCycHeredProp`.
> Route: Glauberman 1968 §5–6.  ZB1 Lemma 5.1; ZB2 Theorem 5.1(a) steps (I)–(IV);
> ZB3 Lemma 5.3 + Theorem 5.2; ZB4 induction on `|G|` (end of §6).

## Vocabulary

The contract vocabulary (`Work.GW2.*`) is *imported*, not copied: area **GLUE** already holds a
verbatim copy of `Submission/Work/_design_gw/Contracts2.lean` (`Work.GLUE.Defs`), and duplicating
it here would collide in `Work.GW2`.  So this file imports `Submission.Work.GLUE.ZjA` and this
area defines its notions in namespace `Work.ZJB`, on top of `Work.GW2`.

`Work.GW2.DihOrCycHeredProp`, which lives in `Submission/Work/_design_gw/Core2.lean` and not in
`Contracts2.lean`, is *not* in `Work.GW2` yet; it is copied verbatim here (this is the copy this
area consumes; a caller holding the `FUS`/`DSTR` copy may pass it, the two are definitionally
equal because both unfold to the same term).

## The two central notions

* `ControlsStrongFusion P K` — Glauberman's *control of strong fusion*: for every nonempty
  `W ⊆ P` and every `g` with `W^g ⊆ P`, we have `g ∈ C_G(W)·N_G(K)`.  This is exactly the
  conclusion of `Work.GW2.ZJBProp` with `K = Z(J(P))`.
* `ControlsStrongFusionOn P K` — the same condition tested on *subgroups* rather than arbitrary
  subsets (`Basic.lean` proves the two equivalent).

Also here: the strongly/weakly closed conditions, and `TheoremBStable`, the `p`-stable form of
Glauberman's Theorem B that `TheoremB.lean` reduces the deliverable to.
-/

namespace Work.ZJB

open Work.GW2
open Subgroup

variable {G : Type*} [Group G]

/-! ## Heredity of the Sylow-2 shape (`FUS`/`DSTR`'s `DihOrCycHeredProp`) -/

/-- Sylow 2-subgroups are dihedral or cyclic, in every subgroup and every quotient.  Verbatim
copy of `GW2.DihOrCycHeredProp` (`Submission/Work/_design_gw/Core2.lean`). -/
def DihOrCycHeredProp : Prop :=
  ∀ (X : Type) [Group X] [Finite X], DihOrCycSylow X →
    (∀ K : Subgroup X, DihOrCycSylow K) ∧ (∀ (N : Subgroup X) [N.Normal], DihOrCycSylow (X ⧸ N))

/-! ## Control of strong fusion -/

/-- **Glauberman's control of strong fusion.**  `P` is a `p`-subgroup (in the applications a
Sylow `p`-subgroup) and `K ≤ P`.  The condition says: every `G`-conjugacy `W ↦ W^g` of a
nonempty subset `W` of `P` into `P` is realised inside `N_G(K)` up to a centralising element.

This is the conclusion of Glauberman's Theorem B with `K = Z(J(P))`; it is the
`(C_p)`-type condition of Glauberman 1968 §5 in the "strong" (subset) form used in the paper,
and the form in which Bender 1981 Lemma 2.4 consumes it. -/
def ControlsStrongFusion (P K : Subgroup G) : Prop :=
  ∀ W : Set G, W.Nonempty → W ⊆ (P : Set G) → ∀ g : G,
    (∀ w ∈ W, g * w * g⁻¹ ∈ (P : Set G)) →
    ∃ c n : G, c ∈ centralizer W ∧ n ∈ normalizer (K : Set G) ∧ g = c * n

/-- The *subgroup* form of `ControlsStrongFusion`.  `Basic.lean` proves the two equivalent
(`controlsStrongFusion_iff_controlsStrongFusionOn`); the subgroup form is the one that is
convenient to induct on. -/
def ControlsStrongFusionOn (P K : Subgroup G) : Prop :=
  ∀ U : Subgroup G, U ≤ P → ∀ g : G, U.map (MulAut.conj g).toMonoidHom ≤ P →
    ∃ c n : G, c ∈ centralizer (U : Set G) ∧ n ∈ normalizer (K : Set G) ∧ g = c * n

/-- Weak control of fusion: every `G`-conjugacy of `U ≤ P` into `P` is realised by an element
of `N_G(K)`.  This is what "controls fusion" classically means; `Basic.lean` shows
`ControlsStrongFusion` implies it. -/
def ControlsFusion (P K : Subgroup G) : Prop :=
  ∀ U : Subgroup G, U ≤ P → ∀ g : G, U.map (MulAut.conj g).toMonoidHom ≤ P →
    ∃ n : G, n ∈ normalizer (K : Set G) ∧
      U.map (MulAut.conj n).toMonoidHom = U.map (MulAut.conj g).toMonoidHom

/-- `D` is strongly closed in `P` (with respect to `G`): `D ⊆ P` and the `G`-conjugates into
`P` of any subset of `D` remain inside `D`.  (Kizmaz, following Glauberman; the notion used in
Bender's Lemma 2.4 is `W = Z(F*(Ĥ))` strongly closed in a Sylow `p`-subgroup.) -/
def IsStronglyClosedSubset (D : Set G) (P : Subgroup G) : Prop :=
  D ⊆ (P : Set G) ∧ ∀ U : Set G, U ⊆ D → ∀ g : G,
    (∀ u ∈ U, g * u * g⁻¹ ∈ (P : Set G)) → ∀ u ∈ U, g * u * g⁻¹ ∈ D

/-- `D` is weakly closed in `P`: `D ≤ P` and every `G`-conjugate of `D` lying in `P` equals
`D`.  (`IsWeaklyClosed D P` is the `U = D` case of strong closure; `Basic.lean` relates the
two.) -/
def IsWeaklyClosed (D P : Subgroup G) : Prop :=
  D ≤ P ∧ ∀ g : G, D.map (MulAut.conj g).toMonoidHom ≤ P →
    D.map (MulAut.conj g).toMonoidHom = D

/-- `K ≤ P` is normalised by every element of `N_G(P)`; the `K`s that arise here
(`Z(J(P))`, `Z(P)`) have this property because they are characteristic in `P`. -/
def NormalizedByNormalizer (P K : Subgroup G) : Prop :=
  normalizer (P : Set G) ≤ normalizer (K : Set G)

/-! ## Glauberman 1968, §5: the conditions `(C_p)` and `(C_p*)`

The paper (p. 1116) fixes a prime `p`, a finite group `G`, and a *characteristic functor* `K`
(a map sending every finite `p`-group `P` to a nontrivial characteristic subgroup `K(P) ≤ P`),
and defines

* `(C_p)`: if `S ∈ Syl_p(G)`, `W ⊆ S`, `g ∈ G` and `W^g ⊆ S`, then `g = c n` for some
  `c ∈ C_G(W)` and `n ∈ N_G(K(S))`;

* `(C_p*)`: the same, but with `W` running over the *`p`-subgroups of `N_G(K(S))`* and
  `W^g ⊆ N_G(K(S))`.

With `K(S) = Z(J(S))` these are `Work.ZJB.SatisfiesCp` and `Work.ZJB.SatisfiesCpStar` below:
`SatisfiesCp p X` is *exactly* the conclusion of `Work.GW2.ZJBProp` for the group `X` and the
prime `p` (Glauberman's Theorem B is the statement that every `Qd(p)`-free `G` satisfies
`(C_p)` for `K = Z(J(·))`).

* Lemma 5.1: `(C_p) ⟺ (C_p*)` for an arbitrary characteristic functor.
* Theorem 5.1: `(C_p)` holds if it holds for `N_G(H)` for all `Z(S) ≤ H ≤ S` (or for every
  element of `M_p(G)`, the maximal `p`-subgroups).
* Theorem 5.2: if `O_p(G) ≠ 1` and every proper subquotient of `G` satisfies `(C_p)` while
  every subquotient `Q` with `C(O_p(Q)) ≤ O_p(Q)` has `K(Q_p) ⊴ Q`, then `G` satisfies `(C_p)`.
* Theorem B (p. 1125): every `Qd(p)`-free finite group satisfies `(C_p)` for `K = Z(J(·))`,
  by induction on `|G|` from Theorem 5.1(a) (case `O_p(G) = 1`) and Theorem 5.2 (case
  `O_p(G) ≠ 1`). -/

/-- `Z(S)`, the centre of `S`, as a subgroup of the ambient group. -/
def ZS (S : Subgroup G) : Subgroup G := centralizer (S : Set G) ⊓ S

/-- **Glauberman's condition `(C_p)` (p. 1116), with `K(S) = Z(J(S))`**: for every Sylow
`p`-subgroup `S` of `G`, `N_G(Z(J(S)))` controls strong fusion in `S`.  This is exactly the
conclusion of `Work.GW2.ZJBProp` at `(G, p)`, and the statement of Theorem B. -/
def SatisfiesCp (p : ℕ) (G : Type*) [Group G] [Finite G] : Prop :=
  ∀ S : Sylow p G, ControlsStrongFusion (S : Subgroup G) (ZJ (S : Subgroup G))

/-- The `(C_p*)` condition for a single subgroup `K`: for every `p`-subgroup `W ≤ N_G(K)` and
every `g` with `W^g ≤ N_G(K)`, `g ∈ C_G(W)·N_G(K)`. -/
def ControlsStrongFusionStar (p : ℕ) (K : Subgroup G) : Prop :=
  ∀ W : Subgroup G, W ≤ normalizer (K : Set G) → IsPGroup p W → ∀ g : G,
    (∀ w ∈ W, g * w * g⁻¹ ∈ normalizer (K : Set G)) →
    ∃ c n : G, c ∈ centralizer (W : Set G) ∧ n ∈ normalizer (K : Set G) ∧ g = c * n

/-- **Glauberman's condition `(C_p*)` (p. 1116), with `K(S) = Z(J(S))`**: the control condition
tested on the `p`-subgroups of `N_G(Z(J(S)))`.  Lemma 5.1 (`Lemma51.lean`) proves
`SatisfiesCp p G ↔ SatisfiesCpStar p G`. -/
def SatisfiesCpStar (p : ℕ) (G : Type*) [Group G] [Finite G] : Prop :=
  ∀ S : Sylow p G, ControlsStrongFusionStar p (ZJ (S : Subgroup G))

/-- The `p`-stable form of Theorem B (Glauberman 1968, Theorem B): a `p`-stable finite group
satisfies `(C_p)` for `K(S) = Z(J(S))`.  `TheoremB.lean` derives `Work.GW2.ZJBProp` from it
using `PStableProp` (area `PSTAB`) and `DihOrCycHeredProp`. -/
def TheoremBStable : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (p : ℕ) [Fact p.Prime], p ≠ 2 → IsPStable' p X →
    SatisfiesCp p X

end Work.ZJB
