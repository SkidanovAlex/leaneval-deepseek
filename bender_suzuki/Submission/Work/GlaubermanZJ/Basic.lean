/-
Area `GlaubermanZJ` of the Bender–Suzuki project: Glauberman's `ZJ`-theorem
(Canad. J. Math. **20** (1968), 1101–1135, Theorem A) in the form used by Peterfalvi
(*Le théorème de Bender–Suzuki I*, Astérisque 142–143, p. 145) and by the area
`Submission.Blueprint.GlaubermanZJProp`.

## What the area is

`Submission.Blueprint.GlaubermanZJProp` says: for `G` finite **solvable** with **abelian Sylow
2-subgroups**, `p` an odd prime and `P` a Sylow `p`-subgroup of `G`, the subgroup
`O_{p'}(G) ⊔ Z(J(P))` is **characteristic** in `G` (i.e. `O_{p'}(G)·Z(J(P))` is characteristic).

The route (Glauberman 1968, `REFS/glauberman_zj.md`) is

1. quotient by `O_{p'}(G)`, so that the problem becomes `Z(J(S))` characteristic in a group `X`
   with `O_{p'}(X) = ⊥`;
2. `C(O_p(X)) ≤ O_p(X)` (Hall–Higman Lemma 1.2.3; delivered as
   `Work.Fitting.centralizer_pPrimePCore_le`);
3. `p`-stability of `X` (Glauberman §6; here from the delivered quadratic Hall–Higman material
   `Work.PStable`/`Work.LocalPrelim.ft7_2_cond3_pstable`);
4. Glauberman's Theorem A: a `p`-stable finite group with `C(O_p(G)) ≤ O_p(G)` has `Z(J(S))`
   characteristic.

The proof of Theorem A (§3–§5 of the paper) runs through the Thompson replacement theorem
(delivered as `Work.PGroup.thompson_replacement`), Glauberman's replacement theorem for odd `p`
(Theorem 4.1) and Theorems 3.2, 4.2, 4.3.

## This file

Vocabulary only: the bridge between the blueprint's `thompsonJ`/`ZJ` and the delivered
`Work.PGroup` API, and the statement of `p`-stability in the form in which the area uses it.
`bridge.lean` (same directory) contains the actual bridge theorems.
-/

import Mathlib
import Submission.Blueprint.Interfaces
import Submission.Work.PGroup.Basic
import Submission.Work.HallHigman.Basic
import Submission.Work.Fitting.Defs

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option autoImplicit false
set_option linter.unusedVariables false

open LeanEval.GroupTheory.Defs

namespace Work.GlaubermanZJ

variable {G : Type*} [Group G]

/-! ## 1. Sylow 2-subgroups -/

/-- **`G` has abelian Sylow 2-subgroups** (all of them).  This is the hypothesis that replaces
"no `SL(2,p)` section" in `GlaubermanZJProp`: `SL(2,p)` has generalised quaternion Sylow
2-subgroups for odd `p`, and quotients of abelian groups are abelian. -/
def HasAbelianSylowTwo (G : Type*) [Group G] : Prop :=
  ∀ S : Sylow 2 G, Submission.Blueprint.IsAbelianSubgroup (S : Subgroup G)

/-! ## 2. `p`-stability (Glauberman, Definition 2.1) -/

/-- The side condition of Glauberman's Definition 2.1: `O_{p'}(G)·P` is normal in `G`. -/
def OpPrimeMulNormal (p : ℕ) (G : Type*) [Group G] (P : Subgroup G) : Prop :=
  (Submission.Blueprint.pPrimeCore p G ⊔ P).Normal

/-- **Glauberman's `p`-stability condition** (Definition 2.1 of Glauberman 1968), in the case
`P ⊴ G` of the side condition `O_{p'}(G)P ⊴ G`, which is the case in which the theorem is
applied: for every normal `p`-subgroup `P` and every `p`-subgroup `A ≤ N_G(P)` with
`[P,A,A] = 1`, the image of `A` in `N_G(P)/C_G(P) = G/C_G(P)` lies in `O_p(G/C_G(P))`.

For a general `p`-subgroup `P` with `O_{p'}(G)P ⊴ G` one applies this to `N_G(P)` and the
normal subgroup `P` of it.  `pstable_iff_opPrimeMulNormal` in `pstable_basic.lean` records the
equivalence with `OpPrimeMulNormal`.

The exponent `p` is not required to be prime here; every use carries `p.Prime`. -/
def IsPStable (p : ℕ) (G : Type*) [Group G] : Prop :=
  ∀ (P : Subgroup G) [P.Normal], IsPGroup p P →
    ∀ (A : Subgroup G), IsPGroup p A → ⁅⁅P, A⁆, A⁆ = ⊥ →
      A.map (QuotientGroup.mk' (Subgroup.centralizer (P : Set G))) ≤
        Work.HallHigman.pCore p (G ⧸ Subgroup.centralizer (P : Set G))

/-- `G` is `p`-stable in the sense of Glauberman's Definition 2.3: every subgroup `M` maximal
subject to `O_p(M) ≠ ⊥` satisfies Definition 2.1.  Only the `O_p(G) ≠ ⊥` instance is used in
this area, and then `𝒜_p(G) = {G}`. -/
def IsPStableG (p : ℕ) (G : Type*) [Group G] : Prop :=
  IsPStable p G

/-! ## 3. The `J`/`ZJ` vocabulary -/

/-- The blueprint's `thompsonJ` and the delivered `Work.PGroup.thompsonJ` are the same subgroup;
see `Work.GlaubermanZJ.thompsonJ_eq` in `bridge.lean`.  This abbreviation lets later files use
the shorthand `ZJ` for the blueprint's subgroup while the p-group API is applied through the
bridge. -/
abbrev ZJ (P : Subgroup G) : Subgroup G := Submission.Blueprint.ZJ P

/-- `A` is an abelian subgroup of `P` of maximal order (`𝓐(S)` of Glauberman §2, written
`𝒜(S)` in the project; `d(S)` is `Work.PGroup.maxAbelianOrder`). -/
def IsMaxAbelianSubgroup (P A : Subgroup G) : Prop :=
  A ≤ P ∧ Submission.Blueprint.IsAbelianSubgroup A ∧
    ∀ B : Subgroup G, B ≤ P → Submission.Blueprint.IsAbelianSubgroup B →
      Nat.card B ≤ Nat.card A

end Work.GlaubermanZJ
