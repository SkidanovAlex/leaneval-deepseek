/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gorenstein–Walter formalisation team (area DSTR, `Work.DSTR`)

# AREA DSTR — the structure of D-groups (Bender 1981 §1.6–1.10)

Route: Bender 1981, *Finite groups with dihedral Sylow 2-subgroups*, J. Algebra **70** (1981)
216–228, §1; the leaves are §C of `Submission/Work/_design_gw/Core2.lean`, the DAG is §10 of
`Submission/Work/NOTES_LEAD_gw_design2.md`.

This is the *interface* file of the area.  It contains

* the shared contract vocabulary, imported from the canonical `Work.GW2` module
  `Submission.Work.ASM.Defs` (the deliverables of this area, `D16Prop`, `LayerProp`, `L19Prop`,
  `D110iProp`, `D110iiProp`, `FStarProp`, are defined there, verbatim from `Contracts2.lean`);
* the `Prop`s of the DSTR leaves `DS1`–`DS10b` (namespace `Work.GW2`, copied from `Core2.lean`
  §C/§G), which is what the delegated lemmas prove;
* four auxiliary `Prop`s of the area's own design, which make the leaves statable with all their
  inputs explicit:
  * `DihedralSubgroupProp`, `DihedralQuotientProp`, `DihedralAbelianRankProp` — the elementary
    subgroup structure of `DihedralGroup n` needed by `DS1`, `DS3`, `DS5`;
  * `L2OddSylowCyclicProp` — the `L₂(q)` input of `L19Prop` (odd Sylow subgroups of `L₂(q)` are
    cyclic), which is an `L2F` fact used by the transfer argument of Bender 1.9.

The mathematical content lives in the sibling files:

* `Submission/Work/DSTR/<leaf>.lean` — the proofs of the leaves (`Work.DSTR.<leaf>`);
* `Submission/Work/DSTR/Main.lean` — the six area deliverables, assembled from the leaves.

NOTE on module layout.  This file is self-contained in the sense that it re-uses the canonical
`Work.GW2` vocabulary module of area ASM (`Submission.Work.ASM.Defs`), which is a verbatim copy of
`_design_gw/Contracts2.lean`.  It defines no `Work.GW2` name that is already defined there; the new
names introduced here (the DSTR leaves and the auxiliary `Prop`s) are unique in the workspace.
-/
import Submission.Work.ASM.Defs

open scoped MatrixGroups

namespace Work.GW2

open Subgroup

/-! ## Auxiliary vocabulary of the area (our own design) -/

/-- Every subgroup of `DihedralGroup n` (including the infinite dihedral group, `n = 0`) is cyclic
or is itself dihedral.  This is the raw group-theoretic input of `DS1`. -/
def DihedralSubgroupProp : Prop :=
  ∀ (n : ℕ) (H : Subgroup (DihedralGroup n)),
    IsCyclic H ∨ ∃ m : ℕ, Nonempty (H ≃* DihedralGroup m)

/-- Every quotient of `DihedralGroup n` by a normal subgroup is cyclic or dihedral. -/
def DihedralQuotientProp : Prop :=
  ∀ (n : ℕ) (N : Subgroup (DihedralGroup n)) [N.Normal],
    IsCyclic (DihedralGroup n ⧸ N) ∨ ∃ m : ℕ, Nonempty ((DihedralGroup n ⧸ N) ≃* DihedralGroup m)

/-- Every abelian subgroup of `DihedralGroup n` is cyclic or of order at most `4` (in a dihedral
group the abelian subgroups are cyclic or Klein four-groups).  This is the rank input of `DS3` and
`DS5`.  For `n = 0` both disjuncts are harmless (`Nat.card` of an infinite group is `0`). -/
def DihedralAbelianRankProp : Prop :=
  ∀ (n : ℕ) (A : Subgroup (DihedralGroup n)),
    IsMulCommutative A → IsCyclic A ∨ Nat.card A ≤ 4

/-- For an odd prime `r ≠ p`, the Sylow `r`-subgroups of `L₂(q)`, `q = p^k` odd `≥ 5`, are cyclic
(the maximal tori are cyclic).  This is the `L2F` input of the transfer argument in `L19Prop`. -/
def L2OddSylowCyclicProp : Prop :=
  ∀ (p k : ℕ) [Fact p.Prime], Odd p → 5 ≤ p ^ k → ∀ (r : ℕ) [Fact r.Prime], r ≠ 2 → r ≠ p →
    ∀ R : Sylow r (PSL(2, GaloisField p k)), IsCyclic R

/-- **Bender 1.2** (`E1`), stated in this area's vocabulary: for a finite solvable group the
Fitting subgroup contains its centralizer.  This is
`OddOrder.GroupTheory.centralizer_fitting_le_fitting`, transported from the FT-closure's
`OddOrder.Isaacs.Ch01.fitting` to `Work.GW2.fitting` (the bridge is proved in the leaf
`Submission/Work/DSTR/fittingSelfCentralizing.lean`).  Input of `D16Prop` and `FStarProp`. -/
def FittingSelfCentralizingProp : Prop :=
  ∀ (X : Type) [Group X] [Finite X], Group.IsSolvable X →
    centralizer (fitting X : Set X) ≤ fitting X

/-! ## The CORE4 fusion input `LayerOneInvClassProp` (Core3 §4; producer DSTR) -/

/-- `K` has one class of involutions under conjugation by elements of `K` (Core3 §4). -/
def C3OneInvClassIn {G : Type*} [Group G] (K : Subgroup G) : Prop :=
  ∀ x ∈ K, ∀ y ∈ K, orderOf x = 2 → orderOf y = 2 → ∃ g ∈ K, g * x * g⁻¹ = y

/-- **`LayerOneInvClassProp`** (design3 §9, Core3 §4): the normal quasisimple subgroup of a
D-group has one class of involutions.  The subgroup is perfect, hence has no normal subgroup of
index `2`, and `DS1` + `DS4` give it a noncyclic dihedral Sylow 2, so FUS
(`InvolutionFusionProp`) applies to it.  Consumed by CORE4. -/
def LayerOneInvClassProp : Prop :=
  ∀ (X : Type) [Group X] [Finite X], FeitThompsonProp → DihOrCycSylow X →
    ∀ E : Subgroup X, E.Normal → IsQuasisimple E → C3OneInvClassIn E

/-! ## DSTR leaves, `Core2.lean` §C -/

/-- **DS1.**  The Sylow 2-shape of a D-group passes to subgroups and to quotients. -/
def DihOrCycHeredProp : Prop :=
  ∀ (X : Type) [Group X] [Finite X], DihOrCycSylow X →
    (∀ K : Subgroup X, DihOrCycSylow K) ∧ (∀ (N : Subgroup X) [N.Normal], DihOrCycSylow (X ⧸ N))

/-- **DS2.**  `O(X/O(X)) = 1`. -/
def OddCoreQuotProp : Prop :=
  ∀ (X : Type) [Group X] [Finite X], oddCore (X ⧸ oddCore X) = ⊥

/-- **DS3.**  2-rank at most 2. -/
def TwoRankProp : Prop :=
  ∀ (X : Type) [Group X] [Finite X], DihOrCycSylow X →
    ∀ E : Subgroup X, IsMulCommutative E → (∀ x ∈ E, x ^ 2 = 1) → Nat.card E ≤ 4

/-- **DS4.**  A quasisimple subgroup has noncyclic Sylow 2-subgroups (FT + Burnside's transfer
theorem). -/
def QuasisimpleSylowProp : Prop :=
  ∀ (X : Type) [Group X] [Finite X], FeitThompsonProp → ∀ E : Subgroup X, IsQuasisimple E →
    ∀ P : Sylow 2 E, ¬ IsCyclic P

/-- **DS5.**  There is at most one normal quasisimple subgroup. -/
def LayerUniqueProp : Prop :=
  ∀ (X : Type) [Group X] [Finite X], FeitThompsonProp → DihOrCycSylow X →
    ∀ E₁ E₂ : Subgroup X, E₁.Normal → E₂.Normal → IsQuasisimple E₁ → IsQuasisimple E₂ → E₁ = E₂

/-- **DS6.**  `Z(E)` is odd. -/
def QuasisimpleCenterOddProp : Prop :=
  ∀ (X : Type) [Group X] [Finite X], DihOrCycSylow X → ∀ E : Subgroup X, IsQuasisimple E →
    Odd (Nat.card (center E))

/-- **DS7.**  `E/Z(E)` is the simple section of `X/O(X)`. -/
def LayerShapeProp : Prop :=
  ∀ (X : Type) [Group X] [Finite X], FeitThompsonProp → DihOrCycSylow X → IsDGroup X →
    ∀ E : Subgroup X, E.Normal → IsQuasisimple E →
      Nonempty ((↥E ⧸ center ↥E) ≃* alternatingGroup (Fin 7)) ∨
        ∃ p k : ℕ, ∃ _ : Fact p.Prime, Odd p ∧ 5 ≤ p ^ k ∧
          Nonempty ((↥E ⧸ center ↥E) ≃* PSL(2, GaloisField p k))

/-- **DS9a.**  1.10(i) in the reduced shapes (`O(Q) = 1`, not a 2-group). -/
def D110iModelProp : Prop :=
  ∀ (Q : Type) [Group Q] [Finite Q], DihOrCycSylow Q → oddCore Q = ⊥ → DShape Q →
    ∀ t : Q, orderOf t = 2 → ∀ (p : ℕ) [Fact p.Prime], p ≠ 2 → ∀ P : Subgroup Q, IsPGroup p P →
      centralizer ({t} : Set Q) ≤ normalizer (P : Set Q) → P ≤ centralizer ({t} : Set Q)

/-- **DS9b.**  1.10(i) in the case `[P,t] ⊆ O(X)` (B70 2.4, second paragraph). -/
def D110iOddProp : Prop :=
  ∀ (X : Type) [Group X] [Finite X], FeitThompsonProp → DihOrCycSylow X → IsDGroup X →
    ∀ t : X, orderOf t = 2 → ∀ (p : ℕ) [Fact p.Prime], p ≠ 2 → ∀ P : Subgroup X, IsPGroup p P →
      centralizer ({t} : Set X) ≤ normalizer (P : Set X) → ⁅P, zpowers t⁆ ≤ oddCore X →
      ⁅P, zpowers t⁆ ≤ pCore p X

/-- **DS10a.**  1.10(ii) on the almost simple model: `F_{2'}(C_Q(t)) ≤ L`. -/
def D110iiModelProp : Prop :=
  ∀ (Q : Type) [Group Q] [Finite Q] (L : Subgroup Q) (p k : ℕ) [Fact p.Prime], Odd p → 5 ≤ p ^ k →
    L.Normal → Nonempty (L ≃* PSL(2, GaloisField p k)) → centralizer (L : Set Q) = ⊥ →
    DihOrCycSylow Q → ∀ t : Q, orderOf t = 2 →
      fittingPiIn {2}ᶜ (centralizer ({t} : Set Q)) ≤ L

/-- **DS10b.**  Lifting inner automorphisms from `E/Z(E)` to a perfect `E`. -/
def InnerLiftProp : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (E : Subgroup X), E.Normal → IsQuasisimple E →
    ∀ x : X,
      (∃ e ∈ E, ∀ y ∈ E, (x * y * x⁻¹) * (e * y * e⁻¹)⁻¹ ∈ (center E).map E.subtype) →
      ∃ e ∈ E, ∀ y ∈ E, x * y * x⁻¹ = e * y * e⁻¹

end Work.GW2
