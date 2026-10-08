import Submission.Work.CharCore.Main
import Submission.Work.Induction.All
import Submission.Work.Clifford.All

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.CharPrelim.Defs`: definitions shared by the Ch. I preliminary lemmas

This is the base module of area P2-03 (`Work.CharPrelim`) of the Feit--Thompson drive:
FT 3.15, 4.1--4.6, 5.1--5.2 and the inequalities (5.1)--(5.12) of the 1963 paper
(Pacific J. Math. 13 (1963), 775--1029, pages 782--787).

Source: `Submission/Work/ft1963/tex/ch1.md` (a faithful transcription of the page images).

## Conventions

* everything is stated over a finite group type (`[Fintype G]`); a caller holding only
  `[Finite G]` passes with `letI := Fintype.ofFinite G`;
* characters are functions `X → ℂ` in the vocabulary of `Work.CharCore`
  (`Irr : Finset (X → ℂ)`, `IsVChar`, `irrDeg`, `charKernel`, `cfInner`), and induction is
  `Work.Induction.indFun`;
* subgroups live in an ambient group `G` (PGroup convention): conjugation is
  `MulAut.conj g • H` (`Work.PGroup.conjBy`).
-/

noncomputable section

open Classical

namespace Work.CharPrelim

variable {G : Type*} [Group G]

/-- FT's "`S`-subgroup of `X`", i.e. a Hall subgroup of `X`: `H ≤ X` and `|H|` is coprime to
`[X : H]`.  (This is the definition of the blueprint's `FTSpine.IsHallIn`; recorded here so
that this area is self-contained until area P2-00 lands.) -/
def IsHallIn (H X : Subgroup G) : Prop := H ≤ X ∧ (Nat.card H).Coprime (H.relIndex X)

/-- FT §2: `X` is a Frobenius group with Frobenius kernel `K` (both subgroups of the ambient
group `G`).  `K` is a proper nontrivial normal subgroup of `X` and `C_X(h) ≤ K` for every
`h ∈ K \ {1}`.  (The blueprint's `FTSpine.IsFrobeniusIn`.) -/
structure IsFrobeniusIn (X K : Subgroup G) : Prop where
  le : K ≤ X
  normal : (K.subgroupOf X).Normal
  ne_bot : K ≠ ⊥
  ne : K ≠ X
  cent : ∀ h ∈ K, h ≠ 1 → Subgroup.centralizer ({h} : Set G) ⊓ X ≤ K

/-- The irreducible characters of a subgroup `H`, as a finset of functions `↥H → ℂ`.

This is `Work.CharCore.Irr ↥H`; the wrapper exists so that the `Fintype ↥H` instance (which is
classical) is resolved once and for all here, and callers and statements never need
`open Classical` merely to *mention* `Irr` of a subgroup.  `IrrSub H = Irr ↥H` definitionally
(`mem_IrrSub`). -/
noncomputable def IrrSub {X : Type*} [Group X] [Fintype X] (H : Subgroup X) : Finset (↥H → ℂ) :=
  Work.CharCore.Irr ↥H

/-- Membership in `IrrSub H` is membership in `Work.CharCore.Irr ↥H` (definitional). -/
theorem mem_IrrSub {X : Type*} [Group X] [Fintype X] {H : Subgroup X} {χ : ↥H → ℂ} :
    χ ∈ IrrSub H ↔ χ ∈ Work.CharCore.Irr ↥H := Iff.rfl

/-- "`γ` is a virtual (generalized) character of the subgroup `H`", i.e. `Work.CharCore.IsVChar γ`
for `γ : ↥H → ℂ`, with the classical `Fintype ↥H` instance resolved here (cf. `IrrSub`). -/
def IsVCharSub {X : Type*} [Group X] [Fintype X] (H : Subgroup X) (γ : ↥H → ℂ) : Prop :=
  Work.CharCore.IsVChar γ

/-- `IsVCharSub H γ ↔ IsVChar γ` (definitional). -/
theorem isVCharSub_iff {X : Type*} [Group X] [Fintype X] {H : Subgroup X} {γ : ↥H → ℂ} :
    IsVCharSub H γ ↔ Work.CharCore.IsVChar γ := Iff.rfl

/-- `ξ_d` of FT Lemma 4.4: the sum of all irreducible characters of `X` of degree `d` which do
not contain the normal subgroup `H` in their kernel. -/
noncomputable def xi {X : Type*} [Group X] [Fintype X] (H : Subgroup X) (d : ℕ) : X → ℂ :=
  fun x => ∑ χ ∈ (Work.CharCore.Irr X).filter
      (fun χ => Work.CharCore.irrDeg χ = d ∧ ¬ (H : Set X) ⊆ Work.CharCore.charKernel χ), χ x

/-- The sum of the squares of the degrees of the irreducible characters of a finite group `P`
whose degree is `< d`; this is the right hand side of FT 3.15. -/
noncomputable def degLtSum (P : Type*) [Group P] [Fintype P] (d : ℕ) : ℕ :=
  ((Work.CharCore.Irr P).filter (fun φ => Work.CharCore.irrDeg φ < d)).sum
    (fun φ => Work.CharCore.irrDeg φ ^ 2)

end Work.CharPrelim
