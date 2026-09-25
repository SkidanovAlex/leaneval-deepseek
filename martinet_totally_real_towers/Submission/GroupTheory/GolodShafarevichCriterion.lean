import Mathlib
import Submission.Commons.Algebra.FreeAlgebra.golod_shafarevich_finite_dimensional_pos
import Submission.Commons.GroupTheory.ProPGroup.freeAlgebraData_congr

set_option linter.style.haveILetI false
set_option linter.unusedVariables false

/-!
# The Golod--Shafarevich criterion: the corrected packaging

**STATUS: sorry-free.**  Namespace `Submission.GroupTheory`; not on the
`Submission.lean` proof path.

## 1. The problem with the delivered packaging

The commons lemma
`Commons.GroupTheory.ProPGroup.infinite_of_presentation_of_algebra_data`
concludes `Infinite G` from a presentation of a group `G` together with

* `hgen` (minimality of the generating set `α`),
* `hpg` (every finite quotient of `G` is a `p`-group),
* `hdata`, the *algebra data*: homogeneous elements `relAlg r` of degree `≥ 2`,
  indexed by the relator set `rel`, whose two-sided span has **finite-dimensional**
  quotient (`∀ᶠ n, finrank (A_n) = 0`), and
* `hineq : 4 * rel.card ≤ Fintype.card α * Fintype.card α`.

The point of this module is that **the hypothesis package `hdata ∧ hineq` is
unsatisfiable**: `hdata` alone already implies the *reverse* Golod--Shafarevich
inequality

    `Fintype.card α * Fintype.card α < 4 * rel.card`

(the finite-dimensionality in `hdata` is exactly the hypothesis of the commons
Golod--Shafarevich algebra theorem
`Commons.Algebra.FreeAlgebra.golod_shafarevich_finite_dimensional_pos`).
Consequently `infinite_of_presentation_of_algebra_data` can never be applied: it
is *vacuously* true.  (`HasGSData`, `hasGSData_ineq`,
`delivered_hdata_package_unsatisfiable` below make this precise and
machine-checked; the last one is stated with the *verbatim* `hdata` of the
delivered lemma, so the verification is against the literal delivered hypotheses.)

Note that the incompatibility is not an accident of indexing: the algebra
relators `relAlg r` are attached to the *index* (`rel` is coerced to its subtype)
and **no compatibility whatsoever** is imposed between the group relator
`(r : FreeGroup α)` and the algebra element `relAlg r`.  So `hdata` is a
condition on the *cardinality* of `rel` and on an arbitrary choice of `rel.card`
homogeneous algebra elements of degrees `≥ 2`; and by the algebra theorem it is
equivalent to "there are `rel.card` such elements whose quotient is
finite-dimensional", which forces `card α ^ 2 < 4 * rel.card`.

## 2. The corrected criterion

The classical theorem (Golod--Shafarevich, finite `p`-groups) is

  `FinitePGroupGolodShafarevich p`:  a nontrivial finite `p`-group with a minimal
  generating set `α` and *any* presentation by `α` with relator set `rel`
  satisfies `4 * rel.card > Fintype.card α ^ 2`.

It is *not* an instance of the algebra theorem above: it is obtained by proving
that `hdata` holds for **every** finite `p`-group presentation, i.e. by the
**Magnus/Jennings theorem** (the leading forms of the relators under the Magnus
embedding `x_i ↦ 1 + X_i` generate an ideal whose quotient is the graded algebra
`gr F_p[Q]` of the group algebra for the Zassenhaus filtration, hence is
finite-dimensional, of dimension `|Q|`).

Given only `FinitePGroupGolodShafarevich p` we derive
(`infinite_of_presentation_of_golodShafarevich`) the *correct* criterion: a group
with a minimal presentation by `α` with `4 * rel.card ≤ Fintype.card α ^ 2`, all of
whose finite quotients are `p`-groups, is **infinite**.  This is the statement
that the arithmetic side (the class field tower) has to feed.
-/

namespace Submission.GroupTheory

open Commons.GroupTheory.ProPGroup

variable {K : Type*} [Field K]
variable {α : Type*} [Fintype α] [DecidableEq α]

/-- **The algebra data package** (`hdata`) of the delivered commons packaging
`Commons.GroupTheory.ProPGroup.infinite_of_presentation_of_algebra_data`,
extracted as a named `Prop` (over an arbitrary coefficient field `K`) so that its
consequences can be stated. -/
def HasGSData (K : Type*) [Field K] (α : Type*) [Fintype α] [DecidableEq α]
    (rel : Finset (FreeGroup α)) : Prop :=
  0 < Fintype.card α ∧
  ∃ (degRel : rel → ℕ) (relAlg : rel → FreeAlgebra K α),
    (∀ r : rel, 2 ≤ degRel r) ∧
    (∀ r : rel, relAlg r ∈ degreeSubmodule K α (degRel r)) ∧
    (∀ᶠ n : ℕ in Filter.atTop,
      Module.finrank K
        (Submodule.map (Submodule.mkQ (twoSidedSpan K α rel relAlg))
          (degreeSubmodule K α n)) = 0)

/-- **`hdata` implies the Golod--Shafarevich inequality in the *opposite*
direction.**  This is the commons algebra theorem
`Commons.Algebra.FreeAlgebra.golod_shafarevich_finite_dimensional_pos` applied to
the data of `HasGSData`. -/
theorem hasGSData_ineq {rel : Finset (FreeGroup α)} (h : HasGSData K α rel) :
    Fintype.card α * Fintype.card α < 4 * rel.card := by
  classical
  obtain ⟨hpos, degRel, relAlg, hdeg, hhom, hfin⟩ := h
  have hmain := Commons.Algebra.FreeAlgebra.golod_shafarevich_finite_dimensional_pos
    (K := K) (ι := α) (σ := rel) hpos degRel relAlg hdeg
    (by intro r; simpa [Commons.GroupTheory.ProPGroup.degreeSubmodule] using hhom r) hfin
  simpa [Fintype.card_coe] using hmain

/-- **The hypothesis package `hdata ∧ hineq` is unsatisfiable.** -/
theorem not_hasGSData_and_ineq {rel : Finset (FreeGroup α)} :
    ¬ (HasGSData K α rel ∧ 4 * rel.card ≤ Fintype.card α * Fintype.card α) :=
  fun h => absurd (hasGSData_ineq h.1) (not_lt_of_ge h.2)

/-- **The delivered `hdata` package is unsatisfiable *verbatim*.**

The hypothesis list of `Commons.GroupTheory.ProPGroup.infinite_of_presentation_of_algebra_data`
is repeated here in its literal syntactic form (same `degreeSubmodule`,
`twoSidedSpan`, `ZMod p`); it is inconsistent, so that lemma can never be applied
-- it is vacuously true, and cannot carry the Golod--Shafarevich seam. -/
theorem delivered_hdata_package_unsatisfiable (p : ℕ) [Fact p.Prime]
    {α : Type*} [Fintype α] [DecidableEq α] (rel : Finset (FreeGroup α))
    (hdata : 0 < Fintype.card α ∧
      ∃ (degRel : rel → ℕ) (relAlg : rel → FreeAlgebra (ZMod p) α),
        (∀ r : rel, 2 ≤ degRel r) ∧
        (∀ r : rel, relAlg r ∈ degreeSubmodule (ZMod p) α (degRel r)) ∧
        (∀ᶠ n : ℕ in Filter.atTop,
          Module.finrank (ZMod p)
            (Submodule.map (Submodule.mkQ (twoSidedSpan (ZMod p) α rel relAlg))
              (degreeSubmodule (ZMod p) α n)) = 0))
    (hineq : 4 * rel.card ≤ Fintype.card α * Fintype.card α) : False := by
  classical
  obtain ⟨hpos, degRel, relAlg, hdeg, hhom, hfin⟩ := hdata
  have hmain := Commons.Algebra.FreeAlgebra.golod_shafarevich_finite_dimensional_pos
    (K := ZMod p) (ι := α) (σ := rel) hpos degRel relAlg hdeg
    (by intro r; simpa [Commons.GroupTheory.ProPGroup.degreeSubmodule] using hhom r) hfin
  have hlt : Fintype.card α * Fintype.card α < 4 * rel.card := by
    simpa [Fintype.card_coe] using hmain
  exact absurd hlt (not_lt_of_ge hineq)

/-- **The finite `p`-group Golod--Shafarevich inequality, in presentation form.**
This is the missing mathematical input of the whole Golod--Shafarevich seam: the
theorem to be extracted from the Magnus/Jennings algebra data. -/
def FinitePGroupGolodShafarevich (p : ℕ) : Prop :=
  ∀ {α : Type} [Fintype α] [DecidableEq α] (Q : Type) [Group Q] [Fintype Q] [Nontrivial Q]
    (rel : Finset (FreeGroup α)),
    IsPGroup p Q →
    Nonempty (Q ≃* FreeGroup α ⧸ Subgroup.normalClosure (rel : Set (FreeGroup α))) →
    (∀ S : Finset Q, Subgroup.closure (S : Set Q) = ⊤ → Fintype.card α ≤ S.card) →
    4 * rel.card > Fintype.card α * Fintype.card α

/-- **The Magnus/Jennings input produces the finite `p`-group Golod--Shafarevich
inequality.**  The hypothesis is exactly "every finite `p`-group presentation
carries the algebra data `HasGSData`" -- what the classical Magnus/Jennings
theorem (leading forms of the relators under the Magnus embedding) supplies;
together with the algebra theorem above it yields the inequality. -/
theorem finitePGroupGolodShafarevich_of_gsData (p : ℕ) [Fact p.Prime]
    (hdata : ∀ {β : Type} [Fintype β] [DecidableEq β] (Q : Type) [Group Q] [Fintype Q]
      [Nontrivial Q] (rel : Finset (FreeGroup β)),
      IsPGroup p Q →
      Nonempty (Q ≃* FreeGroup β ⧸ Subgroup.normalClosure (rel : Set (FreeGroup β))) →
      (∀ S : Finset Q, Subgroup.closure (S : Set Q) = ⊤ → Fintype.card β ≤ S.card) →
      HasGSData (ZMod p) β rel) :
    FinitePGroupGolodShafarevich p := by
  intro β _ _ Q _ _ _ rel hpg hpres hgen
  exact hasGSData_ineq (hdata Q rel hpg hpres hgen)

/-- **THE CORRECTED GOLOD--SHAFAREVICH CRITERION.**  A group `G` presented by
finitely many generators `α` modulo the normal closure of the relator set `rel`,
with `α` minimal, all of whose finite quotients are `p`-groups, and with

    `4 * rel.card ≤ Fintype.card α * Fintype.card α`,

is **infinite**.  The only mathematical input is the finite `p`-group
Golod--Shafarevich inequality `FinitePGroupGolodShafarevich p`. -/
theorem infinite_of_presentation_of_golodShafarevich {p : ℕ} [Fact p.Prime]
    (hGS : FinitePGroupGolodShafarevich p)
    {α : Type} [Fintype α] [DecidableEq α] {G : Type} [Group G]
    (rel : Finset (FreeGroup α))
    (hpos : 0 < Fintype.card α)
    (hpres : Nonempty (G ≃* FreeGroup α ⧸ Subgroup.normalClosure (rel : Set (FreeGroup α))))
    (hgen : ∀ S : Finset G, Subgroup.closure (S : Set G) = ⊤ → Fintype.card α ≤ S.card)
    (hpg : ∀ (N : Subgroup G) [N.Normal], Finite (G ⧸ N) → IsPGroup p (G ⧸ N))
    (hineq : 4 * rel.card ≤ Fintype.card α * Fintype.card α) :
    Infinite G := by
  classical
  by_contra hinf
  haveI : Finite G := not_infinite_iff_finite.mp hinf
  haveI : Fintype G := Fintype.ofFinite G
  have hpgG : IsPGroup p G := by
    have hfin : Finite (G ⧸ (⊥ : Subgroup G)) := inferInstance
    exact (hpg ⊥ hfin).of_equiv (QuotientGroup.quotientBot (G := G))
  have hnt : Nontrivial G := by
    rw [← not_subsingleton_iff_nontrivial]
    intro hss
    haveI := hss
    have hcl : Subgroup.closure ((∅ : Finset G) : Set G) = ⊤ := by
      refine eq_top_iff.mpr fun x _ => ?_
      rw [Subsingleton.elim x 1]
      exact Subgroup.one_mem _
    have h := hgen ∅ hcl
    rw [Finset.card_empty] at h
    exact absurd h (not_le.mpr hpos)
  exact absurd (hGS G rel hpgG hpres hgen) (not_lt_of_ge hineq)

end Submission.GroupTheory
