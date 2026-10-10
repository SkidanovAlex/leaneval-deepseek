/-
This module is a local copy of the three generic transport lemmas that
`Submission/Work/MotA/exists_awayBirationalMap_cInv.lean` needs, so that the `MotA` area does not
depend on the (dead-listed) `Work.Wire123` directory.  The statements are Mathlib-level facts about
`cInv` and partial isomorphisms with source everything; the proofs are unchanged.
-/
import Submission.Work.CrauderKatz.exDiv_toBirationalMap_eq_empty_of_source_eq_top
import Submission.Work.CrauderKatz.BlowUp.exists_birationalMap_exDiv_singleton_of_openImmersion
import Submission.Work.Reflect.PolyId
set_option maxRecDepth 100000

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.MotA.TransportAPI` — the invariant of a partial isomorphism

Every transport argument in the `n ≥ 5` area (the paper's `ε : 𝔸ⁿ ⇢ G/P`, `δ : G/P' ⇢ 𝔸ⁿ`, the
one-sided modifications of `Submission/Work/CrauderKatz`) has the shape: a birational map given by
a partial isomorphism `i : X.PartialIso Y` whose *source* is everything (`i.source = ⊤`, an open
immersion), and the computation of its Lin–Shinder coefficient `cInv 𝕜 z i.toBirationalMap`.

Two facts make that computation mechanical, and they are proved here in the general form (no
hypotheses on `X`, `Y` beyond irreducibility and the separated/reduced conditions needed to compare
partial maps):

* `cInv_of_partialIso_source_eq_top` — the coefficient of such a map is the number of
  **codimension-one points of `Y` outside the image `i.target` whose function field is that of
  `z`** (this is the `+1` of a "missing divisor": an open immersion is an isomorphism at every
  codimension-one point of its source, so its only exception is on the target side);
* `cInv_eq_zero_of_partialIso_source_target_eq_top` — in particular an **isomorphism** has
  vanishing coefficient at every base point: this is what makes the paper's transports harmless when
  their exceptional divisors have classes different from the base point's, and it is the formal
  content of the "the transports contribute nothing" step of `thm:birational-sets`'s proof.

The companion `exDiv_symm_of_partialIso_source_eq_top` (the `exDiv` computation behind the first
fact) is the general form of
`Work.CrauderKatz.BlowUp.mem_target_of_toRationalMap_eq_symm`, which the one-sided-link machinery
proves for a single missing point.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
attribute [instance] MotivicInvariants.Variety.over MotivicInvariants.Variety.isIntegral

namespace Work.MotA

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme MotivicInvariants Order

noncomputable section

/-- The symmetric partial isomorphism represents the inverse birational map. -/
theorem PartialIso.toBirationalMap_symm {X Y : Scheme.{0}} [IrreducibleSpace X]
    [IrreducibleSpace Y] (i : X.PartialIso Y) :
    i.toBirationalMap.symm = i.symm.toBirationalMap := by
  ext
  simp [Scheme.PartialIso.toBirationalMap, BirationalMap.symm]

/-- **The exceptional divisors of the inverse of a partial isomorphism are exactly the
codimension-one points of the target that are not in its image.**  A partial isomorphism with
`i.source = ⊤` is an isomorphism onto its target, so it is an isomorphism at every point of its
source, and — conversely — no partial isomorphism representing its inverse can be defined at a
point outside the target `i.target` (comparing the two on a dense open forces the inverse to agree
with the inclusion). -/
theorem exDiv_symm_of_partialIso_source_eq_top {X Y : Scheme.{0}} [IrreducibleSpace X]
    [IrreducibleSpace Y] [IsReduced Y] [Y.IsSeparated] (i : X.PartialIso Y) (h : i.source = ⊤) :
    exDiv i.toBirationalMap.symm = {y : Y | coheight y = 1 ∧ y ∉ (i.target : Set Y)} := by
  ext y
  rw [exDiv, Set.mem_setOf_eq, Set.mem_setOf_eq]
  constructor
  · rintro ⟨hc, hniso⟩
    refine ⟨hc, fun hyt => hniso ?_⟩
    refine ⟨i.symm, hyt, ?_⟩
    rw [PartialIso.toBirationalMap_symm]
    simp [Scheme.PartialIso.toBirationalMap, BirationalMap.symm]
  · rintro ⟨hc, hyt⟩
    refine ⟨hc, fun hniso => hyt ?_⟩
    obtain ⟨i', hy', hrat⟩ := hniso
    refine Work.CrauderKatz.BlowUp.mem_target_of_toRationalMap_eq_symm i' i h ?_ hy'
    rw [hrat, PartialIso.toBirationalMap_symm]
    simp [Scheme.PartialIso.toBirationalMap, BirationalMap.symm]

/-- **The coefficient of an open immersion (a partial isomorphism with `i.source = ⊤`).**  Its
`exDiv` is empty — an open immersion is an isomorphism at every point of its source — so the whole
contribution comes from the target side: the codimension-one points of `Y` outside the image
`i.target` whose function field is that of the base point.

This is the `+1` of a "missing divisor" used at every transport step of the `n ≥ 5` area. -/
theorem cInv_of_partialIso_source_eq_top {𝕜 : Type} [Field 𝕜] {X Y : Scheme.{0}}
    [IrreducibleSpace X] [IrreducibleSpace Y] [IsReduced Y] [Y.IsSeparated]
    [X.Over (Spec (.of 𝕜))] [Y.Over (Spec (.of 𝕜))] (i : X.PartialIso Y) (h : i.source = ⊤)
    {Z : Scheme.{0}} [Z.Over (Spec (.of 𝕜))] (z : Z) :
    cInv 𝕜 z i.toBirationalMap =
      ((Set.ncard {y : Y | coheight y = 1 ∧ y ∉ (i.target : Set Y) ∧
        ResEquiv 𝕜 y z} : ℕ) : ℤ) := by
  have h0 : excCount 𝕜 z i.toBirationalMap = 0 := by
    rw [excCount, Work.CrauderKatz.exDiv_toBirationalMap_eq_empty_of_source_eq_top i h]
    simp
  have hset : {x : Y | x ∈ exDiv i.toBirationalMap.symm ∧ ResEquiv 𝕜 x z}
      = {y : Y | coheight y = 1 ∧ y ∉ (i.target : Set Y) ∧ ResEquiv 𝕜 y z} := by
    rw [exDiv_symm_of_partialIso_source_eq_top i h]
    ext y
    simp only [Set.mem_setOf_eq, and_assoc]
  unfold cInv
  rw [h0]
  unfold excCount
  rw [hset]
  simp

/-- **An isomorphism has vanishing coefficient**, at every base point.  Both `exDiv` sets are
empty (`i.source = i.target = ⊤`). -/
theorem cInv_eq_zero_of_partialIso_source_target_eq_top {𝕜 : Type} [Field 𝕜] {X Y : Scheme.{0}}
    [IrreducibleSpace X] [IrreducibleSpace Y] [IsReduced Y] [Y.IsSeparated]
    [X.Over (Spec (.of 𝕜))] [Y.Over (Spec (.of 𝕜))] (i : X.PartialIso Y)
    (hs : i.source = ⊤) (ht : i.target = ⊤) {Z : Scheme.{0}} [Z.Over (Spec (.of 𝕜))] (z : Z) :
    cInv 𝕜 z i.toBirationalMap = 0 := by
  have h0 : excCount 𝕜 z i.toBirationalMap = 0 := by
    unfold excCount
    rw [Work.CrauderKatz.exDiv_toBirationalMap_eq_empty_of_source_eq_top i hs]
    simp
  have h1 : excCount 𝕜 z i.toBirationalMap.symm = 0 := by
    unfold excCount
    rw [PartialIso.toBirationalMap_symm i,
      Work.CrauderKatz.exDiv_toBirationalMap_eq_empty_of_source_eq_top i.symm (by simpa using ht)]
    simp
  unfold cInv
  rw [h1, h0]
  first | refl_ring1 | ring

end

end Work.MotA

namespace Work.MotA

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme MotivicInvariants Order

noncomputable section

/-- **The structural `−1` of every transport into a chart.**  For a partial isomorphism
`i : X.PartialIso Y` with `i.source = ⊤` (an open immersion), the *inverse* birational map
`Y ⇢ X` has coefficient the negative of the number of codimension-one points of `Y` outside the
image `i.target` whose function field is that of the base point (the companion of
`cInv_of_partialIso_source_eq_top` through `Work.LLink.cInv_eq_neg_symm`).

This is the term that cancels the `+1` of a Crauder–Katz link in every transport-only construction:
the missing divisor of the chart and the exceptional divisor of the link have the same class. -/
theorem cInv_symm_of_partialIso_source_eq_top {𝕜 : Type} [Field 𝕜] {X Y : Scheme.{0}}
    [IrreducibleSpace X] [IrreducibleSpace Y] [IsReduced Y] [Y.IsSeparated]
    [X.Over (Spec (.of 𝕜))] [Y.Over (Spec (.of 𝕜))] (i : X.PartialIso Y) (h : i.source = ⊤)
    {Z : Scheme.{0}} [Z.Over (Spec (.of 𝕜))] (z : Z) :
    cInv 𝕜 z i.toBirationalMap.symm =
      -((Set.ncard {y : Y | coheight y = 1 ∧ y ∉ (i.target : Set Y) ∧ ResEquiv 𝕜 y z} : ℕ) : ℤ) := by
  rw [Work.LLink.cInv_eq_neg_symm, cInv_of_partialIso_source_eq_top i h z]

/-- **The `−1` in the case of a single missing divisor of the base point's class** — the shape of
one Crauder–Katz one-sided modification: if the only codimension-one point of `Y` outside the image
of the chart is `η`, and `η` has the function field of the base point, then the transported map has
coefficient exactly `-1` there. -/
theorem cInv_symm_of_partialIso_source_eq_top_singleton {𝕜 : Type} [Field 𝕜]
    {X Y : Scheme.{0}} [IrreducibleSpace X] [IrreducibleSpace Y] [IsReduced Y] [Y.IsSeparated]
    [X.Over (Spec (.of 𝕜))] [Y.Over (Spec (.of 𝕜))] (i : X.PartialIso Y) (h : i.source = ⊤)
    {Z : Scheme.{0}} [Z.Over (Spec (.of 𝕜))] (z : Z) {η : Y}
    (hη : {y : Y | coheight y = 1 ∧ y ∉ (i.target : Set Y)} = {η})
    (hr : ResEquiv 𝕜 η z) :
    cInv 𝕜 z i.toBirationalMap.symm = -1 := by
  have h1 : ∀ y : Y, (coheight y = 1 ∧ y ∉ (i.target : Set Y)) ↔ y = η := by
    intro y
    have := congrArg (fun s : Set Y => y ∈ s) hη
    simpa using this
  have hset : {y : Y | coheight y = 1 ∧ y ∉ (i.target : Set Y) ∧ ResEquiv 𝕜 y z} = {η} := by
    ext y
    rw [Set.mem_setOf_eq, Set.mem_singleton_iff]
    constructor
    · rintro ⟨h1y, h2y, h3y⟩
      exact (h1 y).mp ⟨h1y, h2y⟩
    · intro hy
      obtain ⟨h1y, h2y⟩ := (h1 y).mpr hy
      exact ⟨h1y, h2y, by rw [hy]; exact hr⟩
  rw [cInv_symm_of_partialIso_source_eq_top i h z, hset]
  simp

end

end Work.MotA
