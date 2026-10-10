import Submission.Work.K3Inputs.Defs

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.K3Inputs.Terasoma` — the Terasoma input (`lem:HL-admis-pencil` + `pro-K3HLPic1`)

Lin–Shinder, *Motivic invariants of birational maps*, Annals **199** (1), 2024, § *K3 surfaces of
degree 12*, tex 2282–2404.  The paper's construction of the K3 L-links starts from:

> Consider a general `3`-dimensional linear section `V ⊂ ℙ⁸` over `ℚ` of the Mukai Grassmannian
> `OG₊(5,10)`.  … As `OG₊(5,10)`, being a rational homogeneous variety, has dense `ℚ`-points and
> since the linear section cutting off `V` is general, we can assume that `V` is smooth and has a
> `ℚ`-point.  This implies that `V` is `ℚ`-rational (Kuznetsov–Prokhorov).
>
> **Lemma `lem:HL-admis-pencil`.**  For a general `V` as above, there exists an HL-admissible pair
> `(ℙ⁶, Σ)` defined over `ℚ`.   *(Proof: the HL-admissible pairs form a Zariski dense open subset
> `U` of the incidence variety `𝒳 ⊂ V³ × Gr(ℙ⁶, ℙ⁸)`; `𝒳` is `ℚ`-rational, hence `U` has dense
> `ℚ`-points.)*
>
> **Proposition `pro-K3HLPic1`.**  There exist infinitely many polarized K3 surfaces `(S,H)` of
> degree `12` over `ℚ` together with three `ℚ`-points `Σ = {x₁,x₂,x₃} ⊂ S(ℚ)` such that
> (1) `Pic(S_ℂ) ≃ ℤ`, (2) `(S;Σ)` is HL-admissible.  The same conclusion holds if `ℚ` is replaced
> by any subfield `𝕜` of `ℂ`, and the isomorphism classes of such K3 surfaces `S` form a set `I`
> which has the cardinality of `𝕜`.   *(Proof: Terasoma's argument — Step 2 and Step 3 of §3 of
> Terasoma's paper — applied to the `ℚ`-defined Lefschetz pencil of Lemma `lem:HL-admis-pencil`,
> together with the non-isotriviality of the pencil: the monodromy action on `H²(S_{t,ℂ}, ℚ)` is
> nontrivial by the invariant cycle theorem, and `Aut(S_{t,ℂ}) = {Id}` when `ρ(S_{t,ℂ}) = 1`.)*

## What this file records

`Work.K3.TerasomaInput` (the K3 chapter's arithmetic input) is exactly the **data form of
`pro-K3HLPic1` over `ℚ`**, with the cardinality clause dropped (as in the K3 chapter: the
cardinality is used for `cor:homZ`, not for Theorem 1.2 (2)).  This file

* restates the conclusion over an *arbitrary* field `𝕜` (`TerasomaData 𝕜`) and proves the two
  packagings `TerasomaData ↥ℚ ↔ Work.K3.TerasomaInput` (`TerasomaData.toInput`, `…ofInput`), so
  that a caller knows exactly which form of the paper's proposition the K3 chapter consumes;
* records the paper's *stronger* conclusion — infinitely many pairwise non-isomorphic such
  surfaces (`TerasomaFamily 𝕜`), which is what the proof actually gives (non-isotriviality) — and
  **proves** that it implies the data form (`TerasomaFamily.toData`, `…toInput`);
* records the "same conclusion over every subfield `𝕜 ⊆ ℂ`" strengthening
  (`TerasomaAllSubfields`) and its provable consequence over `ℚ`;
* names the three unformalised ingredients of the proof — the pencil lemma
  (`HLAdmisPencil`), Terasoma's argument (`TerasomaArgument`) and the non-isotriviality
  (`PencilNonisotrivial`) — together with the cardinality clause (`PencilCardinality`),
  so that the residual of the arithmetic input is precisely these four statements about
  `OG₊(5,10)`, `ℙ⁸`, `ℙ⁶`, Lefschetz pencils and monodromy, none of which is in Mathlib.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option warn.classDefReducibility false
attribute [instance] MotivicInvariants.Variety.over MotivicInvariants.Variety.isIntegral

namespace Work.K3Inputs

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
  MotivicInvariants Order

noncomputable section

variable {𝕜 : Type} [Field 𝕜]

/-! ## 1. The conclusion of `pro-K3HLPic1` over an arbitrary field -/

/-- **The data of the arithmetic input, over an arbitrary field `𝕜`.**

A K3 surface `S` of degree `12` over `𝕜` (named predicate), `K`-trivial, of geometric Picard rank
one, together with a length-three closed subscheme `Σ ⊂ S` — the paper's three points
`Σ = {x₁,x₂,x₃} ⊂ S(𝕜)` — which is HL-admissible.  This is `Work.K3.TerasomaInput` with `ℚ`
replaced by `𝕜`; `TerasomaData.toInput` and `TerasomaData.ofInput` identify the two at `ℚ`. -/
structure TerasomaData (𝕜 : Type) [Field 𝕜] where
  /-- the K3 surface of degree `12` -/
  S : Scheme.{0}
  [varietyS : Variety 𝕜 S]
  /-- `S` is a K3 surface of degree `12` (named predicate). -/
  isK3 : Work.K3.IsK3Degree12 𝕜 S
  /-- `S` is `K`-trivial (named predicate). -/
  kTrivial : Work.K3.IsKTrivial 𝕜 S
  /-- `S` has geometric Picard rank one (`Pic(S_ℂ) ≃ ℤ`). -/
  picardOne : Work.K3.PicardRankOneGeom 𝕜 S
  /-- the length-three subscheme `Σ = {x₁,x₂,x₃} ⊂ S` -/
  Sigma : Scheme.{0}
  [overSigma : Sigma.Over (Spec (.of 𝕜))]
  /-- the closed immersion `Σ ⟶ S` -/
  sigma : Sigma ⟶ S
  [isOverSigma : sigma.IsOver (Spec (.of 𝕜))]
  [isClosedImmersionSigma : IsClosedImmersion sigma]
  [isReducedSigma : IsReduced Sigma]
  [smoothSigma : Smooth sigma]
  /-- `Σ` has length three (named predicate). -/
  hasLengthThree : Work.K3.HasLengthThree 𝕜 sigma
  /-- `(S, Σ)` is HL-admissible (named predicate). -/
  hl : Work.K3.HLAdmissible 𝕜 sigma

attribute [instance] TerasomaData.varietyS TerasomaData.overSigma TerasomaData.isOverSigma

/-- **The K3 chapter's arithmetic input is the `ℚ`-form of `pro-K3HLPic1`.** -/
def TerasomaData.toInput (D : TerasomaData ℚ) : Work.K3.TerasomaInput where
  S := D.S
  varietyS := D.varietyS
  isK3 := D.isK3
  kTrivial := D.kTrivial
  picardOne := D.picardOne
  Sigma := D.Sigma
  overSigma := D.overSigma
  sigma := D.sigma
  isOverSigma := D.isOverSigma
  isClosedImmersionSigma := D.isClosedImmersionSigma
  isReducedSigma := D.isReducedSigma
  smoothSigma := D.smoothSigma
  hasLengthThree := D.hasLengthThree
  hl := D.hl

/-- Conversely, the K3 chapter's arithmetic input is a `TerasomaData` over `ℚ`. -/
def TerasomaData.ofInput (T : Work.K3.TerasomaInput) : TerasomaData ℚ where
  S := T.S
  varietyS := T.varietyS
  isK3 := T.isK3
  kTrivial := T.kTrivial
  picardOne := T.picardOne
  Sigma := T.Sigma
  overSigma := T.overSigma
  sigma := T.sigma
  isOverSigma := T.isOverSigma
  isClosedImmersionSigma := T.isClosedImmersionSigma
  isReducedSigma := T.isReducedSigma
  smoothSigma := T.smoothSigma
  hasLengthThree := T.hasLengthThree
  hl := T.hl

/-! ## 2. The strong form: infinitely many pairwise non-isomorphic surfaces -/

/-- **The paper's `pro-K3HLPic1` in the form its proof gives.**  The Lefschetz pencil is
non-isotrivial (its monodromy action is nontrivial, and `Aut(S_{t,ℂ}) = {Id}` when
`ρ(S_{t,ℂ}) = 1`), so the construction produces *infinitely many pairwise non-isomorphic* K3
surfaces of degree `12` over `𝕜`, each with a length-three HL-admissible subscheme and geometric
Picard rank one.

This is the honest form of the "there exist infinitely many" clause of `pro-K3HLPic1`; the data
form `TerasomaData 𝕜` (what `Work.K3.TerasomaInput` consumes) is a *consequence* of it
(`TerasomaFamily.toData`, `TerasomaFamily.toInput`), so recording the strong form loses nothing
and shows that the input is not strengthened beyond the paper. -/
structure TerasomaFamily (𝕜 : Type) [Field 𝕜] where
  /-- the members of the family -/
  idx : ℕ → TerasomaData 𝕜
  /-- distinct members are non-isomorphic (non-isotriviality of the pencil) -/
  not_iso : ∀ i j : ℕ, i ≠ j → ¬ Work.K3.IsoOver 𝕜 (idx i).S (idx j).S

/-- The data form is a consequence of the strong form (take the first member). -/
def TerasomaFamily.toData (F : TerasomaFamily 𝕜) : TerasomaData 𝕜 := F.idx 0

/-- The strong form over `ℚ` yields the K3 chapter's arithmetic input. -/
def TerasomaFamily.toInput (F : TerasomaFamily ℚ) : Work.K3.TerasomaInput :=
  F.toData.toInput

/-! ## 3. The paper's "same conclusion over any subfield" -/

/-- **The paper's remark**: the conclusion of `pro-K3HLPic1` holds with `ℚ` replaced by any
subfield `𝕜 ⊆ ℂ`.  Recorded as a named input (it is proved in the paper by the same construction,
the Lefschetz pencil being defined over `ℚ`); the `ℚ`-clause is kept separately so that the
K3 chapter's input can be read off without any comparison of `↥(⊥ : Subfield ℂ)` with `ℚ`. -/
structure TerasomaAllSubfields : Prop where
  /-- the conclusion over every subfield `𝕜 ⊆ ℂ` -/
  all : ∀ K : Subfield ℂ, Nonempty (TerasomaFamily ↥K)
  /-- the conclusion over `ℚ` -/
  rat : Nonempty (TerasomaFamily ℚ)

/-- **The provable consequence**: the uniform statement gives the K3 chapter's input over `ℚ`. -/
def TerasomaAllSubfields.toInput (h : TerasomaAllSubfields) : Work.K3.TerasomaInput :=
  (Classical.choice h.rat).toInput

/-- The conclusion of `pro-K3HLPic1` over a fixed subfield `𝕜 ⊆ ℂ`, in data form. -/
abbrev TerasomaStatement (K : Subfield ℂ) : Prop := Nonempty (TerasomaData ↥K)

/-- The uniform statement implies the statement over every subfield. -/
theorem TerasomaAllSubfields.toStatement (h : TerasomaAllSubfields) (K : Subfield ℂ) :
    TerasomaStatement K :=
  (h.all K).map TerasomaFamily.toData

/-! ## 4. The named ingredients of the arithmetic input

Each of the following is a `Prop`-valued named hypothesis: the objects it speaks about
(`OG₊(5,10)`, `ℙ⁸`, `ℙ⁶`, the Grassmannian `Gr(ℙ⁶,ℙ⁸)`, the incidence variety `𝒳`, Lefschetz
pencils, monodromy on `H²(S_{t,ℂ}, ℚ)`, the `ℚ`-rationality of `V` of Kuznetsov–Prokhorov) do
not exist in Mathlib.  Together they are the exact residual of the arithmetic input: the paper
proves `pro-K3HLPic1` from `HLAdmisPencil` + `TerasomaArgument` + `PencilNonisotrivial`, and the
cardinality clause `PencilCardinality` is not needed for Theorem 1.2 (2). -/

/-- **Lemma `lem:HL-admis-pencil`** (tex 2342–2372): for a general `ℚ`-rational `3`-dimensional
linear section `V ⊂ ℙ⁸` of the Mukai Grassmannian `OG₊(5,10)`, there exists an HL-admissible pair
`(ℙ⁶, Σ)` defined over `ℚ`.

Named: the proof is the statement that the incidence variety
`𝒳 = {(x₁,x₂,x₃; L) ∈ V³ × Gr(ℙ⁶,ℙ⁸) | x₁,x₂,x₃ ∈ V ∩ L}` is `ℚ`-rational, and that the
HL-admissible pairs form a dense open subset `U ⊆ 𝒳` — a "very general property" argument on a
rational variety.  None of `OG₊(5,10)`, `Gr(ℙ⁶,ℙ⁸)`, `V`, `𝒳` is in Mathlib. -/
class HLAdmisPencil : Prop

/-- **Terasoma's argument** (Step 2 and Step 3 in §3 of Terasoma's paper, proving its Theorem 1):
applied to the `ℚ`-defined Lefschetz pencil of K3 surfaces of degree `12` produced by
`HLAdmisPencil`, it yields infinitely many members with geometric Picard rank one.

Named: Terasoma's theorem is about the density of rank-one members of a Lefschetz pencil, via
monodromy (the Noether–Lefschetz locus is a countable union of divisors in the base); none of
monodromy, `H²(S,ℚ)`, or the Picard group of a K3 surface is in Mathlib. -/
class TerasomaArgument : Prop

/-- **Non-isotriviality of the Lefschetz pencil** (tex 2382–2398 of the paper): the monodromy
action on `H²(S_{t,ℂ}, ℚ)` is nontrivial by the invariant cycle theorem, and `Aut(S_{t,ℂ}) = {Id}`
when `ρ(S_{t,ℂ}) = 1` (Huybrechts, Corollary 15.2.12), hence the pencil contains infinitely many
pairwise non-isomorphic members.  This is what makes `TerasomaFamily` (rather than a single
surface) the correct conclusion.

Named, for the same reason as `TerasomaArgument` (monodromy, `Aut`, `H²`). -/
class PencilNonisotrivial : Prop

/-- **The cardinality clause of `pro-K3HLPic1`**: the isomorphism classes of the K3 surfaces `S`
occurring in these L-links form a set of the cardinality of `𝕜`.  Recorded for completeness; it
is used in the paper only for `cor:homZ` (the homeomorphism count), not for Theorem 1.2 (2), which
needs a single non-vanishing coefficient — hence `Work.K3.TerasomaInput` drops it. -/
class PencilCardinality (K : Subfield ℂ) : Prop

end

end Work.K3Inputs
