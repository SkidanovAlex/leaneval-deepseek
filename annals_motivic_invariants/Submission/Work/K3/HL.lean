import Mathlib
import Submission.Work.K3.Defs
import Submission.Work.K3.K3Link
import Submission.Work.K3.BaseChange
import Submission.Work.K3.BaseChangeBirational

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.K3.HL` — the named inputs of Theorem `thm:K3` (Hassett–Lai, Terasoma, Totaro)

This file records the three *named inputs* of the `n = 4` case of Lin–Shinder's
*Motivic invariants of birational maps* (Annals **199** (1), 2024, § *K3 surfaces of degree 12*),
in the exact shape in which the theorem-level argument consumes them, and derives from them the
non-triviality input of the L-link `Work.K3.K3Link`.

## The inputs

1. `HLAdmissible` — a *named geometric predicate*: the pair `(S, Σ)` (`S` a K3 surface of degree
   `12` over `𝕜`, `Σ ⊂ S` a smooth subscheme of length three) is *HL-admissible*, i.e. items
   (1)–(4) of Theorem `thm-HL` hold for `(S_ℂ, Σ_ℂ)`.  Since Mathlib has no Grassmannian
   `OG₊(5,10)`, no `ℙ⁷`, no blow-up and no minimal models, this is a hypothesis.

2. `TerasomaInput` — the arithmetic input: **Lemma `lem:HL-admis-pencil` + Proposition
   `pro-K3HLPic1` + Terasoma**.  There is a K3 surface `S` of degree `12` over `ℚ`, `ℚ`-defined
   with an HL-admissible pair `(S, Σ)`, of *geometric* Picard rank one.  (The paper obtains it
   from a `ℚ`-rational smooth `3`-dimensional linear section `V ⊂ ℙ⁸` of `OG₊(5,10)` and the
   Lefschetz pencil cut out by the hyperplanes through a general `ℚ`-rational `ℙ⁶`, then applies
   Terasoma's argument to find members of the pencil with `ρ(S_ℂ) = 1`; the isomorphism classes
   of the resulting surfaces have the cardinality of `𝕜`.)

3. `HassettLaiTheorem` — the geometric input **Theorem `thm-HL`(1)–(4)** (Hassett–Lai Thm 2.1,
   Thm 3.1), *together with its last sentence* ("if `S ↪ ℙ⁷` and `Σ ⊂ S` are defined over a
   subfield `k ⊂ ℂ`, then both `ψ` and the pair `(S', Σ')` are defined over `k`"): from the
   `ℚ`-admissible pair one gets the whole L-link geometry over `ℚ` (`data : K3Data ℚ`), and its
   two centres are *geometrically* non-isomorphic (`S_ℂ ≄ S'_ℂ`; Hassett–Lai Thm 3.1 plus Oguiso
   Prop 1.10 for the Fourier–Mukai partner).

4. `HLDescent` — the descent step to a subfield `𝕜 ⊆ ℂ`: the `𝕜`-model of the `ℚ`-link, whose two
   centres are the base changes of the `ℚ`-model's centres.  This is the paper's extension from
   `ℂ` to `𝕜`; see `Submission/Work/K3/Descent.lean` for what is *proved* about it (the
   non-isomorphism of the two centres over `𝕜`) and `NOTES.md` for the exact residue.

5. `TotaroInput` — Totaro's Theorem `thm:BurtCY` / Corollary `cor-CYnSB`: two non-isomorphic
   `K`-trivial varieties of Picard number one over a field are not stably birational.

## What is proved here

`Work.K3.K3Data.not_resEquiv_yx_of_totaro` — Totaro's input, applied to the two centres of the
link, turns the failure of `ResEquiv` for the two exceptional divisors into the non-stable
birationality of the centres (via the `ℙ¹`-bundle bridge `K3Data.bridge`), and conversely:
`¬ ResEquiv 𝕜 y x` follows from `¬ IsoOver 𝕜 S S'` and `TotaroInput 𝕜`.  The link
`K3Data.toK3Link` is then the K3 L-link of `Work.K3.K3Link`, whose invariant coefficient is `1`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
attribute [instance] MotivicInvariants.Variety.over MotivicInvariants.Variety.isIntegral

namespace Work.K3

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
  MotivicInvariants Order

/-! ## 1. The named geometric and arithmetic inputs -/

/-- **Named geometric predicate: length three.**  The closed subscheme `ι : Σ ⟶ S` has length
three (for the `Σ = {x₁, x₂, x₃}` of the Hassett–Lai construction, `Σ` is the disjoint union of
three `Spec` of fields, i.e. `Σ = Spec ℚ × Spec ℚ × Spec ℚ` over `ℚ` up to isomorphism: smooth of
degree three over the base field, hence length three).  "Length" (the degree of a closed
subscheme) is not expressible in Mathlib, so it is a named hypothesis; closedness, smoothness and
reducedness *are* required as hypotheses (see `TerasomaInput`). -/
class HasLengthThree (𝕜 : Type) [Field 𝕜] {S Sig : Scheme.{0}} [S.Over (Spec (.of 𝕜))]
    [Sig.Over (Spec (.of 𝕜))] (ι : Sig ⟶ S) : Prop

/-- **Named geometric predicate: HL-admissibility of the pair `(S, Σ)`** (paper, § *K3 surfaces of
degree 12*).

`HLAdmissible 𝕜 ι` says that the closed subscheme `ι : Σ ⟶ S` — three general points of `S`,
mapped into the K3 surface `S` of degree `12` — is such that `(S_ℂ, Σ_ℂ)` satisfies items (1)–(4)
of Theorem `thm-HL`: the proper transform `S_0 ⊂ ℙ⁴` of `S ↪ ℙ⁷` under the projection from the
plane spanned by `Σ` has three transverse double points with normalisation `Bl_Σ S`, the linear
system of quartics containing `S_0` cuts it out scheme-theoretically and defines a birational
`ψ : ℙ⁴ ⤏ ℙ⁴`, and `ψ⁻¹` arises the same way from `(S', Σ')`.

Mathlib has none of the objects involved (the Grassmannian `OG₊(5,10)`, `ℙ⁷`, blow-ups,
normalisations, minimal models), so this is a named hypothesis. -/
class HLAdmissible (𝕜 : Type) [Field 𝕜] {S Sig : Scheme.{0}} [S.Over (Spec (.of 𝕜))]
    [Sig.Over (Spec (.of 𝕜))] (ι : Sig ⟶ S) : Prop

/-- **Named arithmetic input: `lem:HL-admis-pencil` + Terasoma + `pro-K3HLPic1`.**

There exists a K3 surface `S` of degree `12` over `ℚ`, together with a length-three closed
subscheme `Σ ⊂ S` forming an HL-admissible pair, whose geometric Picard rank is one.

The paper's construction: a general `3`-dimensional linear section `V ⊂ ℙ⁸` of the Grassmannian
`OG₊(5,10)`, defined over `ℚ` and `ℚ`-rational (Kuznetsov–Prokhorov); a general `ℚ`-rational
`ℙ⁶ ⊂ ℙ⁸` giving an HL-admissible pair `(ℙ⁶, Σ)` (`lem:HL-admis-pencil`); Terasoma's argument
(`pro-K3HLPic1`) then produces members of the Lefschetz pencil with `ρ(S_ℂ) = 1`, and the
isomorphism classes of the resulting surfaces `S` have the cardinality of the subfield `𝕜 ⊆ ℂ`
(uncountably many if `𝕜` is uncountable). -/
structure TerasomaInput where
  /-- the K3 surface of degree `12` over `ℚ` -/
  S : Scheme.{0}
  [varietyS : Variety ℚ S]
  /-- `S` is a K3 surface of degree `12` (named predicate). -/
  isK3 : IsK3Degree12 ℚ S
  /-- `S` is `K`-trivial (named predicate). -/
  kTrivial : IsKTrivial ℚ S
  /-- `S` has geometric Picard rank one. -/
  picardOne : PicardRankOneGeom ℚ S
  /-- the length-three subscheme `Σ ⊂ S` (three general `ℚ`-points of `S`) -/
  Sigma : Scheme.{0}
  [overSigma : Sigma.Over (Spec (.of ℚ))]
  /-- the closed immersion `Σ ⟶ S` -/
  sigma : Sigma ⟶ S
  [isOverSigma : sigma.IsOver (Spec (.of ℚ))]
  [isClosedImmersionSigma : IsClosedImmersion sigma]
  [isReducedSigma : IsReduced Sigma]
  [smoothSigma : Smooth sigma]
  /-- `Σ` has length three (named predicate). -/
  hasLengthThree : HasLengthThree ℚ sigma
  /-- `(S, Σ)` is HL-admissible. -/
  hl : HLAdmissible ℚ sigma

attribute [instance] TerasomaInput.varietyS TerasomaInput.overSigma
  TerasomaInput.isOverSigma

/-- **Named geometric input: Theorem `thm-HL`(1)–(4) + its "defined over `ℚ`" clause.**

From an HL-admissible pair `(S, Σ)` over `ℚ` (the input `T`) the Hassett–Lai construction produces
the whole L-link geometry over `ℚ` (the `ℚ`-model `data` of the link: the two K3 centres, `ℙ⁴` with
the birational `ψ` and its two exceptional divisors, the `ℙ¹`-bundle bridge, and the strongly
rational transports to `𝔸⁴`), together with the second pair `(S', Σ')` — the surface `S'` from
which `ψ⁻¹` is constructed the same way, with its length-three subscheme `Σ'` — and the two
centres are *geometrically* non-isomorphic. -/
structure HassettLaiTheorem (T : TerasomaInput) where
  /-- the `ℚ`-model of the L-link of `thm:K3` -/
  data : K3Data ℚ
  /-- the first centre of the link is the input surface `T.S`, up to `ℚ`-isomorphism -/
  centre : IsoOver ℚ T.S data.S
  /-- the length-three subscheme `Σ' ⊂ S'` from which `ψ⁻¹` is constructed -/
  Sigma' : Scheme.{0}
  [overSigma' : Sigma'.Over (Spec (.of ℚ))]
  /-- the closed immersion `Σ' ⟶ S'` -/
  sigma' : Sigma' ⟶ data.S'
  [isOverSigma' : sigma'.IsOver (Spec (.of ℚ))]
  [isClosedImmersionSigma' : IsClosedImmersion sigma']
  [isReducedSigma' : IsReduced Sigma']
  [smoothSigma' : Smooth sigma']
  /-- `Σ'` has length three (named predicate). -/
  hasLengthThree' : HasLengthThree ℚ sigma'
  /-- `(S', Σ')` is again HL-admissible (`ψ⁻¹` is constructed the same way from it). -/
  hl' : HLAdmissible ℚ sigma'
  /-- `S_ℂ ≄ S'_ℂ`: the two centres are geometrically non-isomorphic (Hassett–Lai Thm 3.1 with
  Oguiso Prop 1.10: `S'_ℂ` is the unique non-trivial Fourier–Mukai partner of `S_ℂ`). -/
  notIsoGeom : ¬ IsoOver ℂ (baseChange ℚ ℂ data.S) (baseChange ℚ ℂ data.S')

  /- ### Base-change-uniform clauses

  The clauses below are the part of the *geometric* input `thm-HL` needed to run the descent: each
  says that one ingredient of the `ℚ`-model behaves under base change as its geometric description
  predicts.  They are all statements about the `ℚ`-model `data`, each true in the Hassett–Lai
  situation, and each of the same nature as the clauses of `thm-HL` itself — for instance
  `xCodimOne` is exactly (L3) of the definition of an L-link ("the exceptional divisors of the two
  blow-ups are irreducible").  Everything else about the descent — the `𝕜`-model of the link, the
  identification of its exceptional divisors with the base changes of `x`, `y`, the
  non-isomorphism of its two centres and the non-vanishing of the coefficient — is *proved*
  from them, in `Submission/Work/K3/Uniform.lean`. -/

  /-- `S` is geometrically integral (it is a K3 surface over `ℚ`). -/
  [geomIntS : GeometricallyIntegral (data.S ↘ Spec (.of ℚ))]
  /-- `S'` is geometrically integral. -/
  [geomIntS' : GeometricallyIntegral (data.S' ↘ Spec (.of ℚ))]
  /-- the fourfold `P` is geometrically integral (a model of `ℙ⁴`). -/
  [geomIntP : GeometricallyIntegral (data.P ↘ Spec (.of ℚ))]
  /-- `S_𝕜` is again a K3 surface of degree `12`. -/
  isK3_bc : ∀ (𝕜 : Subfield ℂ) [Variety ↥𝕜 (baseChange ℚ ↥𝕜 data.S)],
    IsK3Degree12 ↥𝕜 (baseChange ℚ ↥𝕜 data.S)
  /-- `S_𝕜` is `K`-trivial. -/
  kTrivial_bc : ∀ (𝕜 : Subfield ℂ) [Variety ↥𝕜 (baseChange ℚ ↥𝕜 data.S)],
    IsKTrivial ↥𝕜 (baseChange ℚ ↥𝕜 data.S)
  /-- `S_𝕜` has geometric Picard rank one. -/
  picardOne_bc : ∀ (𝕜 : Subfield ℂ) [Variety ↥𝕜 (baseChange ℚ ↥𝕜 data.S)],
    PicardRankOneGeom ↥𝕜 (baseChange ℚ ↥𝕜 data.S)
  /-- `S'_𝕜` is again a K3 surface of degree `12`. -/
  isK3'_bc : ∀ (𝕜 : Subfield ℂ) [Variety ↥𝕜 (baseChange ℚ ↥𝕜 data.S')],
    IsK3Degree12 ↥𝕜 (baseChange ℚ ↥𝕜 data.S')
  /-- `S'_𝕜` is `K`-trivial. -/
  kTrivial'_bc : ∀ (𝕜 : Subfield ℂ) [Variety ↥𝕜 (baseChange ℚ ↥𝕜 data.S')],
    IsKTrivial ↥𝕜 (baseChange ℚ ↥𝕜 data.S')
  /-- `S'_𝕜` has geometric Picard rank one. -/
  picardOne'_bc : ∀ (𝕜 : Subfield ℂ) [Variety ↥𝕜 (baseChange ℚ ↥𝕜 data.S')],
    PicardRankOneGeom ↥𝕜 (baseChange ℚ ↥𝕜 data.S')
  /-- the length-three subscheme `Σ'` base changes to a length-three subscheme. -/
  hasLengthThree_bc : ∀ (𝕜 : Subfield ℂ), HasLengthThree ↥𝕜 (baseChangeMap ℚ ↥𝕜 sigma')
  /-- the HL-admissible pair `(S', Σ')` base changes to an HL-admissible pair
  (`HLAdmissible 𝕜 σ` only refers to the `ℂ`-fibre of `σ`). -/
  hl_bc : ∀ (𝕜 : Subfield ℂ), HLAdmissible ↥𝕜 (baseChangeMap ℚ ↥𝕜 sigma')
  /-- **(L3) transported.**  The divisor `X = closure x` is geometrically irreducible: over every
  subfield `𝕜 ⊆ ℂ` the fibre of `P_𝕜 → P_ℚ` over `x` has exactly one point of codimension one,
  the generic point of the base-changed divisor. -/
  x_codim1 : ∀ (𝕜 : Subfield ℂ), ∃! p : baseChange ℚ ↥𝕜 data.P,
    baseChangeProj ℚ ↥𝕜 data.P p = data.x ∧ coheight p = 1
  /-- **(L3) transported**, for the other exceptional divisor. -/
  y_codim1 : ∀ (𝕜 : Subfield ℂ), ∃! p : baseChange ℚ ↥𝕜 data.P,
    baseChangeProj ℚ ↥𝕜 data.P p = data.y ∧ coheight p = 1
  /-- **The non-isomorphism locus of `ψ` base changes.**  Every point of `P_𝕜` lying over the
  (geometrically irreducible) divisor `x` is a point at which the base-changed map fails to be an
  isomorphism: the divisor `X` is contained in the (closed) non-isomorphism locus of `ψ`, and the
  latter is defined over `ℚ`. -/
  x_notIso : ∀ (𝕜 : Subfield ℂ) [IrreducibleSpace (baseChange ℚ ↥𝕜 data.P)]
    (Ψ : (baseChange ℚ ↥𝕜 data.P).BirationalMap (baseChange ℚ ↥𝕜 data.P)),
    (∀ (g : data.P.PartialMap data.P) [g.IsOver (Spec (.of ℚ))], g.toRationalMap = data.ψ.hom →
      (PartialMap.baseChangeAlong (specMap ℚ ↥𝕜) g).toRationalMap = Ψ.hom) →
    ∀ p : baseChange ℚ ↥𝕜 data.P, baseChangeProj ℚ ↥𝕜 data.P p = data.x → ¬ IsIsoAt Ψ p
  /-- **The non-isomorphism locus of `ψ⁻¹` base changes.** -/
  y_notIso : ∀ (𝕜 : Subfield ℂ) [IrreducibleSpace (baseChange ℚ ↥𝕜 data.P)]
    (Ψ : (baseChange ℚ ↥𝕜 data.P).BirationalMap (baseChange ℚ ↥𝕜 data.P)),
    (∀ (g : data.P.PartialMap data.P) [g.IsOver (Spec (.of ℚ))], g.toRationalMap = data.ψ.inv →
      (PartialMap.baseChangeAlong (specMap ℚ ↥𝕜) g).toRationalMap = Ψ.hom) →
    ∀ p : baseChange ℚ ↥𝕜 data.P, baseChangeProj ℚ ↥𝕜 data.P p = data.y → ¬ IsIsoAt Ψ p
  /-- **The `ℙ¹`-bundle bridge, base-change-uniform.**  The exceptional divisor `y` is birational
  to `S × ℙ¹` and `x` to `S' × ℙ¹`; hence over every subfield `𝕜 ⊆ ℂ` an isomorphism of the
  function fields of the two base-changed divisors forces `S_𝕜` and `S'_𝕜` to be stably
  birational. -/
  bridge_bc : ∀ (𝕜 : Subfield ℂ) [Variety ↥𝕜 (baseChange ℚ ↥𝕜 data.S)]
    [Variety ↥𝕜 (baseChange ℚ ↥𝕜 data.S')] (p q : baseChange ℚ ↥𝕜 data.P),
    baseChangeProj ℚ ↥𝕜 data.P p = data.x → coheight p = 1 →
    baseChangeProj ℚ ↥𝕜 data.P q = data.y → coheight q = 1 →
    ResEquiv ↥𝕜 q p → StablyBirational ↥𝕜 (baseChange ℚ ↥𝕜 data.S) (baseChange ℚ ↥𝕜 data.S')
  /-- **Strong rationality base changes.**  For every subfield `𝕜 ⊆ ℂ` there are transports
  `ε_𝕜 : 𝔸⁴_𝕜 ⤏ P_𝕜` and `δ_𝕜 : P_𝕜 ⤏ 𝔸⁴_𝕜` over `𝕜` whose invariant coefficient vanishes at
  every base point (they are the base changes of the `ℚ`-transports `ε`, `δ` of the model).
  Strong rationality of `ℙ⁴` is what makes the coefficient of the link an invariant of the
  Cremona group; being a statement about `ℙ⁴` and not about the link, it is recorded here
  uniformly, as a clause about the `ℚ`-model. -/
  transports_bc : ∀ (𝕜 : Subfield ℂ) [IrreducibleSpace (baseChange ℚ ↥𝕜 data.P)],
    ∃ (ε : (Affine4 ↥𝕜).BirationalMap (baseChange ℚ ↥𝕜 data.P))
      (δ : (baseChange ℚ ↥𝕜 data.P).BirationalMap (Affine4 ↥𝕜)),
      ε.IsOver (Spec (.of ↥𝕜)) ∧ δ.IsOver (Spec (.of ↥𝕜)) ∧
      (∀ z : baseChange ℚ ↥𝕜 data.P, cInv ↥𝕜 z ε = 0) ∧
      (∀ z : baseChange ℚ ↥𝕜 data.P, cInv ↥𝕜 z δ = 0)

attribute [instance] HassettLaiTheorem.overSigma' HassettLaiTheorem.isOverSigma'
  HassettLaiTheorem.geomIntS HassettLaiTheorem.geomIntS' HassettLaiTheorem.geomIntP
attribute [instance] HassettLaiTheorem.isClosedImmersionSigma' HassettLaiTheorem.isReducedSigma'
  HassettLaiTheorem.smoothSigma'

/-- **The descent step of `thm:K3`** (the last sentence of the proof of `thm-HL`): the `𝕜`-model
of the `ℚ`-link, for a subfield `𝕜 ⊆ ℂ`.

For `𝕜 = ℚ` the paper's proof of that sentence reads: *`ψ` is defined over `ℚ` by construction
(the quartic system has `ℚ`-coefficients); `S'_0` is the fundamental locus of `ψ⁻¹`, hence
`ℚ`-defined; `S'` is the minimal model of the normalisation of `S'_0`; `Σ'` is the image of the
`(-1)`-curves*; hence the whole output is defined over `ℚ` — and therefore over every `𝕜 ⊇ ℚ`.

We record the outcome: the `𝕜`-model `data` of the link (the birational `ψ_𝕜` with its two
exceptional divisors and their function fields over `𝕜`), the `𝕜`-model `SigmaK` of the pair
`(S', Σ')`, and the base-change identifications of `S_𝕜`, `S'_𝕜`, `Σ'` with the `ℚ`-model's.

The *non-isomorphism* of the two `𝕜`-centres is **proved** from this data
(`Work.K3.HLDescent.notIso`), and since `Submission/Work/K3/Uniform.lean` the structure itself is
**constructed** from `h` by base change (`Work.K3.HassettLaiTheorem.toHLDescent`): the two centres,
the fourfold and the link map are the base changes of the `ℚ`-model's, the two exceptional divisors
are the base-changed divisors (with `exDiv ψ_𝕜 = {x_𝕜}`, `exDiv ψ_𝕜⁻¹ = {y_𝕜}` *proved*, see
`Work.K3.exDiv_psiBC`), and `Σ'_𝕜` is the base change of `Σ'`.  See `NOTES.md` §6(f). -/
structure HLDescent (T : TerasomaInput) (h : HassettLaiTheorem T) (𝕜 : Subfield ℂ) where
  /-- the `𝕜`-model of the L-link -/
  data : K3Data 𝕜
  /-- the first centre is the base change of the `ℚ`-model's first centre -/
  centre : IsoOver 𝕜 (baseChange ℚ 𝕜 h.data.S) data.S
  /-- the Fourier–Mukai partner is the base change of the `ℚ`-model's second centre -/
  centrePartner : IsoOver 𝕜 (baseChange ℚ 𝕜 h.data.S') data.S'
  /-- the `𝕜`-model `Σ'_𝕜` of the length-three subscheme `Σ' ⊂ S'` -/
  SigmaK : Scheme.{0}
  [overSigmaK : SigmaK.Over (Spec (.of 𝕜))]
  /-- the closed immersion `Σ'_𝕜 ⟶ S'_𝕜` -/
  sigmaK : SigmaK ⟶ data.S'
  [isOverSigmaK : sigmaK.IsOver (Spec (.of 𝕜))]
  [isClosedImmersionSigmaK : IsClosedImmersion sigmaK]
  [isReducedSigmaK : IsReduced SigmaK]
  [smoothSigmaK : Smooth sigmaK]
  /-- `Σ'_𝕜` has length three (named predicate). -/
  hasLengthThreeK : HasLengthThree 𝕜 sigmaK
  /-- `(S'_𝕜, Σ'_𝕜)` is HL-admissible over `𝕜` (`ψ_𝕜⁻¹` is constructed the same way from it). -/
  hlK : HLAdmissible 𝕜 sigmaK
  /-- the pair `(S'_𝕜, Σ'_𝕜)` is the base change of `(S'_ℚ, Σ'_ℚ)` -/
  sigmaPartner : IsoOver 𝕜 (baseChange ℚ 𝕜 h.Sigma') SigmaK

/-- **Named input: Totaro's theorem** (`thm:BurtCY`, `cor-CYnSB`).

Let `X`, `Y` be non-isomorphic `K`-trivial varieties of Picard number one over a field.  Then `X`
and `Y` are not stably birational (indeed `X × W` is not birational to `Y × W` for any separably
rationally connected `W`).  Stated here for the two K3 surfaces of the link, in the form in which
the theorem consumes it. -/
structure TotaroInput (𝕜 : Type) [Field 𝕜] : Prop where
  /-- `K`-trivial, Picard number one, non-isomorphic `⟹` not stably birational. -/
  not_stablyBirat_of_not_iso : ∀ (X Y : Scheme.{0}) [Variety 𝕜 X] [Variety 𝕜 Y],
    IsKTrivial 𝕜 X → IsKTrivial 𝕜 Y → PicardRankOneGeom 𝕜 X → PicardRankOneGeom 𝕜 Y →
    ¬ IsoOver 𝕜 X Y → ¬ StablyBirational 𝕜 X Y

/-- **The per-pair form of Totaro's input** — see `Work.CY3.TotaroInputAt` for why the universal
form is not instantiable (its hypotheses `IsKTrivial`, `PicardRankOneGeom` are fieldless, so it
quantifies over all pairs of `𝕜`-varieties; `Work.Wire123.not_k3TotaroInput` refutes it), and why
the pair form is the shape in which the input is consumed (each link uses it at its own two
centres only). -/
structure TotaroInputAt (𝕜 : Type) [Field 𝕜] (X Y : Scheme.{0}) [Variety 𝕜 X] [Variety 𝕜 Y] :
    Prop where
  /-- non-isomorphic `K`-trivial varieties of Picard rank one are not stably birational -/
  not_stablyBirat : ¬ IsoOver 𝕜 X Y → ¬ StablyBirational 𝕜 X Y

/-- The universal input gives the pair form at every pair satisfying its (named) hypotheses. -/
theorem TotaroInput.toInputAt (𝕜 : Type) [Field 𝕜] (T : TotaroInput 𝕜) {X Y : Scheme.{0}}
    [Variety 𝕜 X] [Variety 𝕜 Y] (hX : IsKTrivial 𝕜 X) (hY : IsKTrivial 𝕜 Y) (pX : PicardRankOneGeom 𝕜 X)
    (pY : PicardRankOneGeom 𝕜 Y) : TotaroInputAt 𝕜 X Y :=
  ⟨fun hne => T.not_stablyBirat_of_not_iso X Y hX hY pX pY hne⟩

/-! ## 2. From the inputs to the non-triviality of the link -/

variable {𝕜 : Type} [Field 𝕜]

/-- **Totaro's input enters the link.**  If the two centres of the geometric link data are not
isomorphic over `𝕜`, then the two exceptional divisors do not have isomorphic function fields:
by the `ℙ¹`-bundle bridge `D.bridge`, an isomorphism of the function fields `κ(y) ≅ κ(x)` would
make `S` and `S'` stably birational, contradicting Totaro's input. -/
theorem K3Data.not_resEquiv_yx_of_totaro (D : K3Data 𝕜) (T : TotaroInputAt 𝕜 D.S D.S')
    (h : ¬ IsoOver 𝕜 D.S D.S') : ¬ ResEquiv 𝕜 D.y D.x := fun hres =>
  T.not_stablyBirat h (D.bridge hres)

/-- **The K3 L-link**, produced from the geometric data, Totaro's input and the failure of the
centres to be isomorphic over `𝕜`. -/
noncomputable def K3Data.toK3Link (D : K3Data 𝕜) (T : TotaroInputAt 𝕜 D.S D.S')
    (h : ¬ IsoOver 𝕜 D.S D.S') : K3Link 𝕜 :=
  { toK3Data := D, not_resEquiv_yx := D.not_resEquiv_yx_of_totaro T h }

/-- The non-vanishing of the invariant coefficient of the link, directly from the geometric data
and the two named inputs.  This is the shape consumed by `Work.Motivic.not_gen_of_cInv_ne_zero`
for `n = 4`. -/
theorem K3Data.exists_cInv_ne_zero (D : K3Data 𝕜) (T : TotaroInputAt 𝕜 D.S D.S')
    (h : ¬ IsoOver 𝕜 D.S D.S') :
    ∃ (Z : Scheme.{0}) (_ : Z.Over (Spec (.of 𝕜))) (z₀ : Z) (φ : Cr 𝕜 4),
      cInv 𝕜 z₀ (φ : (Affine4 𝕜).BirationalMap (Affine4 𝕜)) ≠ 0 :=
  K3Link.exists_cInv_ne_zero (D.toK3Link T h)

end Work.K3
