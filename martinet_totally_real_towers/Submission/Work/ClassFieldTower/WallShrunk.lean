import Mathlib
import Submission.Work.ClassFieldTower.Defs
import Submission.Work.ClassFieldTower.ProTwoDefs
import Submission.Work.ClassFieldTower.ProTwo
import Submission.Work.ClassFieldTower.ProTwoGenus
import Submission.Work.ClassFieldTower.ProTwoGeneratorRank
import Submission.Work.ClassFieldTower.Wall
import Submission.Work.ClassFieldTower.ResiduallyFiniteGaloisGroup
import Submission.Work.ClassFieldTower.five_le_of_surjective_zmodTwo_five
import Submission.Work.ClassFieldTower.exists_fiveUnramifiedQuadratics_of_unramified_exponentTwo
import Submission.Work.ClassFieldTower.hasGenusLevel_witness
import Submission.Work.ClassFieldTower.WitnessField
import Submission.Work.ClassFieldTower.Bridge
import Submission.Work.ProPDeficiency.Deficiency

/-!
# `Work.ClassFieldTower.WallShrunk` -- the wall split into its two classical halves

`Work.ClassFieldTower.KcWall` (= `ProTwoShafarevichKochInput Kc`, `Wall.lean`) bundles four things:

1. the existence of an abstract finitely presented group `G` whose finite `2`-quotients are the
   finite unramified pro-`2` Galois extensions of `Kc` (`DescribesMaximalProTwo`), i.e. the *pro-`2`
   finite presentability* of `G_∅` over a countable model;
2. `ResiduallyFiniteTwoGroup G`;
3. minimality of the generating set `α`;
4. the relation count `#rel ≤ #α + 1` -- the classical Shafarevich--Koch deficiency bound.

This module splits the bundle into named pieces and *derives* as much as is derivable:

* `KcModelData` -- item 1--3, in the **strictly weaker** form in which the full quantifier
  "every finite unramified pro-`2` `L/Kc` is a quotient of `G`" (`DescribesMaximalProTwo`'s second
  conjunct) is replaced by the single, checkable statement that the *genus level* of `Kc`
  (proved: `hasGenusLevel_witness`) gives a surjection `G ↠ (𝔽₂)^5`;
* `KcRelationBound` -- item 4 alone, as a theorem **about every such model**: the Shafarevich--Koch
  deficiency bound, i.e. `df(G_∅) = r - d ≤ d₂(O_{Kc}^×) = 1` (Koch, *Galois Theory of
  p-Extensions*, Ch. 11 Thm 11.3; Neukirch--Schmidt--Wingberg Cor. 10.7.7, via
  `Sha_∅ ↪ C_∅ = (V_∅/K^{×2})^∨` with `V_∅ = {x ∈ K^× : (x) = I²}`).  This is THE single
  classical input; everything else about the bundle is either proved here or derived from it;
* `KcShrunkInput` -- the form actually consumed by the Golod--Shafarevich argument (relation count
  + minimality + residual `2`-finiteness + realization of the finite `2`-quotients + the genus
  surjection).  It is **strictly weaker** than `KcWall`, and it still yields the conclusion.

**WARNING (added later, machine-checked in `RefuteRelationBound.lean`).**  The universally
quantified form `KcRelationBound` is **FALSE**, and so is the decomposition
`KcModelData ∧ KcRelationBound`: `KcModelData` is a *theorem* (it is satisfied by the explicit
finite genus model `GF` of `FiniteModelDefs.lean`, see `Work.ClassFieldTower.kcModelData`), while
`KcRelationBound` is refuted by `Work.ClassFieldTower.not_kcRelationBound` -- a finite `2`-group
cannot have a minimal presentation with `#β ≥ 5` generators and `≤ #β + 1` relators (the finite
`p`-group Golod--Shafarevich inequality, Chapter B).  **The sound arithmetic input is the
existential `KcShrunkInput`** (equivalently `KcWall` or `KcPresentationWall`), which forces its
witness group to be infinite and therefore cannot be refuted this way.  The theorems
`kcShrunkInput_of_modelData_and_relationBound` and
`infiniteProTwoExtension_of_modelData_and_relationBound` below are *vacuous* and are deprecated.

Main results:

* `infiniteProTwoExtension_of_kcShrunkInput` : `KcShrunkInput → InfiniteProTwoExtension Kc`
  (`G_∅` is infinite -- the deliverable's conclusion), plus the tower / root-discriminant /
  `UnramifiedPro2TowerWall` / `BoundedRdTowerWall` consequences;
* `kcShrunkInput_of_kcWall` : `KcWall → KcShrunkInput` (the whole bundle of `KcWall` implies the
  shrunk input; in particular direction (b) of `DescribesMaximalProTwo` is only ever needed to
  produce the genus surjection, and `5 ≤ #α` is *derived*, not assumed);
* `kcShrunkInput_of_modelData_and_relationBound` and
  `infiniteProTwoExtension_of_modelData_and_relationBound` : the two classical halves suffice --
  **DEPRECATED and VACUOUS**, see the warning above (`KcRelationBound` is refuted);
* `kcRelationBound_iff_deficiency` : the relation count in the `Work.ProPDeficiency` normalisation
  (`Deficiency d r (-1)`, i.e. `df ≤ d₂(O_K^×) = 1`).

So the remaining classical input is isolated to ONE named, citable *existential* statement
(`KcShrunkInput`, equivalently `KcWall` / `KcPresentationWall`), and half of `KcWall`'s bundle (the
generator bound and the description direction used here) is discharged by this chapter.  The
`KcRelationBound` / `KcModelData` decomposition is refuted (`not_kcRelationBound`) and must not be
used.
-/

set_option linter.style.haveILetI false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

open scoped Classical
open scoped NumberField
open NumberField

noncomputable section

namespace Work.ClassFieldTower

/-! ## 1. The `(𝔽₂)^5`-quotient and its target group -/

/-- The target of the five independent unramified quadratics: `(𝔽₂)^5` (the same group as
`Multiplicative (Fin 5 → ZMod 2)`, definitionally). -/
abbrev F2five : Type := Fin 5 → Multiplicative (ZMod 2)

/-- **The genus level of `Kc` gives a surjection `G ↠ (𝔽₂)^5`** out of any group `G` whose finite
`2`-quotients are the unramified `2`-extensions of `Kc` (direction (b) of
`DescribesMaximalProTwo`), with no class field theory: `hasGenusLevel_witness` supplies an
unramified exponent-`2` extension of degree `2^5`, hence a quotient `G ⧸ N ≅ (𝔽₂)^5`. -/
theorem exists_surjective_f2five_of_describes {G : Type*} [Group G]
    (hdesc : DescribesMaximalProTwo Kc G) :
    ∃ φ : G →* F2five, Function.Surjective φ := by
  classical
  obtain ⟨L, iL, iNL, iAL, hfd, hgal, hunr, hexp, hcard⟩ := hasGenusLevel_witness
  letI : Field L := iL
  letI : NumberField L := iNL
  letI : Algebra Kc L := iAL
  letI : FiniteDimensional Kc L := hfd
  letI : IsGalois Kc L := hgal
  have hpg : IsPGroup 2 (L ≃ₐ[Kc] L) := by
    rw [isPGroup_iff_pow_pow_eq_one]
    intro σ
    exact ⟨1, by rw [pow_one]; exact hexp σ⟩
  obtain ⟨N, hN, hfinN, hpgN, ⟨eN⟩⟩ := hdesc.2 L hunr hpg
  haveI : N.Normal := hN
  haveI : Fintype (G ⧸ N) := Fintype.ofFinite _
  -- `Gal(L/Kc)` is a finite group of exponent `2` and order `2^5`, hence `(𝔽₂)^5`
  have h2N : ∀ z : G ⧸ N, z ^ 2 = 1 := by
    intro z
    refine eN.injective ?_
    rw [map_pow, hexp (eN z), map_one]
  haveI : IsMulCommutative (G ⧸ N) :=
    IsMulCommutative.of_comm (fun a b => commute_of_sq_eq_one h2N a b)
  have hcardN : Nat.card (G ⧸ N) = 2 ^ 5 := by
    rw [Nat.card_congr eN.toEquiv]
    exact hcard
  obtain ⟨e5⟩ :=
    Commons.GroupTheory.SpecificGroups.ZModProd.exists_mulEquiv_multiplicative_fin_zmod_two_of_fintype_commutative_pow_two_eq_one_card
      (G := G ⧸ N) h2N hcardN
  exact ⟨e5.toMonoidHom.comp (QuotientGroup.mk' N),
    e5.surjective.comp (QuotientGroup.mk'_surjective N)⟩

/-! ## 2. The two classical halves -/

/-- **(I) THE MODEL HALF: pro-`2` finite presentability of `G_∅` over a countable model.**

There is an abstract finitely presented group `G` with a minimal generating set `α` and relators
`rel`, which is residually a finite `2`-group (so that `G` embeds in its pro-`2` completion), whose
finite `2`-quotients are realized by unramified extensions of `Kc`
(`RealizedByUnramifiedExtensions`), and which maps onto `(𝔽₂)^5` (the genus level).

Note that this is *strictly weaker* than `ProTwoShafarevichKochInput Kc` minus the relation count:
the full direction (b) of `DescribesMaximalProTwo` is replaced by the single genus surjection, and
the generator bound `5 ≤ #α` is *derived* from it (`five_le_of_surjective_zmodTwo_five`).

**This proposition is a THEOREM** -- it is satisfied by the explicit *finite* genus model
`Work.ClassFieldTower.GF` (`RefuteRelationBound.lean`,
`Work.ClassFieldTower.kcModelData`): every finite `2`-quotient of `(𝔽₂)^5` is realized by an
unramified extension of `Kc` (`realizedByUnramifiedExtensions_f2five`), and the five generators of
`(𝔽₂)^5` are minimal.  Hence `KcModelData` carries **no** arithmetic content: the whole content of
the Shafarevich--Koch input is the relation count, in the sound existential form `KcShrunkInput`. -/
def KcModelData : Prop :=
  ∃ (α : Type) (_ : Fintype α) (_ : DecidableEq α) (rel : Finset (FreeGroup α)),
    let G := FreeGroup α ⧸ Subgroup.normalClosure (rel : Set (FreeGroup α))
    (∀ S : Finset G, Subgroup.closure (S : Set G) = ⊤ → Fintype.card α ≤ S.card) ∧
    ResiduallyFiniteTwoGroup G ∧
    RealizedByUnramifiedExtensions Kc G ∧
    (∃ φ : G →* F2five, Function.Surjective φ)

/-- **(II) THE SINGLE CLASSICAL INPUT: the Shafarevich--Koch deficiency bound for `Kc`.**

`df(G_∅) = r - d ≤ d₂(O_{Kc}^×) = 1`: every model of the finite `2`-quotients of `G_∅` as in
`KcModelData` can be *re-presented* by a minimal generating set `β` with at most `#β + 1` relators.

Classically this is Koch, *Galois Theory of `p`-Extensions*, Ch. 11 Thm 11.3 (and
Neukirch--Schmidt--Wingberg Cor. 10.7.7), proved via the injection
`Sha_∅ ↪ C_∅ = (V_∅/K^{×2})^∨`, `V_∅ = {x ∈ K^× : (x) = I²}`.  For `Kc` the bound reads
`r ≤ d + d₂(O^×) = d + 1`; together with `d ≥ 5` (proved) it gives `4r ≤ d²`, hence, by the finite
`p`-group Golod--Shafarevich inequality, that `G_∅` is infinite.

*Status of this exact formulation: IT IS FALSE.*  The classical theorem is about the pro-`2`
presentation of `G_∅` itself, i.e. it asserts the *existence* of a model with a minimal
presentation of deficiency `≥ -1`; that sound statement is `KcShrunkInput` below.  The present
universally quantified form is **refuted**, machine-checked, in
`Submission/Work/ClassFieldTower/RefuteRelationBound.lean`:
`Work.ClassFieldTower.not_kcRelationBound : ¬ KcRelationBound`.  The reason is purely
group-theoretic: the hypotheses are satisfied by the *finite* genus model
`Work.ClassFieldTower.GF` (order `32`), but the demanded conclusion -- a minimal presentation with
`rel'.card ≤ #β + 1` and `#β ≥ 5` -- contradicts the finite `p`-group Golod--Shafarevich
inequality (Chapter B).  Do **not** try to prove `KcRelationBound`; the classical relation count is
the *existential* statement `KcShrunkInput` (equivalently `KcWall`, `KcPresentationWall`), which is
not refutable this way because it forces its witness group to be infinite. -/
def KcRelationBound : Prop :=
  ∀ (α : Type) (_ : Fintype α) (_ : DecidableEq α) (rel : Finset (FreeGroup α)),
    let G := FreeGroup α ⧸ Subgroup.normalClosure (rel : Set (FreeGroup α))
    (∀ S : Finset G, Subgroup.closure (S : Set G) = ⊤ → Fintype.card α ≤ S.card) →
    ResiduallyFiniteTwoGroup G →
    RealizedByUnramifiedExtensions Kc G →
    (∃ φ : G →* F2five, Function.Surjective φ) →
    ∃ (β : Type) (_ : Fintype β) (_ : DecidableEq β) (rel' : Finset (FreeGroup β)),
      Nonempty (G ≃* FreeGroup β ⧸ Subgroup.normalClosure (rel' : Set (FreeGroup β))) ∧
      (∀ S : Finset G, Subgroup.closure (S : Set G) = ⊤ → Fintype.card β ≤ S.card) ∧
      rel'.card ≤ Fintype.card β + 1

/-- **The relation count in the `Work.ProPDeficiency` normalisation**: `Deficiency β rel' (-1)`,
i.e. `df = r - d ≤ d₂(O_{Kc}^×) = 1`. -/
theorem kcRelationBound_iff_deficiency {β : Type} [Fintype β] (rel' : Finset (FreeGroup β)) :
    rel'.card ≤ Fintype.card β + 1 ↔
      Work.ProPDeficiency.Deficiency (Fintype.card β) rel'.card (-1) := by
  simp only [Work.ProPDeficiency.Deficiency]
  omega

/-! ## 3. The shrunk input and its consequences -/

/-- **THE SHRUNK INPUT** (the form actually consumed by Golod--Shafarevich).  Strictly weaker than
`KcWall`: a group `G` with a minimal generating set `α` and relators `rel` witnessing
`rel.card ≤ #α + 1`, residual `2`-finiteness, realization of the finite `2`-quotients by
unramified extensions (direction (a)), and the surjection `G ↠ (𝔽₂)^5` from the genus level.  The
generator bound `5 ≤ #α` is derived from that surjection. -/
def KcShrunkInput : Prop :=
  ∃ (G : Type) (_ : Group G) (α : Type) (_ : Fintype α) (_ : DecidableEq α)
    (rel : Finset (FreeGroup α)),
    Nonempty (G ≃* FreeGroup α ⧸ Subgroup.normalClosure (rel : Set (FreeGroup α))) ∧
    rel.card ≤ Fintype.card α + 1 ∧
    (∀ S : Finset G, Subgroup.closure (S : Set G) = ⊤ → Fintype.card α ≤ S.card) ∧
    ResiduallyFiniteTwoGroup G ∧
    RealizedByUnramifiedExtensions Kc G ∧
    5 ≤ Fintype.card α

/-- **THE TWO CLASSICAL HALVES SUFFICE**: `KcModelData` (pro-`2` presentability over a countable
model, residuality, minimality, realization of the finite `2`-quotients, the genus surjection)
together with the single classical theorem `KcRelationBound` (the Shafarevich--Koch deficiency
bound, which re-presents the same group by a minimal generating set with `rel ≤ d + 1`) give the
shrunk input. -/
@[deprecated (since := "2026-09-18")]
theorem kcShrunkInput_of_modelData_and_relationBound (h₁ : KcModelData) (h₂ : KcRelationBound) :
    KcShrunkInput := by
  obtain ⟨α, iα, iD, rel, hmin, hres, hreal, hsurj⟩ := h₁
  let G := FreeGroup α ⧸ Subgroup.normalClosure (rel : Set (FreeGroup α))
  obtain ⟨β, iβ, iDβ, rel', hpres, hminβ, hbound⟩ := h₂ α iα iD rel hmin hres hreal hsurj
  -- the genus surjection gives the generator bound
  obtain ⟨φ, hφ⟩ := hsurj
  have hpresβ : HasMinimalPresentation G (Fintype.card β) rel'.card :=
    ⟨β, iβ, iDβ, rel', rfl, rfl, hpres, hminβ⟩
  have h5 : 5 ≤ Fintype.card β := five_le_of_surjective_zmodTwo_five hpresβ φ hφ
  exact ⟨G, inferInstance, β, iβ, iDβ, rel', hpres, hbound, hminβ, hres, hreal, h5⟩

/-- **The presentation wall implies the shrunk input** (the Artin generator rank
`#α = rank₂ Cl(Kc)` supplies the numerical generator bound `5 ≤ #α` directly, via the proved
`five_le_classGroupTwoRank`). -/
theorem kcShrunkInput_of_kcPresentationWall (h : KcPresentationWall) : KcShrunkInput := by
  obtain ⟨α, iα, iD, rel, hgen, hrel, hmin, hres, hreal⟩ := h
  have h5 : 5 ≤ Fintype.card α := by rw [hgen]; exact five_le_classGroupTwoRank
  have hbound : rel.card ≤ Fintype.card α + 1 := by
    have h1 : rel.card ≤ Fintype.card α + unitTwoRank Kc := by rw [hgen]; exact hrel
    have h2 : unitTwoRank Kc ≤ 1 := unitTwoRank_witness_le_one
    omega
  exact ⟨FreeGroup α ⧸ Subgroup.normalClosure (rel : Set (FreeGroup α)), inferInstance,
    α, iα, iD, rel, ⟨MulEquiv.refl _⟩, hbound, hmin, hres, hreal, h5⟩

/-- **`KcWall` implies the shrunk input** (so nothing is lost by consuming the weaker form; the full
description direction of `KcWall` is only needed to produce the genus surjection, and the generator
bound is not assumed at all). -/
theorem kcShrunkInput_of_kcWall (h : KcWall) : KcShrunkInput := by
  obtain ⟨α, iα, iD, rel, hrel, hmin, hres, hdesc⟩ := h
  have h5 : 5 ≤ Fintype.card α :=
    five_le_card_of_genusLevel ⟨MulEquiv.refl _⟩ hmin hdesc hasGenusLevel_witness
  exact ⟨FreeGroup α ⧸ Subgroup.normalClosure (rel : Set (FreeGroup α)), inferInstance,
    α, iα, iD, rel, ⟨MulEquiv.refl _⟩, hrel, hmin, hres, hdesc.1, h5⟩

/-- **THE CONCLUSION FROM THE SHRUNK INPUT**: the maximal unramified pro-`2` extension of
`Kc = ℚ(√-30030)` is INFINITE. -/
theorem infiniteProTwoExtension_of_kcShrunkInput (h : KcShrunkInput) :
    InfiniteProTwoExtension Kc := by
  classical
  obtain ⟨G, iG, α, iα, iD, rel, hpres, hrel, hmin, hres, hreal, h5⟩ := h
  have hpos : 0 < Fintype.card α := by omega
  have hineq : 4 * rel.card ≤ Fintype.card α * Fintype.card α :=
    four_mul_le_sq_of_le_add_one hrel h5
  obtain ⟨M⟩ := exists_maximalUnramifiedProP Kc 2
  refine ⟨M, ?_⟩
  rw [M.infinite_galoisGroup_iff_unbounded_subfields]
  intro N
  obtain ⟨L, iL, iNL, iAL, hfd, hgal, hdeg, hdiff, hpgL⟩ :=
    exists_unramifiedLevel_of_proTwoPresentation (F := Kc) (G := G) rel
      hpres hmin hpos hineq hres hreal N
  letI : Field L := iL
  letI : NumberField L := iNL
  letI : Algebra Kc L := iAL
  letI : FiniteDimensional Kc L := hfd
  letI : IsGalois Kc L := hgal
  letI : IsPGroup 2 (L ≃ₐ[Kc] L) := hpgL
  obtain ⟨ψ, -⟩ := M.universal L hpgL hdiff
  let e : L ≃ₐ[Kc] ↥(ψ.fieldRange) := AlgEquiv.ofInjectiveField ψ
  haveI : FiniteDimensional Kc ↥(ψ.fieldRange) := e.toLinearEquiv.finiteDimensional
  haveI : IsGalois Kc ↥(ψ.fieldRange) := IsGalois.of_algEquiv e
  refine ⟨ψ.fieldRange, inferInstance, inferInstance, ?_⟩
  rw [← e.toLinearEquiv.finrank_eq]
  exact hdeg

/-- **The two classical halves give the conclusion** (packaged). -/
@[deprecated (since := "2026-09-18")]
theorem infiniteProTwoExtension_of_modelData_and_relationBound (h₁ : KcModelData)
    (h₂ : KcRelationBound) : InfiniteProTwoExtension Kc :=
  infiniteProTwoExtension_of_kcShrunkInput (kcShrunkInput_of_modelData_and_relationBound h₁ h₂)

/-- **Unramified levels of any prescribed degree from the shrunk input**, with constant root
discriminant `rootDiscr Kc`. -/
theorem exists_unramifiedLevel_rootDiscr_of_kcShrunkInput (h : KcShrunkInput) (N : ℕ) :
    ∃ (L : Type) (_ : Field L) (_ : NumberField L) (_ : Algebra Kc L)
      (_ : FiniteDimensional Kc L) (_ : IsGalois Kc L),
      N ≤ Module.finrank Kc L ∧ differentIdeal (𝓞 Kc) (𝓞 L) = ⊤ ∧
        NumberField.rootDiscr L = NumberField.rootDiscr Kc := by
  obtain ⟨M, hM⟩ := infiniteProTwoExtension_of_kcShrunkInput h
  exact exists_unramifiedLevel_of_infinite M hM N

/-- **The pointwise form consumed by `Submission.NumberField.boundedRdTowerWall_of_unbounded_unramified`.** -/
theorem unbounded_unramified_of_kcShrunkInput (h : KcShrunkInput) :
    ∀ N : ℕ, ∃ (L : Type) (_ : Field L) (_ : NumberField L) (_ : Algebra Kc L)
      (_ : FiniteDimensional Kc L),
      N ≤ Module.finrank Kc L ∧ differentIdeal (𝓞 Kc) (𝓞 L) = ⊤ := by
  intro N
  obtain ⟨L, iL, iNL, iAL, hfd, hgal, hdeg, hdiff, -⟩ :=
    exists_unramifiedLevel_rootDiscr_of_kcShrunkInput h N
  exact ⟨L, iL, iNL, iAL, hfd, hdeg, hdiff⟩

/-- **The main agent's `UnramifiedPro2TowerWall` from the shrunk input.** -/
theorem unramifiedPro2TowerWall_of_kcShrunkInput (h : KcShrunkInput) :
    Submission.NumberField.UnramifiedPro2TowerWall :=
  unramifiedPro2TowerWall_of_infiniteProTwoExtension (infiniteProTwoExtension_of_kcShrunkInput h)

/-- **The main agent's `BoundedRdTowerWall` from the shrunk input** (root-discriminant form). -/
theorem boundedRdTowerWall_of_kcShrunkInput (h : KcShrunkInput) :
    Submission.NumberField.BoundedRdTowerWall :=
  Submission.NumberField.boundedRdTowerWall_of_unramifiedPro2TowerWall
    (unramifiedPro2TowerWall_of_kcShrunkInput h)

/-- **The main agent's `BoundedDiscrTowerWall` from the shrunk input** (discriminant form). -/
theorem boundedDiscrTowerWall_of_kcShrunkInput (h : KcShrunkInput) :
    Submission.NumberField.BoundedDiscrTowerWall :=
  Submission.NumberField.boundedDiscrTowerWall_of_boundedRdTowerWall
    (boundedRdTowerWall_of_kcShrunkInput h)

end Work.ClassFieldTower
