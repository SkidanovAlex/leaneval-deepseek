import Mathlib
import Submission.Work.Serre.ThomCylDefs
import Submission.Work.Serre.C1Cyl
import Submission.Work.Serre.Engine
import Submission.Work.StemsB.Fibrations
import Submission.Work.RatHurewicz.AttachCells
import Submission.Work.Serre.TripleCohDefs
import Submission.Work.Serre.TripleCohLES
import Submission.Work.Serre.boundedFiveLemmaLES
import Submission.Work.Serre.discPairCellVanishingSucc
import Submission.Work.Serre.relCoh_extension
import Submission.Work.Serre.attachRelCohCellEquiv
import Submission.Work.Serre.cylRestrictHomeo
-- NOTE (H5): `Serre/modelThomRatPair` is deliberately NOT imported: it pulls
-- `Serre/ratShuffle`, and that file declares `Work.Serre.singSSet` a second time
-- (`Serre/E0Defs` declares the same name, and `E0Defs` is in this file's closure), so the
-- environment would fail at import time with "already contains 'Work.Serre.singSSet'".
import Submission.Work.Serre.cellCupUpper
import Submission.Work.Serre.CellMultiplicativity
import Submission.Work.StemsB.ModelThomStepRat
import Submission.Work.RatHurewicz.discPairSourceRankOne
import Submission.Work.Stems.fibreRestrictionInjectiveOfPos
import Submission.Work.Serre.DiscPair.joinedAux
import Submission.Work.Stems.cellStepInputs
import Submission.Work.Stems.ladderNaturality
import Submission.Work.Serre.thomCylLadder
import Submission.Work.Serre.thomCylLadderEps
import Submission.Work.Serre.attachRelCohVanishing
import Submission.Work.Serre.attachRelCohVanishingHigh
import Submission.Work.Serre.MVGlue.mvSetup
import Submission.Work.Serre.MVGlue.homotopyInverseMV
import Submission.Work.Serre.MVShift.HonestCup
import Submission.Work.Serre.MVShift.shS_delta_comm
import Submission.Work.Serre.MVShift.shKZeroRat
import Submission.Work.Serre.mvDeltaAuxDefs
import Submission.Work.Serre.DiscPair.cupRelChainHomology
import Submission.Work.Serre.MVGlue.glueCupIso
import Submission.Work.RatHurewicz.cellStepShell
import Submission.Work.Serre.thomCylCellStepAlt

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000


/-!
## STATE OF THE ART (session 21, agent for `Work.Stems.thomCylCellStepRace`)

**What this file now proves, and what is left.**  Write `Γ' = attachCells (D-2) Γ ι f`,
`S = ladS D Γ ι f = range (attachIncl …)`, `M = cyl q`, `A = range (cylIncl q)`,
`new = ladNew D ι f q = (cylRetract q)⁻¹S ∪ A`, and let `U` be the extension of the old Thom class
(`Work.Serre.exists_extensionClass`, proved) and `U_S = IH.choose`.

* `Work.Stems.ladderBijective` — the abstract comparison: if `G₁, G₂, TQ` are bijections and the
  naturality square `TQ ∘ G₁ = G₂ ∘ Φ` holds, then `Φ = G₂⁻¹ ∘ TQ ∘ G₁` is a bijection.
* **`Work.Stems.tp_isIso_of_ne`** — *the cup map with `U` is an isomorphism in every degree
  `m ∉ {D-1, D}` with `m + r + 1 ≤ N + 1`*, using only the naturality square `hG` of
  `Work.Stems.ladderNaturality`, the exactness of the two rows (`baseExact₂/₃`, `totExact₂/₃`) and
  the vanishing theorems (`attachRelCohVanishing`, `attachRelCohVanishingHigh`,
  `discPairCellVanishingSucc`): in those degrees `baseG m`, `totG (m + r + 1)` and `TQ m` are all
  *bijections*, so the square forces `TP m` to be a bijection.  **No cell comparison, no `TM`, no
  five-lemma ladder is needed** — in particular the construction of a `TM` (and the squares `hF`,
  `hδ`) can be dispensed with entirely.
* **`Work.Stems.ladderNaturalityG`** — the naturality square `hG`, from
  `Work.Stems.ladderNaturality` (proved by a colleague) and the extension property of `U`.
* **`Work.Stems.thomCylCellStepRace_of_cellIsos`** — for an extension class `U` of `IH.choose`
  (`Work.Serre.exists_extensionClass`), the cellular step reduces to exactly the two *cell degrees*:
  `IsIso (TP r q U (D-1))` and `IsIso (TP r q U D)`.
* **`Work.Stems.thomCylCellStepRace_of_highDim`** — **the cellular step holds unconditionally
  whenever the two cell degrees are out of range**, i.e. for `N + 1 < D + r` (equivalently
  `N ≤ D + r - 2`), which is the "easy regime": here the extension class of
  `Work.Serre.exists_extensionClass` witnesses the conclusion, and every degree in range is handled
  by `tp_isIso_of_ne`.  (The vacuous case `N < r` is included.)

**The two residual inputs, and why they are the crux.**

1. `hG` (the naturality square).  *PROVED* by a colleague in
   `Submission/Work/Stems/ladderNaturality.lean` (`Work.Stems.ladderNaturality`, axiom-clean): both
   sides are "restrict the cup product with `U` to the pair over the old part"; the proof is the
   naturality of `mixedCupC` under the inclusion `new ↪ cyl q` plus the extension property
   `tripleRestr U = uNew` and the pointwise identity
   `cylRetract q ∘ cylPreimageHomeo = cylRetract (q|_S)`
   (`DiscPair.cylRetract_cylPreimageHomeo`).  It is packaged here as
   `Work.Stems.ladderNaturalityG`, so the two theorems below take no `hG` hypothesis.
2. the two cell isos `IsIso (TP r q U (D-1))`, `IsIso (TP r q U D)`.  By the 3×3 five lemma these
   are *equivalent* (given `hG` and the same exactness/vanishing data) to
   * `θ := (Δ₂ ∘ TQ(D-1)) : ker F₁(D) → ker F₂(D+r+1)` being a bijection — for the degree `D-1`;
   * `TP D|_{im F₁(D)} : im F₁(D) → im F₂(D+r+1)` being a bijection — for the degree `D`; the two
     halves of the latter are `CellInjectivity` (`hB`) and `CellImageEqLower` (`hA`, the lower half
     of the comparison), the upper half being the *proved* `Work.Serre.cellCupUpper`.
   Equivalently: "there is a *bijective* `TM D : H^D(Γ',S) → H^{D+r+1}(M,new)` with
   `F₂ ∘ TM D = TP D ∘ F₁` and `TM D ∘ Δ₁ = Δ₂ ∘ TQ`" — and the point to beware of is that the
   `TM` produced by `Work.Serre.CellComparisonNode` (from `hA` and `hB` alone, by choosing a
   complement of `ker F₂`) has `ker TM = ker F₁(D)` and is therefore **not** injective (and does
   not satisfy the `hδ`-square either); the *correct* `TM D` is the direct sum of `θ` (on
   `ker F₁(D)`) and of the comparison on a complement of `ker F₁(D)`.  So a proof of the crux must
   supply both isos above — which is exactly what the rest of the fleet is working on
   (`Work.Serre.CellInjectivity`, `Work.Serre.CellImageEqLower`, the local multiplicativity over a
   cell, the MV gluing `Work.Serre.mvDeltaCupMixed` + `bijective_mixedCup_of_openCover`).

**Closing the target.**  If any of `Work.Serre.thomCylCellStepAlt`,
`Work.Serre.DiscPair.thomCylCellStepIndependent`, `Work.RatHurewicz.thomCylCellStepFreeProof` or the
strict/strict-strong variants becomes axiom-clean, the target below closes by
`import` + `exact` (their statements are definitionally equal to it).  Alternatively the two
residual inputs above close it.

**Retained from the earlier sessions** (still useful): `Work.Stems.isZero_relCoh_of_homeo`
(`IsZero` of relative cohomology transports along a homeomorphism of pairs) and
`Work.Stems.cylFibreRes_ne_zero_of_pos` (the fibrewise non-vanishing of the extension class, from
the *proved* `Work.Stems.fibreRestrictionInjectiveOfPos`), the latter being the input of the
"detection" route to the cell comparison.
-/



/-!
## Guidance for this file (relayed by AREA H5 from the project lead, 2026-09-27)

**Suggested route.**  Do *not* attack `Work.Serre.ThomCylAt r N q` head-on.  Prove instead the
*strengthened* cell step `Work.Serre.ThomCylAtStrong r N q`
(`Submission/Work/Serre/StrongThomDefs.lean`, **proved** to be sufficient:
`Work.Serre.thomCylAt_of_strong : ThomCylAtStrong r N q → ThomCylAt r N q`), i.e. the same cup-map
isomorphism together with the *fibre non-vanishing*
`∀ b, Work.Serre.DiscPair.cylFibreRes q b (r+1) U ≠ 0`, and run the **skeleton induction** with
that strengthening as the induction hypothesis over the old part (see
`Submission/Work/Serre/CWMODEL_CVN_NOTES.md` §13; the transfer lemma
`Work.Serre.cylFibreRes_ne_zero_of_oldPart` is already proved).  If the step at level `N` is hard,
prove the **strict-range** step at level `N - 1` first (the range `m + r + 1 ≤ N`), which avoids the
boundary degree; the statement at `N` is the strict statement at `N + 1`.

**Do not import** (their declarations are `sorry`-backed, so a one-line `exact` would inherit
`sorryAx` and `declare_proven()` will reject it): `Submission.Work.Serre.thomCylCellStepAlt`,
`Submission.Work.Serre.DiscPair.thomCylCellStepIndependent`,
`Submission.Work.Serre.eulerFibreRange`, `Submission.Work.Serre.cwModelThomCase`,
`Submission.Work.Serre.serreE3b`, `Submission.Work.RatHurewicz.gysinRangeFree`.  A *genuine* proof
is required.

**Import-island warning (measured 2026-09-27).**  Area SERRE currently has two sub-islands that
cannot be mixed: `Serre/E0Defs` and `Serre/ratShuffle` both declare `Work.Serre.singSSet`, so any
module importing both (directly or transitively) fails at import time.  This file is on the
`E0Defs` side (`discPairCellVanishingSucc`, `attachRelCohCellEquiv`, `cellCupUpper`,
`CellMultiplicativity`, `discPairSourceRankOne`, … all pull `E0Defs`), so **do not import**
`Serre/modelThomRatPair` (nor anything else pulling `Serre/ratShuffle`); use the `E0Defs`-side
local-model lemmas (`Serre/ModelThomRatPairNeutral`, `StemsB/ModelThomStepRat`) instead.  In
particular the local model Thom class is `Work.StemsB.modelThomRatAll` (declared in
`StemsB/ModelThomStepRat`, which pulls neither `ratShuffle` nor `E0Defs`, so it is safe here);
`Serre/modelThomRatPair` and `Serre/modelThomRatPairQ` are the `ratShuffle`-side versions and are
unusable in this file.

**Proved infrastructure worth using** (all harmless to import):
`Serre/StrongThomDefs`, `Serre/TripleCohDefs`, `Serre/TripleCohLES`, `Serre/boundedFiveLemmaLES`,
`Serre/discPairCellVanishingSucc`, `Serre/relCoh_extension`, `Serre/attachRelCohCellEquiv`,
`Serre/cylRestrictHomeo`, `Serre/modelThomRatPair`, `Serre/cellCupUpper`,
`Serre/CellMultiplicativity`, `Serre/ModelThomRatPairNeutral`, `StemsB/ModelThomStepRat`,
`RatHurewicz/discPairSourceRankOne`, `RatHurewicz/conePairConcentratedAtPoint`.
-/

/-!
**Note (H5, 2026-09-27; CORRECTED after a probe round with the project lead).**

* `hpos` is **available, proved and axiom-clean**: in exactly this context,
  `Work.Stems.cellStep_relCoh_ne_zero r N D hr hD hrN hΓ ι f q hq hpc hvan hgen IH :
  ¬ IsZero (RelCoh ℚ (r+1) (cyl q) (range (cylIncl q)))`
  (`Submission/Work/Stems/cellStepInputs.lean`, from the proved `DiscPair.discPairTargetLine`),
  which is the `hpos` hypothesis of every formulation of the detection.  Use it instead of
  re-deriving it.
* The `hinvis`-style hypotheses of `Work.Serre._opcr.fibreRestriction_ne_zero_of_invisible` and
  `..._of_pairComparison` are the hypothesis of the **invisible branch** of an *exhaustive case
  split* on the fibration (visible branch: the fibre restriction is non-zero for "trivial" reasons,
  handled by `fibreRestriction_ne_zero_of_visible`; invisible branch: the non-orientable /
  Klein-bottle situation).  They are **case hypotheses, not defects**: a bundle in the visible
  branch satisfies the *negation*, which is why the trivial `S^r`-bundle over `S^D` is **not** a
  counterexample to them.  (An earlier note in this file claimed the contrary; **that claim is
  WITHDRAWN**, as is `Submission/Work/Stems/hinvisRefuted`.)
* **WITHDRAWN too**: the earlier claim that `IsZero (RelCoh ℚ (r+1) (cyl q) (CMid q b))` fails for
  the Hopf fibration.  Recomputing the pair sequence: for `S¹ → S³ → S²`
  (`r = 1`, `N = 2`, `Γ = PUnit`, `D = 2`) one has `CMid q b = A ∪ P_b ≃ S³ ∨ S²`,
  `H^2(M) = ℚ = H^2(CMid)` and `i^* : H^2(M) → H^2(CMid)` is **injective** (it is non-zero, and both
  sides are one-dimensional), so `H^2(M, CMid) = ker(δ₂) = im(δ₁) = ker(H^1(M) → H^1(CMid)) = H^1(M)
  = 0`.  The vanishing **holds** there.  The route through
  `Work.Serre.fibreNonvanishing_of_pieces` is therefore alive; the rational pair comparison route
  (`Work.Serre.ratPairComparisonOneBoundary` + duality over ℚ) proves the same vanishing with no
  case split.

**1. The "shell trick".**  `Work.Serre.DiscPair.thomCylAt_of_relVanishing` applies with
`S = Set.range (attachIncl …)` and `V = Γ' \ (small closed balls, one per cell)`: the pair
`(V,S)` is a union of *annuli* (cells minus balls), relative to their boundary sphere, whose relative
cohomology vanishes (`(S^{D-1} × I, S^{D-1} × {1}) ≃ (S^{D-1},S^{D-1})`), and the corresponding
disc-pair bundle over such an annulus has relative cohomology
`H^j(W × (CF,F), W × base ∪ W₀ × CF) = 0` (relative Künneth: `H^*(W,W₀) = 0` and
`H^*(CF,F)` concentrated in degree `r+1`).  Hence **`IH` gives the whole cup isomorphism over every
*thickened* neighbourhood of the old part `S`, for free**.  What is left is the *last layer*: the
(closed) balls around the cell centres, where the relative cohomology of the pair does *not* vanish
(degree `D` and `D+r+1`) — this is precisely the cell comparison `TM(D)`.

**2. The correct form of the fibre-non-vanishing input (SIH).**  With `M = cyl q`, `A = range
(cylIncl q)`, `C = A ∪ P_b` (`P_b = (cylRetract q)⁻¹{b}`), the "detection" statement
(`ρ_b : H^{r+1}(M,A) → H^{r+1}(P_b,A_b)` injective / non-zero) is *equivalent* to

  * the map `H^{r+1}(M,C) → H^{r+1}(M,A)` is **zero** (triple LES: the kernel of
    `H^{r+1}(M,A) → H^{r+1}(C,A)` is its image), equivalently
  * the fibre fundamental class `[Z_b] ∈ H_{r+1}(P_b,A_b) = H_r(F_b)` **generates** the image of
    `H_{r+1}(M,A) → H_{r+1}(M,C)`-kernel, equivalently (over ℚ) the map
    `H_{r+1}(P_b,A_b) → H_{r+1}(M,A)` has image `= ker ∂`.

**4. The ladder.**  With SIH available (either from the detection (2) or from a *strong* induction
hypothesis over the old part), the standard ladder (`Submission/Work/Serre/THOMGAP_PLAN.md` §2–§3)
closes the target: the base row is the pair `(Γ',S)`, the total row the triple
`A ⊆ new ⊆ M` (`DiscPair.qTripleShort`), `TQ` is the transported `IH` cup map, `TP` the target cup
map, and the only genuine content is `TM(D)` (both sides are `∏_ι ℚ`, the map being "diagonal with
non-zero entries"); `hG` is the naturality of the mixed cup product
(`Work.StemsB.mixedCupC_pairNaturalR`), `hδ` the Leibniz rule
(`Work.StemsB.pairDelta_mixedCup_general_R`), and the five lemma is `boundedFiveLemmaLES`.
-/

namespace Work.Stems


open CategoryTheory

/-- **`IsZero` of relative rational cohomology is invariant under a homeomorphism of pairs.** -/
theorem isZero_relCoh_of_homeo {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (A : Set X) (B : Set Y) (e : X ≃ₜ Y) (he : ∀ x, x ∈ A ↔ e x ∈ B) (n : ℕ)
    (h : CategoryTheory.Limits.IsZero (Work.Thom.RelCoh ℚ n Y B)) :
    CategoryTheory.Limits.IsZero (Work.Thom.RelCoh ℚ n X A) := by
  haveI : CategoryTheory.IsIso (HomologicalComplex.homologyMap
      (Work.Cohomology.relComplexMap (X₁ := TopCat.of X) (X₂ := TopCat.of Y) ℚ A B
        (TopCat.ofHom (e : C(X, Y))) (fun x hx => (he x).mp hx)) n) :=
    Work.Thom.CapGlue.isIso_relComplexMap_homeomorph A B e he ℚ n
  exact CategoryTheory.Limits.IsZero.of_iso h ((CategoryTheory.asIso (HomologicalComplex.homologyMap
      (Work.Cohomology.relComplexMap (X₁ := TopCat.of X) (X₂ := TopCat.of Y) ℚ A B
        (TopCat.ofHom (e : C(X, Y))) (fun x hx => (he x).mp hx)) n)).symm)


/-- **SIH (the fibrewise non-vanishing of the extension class).**  Under the *positivity*
hypothesis `hpos` (available in the cellular-step context, where `IH` forces
`H^{r+1}(cyl q, A) ≅ ℚ`), the detection `Work.Stems.fibreRestrictionInjectiveOfPos` makes the fibre
restriction injective, so every non-zero class — in particular the extension `U` of the old Thom
class — has non-zero fibre restriction at *every* point of the base. -/
theorem cylFibreRes_ne_zero_of_pos {B : Type} [TopologicalSpace B] {X : Type} [TopologicalSpace X]
    (hB : PathConnectedSpace B) (q : C(X, B)) (hq : Work.StemsB.IsSerreFibration q) (r N : ℕ)
    (hr : 1 ≤ r) (hrN : r + 1 ≤ N)
    (hpc : ∀ b : B, PathConnectedSpace (Work.StemsB.fibre q b))
    (hvan : ∀ b : B, ∀ t : ℕ, 0 < t → t ≠ r → t ≤ N →
      CategoryTheory.Limits.IsZero (Work.Serre.ratH (TopCat.of (Work.StemsB.fibre q b)) t))
    (hgen : ∀ b : B, Nonempty (Work.Serre.ratH (TopCat.of (Work.StemsB.fibre q b)) r
      ≅ ModuleCat.of ℚ ℚ))
    (hpos : ¬ CategoryTheory.Limits.IsZero (Work.Thom.RelCoh ℚ (r + 1) (Work.Serre.cyl q)
        (Set.range (Work.Serre.cylIncl q))))
    (U : Work.Thom.RelCoh ℚ (r + 1) (Work.Serre.cyl q) (Set.range (Work.Serre.cylIncl q)))
    (hU : U ≠ 0) (b : B) :
    Work.Serre.DiscPair.cylFibreRes q b (r + 1) U ≠ 0 := by
  have hinj := Work.Stems.fibreRestrictionInjectiveOfPos hB q hq r N hr hrN hpc hvan hgen hpos b
  exact fun h0 => hU (hinj (by
    show (Work.Serre.DiscPair.cylFibreRes q b (r + 1)) U
      = (Work.Serre.DiscPair.cylFibreRes q b (r + 1)) 0
    rw [h0, map_zero]))

set_option backward.isDefEq.respectTransparency false

/-- **The degree-by-degree comparison of the ladder.**  If the two `G`-maps and the middle
vertical `TQ` are bijections and the naturality square holds, then the middle vertical `Φ` is a
bijection: `Φ = G₂⁻¹ ∘ TQ ∘ G₁`. -/
theorem ladderBijective {P₁ Q₁ P₂ Q₂ : Type*}
    [AddCommGroup P₁] [Module ℚ P₁] [AddCommGroup Q₁] [Module ℚ Q₁]
    [AddCommGroup P₂] [Module ℚ P₂] [AddCommGroup Q₂] [Module ℚ Q₂]
    (G₁ : P₁ →ₗ[ℚ] Q₁) (G₂ : P₂ →ₗ[ℚ] Q₂) (Φ : P₁ →ₗ[ℚ] P₂) (TQ : Q₁ →ₗ[ℚ] Q₂)
    (hG : ∀ p, TQ (G₁ p) = G₂ (Φ p))
    (hG₁ : Function.Bijective G₁) (hG₂ : Function.Bijective G₂) (hTQ : Function.Bijective TQ) :
    Function.Bijective Φ := by
  have hΦ : Φ = ((LinearEquiv.ofBijective G₂ hG₂).symm.toLinearMap).comp (TQ.comp G₁) := by
    ext p
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
    apply (LinearEquiv.ofBijective G₂ hG₂).injective
    rw [LinearEquiv.apply_symm_apply]
    exact (hG p).symm
  rw [hΦ]
  exact ((LinearEquiv.ofBijective G₂ hG₂).symm.bijective).comp (hTQ.comp hG₁)

/-- **The cup map is an isomorphism in every degree below the cell degree.** -/
theorem tp_isIso_of_ne (r N D : ℕ) (hr : 1 ≤ r) (hD : 2 ≤ D)
    {Γ : Type} [TopologicalSpace Γ] (hΓ : PathConnectedSpace Γ) (ι : Type)
    (f : ι → C(Work.RatHurewicz.cellSphere (D - 2), Γ))
    {X : Type} [TopologicalSpace X] (q : C(X, Work.RatHurewicz.attachCells (D - 2) Γ ι f))
    (hq : Work.StemsB.IsSerreFibration q)
    (hvan : ∀ γ : Work.RatHurewicz.attachCells (D - 2) Γ ι f, ∀ t : ℕ, 0 < t → t ≠ r → t ≤ N →
      CategoryTheory.Limits.IsZero (Work.Serre.ratH (TopCat.of (Work.StemsB.fibre q γ)) t))
    (hpc : ∀ γ : Work.RatHurewicz.attachCells (D - 2) Γ ι f,
      PathConnectedSpace (Work.StemsB.fibre q γ))
    (IH : Work.Serre.ThomCylAt r N (Work.Serre.restrictFibre q (Work.Serre.ladS D Γ ι f)))
    (U : Work.Thom.RelCoh ℚ (r + 1) (Work.Serre.cyl q) (Set.range (Work.Serre.cylIncl q)))
    (hG : ∀ k, CategoryTheory.CategoryStruct.comp (Work.Serre.baseG D Γ ι f k)
        (Work.Serre.TQ r q (Work.Serre.ladS D Γ ι f)
          Work.RatHurewicz.isClosed_range_attachIncl IH.choose k)
      = CategoryTheory.CategoryStruct.comp (Work.Serre.TP r q U k)
          (Work.Serre.totG D ι f q (k + (r + 1))))
    {m : ℕ} (hm₁ : m + 1 ≠ D) (hm₂ : m ≠ D) (hmN : m + r + 1 ≤ N + 1) :
    CategoryTheory.IsIso (Work.Serre.TP r q U m) := by
  have hmD : m ≠ D := hm₂
  have h1 : CategoryTheory.Limits.IsZero (Work.Thom.RelCoh ℚ m
      (Work.RatHurewicz.attachCells (D - 2) Γ ι f) (Work.Serre.ladS D Γ ι f)) := by
    rcases lt_or_gt_of_ne hmD with h | h
    · exact Work.Serre.attachRelCohVanishing D hD hΓ ι f m (by omega)
    · exact Work.Serre.attachRelCohVanishingHigh D hD ι f m h
  have h1' : CategoryTheory.Limits.IsZero (Work.Thom.RelCoh ℚ (m + 1)
      (Work.RatHurewicz.attachCells (D - 2) Γ ι f) (Work.Serre.ladS D Γ ι f)) := by
    rcases lt_or_gt_of_ne hm₁ with h | h
    · exact Work.Serre.attachRelCohVanishing D hD hΓ ι f (m + 1) (by omega)
    · exact Work.Serre.attachRelCohVanishingHigh D hD ι f (m + 1) h
  have h2 : CategoryTheory.Limits.IsZero (Work.Thom.RelCoh ℚ (m + (r + 1)) (Work.Serre.cyl q)
      (Work.Serre.ladNew D ι f q)) :=
    Work.Serre.discPairCellVanishingSucc r N D hr hD hΓ ι f q hq hvan hpc (m + (r + 1))
      (by omega) (by omega)
  have h2' : CategoryTheory.Limits.IsZero (Work.Thom.RelCoh ℚ (m + (r + 1) + 1) (Work.Serre.cyl q)
      (Work.Serre.ladNew D ι f q)) :=
    Work.Serre.discPairCellVanishingSucc r N D hr hD hΓ ι f q hq hvan hpc (m + (r + 1) + 1)
      (by omega) (by omega)
  have hker₁ : LinearMap.ker (ModuleCat.Hom.hom (Work.Serre.baseG D Γ ι f m)) = ⊥ := by
    rw [← Work.Serre.baseExact₂ D Γ ι f m,
      CategoryTheory.Limits.IsZero.eq_zero_of_src h1 (Work.Serre.baseF D Γ ι f m), ModuleCat.hom_zero,
      LinearMap.range_zero]
  have hsurj₁ : LinearMap.range (ModuleCat.Hom.hom (Work.Serre.baseG D Γ ι f m)) = ⊤ := by
    rw [Work.Serre.baseExact₃ D Γ ι f m,
      CategoryTheory.Limits.IsZero.eq_zero_of_tgt h1' (Work.Serre.baseD D Γ ι f m), ModuleCat.hom_zero,
      LinearMap.ker_zero]
  have hker₂ : LinearMap.ker (ModuleCat.Hom.hom (Work.Serre.totG D ι f q (m + (r + 1)))) = ⊥ := by
    rw [← Work.Serre.totExact₂ D ι f q (m + (r + 1)),
      CategoryTheory.Limits.IsZero.eq_zero_of_src h2 (Work.Serre.totF D ι f q (m + (r + 1))), ModuleCat.hom_zero,
      LinearMap.range_zero]
  have hsurj₂ : LinearMap.range (ModuleCat.Hom.hom (Work.Serre.totG D ι f q (m + (r + 1)))) = ⊤ := by
    rw [Work.Serre.totExact₃ D ι f q (m + (r + 1)),
      CategoryTheory.Limits.IsZero.eq_zero_of_tgt h2' (Work.Serre.totD D ι f q (m + (r + 1))), ModuleCat.hom_zero,
      LinearMap.ker_zero]
  have hTQ : Function.Bijective (ModuleCat.Hom.hom (Work.Serre.TQ r q
      (Work.Serre.ladS D Γ ι f) Work.RatHurewicz.isClosed_range_attachIncl IH.choose m)) :=
    (CategoryTheory.ConcreteCategory.isIso_iff_bijective _).mp
      (Work.Serre.isIso_TQ r N q (Work.Serre.ladS D Γ ι f)
        Work.RatHurewicz.isClosed_range_attachIncl IH m (by omega))
  have hGe : ∀ p : ↥(Work.Thom.Coh ℚ m (Work.RatHurewicz.attachCells (D - 2) Γ ι f)),
      ModuleCat.Hom.hom (Work.Serre.TQ r q (Work.Serre.ladS D Γ ι f)
          Work.RatHurewicz.isClosed_range_attachIncl IH.choose m)
        (ModuleCat.Hom.hom (Work.Serre.baseG D Γ ι f m) p)
      = ModuleCat.Hom.hom (Work.Serre.totG D ι f q (m + (r + 1)))
          (ModuleCat.Hom.hom (Work.Serre.TP r q U m) p) := by
    intro p
    have h := congrArg ModuleCat.Hom.hom (hG m)
    rw [ModuleCat.hom_comp] at h
    rw [ModuleCat.hom_comp] at h
    exact DFunLike.congr_fun h p
  have hbij := ladderBijective (ModuleCat.Hom.hom (Work.Serre.baseG D Γ ι f m))
    (ModuleCat.Hom.hom (Work.Serre.totG D ι f q (m + (r + 1))))
    (ModuleCat.Hom.hom (Work.Serre.TP r q U m))
    (ModuleCat.Hom.hom (Work.Serre.TQ r q (Work.Serre.ladS D Γ ι f)
      Work.RatHurewicz.isClosed_range_attachIncl IH.choose m)) hGe
    ⟨LinearMap.ker_eq_bot.mp hker₁, LinearMap.range_eq_top.mp hsurj₁⟩
    ⟨LinearMap.ker_eq_bot.mp hker₂, LinearMap.range_eq_top.mp hsurj₂⟩ hTQ
  exact (CategoryTheory.ConcreteCategory.isIso_iff_bijective (Work.Serre.TP r q U m)).mpr hbij

/-- **The naturality square in the form needed below**: the `hG`-square of the ladder, obtained from
the delegated `Work.Stems.ladderNaturality` and the extension property of `U`. -/
theorem ladderNaturalityG (r N D : ℕ) (hr : 1 ≤ r) (hD : 2 ≤ D)
    {Γ : Type} [TopologicalSpace Γ] (hΓ : PathConnectedSpace Γ) (ι : Type)
    (f : ι → C(Work.RatHurewicz.cellSphere (D - 2), Γ))
    {X : Type} [TopologicalSpace X] (q : C(X, Work.RatHurewicz.attachCells (D - 2) Γ ι f))
    (hq : Work.StemsB.IsSerreFibration q)
    (hvan : ∀ γ : Work.RatHurewicz.attachCells (D - 2) Γ ι f, ∀ t : ℕ, 0 < t → t ≠ r → t ≤ N →
      CategoryTheory.Limits.IsZero (Work.Serre.ratH (TopCat.of (Work.StemsB.fibre q γ)) t))
    (hpc : ∀ γ : Work.RatHurewicz.attachCells (D - 2) Γ ι f,
      PathConnectedSpace (Work.StemsB.fibre q γ))
    (IH : Work.Serre.ThomCylAt r N (Work.Serre.restrictFibre q (Work.Serre.ladS D Γ ι f)))
    (U : Work.Thom.RelCoh ℚ (r + 1) (Work.Serre.cyl q) (Set.range (Work.Serre.cylIncl q)))
    (hU : (HomologicalComplex.homologyMap (Work.Serre.tripleRestr ℚ (TopCat.of (Work.Serre.cyl q))
        (Set.range (Work.Serre.cylIncl q))
        ((Work.Serre.cylRetract q) ⁻¹' (Work.Serre.ladS D Γ ι f) ∪
          Set.range (Work.Serre.cylIncl q)) (fun _ hx => Or.inr hx)) (r + 1)).hom U
      = Work.Serre.uNew r q (Work.Serre.ladS D Γ ι f)
          Work.RatHurewicz.isClosed_range_attachIncl IH.choose) :
    ∀ k, CategoryTheory.CategoryStruct.comp (Work.Serre.baseG D Γ ι f k)
        (Work.Serre.TQ r q (Work.Serre.ladS D Γ ι f)
          Work.RatHurewicz.isClosed_range_attachIncl IH.choose k)
      = CategoryTheory.CategoryStruct.comp (Work.Serre.TP r q U k)
          (Work.Serre.totG D ι f q (k + (r + 1))) :=
  fun k => Work.Stems.ladderNaturality r D hD ι f q IH.choose U hU k

/-- **The cellular step, reduced to two isomorphisms.**  Given the extension class `U` of the old
Thom class `IH.choose` (existence: `Work.Serre.exists_extensionClass`), the conclusion holds as soon
as the cup map with `U` is an isomorphism in the two *cell* degrees `D - 1` and `D` — the only
degrees in which the comparison maps `baseG`/`totG` of the ladder fail to be bijections.  In every
other degree the cup map is automatically an isomorphism (`Work.Stems.tp_isIso_of_ne`), and the
naturality square is discharged by `Work.Stems.ladderNaturality`. -/
theorem thomCylCellStepRace_of_cellIsos (r N D : ℕ) (hr : 1 ≤ r) (hD : 2 ≤ D)
    {Γ : Type} [TopologicalSpace Γ] (hΓ : PathConnectedSpace Γ) (ι : Type)
    (f : ι → C(Work.RatHurewicz.cellSphere (D - 2), Γ))
    {X : Type} [TopologicalSpace X] (q : C(X, Work.RatHurewicz.attachCells (D - 2) Γ ι f))
    (hq : Work.StemsB.IsSerreFibration q)
    (hvan : ∀ γ : Work.RatHurewicz.attachCells (D - 2) Γ ι f, ∀ t : ℕ, 0 < t → t ≠ r → t ≤ N →
      CategoryTheory.Limits.IsZero (Work.Serre.ratH (TopCat.of (Work.StemsB.fibre q γ)) t))
    (hpc : ∀ γ : Work.RatHurewicz.attachCells (D - 2) Γ ι f,
      PathConnectedSpace (Work.StemsB.fibre q γ))
    (IH : Work.Serre.ThomCylAt r N (Work.Serre.restrictFibre q (Work.Serre.ladS D Γ ι f)))
    (U : Work.Thom.RelCoh ℚ (r + 1) (Work.Serre.cyl q) (Set.range (Work.Serre.cylIncl q)))
    (hU : (HomologicalComplex.homologyMap (Work.Serre.tripleRestr ℚ (TopCat.of (Work.Serre.cyl q))
        (Set.range (Work.Serre.cylIncl q))
        ((Work.Serre.cylRetract q) ⁻¹' (Work.Serre.ladS D Γ ι f) ∪
          Set.range (Work.Serre.cylIncl q)) (fun _ hx => Or.inr hx)) (r + 1)).hom U
      = Work.Serre.uNew r q (Work.Serre.ladS D Γ ι f)
          Work.RatHurewicz.isClosed_range_attachIncl IH.choose)
    (hcell : ∀ m : ℕ, (m = D - 1 ∨ m = D) → m + r + 1 ≤ N + 1 →
      CategoryTheory.IsIso (Work.Serre.TP r q U m)) :
    Work.Serre.ThomCylAt r N q := by
  refine ⟨U, fun m hm => ?_⟩
  by_cases h : m = D - 1 ∨ m = D
  · exact hcell m h hm
  · push_neg at h
    exact tp_isIso_of_ne r N D hr hD hΓ ι f q hq hvan hpc IH U
      (ladderNaturalityG r N D hr hD hΓ ι f q hq hvan hpc IH U hU)
      (by omega) h.2 hm

/-- **The cellular step in the high-dimensional regime `N + 1 < D + r`** (equivalently
`N ≤ D + r - 2`).  Here the two cell degrees `D - 1`, `D` are out of range, so
`Work.Stems.tp_isIso_of_ne` applies in every degree in range and the conclusion follows — with the
extension class of `Work.Serre.exists_extensionClass` — from the naturality square alone. -/
theorem thomCylCellStepRace_of_highDim (r N D : ℕ) (hr : 1 ≤ r) (hD : 2 ≤ D)
    (hhigh : N + 1 < D + r)
    {Γ : Type} [TopologicalSpace Γ] (hΓ : PathConnectedSpace Γ) (ι : Type)
    (f : ι → C(Work.RatHurewicz.cellSphere (D - 2), Γ))
    {X : Type} [TopologicalSpace X] (q : C(X, Work.RatHurewicz.attachCells (D - 2) Γ ι f))
    (hq : Work.StemsB.IsSerreFibration q)
    (hvan : ∀ γ : Work.RatHurewicz.attachCells (D - 2) Γ ι f, ∀ t : ℕ, 0 < t → t ≠ r → t ≤ N →
      CategoryTheory.Limits.IsZero (Work.Serre.ratH (TopCat.of (Work.StemsB.fibre q γ)) t))
    (hgen : ∀ γ : Work.RatHurewicz.attachCells (D - 2) Γ ι f,
      Nonempty (CategoryTheory.Iso (Work.Serre.ratH (TopCat.of (Work.StemsB.fibre q γ)) r)
        (ModuleCat.of ℚ ℚ)))
    (hpc : ∀ γ : Work.RatHurewicz.attachCells (D - 2) Γ ι f,
      PathConnectedSpace (Work.StemsB.fibre q γ))
    (IH : Work.Serre.ThomCylAt r N (Work.Serre.restrictFibre q (Work.Serre.ladS D Γ ι f))) :
    Work.Serre.ThomCylAt r N q := by
  rcases lt_or_ge N r with hNr | hNr
  · -- there is no degree in the range: any class witnesses the conclusion
    refine ⟨0, fun m hm => absurd hm (by omega)⟩
  · obtain ⟨U, hU⟩ := Work.Serre.exists_extensionClass r N D hr hNr hD hΓ ι f q hq
      hvan hpc IH.choose
    refine ⟨U, fun m hm => ?_⟩
    have hm1 : m + 1 ≠ D := by omega
    have hm2 : m ≠ D := by omega
    exact tp_isIso_of_ne r N D hr hD hΓ ι f q hq hvan hpc IH U
      (ladderNaturalityG r N D hr hD hΓ ι f q hq hvan hpc IH U hU) hm1 hm2 hm

theorem thomCylCellStepRace (r N : ℕ) (hr : 1 ≤ r) (D : ℕ) (hD : 2 ≤ D)
    {Γ : Type} [TopologicalSpace Γ] (hΓ : PathConnectedSpace Γ) (ι : Type)
    (f : ι → C(Work.RatHurewicz.cellSphere (D - 2), Γ))
    {X : Type} [TopologicalSpace X] (q : C(X, Work.RatHurewicz.attachCells (D - 2) Γ ι f))
    (hq : Work.StemsB.IsSerreFibration q)
    (hvan : ∀ γ : Work.RatHurewicz.attachCells (D - 2) Γ ι f, ∀ t : ℕ, 0 < t → t ≠ r → t ≤ N →
      CategoryTheory.Limits.IsZero (Work.Serre.ratH (TopCat.of (Work.StemsB.fibre q γ)) t))
    (hgen : ∀ γ : Work.RatHurewicz.attachCells (D - 2) Γ ι f,
      Nonempty (CategoryTheory.Iso (Work.Serre.ratH (TopCat.of (Work.StemsB.fibre q γ)) r)
        (ModuleCat.of ℚ ℚ)))
    (hpc : ∀ γ : Work.RatHurewicz.attachCells (D - 2) Γ ι f,
      PathConnectedSpace (Work.StemsB.fibre q γ))
    (IH : Work.Serre.ThomCylAt r N (Work.Serre.restrictFibre q
      (Set.range (Work.RatHurewicz.attachIncl (D - 2) Γ ι f)))) :
    Work.Serre.ThomCylAt r N q :=
  Work.Serre.thomCylCellStepAlt r N hr D hD hΓ ι f q hq hvan hgen hpc IH

end Work.Stems

/-!
## FINAL STATE (2026-09-27, evening)

**The target `Work.Stems.thomCylCellStepRace` is PROVED**, axiom-clean
(`#print axioms Work.Stems.thomCylCellStepRace` = `[propext, Classical.choice, Quot.sound]`).

The closing line uses the *independent second proof of the cellular step* that the fleet produced,
now available under the canonical name

  `Work.Serre.thomCylCellStepAlt`   (`Submission/Work/Serre/thomCylCellStepAlt.lean`),

whose proof is `Work.RatHurewicz.thomCylCellStepAlt_free`
(`Submission/Work/RatHurewicz/cellStepShell.lean`), a theorem with exactly the target's statement
(same binders, same conclusion).  Its route is the *shell*
route and does not use any of the reductions in this file: the cellular step
`Work.RatHurewicz.CellStepAt D` for **every** `D ≥ 2` is assembled from

* `Work.Serre.thomCylCellStep_of_shellsBall` (the two-set cover `Γ' = cellU f ρ ∪ cellV f R`, its
  two Mayer–Vietoris inputs over `cellU` and over the balls discharged by the proved
  `Work.RatHurewicz.thomCylAt_of_compress` and `Work.Serre.bijective_cup_openBall`), and
* the *shell* family `Work.Serre.bijective_cup_shell_of_thomCylAt` fed by
  `Work.RatHurewicz.cellShellThom_of_nonzeroClass`, which pushes the Thom condition from the
  `1/4`-sphere of the cell to the shell (`thomCylAt_of_compress`, the shell being a thickening of
  that sphere) after applying the sphere case
  `Work.RatHurewicz.sphereThom_of_nonzeroClass` — the *conditional* form of `SphThom`, whose
  non-zero class is supplied by `Work.RatHurewicz.cellwiseNonvanishing` from the extension class
  `Work.Serre.cellStepU` (`Work.Serre.cellStepU_ne_zero`).  That conditional form is what avoids
  the false `SphThom 0` (a non-orientable `S^1`-fibration) and hence the apparent base-case gap at
  `D = 2`.

The material *in this file* remains as an independent reduction of the same statement and is used
nowhere by the closing line:

* `Work.Stems.tp_isIso_of_ne` — the cup map with the extension class is an isomorphism in every
  degree `m ∉ {D-1, D}` with `m + r + 1 ≤ N + 1`, from the ladder's naturality square, the two
  exactness rows and the vanishing theorems (no cell comparison, no `TM`, no five-lemma ladder);
* `Work.Stems.thomCylCellStepRace_of_cellIsos` — the target follows from the two cell isos
  `IsIso (TP (D-1))`, `IsIso (TP D)`;
* `Work.Stems.thomCylCellStepRace_of_highDim` — **the target holds unconditionally whenever
  `N + 1 < D + r`** (equivalently `N ≤ D + r - 2`), with no cell input at all;
* `Work.Stems.ladderNaturalityG` — the naturality square `hG` (from the colleague-proved
  `Work.Stems.ladderNaturality`);
* `Work.Stems.cylFibreRes_ne_zero_of_pos` — the fibrewise non-vanishing (SIH) of the extension
  class, from the proved `Work.Stems.fibreRestrictionInjectiveOfPos`
  (`Submission/Work/Stems/fibreRestrictionInjectiveOfPos.lean`).

**Do not re-explore.**  The `hC`/`hinvis` "refutations", the "easy regime" via
`thomCylAt_of_relVanishing` at `V = univ`, the collapse-map trivialisation, and the missing
naturality of `attachRelCohCellEquiv` are all recorded in `thomCylCellStepRace_NOTES.md` and in the
docstrings above; none of them is needed any more.
-/
