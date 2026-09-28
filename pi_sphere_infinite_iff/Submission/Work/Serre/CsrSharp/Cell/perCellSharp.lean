import Mathlib
import Submission.Work.Serre.CsrSharp.Defs
import Submission.Work.Serre.CsrSharp.Tools
import Submission.Work.Serre.CsrSharp.Cell.targetGroups
import Submission.Work.Serre.CsrSharp.Cell.sourceIso
import Submission.Work.Serre.CsrSharp.Cell.sourceIsZero
import Submission.Work.Serre.Csr.Section
import Submission.Work.Serre.csrDefs
import Submission.Work.Serre.csrGeom
import Submission.Work.Serre.csrGlue
import Submission.Work.Serre.csrPairFunctoriality
import Submission.Work.Serre.Csr.Base

/-!
# The sharp rational per-cell computation

`Work.Serre.CsrSharp.perCellSharp` deduces the sharp rational per-cell computation
`Work.Serre.CsrSharp.PerCellIso` from the cube computation `Work.Serre.CsrSharp.CubeIsoRat`.

The argument is short because the two sides of the per-cell pair map
`(q⁻¹o, q⁻¹(o∖{c})) → (o, o∖{c})` are already computed, over `ℤ`, by the library:

* the target side `(o, o∖{c})` is the pair of the `(n+2)`-disc with its boundary sphere
  (`Work.Serre.Csr.csrTargetPair`, base changed to `ℚ` in
  `Submission/Work/Serre/CsrSharp/Cell/targetGroups.lean`): its relative homology is `ℚ` in degree
  `n+2` and vanishes elsewhere;
* the source side is the fibre homology shifted by `n+2`
  (`Work.Serre.Csr.csrSourceDiscIso` composed with `Work.Serre.csrDiscChain` and
  `Work.Serre.Csr.csrTransferPair`): `H_{k+(n+2)}(q⁻¹o, q⁻¹(o∖{c});ℚ) ≅ H_k(F;ℚ)`, and it vanishes
  below the cell dimension.

Since the source vanishes below `n+2` and the target only lives in degree `n+2`, the pair map is an
isomorphism in every degree different from `n+2`; in degree `n+2` both sides are one dimensional
over `ℚ` and the map is surjective because the fibration admits a section over the contractible open
half-ball `o` (lift the contraction of the cell along the fibration,
`Work.Serre.exists_section_cubePullback`), so the map is an isomorphism there as well.  The
surjectivity in the top degree `(n+2)+φ` is the same surjectivity, available in every degree.  The
fibre hypotheses `hfib`/`h0` are only used through the vanishing of `H_{m-(n+2)}(F;ℚ)` for
`0 < m-(n+2) < φ` and the non-vanishing of `H_0(F;ℚ)`. -/

set_option linter.style.haveILetI false

open scoped Topology unitInterval
open CategoryTheory CategoryTheory.Limits

namespace Work.Serre.CsrSharp.Cell

noncomputable section

/-! ## The two pairs of the per-cell map -/

/-- The relative part of the target pair of the per-cell map: `o ∖ {c}` inside `o`. -/
abbrev tgtRel (n : ℕ) (Y : Type) [TopologicalSpace Y] (ι : Type)
    (f : ι → C(Work.RatHurewicz.cellSphere n, Y)) (i : ι) :
    Set ↥(Work.Serre.csrOpenBall n Y ι f i) :=
  {x | (x : Work.RatHurewicz.attachCells n Y ι f) ∈
    Work.Serre.csrOpenBall n Y ι f i \ {Work.Serre.csrCentre n Y ι f i}}

/-- The relative part of the source pair of the per-cell map: `q⁻¹'(o ∖ {c})` inside `q⁻¹'o`. -/
abbrev srcRel (n : ℕ) (Y : Type) [TopologicalSpace Y] (ι : Type)
    (f : ι → C(Work.RatHurewicz.cellSphere n, Y)) {E : Type} [TopologicalSpace E]
    (q : C(E, Work.RatHurewicz.attachCells n Y ι f)) (i : ι) :
    Set ↥(q ⁻¹' Work.Serre.csrOpenBall n Y ι f i) :=
  {x | (x : E) ∈ q ⁻¹' (Work.Serre.csrOpenBall n Y ι f i \ {Work.Serre.csrCentre n Y ι f i})}

/-- The target pair of the per-cell map, as a relative chain complex over `ℚ`. -/
abbrev tgt (n : ℕ) (Y : Type) [TopologicalSpace Y] (ι : Type)
    (f : ι → C(Work.RatHurewicz.cellSphere n, Y)) (i : ι) : ChainComplex (ModuleCat ℚ) ℕ :=
  Work.StemsB.relChainsR ℚ (TopCat.of ↥(Work.Serre.csrOpenBall n Y ι f i)) (tgtRel n Y ι f i)

/-- The source pair of the per-cell map, as a relative chain complex over `ℚ`. -/
abbrev src (n : ℕ) (Y : Type) [TopologicalSpace Y] (ι : Type)
    (f : ι → C(Work.RatHurewicz.cellSphere n, Y)) {E : Type} [TopologicalSpace E]
    (q : C(E, Work.RatHurewicz.attachCells n Y ι f)) (i : ι) : ChainComplex (ModuleCat ℚ) ℕ :=
  Work.StemsB.relChainsR ℚ (TopCat.of ↥(q ⁻¹' Work.Serre.csrOpenBall n Y ι f i))
    (srcRel n Y ι f q i)

/-- The per-cell map is the pair map of the relative chain complexes `src → tgt`. -/
theorem perCellMap_eq (n : ℕ) (Y : Type) [TopologicalSpace Y] (ι : Type)
    (f : ι → C(Work.RatHurewicz.cellSphere n, Y)) {E : Type} [TopologicalSpace E]
    (q : C(E, Work.RatHurewicz.attachCells n Y ι f)) (i : ι) :
    Work.Serre.CsrSharp.perCellMap n Y ι f q i
      = Work.Serre.relChainsRPairMap (srcRel n Y ι f q i) (tgtRel n Y ι f i)
          (Work.Serre.csrRestrict q (Work.Serre.csrOpenBall n Y ι f i)) (fun _ hx => hx) := rfl

/-! ## Surjectivity from a section of the fibration over the open half-ball -/

/-- **The per-cell map is surjective on homology in every degree** as soon as the restriction of the
fibration to the open half-ball `o` admits a section: the section is a map of pairs
`(o, o∖{c}) → (q⁻¹'o, q⁻¹'(o∖{c}))` whose composite with the per-cell map is the identity, so the
composite of the induced maps on relative chains is the identity. -/
theorem perCellMap_surjective (n : ℕ) (Y : Type) [TopologicalSpace Y] (ι : Type)
    (f : ι → C(Work.RatHurewicz.cellSphere n, Y)) {E : Type} [TopologicalSpace E]
    (q : C(E, Work.RatHurewicz.attachCells n Y ι f)) (i : ι)
    (s : C(↥(Work.Serre.csrOpenBall n Y ι f i), ↥(q ⁻¹' Work.Serre.csrOpenBall n Y ι f i)))
    (hs : (Work.Serre.csrRestrict q (Work.Serre.csrOpenBall n Y ι f i)).comp s
      = ContinuousMap.id ↥(Work.Serre.csrOpenBall n Y ι f i)) (m : ℕ) :
    Function.Surjective
      (HomologicalComplex.homologyMap (Work.Serre.CsrSharp.perCellMap n Y ι f q i) m).hom := by
  have hmap : ∀ x : ↥(Work.Serre.csrOpenBall n Y ι f i),
      (Work.Serre.csrRestrict q (Work.Serre.csrOpenBall n Y ι f i)) (s x) = x :=
    fun x => congrFun (congrArg DFunLike.coe hs) x
  have hval : ∀ x : ↥(Work.Serre.csrOpenBall n Y ι f i),
      q ((s x : ↥(q ⁻¹' Work.Serre.csrOpenBall n Y ι f i)) : E)
        = (x : Work.RatHurewicz.attachCells n Y ι f) :=
    fun x => congrArg Subtype.val (hmap x)
  have hs' : Set.MapsTo s (tgtRel n Y ι f i) (srcRel n Y ι f q i) := by
    intro x hx
    show q ((s x : ↥(q ⁻¹' Work.Serre.csrOpenBall n Y ι f i)) : E) ∈
      Work.Serre.csrOpenBall n Y ι f i \ {Work.Serre.csrCentre n Y ι f i}
    rw [hval x]
    exact hx
  have hAA : Set.MapsTo ((Work.Serre.csrRestrict q (Work.Serre.csrOpenBall n Y ι f i)).comp s)
      (tgtRel n Y ι f i) (tgtRel n Y ι f i) := fun x hx => by
    show (Work.Serre.csrRestrict q (Work.Serre.csrOpenBall n Y ι f i)) (s x) ∈ tgtRel n Y ι f i
    rw [hmap x]
    exact hx
  have hcomp : Work.Serre.relChainsRPairMap (tgtRel n Y ι f i) (srcRel n Y ι f q i) s hs' ≫
      Work.Serre.CsrSharp.perCellMap n Y ι f q i = 𝟙 _ := by
    rw [perCellMap_eq n Y ι f q i]
    rw [Work.Serre.csrPairFunctoriality s
      (Work.Serre.csrRestrict q (Work.Serre.csrOpenBall n Y ι f i)) hs' (fun _ hx => hx)]
    refine (Work.Serre.CsrSharp.Tools.relChainsRPairMap_congr hs hAA (fun x hx => hx)).trans ?_
    exact Work.Serre.CsrSharp.Tools.relChainsRPairMap_id' _ _
  have h1 : HomologicalComplex.homologyMap
        (Work.Serre.relChainsRPairMap (tgtRel n Y ι f i) (srcRel n Y ι f q i) s hs') m
      ≫ HomologicalComplex.homologyMap (Work.Serre.CsrSharp.perCellMap n Y ι f q i) m = 𝟙 _ := by
    rw [← HomologicalComplex.homologyMap_comp, hcomp, HomologicalComplex.homologyMap_id]
  intro y
  refine ⟨(HomologicalComplex.homologyMap
      (Work.Serre.relChainsRPairMap (tgtRel n Y ι f i) (srcRel n Y ι f q i) s hs') m).hom y, ?_⟩
  have h2 := congrArg ModuleCat.Hom.hom h1
  rw [ModuleCat.hom_comp, ModuleCat.hom_id] at h2
  exact LinearMap.congr_fun h2 y

/-! ## The reduction to the two group computations -/

/-- **The sharp rational per-cell computation, from the two group computations.** -/
theorem perCellSharp_of_groups
    (hT : ∀ (n : ℕ) (Y : Type) [TopologicalSpace Y] (ι : Type)
      (f : ι → C(Work.RatHurewicz.cellSphere n, Y)) (i : ι),
      (∀ m : ℕ, m ≠ n+2 → CategoryTheory.Limits.IsZero ((tgt n Y ι f i).homology m)) ∧
      Nonempty ((tgt n Y ι f i).homology (n+2) ≅ ModuleCat.of ℚ ℚ))
    (hS : ∀ (n : ℕ) (Y : Type) [TopologicalSpace Y] (ι : Type)
      (f : ι → C(Work.RatHurewicz.cellSphere n, Y)) {E : Type} [TopologicalSpace E]
      (q : C(E, Work.RatHurewicz.attachCells n Y ι f)), Work.StemsB.IsSerreFibration q → (i : ι) →
      (∀ k : ℕ, Nonempty ((src n Y ι f q i).homology (k + (n+2)) ≅
        (Work.Cohomology.singularChains ℚ
          (TopCat.of (Work.StemsB.fibre q (Work.Serre.csrCentre n Y ι f i)))).homology k)) ∧
      (∀ m : ℕ, m < n+2 → CategoryTheory.Limits.IsZero ((src n Y ι f q i).homology m)))
    (hsec : ∀ (n : ℕ) (Y : Type) [TopologicalSpace Y] (ι : Type)
      (f : ι → C(Work.RatHurewicz.cellSphere n, Y)) {E : Type} [TopologicalSpace E]
      (q : C(E, Work.RatHurewicz.attachCells n Y ι f)), Work.StemsB.IsSerreFibration q → (i : ι) →
      Nonempty (Work.StemsB.fibre q (Work.Serre.csrCentre n Y ι f i)) →
      ∃ s : C(↥(Work.Serre.csrOpenBall n Y ι f i),
          ↥(q ⁻¹' Work.Serre.csrOpenBall n Y ι f i)),
        (Work.Serre.csrRestrict q (Work.Serre.csrOpenBall n Y ι f i)).comp s
          = ContinuousMap.id ↥(Work.Serre.csrOpenBall n Y ι f i)) :
    Work.Serre.CsrSharp.PerCellIso := by
  intro n Y _ ι f E _ q hq φ hfib h0 i
  obtain ⟨hTz, hTtop⟩ := hT n Y ι f i
  obtain ⟨hSiso, hSzero⟩ := hS n Y ι f q hq i
  -- the surjectivity of the per-cell map in every degree, from a section over `o`
  have hne := Work.Serre.Csr.nonempty_of_nonempty_homologyZeroIso _
    (h0 (Work.Serre.csrCentre n Y ι f i))
  obtain ⟨s, hs⟩ := hsec n Y ι f q hq i hne
  have hsurj := perCellMap_surjective n Y ι f q i s hs
  refine ⟨fun m hm => ?_, fun y => hsurj (n+2+φ) y⟩
  rcases lt_trichotomy m (n+2) with hlt | heq | hgt
  · -- below the cell dimension both sides vanish
    haveI hzS : IsZero ((src n Y ι f q i).homology m) := hSzero m hlt
    haveI hzT : IsZero ((tgt n Y ι f i).homology m) := hTz m (by omega)
    haveI : Subsingleton ((src n Y ι f q i).homology m) := ModuleCat.subsingleton_of_isZero hzS
    haveI : Subsingleton ((tgt n Y ι f i).homology m) := ModuleCat.subsingleton_of_isZero hzT
    haveI : Mono (HomologicalComplex.homologyMap (Work.Serre.CsrSharp.perCellMap n Y ι f q i) m) :=
      (ModuleCat.mono_iff_injective _).mpr (fun a b _ => Subsingleton.elim a b)
    haveI : Epi (HomologicalComplex.homologyMap (Work.Serre.CsrSharp.perCellMap n Y ι f q i) m) :=
      (ModuleCat.epi_iff_surjective _).mpr (fun b =>
        ⟨0, Subsingleton.elim _ b⟩)
    exact isIso_of_mono_of_epi _
  · -- in the cell dimension both sides are one dimensional over `ℚ` and the map is surjective
    subst heq
    obtain ⟨eS⟩ := hSiso 0
    rw [Nat.zero_add] at eS
    obtain ⟨eF⟩ := h0 (Work.Serre.csrCentre n Y ι f i)
    obtain ⟨eT⟩ := hTtop
    exact Work.Serre.Csr.isIso_of_epi_of_ratIso (eS ≪≫ eF) eT
      (HomologicalComplex.homologyMap (Work.Serre.CsrSharp.perCellMap n Y ι f q i) (n+2))
      ((ModuleCat.epi_iff_surjective _).mpr (hsurj (n+2)))
  · -- above the cell dimension (and below `(n+2)+φ`) the fibre homology vanishes
    haveI hzT : IsZero ((tgt n Y ι f i).homology m) := hTz m (by omega)
    have hk : m - (n+2) + (n+2) = m := Nat.sub_add_cancel (by omega)
    obtain ⟨eS⟩ := hSiso (m - (n+2))
    haveI hzF : IsZero ((Work.Cohomology.singularChains ℚ
        (TopCat.of (Work.StemsB.fibre q (Work.Serre.csrCentre n Y ι f i)))).homology
          (m - (n+2))) := hfib (Work.Serre.csrCentre n Y ι f i) (m - (n+2)) (by omega)
            (by omega)
    haveI hzS' : IsZero ((src n Y ι f q i).homology (m - (n+2) + (n+2))) := hzF.of_iso eS
    haveI hzS : IsZero ((src n Y ι f q i).homology m) := by rwa [hk] at hzS'
    haveI : Subsingleton ((src n Y ι f q i).homology m) := ModuleCat.subsingleton_of_isZero hzS
    haveI : Subsingleton ((tgt n Y ι f i).homology m) := ModuleCat.subsingleton_of_isZero hzT
    haveI : Mono (HomologicalComplex.homologyMap (Work.Serre.CsrSharp.perCellMap n Y ι f q i) m) :=
      (ModuleCat.mono_iff_injective _).mpr (fun a b _ => Subsingleton.elim a b)
    haveI : Epi (HomologicalComplex.homologyMap (Work.Serre.CsrSharp.perCellMap n Y ι f q i) m) :=
      (ModuleCat.epi_iff_surjective _).mpr (fun b => ⟨0, Subsingleton.elim _ b⟩)
    exact isIso_of_mono_of_epi _

/-! ## The per-cell computation -/

theorem perCellSharp (hcube : Work.Serre.CsrSharp.CubeIsoRat) : Work.Serre.CsrSharp.PerCellIso := by
  refine perCellSharp_of_groups (fun n Y _ ι f i => targetGroups n Y ι f i) ?_ ?_
  · intro n Y _ ι f E _ q hq i
    exact ⟨fun k => sourceIso n Y ι f q hq i k, fun m hm => sourceIsZero n Y ι f q hq i m hm⟩
  · intro n Y _ ι f E _ q hq i hne
    exact Work.Serre.Csr.csrOpenBallSection' n Y ι f q hq i hne

end

end Work.Serre.CsrSharp.Cell
