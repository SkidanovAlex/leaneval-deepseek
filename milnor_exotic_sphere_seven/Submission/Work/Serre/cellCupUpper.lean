import Mathlib
import Submission.Work.Serre.CellCupDefs
import Submission.Work.Serre.DiscPair.oldPartRelCohIso
import Submission.Work.Serre.DiscPair.isIso_relCohMap_incl_of_isZero
import Submission.Work.StemsB.AToolsR
import Submission.Work.Whitney.RelRelCupNat
import Submission.Work.Serre.cohMapIsoOfRatHomologyIso
import Submission.Work.Serre.relCohomologyUnivVanishing
import Submission.Work.Serre.relRelCupOpen_mixedCup
import Submission.Work.Cohomology.Endgame.tripleLES
import Submission.Work.Serre.isZero_relCoh_of_cohMapIso

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false

namespace Work.Serre

open CategoryTheory CategoryTheory.Limits

noncomputable section

variable {D : ℕ} {Γ : Type} [TopologicalSpace Γ] {ι : Type}
  {f : ι → C(Work.RatHurewicz.cellSphere (D - 2), Γ)} {X : Type} [TopologicalSpace X]
  {q : C(X, Work.RatHurewicz.attachCells (D - 2) Γ ι f)}

/-- The class `α = (cylRetract q)^*(F₁ z)` pulled back to `A₂`. -/
abbrev cellCupAlpha (q : C(X, Work.RatHurewicz.attachCells (D - 2) Γ ι f))
    (z : Work.Thom.RelCoh ℚ D (Work.RatHurewicz.attachCells (D - 2) Γ ι f)
      (Work.Serre.cellCupS D Γ ι f)) : Work.Thom.Coh ℚ D ↥(DiscPair.cylPairA₂ (f := f) q) :=
  (Work.Thom.CohMap (Work.Thom.subtypeMap (DiscPair.cylPairA₂ (f := f) q)) ℚ D).hom
    ((Work.Thom.CohMap (Work.Serre.cylRetract q) ℚ D).hom
      ((Work.Thom.relToAbs ℚ (Work.Serre.cellCupS D Γ ι f) D).hom z))

/-- The class `U₀ = ρ U` on the disc pair. -/
abbrev cellCupU₀ (q : C(X, Work.RatHurewicz.attachCells (D - 2) Γ ι f)) (r : ℕ)
    (U : Work.Thom.RelCoh ℚ (r + 1) (Work.Serre.cyl q) (Set.range (Work.Serre.cylIncl q))) :
    Work.Thom.RelCoh ℚ (r + 1) ↥(DiscPair.cylPairA₂ (f := f) q) (DiscPair.oldA (f := f) q) :=
  (Work.Thom.relCohMap (Work.Thom.subtypeMap (DiscPair.cylPairA₂ (f := f) q))
    (DiscPair.oldA (f := f) q) (Set.range (Work.Serre.cylIncl q))
    (fun _ hx => hx) ℚ (r + 1)).hom U

/-- The retraction to `S` on the open part `V` of the disc pair: the composite
`V → cyl q → Z` lands in `S`. -/
def cellCupGv (q : C(X, Work.RatHurewicz.attachCells (D - 2) Γ ι f)) :
    C(↥(DiscPair.cylU₁A₂ (f := f) q), ↥(Work.Serre.cellCupS D Γ ι f)) where
  toFun x := ⟨Work.Serre.cylRetract q (x : Work.Serre.cyl q),
    DiscPair.cylU₁_inter_cylPairA₂_subset q ⟨x.2, x.1.2⟩⟩
  continuous_toFun := Continuous.subtype_mk
    ((Work.Serre.cylRetract q).continuous.comp
      (continuous_subtype_val.comp continuous_subtype_val))
    (fun x => DiscPair.cylU₁_inter_cylPairA₂_subset q ⟨x.2, x.1.2⟩)

/-- The bottom copy of the collar, viewed inside the collar. -/
abbrev cellCupCollarA₁ (q : C(X, Work.RatHurewicz.attachCells (D - 2) Γ ι f)) :
    Set ↥(DiscPair.cylU₀A₂ (f := f) q) :=
  Work.Cohomology.Endgame.A₁' (TopCat.of ↥(DiscPair.cylPairA₂ (f := f) q))
    (DiscPair.oldA (f := f) q) (DiscPair.cylU₀A₂ (f := f) q)

/-- The canonical map from the collar-model bottom to the bottom copy. -/
def cellCupCollarH (q : C(X, Work.RatHurewicz.attachCells (D - 2) Γ ι f)) :
    C(↥(cellCupCollarA₁ (D := D) (Γ := Γ) (ι := ι) (f := f) q), ↥(DiscPair.oldA (f := f) q)) where
  toFun x := ⟨(x.1 : ↥(DiscPair.cylPairA₂ (f := f) q)),
    (show (x.1 : ↥(DiscPair.cylU₀A₂ (f := f) q)) ∈ cellCupCollarA₁ (D := D) (Γ := Γ) (ι := ι) (f := f) q
      from x.2)⟩
  continuous_toFun := Continuous.subtype_mk
    (continuous_subtype_val.comp continuous_subtype_val) (fun x => x.2)

/-- Its inverse. -/
def cellCupCollarHinv (q : C(X, Work.RatHurewicz.attachCells (D - 2) Γ ι f)) :
    C(↥(DiscPair.oldA (f := f) q), ↥(cellCupCollarA₁ (D := D) (Γ := Γ) (ι := ι) (f := f) q)) where
  toFun y := ⟨⟨(y : ↥(DiscPair.cylPairA₂ (f := f) q)),
      DiscPair.oldA_subset_oldU₀ (f := f) q y.2⟩, y.2⟩
  continuous_toFun := Continuous.subtype_mk
    (Continuous.subtype_mk continuous_subtype_val
      (fun y => DiscPair.oldA_subset_oldU₀ (f := f) q y.2)) (fun y => y.2)

theorem cellCupCollarH_hcomp (q : C(X, Work.RatHurewicz.attachCells (D - 2) Γ ι f)) :
    (cellCupCollarHinv (D := D) (Γ := Γ) (ι := ι) (f := f) q).comp
      (cellCupCollarH (D := D) (Γ := Γ) (ι := ι) (f := f) q) = ContinuousMap.id _ := by
  ext x
  rfl

theorem cellCupCollarH_hcomp' (q : C(X, Work.RatHurewicz.attachCells (D - 2) Γ ι f)) :
    (cellCupCollarH (D := D) (Γ := Γ) (ι := ι) (f := f) q).comp
      (cellCupCollarHinv (D := D) (Γ := Γ) (ι := ι) (f := f) q) = ContinuousMap.id _ := by
  ext y
  rfl

/-- `oldIncl` composed with the homeomorphism is the inclusion of the bottom in the collar. -/
theorem cellCupCollarH_incl (q : C(X, Work.RatHurewicz.attachCells (D - 2) Γ ι f)) :
    (DiscPair.oldIncl (D := D) (Γ := Γ) (ι := ι) (f := f) q).comp
      (cellCupCollarH (D := D) (Γ := Γ) (ι := ι) (f := f) q)
      = (Work.Thom.subtypeMap (cellCupCollarA₁ (D := D) (Γ := Γ) (ι := ι) (f := f) q)) := by
  ext x
  rfl

/-- The bottom of the collar is a rational homology isomorphism. -/
theorem cellCupCollar_isRatHomologyIso (q : C(X, Work.RatHurewicz.attachCells (D - 2) Γ ι f)) :
    IsRatHomologyIso (cellCupCollarH (D := D) (Γ := Γ) (ι := ι) (f := f) q) :=
  IsRatHomologyIso.of_homotopyEquiv (ContinuousMap.HomotopyEquiv.mk
    (cellCupCollarH (D := D) (Γ := Γ) (ι := ι) (f := f) q)
    (cellCupCollarHinv (D := D) (Γ := Γ) (ι := ι) (f := f) q)
    (by rw [cellCupCollarH_hcomp])
    (by rw [cellCupCollarH_hcomp']))

/-- **The relative cohomology of the collar pair vanishes.** -/
theorem isZero_relCoh_collarAuxSelf (q : C(X, Work.RatHurewicz.attachCells (D - 2) Γ ι f))
    (K : ℕ) (hK : 1 ≤ K) :
    IsZero (Work.Thom.RelCoh ℚ K ↥(DiscPair.cylU₀A₂ (f := f) q)
      (cellCupCollarA₁ (D := D) (Γ := Γ) (ι := ι) (f := f) q)) := by
  refine isZero_relCoh_of_cohMapIso (cellCupCollarA₁ (D := D) (Γ := Γ) (ι := ι) (f := f) q) hK
    (fun j => ?_)
  haveI h1 : IsIso (Work.Thom.CohMap (DiscPair.oldIncl (D := D) (Γ := Γ) (ι := ι) (f := f) q)
      ℚ j) :=
    cohMapIsoOfRatHomologyIso (DiscPair.oldIncl (D := D) (Γ := Γ) (ι := ι) (f := f) q) j
      (DiscPair.oldPartCollarIncl D ι f q j)
  haveI h2 : IsIso (Work.Thom.CohMap
      (cellCupCollarH (D := D) (Γ := Γ) (ι := ι) (f := f) q) ℚ j) :=
    cohMapIsoOfRatHomologyIso (cellCupCollarH (D := D) (Γ := Γ) (ι := ι) (f := f) q) j
      (cellCupCollar_isRatHomologyIso (D := D) (Γ := Γ) (ι := ι) (f := f) q j)
  let comp : C(↥(cellCupCollarA₁ (D := D) (Γ := Γ) (ι := ι) (f := f) q),
      ↥(DiscPair.cylU₀A₂ (f := f) q)) :=
    (DiscPair.oldIncl (D := D) (Γ := Γ) (ι := ι) (f := f) q).comp
      (cellCupCollarH (D := D) (Γ := Γ) (ι := ι) (f := f) q)
  have heq : (⟨Subtype.val, continuous_subtype_val⟩ :
        C(↥(cellCupCollarA₁ (D := D) (Γ := Γ) (ι := ι) (f := f) q),
          ↥(DiscPair.cylU₀A₂ (f := f) q))) = comp := by
    ext x
    rfl
  have hCoh : Work.Thom.CohMap (⟨Subtype.val, continuous_subtype_val⟩ :
        C(↥(cellCupCollarA₁ (D := D) (Γ := Γ) (ι := ι) (f := f) q),
          ↥(DiscPair.cylU₀A₂ (f := f) q))) ℚ j = Work.Thom.CohMap comp ℚ j := by
    rw [heq]
  have hcomp : comp = (DiscPair.oldIncl (D := D) (Γ := Γ) (ι := ι) (f := f) q).comp
      (cellCupCollarH (D := D) (Γ := Γ) (ι := ι) (f := f) q) := rfl
  rw [hCoh, hcomp, Work.Thom.CohMap_comp (cellCupCollarH (D := D) (Γ := Γ) (ι := ι) (f := f) q)
    (DiscPair.oldIncl (D := D) (Γ := Γ) (ι := ι) (f := f) q) ℚ j]
  infer_instance


/-- **`α` vanishes on `V = A₂ ∩ {λ > 0}`.** -/
theorem cellCupAlphaV (q : C(X, Work.RatHurewicz.attachCells (D - 2) Γ ι f))
    (z : Work.Thom.RelCoh ℚ D (Work.RatHurewicz.attachCells (D - 2) Γ ι f)
      (Work.Serre.cellCupS D Γ ι f)) :
    (Work.Thom.CohMap (Work.Thom.subtypeMap (DiscPair.cylU₁A₂ (f := f) q)) ℚ D).hom
      (cellCupAlpha (f := f) q z) = 0 := by
  have hcomp : (Work.Serre.cylRetract q).comp
      ((Work.Thom.subtypeMap (DiscPair.cylPairA₂ (f := f) q)).comp
        (Work.Thom.subtypeMap (DiscPair.cylU₁A₂ (f := f) q)))
      = (Work.Thom.subtypeMap (Work.Serre.cellCupS D Γ ι f)).comp
        (cellCupGv (D := D) (f := f) q) := by
    ext x
    rfl
  have h1 : (Work.Thom.CohMap (Work.Thom.subtypeMap (DiscPair.cylU₁A₂ (f := f) q)) ℚ D).hom
      (cellCupAlpha (f := f) q z)
      = (Work.Thom.CohMap
          ((Work.Thom.subtypeMap (DiscPair.cylPairA₂ (f := f) q)).comp
            (Work.Thom.subtypeMap (DiscPair.cylU₁A₂ (f := f) q))) ℚ D).hom
        ((Work.Thom.CohMap (Work.Serre.cylRetract q) ℚ D).hom
          ((Work.Thom.relToAbs ℚ (Work.Serre.cellCupS D Γ ι f) D).hom z)) := by
    show (Work.Thom.CohMap (Work.Thom.subtypeMap (DiscPair.cylU₁A₂ (f := f) q)) ℚ D).hom
        ((Work.Thom.CohMap (Work.Thom.subtypeMap (DiscPair.cylPairA₂ (f := f) q)) ℚ D).hom
          ((Work.Thom.CohMap (Work.Serre.cylRetract q) ℚ D).hom
            ((Work.Thom.relToAbs ℚ (Work.Serre.cellCupS D Γ ι f) D).hom z))) = _
    rw [Work.Thom.CohMap_comp (Work.Thom.subtypeMap (DiscPair.cylU₁A₂ (f := f) q))
      (Work.Thom.subtypeMap (DiscPair.cylPairA₂ (f := f) q)) ℚ D,
      ModuleCat.hom_comp, LinearMap.comp_apply]
  rw [h1]
  have h2 : (Work.Thom.CohMap
        ((Work.Thom.subtypeMap (DiscPair.cylPairA₂ (f := f) q)).comp
          (Work.Thom.subtypeMap (DiscPair.cylU₁A₂ (f := f) q))) ℚ D).hom
      ((Work.Thom.CohMap (Work.Serre.cylRetract q) ℚ D).hom
        ((Work.Thom.relToAbs ℚ (Work.Serre.cellCupS D Γ ι f) D).hom z))
      = (Work.Thom.CohMap
          ((Work.Serre.cylRetract q).comp
            ((Work.Thom.subtypeMap (DiscPair.cylPairA₂ (f := f) q)).comp
              (Work.Thom.subtypeMap (DiscPair.cylU₁A₂ (f := f) q)))) ℚ D).hom
        ((Work.Thom.relToAbs ℚ (Work.Serre.cellCupS D Γ ι f) D).hom z) := by
    rw [Work.Thom.CohMap_comp
      ((Work.Thom.subtypeMap (DiscPair.cylPairA₂ (f := f) q)).comp
        (Work.Thom.subtypeMap (DiscPair.cylU₁A₂ (f := f) q)))
      (Work.Serre.cylRetract q) ℚ D, ModuleCat.hom_comp, LinearMap.comp_apply]
  rw [h2, hcomp]
  rw [Work.Thom.CohMap_comp (cellCupGv (D := D) (f := f) q)
      (Work.Thom.subtypeMap (Work.Serre.cellCupS D Γ ι f)) ℚ D, ModuleCat.hom_comp,
    LinearMap.comp_apply]
  have hz : (Work.Thom.CohMap (Work.Thom.subtypeMap (Work.Serre.cellCupS D Γ ι f)) ℚ D).hom
      ((Work.Thom.relToAbs ℚ (Work.Serre.cellCupS D Γ ι f) D).hom z) = 0 := by
    have h := congrArg
      (fun (g : Work.Thom.RelCoh ℚ D (Work.RatHurewicz.attachCells (D - 2) Γ ι f)
          (Work.Serre.cellCupS D Γ ι f) ⟶
            Work.Thom.Coh ℚ D (Work.Serre.cellCupS D Γ ι f)) => ModuleCat.Hom.hom g z)
      (Work.Thom.relToAbs_comp_CohMap_subtype ℚ (Work.Serre.cellCupS D Γ ι f) D)
    simpa only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_zero,
      LinearMap.zero_apply] using h
  rw [hz, map_zero]

/-- **The lift of `α` to the `V`-relative group.** -/
theorem cellCupExists_lift_alpha (q : C(X, Work.RatHurewicz.attachCells (D - 2) Γ ι f))
    (z : Work.Thom.RelCoh ℚ D (Work.RatHurewicz.attachCells (D - 2) Γ ι f)
      (Work.Serre.cellCupS D Γ ι f)) :
    ∃ aT : Work.Thom.RelCoh ℚ D ↥(DiscPair.cylPairA₂ (f := f) q)
        (DiscPair.cylU₁A₂ (f := f) q),
      (Work.Thom.relToAbs ℚ (DiscPair.cylU₁A₂ (f := f) q) D).hom aT
        = cellCupAlpha (f := f) q z := by
  have hrange : (Work.Thom.relToAbs ℚ (DiscPair.cylU₁A₂ (f := f) q) D).hom.range
      = (Work.Thom.restrCoh (DiscPair.cylU₁A₂ (f := f) q) ℚ D).hom.ker := by
    have hex := Work.Cohomology.pair_exact₂ ℚ (TopCat.of ↥(DiscPair.cylPairA₂ (f := f) q))
      (DiscPair.cylU₁A₂ (f := f) q) D
    rw [ShortComplex.moduleCat_exact_iff_range_eq_ker] at hex
    exact hex
  have hmem : cellCupAlpha (f := f) q z
      ∈ (Work.Thom.restrCoh (DiscPair.cylU₁A₂ (f := f) q) ℚ D).hom.ker :=
    LinearMap.mem_ker.mpr (cellCupAlphaV (D := D) (f := f) q z)
  rw [← hrange] at hmem
  obtain ⟨aT, haT⟩ := LinearMap.mem_range.mp hmem
  exact ⟨aT, haT⟩

/-- The `qTripleF` map of the collar triple is the `relCohMap` of the identity. -/
theorem cellCupTripleF_eq (q : C(X, Work.RatHurewicz.attachCells (D - 2) Γ ι f)) (r : ℕ) :
    HomologicalComplex.homologyMap
      (DiscPair.qTripleF (TopCat.of ↥(DiscPair.cylPairA₂ (f := f) q))
        (DiscPair.oldA (f := f) q) (DiscPair.cylU₀A₂ (f := f) q)
        (DiscPair.oldA_subset_oldU₀ (f := f) q)) (r + 1)
      = Work.Thom.relCohMap (ContinuousMap.id ↥(DiscPair.cylPairA₂ (f := f) q))
          (DiscPair.oldA (f := f) q) (DiscPair.cylU₀A₂ (f := f) q)
          (DiscPair.oldA_subset_oldU₀ (f := f) q) ℚ (r + 1) := rfl

/-- **The lift of `U₀` over the collar.** -/
theorem cellCupExists_lift_U₀ (q : C(X, Work.RatHurewicz.attachCells (D - 2) Γ ι f)) (r : ℕ)
    (U : Work.Thom.RelCoh ℚ (r + 1) (Work.Serre.cyl q) (Set.range (Work.Serre.cylIncl q))) :
    ∃ Ũ : Work.Thom.RelCoh ℚ (r + 1) ↥(DiscPair.cylPairA₂ (f := f) q)
        (DiscPair.cylU₀A₂ (f := f) q),
      (Work.Thom.relCohMap (ContinuousMap.id ↥(DiscPair.cylPairA₂ (f := f) q))
          (DiscPair.oldA (f := f) q) (DiscPair.cylU₀A₂ (f := f) q)
          (DiscPair.oldA_subset_oldU₀ (f := f) q) ℚ (r + 1)).hom Ũ
        = cellCupU₀ (D := D) (Γ := Γ) (ι := ι) (f := f) (X := X) q r U := by
  have hS := DiscPair.qTripleShort_shortExact (TopCat.of ↥(DiscPair.cylPairA₂ (f := f) q))
    (DiscPair.oldA (f := f) q) (DiscPair.cylU₀A₂ (f := f) q)
    (DiscPair.oldA_subset_oldU₀ (f := f) q)
  haveI hZ : CategoryTheory.Limits.IsZero (Work.Thom.RelCoh ℚ (r + 1)
      ↥(DiscPair.cylU₀A₂ (f := f) q)
      (Work.Cohomology.Endgame.A₁' (TopCat.of ↥(DiscPair.cylPairA₂ (f := f) q))
        (DiscPair.oldA (f := f) q) (DiscPair.cylU₀A₂ (f := f) q))) :=
    isZero_relCoh_collarAuxSelf (D := D) (Γ := Γ) (ι := ι) (f := f) (X := X) q (r + 1)
      (by omega)
  have hz : HomologicalComplex.homologyMap
      (DiscPair.qTripleG (TopCat.of ↥(DiscPair.cylPairA₂ (f := f) q))
        (DiscPair.oldA (f := f) q) (DiscPair.cylU₀A₂ (f := f) q)
        (DiscPair.oldA_subset_oldU₀ (f := f) q)) (r + 1) = 0 :=
    CategoryTheory.Limits.IsZero.eq_zero_of_tgt hZ _
  have hex := hS.homology_exact₂ (r + 1)
  haveI hE : Epi (HomologicalComplex.homologyMap
      (DiscPair.qTripleF (TopCat.of ↥(DiscPair.cylPairA₂ (f := f) q))
        (DiscPair.oldA (f := f) q) (DiscPair.cylU₀A₂ (f := f) q)
        (DiscPair.oldA_subset_oldU₀ (f := f) q)) (r + 1)) :=
    (ShortComplex.exact_iff_epi _ hz).mp hex
  obtain ⟨Ũ, hŨ⟩ := (ModuleCat.epi_iff_surjective _).mp hE (cellCupU₀ (f := f) q r U)
  refine ⟨Ũ, ?_⟩
  rw [← cellCupTripleF_eq (D := D) (Γ := Γ) (ι := ι) (f := f) (X := X) q r]
  exact hŨ

/-- `V = A₂ ∩ {λ > 0}` is open in `A₂`. -/
theorem cellCupIsOpen_cylU₁A₂ (q : C(X, Work.RatHurewicz.attachCells (D - 2) Γ ι f)) :
    IsOpen (DiscPair.cylU₁A₂ (f := f) q) :=
  (DiscPair.isOpen_cylU₁ q).preimage continuous_subtype_val

/-- `W = A₂ ∩ {λ < 1/2}` is open in `A₂`. -/
theorem cellCupIsOpen_cylU₀A₂ (q : C(X, Work.RatHurewicz.attachCells (D - 2) Γ ι f)) :
    IsOpen (DiscPair.cylU₀A₂ (f := f) q) :=
  (DiscPair.isOpen_cylU₀ q).preimage continuous_subtype_val

/-- **The two-relative cup product of the collar cover vanishes**: its target is the (zero)
`univ`-relative group of `A₂`. -/
theorem cellCupRelRelCupZero {r : ℕ} (q : C(X, Work.RatHurewicz.attachCells (D - 2) Γ ι f))
    (aT : Work.Thom.RelCoh ℚ D ↥(DiscPair.cylPairA₂ (f := f) q) (DiscPair.cylU₁A₂ (f := f) q))
    (Ut : Work.Thom.RelCoh ℚ (r + 1) ↥(DiscPair.cylPairA₂ (f := f) q)
      (DiscPair.cylU₀A₂ (f := f) q)) :
    Work.Whitney.relRelCupOpen (DiscPair.cylU₁A₂ (f := f) q) (DiscPair.cylU₀A₂ (f := f) q)
      (cellCupIsOpen_cylU₁A₂ (D := D) (Γ := Γ) (ι := ι) (f := f) (X := X) q)
      (cellCupIsOpen_cylU₀A₂ (D := D) (Γ := Γ) (ι := ι) (f := f) (X := X) q) D (r + 1) aT Ut = 0 := by
  haveI : Subsingleton (Work.Thom.RelCoh ℚ (D + (r + 1))
      ↥(DiscPair.cylPairA₂ (f := f) q) (DiscPair.cylU₁A₂ (f := f) q ∪ DiscPair.cylU₀A₂ (f := f) q)) := by
    rw [Set.union_comm, DiscPair.cylU₀A₂_union_cylU₁A₂]
    exact Work.Serre.relCohomologyUnivVanishing ℚ (TopCat.of ↥(DiscPair.cylPairA₂ (f := f) q)) (D + (r + 1))
  exact Subsingleton.elim _ _

/-- **The mixed cup product in the collar vanishes.** -/
theorem cellCupMixedW_zero {r : ℕ} (q : C(X, Work.RatHurewicz.attachCells (D - 2) Γ ι f)) (hD : 2 ≤ D)
    (z : Work.Thom.RelCoh ℚ D (Work.RatHurewicz.attachCells (D - 2) Γ ι f)
      (Work.Serre.cellCupS D Γ ι f))
    (Ut : Work.Thom.RelCoh ℚ (r + 1) ↥(DiscPair.cylPairA₂ (f := f) q)
      (DiscPair.cylU₀A₂ (f := f) q)) :
    Work.Thom.mixedCupC ℚ (DiscPair.cylU₀A₂ (f := f) q) D (r + 1)
      (cellCupAlpha (f := f) q z) Ut = 0 := by
  obtain ⟨aT, haT⟩ := cellCupExists_lift_alpha (D := D) (Γ := Γ) (ι := ι) (f := f) (X := X) q z
  have h := Work.Serre.relRelCupOpen_mixedCup (DiscPair.cylU₁A₂ (f := f) q)
    (DiscPair.cylU₀A₂ (f := f) q)
    (cellCupIsOpen_cylU₁A₂ (D := D) (Γ := Γ) (ι := ι) (f := f) (X := X) q)
    (cellCupIsOpen_cylU₀A₂ (D := D) (Γ := Γ) (ι := ι) (f := f) (X := X) q) D (r + 1) aT Ut
  rw [cellCupRelRelCupZero (D := D) (Γ := Γ) (ι := ι) (f := f) (X := X) q aT Ut,
    map_zero, haT] at h
  exact h.symm

/-- **The mixed cup product of `α` with `U₀` vanishes.** -/
theorem cellCupMixedU₀_zero {r : ℕ} (q : C(X, Work.RatHurewicz.attachCells (D - 2) Γ ι f)) (hD : 2 ≤ D)
    (z : Work.Thom.RelCoh ℚ D (Work.RatHurewicz.attachCells (D - 2) Γ ι f)
      (Work.Serre.cellCupS D Γ ι f))
    (U : Work.Thom.RelCoh ℚ (r + 1) (Work.Serre.cyl q) (Set.range (Work.Serre.cylIncl q))) :
    Work.Thom.mixedCupC ℚ (DiscPair.oldA (f := f) q) D (r + 1)
      (cellCupAlpha (f := f) q z) (cellCupU₀ (f := f) q r U) = 0 := by
  obtain ⟨Ut, hUt⟩ := cellCupExists_lift_U₀ (D := D) (Γ := Γ) (ι := ι) (f := f) (X := X) q r U
  have hnat := Work.StemsB.mixedCupC_pairNaturalR ℚ (ContinuousMap.id ↥(DiscPair.cylPairA₂ (f := f) q))
    (DiscPair.oldA (f := f) q) (DiscPair.cylU₀A₂ (f := f) q)
    (DiscPair.oldA_subset_oldU₀ (f := f) q) D (r + 1) (cellCupAlpha (f := f) q z) Ut
  rw [cellCupMixedW_zero (D := D) (Γ := Γ) (ι := ι) (f := f) (X := X) q hD z Ut, map_zero,
    Work.Thom.CohMap_id, ModuleCat.hom_id, LinearMap.id_apply, hUt] at hnat
  exact hnat.symm

theorem cellCupUpper (r N D : ℕ) (hr : 1 ≤ r) (hD : 2 ≤ D)
    {Γ : Type} [TopologicalSpace Γ] (hΓ : PathConnectedSpace Γ) (ι : Type)
    (f : ι → C(Work.RatHurewicz.cellSphere (D - 2), Γ))
    {X : Type} [TopologicalSpace X] (q : C(X, Work.RatHurewicz.attachCells (D - 2) Γ ι f))
    (hq : Work.StemsB.IsSerreFibration q) (hN : D + r + 1 ≤ N + 1)
    (U : Work.Thom.RelCoh ℚ (r + 1) (Work.Serre.cyl q) (Set.range (Work.Serre.cylIncl q))) :
    Set.range (Work.Serre.cellCupPsi r N D ι f q U) ⊆
      Set.range (Work.Serre.cellCupForget r N D ι f q) := by
  intro y hy
  obtain ⟨z, rfl⟩ := hy
  -- (1) the restriction of the cup map to the disc pair is the mixed cup of `α` with `U₀`
  have hρ : (Work.Thom.relCohMap (Work.Thom.subtypeMap (DiscPair.cylPairA₂ (f := f) q))
        (DiscPair.oldA (f := f) q) (Set.range (Work.Serre.cylIncl q))
        (fun _ hx => hx) ℚ (D + r + 1)).hom
      (Work.Serre.cellCupPsi r N D ι f q U z)
      = Work.Thom.mixedCupC ℚ (DiscPair.oldA (f := f) q) D (r + 1)
          (cellCupAlpha (f := f) q z) (cellCupU₀ (f := f) q r U) := by
    show (Work.Thom.relCohMap (Work.Thom.subtypeMap (DiscPair.cylPairA₂ (f := f) q))
        (DiscPair.oldA (f := f) q) (Set.range (Work.Serre.cylIncl q))
        (fun _ hx => hx) ℚ (D + r + 1)).hom
      (Work.Thom.mixedCupC ℚ (Set.range (Work.Serre.cylIncl q)) D (r + 1)
        ((Work.Thom.CohMap (Work.Serre.cylRetract q) ℚ D).hom
          ((Work.Thom.relToAbs ℚ (Work.Serre.cellCupS D Γ ι f) D).hom z)) U) = _
    exact Work.StemsB.mixedCupC_pairNaturalR ℚ
      (Work.Thom.subtypeMap (DiscPair.cylPairA₂ (f := f) q))
      (DiscPair.oldA (f := f) q) (Set.range (Work.Serre.cylIncl q)) (fun _ hx => hx) D (r + 1)
      ((Work.Thom.CohMap (Work.Serre.cylRetract q) ℚ D).hom
        ((Work.Thom.relToAbs ℚ (Work.Serre.cellCupS D Γ ι f) D).hom z)) U
  -- (2) that mixed cup vanishes
  have hρ0 : (Work.Thom.relCohMap (Work.Thom.subtypeMap (DiscPair.cylPairA₂ (f := f) q))
        (DiscPair.oldA (f := f) q) (Set.range (Work.Serre.cylIncl q))
        (fun _ hx => hx) ℚ (D + r + 1)).hom
      (Work.Serre.cellCupPsi r N D ι f q U z) = 0 := by
    rw [hρ, cellCupMixedU₀_zero (D := D) (Γ := Γ) (ι := ι) (f := f) (X := X) q hD z U]
  -- (3) the long exact sequence of the triple `A ⊆ A₂ ⊆ M`
  have hrange : (HomologicalComplex.homologyMap (DiscPair.qTripleF (TopCat.of (Work.Serre.cyl q))
        (Set.range (Work.Serre.cylIncl q)) (DiscPair.cylPairA₂ (f := f) q)
        Set.subset_union_right) (D + r + 1)).hom.range
      = (HomologicalComplex.homologyMap (DiscPair.qTripleG (TopCat.of (Work.Serre.cyl q))
        (Set.range (Work.Serre.cylIncl q)) (DiscPair.cylPairA₂ (f := f) q)
        Set.subset_union_right) (D + r + 1)).hom.ker := by
    have hex := (DiscPair.qTripleShort_shortExact (TopCat.of (Work.Serre.cyl q))
      (Set.range (Work.Serre.cylIncl q)) (DiscPair.cylPairA₂ (f := f) q)
      Set.subset_union_right).homology_exact₂ (D + r + 1)
    rw [ShortComplex.moduleCat_exact_iff_range_eq_ker] at hex
    exact hex
  have hmem : Work.Serre.cellCupPsi r N D ι f q U z
      ∈ (HomologicalComplex.homologyMap (DiscPair.qTripleF (TopCat.of (Work.Serre.cyl q))
          (Set.range (Work.Serre.cylIncl q)) (DiscPair.cylPairA₂ (f := f) q)
          Set.subset_union_right) (D + r + 1)).hom.range := by
    rw [hrange]
    exact hρ0
  obtain ⟨w, hw⟩ := LinearMap.mem_range.mp hmem
  refine ⟨w, ?_⟩
  have hF : Work.Serre.cellCupForget r N D ι f q w
      = (HomologicalComplex.homologyMap (DiscPair.qTripleF (TopCat.of (Work.Serre.cyl q))
          (Set.range (Work.Serre.cylIncl q)) (DiscPair.cylPairA₂ (f := f) q)
          Set.subset_union_right) (D + r + 1)).hom w := rfl
  rw [hF]
  exact hw

end

end Work.Serre
