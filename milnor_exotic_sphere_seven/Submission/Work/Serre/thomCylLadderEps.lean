import Mathlib
import Submission.Work.Serre.thomCylLadder
import Submission.Work.Serre.relCohMap_oldIncl_bijective
import Submission.Work.Serre.DiscPair.cylPreimageRelChainsIso
import Submission.Work.Thom.CapGlue.isIso_relComplexMap_homeomorph
import Submission.Work.Serre.TripleCohDefs
import Submission.Work.Serre.relCoh_extension
import Submission.Work.Serre.discPairCellVanishing
import Submission.Work.Serre.discPairCellVanishingSucc

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-! # The specific old-part identification `ε` of the cellular-step ladder -/

open CategoryTheory CategoryTheory.Limits

namespace Work.Serre

noncomputable section

set_option maxHeartbeats 8000000

variable {D : ℕ} {Γ : Type} [TopologicalSpace Γ] {ι : Type}
  {f : ι → C(Work.RatHurewicz.cellSphere (D - 2), Γ)} {X : Type} [TopologicalSpace X]

/-- The inclusion of the part of the cylinder over `S` into `old ∪ A`. -/
def oldInclToNew (q : C(X, Work.RatHurewicz.attachCells (D - 2) Γ ι f))
    (S : Set (Work.RatHurewicz.attachCells (D - 2) Γ ι f)) :
    C(↥((Work.Serre.cylRetract q) ⁻¹' S),
      ↥((Work.Serre.cylRetract q) ⁻¹' S ∪ Set.range (Work.Serre.cylIncl q))) where
  toFun x := ⟨x.1, Or.inl x.2⟩
  continuous_toFun := by fun_prop

/-- **The pullback along the inclusion `old ↪ old ∪ A` is an isomorphism.** -/
theorem isIso_oldInclToNew (q : C(X, Work.RatHurewicz.attachCells (D - 2) Γ ι f))
    (S : Set (Work.RatHurewicz.attachCells (D - 2) Γ ι f)) (hS : IsClosed S) (k : ℕ) :
    CategoryTheory.IsIso (Work.Thom.relCohMap (oldInclToNew q S)
      {x : ↥((Work.Serre.cylRetract q) ⁻¹' S) | (x : Work.Serre.cyl q) ∈
        Set.range (Work.Serre.cylIncl q)}
      {x : ↥((Work.Serre.cylRetract q) ⁻¹' S ∪ Set.range (Work.Serre.cylIncl q)) |
        (x : Work.Serre.cyl q) ∈ Set.range (Work.Serre.cylIncl q)}
      (fun _ hx => hx) ℚ k) :=
  (CategoryTheory.ConcreteCategory.isIso_iff_bijective _).mpr
    (Work.Serre.relCohMap_oldIncl_bijective q S hS k)

/-- The pullback along the inclusion, as an isomorphism. -/
noncomputable def oldInclIso (q : C(X, Work.RatHurewicz.attachCells (D - 2) Γ ι f))
    (S : Set (Work.RatHurewicz.attachCells (D - 2) Γ ι f)) (hS : IsClosed S) (k : ℕ) :
    Work.Thom.RelCoh ℚ k
        ↥((Work.Serre.cylRetract q) ⁻¹' S ∪ Set.range (Work.Serre.cylIncl q))
        {x : ↥((Work.Serre.cylRetract q) ⁻¹' S ∪ Set.range (Work.Serre.cylIncl q)) |
          (x : Work.Serre.cyl q) ∈ Set.range (Work.Serre.cylIncl q)} ≅
      Work.Thom.RelCoh ℚ k ↥((Work.Serre.cylRetract q) ⁻¹' S)
        {x : ↥((Work.Serre.cylRetract q) ⁻¹' S) | (x : Work.Serre.cyl q) ∈
          Set.range (Work.Serre.cylIncl q)} :=
  @asIso _ _ _ _
    (Work.Thom.relCohMap (oldInclToNew q S)
      {x : ↥((Work.Serre.cylRetract q) ⁻¹' S) | (x : Work.Serre.cyl q) ∈
        Set.range (Work.Serre.cylIncl q)}
      {x : ↥((Work.Serre.cylRetract q) ⁻¹' S ∪ Set.range (Work.Serre.cylIncl q)) |
        (x : Work.Serre.cyl q) ∈ Set.range (Work.Serre.cylIncl q)}
      (fun _ hx => hx) ℚ k)
    (isIso_oldInclToNew q S hS k)

/-- The homeomorphism `cyl (q|_S) ≃ old` as a continuous map. -/
def preimageMap (q : C(X, Γ)) (S : Set Γ) (hS : IsClosed S) :
    C(Work.Serre.cyl (Work.Serre.restrictFibre q S), ↥((Work.Serre.cylRetract q) ⁻¹' S)) :=
  ⟨(DiscPair.cylPreimageHomeo q S hS : Work.Serre.cyl (Work.Serre.restrictFibre q S) →
      ↥((Work.Serre.cylRetract q) ⁻¹' S)),
    (DiscPair.cylPreimageHomeo q S hS).continuous⟩

/-- The pullback along the homeomorphism, as an isomorphism. -/
noncomputable def preimageIso (q : C(X, Γ)) (S : Set Γ) (hS : IsClosed S) (k : ℕ) :
    Work.Thom.RelCoh ℚ k ↥((Work.Serre.cylRetract q) ⁻¹' S)
        {x : ↥((Work.Serre.cylRetract q) ⁻¹' S) | (x : Work.Serre.cyl q) ∈
          Set.range (Work.Serre.cylIncl q)} ≅
      Work.Thom.RelCoh ℚ k (Work.Serre.cyl (Work.Serre.restrictFibre q S))
        (Set.range (Work.Serre.cylIncl (Work.Serre.restrictFibre q S))) :=
  @asIso _ _ _ _
    (Work.Thom.relCohMap (preimageMap q S hS)
      (Set.range (Work.Serre.cylIncl (Work.Serre.restrictFibre q S)))
      {x : ↥((Work.Serre.cylRetract q) ⁻¹' S) | (x : Work.Serre.cyl q) ∈
        Set.range (Work.Serre.cylIncl q)}
      (fun x hx => (DiscPair.cylPreimageHomeo_range q S hS x).mpr hx) ℚ k)
    (Work.Thom.CapGlue.isIso_relComplexMap_homeomorph
      (Set.range (Work.Serre.cylIncl (Work.Serre.restrictFibre q S)))
      {x : ↥((Work.Serre.cylRetract q) ⁻¹' S) | (x : Work.Serre.cyl q) ∈
        Set.range (Work.Serre.cylIncl q)}
      (DiscPair.cylPreimageHomeo q S hS)
      (fun x => (DiscPair.cylPreimageHomeo_range q S hS x).symm) ℚ k)

end

end Work.Serre

namespace Work.Serre

noncomputable section

variable {D : ℕ} {Γ : Type} [TopologicalSpace Γ] {ι : Type}
  {f : ι → C(Work.RatHurewicz.cellSphere (D - 2), Γ)} {X : Type} [TopologicalSpace X]

/-- **The specific identification `ε` of the pair `(new, A)` of the ladder with the cylinder pair of
the restricted fibration `q|_S`.**  It is the composite of the pullback along the inclusion
`old ↪ new` and the pullback along the homeomorphism `cyl (q|_S) ≃ old`. -/
noncomputable def oldPartIso (q : C(X, Work.RatHurewicz.attachCells (D - 2) Γ ι f))
    (S : Set (Work.RatHurewicz.attachCells (D - 2) Γ ι f)) (hS : IsClosed S) (k : ℕ) :
    Work.Thom.RelCoh ℚ k
        ↥((Work.Serre.cylRetract q) ⁻¹' S ∪ Set.range (Work.Serre.cylIncl q))
        {x : ↥((Work.Serre.cylRetract q) ⁻¹' S ∪ Set.range (Work.Serre.cylIncl q)) |
          (x : Work.Serre.cyl q) ∈ Set.range (Work.Serre.cylIncl q)} ≅
      Work.Thom.RelCoh ℚ k (Work.Serre.cyl (Work.Serre.restrictFibre q S))
        (Set.range (Work.Serre.cylIncl (Work.Serre.restrictFibre q S))) :=
  (oldInclIso q S hS k) ≪≫ (preimageIso q S hS k)

end

end Work.Serre

namespace Work.Serre

noncomputable section

variable {D : ℕ} {Γ : Type} [TopologicalSpace Γ] {ι : Type}
  {f : ι → C(Work.RatHurewicz.cellSphere (D - 2), Γ)} {X : Type} [TopologicalSpace X]

/-- The `IH` class pushed along `ε⁻¹`: the class on `(new, A)` extending the old part. -/
noncomputable def uNew (r : ℕ) (q : C(X, Work.RatHurewicz.attachCells (D - 2) Γ ι f))
    (S : Set (Work.RatHurewicz.attachCells (D - 2) Γ ι f)) (hS : IsClosed S)
    (U_S : Work.Thom.RelCoh ℚ (r + 1) (Work.Serre.cyl (Work.Serre.restrictFibre q S))
      (Set.range (Work.Serre.cylIncl (Work.Serre.restrictFibre q S)))) :
    Work.Thom.RelCoh ℚ (r + 1)
      ↥((Work.Serre.cylRetract q) ⁻¹' S ∪ Set.range (Work.Serre.cylIncl q))
      {x : ↥((Work.Serre.cylRetract q) ⁻¹' S ∪ Set.range (Work.Serre.cylIncl q)) |
        (x : Work.Serre.cyl q) ∈ Set.range (Work.Serre.cylIncl q)} :=
  (oldPartIso q S hS (r + 1)).inv U_S

end

end Work.Serre

namespace Work.Serre

noncomputable section

variable {D : ℕ} {Γ : Type} [TopologicalSpace Γ] {ι : Type}
  {f : ι → C(Work.RatHurewicz.cellSphere (D - 2), Γ)} {X : Type} [TopologicalSpace X]

/-- **The extension class `U` of the ladder.**  For the class `U_S` produced by the induction
hypothesis, there is a class `U ∈ H^{r+1}(cyl q, A)` whose restriction to `(new, A)` is `ε⁻¹ U_S`;
it is unique. -/
theorem exists_extensionClass (r N D : ℕ) (hr : 1 ≤ r) (hN : r ≤ N) (hD : 2 ≤ D)
    {Γ : Type} [TopologicalSpace Γ] (hΓ : PathConnectedSpace Γ) (ι : Type)
    (f : ι → C(Work.RatHurewicz.cellSphere (D - 2), Γ)) {X : Type} [TopologicalSpace X]
    (q : C(X, Work.RatHurewicz.attachCells (D - 2) Γ ι f))
    (hq : Work.StemsB.IsSerreFibration q)
    (hvan : ∀ γ : Work.RatHurewicz.attachCells (D - 2) Γ ι f, ∀ t : ℕ, 0 < t → t ≠ r → t ≤ N →
      CategoryTheory.Limits.IsZero (Work.Serre.ratH (TopCat.of (Work.StemsB.fibre q γ)) t))
    (hpc : ∀ γ : Work.RatHurewicz.attachCells (D - 2) Γ ι f,
      PathConnectedSpace (Work.StemsB.fibre q γ))
    (U_S : Work.Thom.RelCoh ℚ (r + 1)
      (Work.Serre.cyl (Work.Serre.restrictFibre q (Work.Serre.ladS D Γ ι f)))
      (Set.range (Work.Serre.cylIncl (Work.Serre.restrictFibre q (Work.Serre.ladS D Γ ι f))))) :
    ∃ U : Work.Thom.RelCoh ℚ (r + 1) (Work.Serre.cyl q) (Set.range (Work.Serre.cylIncl q)),
      (HomologicalComplex.homologyMap (Work.Serre.tripleRestr ℚ (TopCat.of (Work.Serre.cyl q))
        (Set.range (Work.Serre.cylIncl q))
        ((Work.Serre.cylRetract q) ⁻¹' (Work.Serre.ladS D Γ ι f) ∪
          Set.range (Work.Serre.cylIncl q)) (fun _ hx => Or.inr hx)) (r + 1)).hom U
        = uNew r q (Work.Serre.ladS D Γ ι f) Work.RatHurewicz.isClosed_range_attachIncl U_S := by
  obtain ⟨U, hU, -⟩ := Work.Serre.relCoh_extension (TopCat.of (Work.Serre.cyl q))
    (Set.range (Work.Serre.cylIncl q))
    ((Work.Serre.cylRetract q) ⁻¹' (Work.Serre.ladS D Γ ι f) ∪ Set.range (Work.Serre.cylIncl q))
    (fun _ hx => Or.inr hx) (r + 1)
    (Work.Serre.discPairCellVanishing r N D hr hD hΓ ι f q hq hvan hpc (r + 1)
      (by omega) (by omega))
    (Work.Serre.discPairCellVanishingSucc r N D hr hD hΓ ι f q hq hvan hpc (r + 2)
      (by omega) (by omega))
    (uNew r q (Work.Serre.ladS D Γ ι f) Work.RatHurewicz.isClosed_range_attachIncl U_S)
  exact ⟨U, hU⟩

end

end Work.Serre

namespace Work.Serre

noncomputable section

variable {D : ℕ} {Γ : Type} [TopologicalSpace Γ] {ι : Type}
  {f : ι → C(Work.RatHurewicz.cellSphere (D - 2), Γ)} {X : Type} [TopologicalSpace X]

/-- The cup map of the restricted fibration over the old part, with the `IH` class `U_S`. -/
noncomputable def oldCupMap (r : ℕ) (q : C(X, Work.RatHurewicz.attachCells (D - 2) Γ ι f))
    (S : Set (Work.RatHurewicz.attachCells (D - 2) Γ ι f))
    (U_S : Work.Thom.RelCoh ℚ (r + 1) (Work.Serre.cyl (Work.Serre.restrictFibre q S))
      (Set.range (Work.Serre.cylIncl (Work.Serre.restrictFibre q S)))) (k : ℕ) :
    Work.Thom.Coh ℚ k ↥S ⟶
      Work.Thom.RelCoh ℚ (k + (r + 1)) (Work.Serre.cyl (Work.Serre.restrictFibre q S))
        (Set.range (Work.Serre.cylIncl (Work.Serre.restrictFibre q S))) :=
  ModuleCat.ofHom (((Work.Thom.mixedCupC ℚ
      (Set.range (Work.Serre.cylIncl (Work.Serre.restrictFibre q S))) k (r + 1))).flip U_S ∘ₗ
    (Work.Thom.CohMap (Work.Serre.cylRetract (Work.Serre.restrictFibre q S)) ℚ k).hom)

/-- **The old-part vertical `TQ` of the ladder**: the cup map over the old part, transported to the
pair `(old ∪ A, A)` of the mapping cylinder by `ε⁻¹`. -/
noncomputable def TQ (r : ℕ) (q : C(X, Work.RatHurewicz.attachCells (D - 2) Γ ι f))
    (S : Set (Work.RatHurewicz.attachCells (D - 2) Γ ι f)) (hS : IsClosed S)
    (U_S : Work.Thom.RelCoh ℚ (r + 1) (Work.Serre.cyl (Work.Serre.restrictFibre q S))
      (Set.range (Work.Serre.cylIncl (Work.Serre.restrictFibre q S)))) (k : ℕ) :
    Work.Thom.Coh ℚ k ↥S ⟶
      Work.Thom.RelCoh ℚ (k + (r + 1))
        ↥((Work.Serre.cylRetract q) ⁻¹' S ∪ Set.range (Work.Serre.cylIncl q))
        {x : ↥((Work.Serre.cylRetract q) ⁻¹' S ∪ Set.range (Work.Serre.cylIncl q)) |
          (x : Work.Serre.cyl q) ∈ Set.range (Work.Serre.cylIncl q)} :=
  oldCupMap r q S U_S k ≫ (oldPartIso q S hS (k + (r + 1))).inv

/-- **`TQ k` is an isomorphism in the range**: it is the cup map of `IH` followed by the
identification `ε⁻¹`. -/
theorem isIso_TQ (r N : ℕ) (q : C(X, Work.RatHurewicz.attachCells (D - 2) Γ ι f))
    (S : Set (Work.RatHurewicz.attachCells (D - 2) Γ ι f)) (hS : IsClosed S)
    (IH : Work.Serre.ThomCylAt r N (Work.Serre.restrictFibre q S)) (k : ℕ)
    (hk : k + (r + 1) ≤ N + 1) :
    CategoryTheory.IsIso (TQ r q S hS IH.choose k) := by
  haveI : CategoryTheory.IsIso (oldCupMap r q S IH.choose k) := IH.choose_spec k hk
  show CategoryTheory.IsIso (oldCupMap r q S IH.choose k ≫
    (oldPartIso q S hS (k + (r + 1))).inv)
  infer_instance

end

end Work.Serre

namespace Work.Serre

noncomputable section

variable {D : ℕ} {Γ : Type} [TopologicalSpace Γ] {ι : Type}
  {f : ι → C(Work.RatHurewicz.cellSphere (D - 2), Γ)} {X : Type} [TopologicalSpace X]

/-- **The target vertical `TP` of the ladder**: the mixed cup product with the extension class `U`,
i.e. exactly the map whose being an isomorphism is the conclusion `Work.Serre.ThomCylAt r N q`. -/
noncomputable def TP (r : ℕ) (q : C(X, Work.RatHurewicz.attachCells (D - 2) Γ ι f))
    (U : Work.Thom.RelCoh ℚ (r + 1) (Work.Serre.cyl q) (Set.range (Work.Serre.cylIncl q)))
    (k : ℕ) :
    Work.Thom.Coh ℚ k (Work.RatHurewicz.attachCells (D - 2) Γ ι f) ⟶
      Work.Thom.RelCoh ℚ (k + (r + 1)) (Work.Serre.cyl q)
        (Set.range (Work.Serre.cylIncl q)) :=
  ModuleCat.ofHom (((Work.Thom.mixedCupC ℚ (Set.range (Work.Serre.cylIncl q)) k (r + 1))).flip U ∘ₗ
    (Work.Thom.CohMap (Work.Serre.cylRetract q) ℚ k).hom)

/-- `TP` is the map appearing in the definition of `Work.Serre.ThomCylAt`. -/
theorem tp_eq (r : ℕ) (q : C(X, Work.RatHurewicz.attachCells (D - 2) Γ ι f))
    (U : Work.Thom.RelCoh ℚ (r + 1) (Work.Serre.cyl q) (Set.range (Work.Serre.cylIncl q)))
    (k : ℕ) :
    TP r q U k = ModuleCat.ofHom
      (((Work.Thom.mixedCupC ℚ (Set.range (Work.Serre.cylIncl q)) k (r + 1))).flip U ∘ₗ
        (Work.Thom.CohMap (Work.Serre.cylRetract q) ℚ k).hom) := rfl

end

end Work.Serre

namespace Work.Serre

noncomputable section

variable {D : ℕ} {Γ : Type} [TopologicalSpace Γ] {ι : Type}
  {f : ι → C(Work.RatHurewicz.cellSphere (D - 2), Γ)} {X : Type} [TopologicalSpace X]

/-- **The extension class is non-zero**: its restriction to `(old ∪ A, A)` is `ε⁻¹ U_S`, and `ε`, the
restriction `tripleRestr` and the zero map are all `ℚ`-linear with `tripleRestr 0 = 0`. -/
theorem extensionClass_ne_zero (r : ℕ) (q : C(X, Work.RatHurewicz.attachCells (D - 2) Γ ι f))
    (S : Set (Work.RatHurewicz.attachCells (D - 2) Γ ι f)) (hS : IsClosed S)
    (U_S : Work.Thom.RelCoh ℚ (r + 1) (Work.Serre.cyl (Work.Serre.restrictFibre q S))
      (Set.range (Work.Serre.cylIncl (Work.Serre.restrictFibre q S))))
    (hU_S : U_S ≠ 0)
    (U : Work.Thom.RelCoh ℚ (r + 1) (Work.Serre.cyl q) (Set.range (Work.Serre.cylIncl q)))
    (hU : (HomologicalComplex.homologyMap (Work.Serre.tripleRestr ℚ (TopCat.of (Work.Serre.cyl q))
        (Set.range (Work.Serre.cylIncl q))
        ((Work.Serre.cylRetract q) ⁻¹' S ∪ Set.range (Work.Serre.cylIncl q))
        (fun _ hx => Or.inr hx)) (r + 1)).hom U
      = uNew r q S hS U_S) :
    U ≠ 0 := by
  intro h0
  have h1 : (HomologicalComplex.homologyMap (Work.Serre.tripleRestr ℚ
      (TopCat.of (Work.Serre.cyl q)) (Set.range (Work.Serre.cylIncl q))
      ((Work.Serre.cylRetract q) ⁻¹' S ∪ Set.range (Work.Serre.cylIncl q))
      (fun _ hx => Or.inr hx)) (r + 1)).hom U = 0 := by rw [h0, map_zero]
  rw [hU] at h1
  refine hU_S ?_
  have h2 := congrArg (fun z => (oldPartIso q S hS (r + 1)).hom z) h1
  rw [map_zero] at h2
  simpa [uNew] using h2

end

end Work.Serre
