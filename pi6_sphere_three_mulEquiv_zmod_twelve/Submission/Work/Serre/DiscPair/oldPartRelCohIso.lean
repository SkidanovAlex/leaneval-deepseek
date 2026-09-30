import Mathlib
import Submission.Work.Serre.ThomCylDefs
import Submission.Work.Serre.CWModel.Tower
import Submission.Work.Serre.cylRestrictHomeo
import Submission.Work.Serre.discPairCellVanishing
import Submission.Work.Serre.DiscPair.oldPartDefs
import Submission.Work.Serre.csrExcisionRat
import Submission.Work.Serre.relKronEquiv
import Submission.Work.Serre.RatTower.Defs
import Submission.Work.Serre.DiscPair.oldPartCollarIncl
import Submission.Work.Serre.DiscPair.oldPartCollarInclU

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# The relative cohomology of the old part of the disc-pair bundle

`Work.Serre.DiscPair.oldPartRelCohIso` identifies the relative rational cohomology of the pair
`(N, A₂ ∩ {λ = 0})` of the disc-pair bundle (`N = A₂ = U ∪ range (cylIncl q)`) with the relative
cohomology of the disc-pair bundle of the *restricted* fibration

  `q| : C(↥(q ⁻¹' S), ↥S)`,   `S = range (attachIncl (D-2) Γ ι f)`.

The proof is carried out on rational *homology*, where the two steps "shrink the relative part to
the bottom of the collar" are the deformations of the collar, the two middle steps are the
open-cover excisions (`Work.Serre.csrExcisionRat`), and the passage between the two sides of an
excision is a homeomorphism of pairs (`Work.Serre.DiscPair.relChainsRPairMap_homologyMap_isIso`);
the last step is the homeomorphism `Work.Serre.cylRestrictHomeo` between the collar and the mapping
cylinder of the restriction.  The result is dualised to cohomology with the rational universal
coefficient theorem (`Work.Serre.relKronEquiv`).
-/

set_option maxHeartbeats 1600000

open CategoryTheory CategoryTheory.Limits

namespace Work.Serre.DiscPair

noncomputable section

variable {D : ℕ} {Γ : Type} [TopologicalSpace Γ] {ι : Type}
  {f : ι → C(Work.RatHurewicz.cellSphere (D-2), Γ)} {X : Type} [TopologicalSpace X]

/-- The set `{0 < λ}` inside `U`. -/
abbrev oldU₁U (q : C(X, CylZ D Γ ι f)) : Set ↥(cylPairU q) := {x | (x : cyl q) ∈ cylU₁ q}

/-- Rational relative homology, as a shorthand. -/
abbrev relHR (Y : TopCat) (A : Set Y) (k : ℕ) : ModuleCat ℚ :=
  (Work.StemsB.relChainsR ℚ Y A).homology k

/-! ## The identification of the two sides of the excision -/

/-- The homeomorphism `A₂ ∩ {0 < λ} ≅ U ∩ {0 < λ}`, the identity on the underlying points of the
mapping cylinder. -/
def oldU₁Homeo (q : C(X, CylZ D Γ ι f)) : ↥(cylU₁A₂ q) ≃ₜ ↥(oldU₁U q) :=
  Homeomorph.mk
    ({ toFun := fun z => ⟨⟨z.1.1, cylU₁_inter_cylPairA₂_subset q ⟨z.2, z.1.2⟩⟩, z.2⟩
       invFun := fun w => ⟨⟨w.1.1, Or.inl w.1.2⟩, w.2⟩
       left_inv := fun z => Subtype.ext (Subtype.ext rfl)
       right_inv := fun w => Subtype.ext (Subtype.ext rfl) } : ↥(cylU₁A₂ q) ≃ ↥(oldU₁U q))
    (by
      show Continuous fun z : ↥(cylU₁A₂ q) =>
        (⟨⟨z.1.1, cylU₁_inter_cylPairA₂_subset q ⟨z.2, z.1.2⟩⟩, z.2⟩ : ↥(oldU₁U q))
      fun_prop)
    (by
      show Continuous fun w : ↥(oldU₁U q) => (⟨⟨w.1.1, Or.inl w.1.2⟩, w.2⟩ : ↥(cylU₁A₂ q))
      fun_prop)

/-- Membership is preserved by `oldU₁Homeo`. -/
theorem oldU₁Homeo_mem (q : C(X, CylZ D Γ ι f)) (z : ↥(cylU₁A₂ q)) :
    ((z : ↥(cylPairA₂ q)) ∈ cylU₀A₂ q)
      ↔ ((oldU₁Homeo q z : ↥(oldU₁U q)) : ↥(cylPairU q)) ∈ oldUU₀ q := by
  change ((z.1.1 : cyl q) ∈ cylU₀ q) ↔ (((oldU₁Homeo q z : ↥(oldU₁U q)) : ↥(cylPairU q)).1 : cyl q) ∈ cylU₀ q
  rw [show (((oldU₁Homeo q z : ↥(oldU₁U q)) : ↥(cylPairU q)).1 : cyl q) = (z.1.1 : cyl q) from rfl]

/-! ## The main homology isomorphism -/

set_option maxHeartbeats 3000000 in
/-- **Rational homology form of the old-part identification.** -/
theorem oldPartRelH_iso (D : ℕ) {Γ : Type} [TopologicalSpace Γ] (ι : Type)
    (f : ι → C(Work.RatHurewicz.cellSphere (D-2), Γ)) {X : Type} [TopologicalSpace X]
    (q : C(X, CylZ D Γ ι f))
    (hIncl : Work.Serre.IsRatHomologyIso (oldIncl (D := D) (Γ := Γ) (ι := ι) (f := f) (X := X) q))
    (hInclU : Work.Serre.IsRatHomologyIso
      (oldUIncl (D := D) (Γ := Γ) (ι := ι) (f := f) (X := X) q))
    (k : ℕ) :
    Nonempty (relHR (TopCat.of ↥(cylPairA₂ q)) (oldA q) k ≅
      relHR (TopCat.of (cyl (Work.Serre.restrictFibre q
        (Set.range (Work.RatHurewicz.attachIncl (D-2) Γ ι f)))))
        (Set.range (cylIncl (Work.Serre.restrictFibre q
          (Set.range (Work.RatHurewicz.attachIncl (D-2) Γ ι f))))) k) := by
  classical
  have h1 : IsIso (HomologicalComplex.homologyMap
      (Work.Serre.relChainsRPairMap (oldA q) (oldU₀ q)
        (ContinuousMap.id ↥(cylPairA₂ q)) (oldA_subset_oldU₀ q)) k) :=
    relChainsRPairMap_homologyMap_isIso (oldA q) (oldU₀ q)
      (ContinuousMap.id ↥(cylPairA₂ q)) (oldA_subset_oldU₀ q) k
      (fun j => Work.Serre.IsRatHomologyIso.id ↥(cylPairA₂ q) j)
      (fun j => hIncl j)
  have h2 : IsIso (HomologicalComplex.homologyMap
      (Work.Serre.relChainsRInclPairMap (TopCat.of ↥(cylPairA₂ q)) (cylU₁A₂ q) (cylU₀A₂ q)) k) :=
    Work.Serre.csrExcisionRat (TopCat.of ↥(cylPairA₂ q)) (cylU₁A₂ q) (cylU₀A₂ q)
      ((isOpen_cylU₁ q).preimage continuous_subtype_val)
      ((isOpen_cylU₀ q).preimage continuous_subtype_val)
      (by rw [Set.union_comm]; exact cylU₀A₂_union_cylU₁A₂ q) k
  have h5 : IsIso (HomologicalComplex.homologyMap
      (Work.Serre.relChainsRPairMap (oldUBot q) (oldUU₀ q)
        (ContinuousMap.id ↥(cylPairU q)) (oldUBot_subset_oldUU₀ q)) k) :=
    relChainsRPairMap_homologyMap_isIso (oldUBot q) (oldUU₀ q)
      (ContinuousMap.id ↥(cylPairU q)) (oldUBot_subset_oldUU₀ q) k
      (fun j => Work.Serre.IsRatHomologyIso.id ↥(cylPairU q) j)
      (fun j => hInclU j)
  have h4 : IsIso (HomologicalComplex.homologyMap
      (Work.Serre.relChainsRInclPairMap (TopCat.of ↥(cylPairU q)) (oldU₁U q) (oldUU₀ q)) k) :=
    Work.Serre.csrExcisionRat (TopCat.of ↥(cylPairU q)) (oldU₁U q) (oldUU₀ q)
      ((isOpen_cylU₁ q).preimage continuous_subtype_val)
      ((isOpen_cylU₀ q).preimage continuous_subtype_val)
      (by
        apply Set.eq_univ_of_forall
        intro z
        by_cases h : 0 < (cylLam q z.1 : ℝ)
        · exact Or.inl ((mem_cylU₁_iff q z.1).mpr h)
        · refine Or.inr ((mem_cylU₀_iff q z.1).mpr ?_)
          have h2 : (cylLam q z.1 : ℝ) ≤ 1 := (cylLam q z.1).2.2
          linarith [not_lt.mp h]) k
  set A₃ : Set ↥(cylU₁A₂ q) := {z | (z : ↥(cylPairA₂ q)) ∈ cylU₀A₂ q} with hA₃def
  set B₃ : Set ↥(oldU₁U q) := {w | (w : ↥(cylPairU q)) ∈ oldUU₀ q} with hB₃def
  have hA₃B₃ : Set.MapsTo (⇑(oldU₁Homeo q)) A₃ B₃ :=
    fun z hz => (oldU₁Homeo_mem q z).mp hz
  have h3 : IsIso (HomologicalComplex.homologyMap
      (Work.Serre.relChainsRPairMap A₃ B₃ ⟨oldU₁Homeo q, (oldU₁Homeo q).continuous⟩ hA₃B₃) k) := by
    refine relChainsRPairMap_homologyMap_isIso A₃ B₃
      ⟨oldU₁Homeo q, (oldU₁Homeo q).continuous⟩ hA₃B₃ k
      (fun j => Work.Serre.IsRatHomologyIso.of_homotopyEquiv
        (Homeomorph.toHomotopyEquiv (oldU₁Homeo q)) j) ?_
    intro j
    exact Work.Serre.IsRatHomologyIso.of_homotopyEquiv
      (Homeomorph.toHomotopyEquiv (Homeomorph.subtype (oldU₁Homeo q)
        (fun z => oldU₁Homeo_mem q z))) j
  have hS : IsClosed (Set.range (Work.RatHurewicz.attachIncl (D-2) Γ ι f)) :=
    Work.RatHurewicz.isClosed_range_attachIncl
  obtain ⟨e6, he6⟩ := Work.Serre.cylRestrictHomeo q
    (Set.range (Work.RatHurewicz.attachIncl (D-2) Γ ι f)) hS
  have h6mem : Set.MapsTo (⇑e6)
      (Set.range (cylIncl (Work.Serre.restrictFibre q
        (Set.range (Work.RatHurewicz.attachIncl (D-2) Γ ι f)))))
      (oldUBot q) :=
    fun y hy => (he6 y).mp hy
  have h6 : IsIso (HomologicalComplex.homologyMap
      (Work.Serre.relChainsRPairMap
        (Set.range (cylIncl (Work.Serre.restrictFibre q
          (Set.range (Work.RatHurewicz.attachIncl (D-2) Γ ι f)))))
        (oldUBot q) ⟨e6, e6.continuous⟩ h6mem) k) := by
    refine relChainsRPairMap_homologyMap_isIso _ _ ⟨e6, e6.continuous⟩ h6mem k
      (fun j => Work.Serre.IsRatHomologyIso.of_homotopyEquiv
        (Homeomorph.toHomotopyEquiv e6) j) ?_
    intro j
    exact Work.Serre.IsRatHomologyIso.of_homotopyEquiv
      (Homeomorph.toHomotopyEquiv (Homeomorph.subtype e6 (fun y => he6 y))) j
  letI := h1
  letI := h2
  letI := h3
  letI := h4
  letI := h5
  letI := h6
  exact ⟨asIso (HomologicalComplex.homologyMap (Work.Serre.relChainsRPairMap (oldA q) (oldU₀ q)
      (ContinuousMap.id ↥(cylPairA₂ q)) (oldA_subset_oldU₀ q)) k) ≪≫
    (asIso (HomologicalComplex.homologyMap
      (Work.Serre.relChainsRInclPairMap (TopCat.of ↥(cylPairA₂ q)) (cylU₁A₂ q)
        (cylU₀A₂ q)) k)).symm ≪≫
    asIso (HomologicalComplex.homologyMap
      (Work.Serre.relChainsRPairMap A₃ B₃ ⟨oldU₁Homeo q, (oldU₁Homeo q).continuous⟩ hA₃B₃) k) ≪≫
    asIso (HomologicalComplex.homologyMap
      (Work.Serre.relChainsRInclPairMap (TopCat.of ↥(cylPairU q)) (oldU₁U q) (oldUU₀ q)) k) ≪≫
    (asIso (HomologicalComplex.homologyMap (Work.Serre.relChainsRPairMap (oldUBot q) (oldUU₀ q)
      (ContinuousMap.id ↥(cylPairU q)) (oldUBot_subset_oldUU₀ q)) k)).symm ≪≫
    (asIso (HomologicalComplex.homologyMap
      (Work.Serre.relChainsRPairMap
        (Set.range (cylIncl (Work.Serre.restrictFibre q
          (Set.range (Work.RatHurewicz.attachIncl (D-2) Γ ι f)))))
        (oldUBot q) ⟨e6, e6.continuous⟩ h6mem) k)).symm⟩

/-! ## The cohomological statement -/

/-- **The old-part identification, cohomological form, from the two collar facts.** -/
theorem oldPartRelCohIso_of_collar (D : ℕ) (hD : 2 ≤ D) {Γ : Type} [TopologicalSpace Γ]
    (ι : Type) (f : ι → C(Work.RatHurewicz.cellSphere (D-2), Γ)) {X : Type} [TopologicalSpace X]
    (q : C(X, Work.RatHurewicz.attachCells (D-2) Γ ι f))
    (hIncl : Work.Serre.IsRatHomologyIso (oldIncl (D := D) (Γ := Γ) (ι := ι) (f := f) (X := X) q))
    (hInclU : Work.Serre.IsRatHomologyIso
      (oldUIncl (D := D) (Γ := Γ) (ι := ι) (f := f) (X := X) q))
    (k : ℕ) :
    Nonempty (CategoryTheory.Iso
      (Work.Thom.RelCoh ℚ k
        ↥((Work.Serre.cylRetract q) ⁻¹' Set.range (Work.RatHurewicz.attachIncl (D-2) Γ ι f)
          ∪ Set.range (Work.Serre.cylIncl q))
        {x | (x : Work.Serre.cyl q) ∈ Set.range (Work.Serre.cylIncl q)})
      (Work.Thom.RelCoh ℚ k
        (Work.Serre.cyl (Work.Serre.restrictFibre q
          (Set.range (Work.RatHurewicz.attachIncl (D-2) Γ ι f))))
        (Set.range (Work.Serre.cylIncl (Work.Serre.restrictFibre q
          (Set.range (Work.RatHurewicz.attachIncl (D-2) Γ ι f))))))) := by
  obtain ⟨eH⟩ := oldPartRelH_iso D ι f q hIncl hInclU k
  obtain ⟨e₁, _⟩ := Work.Serre.relKronEquiv (TopCat.of ↥(cylPairA₂ q)) (oldA q) k
  obtain ⟨e₂, _⟩ := Work.Serre.relKronEquiv (TopCat.of (cyl (Work.Serre.restrictFibre q
      (Set.range (Work.RatHurewicz.attachIncl (D-2) Γ ι f)))))
      (Set.range (cylIncl (Work.Serre.restrictFibre q
        (Set.range (Work.RatHurewicz.attachIncl (D-2) Γ ι f))))) k
  exact ⟨LinearEquiv.toModuleIso e₁ ≪≫
    (LinearEquiv.dualMap eH.toLinearEquiv).symm.toModuleIso ≪≫
    (LinearEquiv.toModuleIso e₂).symm⟩

theorem oldPartRelCohIso (D : ℕ) (hD : 2 ≤ D) {Γ : Type} [TopologicalSpace Γ] (ι : Type)
    (f : ι → C(Work.RatHurewicz.cellSphere (D-2), Γ)) {X : Type} [TopologicalSpace X]
    (q : C(X, Work.RatHurewicz.attachCells (D-2) Γ ι f)) (k : ℕ) :
    Nonempty (CategoryTheory.Iso
      (Work.Thom.RelCoh ℚ k
        ↥((Work.Serre.cylRetract q) ⁻¹' Set.range (Work.RatHurewicz.attachIncl (D-2) Γ ι f)
          ∪ Set.range (Work.Serre.cylIncl q))
        {x | (x : Work.Serre.cyl q) ∈ Set.range (Work.Serre.cylIncl q)})
      (Work.Thom.RelCoh ℚ k
        (Work.Serre.cyl (Work.Serre.restrictFibre q
          (Set.range (Work.RatHurewicz.attachIncl (D-2) Γ ι f))))
        (Set.range (Work.Serre.cylIncl (Work.Serre.restrictFibre q
          (Set.range (Work.RatHurewicz.attachIncl (D-2) Γ ι f))))))) :=
  oldPartRelCohIso_of_collar D hD ι f q
    (Work.Serre.DiscPair.oldPartCollarIncl D ι f q)
    (Work.Serre.DiscPair.oldPartCollarInclU D ι f q) k

end

end Work.Serre.DiscPair
