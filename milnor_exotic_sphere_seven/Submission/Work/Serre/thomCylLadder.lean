import Mathlib
import Submission.Work.Serre.ThomCylDefs
import Submission.Work.Serre.CWModel.Tower
import Submission.Work.Serre.DiscPair.isIso_relCohMap_incl_of_isZero
import Submission.Work.Serre.DiscPair.oldPartRelCohIso
import Submission.Work.Serre.discPairCellVanishing
import Submission.Work.Serre.attachRelCohVanishingHigh

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The five-lemma ladder of the cellular step (`Work.Serre.thomCylCellStepAlt`)

This module assembles the proof of the cellular step of the CW-model Thom case: the two long exact
sequences (the pair `(Γ', S)` of the attachment and the triple `A ⊆ new ⊆ M` of the mapping cylinder
of `q`), the vertical maps (the target cup map `TP`, the old-part cup map `TQ` and the cell
comparison `TM`) and the five-lemma application giving `Work.Serre.ThomCylAt r N q`.

The two rows and their exactness are set up below (`baseF/G/D`, `totF/G/D`).
-/

open CategoryTheory CategoryTheory.Limits

namespace Work.Serre

noncomputable section

set_option maxHeartbeats 1600000

/-! ## The two long exact sequences of the cellular step -/

/-- The old part of the base, pulled back to the mapping cylinder. -/
def ladOld (D : ℕ) {Γ : Type} [TopologicalSpace Γ] (ι : Type)
    (f : ι → C(Work.RatHurewicz.cellSphere (D-2), Γ)) {X : Type} [TopologicalSpace X]
    (q : C(X, Work.RatHurewicz.attachCells (D-2) Γ ι f)) : Set (Work.Serre.cyl q) :=
  (Work.Serre.cylRetract q) ⁻¹' Set.range (Work.RatHurewicz.attachIncl (D-2) Γ ι f)

/-- The old part together with the new spheres. -/
def ladNew (D : ℕ) {Γ : Type} [TopologicalSpace Γ] (ι : Type)
    (f : ι → C(Work.RatHurewicz.cellSphere (D-2), Γ)) {X : Type} [TopologicalSpace X]
    (q : C(X, Work.RatHurewicz.attachCells (D-2) Γ ι f)) : Set (Work.Serre.cyl q) :=
  ladOld D ι f q ∪ Set.range (Work.Serre.cylIncl q)

/-- `A ⊆ new`, the hypothesis of the triple sequence. -/
theorem subA_new (D : ℕ) {Γ : Type} [TopologicalSpace Γ] (ι : Type)
    (f : ι → C(Work.RatHurewicz.cellSphere (D-2), Γ)) {X : Type} [TopologicalSpace X]
    (q : C(X, Work.RatHurewicz.attachCells (D-2) Γ ι f)) :
    Set.range (Work.Serre.cylIncl q) ⊆ ladNew D ι f q :=
  fun x hx => Or.inr hx

/-! ## The base pair sequence of `(Γ', S)` -/

/-- The set `S = range (attachIncl …)`. -/
def ladS (D : ℕ) (Γ : Type) [TopologicalSpace Γ] (ι : Type)
    (f : ι → C(Work.RatHurewicz.cellSphere (D-2), Γ)) :
    Set (Work.RatHurewicz.attachCells (D-2) Γ ι f) :=
  Set.range (Work.RatHurewicz.attachIncl (D-2) Γ ι f)

/-- The first map of the base sequence, `H^k(Γ',S) ⟶ H^k(Γ')`. -/
def baseF (D : ℕ) (Γ : Type) [TopologicalSpace Γ] (ι : Type)
    (f : ι → C(Work.RatHurewicz.cellSphere (D-2), Γ)) (k : ℕ) :
    Work.Thom.RelCoh ℚ k (Work.RatHurewicz.attachCells (D-2) Γ ι f) (ladS D Γ ι f) ⟶
      Work.Thom.Coh ℚ k (Work.RatHurewicz.attachCells (D-2) Γ ι f) :=
  HomologicalComplex.homologyMap
    (Work.Cohomology.relIncl ℚ (TopCat.of (Work.RatHurewicz.attachCells (D-2) Γ ι f))
      (ladS D Γ ι f)) k

/-- The second map of the base sequence, `H^k(Γ') ⟶ H^k(S)`. -/
def baseG (D : ℕ) (Γ : Type) [TopologicalSpace Γ] (ι : Type)
    (f : ι → C(Work.RatHurewicz.cellSphere (D-2), Γ)) (k : ℕ) :
    Work.Thom.Coh ℚ k (Work.RatHurewicz.attachCells (D-2) Γ ι f) ⟶
      Work.Thom.Coh ℚ k ↥(ladS D Γ ι f) :=
  HomologicalComplex.homologyMap
    (Work.Cohomology.restr ℚ (TopCat.of (Work.RatHurewicz.attachCells (D-2) Γ ι f))
      (ladS D Γ ι f)) k

/-- The connecting map of the base sequence, `H^k(S) ⟶ H^{k+1}(Γ',S)`. -/
def baseD (D : ℕ) (Γ : Type) [TopologicalSpace Γ] (ι : Type)
    (f : ι → C(Work.RatHurewicz.cellSphere (D-2), Γ)) (k : ℕ) :
    Work.Thom.Coh ℚ k ↥(ladS D Γ ι f) ⟶
      Work.Thom.RelCoh ℚ (k+1) (Work.RatHurewicz.attachCells (D-2) Γ ι f) (ladS D Γ ι f) :=
  Work.Cohomology.pairδ ℚ (TopCat.of (Work.RatHurewicz.attachCells (D-2) Γ ι f))
    (ladS D Γ ι f) k

theorem baseExact₂ (D : ℕ) (Γ : Type) [TopologicalSpace Γ] (ι : Type)
    (f : ι → C(Work.RatHurewicz.cellSphere (D-2), Γ)) (k : ℕ) :
    LinearMap.range (ModuleCat.Hom.hom (baseF D Γ ι f k))
      = LinearMap.ker (ModuleCat.Hom.hom (baseG D Γ ι f k)) :=
  (Work.Cohomology.pair_exact₂ ℚ (TopCat.of (Work.RatHurewicz.attachCells (D-2) Γ ι f))
    (ladS D Γ ι f) k).moduleCat_range_eq_ker

theorem baseExact₃ (D : ℕ) (Γ : Type) [TopologicalSpace Γ] (ι : Type)
    (f : ι → C(Work.RatHurewicz.cellSphere (D-2), Γ)) (k : ℕ) :
    LinearMap.range (ModuleCat.Hom.hom (baseG D Γ ι f k))
      = LinearMap.ker (ModuleCat.Hom.hom (baseD D Γ ι f k)) :=
  (Work.Cohomology.pair_exact₃ ℚ (TopCat.of (Work.RatHurewicz.attachCells (D-2) Γ ι f))
    (ladS D Γ ι f) k).moduleCat_range_eq_ker

theorem baseExact₁ (D : ℕ) (Γ : Type) [TopologicalSpace Γ] (ι : Type)
    (f : ι → C(Work.RatHurewicz.cellSphere (D-2), Γ)) (k : ℕ) :
    LinearMap.range (ModuleCat.Hom.hom (baseD D Γ ι f k))
      = LinearMap.ker (ModuleCat.Hom.hom (baseF D Γ ι f (k+1))) :=
  (Work.Cohomology.pair_exact₁ ℚ (TopCat.of (Work.RatHurewicz.attachCells (D-2) Γ ι f))
    (ladS D Γ ι f) k).moduleCat_range_eq_ker

/-! ## The total triple sequence of `A ⊆ new ⊆ M` -/

/-- The first map of the total sequence, `H^k(M,new) ⟶ H^k(M,A)`. -/
def totF (D : ℕ) {Γ : Type} [TopologicalSpace Γ] (ι : Type)
    (f : ι → C(Work.RatHurewicz.cellSphere (D-2), Γ)) {X : Type} [TopologicalSpace X]
    (q : C(X, Work.RatHurewicz.attachCells (D-2) Γ ι f)) (k : ℕ) :
    Work.Thom.RelCoh ℚ k (Work.Serre.cyl q) (ladNew D ι f q) ⟶
      Work.Thom.RelCoh ℚ k (Work.Serre.cyl q) (Set.range (Work.Serre.cylIncl q)) :=
  HomologicalComplex.homologyMap
    (Work.Serre.DiscPair.qTripleF (TopCat.of (Work.Serre.cyl q))
      (Set.range (Work.Serre.cylIncl q)) (ladNew D ι f q) (subA_new D ι f q)) k

/-- The second map of the total sequence, `H^k(M,A) ⟶ H^k(new,A)`. -/
def totG (D : ℕ) {Γ : Type} [TopologicalSpace Γ] (ι : Type)
    (f : ι → C(Work.RatHurewicz.cellSphere (D-2), Γ)) {X : Type} [TopologicalSpace X]
    (q : C(X, Work.RatHurewicz.attachCells (D-2) Γ ι f)) (k : ℕ) :
    Work.Thom.RelCoh ℚ k (Work.Serre.cyl q) (Set.range (Work.Serre.cylIncl q)) ⟶
      Work.Thom.RelCoh ℚ k ↥(ladNew D ι f q)
        {x | (x : Work.Serre.cyl q) ∈ Set.range (Work.Serre.cylIncl q)} :=
  HomologicalComplex.homologyMap
    (Work.Serre.DiscPair.qTripleG (TopCat.of (Work.Serre.cyl q))
      (Set.range (Work.Serre.cylIncl q)) (ladNew D ι f q) (subA_new D ι f q)) k

/-- The connecting map of the total sequence. -/
def totD (D : ℕ) {Γ : Type} [TopologicalSpace Γ] (ι : Type)
    (f : ι → C(Work.RatHurewicz.cellSphere (D-2), Γ)) {X : Type} [TopologicalSpace X]
    (q : C(X, Work.RatHurewicz.attachCells (D-2) Γ ι f)) (k : ℕ) :
    Work.Thom.RelCoh ℚ k ↥(ladNew D ι f q)
        {x | (x : Work.Serre.cyl q) ∈ Set.range (Work.Serre.cylIncl q)} ⟶
      Work.Thom.RelCoh ℚ (k+1) (Work.Serre.cyl q) (ladNew D ι f q) :=
  (Work.Serre.DiscPair.qTripleShort_shortExact (TopCat.of (Work.Serre.cyl q))
    (Set.range (Work.Serre.cylIncl q)) (ladNew D ι f q) (subA_new D ι f q)).δ k (k+1)
      (by simp [ComplexShape.up])

theorem totExact₂ (D : ℕ) {Γ : Type} [TopologicalSpace Γ] (ι : Type)
    (f : ι → C(Work.RatHurewicz.cellSphere (D-2), Γ)) {X : Type} [TopologicalSpace X]
    (q : C(X, Work.RatHurewicz.attachCells (D-2) Γ ι f)) (k : ℕ) :
    LinearMap.range (ModuleCat.Hom.hom (totF D ι f q k))
      = LinearMap.ker (ModuleCat.Hom.hom (totG D ι f q k)) :=
  (Work.Serre.DiscPair.qTripleShort_shortExact (TopCat.of (Work.Serre.cyl q))
    (Set.range (Work.Serre.cylIncl q)) (ladNew D ι f q) (subA_new D ι f q)
    ).homology_exact₂ k |>.moduleCat_range_eq_ker

theorem totExact₃ (D : ℕ) {Γ : Type} [TopologicalSpace Γ] (ι : Type)
    (f : ι → C(Work.RatHurewicz.cellSphere (D-2), Γ)) {X : Type} [TopologicalSpace X]
    (q : C(X, Work.RatHurewicz.attachCells (D-2) Γ ι f)) (k : ℕ) :
    LinearMap.range (ModuleCat.Hom.hom (totG D ι f q k))
      = LinearMap.ker (ModuleCat.Hom.hom (totD D ι f q k)) :=
  (Work.Serre.DiscPair.qTripleShort_shortExact (TopCat.of (Work.Serre.cyl q))
    (Set.range (Work.Serre.cylIncl q)) (ladNew D ι f q) (subA_new D ι f q)
    ).homology_exact₃ k (k+1) (by simp [ComplexShape.up]) |>.moduleCat_range_eq_ker

theorem totExact₁ (D : ℕ) {Γ : Type} [TopologicalSpace Γ] (ι : Type)
    (f : ι → C(Work.RatHurewicz.cellSphere (D-2), Γ)) {X : Type} [TopologicalSpace X]
    (q : C(X, Work.RatHurewicz.attachCells (D-2) Γ ι f)) (k : ℕ) :
    LinearMap.range (ModuleCat.Hom.hom (totD D ι f q k))
      = LinearMap.ker (ModuleCat.Hom.hom (totF D ι f q (k+1))) :=
  (Work.Serre.DiscPair.qTripleShort_shortExact (TopCat.of (Work.Serre.cyl q))
    (Set.range (Work.Serre.cylIncl q)) (ladNew D ι f q) (subA_new D ι f q)
    ).homology_exact₁ k (k+1) (by simp [ComplexShape.up]) |>.moduleCat_range_eq_ker

end

end Work.Serre
