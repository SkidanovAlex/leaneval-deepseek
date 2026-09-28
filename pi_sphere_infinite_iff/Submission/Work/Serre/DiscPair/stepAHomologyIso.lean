import Mathlib
import Submission.Work.Serre.DiscPair.collarDefs
import Submission.Work.Serre.DiscPair.relPairFiveRat

namespace Work.Serre.DiscPair

open CategoryTheory CategoryTheory.Limits
open scoped Topology unitInterval


noncomputable section

/-!
## Step A of the disc-pair comparison

The relative pair map `(A₂, A₂ ∩ U₁) → (A₂, U)` (identity on `A₂`, inclusion on the relative part)
induced by the collar decomposition of the mapping cylinder.  The relative part `A₂ ∩ U₁` is a
homotopy equivalence onto `U`, with homotopy inverse `y ↦ cylMove q (y,1)` (the push-up of the
mapping cylinder, whose image lies in `range (cylInr q) ⊆ U ∩ U₁`), homotopic to the identity
through `s ↦ cylMove q (y, 1-s)` (which preserves both `U` and `U₁ = {λ > 0}`).  The five lemma for
maps of pairs (`Work.Serre.DiscPair.relChainsRPairMap_homologyMap_isIso`), applied with the
identity on `A₂`, then turns this into the rational homology isomorphism of the statement.
-/

/-- `λ (cylMove q (y,1)) = 1 > 0`: the push-up of the mapping cylinder lands in `U₁ = {λ > 0}`. -/
theorem stepA_cylMove_one_mem_cylU₁ {D : ℕ} {Γ : Type} [TopologicalSpace Γ] {ι : Type}
    {f : ι → C(Work.RatHurewicz.cellSphere (D-2), Γ)} {X : Type} [TopologicalSpace X]
    (q : C(X, CylZ D Γ ι f)) (y : cyl q) :
    Work.Serre.cylMove q (y, 1) ∈ cylU₁ (D := D) (Γ := Γ) (ι := ι) (f := f) q := by
  rw [mem_cylU₁_iff, cylLam_cylMove, unitIntervalLin_one_left]
  norm_num

/-- The push-up of the mapping cylinder, as a map `U → A₂ ∩ U₁` (with `U = cylPairUinA₂`). -/
def stepAPush (D : ℕ) (Γ : Type) [TopologicalSpace Γ] (ι : Type)
    (f : ι → C(Work.RatHurewicz.cellSphere (D-2), Γ)) {X : Type} [TopologicalSpace X]
    (q : C(X, CylZ D Γ ι f)) :
    C(↥(cylPairUinA₂ (D := D) (Γ := Γ) (ι := ι) (f := f) q),
      ↥(cylU₁A₂ (D := D) (Γ := Γ) (ι := ι) (f := f) q)) where
  toFun y := ⟨⟨Work.Serre.cylMove q (y.1.1, 1),
      Or.inl (cylMove_mem_cylPairU (D := D) (Γ := Γ) (ι := ι) (f := f) q y.2 1)⟩,
    stepA_cylMove_one_mem_cylU₁ (D := D) (Γ := Γ) (ι := ι) (f := f) q y.1.1⟩
  continuous_toFun := by fun_prop

/-- The homotopy `cylMove q (·, 1-s)` on `A₂ ∩ U₁`, contracting the push-up to the identity. -/
def stepAHomA (D : ℕ) (Γ : Type) [TopologicalSpace Γ] (ι : Type)
    (f : ι → C(Work.RatHurewicz.cellSphere (D-2), Γ)) {X : Type} [TopologicalSpace X]
    (q : C(X, CylZ D Γ ι f)) :
    C(unitInterval × ↥(cylU₁A₂ (D := D) (Γ := Γ) (ι := ι) (f := f) q),
      ↥(cylU₁A₂ (D := D) (Γ := Γ) (ι := ι) (f := f) q)) where
  toFun p := ⟨⟨Work.Serre.cylMove q (p.2.1.1, Work.Serre.unitIntervalOneSub p.1),
      Or.inl (cylMove_mem_cylPairU (D := D) (Γ := Γ) (ι := ι) (f := f) q
        (cylU₁_inter_cylPairA₂_subset (D := D) (Γ := Γ) (ι := ι) (f := f) q
          ⟨p.2.2, p.2.1.2⟩) (Work.Serre.unitIntervalOneSub p.1))⟩,
    cylMove_mem_cylU₁ (D := D) (Γ := Γ) (ι := ι) (f := f) q p.2.2
      (Work.Serre.unitIntervalOneSub p.1)⟩
  continuous_toFun := by
    have hcm : Continuous (Work.Serre.cylMove q) := (cylMove q).continuous
    have hu : Continuous (Work.Serre.unitIntervalOneSub) :=
      Work.Serre.continuous_unitIntervalOneSub
    fun_prop

/-- The homotopy `cylMove q (·, 1-s)` on `U = cylPairUinA₂`, contracting the push-up to the
identity. -/
def stepAHomB (D : ℕ) (Γ : Type) [TopologicalSpace Γ] (ι : Type)
    (f : ι → C(Work.RatHurewicz.cellSphere (D-2), Γ)) {X : Type} [TopologicalSpace X]
    (q : C(X, CylZ D Γ ι f)) :
    C(unitInterval × ↥(cylPairUinA₂ (D := D) (Γ := Γ) (ι := ι) (f := f) q),
      ↥(cylPairUinA₂ (D := D) (Γ := Γ) (ι := ι) (f := f) q)) where
  toFun p := ⟨⟨Work.Serre.cylMove q (p.2.1.1, Work.Serre.unitIntervalOneSub p.1),
      Or.inl (cylMove_mem_cylPairU (D := D) (Γ := Γ) (ι := ι) (f := f) q p.2.2
        (Work.Serre.unitIntervalOneSub p.1))⟩,
    cylMove_mem_cylPairU (D := D) (Γ := Γ) (ι := ι) (f := f) q p.2.2
      (Work.Serre.unitIntervalOneSub p.1)⟩
  continuous_toFun := by
    have hcm : Continuous (Work.Serre.cylMove q) := (cylMove q).continuous
    have hu : Continuous (Work.Serre.unitIntervalOneSub) :=
      Work.Serre.continuous_unitIntervalOneSub
    fun_prop

/-- **`A₂ ∩ U₁ ⊆ U` is a homotopy equivalence** (the inclusion, with inverse the push-up
`cylmove q (·,1)`), hence a rational homology isomorphism. -/
def stepAHomotopyEquiv (D : ℕ) (Γ : Type) [TopologicalSpace Γ] (ι : Type)
    (f : ι → C(Work.RatHurewicz.cellSphere (D-2), Γ)) {X : Type} [TopologicalSpace X]
    (q : C(X, CylZ D Γ ι f))
    (hsub : Set.MapsTo (⇑(ContinuousMap.id ↥(cylPairA₂ (D := D) (Γ := Γ) (ι := ι) (f := f) q)))
      (cylU₁A₂ (D := D) (Γ := Γ) (ι := ι) (f := f) q)
      (cylPairUinA₂ (D := D) (Γ := Γ) (ι := ι) (f := f) q)) :
    ContinuousMap.HomotopyEquiv
      ↥(cylU₁A₂ (D := D) (Γ := Γ) (ι := ι) (f := f) q)
      ↥(cylPairUinA₂ (D := D) (Γ := Γ) (ι := ι) (f := f) q) := by
  refine ContinuousMap.HomotopyEquiv.mk
    (restrictPair (cylU₁A₂ (D := D) (Γ := Γ) (ι := ι) (f := f) q)
      (cylPairUinA₂ (D := D) (Γ := Γ) (ι := ι) (f := f) q)
      (ContinuousMap.id ↥(cylPairA₂ (D := D) (Γ := Γ) (ι := ι) (f := f) q)) hsub)
    (stepAPush D Γ ι f q) ?_ ?_
  · refine ⟨ContinuousMap.Homotopy.mk (stepAHomA D Γ ι f q) ?_ ?_⟩
    · intro x
      apply Subtype.ext; apply Subtype.ext
      simp [stepAHomA, stepAPush, restrictPair_coe]
    · intro x
      apply Subtype.ext; apply Subtype.ext
      simp [stepAHomA]
  · refine ⟨ContinuousMap.Homotopy.mk (stepAHomB D Γ ι f q) ?_ ?_⟩
    · intro y
      apply Subtype.ext; apply Subtype.ext
      simp [stepAHomB, stepAPush, restrictPair_coe]
    · intro y
      apply Subtype.ext; apply Subtype.ext
      simp [stepAHomB]

/-- **Step A of the disc-pair comparison.**  The map of relative chain complexes
`C_*(A₂, A₂ ∩ U₁) → C_*(A₂, U)` induced by the identity on `A₂` and the inclusion
`A₂ ∩ U₁ ↪ U` is a rational homology isomorphism: `A₂ ∩ U₁ ⊆ U` is a homotopy equivalence,
because `cylMove q` preserves `{λ > 0}` and at time `1` maps `U` into
`S' = range (cylInr q) ⊆ A₂ ∩ U₁`. -/
theorem stepAHomologyIso (D : ℕ) (Γ : Type) [TopologicalSpace Γ] (ι : Type)
    (f : ι → C(Work.RatHurewicz.cellSphere (D-2), Γ)) {X : Type} [TopologicalSpace X]
    (q : C(X, Work.RatHurewicz.attachCells (D-2) Γ ι f))
    (hsub : Set.MapsTo (⇑(ContinuousMap.id ↥(cylPairA₂ (D := D) (Γ := Γ) (ι := ι) (f := f) q)))
      (cylU₁A₂ (D := D) (Γ := Γ) (ι := ι) (f := f) q)
      (cylPairUinA₂ (D := D) (Γ := Γ) (ι := ι) (f := f) q)) (m : ℕ) :
    CategoryTheory.IsIso (HomologicalComplex.homologyMap
      (Work.Serre.relChainsRPairMap
        (cylU₁A₂ (D := D) (Γ := Γ) (ι := ι) (f := f) q)
        (cylPairUinA₂ (D := D) (Γ := Γ) (ι := ι) (f := f) q)
        (ContinuousMap.id ↥(cylPairA₂ (D := D) (Γ := Γ) (ι := ι) (f := f) q)) hsub) m) := by
  refine relChainsRPairMap_homologyMap_isIso
    (cylU₁A₂ (D := D) (Γ := Γ) (ι := ι) (f := f) q)
    (cylPairUinA₂ (D := D) (Γ := Γ) (ι := ι) (f := f) q)
    (ContinuousMap.id ↥(cylPairA₂ (D := D) (Γ := Γ) (ι := ι) (f := f) q)) hsub m ?_ ?_
  · intro k
    exact Work.Serre.IsRatHomologyIso.id ↥(cylPairA₂ (D := D) (Γ := Γ) (ι := ι) (f := f) q) k
  · intro k
    exact Work.Serre.IsRatHomologyIso.of_homotopyEquiv
      (stepAHomotopyEquiv D Γ ι f q hsub) k

end

/-! ## Backwards-compatible alias

`Work.Serre.DiscPair.subPairMapQuasiIso` refers to this lemma under the doubly nested name
`Work.Serre.DiscPair.Work.Serre.DiscPair.stepAHomologyIso` (the file was written with the namespace
`Work.Serre.DiscPair` twice); we keep that spelling available. -/

namespace Work.Serre.DiscPair

/-- **Step A of the disc-pair comparison**, under the doubly nested name used by
`Work.Serre.DiscPair.subPairMapQuasiIso`. -/
theorem stepAHomologyIso (D : ℕ) (Γ : Type) [TopologicalSpace Γ] (ι : Type)
    (f : ι → C(Work.RatHurewicz.cellSphere (D-2), Γ)) {X : Type} [TopologicalSpace X]
    (q : C(X, Work.RatHurewicz.attachCells (D-2) Γ ι f))
    (hsub : Set.MapsTo (⇑(ContinuousMap.id ↥(cylPairA₂ (D := D) (Γ := Γ) (ι := ι) (f := f) q)))
      (cylU₁A₂ (D := D) (Γ := Γ) (ι := ι) (f := f) q)
      (cylPairUinA₂ (D := D) (Γ := Γ) (ι := ι) (f := f) q)) (m : ℕ) :
    CategoryTheory.IsIso (HomologicalComplex.homologyMap
      (Work.Serre.relChainsRPairMap
        (cylU₁A₂ (D := D) (Γ := Γ) (ι := ι) (f := f) q)
        (cylPairUinA₂ (D := D) (Γ := Γ) (ι := ι) (f := f) q)
        (ContinuousMap.id ↥(cylPairA₂ (D := D) (Γ := Γ) (ι := ι) (f := f) q)) hsub) m) :=
  _root_.Work.Serre.DiscPair.stepAHomologyIso D Γ ι f q hsub m

end Work.Serre.DiscPair

end Work.Serre.DiscPair
