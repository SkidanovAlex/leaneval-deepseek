import Mathlib
import Submission.Work.Serre.C1Cyl
import Submission.Work.Serre.csrDefs
import Submission.Work.RatHurewicz.AttachCells
import Submission.Work.StemsB.Fibrations
import Submission.Work.StemsB.RelChainsR

/-!
# The pair of the mapping cylinder of a map to a CW-type attachment

Vocabulary file for `Work.Serre.DiscPair.cylPairCofibre`.
-/

open CategoryTheory CategoryTheory.Limits
open scoped Topology unitInterval

namespace Work.Serre.DiscPair

noncomputable section

variable {D : ℕ} {Γ : Type} [TopologicalSpace Γ] {ι : Type}
  {f : ι → C(Work.RatHurewicz.cellSphere (D-2), Γ)} {X : Type} [TopologicalSpace X]

/-- The old part `Y' = range (attachIncl (D-2) Γ ι f) ⊆ attachCells (D-2) Γ ι f`. -/
def cylPairS : Set (Work.RatHurewicz.attachCells (D-2) Γ ι f) :=
  Set.range (Work.RatHurewicz.attachIncl (D-2) Γ ι f)

/-- `A = q ⁻¹' Y' ⊆ X`. -/
abbrev cylPairA (q : C(X, Work.RatHurewicz.attachCells (D-2) Γ ι f)) : Set X :=
  q ⁻¹' cylPairS (D := D) (Γ := Γ) (ι := ι) (f := f)

/-- `U = (cylRetract q) ⁻¹' Y' ⊆ cyl q`: the mapping cylinder of the restriction `q|_A`. -/
abbrev cylPairU (q : C(X, Work.RatHurewicz.attachCells (D-2) Γ ι f)) : Set (cyl q) :=
  (cylRetract q) ⁻¹' cylPairS (D := D) (Γ := Γ) (ι := ι) (f := f)

/-- The bottom copy `range (cylIncl q) ⊆ cyl q`. -/
abbrev cylPairBot (q : C(X, Work.RatHurewicz.attachCells (D-2) Γ ι f)) : Set (cyl q) :=
  Set.range (cylIncl q)

/-- `A₂ = U ∪ range (cylIncl q)`, the pair of the target statement. -/
abbrev cylPairA₂ (q : C(X, Work.RatHurewicz.attachCells (D-2) Γ ι f)) : Set (cyl q) :=
  cylPairU (D := D) (Γ := Γ) (ι := ι) (f := f) q ∪ cylPairBot (D := D) (Γ := Γ) (ι := ι) q

/-- `U` as a subset of `A₂` (in the subtype). -/
abbrev cylPairUinA₂ (q : C(X, Work.RatHurewicz.attachCells (D-2) Γ ι f)) :
    Set ↥(cylPairA₂ (D := D) (Γ := Γ) (ι := ι) (f := f) q) :=
  {x | (x : cyl q) ∈ cylPairU (D := D) (Γ := Γ) (ι := ι) (f := f) q}

/-- The inclusion `U ⊆ A₂`. -/
def cylPairUincl (q : C(X, Work.RatHurewicz.attachCells (D-2) Γ ι f)) :
    C(↥(cylPairU (D := D) (Γ := Γ) (ι := ι) (f := f) q),
      ↥(cylPairA₂ (D := D) (Γ := Γ) (ι := ι) (f := f) q)) where
  toFun x := ⟨x.1, Or.inl x.2⟩
  continuous_toFun := Continuous.subtype_mk
    (f := fun x : ↥(cylPairU (D := D) (Γ := Γ) (ι := ι) (f := f) q) => (x.1 : cyl q))
    continuous_subtype_val (fun x => Or.inl x.2)

/-- The inclusion `A₂ ⊆ C`. -/
def cylPairA₂sub (q : C(X, Work.RatHurewicz.attachCells (D-2) Γ ι f)) :
    C(↥(cylPairA₂ (D := D) (Γ := Γ) (ι := ι) (f := f) q), cyl q) where
  toFun x := x.1
  continuous_toFun := continuous_subtype_val

/-- The inclusion `U ⊆ C`. -/
def cylPairUsub (q : C(X, Work.RatHurewicz.attachCells (D-2) Γ ι f)) :
    C(↥(cylPairU (D := D) (Γ := Γ) (ι := ι) (f := f) q), cyl q) where
  toFun x := x.1
  continuous_toFun := continuous_subtype_val

/-- `cylIncl q` viewed as a map into `A₂` (its image is the bottom copy). -/
def cylInclA₂ (q : C(X, Work.RatHurewicz.attachCells (D-2) Γ ι f)) :
    C(X, ↥(cylPairA₂ (D := D) (Γ := Γ) (ι := ι) (f := f) q)) where
  toFun x := ⟨cylIncl q x, Or.inr ⟨x, rfl⟩⟩
  continuous_toFun := Continuous.subtype_mk
    (f := fun x : X => cylIncl q x) ((cylIncl q).continuous) (fun x => Or.inr ⟨x, rfl⟩)

/-- `cylIncl q` viewed as a map `A → U` (for `q x ∈ Y'` the point `cylIncl q x` lies in `U`). -/
def cylInclU (q : C(X, Work.RatHurewicz.attachCells (D-2) Γ ι f)) :
    C(↥(cylPairA (D := D) (Γ := Γ) (ι := ι) (f := f) (X := X) q),
      ↥(cylPairU (D := D) (Γ := Γ) (ι := ι) (f := f) (X := X) q)) where
  toFun x := ⟨cylIncl q x.1, x.2⟩
  continuous_toFun := Continuous.subtype_mk
    (f := fun x : ↥(cylPairA (D := D) (Γ := Γ) (ι := ι) (f := f) (X := X) q) =>
      cylIncl q x.1)
    ((cylIncl q).continuous.comp continuous_subtype_val) (fun x => x.2)

/-- `cylIncl q` viewed as a map `A → A₂`. -/
def cylInclAA₂ (q : C(X, Work.RatHurewicz.attachCells (D-2) Γ ι f)) :
    C(↥(cylPairA (D := D) (Γ := Γ) (ι := ι) (f := f) (X := X) q),
      ↥(cylPairA₂ (D := D) (Γ := Γ) (ι := ι) (f := f) q)) where
  toFun x := ⟨cylIncl q x.1, Or.inl x.2⟩
  continuous_toFun := Continuous.subtype_mk
    (f := fun x : ↥(cylPairA (D := D) (Γ := Γ) (ι := ι) (f := f) (X := X) q) =>
      cylIncl q x.1)
    ((cylIncl q).continuous.comp continuous_subtype_val) (fun x => Or.inl x.2)

@[simp] lemma cylInclA₂_coe (q : C(X, Work.RatHurewicz.attachCells (D-2) Γ ι f)) (x : X) :
    ((cylInclA₂ (D := D) (Γ := Γ) (ι := ι) (f := f) q) x : cyl q) = cylIncl q x := rfl

@[simp] lemma cylPairUincl_coe (q : C(X, Work.RatHurewicz.attachCells (D-2) Γ ι f))
    (x : ↥(cylPairU (D := D) (Γ := Γ) (ι := ι) (f := f) q)) :
    ((cylPairUincl (D := D) (Γ := Γ) (ι := ι) (f := f) q) x : cyl q) = x.1 := rfl

@[simp] lemma cylInclU_coe (q : C(X, Work.RatHurewicz.attachCells (D-2) Γ ι f))
    (x : ↥(cylPairA (D := D) (Γ := Γ) (ι := ι) (f := f) (X := X) q)) :
    ((cylInclU (D := D) (Γ := Γ) (ι := ι) (f := f) q) x : cyl q) = cylIncl q x.1 := rfl

lemma mapsTo_cylInclA₂ (q : C(X, Work.RatHurewicz.attachCells (D-2) Γ ι f)) :
    Set.MapsTo (cylInclA₂ (D := D) (Γ := Γ) (ι := ι) (f := f) q)
      (cylPairA (D := D) (Γ := Γ) (ι := ι) (f := f) (X := X) q)
      (cylPairUinA₂ (D := D) (Γ := Γ) (ι := ι) (f := f) q) :=
  fun _ hx => hx

/-- The two composites `A → U → A₂` and `A → A₂` agree. -/
lemma cylInclU_comp_Uincl (q : C(X, Work.RatHurewicz.attachCells (D-2) Γ ι f)) :
    ((cylPairUincl (D := D) (Γ := Γ) (ι := ι) (f := f) q).comp
        (cylInclU (D := D) (Γ := Γ) (ι := ι) (f := f) q))
      = cylInclAA₂ (D := D) (Γ := Γ) (ι := ι) (f := f) q :=
  ContinuousMap.ext (fun _ => rfl)

/-- The composite `U → A₂ → C` is the inclusion `U → C`. -/
lemma cylPairUincl_comp_A₂sub (q : C(X, Work.RatHurewicz.attachCells (D-2) Γ ι f)) :
    ((cylPairA₂sub (D := D) (Γ := Γ) (ι := ι) (f := f) q).comp
        (cylPairUincl (D := D) (Γ := Γ) (ι := ι) (f := f) q))
      = cylPairUsub (D := D) (Γ := Γ) (ι := ι) (f := f) q :=
  ContinuousMap.ext (fun _ => rfl)

/-- The restriction of a map of pairs to the sub-pair, as a continuous map. -/
def restrictPair {X' Y' : Type} [TopologicalSpace X'] [TopologicalSpace Y']
    (A : Set X') (B : Set Y') (g : C(X', Y')) (hg : Set.MapsTo g A B) : C(↥A, ↥B) where
  toFun x := ⟨g x.1, hg x.2⟩
  continuous_toFun := Continuous.subtype_mk (g.continuous.comp continuous_subtype_val)
    (fun x => hg x.2)

@[simp] lemma restrictPair_coe {X' Y' : Type} [TopologicalSpace X'] [TopologicalSpace Y']
    (A : Set X') (B : Set Y') (g : C(X', Y')) (hg : Set.MapsTo g A B) (x : ↥A) :
    ((restrictPair A B g hg) x : Y') = g x.1 := rfl

/-- The chain map `C_*(U;ℚ) ⟶ C_*(A₂;ℚ)`. -/
def cylPairChainInclU (q : C(X, Work.RatHurewicz.attachCells (D-2) Γ ι f)) :
    Work.Cohomology.singularChains ℚ
        (TopCat.of ↥(cylPairU (D := D) (Γ := Γ) (ι := ι) (f := f) q)) ⟶
      Work.Cohomology.singularChains ℚ
        (TopCat.of ↥(cylPairA₂ (D := D) (Γ := Γ) (ι := ι) (f := f) q)) :=
  Work.Cohomology.chainMap ℚ
    (TopCat.of ↥(cylPairU (D := D) (Γ := Γ) (ι := ι) (f := f) q))
    (TopCat.of ↥(cylPairA₂ (D := D) (Γ := Γ) (ι := ι) (f := f) q))
    (TopCat.ofHom (cylPairUincl (D := D) (Γ := Γ) (ι := ι) (f := f) q))

/-- **The sub-pair map** `C_*(X,A;ℚ) ⟶ coker(C_*(U;ℚ) ⟶ C_*(A₂;ℚ))`: the map of relative chain
complexes induced by `cylIncl q : (X,A) → (A₂,U)`, with the target written as the cokernel of
`C_*(U) → C_*(A₂)`.  This is the map whose being a rational homology isomorphism expresses the
statement `H_m(A₂,U) ≅ H_m(X,A)` (the "collapse" `A₂/U ≅ X/A`). -/
def subPairMap (q : C(X, Work.RatHurewicz.attachCells (D-2) Γ ι f)) :
    Work.StemsB.relChainsR ℚ (TopCat.of X)
        (cylPairA (D := D) (Γ := Γ) (ι := ι) (f := f) q) ⟶
      cokernel (cylPairChainInclU (D := D) (Γ := Γ) (ι := ι) (f := f) q) :=
  cokernel.map (Work.StemsB.relChainsRIncl ℚ (TopCat.of X)
      (cylPairA (D := D) (Γ := Γ) (ι := ι) (f := f) q))
    (cylPairChainInclU (D := D) (Γ := Γ) (ι := ι) (f := f) q)
    (Work.Cohomology.chainMap ℚ
      (TopCat.of ↥(cylPairA (D := D) (Γ := Γ) (ι := ι) (f := f) (X := X) q))
      (TopCat.of ↥(cylPairU (D := D) (Γ := Γ) (ι := ι) (f := f) (X := X) q))
      (TopCat.ofHom (cylInclU (D := D) (Γ := Γ) (ι := ι) (f := f) q)))
    (Work.Cohomology.chainMap ℚ (TopCat.of X)
      (TopCat.of ↥(cylPairA₂ (D := D) (Γ := Γ) (ι := ι) (f := f) q))
      (TopCat.ofHom (cylInclA₂ (D := D) (Γ := Γ) (ι := ι) (f := f) q)))
    (by
      simp only [cylPairChainInclU, Work.StemsB.relChainsRIncl, Work.Cohomology.chainMap]
      have h : Work.Cohomology.subtypeIncl (TopCat.of X)
            (cylPairA (D := D) (Γ := Γ) (ι := ι) (f := f) (X := X) q) ≫
            TopCat.ofHom (cylInclA₂ (D := D) (Γ := Γ) (ι := ι) (f := f) q)
          = TopCat.ofHom (cylInclU (D := D) (Γ := Γ) (ι := ι) (f := f) q) ≫
            TopCat.ofHom (cylPairUincl (D := D) (Γ := Γ) (ι := ι) (f := f) q) := by
        rw [← TopCat.ofHom_comp, cylInclU_comp_Uincl]
        ext x
        rfl
      rw [← Functor.map_comp, ← Functor.map_comp, h])

lemma mapsTo_q_cylPairA (q : C(X, Work.RatHurewicz.attachCells (D-2) Γ ι f)) :
    Set.MapsTo q (cylPairA (D := D) (Γ := Γ) (ι := ι) (f := f) (X := X) q)
      (cylPairS (D := D) (Γ := Γ) (ι := ι) (f := f)) := by
  intro x hx
  exact hx

lemma mapsTo_cylRetract_cylPairU (q : C(X, Work.RatHurewicz.attachCells (D-2) Γ ι f)) :
    Set.MapsTo (cylRetract q) (cylPairU (D := D) (Γ := Γ) (ι := ι) (f := f) q)
      (cylPairS (D := D) (Γ := Γ) (ι := ι) (f := f)) := fun _ hx => hx

end

end Work.Serre.DiscPair
