import Mathlib
import Submission.Work.ThomBordism.Interface
import Submission.Work.Thom.manifoldP1
import Submission.Work.ThomBordism.PontryaginThom.Frames
import Submission.Work.ThomBordism.FrameSigns.Defs
import Submission.Work.Orient.Bridge
import Submission.Work.Thom.ATools
import Submission.Work.Tubular.relKronecker_chain

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedSectionVars false

/-!
# The chartwise cohomological data of the tangent frame signs

For a chart index `i` of the finite cover `Work.Thom.chartCover` of a closed `8`-manifold `V`, with
source `src V i`, and a point `x ∈ src V i`:

* `chartTrans V i x` is the translated chart `z ↦ eᵢ z − eᵢ x`, a map of pairs
  `(Uᵢ, Uᵢ ∖ {x}) → (ℝ⁸, ℝ⁸∖0)`;
* `isIso_exc` is the (specific) excision isomorphism `H⁸(V,V∖{x}) ≅ H⁸(Uᵢ,Uᵢ∖{x})`;
* `chartCoh V i x` is the inverse image under it of `(chartTrans)⁎ τ`, where `τ` is the model class
  of `Submission/Work/ThomBordism/FrameSigns/Defs.lean` (with `⟨τ,−⟩` the isomorphism
  `H₈(ℝ⁸,ℝ⁸∖0) ≅ ℤ`);
* `frameSign V i x` is the sign of `⟨chartCoh V i x, locClass V x⟩`.
-/

open Classical CategoryTheory

namespace Work.ThomBordism.FrameSigns

noncomputable section

/-- The index type of the finite chart cover of `V`. -/
abbrev ChartIdx (V : Man8) : Type :=
  Fin (Work.Thom.chartCoverSize (H := PontryaginThom.Euc 8) (M := V.pt))

/-- The chart of the finite cover. -/
def chartOf (V : Man8) (i : ChartIdx V) : atlas (PontryaginThom.Euc 8) V.pt :=
  Work.Thom.chartCover (H := PontryaginThom.Euc 8) (M := V.pt) i

/-- The source of the chart `i`. -/
def src (V : Man8) (i : ChartIdx V) : Set V.pt := (chartOf V i).1.source

/-- The chart map `eᵢ`, as a function. -/
def chartMap (V : Man8) (i : ChartIdx V) : V.pt → EuclideanSpace ℝ (Fin 8) := (chartOf V i).1

@[simp] theorem chartMap_apply (V : Man8) (i : ChartIdx V) (x : V.pt) :
    chartMap V i x = (chartOf V i).1 x := rfl

/-- The complement of a point, as a subset (spelled with the carrier of `TopCat.of V.pt` so that it
agrees syntactically with `Work.Orient.LocH`). -/
abbrev punct (V : Man8) (x : V.pt) : Set ↑(TopCat.of V.pt) := {y | y ≠ x}

theorem isOpen_punct (V : Man8) (x : V.pt) : IsOpen (punct V x) :=
  isClosed_singleton.isOpen_compl

/-- The inclusion `↥(src V i) → V.pt`. -/
def srcIncl (V : Man8) (i : ChartIdx V) : C(↥(src V i), V.pt) :=
  ⟨Subtype.val, continuous_subtype_val⟩

/-- The punctured chart source, as a subset of `↥(src V i)`. -/
def punctSrc (V : Man8) (i : ChartIdx V) (x : V.pt) : Set ↥(src V i) := {z | (z : V.pt) ≠ x}

/-- The translated chart map `z ↦ eᵢ z − eᵢ x`, out of the chart source. -/
def chartTrans (V : Man8) (i : ChartIdx V) (x : V.pt) (hx : x ∈ src V i) :
    C(↥(src V i), EuclideanSpace ℝ (Fin 8)) :=
  ⟨fun z => chartMap V i (z : V.pt) - chartMap V i x,
    ((continuousOn_iff_continuous_domRestrict.mp (chartOf V i).1.continuousOn).sub
      continuous_const)⟩

@[simp] theorem chartTrans_apply (V : Man8) (i : ChartIdx V) (x : V.pt) (hx : x ∈ src V i)
    (z : ↥(src V i)) :
    chartTrans V i x hx z = chartMap V i (z : V.pt) - chartMap V i x := rfl

/-- `chartTrans` carries the punctured chart source into `ℝ⁸∖0`. -/
theorem chartTrans_mem (V : Man8) (i : ChartIdx V) (x : V.pt) (hx : x ∈ src V i) :
    ∀ z ∈ punctSrc V i x, chartTrans V i x hx z ∈ E8p := by
  intro z hz
  simp only [punctSrc, Set.mem_setOf_eq, E8p, Set.mem_setOf_eq] at hz ⊢
  intro h
  have h1 : (chartOf V i).1.symm (chartMap V i (z : V.pt)) = (z : V.pt) :=
    (chartOf V i).1.left_inv z.2
  have h2 : (chartOf V i).1.symm (chartMap V i x) = x := (chartOf V i).1.left_inv hx
  have h3 : chartMap V i (z : V.pt) = chartMap V i x := sub_eq_zero.mp h
  exact hz (by rw [← h1, h3, h2])

/-- The membership hypothesis of the excision: the punctured chart source maps into the punctured
space. -/
theorem punctSrc_mem (V : Man8) (i : ChartIdx V) (x : V.pt) :
    ∀ z ∈ punctSrc V i x, (srcIncl V i) z ∈ punct V x := fun z hz => hz

/-- **Excision for the chart**: the inclusion of pairs `(Uᵢ, Uᵢ ∖ {x}) → (V, V ∖ {x})` induces an
isomorphism on relative cohomology. -/
theorem isIso_exc (V : Man8) (i : ChartIdx V) (x : V.pt) (hx : x ∈ src V i) :
    CategoryTheory.IsIso (Work.Thom.relCohMap (srcIncl V i) (punctSrc V i x) (punct V x)
      (punctSrc_mem V i x) ℤ 8) := by
  have hcov : src V i ∪ punct V x = Set.univ := by
    ext y
    simp only [Set.mem_union, Set.mem_univ, iff_true]
    by_cases hy : y ∈ src V i
    · exact Or.inl hy
    · exact Or.inr (by simp only [punct, Set.mem_setOf_eq]; intro hyx; exact hy (hyx ▸ hx))
  have hsub : ∀ y ∈ {z : ↥(src V i) | (z : V.pt) ∈ punct V x},
      (Work.Cohomology.subtypeIncl (TopCat.of V.pt) (src V i)) y ∈ punct V x := fun y hy => hy
  have hgoal : ∀ y ∈ punctSrc V i x,
      (Work.Cohomology.subtypeIncl (TopCat.of V.pt) (src V i)) y ∈ punct V x :=
    fun y hy => hy
  have heq : (Work.Cohomology.subtypeIncl (TopCat.of V.pt) (src V i))
      = TopCat.ofHom (srcIncl V i) := rfl
  have key := Work.Cohomology.capRel_excision_isIso (TopCat.of V.pt) (src V i) (punct V x)
    (chartOf V i).1.open_source (isOpen_punct V x) hcov 8 hsub
  have hcongr := Work.Cohomology.capRel_relComplexMap_congr ℤ (punctSrc V i x) (punct V x) heq
    hsub hgoal
  have key' : CategoryTheory.IsIso (HomologicalComplex.homologyMap
      (Work.Cohomology.relComplexMap ℤ (punctSrc V i x) (punct V x)
        (TopCat.ofHom (srcIncl V i)) hgoal) 8) := by
    rw [← hcongr]
    exact key
  exact key'

/-- **The chart class at `x`**: the inverse image under the excision isomorphism of the pullback of
the model class `τ` along the translated chart. -/
def chartCoh (V : Man8) (i : ChartIdx V) (x : V.pt) (hx : x ∈ src V i) :
    Work.Thom.RelCoh ℤ 8 V.pt (punct V x) :=
  haveI : CategoryTheory.IsIso (Work.Thom.relCohMap (srcIncl V i) (punctSrc V i x) (punct V x)
      (punctSrc_mem V i x) ℤ 8) := isIso_exc V i x hx
  (CategoryTheory.inv (Work.Thom.relCohMap (srcIncl V i) (punctSrc V i x) (punct V x)
      (punctSrc_mem V i x) ℤ 8)).hom
    ((Work.Thom.relCohMap (chartTrans V i x hx) (punctSrc V i x) E8p
      (chartTrans_mem V i x hx) ℤ 8).hom tau)

/-- The transition determinant sign, exactly as in the target statement. -/
def transSign (V : Man8) (i j : ChartIdx V) (x : V.pt) : ℝ :=
  Real.sign (LinearMap.det (ContinuousLinearMap.toLinearMap
    (fderiv ℝ (fun y => chartMap V j ((chartOf V i).1.symm y)) ((chartOf V i).1 x))))

/-- For a `ℤ`-linear functional and an integer scalar, `(k • φ) z = k * φ z`. -/
theorem zsmul_apply_int {M : Type*} [AddCommGroup M] (φ : M →ₗ[ℤ] ℤ) (k : ℤ) (z : M) :
    (k • φ) z = k * φ z := by
  rw [LinearMap.smul_apply]
  exact Int.zsmul_eq_mul k (φ z)

/-- The local fundamental class of `V` at `x`, in the spelling of the pair `(V, V∖{x})` used by
`Work.Tubular.relKronH`. -/
def pairLoc (V : Man8) (x : V.pt) :
    ↑(HomologicalComplex.homology (Work.Cohomology.relChains (TopCat.of V.pt) (punct V x)) 8) :=
  Work.Orient.locClass (TopCat.of V.pt) 8 V.c x

/-- **The Kronecker pairing of the chart class with the local fundamental class** at a point of the
chart source. -/
def pairVal (V : Man8) (i : ChartIdx V) (x : V.pt) (hx : x ∈ src V i) : ℤ :=
  (Work.Tubular.relKronH (TopCat.of V.pt) (punct V x) 8) (chartCoh V i x hx) (pairLoc V x)

/-- **The chart frame sign**: the sign of the pairing of the chart class with the local fundamental
class.  Junk value `1` outside the chart source. -/
def frameSign (V : Man8) (i : ChartIdx V) (x : V.pt) : ℝ :=
  if hx : x ∈ src V i then (if 0 < pairVal V i x hx then (1 : ℝ) else -1) else 1

@[simp] theorem frameSign_of_mem (V : Man8) (i : ChartIdx V) (x : V.pt) (hx : x ∈ src V i) :
    frameSign V i x = (if 0 < pairVal V i x hx then (1 : ℝ) else -1) := by
  rw [frameSign, dif_pos hx]

/-- **The values of `frameSign`.** -/
theorem frameSign_eq_one_or_neg_one (V : Man8) (i : ChartIdx V) (x : V.pt) :
    frameSign V i x = 1 ∨ frameSign V i x = -1 := by
  by_cases hx : x ∈ src V i
  · rw [frameSign_of_mem V i x hx]
    by_cases h : 0 < pairVal V i x hx
    · rw [if_pos h]; exact Or.inl rfl
    · rw [if_neg h]; exact Or.inr rfl
  · rw [frameSign, dif_neg hx]; exact Or.inl rfl


/-! ## The transition germ between two charts -/

/-- The image of the overlap of the charts `i`, `j` under the translated chart `i`: the open set on
which the transition germ between `i` and `j` at `x` is considered. -/
def germSet (V : Man8) (i j : ChartIdx V) (x : V.pt) : Set (EuclideanSpace ℝ (Fin 8)) :=
  (fun z : V.pt => (chartOf V i).1 z - (chartOf V i).1 x) '' (src V i ∩ src V j)

/-- The transition germ `w ↦ eⱼ (eᵢ⁻¹ (w + eᵢ x)) − eⱼ x` between the charts `i` and `j` at `x`
(junk values outside the domain of definition of the charts). -/
def germFun (V : Man8) (i j : ChartIdx V) (x : V.pt) : EuclideanSpace ℝ (Fin 8) → EuclideanSpace ℝ (Fin 8) :=
  fun w => (chartOf V j).1 ((chartOf V i).1.symm (w + (chartOf V i).1 x)) - (chartOf V j).1 x

/-- The transition germ vanishes at `0`. -/
theorem germFun_zero (V : Man8) (i j : ChartIdx V) (x : V.pt) (hi : x ∈ src V i) :
    germFun V i j x 0 = 0 := by
  show (chartOf V j).1 ((chartOf V i).1.symm (0 + (chartOf V i).1 x)) - (chartOf V j).1 x = 0
  rw [zero_add, (chartOf V i).1.left_inv hi, sub_self]

/-- **The transition germ is the transition function composed with the translated chart**: for
`z` in the source of the chart `i`, `germFun (chartTrans i z) = eⱼ z − eⱼ x`. -/
theorem germFun_chartTrans (V : Man8) (i j : ChartIdx V) (x : V.pt) (hi : x ∈ src V i)
    (z : ↥(src V i)) :
    germFun V i j x (chartTrans V i x hi z)
      = (chartOf V j).1 (z : V.pt) - (chartOf V j).1 x := by
  show (chartOf V j).1 ((chartOf V i).1.symm
      (chartTrans V i x hi z + (chartOf V i).1 x)) - (chartOf V j).1 x = _
  rw [chartTrans_apply, chartMap_apply, chartMap_apply, sub_add_cancel,
    (chartOf V i).1.left_inv z.2]

/-- The translated chart `i` maps the overlap of the two charts into `germSet`. -/
theorem germSet_mem (V : Man8) (i j : ChartIdx V) (x : V.pt) (hi : x ∈ src V i) {z : V.pt}
    (hz : z ∈ src V i ∩ src V j) :
    chartTrans V i x hi ⟨z, hz.1⟩ ∈ germSet V i j x :=
  ⟨z, hz, rfl⟩

end

end Work.ThomBordism.FrameSigns
