import Mathlib
import Submission.Work.Serre.E3aDefs
import Submission.Work.Serre.OneCell.Defs
import Submission.Work.Serre.OneCell.OneCellGeom
import Submission.Work.RatHurewicz.ExcisionSetup
import Submission.Work.Serre.E2dEngine

/-!
# The complement of the cell centres compresses onto the old part

`W = (oneCellCentresOne Y ι f)ᶜ ⊆ Z = attachOneCells Y ι f` is the space obtained by deleting the
centres of the attached intervals.  The centre cuts each interval `D¹` into two half-open intervals,
and each half retracts linearly onto its endpoint, which lies in the old part `Y' = range oneIncl`.
Hence `W` deformation retracts onto `Y'`, and `Work.Serre.compressRel_of_deformation` gives the
compression property of the pair `(W, Y')` in every dimension.

The deformation is defined on the disjoint union `Y ⊕ (Σ i, D¹)`: it is the identity on the
`Y`-part, and on a cell it moves the coordinate `x ∈ D¹ ∖ {0}` along the straight line from `x` to
its "sign" `|x| / x ∈ S⁰`, which is the endpoint of the half interval containing `x`.  This map
descends to the quotient `W` because it fixes the boundary sphere `S⁰`, which is exactly where the
gluing happens; the descent uses `Topology.IsQuotientMap.continuous_lift_prod_left` for the
quotient map `(mk)⁻¹(W) → W` obtained from
`Topology.IsQuotientMap.restrictPreimage_isOpen`.

The file is a transliteration of the identical proof for the duplicate construction
`Work.Serre.SPC.attachOneCells` in `Submission/Work/Serre/SPC/One/compressRel_cellCompl.lean`.
-/

open scoped Topology unitInterval
open CategoryTheory CategoryTheory.Limits

namespace Work.Serre.OneCell

open Work.Serre

noncomputable section

variable {Y : Type} [TopologicalSpace Y] {ι : Type} {f : ι → C(cellSphereZero, Y)}

/-- The complement of the centres of the attached intervals is open. -/
theorem isOpen_complCentresOne (Y : Type) [TopologicalSpace Y] (ι : Type)
    (f : ι → C(cellSphereZero, Y)) : IsOpen ((oneCellCentresOne Y ι f)ᶜ) := by
  obtain ⟨-, -, -, -, -, -, -, hcl⟩ := oneCellGeometry Y ι f
  exact hcl.isOpen_compl


/-! ## Continuity is local for an open cover -/

/-- Continuity is local for an open cover. -/
theorem continuous_of_isOpen_cover_pc {X Z : Type*} [TopologicalSpace X] [TopologicalSpace Z]
    {κ : Type*} {U : κ → Set X} (hU : ∀ k, IsOpen (U k)) (hcov : (⋃ k, U k) = Set.univ)
    {g : X → Z} (hg : ∀ k, Continuous fun x : ↥(U k) => g x) : Continuous g := by
  rw [continuous_def]
  intro O hO
  have hpre : g ⁻¹' O = ⋃ k, Subtype.val '' ((fun x : ↥(U k) => g x) ⁻¹' O) := by
    ext x
    constructor
    · intro hx
      have hxU : x ∈ ⋃ k, U k := by rw [hcov]; trivial
      obtain ⟨k, hk⟩ := Set.mem_iUnion.mp hxU
      exact Set.mem_iUnion.mpr ⟨k, ⟨⟨x, hk⟩, hx, rfl⟩⟩
    · intro hx
      obtain ⟨k, y, hy, hxy⟩ := Set.mem_iUnion.mp hx
      rw [← hxy]
      exact hy
  rw [hpre]
  refine isOpen_iUnion fun k => ?_
  obtain ⟨W, hW, hWeq⟩ := isOpen_induced_iff.mp ((hg k).isOpen_preimage O hO)
  have hWk : Subtype.val '' ((fun x : ↥(U k) => g x) ⁻¹' O) = U k ∩ W := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      refine ⟨y.2, ?_⟩
      show y ∈ Subtype.val ⁻¹' W
      rw [hWeq]
      exact hy
    · rintro ⟨hxU, hxW⟩
      refine ⟨⟨x, hxU⟩, ?_, rfl⟩
      rw [← hWeq]
      exact hxW
  rw [hWk]
  exact (hU k).inter hW

/-! ## The punctured model interval and its push -/

/-- The centre of the model interval belongs to its interior. -/
theorem cellDiskOneCentreOne_mem_cellInnerOne : cellDiskOneCentreOne ∈ cellInnerOne := by
  simp [cellDiskOneCentreOne, cellInnerOne]

theorem cellDiskOneCentreOne_coe : ((cellDiskOneCentreOne : cellDiskOne) : ℝ) = 0 := rfl

theorem eq_cellDiskOneCentreOne_iff {x : cellDiskOne} : x = cellDiskOneCentreOne ↔ (x : ℝ) = 0 :=
  ⟨fun h => by rw [h, cellDiskOneCentreOne_coe], fun h => Subtype.ext (by simpa [cellDiskOneCentreOne] using h)⟩

/-- The punctured model interval `D¹ ∖ {0}`. -/
abbrev punctD1 : Set cellDiskOne := {x | x ≠ cellDiskOneCentreOne}

theorem isOpen_punctD1 : IsOpen punctD1 := isClosed_singleton.isOpen_compl

theorem mem_punctD1_iff {x : cellDiskOne} : x ∈ punctD1 ↔ (x : ℝ) ≠ 0 :=
  not_congr eq_cellDiskOneCentreOne_iff

theorem punctD1_coe_ne_zero {x : ↥punctD1} : ((x : cellDiskOne) : ℝ) ≠ 0 := by
  intro h
  exact x.2 (eq_cellDiskOneCentreOne_iff.mpr h)

/-- The coordinate of the push of a punctured interval point towards its endpoint. -/
def punctPushVal (x : ↥punctD1) (s : I) : ℝ :=
  (1 - (s : ℝ)) * ((x : cellDiskOne) : ℝ) +
    (s : ℝ) * (|((x : cellDiskOne) : ℝ)| / ((x : cellDiskOne) : ℝ))

theorem punctAbs_div_self (x : ℝ) (hx : x ≠ 0) : |x| / x = 1 ∨ |x| / x = -1 := by
  rcases lt_or_gt_of_ne hx with h | h
  · right; rw [abs_of_neg h]; field_simp
  · left; rw [abs_of_pos h]; field_simp

theorem punctAbs_abs_div_self (x : ℝ) (hx : x ≠ 0) : |(|x| / x)| = 1 := by
  obtain h | h := punctAbs_div_self x hx <;> rw [h] <;> norm_num

/-- The push is the sign of `x` times the convex combination of `|x|` and `1`. -/
theorem punctPushVal_eq (x : ↥punctD1) (s : I) :
    punctPushVal x s = (|((x : cellDiskOne) : ℝ)| / ((x : cellDiskOne) : ℝ)) *
      ((1 - (s : ℝ)) * |((x : cellDiskOne) : ℝ)| + (s : ℝ)) := by
  have hx : ((x : cellDiskOne) : ℝ) ≠ 0 := punctD1_coe_ne_zero
  rw [punctPushVal]
  field_simp
  rw [← sq_abs]
  ring

theorem punctAbs_pushVal (x : ↥punctD1) (s : I) :
    |punctPushVal x s| = (1 - (s : ℝ)) * |((x : cellDiskOne) : ℝ)| + (s : ℝ) := by
  rw [punctPushVal_eq, abs_mul, punctAbs_abs_div_self _ punctD1_coe_ne_zero, one_mul]
  have hs0 : (0 : ℝ) ≤ (s : ℝ) := s.2.1
  have hs1 : (s : ℝ) ≤ 1 := s.2.2
  have hx0 : (0 : ℝ) ≤ |((x : cellDiskOne) : ℝ)| := abs_nonneg _
  rw [abs_of_nonneg]
  have h1 : (0 : ℝ) ≤ 1 - (s : ℝ) := by linarith
  exact add_nonneg (mul_nonneg h1 hx0) hs0

theorem punctPushVal_mem (x : ↥punctD1) (s : I) : punctPushVal x s ∈ Metric.closedBall (0 : ℝ) 1 := by
  have hx : |((x : cellDiskOne) : ℝ)| ≤ 1 := by
    have h := Metric.mem_closedBall.mp (x : cellDiskOne).2
    simpa [dist_eq_norm, Real.norm_eq_abs] using h
  have hs0 : (0 : ℝ) ≤ (s : ℝ) := s.2.1
  have hs1 : (s : ℝ) ≤ 1 := s.2.2
  rw [Metric.mem_closedBall, dist_eq_norm, Real.norm_eq_abs, sub_zero, punctAbs_pushVal]
  have h1 : (0 : ℝ) ≤ 1 - (s : ℝ) := by linarith
  have := mul_le_mul_of_nonneg_left hx h1
  linarith

theorem punctPushVal_ne_zero (x : ↥punctD1) (s : I) : punctPushVal x s ≠ 0 := by
  intro hzero
  have hx0 : (0 : ℝ) ≤ |((x : cellDiskOne) : ℝ)| := abs_nonneg _
  have hs0 : (0 : ℝ) ≤ (s : ℝ) := s.2.1
  have hkey : (1 - (s : ℝ)) * |((x : cellDiskOne) : ℝ)| + (s : ℝ) = 0 := by
    have h := congrArg (fun r : ℝ => (|((x : cellDiskOne) : ℝ)| / ((x : cellDiskOne) : ℝ))⁻¹ * r) hzero
    rw [punctPushVal_eq] at h
    rw [← mul_assoc, inv_mul_cancel₀] at h
    · simpa using h
    · intro hc
      have h1 := punctAbs_abs_div_self ((x : cellDiskOne) : ℝ) punctD1_coe_ne_zero
      rw [hc, abs_zero] at h1
      exact one_ne_zero h1.symm
  have hs1 : (s : ℝ) ≤ 1 := s.2.2
  have h1 : (0 : ℝ) ≤ 1 - (s : ℝ) := by linarith
  have hprod : (0 : ℝ) ≤ (1 - (s : ℝ)) * |((x : cellDiskOne) : ℝ)| := mul_nonneg h1 hx0
  have hs : (s : ℝ) = 0 := le_antisymm (by linarith) hs0
  have hxa : ((x : cellDiskOne) : ℝ) = 0 := by
    rw [hs] at hkey
    have habs : |((x : cellDiskOne) : ℝ)| = 0 := by linarith
    exact abs_eq_zero.mp habs
  exact punctD1_coe_ne_zero (x := x) hxa

/-- The coordinate of the push is continuous. -/
theorem continuous_punctPushVal :
    Continuous fun p : ↥punctD1 × I => punctPushVal p.1 p.2 := by
  have hx : Continuous fun p : ↥punctD1 × I => (((p.1 : ↥punctD1) : cellDiskOne) : ℝ) := by
    fun_prop
  have hs : Continuous fun p : ↥punctD1 × I => ((p.2 : I) : ℝ) := by fun_prop
  have hdiv : Continuous fun p : ↥punctD1 × I =>
      |(((p.1 : ↥punctD1) : cellDiskOne) : ℝ)| / (((p.1 : ↥punctD1) : cellDiskOne) : ℝ) :=
    hx.abs.div hx (fun p => punctD1_coe_ne_zero (x := p.1))
  have h : Continuous fun p : ↥punctD1 × I =>
      (1 - ((p.2 : I) : ℝ)) * (((p.1 : ↥punctD1) : cellDiskOne) : ℝ) +
        ((p.2 : I) : ℝ) *
          (|(((p.1 : ↥punctD1) : cellDiskOne) : ℝ)| / (((p.1 : ↥punctD1) : cellDiskOne) : ℝ)) :=
    ((continuous_const.sub hs).mul hx).add (hs.mul hdiv)
  simpa only [punctPushVal] using h

/-- The push of the punctured model interval towards its endpoints, as a function. -/
def punctPushFun (p : ↥punctD1 × I) : ↥punctD1 :=
  ⟨⟨punctPushVal p.1 p.2, punctPushVal_mem p.1 p.2⟩,
    fun h => punctPushVal_ne_zero p.1 p.2 (congrArg Subtype.val h)⟩

theorem punctPushFun_continuous : Continuous punctPushFun := by
  show Continuous fun p : ↥punctD1 × I =>
    (⟨⟨punctPushVal p.1 p.2, punctPushVal_mem p.1 p.2⟩,
      fun h => punctPushVal_ne_zero p.1 p.2 (congrArg Subtype.val h)⟩ : ↥punctD1)
  exact Continuous.subtype_mk
    (Continuous.subtype_mk continuous_punctPushVal (fun p => punctPushVal_mem p.1 p.2))
    (fun p => fun h => punctPushVal_ne_zero p.1 p.2 (congrArg Subtype.val h))

/-- The push of the punctured model interval, as a bundled continuous map. -/
def punctPush : C(↥punctD1 × I, ↥punctD1) := ⟨punctPushFun, punctPushFun_continuous⟩

@[simp] theorem punctPush_coe (p : ↥punctD1 × I) :
    (((punctPush p : ↥punctD1) : cellDiskOne) : ℝ) = punctPushVal p.1 p.2 := rfl

theorem punctPush_zero (x : ↥punctD1) : punctPush (x, (0 : I)) = x := by
  refine Subtype.ext (Subtype.ext ?_)
  rw [punctPush_coe, punctPushVal_eq]
  have h1 : (1 - (((0 : I)) : ℝ)) * |((x : cellDiskOne) : ℝ)| + ((0 : I) : ℝ) =
      |((x : cellDiskOne) : ℝ)| := by norm_num
  rw [h1]
  have hx : ((x : cellDiskOne) : ℝ) ≠ 0 := punctD1_coe_ne_zero
  have key : ((x : cellDiskOne) : ℝ) =
      (|((x : cellDiskOne) : ℝ)| / ((x : cellDiskOne) : ℝ)) * |((x : cellDiskOne) : ℝ)| := by
    field_simp
    rw [sq_abs]
  exact key.symm

/-- The push fixes the boundary `S⁰` of the interval pointwise. -/
theorem punctPush_sphere {x : cellDiskOne} (hx : x ∈ punctD1) (habs : ‖(x : ℝ)‖ = 1) (s : I) :
    punctPush ((⟨x, hx⟩ : ↥punctD1), s) = ⟨x, hx⟩ := by
  have habs' : |(x : ℝ)| = 1 := by simpa [Real.norm_eq_abs] using habs
  refine Subtype.ext (Subtype.ext ?_)
  rw [punctPush_coe, punctPushVal_eq]
  have h1 : (1 - (s : ℝ)) * |(x : ℝ)| + (s : ℝ) = 1 := by rw [habs']; ring
  rw [h1, mul_one]
  rcases (abs_eq (show (0 : ℝ) ≤ 1 by norm_num)).mp habs' with h | h <;> rw [h] <;> norm_num

/-- At time `1` the push of a punctured interval point lands on the boundary sphere. -/
theorem norm_punctPush_one (x : ↥punctD1) :
    ‖(((punctPush (x, (1 : I)) : ↥punctD1) : cellDiskOne) : ℝ)‖ = 1 := by
  rw [punctPush_coe, Real.norm_eq_abs, punctAbs_pushVal]
  norm_num

/-- The boundary of the model interval is the image of `S⁰`. -/
theorem cellSphereZeroToDiskOne_surj {v : cellDiskOne} (hv : ‖(v : ℝ)‖ = 1) :
    ∃ z : cellSphereZero, cellSphereZeroToDiskOne z = v := by
  refine ⟨⟨(v : ℝ), ?_⟩, Subtype.ext rfl⟩
  rw [Metric.mem_sphere, dist_eq_norm, sub_zero, Real.norm_eq_abs]
  simpa [Real.norm_eq_abs] using hv

/-! ## The ambient sets -/

/-- The points of the disjoint union lying over `Y`. -/
def pushPieceInl (Y : Type) (ι : Type) : Set (Y ⊕ (Σ _ : ι, cellDiskOne)) :=
  {a | ∃ y : Y, a = Sum.inl y}

/-- The non-central points of the `i`-th cell. -/
def pushPieceInr (Y : Type) (ι : Type) (i : ι) : Set (Y ⊕ (Σ _ : ι, cellDiskOne)) :=
  {a | ∃ x : cellDiskOne, x ∈ punctD1 ∧ a = Sum.inr ⟨i, x⟩}

theorem isOpen_pushPieceInl (Y : Type) [TopologicalSpace Y] (ι : Type) :
    IsOpen (pushPieceInl Y ι) := by
  rw [isOpen_sum_iff]
  constructor
  · have h : Sum.inl ⁻¹' pushPieceInl Y ι = (Set.univ : Set Y) := by
      ext y; exact ⟨fun _ => trivial, fun _ => ⟨y, rfl⟩⟩
    rw [h]; exact isOpen_univ
  · have h : Sum.inr ⁻¹' pushPieceInl Y ι = (∅ : Set (Σ _ : ι, cellDiskOne)) := by
      ext p; constructor
      · rintro ⟨y, hy⟩; exact absurd hy Sum.inr_ne_inl
      · intro h; exact absurd h (Set.notMem_empty p)
    rw [h]; exact isOpen_empty

theorem isOpen_pushPieceInr (Y : Type) [TopologicalSpace Y] (ι : Type) (i : ι) :
    IsOpen (pushPieceInr Y ι i) := by
  rw [isOpen_sum_iff]
  constructor
  · have h : Sum.inl ⁻¹' pushPieceInr Y ι i = (∅ : Set Y) := by
      ext y; constructor
      · rintro ⟨x, -, hy⟩; exact absurd hy Sum.inl_ne_inr
      · intro h; exact absurd h (Set.notMem_empty y)
    rw [h]; exact isOpen_empty
  · rw [isOpen_sigma_iff]
    intro j
    by_cases hji : j = i
    · subst j
      have h : Sigma.mk i ⁻¹' (Sum.inr ⁻¹' pushPieceInr Y ι i) = punctD1 := by
        ext x; constructor
        · rintro ⟨x', hx', h⟩
          have h2 : (⟨i, x⟩ : Σ _ : ι, cellDiskOne) = ⟨i, x'⟩ := Sum.inr.inj h
          have h3 : x = x' := congrArg (fun p : Σ _ : ι, cellDiskOne => p.2) h2
          rwa [h3]
        · intro hx; exact ⟨x, hx, rfl⟩
      rw [h]; exact isOpen_punctD1
    · have h : Sigma.mk j ⁻¹' (Sum.inr ⁻¹' pushPieceInr Y ι i) = (∅ : Set cellDiskOne) := by
        ext x; constructor
        · rintro ⟨x', -, h⟩
          have h2 : (⟨j, x⟩ : Σ _ : ι, cellDiskOne) = ⟨i, x'⟩ := Sum.inr.inj h
          exact absurd (congrArg (fun p : Σ _ : ι, cellDiskOne => p.1) h2) hji
        · intro h; exact absurd h (Set.notMem_empty x)
      rw [h]; exact isOpen_empty

/-- The preimage of the complement of the centres: the saturated open set on which the push lives. -/
abbrev pushDomainOne (Y : Type) [TopologicalSpace Y] (ι : Type) (f : ι → C(cellSphereZero, Y)) :
    Set (Y ⊕ (Σ _ : ι, cellDiskOne)) :=
  (Quotient.mk' (s := Relation.EqvGen.setoid (oneCellRel Y ι f)) :
      (Y ⊕ (Σ _ : ι, cellDiskOne)) → attachOneCells Y ι f) ⁻¹' (oneCellCentresOne Y ι f)ᶜ

theorem mk_inr_mem_centres_iff {i : ι} {x : cellDiskOne} :
    (Quotient.mk' (s := Relation.EqvGen.setoid (oneCellRel Y ι f))
      (Sum.inr (⟨i, x⟩ : Σ _ : ι, cellDiskOne)) : attachOneCells Y ι f) ∈
        oneCellCentresOne Y ι f ↔ x = cellDiskOneCentreOne := by
  constructor
  · intro h
    obtain ⟨j, hj⟩ := mem_oneCellCentresOne.mp h
    have hEq : (Quotient.mk' (s := Relation.EqvGen.setoid (oneCellRel Y ι f))
          (Sum.inr (⟨j, cellDiskOneCentreOne⟩ : Σ _ : ι, cellDiskOne)) : attachOneCells Y ι f) =
        (Quotient.mk' (s := Relation.EqvGen.setoid (oneCellRel Y ι f))
          (Sum.inr (⟨i, x⟩ : Σ _ : ι, cellDiskOne)) : attachOneCells Y ι f) := hj
    have hrel : Relation.EqvGen (oneCellRel Y ι f) (Sum.inr ⟨j, cellDiskOneCentreOne⟩)
        (Sum.inr ⟨i, x⟩) :=
      Quotient.exact (s := Relation.EqvGen.setoid (oneCellRel Y ι f)) hEq
    have hcls := (clsOne_of_inner (Y := Y) (ι := ι) f (i := j) (x := cellDiskOneCentreOne)
      cellDiskOneCentreOne_mem_cellInnerOne (Sum.inr ⟨i, x⟩)).mp (eqvGen_le_clsOne f hrel)
    exact congrArg (fun p : Σ _ : ι, cellDiskOne => p.2) (Sum.inr.inj hcls)
  · intro h
    refine mem_oneCellCentresOne.mpr ⟨i, ?_⟩
    show (Quotient.mk' (s := Relation.EqvGen.setoid (oneCellRel Y ι f))
      (Sum.inr (⟨i, cellDiskOneCentreOne⟩ : Σ _ : ι, cellDiskOne)) : attachOneCells Y ι f) = _
    rw [h]

theorem mk_inl_notMem_centres (y : Y) :
    (Quotient.mk' (s := Relation.EqvGen.setoid (oneCellRel Y ι f))
      (Sum.inl y) : attachOneCells Y ι f) ∉ oneCellCentresOne Y ι f := by
  intro h
  obtain ⟨i, hi⟩ := mem_oneCellCentresOne.mp h
  exact oneCellCentreOne_not_mem_oldPart (Y := Y) (ι := ι) (f := f) i ⟨y, hi.symm⟩

theorem mem_pushDomainOne_iff (a : Y ⊕ (Σ _ : ι, cellDiskOne)) :
    a ∈ pushDomainOne Y ι f ↔
      (∃ y : Y, a = Sum.inl y) ∨
        ∃ (i : ι) (x : cellDiskOne), x ∈ punctD1 ∧ a = Sum.inr ⟨i, x⟩ := by
  constructor
  · intro ha
    rcases a with y | p
    · exact Or.inl ⟨y, rfl⟩
    · refine Or.inr ⟨p.1, p.2, ?_, rfl⟩
      by_contra hx
      have hxc : p.2 = cellDiskOneCentreOne := by
        by_contra h2
        exact hx (by simpa [punctD1] using h2)
      exact ha (mk_inr_mem_centres_iff.mpr hxc)
  · rintro (⟨y, rfl⟩ | ⟨i, x, hx, rfl⟩)
    · exact mk_inl_notMem_centres y
    · intro hmem
      exact hx ((mk_inr_mem_centres_iff).mp hmem)

theorem pushDomainOne_subset_pieces :
    pushDomainOne Y ι f ⊆ pushPieceInl Y ι ∪ ⋃ i, pushPieceInr Y ι i := by
  intro a ha
  rcases (mem_pushDomainOne_iff a).mp ha with ⟨y, rfl⟩ | ⟨i, x, hx, rfl⟩
  · exact Or.inl ⟨y, rfl⟩
  · exact Or.inr (Set.mem_iUnion.mpr ⟨i, x, hx, rfl⟩)

/-! ## The push on the disjoint union -/

/-- The push of the cells, as a total function on the disjoint union; the branch at the centres is
a junk value and is never used, because the push is only evaluated on `pushDomainOne`. -/
def pushC (a : Y ⊕ (Σ _ : ι, cellDiskOne)) (s : I) : attachOneCells Y ι f :=
  Sum.elim (fun y : Y => oneIncl Y ι f y)
    (fun p : Σ _ : ι, cellDiskOne =>
      if h : p.2 ∈ punctD1 then
        oneCellMap Y ι f p.1 ((punctPush ((⟨p.2, h⟩ : ↥punctD1), s) : ↥punctD1) : cellDiskOne)
      else oneCellCentreOne Y ι f p.1) a

@[simp] theorem pushC_inl (y : Y) (s : I) : pushC (Sum.inl y) s = oneIncl Y ι f y := rfl

theorem pushC_inr {i : ι} {x : cellDiskOne} (hx : x ∈ punctD1) (s : I) :
    pushC (Sum.inr (⟨i, x⟩ : Σ _ : ι, cellDiskOne)) s =
      oneCellMap Y ι f i ((punctPush ((⟨x, hx⟩ : ↥punctD1), s) : ↥punctD1) : cellDiskOne) := by
  show (if h : x ∈ punctD1 then
      oneCellMap Y ι f i ((punctPush ((⟨x, h⟩ : ↥punctD1), s) : ↥punctD1) : cellDiskOne)
      else oneCellCentreOne Y ι f i) = _
  rw [dif_pos hx]

/-- The push of a point of the push domain stays off the centres. -/
theorem pushC_notMem_centres {a : Y ⊕ (Σ _ : ι, cellDiskOne)} (ha : a ∈ pushDomainOne Y ι f) (s : I) :
    pushC (f := f) a s ∉ oneCellCentresOne Y ι f := by
  rcases (mem_pushDomainOne_iff a).mp ha with ⟨y, rfl⟩ | ⟨i, x, hx, rfl⟩
  · rw [pushC_inl]
    exact mk_inl_notMem_centres y
  · rw [pushC_inr (i := i) (x := x) hx s]
    have hv : ((punctPush ((⟨x, hx⟩ : ↥punctD1), s) : ↥punctD1) : cellDiskOne) ∈ punctD1 :=
      (punctPush _).2
    intro hmem
    exact hv ((mk_inr_mem_centres_iff).mp hmem)

theorem mem_pushDomainOne_of_eqvGen {a b : Y ⊕ (Σ _ : ι, cellDiskOne)}
    (hab : Relation.EqvGen (oneCellRel Y ι f) a b) (ha : a ∈ pushDomainOne Y ι f) :
    b ∈ pushDomainOne Y ι f := by
  have hq : (Quotient.mk' (s := Relation.EqvGen.setoid (oneCellRel Y ι f)) a :
      attachOneCells Y ι f) =
      Quotient.mk' (s := Relation.EqvGen.setoid (oneCellRel Y ι f)) b :=
    Quotient.sound (s := Relation.EqvGen.setoid (oneCellRel Y ι f)) hab
  intro hb
  exact ha (hq.symm ▸ hb)

theorem pushC_eq_of_eqvGen : ∀ (s : I) {a b : Y ⊕ (Σ _ : ι, cellDiskOne)},
    Relation.EqvGen (oneCellRel Y ι f) a b → a ∈ pushDomainOne Y ι f →
      b ∈ pushDomainOne Y ι f → pushC (f := f) a s = pushC (f := f) b s := by
  intro s a b hab
  induction hab with
  | rel a b hab =>
    intro ha hb
    obtain ⟨i, z, rfl, rfl⟩ := hab
    have hzne : (cellSphereZeroToDiskOne z : cellDiskOne) ∈ punctD1 := by
      rw [mem_punctD1_iff]
      intro h0
      have h := norm_cellSphereZeroToDiskOne z
      rw [h0, norm_zero] at h
      exact one_ne_zero h.symm
    rw [pushC_inl, pushC_inr (i := i) (x := cellSphereZeroToDiskOne z) hzne s,
      punctPush_sphere hzne (norm_cellSphereZeroToDiskOne z) s]
    exact oneIncl_oneCellRel Y ι f i z
  | refl a => intro ha hb; rfl
  | symm a b hab ih => intro ha hb; exact (ih hb ha).symm
  | trans a b c hab hbc ih1 ih2 =>
    intro ha hc
    exact (ih1 ha (mem_pushDomainOne_of_eqvGen hab ha)).trans
      (ih2 (mem_pushDomainOne_of_eqvGen hab ha) hc)

theorem pushC_zero {a : Y ⊕ (Σ _ : ι, cellDiskOne)} (ha : a ∈ pushDomainOne Y ι f) :
    pushC (f := f) a 0 = (Quotient.mk' (s := Relation.EqvGen.setoid (oneCellRel Y ι f)) a :
      attachOneCells Y ι f) := by
  rcases (mem_pushDomainOne_iff a).mp ha with ⟨y, rfl⟩ | ⟨i, x, hx, rfl⟩
  · rfl
  · rw [pushC_inr (i := i) (x := x) hx 0]
    exact congrArg (fun v : ↥punctD1 => oneCellMap Y ι f i (v : cellDiskOne))
      (punctPush_zero ⟨x, hx⟩)

theorem pushC_one_mem {a : Y ⊕ (Σ _ : ι, cellDiskOne)} (ha : a ∈ pushDomainOne Y ι f) :
    pushC (f := f) a 1 ∈ oneCellOldPart Y ι f := by
  rcases (mem_pushDomainOne_iff a).mp ha with ⟨y, rfl⟩ | ⟨i, x, hx, rfl⟩
  · exact ⟨y, rfl⟩
  · rw [pushC_inr (i := i) (x := x) hx 1]
    have hbound : ‖(((punctPush ((⟨x, hx⟩ : ↥punctD1), (1 : I)) : ↥punctD1) : cellDiskOne) : ℝ)‖ = 1 :=
      norm_punctPush_one ⟨x, hx⟩
    obtain ⟨z, hz⟩ := cellSphereZeroToDiskOne_surj hbound
    rw [← hz, ← oneIncl_oneCellRel Y ι f i z]
    exact ⟨f i z, rfl⟩

theorem pushC_fix {a : Y ⊕ (Σ _ : ι, cellDiskOne)} (ha : a ∈ pushDomainOne Y ι f)
    (hA : (Quotient.mk' (s := Relation.EqvGen.setoid (oneCellRel Y ι f)) a :
      attachOneCells Y ι f) ∈ oneCellOldPart Y ι f) (s : I) :
    pushC (f := f) a s = (Quotient.mk' (s := Relation.EqvGen.setoid (oneCellRel Y ι f)) a :
      attachOneCells Y ι f) := by
  obtain ⟨y, hy⟩ := hA
  have hb : (Sum.inl y : Y ⊕ (Σ _ : ι, cellDiskOne)) ∈ pushDomainOne Y ι f := by
    rw [mem_pushDomainOne_iff]; exact Or.inl ⟨y, rfl⟩
  have hrel : Relation.EqvGen (oneCellRel Y ι f) a (Sum.inl y) :=
    Quotient.exact (s := Relation.EqvGen.setoid (oneCellRel Y ι f))
      (show (Quotient.mk' (s := Relation.EqvGen.setoid (oneCellRel Y ι f)) a :
          attachOneCells Y ι f) =
        (Quotient.mk' (s := Relation.EqvGen.setoid (oneCellRel Y ι f))
          (Sum.inl y) : attachOneCells Y ι f) from hy.symm)
  rw [pushC_eq_of_eqvGen s hrel ha hb, pushC_inl]
  exact hy

/-! ## Continuity of the push -/

/-- The coordinate of the `inr` part of a point of the disjoint union (junk value on the `inl`
part). -/
def sigmaCoord (Y : Type) [TopologicalSpace Y] (ι : Type) : C(Y ⊕ (Σ _ : ι, cellDiskOne), cellDiskOne) where
  toFun := Sum.elim (fun _ => cellDiskOneCentreOne) (fun p => p.2)
  continuous_toFun := continuous_const.sumElim (continuous_sigma (fun _ => continuous_id))

theorem continuous_pushC :
    Continuous fun p : ↥(pushDomainOne Y ι f) × I =>
      pushC (f := f) (p.1 : Y ⊕ (Σ _ : ι, cellDiskOne)) p.2 := by
  classical
  set U : (Unit ⊕ ι) → Set (↥(pushDomainOne Y ι f) × I) := fun k =>
    match k with
    | Sum.inl _ => {p | (p.1 : Y ⊕ (Σ _ : ι, cellDiskOne)) ∈ pushPieceInl Y ι}
    | Sum.inr i => {p | (p.1 : Y ⊕ (Σ _ : ι, cellDiskOne)) ∈ pushPieceInr Y ι i}
    with hUdef
  refine continuous_of_isOpen_cover_pc (U := U) ?_ ?_ ?_
  · rintro (⟨⟩ | i)
    · have hset : U (Sum.inl ()) =
          (fun p : ↥(pushDomainOne Y ι f) × I => (p.1 : Y ⊕ (Σ _ : ι, cellDiskOne))) ⁻¹'
            pushPieceInl Y ι := rfl
      rw [hset]
      exact (isOpen_pushPieceInl Y ι).preimage (by fun_prop)
    · have hset : U (Sum.inr i) =
          (fun p : ↥(pushDomainOne Y ι f) × I => (p.1 : Y ⊕ (Σ _ : ι, cellDiskOne))) ⁻¹'
            pushPieceInr Y ι i := rfl
      rw [hset]
      exact (isOpen_pushPieceInr Y ι i).preimage (by fun_prop)
  · apply Set.eq_univ_of_forall
    intro p
    rcases pushDomainOne_subset_pieces (Y := Y) (ι := ι) (f := f) p.1.2 with h | h
    · exact Set.mem_iUnion.mpr ⟨Sum.inl (), h⟩
    · obtain ⟨i, hi⟩ := Set.mem_iUnion.mp h
      exact Set.mem_iUnion.mpr ⟨Sum.inr i, hi⟩
  · rintro (⟨⟩ | i)
    · -- the piece over `Y`
      have hq1 : Continuous fun q : ↥(U (Sum.inl ())) =>
          (q.1 : ↥(pushDomainOne Y ι f) × I) :=
        continuous_subtype_val
      have hq2 : Continuous fun q : ↥(U (Sum.inl ())) => (q.1.1 : ↥(pushDomainOne Y ι f)) :=
        continuous_fst.comp hq1
      have hq3 : Continuous fun q : ↥(U (Sum.inl ())) => (q.1.1 : Y ⊕ (Σ _ : ι, cellDiskOne)) :=
        continuous_subtype_val.comp hq2
      have hcont : Continuous fun q : ↥(U (Sum.inl ())) =>
          (Quotient.mk' (s := Relation.EqvGen.setoid (oneCellRel Y ι f))
            (q.1.1 : Y ⊕ (Σ _ : ι, cellDiskOne)) : attachOneCells Y ι f) :=
        (continuous_quotient_mk' (s := Relation.EqvGen.setoid (oneCellRel Y ι f))).comp hq3
      refine hcont.congr (fun q => ?_)
      obtain ⟨y, hy⟩ := q.2
      rw [hy]
      rfl
    · -- the piece over the `i`-th cell
      have hne : ∀ q : ↥(U (Sum.inr i)),
          sigmaCoord Y ι (q.1.1 : Y ⊕ (Σ _ : ι, cellDiskOne)) ∈ punctD1 := by
        intro q
        obtain ⟨x, hx, hxq⟩ := q.2
        rw [hxq]
        exact hx
      have hr1 : Continuous fun q : ↥(U (Sum.inr i)) => (q.1 : ↥(pushDomainOne Y ι f) × I) :=
        continuous_subtype_val
      have hr2 : Continuous fun q : ↥(U (Sum.inr i)) => (q.1.1 : ↥(pushDomainOne Y ι f)) :=
        continuous_fst.comp hr1
      have hg : Continuous fun q : ↥(U (Sum.inr i)) => (q.1.1 : Y ⊕ (Σ _ : ι, cellDiskOne)) :=
        continuous_subtype_val.comp hr2
      have hcoord : Continuous fun q : ↥(U (Sum.inr i)) =>
          sigmaCoord Y ι (q.1.1 : Y ⊕ (Σ _ : ι, cellDiskOne)) :=
        (sigmaCoord Y ι).continuous.comp hg
      have hH : Continuous fun q : ↥(U (Sum.inr i)) =>
          (⟨sigmaCoord Y ι (q.1.1 : Y ⊕ (Σ _ : ι, cellDiskOne)), hne q⟩ : ↥punctD1) :=
        Continuous.subtype_mk hcoord hne
      have htime : Continuous fun q : ↥(U (Sum.inr i)) => q.1.2 :=
        continuous_snd.comp hr1
      have hpc : Continuous fun q : ↥(U (Sum.inr i)) =>
          oneCellMap Y ι f i
            ((punctPush ((⟨sigmaCoord Y ι (q.1.1 : Y ⊕ (Σ _ : ι, cellDiskOne)), hne q⟩ : ↥punctD1),
              q.1.2) : ↥punctD1) : cellDiskOne) :=
        (oneCellMap Y ι f i).continuous.comp (continuous_subtype_val.comp
          (punctPush.continuous.comp (hH.prodMk htime)))
      refine hpc.congr (fun q => ?_)
      obtain ⟨x, hx, hxq⟩ := q.2
      have hsub : (⟨sigmaCoord Y ι (q.1.1 : Y ⊕ (Σ _ : ι, cellDiskOne)), hne q⟩ : ↥punctD1) =
          ⟨x, hx⟩ := by
        refine Subtype.ext ?_
        show sigmaCoord Y ι (q.1.1 : Y ⊕ (Σ _ : ι, cellDiskOne)) = x
        rw [hxq]
        rfl
      show oneCellMap Y ι f i
            ((punctPush ((⟨sigmaCoord Y ι (q.1.1 : Y ⊕ (Σ _ : ι, cellDiskOne)), hne q⟩ : ↥punctD1),
              q.1.2) : ↥punctD1) : cellDiskOne) =
          pushC (f := f) (q.1.1 : Y ⊕ (Σ _ : ι, cellDiskOne)) q.1.2
      rw [hsub, hxq, pushC_inr (i := i) (x := x) hx q.1.2]

/-! ## The compression -/

-- The complement of the cell centres compresses onto the old part.
-- `Z = attachOneCells Y ι f` is `Y` with the intervals `D¹` attached along `f : ι → C(S⁰,Y)`;
-- `P = oneCellCentresOne Y ι f` is the set of centres `χᵢ 0`; `Y' = oneCellOldPart Y ι f` is the
-- image of `Y` in `Z`.  `CompressRel V A d` (Work.RatHurewicz.ExcisionSetup) says: every map of
-- pairs `(Iᵈ, ∂Iᵈ) → (V,A)` is homotopic relative to the boundary to a map into `A`.
-- Geometrically deleting the centre of each interval cuts it into `(0,1)` and `(-1,0)`, and each
-- half is pushed linearly onto its endpoint `χᵢ(±1) ∈ Y'`, the homotopy staying in `Z ∖ P`; the old
-- part is fixed pointwise.
-- A complete proof of exactly this statement for the *duplicate* construction
-- `Work.Serre.SPC.attachOneCells` is already on disk as `Work.Serre.SPC.One.compressRel_cellCompl`
-- (Submission/Work/Serre/SPC/One/compressRel_cellCompl.lean); it cannot be imported here (it pulls
-- in Submission.Work.Serre.cellStepDefs, which re-declares Work.Serre.cellStepMap, clashing with
-- Submission.Work.Serre.E3aDefs) but it can be transliterated, renaming every SPC name to the
-- corresponding Work.Serre / Work.Serre.OneCell name.
theorem compressRel_cellPunctured (Y : Type) [TopologicalSpace Y] (ι : Type)
    (f : ι → C(Work.Serre.cellSphereZero, Y)) (d : ℕ) :
    Work.RatHurewicz.CompressRel ↥((Work.Serre.OneCell.oneCellCentresOne Y ι f)ᶜ)
      {x : ↥((Work.Serre.OneCell.oneCellCentresOne Y ι f)ᶜ) |
        (x : Work.Serre.attachOneCells Y ι f) ∈ Work.Serre.OneCell.oneCellOldPart Y ι f} d := by
  classical
  let qr : ↥(pushDomainOne Y ι f) → ↥((oneCellCentresOne Y ι f)ᶜ) :=
    ((oneCellCentresOne Y ι f)ᶜ).restrictPreimage
      (Quotient.mk' (s := Relation.EqvGen.setoid (oneCellRel Y ι f)) :
        (Y ⊕ (Σ _ : ι, cellDiskOne)) → attachOneCells Y ι f)
  have hqr : Topology.IsQuotientMap qr :=
    Topology.IsQuotientMap.restrictPreimage_isOpen
      (isQuotientMap_quotient_mk' (s := Relation.EqvGen.setoid (oneCellRel Y ι f)))
      (isOpen_complCentresOne Y ι f)
  let G : ↥((oneCellCentresOne Y ι f)ᶜ) × I → attachOneCells Y ι f := fun p =>
    pushC (f := f) ((Classical.choose (hqr.surjective p.1) : ↥(pushDomainOne Y ι f)) :
      Y ⊕ (Σ _ : ι, cellDiskOne)) p.2
  have hG_cont : Continuous G := by
    refine Topology.IsQuotientMap.continuous_lift_prod_left hqr ?_
    have hcomp : (fun p : ↥(pushDomainOne Y ι f) × I => G (qr p.1, p.2)) =
        fun p : ↥(pushDomainOne Y ι f) × I =>
          pushC (f := f) (p.1 : Y ⊕ (Σ _ : ι, cellDiskOne)) p.2 := by
      funext p
      show pushC (f := f) ((Classical.choose (hqr.surjective (qr p.1)) :
          ↥(pushDomainOne Y ι f)) : Y ⊕ (Σ _ : ι, cellDiskOne)) p.2 =
        pushC (f := f) (p.1 : Y ⊕ (Σ _ : ι, cellDiskOne)) p.2
      refine pushC_eq_of_eqvGen p.2 ?_ (Classical.choose (hqr.surjective (qr p.1))).2 p.1.2
      exact Quotient.exact (s := Relation.EqvGen.setoid (oneCellRel Y ι f))
        (show (Quotient.mk' (s := Relation.EqvGen.setoid (oneCellRel Y ι f))
              ((Classical.choose (hqr.surjective (qr p.1)) : ↥(pushDomainOne Y ι f)) :
                Y ⊕ (Σ _ : ι, cellDiskOne)) : attachOneCells Y ι f) =
            Quotient.mk' (s := Relation.EqvGen.setoid (oneCellRel Y ι f))
              (p.1 : Y ⊕ (Σ _ : ι, cellDiskOne)) from
          congrArg (fun w : ↥((oneCellCentresOne Y ι f)ᶜ) => (w : attachOneCells Y ι f))
            (Classical.choose_spec (hqr.surjective (qr p.1))))
    rw [hcomp]
    exact continuous_pushC
  have hG_zero : ∀ v : ↥((oneCellCentresOne Y ι f)ᶜ), G (v, 0) = (v : attachOneCells Y ι f) := by
    intro v
    show pushC (f := f) ((Classical.choose (hqr.surjective v) : ↥(pushDomainOne Y ι f)) :
      Y ⊕ (Σ _ : ι, cellDiskOne)) 0 = (v : attachOneCells Y ι f)
    rw [pushC_zero (Classical.choose (hqr.surjective v)).2]
    exact congrArg (fun w : ↥((oneCellCentresOne Y ι f)ᶜ) => (w : attachOneCells Y ι f))
      (Classical.choose_spec (hqr.surjective v))
  have hG_one : ∀ v : ↥((oneCellCentresOne Y ι f)ᶜ),
      G (v, 1) ∈ oneCellOldPart Y ι f :=
    fun v => pushC_one_mem (Classical.choose (hqr.surjective v)).2
  have hG_fix : ∀ (v : ↥((oneCellCentresOne Y ι f)ᶜ)) (t : I),
      (v : attachOneCells Y ι f) ∈ oneCellOldPart Y ι f →
        G (v, t) = (v : attachOneCells Y ι f) := by
    intro v t hv
    have hchoose : (Quotient.mk' (s := Relation.EqvGen.setoid (oneCellRel Y ι f))
          ((Classical.choose (hqr.surjective v) : ↥(pushDomainOne Y ι f)) :
            Y ⊕ (Σ _ : ι, cellDiskOne)) : attachOneCells Y ι f) =
        (v : attachOneCells Y ι f) :=
      congrArg (fun w : ↥((oneCellCentresOne Y ι f)ᶜ) => (w : attachOneCells Y ι f))
        (Classical.choose_spec (hqr.surjective v))
    have hv' : (Quotient.mk' (s := Relation.EqvGen.setoid (oneCellRel Y ι f))
          ((Classical.choose (hqr.surjective v) : ↥(pushDomainOne Y ι f)) :
            Y ⊕ (Σ _ : ι, cellDiskOne)) : attachOneCells Y ι f) ∈ oneCellOldPart Y ι f :=
      hchoose.symm ▸ hv
    show pushC (f := f) ((Classical.choose (hqr.surjective v) : ↥(pushDomainOne Y ι f)) :
      Y ⊕ (Σ _ : ι, cellDiskOne)) t = (v : attachOneCells Y ι f)
    rw [pushC_fix (Classical.choose (hqr.surjective v)).2 hv' t]
    exact hchoose
  have hGmem : ∀ p : ↥((oneCellCentresOne Y ι f)ᶜ) × I,
      G p ∈ (oneCellCentresOne Y ι f)ᶜ :=
    fun p => pushC_notMem_centres (Classical.choose (hqr.surjective p.1)).2 p.2
  refine Work.Serre.compressRel_of_deformation
    (⟨fun p => (⟨G p, hGmem p⟩ : ↥((oneCellCentresOne Y ι f)ᶜ)),
      hG_cont.subtype_mk hGmem⟩ : C(↥((oneCellCentresOne Y ι f)ᶜ) × I,
        ↥((oneCellCentresOne Y ι f)ᶜ))) ?_ ?_ ?_ d
  · intro v; exact Subtype.ext (hG_zero v)
  · intro v; exact hG_one v
  · intro v hv t; exact Subtype.ext (hG_fix v t hv)

end

end Work.Serre.OneCell

