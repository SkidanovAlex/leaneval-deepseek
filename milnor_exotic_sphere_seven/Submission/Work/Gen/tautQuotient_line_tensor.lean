import Mathlib
import Submission.Work.Gen.LineTensor
import Submission.Work.Thom.tautologicalQuotient
import Submission.Work.Thom.QuotientLin
import Submission.Work.Thom.chernClass
import Submission.Work.Thom.realification_homeo
import Submission.Work.Whitney.Basic
import Submission.Work.Whitney.WBData

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
set_option linter.unusedSectionVars false

/-!
# The determinant trick: `Q_{L ⊕ M} ≅ π^*(L ⊗ M)`

For complex line bundles `L`, `M` over a base `B`, the tautological quotient
`Q_{L⊕M} = π^*(L ⊕ M) / ℂ·s` over the punctured total space of `L ⊕ M` is canonically isomorphic
to the pullback of the tensor product `L ⊗ M`: the fibrewise map is the **wedge** `v ↦ v ∧ s`,
which kills the tautological line `ℂ·s` and lands in `Λ²(L ⊕ M) ≅ L ⊗ M`.

This is the *determinant trick*: combined with the descent equation of the Chern recursion it gives
`c₁(L ⊕ M) = c₁(L ⊗ M)`, hence — with `Work.Gen.TautTensorTriv` and the injectivity of `π^*` in
degree `2` — `c₁(O(1) ⊕ O(-1)) = 0`, the `c₁` input of `Work.Gen.EulerChernTwo`.

## Layout

* `wedgeCoeff`, `wedgeSign`, `wedgeScalar`, `wedgeCLM` — the fibrewise map, read in the **natural**
  charts (the chart `Q.indexAt y = (W.indexAt y.1, tqCoord W y)` of the quotient and
  `Z'.indexAt y` of the tensor pullback);
* `chartSet`, `chartCoord`, `chartWedgeScalar`, `chartWedge` — the same map read in a **fixed**
  chart, which is what one can prove continuous directly;
* `continuousOn_chartWedge` and the transfer lemma — the two-step pattern of
  `Work.Whitney.exists_bundleIso_comap_tautQuotient_whitneySum`.
-/

namespace Work.Gen

open Work.TangentClasses Work.Thom

noncomputable section

variable {B : Type} [TopologicalSpace B] {ι₁ ι₂ : Type} [Fintype ι₁] [Fintype ι₂]

/-- The direct sum of two complex line bundles, in the standard rank-`2` fibre. -/
abbrev lmSum (L : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin 1)) ι₁)
    (M : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin 1)) ι₂) :
    VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin 2)) (ι₁ × ι₂) :=
  Work.Whitney.whitneySum (m₁ := 1) (m₂ := 1) L M

variable (L : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin 1)) ι₁)
  (M : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin 1)) ι₂)

/-- The punctured total space of `L ⊕ M`. -/
abbrev lmPunct : Type := ↥(zeroComplement (realification (lmSum L M)))

/-- The tautological quotient of `L ⊕ M`. -/
abbrev lmQuot : VectorBundleCore ℂ (lmPunct L M) (EuclideanSpace ℂ (Fin 1))
    ((ι₁ × ι₂) × Fin 2) :=
  tautQuotient (m := 1) (lmSum L M)

/-- The projection of the punctured total space of `L ⊕ M`. -/
abbrev lmProj : C(lmPunct L M, B) :=
  (bundleProj (realification (lmSum L M))).comp
    (subtypeMap (zeroComplement (realification (lmSum L M))))

/-- The pullback of the tensor product to the punctured total space. -/
abbrev lmTens : VectorBundleCore ℂ (lmPunct L M) (EuclideanSpace ℂ (Fin 1)) (ι₁ × ι₂) :=
  bundleComap (tensorLine L M) (lmProj L M)

/-! ## The coordinate of the punctured point in a fixed chart -/

/-- The set of punctured points at which the chart `i` of `L ⊕ M` is valid. -/
def chartSet (i : ι₁ × ι₂) : Set (lmPunct L M) :=
  {y | (y : (realification (lmSum L M)).TotalSpace) ∈
    ((realification (lmSum L M)).localTriv i).source}

/-- The coordinate of the punctured point in the chart `i` of `L ⊕ M` (read through the
realification, whose trivialisations agree with those of `L ⊕ M`). -/
def chartCoord (i : ι₁ × ι₂) (y : lmPunct L M) : EuclideanSpace ℂ (Fin 2) :=
  (((realification (lmSum L M)).localTriv i)
    (y : (realification (lmSum L M)).TotalSpace)).2

theorem continuousOn_chartCoord (i : ι₁ × ι₂) :
    ContinuousOn (chartCoord L M i) (chartSet L M i) := by
  have h1 : ContinuousOn (fun y : lmPunct L M =>
      ((realification (lmSum L M)).localTriv i)
        (y : (realification (lmSum L M)).TotalSpace)) (chartSet L M i) :=
    (((realification (lmSum L M)).localTriv i).continuousOn).comp
      continuous_subtype_val.continuousOn (fun y hy => hy)
  exact h1.snd

theorem continuousOn_chartCoord_ofLp (i : ι₁ × ι₂) :
    ContinuousOn (fun y : lmPunct L M => (chartCoord L M i y).ofLp) (chartSet L M i) :=
  (PiLp.continuous_ofLp 2 (fun _ : Fin 2 => ℂ)).comp_continuousOn
    (continuousOn_chartCoord L M i)

theorem continuousOn_chartCoord_apply (i : ι₁ × ι₂) (c : Fin 2) :
    ContinuousOn (fun y : lmPunct L M => (chartCoord L M i y) c) (chartSet L M i) := by
  refine ((continuous_apply c).comp_continuousOn (continuousOn_chartCoord_ofLp L M i)).congr ?_
  intro _ _
  rfl

/-! ## The wedge in a fixed chart -/

/-- The scalar of the wedge `z ↦ (fillFun k z) ∧ w` in the fixed chart `i`, where `w` is the
chart-`i` coordinate of the tautological section. -/
def chartWedgeScalar (i : ι₁ × ι₂) (k : Fin 2) (y : lmPunct L M) : ℂ :=
  (fillFun k oneVec) 0 * (chartCoord L M i y) 1
    - (fillFun k oneVec) 1 * (chartCoord L M i y) 0

/-- The wedge `z ↦ (fillFun k z) ∧ w` in the fixed chart `i`, as a continuous linear map. -/
def chartWedge (i : ι₁ × ι₂) (k : Fin 2) (y : lmPunct L M) :
    EuclideanSpace ℂ (Fin 1) →L[ℂ] EuclideanSpace ℂ (Fin 1) :=
  (chartWedgeScalar L M i k y) •
    ContinuousLinearMap.id ℂ (EuclideanSpace ℂ (Fin 1))

theorem continuousOn_chartWedgeScalar (i : ι₁ × ι₂) (k : Fin 2) :
    ContinuousOn (chartWedgeScalar L M i k) (chartSet L M i) :=
  ((continuousOn_const (c := (fillFun k oneVec) 0)).mul
      (continuousOn_chartCoord_apply L M i 1)).sub
    ((continuousOn_const (c := (fillFun k oneVec) 1)).mul
      (continuousOn_chartCoord_apply L M i 0))

theorem continuousOn_chartWedge (i : ι₁ × ι₂) (k : Fin 2) :
    ContinuousOn (chartWedge L M i k) (chartSet L M i) :=
  (continuousOn_chartWedgeScalar L M i k).smul continuousOn_const

/-! ## The fixed-chart expression of the wedge map is continuous -/

/-- Membership in a chart set, in terms of the base point. -/
theorem chartSet_iff (i : ι₁ × ι₂) (y : lmPunct L M) :
    y ∈ chartSet L M i ↔
      (y : (realification (lmSum L M)).TotalSpace).proj ∈ (lmSum L M).baseSet i := by
  show (y : (realification (lmSum L M)).TotalSpace) ∈
      ((realification (lmSum L M)).localTriv i).source ↔
    (y : (realification (lmSum L M)).TotalSpace).proj ∈ (lmSum L M).baseSet i
  rw [VectorBundleCore.mem_localTriv_source, realification_baseSet]

/-- The chart set of the sum contains the base set of the tautological quotient. -/
theorem baseSet_subset_chartSet (i : (ι₁ × ι₂) × Fin 2) :
    (lmQuot L M).baseSet i ⊆ chartSet L M i.1 := by
  intro y hy
  rw [chartSet_iff]
  rw [Work.Thom.tautQuotient_baseSet] at hy
  exact hy.1

/-- The base set of the tautological quotient is contained in the base set of the pullback of the
tensor product along the *first* index. -/
theorem baseSet_subset_tensSet (i : (ι₁ × ι₂) × Fin 2) :
    (lmQuot L M).baseSet i ⊆ (lmTens L M).baseSet i.1 := by
  intro y hy
  rw [Work.Thom.tautQuotient_baseSet] at hy
  rw [lmTens, Work.Thom.bundleComap_baseSet]
  rw [Work.Gen.tensorLine_baseSet, Work.Whitney.whitneySum_baseSet] at *
  exact hy.1

/-- **The fixed-chart expression of the wedge map is continuous.** -/
theorem continuousOn_fixedChart (i : (ι₁ × ι₂) × Fin 2) (i₂ : ι₁ × ι₂) :
    ContinuousOn (fun y : lmPunct L M =>
      (lmTens L M).coordChange i.1 i₂ y ∘SL chartWedge L M i.1 i.2 y)
      ((lmQuot L M).baseSet i ∩ (lmTens L M).baseSet i₂) :=
  ContinuousOn.clm_comp
    (((lmTens L M).continuousOn_coordChange i.1 i₂).mono
      (fun y hy => ⟨baseSet_subset_tensSet L M i hy.1, hy.2⟩))
    ((continuousOn_chartWedge L M i.1 i.2).mono
      (fun y hy => baseSet_subset_chartSet L M i hy.1))

/-! ## The linear algebra of the wedge under the sum's transition -/

/-- The wedge pairing `u ∧ w = u₀w₁ - u₁w₀` on the rank-`2` model fibre. -/
def wedge2 (u w : EuclideanSpace ℂ (Fin 2)) : ℂ := u 0 * w 1 - u 1 * w 0

/-- **The wedge transforms by the determinant** for a diagonal (`block-diagonal`) transition. -/
theorem wedge2_diag {a b : ℂ} {u w u' w' : EuclideanSpace ℂ (Fin 2)}
    (hu0 : u' 0 = a * u 0) (hu1 : u' 1 = b * u 1)
    (hw0 : w' 0 = a * w 0) (hw1 : w' 1 = b * w 1) :
    wedge2 u' w' = a * b * wedge2 u w := by
  rw [wedge2, wedge2, hu0, hu1, hw0, hw1]
  ring

/-! ## The coordinate form of the sum's transition -/

/-- The splitting `ℂ¹ × ℂ¹ → ℂ²` of the rank-`2` model fibre, as a continuous linear map. -/
abbrev sumPair : (EuclideanSpace ℂ (Fin 1) × EuclideanSpace ℂ (Fin 1)) →L[ℂ]
    EuclideanSpace ℂ (Fin 2) :=
  ↑(Work.Whitney.sumFibreC 1 1)

/-- The inverse splitting `ℂ² → ℂ¹ × ℂ¹`. -/
abbrev sumSplit : EuclideanSpace ℂ (Fin 2) →L[ℂ]
    (EuclideanSpace ℂ (Fin 1) × EuclideanSpace ℂ (Fin 1)) :=
  ↑((Work.Whitney.sumFibreC 1 1).symm)

/-- The sum decomposition of `v`. -/
theorem sumPair_sumSplit (v : EuclideanSpace ℂ (Fin 2)) :
    sumPair (sumSplit v) = v :=
  (Work.Whitney.sumFibreC 1 1).apply_symm_apply v

/-- **The sum's transition is diagonal in the splitting**: `coordChange p q x` acts by the first
factor's scalar on the first component and the second factor's scalar on the second. -/
theorem whitneySum_coordChange_eq_diag {ι₁ ι₂ : Type} [Fintype ι₁] [Fintype ι₂]
    (Z₁ : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin 1)) ι₁)
    (Z₂ : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin 1)) ι₂)
    (p q : ι₁ × ι₂) (x : B) (v : EuclideanSpace ℂ (Fin 2)) :
    (Work.Whitney.whitneySum (m₁ := 1) (m₂ := 1) Z₁ Z₂).coordChange p q x v
      = sumPair ((Z₁.coordChange p.1 q.1 x) (sumSplit v).1,
          (Z₂.coordChange p.2 q.2 x) (sumSplit v).2) := by
  rw [Work.Whitney.whitneySum_coordChange]
  rfl

/-- **The first coordinate of the sum's transition**: it is the first factor's scalar times the
first coordinate. -/
theorem whitneySum_coordChange_apply_zero {ι₁ ι₂ : Type} [Fintype ι₁] [Fintype ι₂]
    (Z₁ : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin 1)) ι₁)
    (Z₂ : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin 1)) ι₂)
    (p q : ι₁ × ι₂) (x : B) (v : EuclideanSpace ℂ (Fin 2)) :
    ((Work.Whitney.whitneySum (m₁ := 1) (m₂ := 1) Z₁ Z₂).coordChange p q x v).ofLp
      (0 : Fin 2) =
      Work.Gen.scl (Z₁.coordChange p.1 q.1 x) * (v.ofLp (0 : Fin 2)) := by
  rw [whitneySum_coordChange_eq_diag]
  rw [show (sumPair ((Z₁.coordChange p.1 q.1 x) (sumSplit v).1,
      (Z₂.coordChange p.2 q.2 x) (sumSplit v).2)).ofLp (0 : Fin 2)
      = ((Z₁.coordChange p.1 q.1 x) (sumSplit v).1).ofLp (0 : Fin 1) from
    Work.Whitney.WB.sumFibreC_apply_castAdd 0 0 _ _ (0 : Fin 1)]
  rw [Work.Gen.scl_smul_id (Z₁.coordChange p.1 q.1 x)]
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply, WithLp.ofLp_smul,
    Pi.smul_apply, smul_eq_mul]
  rw [show (sumSplit v).1.ofLp (0 : Fin 1) = v.ofLp (0 : Fin 2) from by
    rw [← Work.Whitney.WB.sumFibreC_apply_castAdd 0 0 (sumSplit v).1 (sumSplit v).2 (0 : Fin 1)]
    rw [← sumPair_sumSplit v]
    rfl]
  rw [Work.Gen.scl_smul, Work.Gen.scl_id, mul_one]

/-- **The second coordinate of the sum's transition**: it is the second factor's scalar times the
second coordinate. -/
theorem whitneySum_coordChange_apply_one {ι₁ ι₂ : Type} [Fintype ι₁] [Fintype ι₂]
    (Z₁ : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin 1)) ι₁)
    (Z₂ : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin 1)) ι₂)
    (p q : ι₁ × ι₂) (x : B) (v : EuclideanSpace ℂ (Fin 2)) :
    ((Work.Whitney.whitneySum (m₁ := 1) (m₂ := 1) Z₁ Z₂).coordChange p q x v).ofLp
      (1 : Fin 2) =
      Work.Gen.scl (Z₂.coordChange p.2 q.2 x) * (v.ofLp (1 : Fin 2)) := by
  rw [whitneySum_coordChange_eq_diag]
  rw [show (sumPair ((Z₁.coordChange p.1 q.1 x) (sumSplit v).1,
      (Z₂.coordChange p.2 q.2 x) (sumSplit v).2)).ofLp (1 : Fin 2)
      = ((Z₂.coordChange p.2 q.2 x) (sumSplit v).2).ofLp (0 : Fin 1) from
    Work.Whitney.WB.sumFibreC_apply_natAdd 0 0 _ _ (0 : Fin 1)]
  rw [Work.Gen.scl_smul_id (Z₂.coordChange p.2 q.2 x)]
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply, WithLp.ofLp_smul,
    Pi.smul_apply, smul_eq_mul]
  rw [show (sumSplit v).2.ofLp (0 : Fin 1) = v.ofLp (1 : Fin 2) from by
    rw [← Work.Whitney.WB.sumFibreC_apply_natAdd 0 0 (sumSplit v).1 (sumSplit v).2 (0 : Fin 1)]
    rw [← sumPair_sumSplit v]
    rfl]
  rw [Work.Gen.scl_smul, Work.Gen.scl_id, mul_one]

/-! ## The remaining computation for the pointwise identification (step (a))

The overlap identity (for `y ∈ Q.baseSet i₁ ∩ Z'.baseSet i₂`)

  `chartWedge i₁.1 i₁.2 y = (Z'.coordChange i₁.1 (Z'.indexAt y) y) ∘SL wedgeCLM y
      ∘SL (Q.coordChange i₁ (Q.indexAt y) y)`

is the statement that the wedge is chart-independent.  At the scalar level (all maps involved are
`c • id` on the rank-`1` fibres, and `Work.Gen.scl_comp` turns composition into multiplication of
scalars) it reads

  `scl (Z'.coordChange (Z'.indexAt y) i₁.1 y) * wedgeScalar y * scl (Q.coordChange i₁ (Q.indexAt y) y)
      = chartWedgeScalar i₁ y`

and the ingredients are: the transport of the wedge under the sum's *block-diagonal* transition
(`wedge2_diag` above — the determinant is the product of the two scalars), the unfolding of
`Q.coordChange` via `Work.Thom.tautQuotientCore_coordChange` (a `quoFun` along the tautological
section), the scalar of `Z'.coordChange` via `Work.Gen.tensorLine_coordChange`, and the two
cocycles `VectorBundleCore.coordChange_comp` / `coordChange_self`.

What is still needed for that computation, and was the point at which this stretch stopped: the
*coordinate form* of the sum's transition, i.e.
`(whitneySum Z₁ Z₂).coordChange p q x v` in the flat coordinates is `diag (scl A) (scl B)`.  The
statement is `rfl`-level (`(A.prodMap B) x = (A x.1, B x.2)` is `rfl`, and
`Work.Whitney.WB.sumFibreC_apply_castAdd` / `_natAdd` read off the `sumFibreC` coordinates), but
the elaboration needs the `sumFibreC`-coercions annotated explicitly (`((sumFibreC 1 1).symm :
EuclideanSpace ℂ (Fin 2) → EuclideanSpace ℂ (Fin 1) × EuclideanSpace ℂ (Fin 1))`) and the terms
kept light, otherwise `whnf`/`isDefEq` time out at the default heartbeat budget. -/

/-! ## The fibrewise map in the natural charts -/

/-- The `tqCoord`-th coordinate of the tautological section in the natural chart of `L ⊕ M`. -/
def wedgeCoeff (y : lmPunct L M) : ℂ :=
  (chartCoord L M ((lmSum L M).indexAt (y : (realification (lmSum L M)).TotalSpace).proj) y)
    (tqCoord (lmSum L M) y)

/-- The sign in the natural-chart expression of `v ↦ v ∧ s` (the wedge is `± z · w_k`). -/
def wedgeSign (y : lmPunct L M) : ℂ :=
  if ((tqCoord (lmSum L M) y : Fin 2) : ℕ) = 0 then -1 else 1

/-- The fibrewise scalar of the wedge isomorphism, read in the natural charts. -/
def wedgeScalar (y : lmPunct L M) : ℂ := wedgeSign L M y * wedgeCoeff L M y

/-- The fibrewise map of the wedge isomorphism. -/
def wedgeCLM (y : lmPunct L M) :
    EuclideanSpace ℂ (Fin 1) →L[ℂ] EuclideanSpace ℂ (Fin 1) :=
  (wedgeScalar L M y) • ContinuousLinearMap.id ℂ (EuclideanSpace ℂ (Fin 1))

/-! ## The `i₂`-cocycle: from the core identity to the overlap identity -/

/-- The cocycle of the transition functions of a line bundle, as an identity of continuous linear
maps. -/
theorem line_coordChange_comp_map {ι : Type} {Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin 1)) ι}
    (i j k : ι) (x : B) (hx : x ∈ Z.baseSet i ∩ Z.baseSet j ∩ Z.baseSet k) :
    Z.coordChange j k x ∘SL Z.coordChange i j x = Z.coordChange i k x := by
  ext v i'
  exact congrArg (fun w : EuclideanSpace ℂ (Fin 1) => w.ofLp i')
    (Z.coordChange_comp i j k x hx v)

/-- **The scalar cocycle** for a complex line bundle: the scalar of `coordChange i k` is the
product of the scalars of `coordChange i j` and `coordChange j k`. -/
theorem scl_coordChange_comp {ι : Type} {Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin 1)) ι}
    (i j k : ι) (x : B) (hx : x ∈ Z.baseSet i ∩ Z.baseSet j ∩ Z.baseSet k) :
    Work.Gen.scl (Z.coordChange i k x)
      = Work.Gen.scl (Z.coordChange i j x) * Work.Gen.scl (Z.coordChange j k x) := by
  rw [mul_comm (Work.Gen.scl (Z.coordChange i j x)) (Work.Gen.scl (Z.coordChange j k x))]
  rw [← Work.Gen.scl_comp (Z.coordChange j k x) (Z.coordChange i j x),
    line_coordChange_comp_map (Z := Z) i j k x hx]

/-- The cocycle for the tensor pullback, as an identity of linear maps. -/
theorem tens_coordChange_cocycle (i₁ : (ι₁ × ι₂) × Fin 2) (i₂ : ι₁ × ι₂) (y : lmPunct L M)
    (hy : y ∈ (lmQuot L M).baseSet i₁ ∩ (lmTens L M).baseSet i₂) :
    (lmTens L M).coordChange ((lmTens L M).indexAt y) i₂ y
      = (lmTens L M).coordChange i₁.1 i₂ y
        ∘SL (lmTens L M).coordChange ((lmTens L M).indexAt y) i₁.1 y := by
  ext v i'
  exact congrArg (fun w : EuclideanSpace ℂ (Fin 1) => w.ofLp i')
    ((lmTens L M).coordChange_comp ((lmTens L M).indexAt y) i₁.1 i₂ y
      ⟨⟨(lmTens L M).mem_baseSet_at y, baseSet_subset_tensSet L M i₁ hy.1⟩, hy.2⟩ v).symm

/-- **The overlap identity from the core identity** (the `i₂`-cocycle step). -/
theorem overlap_identity_of_core (i₁ : (ι₁ × ι₂) × Fin 2) (i₂ : ι₁ × ι₂) (y : lmPunct L M)
    (hy : y ∈ (lmQuot L M).baseSet i₁ ∩ (lmTens L M).baseSet i₂)
    (hcore : (lmTens L M).coordChange ((lmTens L M).indexAt y) i₁.1 y
        ∘SL (wedgeCLM L M y
          ∘SL (lmQuot L M).coordChange i₁ ((lmQuot L M).indexAt y) y)
      = chartWedge L M i₁.1 i₁.2 y) :
    (lmTens L M).coordChange ((lmTens L M).indexAt y) i₂ y
        ∘SL (wedgeCLM L M y
          ∘SL (lmQuot L M).coordChange i₁ ((lmQuot L M).indexAt y) y)
      = (lmTens L M).coordChange i₁.1 i₂ y ∘SL chartWedge L M i₁.1 i₁.2 y := by
  rw [tens_coordChange_cocycle L M i₁ i₂ y hy, ContinuousLinearMap.comp_assoc, hcore]

/-- **The determinant trick**: the tautological quotient of `L ⊕ M` is the pullback of `L ⊗ M`. -/
theorem tautQuotient_line_tensor :
    Nonempty (BundleIso (lmQuot L M) (lmTens L M)) := by
  sorry

end

end Work.Gen
