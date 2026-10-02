import Mathlib
import Submission.Work.Milnor.Base
import Submission.Work.Milnor.Construction
import Submission.Work.CharacteristicClasses.Invariants
import Submission.Work.TangentClasses.Bundle

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

open scoped Manifold ContDiff Topology
open TopologicalSpace Set

/-!
# The two-chart description of the bundles `L^a R^b` over `S⁴ = OnePoint ℝ⁴`

`S⁴ = OnePoint (EuclideanSpace ℝ (Fin 4))` is described by two charts: the finite part
`hemi0 = {p | p ≠ ∞}` (coordinate `coord0`) and the complement of the origin
`hemi1 = {p | p ≠ ↑0}`.  Over these two charts the rank-`4` real bundle `L^a R^b`
(clutching `q ↦ (v ↦ q^a v q^b)`; Milnor's `ξ = L²R⁻¹` is the case `(a,b) = (2,-1)`) is trivial;
this file records it as *gluing data* (`Work.TangentClasses.RealBundle S4 ℝ⁴ (Fin 2)`) so that the
characteristic-class machinery of the `Thom` chapter applies to it.  This is the missing "home" of
the bundles of `Submission/Work/CharacteristicClasses/` (whose `SpinBundle` records only the
*coefficients*).
-/

namespace Work.Agree

open Work.TangentClasses

noncomputable section

/-- `S⁴ = OnePoint ℝ⁴`, the base of Milnor's bundles. -/
abbrev S4 := Submission.Milnor.S4

/-- **The finite hemisphere** of `S⁴ = ℝ⁴ ∪ {∞}`. -/
def hemi0 : Set S4 := {p | p ≠ OnePoint.infty}

/-- **The second hemisphere**: the complement of the origin `↑0`. -/
def hemi1 : Set S4 := {p | p ≠ (↑(0 : EuclideanSpace ℝ (Fin 4)) : S4)}

lemma isOpen_hemi0 : IsOpen hemi0 := by
  have h : hemi0 = Set.range (Option.some : EuclideanSpace ℝ (Fin 4) → S4) := by
    ext p; constructor
    · intro hp
      obtain ⟨x, rfl⟩ := Option.ne_none_iff_exists'.mp hp
      exact ⟨x, rfl⟩
    · rintro ⟨x, rfl⟩
      exact Option.some_ne_none x
  rw [h]; exact OnePoint.isOpenEmbedding_coe.isOpen_range

lemma isOpen_hemi1 : IsOpen hemi1 := by
  have h : hemi1 = ({((0 : EuclideanSpace ℝ (Fin 4)) : S4)} : Set S4)ᶜ := rfl
  rw [h]; exact isClosed_singleton.isOpen_compl

/-- **The first chart coordinate** of a point of `S⁴` (the junk value `0` at `∞`). -/
def coord0 (p : S4) : EuclideanSpace ℝ (Fin 4) := p.getD 0

@[simp] lemma coord0_some (x : EuclideanSpace ℝ (Fin 4)) : coord0 (↑x : S4) = x := rfl

lemma coord0_mem {p : S4} (hp : p ∈ hemi0) : (coord0 p : S4) = p := by
  obtain ⟨x, rfl⟩ := Option.ne_none_iff_exists'.mp hp
  rfl

lemma coord0_ne_zero {p : S4} (hp0 : p ∈ hemi0) (hp1 : p ∈ hemi1) : coord0 p ≠ 0 := by
  intro h
  exact hp1 (by rw [← coord0_mem hp0, h])

lemma continuous_coord0 : Continuous fun p : ↥hemi0 => coord0 (p : S4) := by
  have h : Continuous fun p : ↥hemi0 => ((coord0 (p : S4) : S4)) := by
    have hfun : (fun p : ↥hemi0 => ((coord0 (p : S4) : S4))) = fun p : ↥hemi0 => (p : S4) := by
      funext p; exact coord0_mem p.2
    rw [hfun]; exact continuous_subtype_val
  exact OnePoint.isOpenEmbedding_coe.isEmbedding.continuous_iff.mpr h

/-! ## The clutching twist `v ↦ q^a v q^b` -/

/-- The linear isometry `ℝ⁴ → ℍ`, as a continuous linear map. -/
def toQ : EuclideanSpace ℝ (Fin 4) →L[ℝ] Quaternion ℝ :=
  LinearMap.toContinuousLinearMap
    (Quaternion.linearIsometryEquivTuple.symm : EuclideanSpace ℝ (Fin 4) →ₗ[ℝ] Quaternion ℝ)

/-- The linear isometry `ℍ → ℝ⁴`, as a continuous linear map. -/
def ofQ : Quaternion ℝ →L[ℝ] EuclideanSpace ℝ (Fin 4) :=
  LinearMap.toContinuousLinearMap
    (Quaternion.linearIsometryEquivTuple : Quaternion ℝ →ₗ[ℝ] EuclideanSpace ℝ (Fin 4))

@[simp] lemma ofQ_toQ (x : EuclideanSpace ℝ (Fin 4)) : ofQ (toQ x) = x :=
  Quaternion.linearIsometryEquivTuple.apply_symm_apply x

@[simp] lemma toQ_ofQ (x : Quaternion ℝ) : toQ (ofQ x) = x :=
  Quaternion.linearIsometryEquivTuple.symm_apply_apply x

lemma ofQ_comp_toQ : ofQ.comp toQ = 1 := by
  apply ContinuousLinearMap.ext
  intro x
  exact ofQ_toQ x

lemma toQ_comp_ofQ : toQ.comp ofQ = 1 := by
  apply ContinuousLinearMap.ext
  intro x
  exact toQ_ofQ x

/-- **The real-linear map `v ↦ q^a v q^b` of `ℍ ≅ ℝ⁴`**, in the standard fibre `ℝ⁴`. -/
def qTwist (a b : ℤ) (q : Quaternion ℝ) : EuclideanSpace ℝ (Fin 4) →L[ℝ]
    EuclideanSpace ℝ (Fin 4) :=
  (ofQ.comp (((ContinuousLinearMap.mul ℝ (Quaternion ℝ)).flip (q ^ b)).comp
    ((ContinuousLinearMap.mul ℝ (Quaternion ℝ)) (q ^ a)))).comp toQ

@[simp] lemma qTwist_apply (a b : ℤ) (q : Quaternion ℝ) (v : EuclideanSpace ℝ (Fin 4)) :
    qTwist a b q v = ofQ (q ^ a * toQ v * q ^ b) := rfl

lemma qTwist_inv (a b : ℤ) (q : Quaternion ℝ) (hq : q ≠ 0) :
    (qTwist a b q).comp (qTwist (-a) (-b) q) = 1 := by
  apply ContinuousLinearMap.ext
  intro v
  show ofQ (q ^ a * toQ (ofQ (q ^ (-a) * toQ v * q ^ (-b))) * q ^ b) = v
  rw [toQ_ofQ, zpow_neg, zpow_neg]
  rw [show q ^ a * ((q ^ a)⁻¹ * toQ v * (q ^ b)⁻¹) * q ^ b = toQ v by
    rw [← mul_assoc (q ^ a) ((q ^ a)⁻¹ * toQ v) ((q ^ b)⁻¹),
        ← mul_assoc (q ^ a) ((q ^ a)⁻¹) (toQ v),
        mul_inv_cancel₀ (zpow_ne_zero a hq), one_mul,
        mul_assoc (toQ v) ((q ^ b)⁻¹) (q ^ b),
        inv_mul_cancel₀ (zpow_ne_zero b hq), mul_one]]
  exact ofQ_toQ v

end

end Work.Agree






namespace Work.Agree
open Work.TangentClasses

noncomputable section

open Classical

/-- **The clutching direction** at a point of `S⁴`, as a unit quaternion: the value of
`Submission.Milnor.unitDir` at the first-chart coordinate.  (Its value at `∞` is the junk value
`1`, which is never used.) -/
def uDir (p : S4) : Quaternion ℝ :=
  ((Submission.Milnor.unitDir (coord0 p) : Submission.Milnor.QS3) : Quaternion ℝ)

@[simp] lemma uDir_coe (x : EuclideanSpace ℝ (Fin 4)) :
    uDir (↑x : S4) = ((Submission.Milnor.unitDir x : Submission.Milnor.QS3) : Quaternion ℝ) :=
  rfl

lemma uDir_ne_zero (p : S4) : uDir p ≠ 0 := by
  have h : uDir p ∈ Metric.sphere (0 : Quaternion ℝ) 1 :=
    (Submission.Milnor.unitDir (coord0 p)).2
  rw [Metric.mem_sphere, dist_zero_right] at h
  intro h0
  rw [h0, norm_zero] at h
  norm_num at h

/-- On the overlap of the two charts the clutching direction is the unit direction of the
coordinate: the value of `Work.Milnor.dirVal`. -/
lemma uDir_eq_dirVal {p : S4} (hp0 : p ∈ hemi0) (hp1 : p ∈ hemi1) :
    uDir p = Work.Milnor.dirVal (coord0 p) :=
  Work.Milnor.unitDir_coe (coord0 p) (coord0_ne_zero hp0 hp1)

lemma continuousOn_coord0 : ContinuousOn (fun p : S4 => coord0 p) hemi0 :=
  continuousOn_iff_continuous_domRestrict.mpr continuous_coord0

lemma continuousOn_dirVal : ContinuousOn Work.Milnor.dirVal
    {x : EuclideanSpace ℝ (Fin 4) | x ≠ 0} :=
  Work.Milnor.dirVal_contMDiffOn.continuousOn

lemma continuousOn_dirAt : ContinuousOn (fun p : S4 => Work.Milnor.dirVal (coord0 p))
    (hemi0 ∩ hemi1) :=
  continuousOn_dirVal.comp (continuousOn_coord0.mono Set.inter_subset_left)
    (fun p hp => coord0_ne_zero hp.1 hp.2)

lemma continuousOn_uDir : ContinuousOn uDir (hemi0 ∩ hemi1) :=
  continuousOn_dirAt.congr (fun p hp => uDir_eq_dirVal hp.1 hp.2)

/-- Continuity of the twist in the quaternion variable. -/
lemma continuousOn_qTwist (a b : ℤ) :
    ContinuousOn (fun q : Quaternion ℝ => qTwist a b q) {q : Quaternion ℝ | q ≠ 0} := by
  have hpowa : ContinuousOn (fun q : Quaternion ℝ => q ^ a) {q : Quaternion ℝ | q ≠ 0} :=
    continuousOn_id.zpow₀ a (fun q hq => Or.inl hq)
  have hpowb : ContinuousOn (fun q : Quaternion ℝ => q ^ b) {q : Quaternion ℝ | q ≠ 0} :=
    continuousOn_id.zpow₀ b (fun q hq => Or.inl hq)
  have hB : ContinuousOn (fun q : Quaternion ℝ =>
      (ContinuousLinearMap.mul ℝ (Quaternion ℝ)) (q ^ a)) {q : Quaternion ℝ | q ≠ 0} :=
    (ContinuousLinearMap.mul ℝ (Quaternion ℝ)).continuous.comp_continuousOn hpowa
  have hC : ContinuousOn (fun q : Quaternion ℝ =>
      (ContinuousLinearMap.mul ℝ (Quaternion ℝ)).flip (q ^ b)) {q : Quaternion ℝ | q ≠ 0} :=
    ((ContinuousLinearMap.mul ℝ (Quaternion ℝ)).flip).continuous.comp_continuousOn hpowb
  have hBC := hC.clm_comp hB
  have h1 : ContinuousOn (fun q : Quaternion ℝ => ofQ.comp
      (((ContinuousLinearMap.mul ℝ (Quaternion ℝ)).flip (q ^ b)).comp
        ((ContinuousLinearMap.mul ℝ (Quaternion ℝ)) (q ^ a)))) {q : Quaternion ℝ | q ≠ 0} :=
    continuousOn_const.clm_comp hBC
  have h2 : ContinuousOn (fun q : Quaternion ℝ => (ofQ.comp
      (((ContinuousLinearMap.mul ℝ (Quaternion ℝ)).flip (q ^ b)).comp
        ((ContinuousLinearMap.mul ℝ (Quaternion ℝ)) (q ^ a)))).comp toQ)
      {q : Quaternion ℝ | q ≠ 0} :=
    h1.clm_comp continuousOn_const
  exact h2

/-- **The four transition functions** of the two-chart description of `L^a R^b`. -/
def ct (a b : ℤ) (i j : Bool) (p : S4) : EuclideanSpace ℝ (Fin 4) →L[ℝ]
    EuclideanSpace ℝ (Fin 4) :=
  match i, j with
  | false, false => 1
  | false, true => qTwist a b (uDir p)
  | true, false => qTwist (-a) (-b) (uDir p)
  | true, true => 1

lemma ct_false_true (a b : ℤ) (p : S4) : ct a b false true p = qTwist a b (uDir p) := rfl
lemma ct_true_false (a b : ℤ) (p : S4) : ct a b true false p = qTwist (-a) (-b) (uDir p) := rfl
lemma ct_self (a b : ℤ) (i : Bool) (p : S4) : ct a b i i p = 1 := by cases i <;> rfl

lemma ct_continuousOn (a b : ℤ) (i j : Bool) : ContinuousOn (ct a b i j)
    ((if i then hemi1 else hemi0) ∩ (if j then hemi1 else hemi0)) := by
  cases i <;> cases j <;> simp only [ct, Bool.false_eq_true, reduceIte]
  · exact continuousOn_const
  · exact (continuousOn_qTwist a b).comp continuousOn_uDir (fun p _ => uDir_ne_zero p)
  · exact (continuousOn_qTwist (-a) (-b)).comp
      (continuousOn_uDir.mono (le_of_eq (Set.inter_comm hemi1 hemi0)))
      (fun p _ => uDir_ne_zero p)
  · exact continuousOn_const

/-- **The rank-`4` real bundle `L^a R^b` over `S⁴ = ℝ⁴ ∪ {∞}`**, in the two-chart description:
trivial over the two hemispheres, with the clutching `q ↦ (v ↦ q^a v q^b)` on the overlap.  For
`(a,b) = (2,-1)` this is Milnor's `ξ = L²R⁻¹`. -/
def clutchBundle (a b : ℤ) : RealBundle S4 (EuclideanSpace ℝ (Fin 4)) Bool where
  baseSet i := if i then hemi1 else hemi0
  isOpen_baseSet i := by cases i <;> simp [isOpen_hemi0, isOpen_hemi1]
  indexAt p := if p = OnePoint.infty then true else false
  mem_baseSet_at p := by
    by_cases hp : p = OnePoint.infty
    · rw [hp]; simp [hemi1]
    · simp [hemi0, hp]
  coordChange i j p := ct a b i j p
  coordChange_self i p hp v := by rw [ct_self]; rfl
  continuousOn_coordChange i j := ct_continuousOn a b i j
  coordChange_comp i j l p hp v := by
    have hq : uDir p ≠ 0 := uDir_ne_zero p
    have h1 : ∀ w : EuclideanSpace ℝ (Fin 4),
        ct a b true false p (ct a b false true p w) = w := by
      intro w
      simp only [ct_true_false, ct_false_true]
      have h := qTwist_inv (-a) (-b) (uDir p) hq
      rw [show (-(-a) : ℤ) = a from neg_neg a, show (-(-b) : ℤ) = b from neg_neg b] at h
      exact congrArg (fun f : EuclideanSpace ℝ (Fin 4) →L[ℝ] EuclideanSpace ℝ (Fin 4) => f w) h
    have h2 : ∀ w : EuclideanSpace ℝ (Fin 4),
        ct a b false true p (ct a b true false p w) = w := by
      intro w
      simp only [ct_true_false, ct_false_true]
      exact congrArg (fun f : EuclideanSpace ℝ (Fin 4) →L[ℝ] EuclideanSpace ℝ (Fin 4) => f w)
        (qTwist_inv a b (uDir p) hq)
    cases i <;> cases j <;> cases l <;> first | rfl | exact h1 v | exact h2 v

@[simp] lemma clutchBundle_baseSet (a b : ℤ) (i : Bool) :
    (clutchBundle a b).baseSet i = if i then hemi1 else hemi0 := rfl

@[simp] lemma clutchBundle_coordChange (a b : ℤ) (i j : Bool) (p : S4) :
    (clutchBundle a b).coordChange i j p = ct a b i j p := rfl

@[simp] lemma clutchBundle_coordChange_false_true (a b : ℤ) (p : S4) :
    (clutchBundle a b).coordChange false true p = qTwist a b (uDir p) := rfl

@[simp] lemma clutchBundle_coordChange_true_false (a b : ℤ) (p : S4) :
    (clutchBundle a b).coordChange true false p = qTwist (-a) (-b) (uDir p) := rfl

end

end Work.Agree
