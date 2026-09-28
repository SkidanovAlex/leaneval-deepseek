import Mathlib
import Submission.Work.ThomBordism.Grassmann.EvalBundle

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000

/-!
# The evaluation of the tautological bundle vanishes exactly on the zero section

`Work.ThomBordism.Grassmann.evalVec` (`EvalBundle.lean`) attaches to a point of the total space of
the tautological oriented bundle `γ = tautologicalBundle k m` the vector of the plane it represents.
The incidence fibration `(P,w) ↦ w/‖w‖` lives on `zeroComplement γ`, so what the geometry below
needs first is that **`evalVec` vanishes exactly on the zero section**: the zero complement of `γ`
is the incidence space of pairs (oriented `k`-plane `P`, non-zero `w ∈ P`).

* `localTriv_snd_ne_zero` — for *any* real bundle, the fibre coordinate of a point in a chart
  vanishes iff the point is on the zero section (the transition functions are invertible).
* `evalChartO_eq_zero_iff`, `evalVec_eq_zero_iff`, `evalVec_ne_zero_of_mem_zeroComplement` —
  `evalVec p = 0 ↔ p ∉ zeroComplement γ`; so on `zeroComplement γ` the evaluation is nowhere zero
  and `evalVec p / ‖evalVec p‖` is a genuine point of the unit sphere.
-/

open Work.TangentClasses

namespace Work.TangentClasses

variable {B : Type*} [TopologicalSpace B] {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {ι : Type*}

/-- **The fibre coordinate in a chart vanishes iff the point is on the zero section.**  This is the
chart-independence of the zero section: the transition functions are invertible, hence preserve
`0`. -/
theorem localTriv_snd_ne_zero (Z : RealBundle B F ι) (S : ι) (p : Z.TotalSpace)
    (hpS : p.1 ∈ Z.baseSet S) :
    (show F from (Z.localTriv S p).2) ≠ 0 ↔ (show F from p.2) ≠ 0 := by
  have happly : (show F from (Z.localTriv S p).2)
      = Z.coordChange (Z.indexAt p.1) S p.1 (show F from p.2) :=
    congrArg (fun q : B × F => q.2) (VectorBundleCore.localTriv_apply Z (i := S) p)
  have hmem : p.1 ∈ Z.baseSet (Z.indexAt p.1) ∩ Z.baseSet S ∩ Z.baseSet (Z.indexAt p.1) :=
    ⟨⟨Z.mem_baseSet_at p.1, hpS⟩, Z.mem_baseSet_at p.1⟩
  have hright : ∀ v : F, Z.coordChange S (Z.indexAt p.1) p.1
      (Z.coordChange (Z.indexAt p.1) S p.1 v) = v := by
    intro v
    have h := VectorBundleCore.coordChange_comp Z (Z.indexAt p.1) S (Z.indexAt p.1) p.1 hmem v
    rw [VectorBundleCore.coordChange_self Z (Z.indexAt p.1) p.1 (Z.mem_baseSet_at p.1) v] at h
    exact h
  rw [happly]
  constructor
  · intro hv h0
    exact hv (by rw [h0, map_zero])
  · intro hv h0
    refine hv ?_
    calc (show F from p.2)
        = Z.coordChange S (Z.indexAt p.1) p.1
            (Z.coordChange (Z.indexAt p.1) S p.1 (show F from p.2)) :=
          (hright (show F from p.2)).symm
      _ = Z.coordChange S (Z.indexAt p.1) p.1 0 := by rw [h0]
      _ = 0 := map_zero _

/-- The same statement in the form used below: the coordinate vanishes iff the point is on the
zero section. -/
theorem localTriv_snd_eq_zero (Z : RealBundle B F ι) (S : ι) (p : Z.TotalSpace)
    (hpS : p.1 ∈ Z.baseSet S) :
    (show F from (Z.localTriv S p).2) = 0 ↔ (show F from p.2) = 0 := by
  constructor
  · intro h
    by_contra hv
    exact ((localTriv_snd_ne_zero Z S p hpS).mpr hv) h
  · intro h
    by_contra hv
    exact ((localTriv_snd_ne_zero Z S p hpS).mp hv) h

end Work.TangentClasses

namespace Work.ThomBordism.Grassmann

noncomputable section

variable {k m : ℕ}

/-- The zero complement of the tautological bundle, in the form used throughout this chapter. -/
abbrev incZero (k m : ℕ) : Set (tautologicalBundle k m).TotalSpace :=
  Work.Thom.zeroComplement (tautologicalBundle k m)

/-- **The oriented chart evaluation vanishes only on the zero coordinate.** -/
theorem evalChartO_eq_zero_iff (S : ChartIdx k m) (x : ↥(baseSet S)) (v : Amb k) :
    evalChartO S x v = 0 ↔ v = 0 := by
  obtain ⟨f, hf⟩ : ∃ f : Stiefel k m, Quotient.mk'' f = (x : OG k m) := Quotient.exists_rep _
  have hfc : f ∈ chartSet S := (mem_baseSet_iff S f).mp (hf ▸ x.2)
  have h1 : evalChartO S x v = coordEval S f (matLin (orientMat S (x : OG k m)) v) := by
    rw [evalChartO, evalChart_spec S x f hfc hf.symm]
  have hinv : ∀ w : Amb k,
      matLin (orientMat S (x : OG k m)) (matLin (orientMat S (x : OG k m)) w) = w := by
    intro w
    rw [← ContinuousLinearMap.comp_apply, ← matLin_mul]
    rw [orientMat_mul_self (S := S) (x := (x : OG k m)) x.2]
    exact congrFun (congrArg DFunLike.coe matLin_one) w
  rw [h1, coordEval_eq_zero_iff S f _ hfc]
  constructor
  · intro h
    have h2 : v = 0 := by
      conv_lhs => rw [← hinv v]
      rw [h, map_zero]
    exact h2
  · intro h
    rw [h, map_zero]

/-- **The evaluation of the tautological bundle vanishes exactly on the zero section.** -/
theorem evalVec_eq_zero_iff (p : (tautologicalBundle k m).TotalSpace) :
    evalVec p = 0 ↔ (show Amb k from p.2) = 0 := by
  have hS : p.1 ∈ (tautologicalBundle k m).baseSet ((tautologicalBundle k m).indexAt p.1) :=
    (tautologicalBundle k m).mem_baseSet_at p.1
  constructor
  · intro h
    by_contra hp2
    exact ((localTriv_snd_ne_zero (tautologicalBundle k m)
      ((tautologicalBundle k m).indexAt p.1) p hS).mpr hp2)
      (by rw [evalVec_apply_chart p _ hS, evalChartO_eq_zero_iff] at h; exact h)
  · intro h
    rw [evalVec_apply_chart p _ hS, evalChartO_eq_zero_iff]
    by_contra hc
    exact ((localTriv_snd_ne_zero (tautologicalBundle k m)
      ((tautologicalBundle k m).indexAt p.1) p hS).mp hc) h

/-- **On the zero complement, the evaluation is nowhere zero.** -/
theorem evalVec_ne_zero_of_mem_zeroComplement (p : (tautologicalBundle k m).TotalSpace)
    (hp : p ∈ incZero k m) : evalVec p ≠ 0 := by
  intro h
  exact (Work.Thom.mem_zeroComplement p).mp hp ((evalVec_eq_zero_iff p).mp h)

end

end Work.ThomBordism.Grassmann

