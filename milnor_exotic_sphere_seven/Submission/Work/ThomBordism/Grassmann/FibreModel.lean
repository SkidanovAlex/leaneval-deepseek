import Mathlib
import Submission.Work.ThomBordism.Grassmann.UpSetRetract

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false

/-!
# The fibre over `baseVec` as `(0,∞) × {planes containing baseVec}`

The fibre `fibreVec k m` of the incidence fibration over `baseVec` is the product of `(0,∞)` (the
norm of the vector of the plane) with the space `planeBaseSet k m` of oriented `k`-planes
containing `baseVec`, which in turn is homeomorphic to `OG (k-1) m` (`fibreBaseHomeomorph`).
-/

open scoped Topology
open unitInterval CategoryTheory

namespace Work.ThomBordism.Grassmann

noncomputable section

variable {k m : ℕ}

/-- The space of oriented `k`-planes of `Amb (k+m)` containing `baseVec`. -/
abbrev planeBaseSet (k m : ℕ) : Set (OG k m) := {P | memPlane P (baseVec k m)}

theorem baseVec_ne_zero {k m : ℕ} (hm : 1 ≤ m) : baseVec k m ≠ 0 := by
  intro h
  have := norm_baseVec (k := k) (m := m) (by omega)
  rw [h, norm_zero] at this
  exact one_ne_zero this.symm

theorem smul_baseVec_ne_zero {k m : ℕ} (hm : 1 ≤ m) {c : ℝ} (hc : 0 < c) :
    c • baseVec k m ≠ 0 :=
  smul_ne_zero (ne_of_gt hc) (baseVec_ne_zero hm)

/-- `baseVec` lies in the plane of a point of the fibre. -/
theorem memPlane_baseVec_of_mem_fibreVec {k m : ℕ} (hm : 1 ≤ m) {x : ↥(incZero k m)}
    (hx : x ∈ fibreVec k m) : memPlane x.1.1 (baseVec k m) := by
  obtain ⟨f, hf, hw⟩ := evalVec_memPlane x.1
  refine ⟨f, hf, ?_⟩
  have hn : 0 < ‖evalVec x.1‖ :=
    norm_pos_iff.mpr (evalVec_ne_zero_of_mem_zeroComplement _ x.2)
  have hsm : evalVec x.1 = ‖evalVec x.1‖ • baseVec k m := evalVec_eq_smul_baseVec hx
  have hpos : (‖evalVec x.1‖)⁻¹ • evalVec x.1 = baseVec k m := by
    rw [hsm, norm_smul, Real.norm_eq_abs, abs_of_pos hn, norm_baseVec (by omega), mul_one]
    rw [smul_smul, inv_mul_cancel₀ (ne_of_gt hn), one_smul]
  rw [← hpos]
  exact Submodule.smul_mem _ _ hw

/-- `k • baseVec` lies in a plane containing `baseVec`. -/
theorem memPlane_smul_baseVec_of_mem_planeBaseSet {k m : ℕ} {c : ℝ}
    {P : OG k m} (hP : memPlane P (baseVec k m)) : memPlane P (c • baseVec k m) := by
  obtain ⟨f, hf, hw⟩ := hP
  exact ⟨f, hf, Submodule.smul_mem _ _ hw⟩

/-- The norm component of the model map. -/
def fibreNormMap (x : ↥(fibreVec k m)) : {c : ℝ // 0 < c} :=
  ⟨‖evalVec x.1.1‖, norm_pos_iff.mpr (evalVec_ne_zero_of_mem_zeroComplement _ x.1.2)⟩

/-- **The fibre over `baseVec` is `(0,∞) × {planes containing baseVec}`.** -/
def fibreModelMap (hm : 1 ≤ m) (x : ↥(fibreVec k m)) :
    {c : ℝ // 0 < c} × ↥(planeBaseSet k m) :=
  (fibreNormMap x, ⟨x.1.1.1, memPlane_baseVec_of_mem_fibreVec hm x.2⟩)

/-- The inverse of `fibreModelMap`: put the plane `P` together with the vector `c • baseVec`. -/
def fibreModelInv (hm : 1 ≤ m) (q : {c : ℝ // 0 < c} × ↥(planeBaseSet k m)) : ↥(fibreVec k m) :=
  ⟨toE q.2.1 (q.1.1 • baseVec k m) (smul_baseVec_ne_zero hm q.1.2)
      (memPlane_smul_baseVec_of_mem_planeBaseSet q.2.2), by
    show dirVec (toE q.2.1 (q.1.1 • baseVec k m) _ _) = baseVec k m
    rw [dirVec, evalVec_toE, norm_smul, Real.norm_eq_abs, abs_of_pos q.1.2,
      norm_baseVec (by omega), mul_one, smul_smul, inv_mul_cancel₀ (ne_of_gt q.1.2), one_smul]⟩

theorem fibreModelInv_map (hm : 1 ≤ m) (x : ↥(fibreVec k m)) :
    fibreModelInv hm (fibreModelMap hm x) = x := by
  refine Subtype.ext ?_
  show toE x.1.1.1 (‖evalVec x.1.1‖ • baseVec k m)
    (smul_baseVec_ne_zero hm (norm_pos_iff.mpr
      (evalVec_ne_zero_of_mem_zeroComplement _ x.1.2)))
    (memPlane_smul_baseVec_of_mem_planeBaseSet (memPlane_baseVec_of_mem_fibreVec hm x.2))
    = (x : ↥(incZero k m))
  exact (toE_congr rfl (evalVec_eq_smul_baseVec x.2).symm _ _
      (evalVec_ne_zero_of_mem_zeroComplement _ x.1.2) (evalVec_memPlane _)).trans
    (toE_self (x : ↥(incZero k m)))

theorem fibreModelMap_inv (hm : 1 ≤ m) (q : {c : ℝ // 0 < c} × ↥(planeBaseSet k m)) :
    fibreModelMap hm (fibreModelInv hm q) = q := by
  refine Prod.ext (Subtype.ext ?_) (Subtype.ext ?_)
  · show ‖evalVec (toE q.2.1 (q.1.1 • baseVec k m) (smul_baseVec_ne_zero hm q.1.2)
        (memPlane_smul_baseVec_of_mem_planeBaseSet q.2.2)).1‖ = q.1.1
    rw [evalVec_toE, norm_smul, Real.norm_eq_abs, abs_of_pos q.1.2,
      norm_baseVec (by omega), mul_one]
  · rfl

theorem continuous_fibreNormMap : Continuous fun x : ↥(fibreVec k m) => fibreNormMap x := by
  have h1 : Continuous fun x : ↥(fibreVec k m) => (x : ↥(incZero k m)) := continuous_subtype_val
  have h2 : Continuous fun z : ↥(incZero k m) => (z : (tautologicalBundle k m).TotalSpace) :=
    continuous_subtype_val
  have h3 : Continuous fun x : ↥(fibreVec k m) => evalVec x.1.1 :=
    continuous_evalVec.comp (h2.comp h1)
  exact Continuous.subtype_mk h3.norm _

theorem continuous_fibreModelMap (hm : 1 ≤ m) :
    Continuous fun x : ↥(fibreVec k m) => fibreModelMap hm x := by
  have h1 : Continuous fun x : ↥(fibreVec k m) => (x : ↥(incZero k m)) := continuous_subtype_val
  have h2 : Continuous fun z : ↥(incZero k m) => (z : (tautologicalBundle k m).TotalSpace) :=
    continuous_subtype_val
  have h3 : Continuous fun x : ↥(fibreVec k m) => x.1.1 := h2.comp h1
  have h4 : Continuous fun x : ↥(fibreVec k m) =>
      (⟨x.1.1.1, memPlane_baseVec_of_mem_fibreVec hm x.2⟩ : ↥(planeBaseSet k m)) :=
    Continuous.subtype_mk
      ((VectorBundleCore.continuous_proj (tautologicalBundle k m)).comp h3) _
  exact (continuous_fibreNormMap (k := k) (m := m)).prodMk h4

theorem continuous_fibreModelInv (hm : 1 ≤ m) :
    Continuous fun q : {c : ℝ // 0 < c} × ↥(planeBaseSet k m) => fibreModelInv hm q := by
  refine Continuous.subtype_mk ?_ _
  have hfst : Continuous fun q : {c : ℝ // 0 < c} × ↥(planeBaseSet k m) => q.1 := continuous_fst
  have hsnd : Continuous fun q : {c : ℝ // 0 < c} × ↥(planeBaseSet k m) => q.2 := continuous_snd
  have hproj : Continuous fun q : {c : ℝ // 0 < c} × ↥(planeBaseSet k m) => (q.2.1 : OG k m) :=
    continuous_subtype_val.comp hsnd
  have hval : Continuous fun q : {c : ℝ // 0 < c} × ↥(planeBaseSet k m) => q.1.1 :=
    continuous_subtype_val.comp hfst
  have hconst : Continuous fun _ : {c : ℝ // 0 < c} × ↥(planeBaseSet k m) => baseVec k m :=
    continuous_const
  have hbase : Continuous fun q : {c : ℝ // 0 < c} × ↥(planeBaseSet k m) =>
      ((q.2.1 : OG k m), q.1.1 • baseVec k m) := hproj.prodMk (hval.smul hconst)
  have hmem : ∀ q : {c : ℝ // 0 < c} × ↥(planeBaseSet k m),
      ((q.2.1 : OG k m), q.1.1 • baseVec k m) ∈
        {q : OG k m × Amb (k+m) | q.2 ≠ 0 ∧ memPlane q.1 q.2} :=
    fun q => ⟨smul_baseVec_ne_zero hm q.1.2, memPlane_smul_baseVec_of_mem_planeBaseSet q.2.2⟩
  have hcont : Continuous fun q : {c : ℝ // 0 < c} × ↥(planeBaseSet k m) =>
      mkTotal q.2.1 (toECoordAt ((tautologicalBundle k m).indexAt q.2.1) q.2.1
        (q.1.1 • baseVec k m)) :=
    continuousOn_toE_underlying.comp_continuous hbase hmem
  refine (hcont.subtype_mk fun q => ?_).congr fun q => ?_
  · show toECoordAt ((tautologicalBundle k m).indexAt q.2.1) q.2.1 (q.1.1 • baseVec k m) ≠ 0
    exact toECoordAt_ne_zero _ _ ((tautologicalBundle k m).mem_baseSet_at _) _
      (smul_baseVec_ne_zero hm q.1.2) (memPlane_smul_baseVec_of_mem_planeBaseSet q.2.2)
  · rfl

/-- **The homeomorphism `fibreVec k m ≃ (0,∞) × planeBaseSet k m`.** -/
noncomputable def fibreModelHomeomorph (hm : 1 ≤ m) :
    ↥(fibreVec k m) ≃ₜ {c : ℝ // 0 < c} × ↥(planeBaseSet k m) where
  toEquiv :=
    { toFun := fibreModelMap hm
      invFun := fibreModelInv hm
      left_inv := fibreModelInv_map hm
      right_inv := fibreModelMap_inv hm }
  continuous_toFun := continuous_fibreModelMap hm
  continuous_invFun := continuous_fibreModelInv hm

end

end Work.ThomBordism.Grassmann
