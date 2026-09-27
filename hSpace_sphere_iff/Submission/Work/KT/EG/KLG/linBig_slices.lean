import Mathlib
import Submission.Work.KT.EG.KLG.linBig_defs

/-!
# `Work.KT.EG.KLG.linBig_slices`

The two end slices of the linear deformation `linBig` (Hatcher, *Vector Bundles and K-Theory*,
Prop. 2.7).  At `t = 0` the homotopy `z • (a + t t₀ • b) + t t₀ • a + b` specialises to the
original linear clutching function `z • a + b`, and at `t = 1` it specialises to the "reduced"
linear clutching function `z • (a + t₀ • b) + (t₀ • a + b)`.  Both statements are pointwise
computations, reducing the cylinder coordinates `z`, `t` and the constant `t₀` along the two
inclusions `incl0`, `incl1`.
-/

namespace Work.KT.EG.KLG

open Matrix

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

/-! ## Evaluating the cylinder coordinates along the two inclusions -/

@[simp] lemma linBig_zCyl_apply (X : Type) [TopologicalSpace X] [CompactSpace X] [T2Space X]
    (q : (X × unitInterval) × Sph ℂ) : Work.KT.EG.zCyl X q = (q.2 : ℂ) := rfl

@[simp] lemma linBig_unitInterval_coe_one : ((1 : unitInterval) : ℝ) = 1 := rfl
@[simp] lemma linBig_unitInterval_coe_zero : ((0 : unitInterval) : ℝ) = 0 := rfl

@[simp] lemma linBig_inc0_apply (X : Type) [TopologicalSpace X]
    (p : X × Sph ℂ) : Work.KT.Fund.incl0 X p = ((p.1, 0), p.2) := rfl

@[simp] lemma linBig_inc1_apply (X : Type) [TopologicalSpace X]
    (p : X × Sph ℂ) : Work.KT.Fund.incl1 X p = ((p.1, 1), p.2) := rfl

@[simp] lemma linBig_cylConst_apply (X : Type) [TopologicalSpace X] (t : ℝ)
    (q : (X × unitInterval) × Sph ℂ) :
    (cylConst t : C((X × unitInterval) × Sph ℂ, ℂ)) q = (t : ℂ) := by
  simp [cylConst]

/-! ## The two slices -/

theorem linBig_slices (X : Type) [TopologicalSpace X] [CompactSpace X] [T2Space X] {n : ℕ}
    (a b : Matrix (Fin n) (Fin n) C(X, ℂ)) (t₀ : ℝ) :
    (Work.KT.EG.KLG.linBig X a b t₀).map (fun f => f.comp (Work.KT.Fund.incl0 X))
        = (Work.KT.zUnit X : C(X × Sph ℂ, ℂ)) • Work.KT.Fund.pullMat X a
          + Work.KT.Fund.pullMat X b
      ∧ (Work.KT.EG.KLG.linBig X a b t₀).map (fun f => f.comp (Work.KT.Fund.incl1 X))
        = (Work.KT.zUnit X : C(X × Sph ℂ, ℂ)) • Work.KT.Fund.pullMat X (a + t₀ • b)
          + Work.KT.Fund.pullMat X (t₀ • a + b) := by
  constructor
  · refine Matrix.ext fun i j => ?_
    ext p
    simp only [linBig, Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply,
      Work.KT.EG.pullBig_apply, Work.KT.Fund.pullMat_apply, ContinuousMap.add_apply,
      ContinuousMap.mul_apply, ContinuousMap.comp_apply, Work.KT.EG.zCyl,
      Work.KT.EG.tCyl_apply, Work.KT.zUnit_apply, linBig_cylConst_apply, linBig_inc0_apply,
      linBig_unitInterval_coe_zero, Complex.ofReal_zero, zero_mul, mul_zero, add_zero,
      smul_eq_mul]
  · refine Matrix.ext fun i j => ?_
    ext p
    simp only [linBig, Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply,
      Work.KT.EG.pullBig_apply, Work.KT.Fund.pullMat_apply, ContinuousMap.add_apply,
      ContinuousMap.mul_apply, ContinuousMap.comp_apply, Work.KT.EG.zCyl,
      Work.KT.EG.tCyl_apply, Work.KT.zUnit_apply, linBig_cylConst_apply, linBig_inc1_apply,
      linBig_unitInterval_coe_one, Complex.ofReal_one, one_mul, mul_one, smul_eq_mul,
      ContinuousMap.smul_apply, Complex.real_smul]
    ring

end

end Work.KT.EG.KLG
