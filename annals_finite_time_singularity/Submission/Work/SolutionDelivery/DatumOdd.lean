import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.ContDiff.WithLp
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Defs
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Basic.ENNReal.Basic
import Mathlib.Geometry.Euclidean.Angle.Unoriented.CrossProduct
import Mathlib.LinearAlgebra.CrossProduct
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.LinearAlgebra.Trace
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Order.CompletePartialOrder
import Mathlib.Order.Filter.Defs
import Mathlib.Order.Interval.Basic
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Have
import Mathlib.Tactic.IntervalCases
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Mathlib.Topology.MetricSpace.Holder
import Mathlib.Topology.Separation.CompletelyRegular
import Submission.Work.Coercivity.HkMem_mono
import Submission.Work.FTS.EllipticEst.OpenFTC.absFtcLeIntegralAbsDeriv
import Submission.Work.FTS.EllipticEst.integrableOn_HkIntegrand_terms
import Submission.Work.FTS.EllipticEst.remov.slice_gprime_ident
import Submission.Work.FTS.Galerkin.Inhabit.regPkg_zero
import Submission.Work.FTS.H2.T1Defs
import Submission.Work.FTS.H2.hard_sq_prod_z
import Submission.Work.FTS.LocData.bumpZ_eq_zero_of_notMem_Icc
import Submission.Work.FTS.LocData.integral_sin_two_rpow_neg
import Submission.Work.LWP.VorticityAPI
import Submission.Work.Spaces.HkSq_terms
import Submission.Work.Spaces.SmoothCompact_HkMem
import Submission.Work.Spaces.bt_integral_weight_id
import Submission.Work.Spaces.factor_bound
import Submission.Work.Spaces.pz_DthIter_mul_eq
import Submission.Work.Spaces.sin_two_rpow
import Submission.Work.Spaces.sq_mul_div_rpow
import Submission.Work.Spaces.sup_mixed_le_H4
import Submission.Work.Stability.CutFactorFderivZero
import Submission.Work.Stability.Cutoff
import Submission.Work.Stability.holderWith_of_dist_le
-- ===== merged: Submission.Work.ConstructionInstance.AxiNoSwirlSymm =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Matrix

namespace Work.ConstructionInstance

/-! ## The rotation about the symmetry axis -/

/-- The coordinate action of the rotation about the `x₃`-axis by the angle `φ`,
`(v₀,v₁,v₂) ↦ (cos φ · v₀ - sin φ · v₁, sin φ · v₀ + cos φ · v₁, v₂)`. -/
def rotCoord (φ : ℝ) : (Fin 3 → ℝ) → (Fin 3 → ℝ) :=
  fun v => ![Real.cos φ * v 0 - Real.sin φ * v 1,
              Real.sin φ * v 0 + Real.cos φ * v 1,
              v 2]

@[simp] lemma rotCoord_apply_zero (φ : ℝ) (v : Fin 3 → ℝ) :
    rotCoord φ v 0 = Real.cos φ * v 0 - Real.sin φ * v 1 := rfl
@[simp] lemma rotCoord_apply_one (φ : ℝ) (v : Fin 3 → ℝ) :
    rotCoord φ v 1 = Real.sin φ * v 0 + Real.cos φ * v 1 := rfl
@[simp] lemma rotCoord_apply_two (φ : ℝ) (v : Fin 3 → ℝ) : rotCoord φ v 2 = v 2 := rfl

lemma rotCoord_add (φ : ℝ) (a b : Fin 3 → ℝ) :
    rotCoord φ (a + b) = rotCoord φ a + rotCoord φ b := by
  funext i
  fin_cases i <;> simp [rotCoord] <;> ring

lemma rotCoord_smul (φ : ℝ) (c : ℝ) (a : Fin 3 → ℝ) :
    rotCoord φ (c • a) = c • rotCoord φ a := by
  funext i
  fin_cases i <;> simp [rotCoord] <;> ring

lemma rotCoord_neg_comp (φ : ℝ) (v : Fin 3 → ℝ) : rotCoord (-φ) (rotCoord φ v) = v := by
  funext i
  fin_cases i
  · show rotCoord (-φ) (rotCoord φ v) 0 = v 0
    simp only [rotCoord_apply_zero, rotCoord_apply_one, Real.cos_neg, Real.sin_neg]
    ring_nf
    linear_combination (v 0) * Real.cos_sq_add_sin_sq φ
  · show rotCoord (-φ) (rotCoord φ v) 1 = v 1
    simp only [rotCoord_apply_zero, rotCoord_apply_one, Real.cos_neg, Real.sin_neg]
    ring_nf
    linear_combination (v 1) * Real.cos_sq_add_sin_sq φ
  · show rotCoord (-φ) (rotCoord φ v) 2 = v 2
    simp [rotCoord]

lemma rotCoord_comp_neg (φ : ℝ) (v : Fin 3 → ℝ) : rotCoord φ (rotCoord (-φ) v) = v := by
  simpa using rotCoord_neg_comp (-φ) v

/-- The rotation preserves the Euclidean norm. -/
lemma rotCoord_norm (φ : ℝ) (v : Fin 3 → ℝ) :
    ‖(WithLp.toLp 2 (rotCoord φ v) : R3)‖ = ‖(WithLp.toLp 2 v : R3)‖ := by
  have h : ‖(WithLp.toLp 2 (rotCoord φ v) : R3)‖ ^ 2
      = ‖(WithLp.toLp 2 v : R3)‖ ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq]
    rw [Fin.sum_univ_three, Fin.sum_univ_three]
    simp [rotCoord]
    ring_nf
    linear_combination (v 0 ^ 2 + v 1 ^ 2) * Real.cos_sq_add_sin_sq φ
  nlinarith [norm_nonneg (WithLp.toLp 2 (rotCoord φ v) : R3),
    norm_nonneg (WithLp.toLp 2 v : R3)]

/-- The rotation is compatible with the cross product. -/
lemma rotCoord_cross (φ : ℝ) (a b : Fin 3 → ℝ) :
    rotCoord φ a ⨯₃ rotCoord φ b = rotCoord φ (a ⨯₃ b) := by
  funext i
  fin_cases i <;> simp [rotCoord, cross_apply]
  · ring
  · ring
  · ring_nf
    linear_combination (a 0 * b 1 - a 1 * b 0) * Real.cos_sq_add_sin_sq φ

/-- The rotation about the `x₃`-axis by the angle `φ`, as a linear isometry equivalence of `ℝ³`. -/
noncomputable def rotLE (φ : ℝ) : R3 ≃ₗᵢ[ℝ] R3 where
  toFun x := WithLp.toLp 2 (rotCoord φ x.ofLp)
  invFun x := WithLp.toLp 2 (rotCoord (-φ) x.ofLp)
  left_inv x := by
    show WithLp.toLp 2 (rotCoord (-φ) (rotCoord φ x.ofLp)) = x
    rw [rotCoord_neg_comp, WithLp.toLp_ofLp]
  right_inv x := by
    show WithLp.toLp 2 (rotCoord φ (rotCoord (-φ) x.ofLp)) = x
    rw [rotCoord_comp_neg, WithLp.toLp_ofLp]
  map_add' x y := by
    show WithLp.toLp 2 (rotCoord φ (x + y).ofLp) = WithLp.toLp 2 (rotCoord φ x.ofLp)
      + WithLp.toLp 2 (rotCoord φ y.ofLp)
    rw [WithLp.ofLp_add, ← WithLp.toLp_add, rotCoord_add]
  map_smul' c x := by
    show WithLp.toLp 2 (rotCoord φ (c • x).ofLp) = c • WithLp.toLp 2 (rotCoord φ x.ofLp)
    rw [WithLp.ofLp_smul, ← WithLp.toLp_smul, rotCoord_smul]
  norm_map' x := by
    show ‖WithLp.toLp 2 (rotCoord φ x.ofLp)‖ = ‖x‖
    rw [rotCoord_norm, WithLp.toLp_ofLp]

@[simp] lemma rotLE_apply (φ : ℝ) (x : R3) :
    rotLE φ x = WithLp.toLp 2 (rotCoord φ x.ofLp) := rfl

@[simp] lemma rotLE_symm_apply (φ : ℝ) (x : R3) :
    (rotLE φ).symm x = WithLp.toLp 2 (rotCoord (-φ) x.ofLp) := rfl

@[simp] lemma rotLE_ofLp (φ : ℝ) (x : R3) : (rotLE φ x).ofLp = rotCoord φ x.ofLp := by
  rw [rotLE_apply, WithLp.ofLp_toLp]



/-! ## The rotation and the cylindrical frame -/

lemma radSq_rotLE (φ : ℝ) (x : R3) :
    Work.Cyl.radSq (rotLE φ x) = Work.Cyl.radSq x := by
  simp only [Work.Cyl.radSq, rotLE_apply, PiLp.toLp_apply, rotCoord_apply_zero,
    rotCoord_apply_one]
  ring_nf
  linear_combination ((x.ofLp 0) ^ 2 + (x.ofLp 1) ^ 2) * Real.cos_sq_add_sin_sq φ

lemma radial_rotLE (φ : ℝ) (x : R3) :
    Work.Cyl.radial (rotLE φ x) = Work.Cyl.radial x := by
  simp only [Work.Cyl.radial, radSq_rotLE]

lemma axial_rotLE (φ : ℝ) (x : R3) :
    Work.Cyl.axial (rotLE φ x) = Work.Cyl.axial x := by
  simp [Work.Cyl.axial, rotLE_apply, rotCoord]

lemma angularVec_rotLE (φ : ℝ) (x : R3) :
    Work.Cyl.angularVec (rotLE φ x) = rotLE φ (Work.Cyl.angularVec x) := by
  ext i
  fin_cases i <;>
    simp [Work.Cyl.angularVec, rotLE_apply, rotCoord] <;>
    ring

lemma eTheta_rotLE (φ : ℝ) (x : R3) :
    Work.Cyl.eTheta (rotLE φ x) = rotLE φ (Work.Cyl.eTheta x) := by
  rw [Work.Cyl.eTheta, Work.Cyl.eTheta, radial_rotLE, angularVec_rotLE]
  exact (map_smul (rotLE φ) (1 / Work.Cyl.radial x) (Work.Cyl.angularVec x)).symm

/-! ## The reflection `x ↦ (x₀, -x₁, x₃)` -/

/-- The reflection `x ↦ (x₀, -x₁, x₃)` of `ℝ³`. -/
def flip1 (x : R3) : R3 := !₂[x 0, - x 1, x 2]

@[simp] lemma flip1_zero (x : R3) : (flip1 x) 0 = x 0 := by simp [flip1]
@[simp] lemma flip1_one (x : R3) : (flip1 x) 1 = - x 1 := by simp [flip1]
@[simp] lemma flip1_two (x : R3) : (flip1 x) 2 = x 2 := by simp [flip1]

lemma flip1_add (a b : R3) : flip1 (a + b) = flip1 a + flip1 b := by
  ext i
  fin_cases i <;> simp [flip1] <;> ring

lemma flip1_smul (c : ℝ) (a : R3) : flip1 (c • a) = c • flip1 a := by
  ext i
  fin_cases i <;> simp [flip1]

lemma flip1_flip1 (v : R3) : flip1 (flip1 v) = v := by
  ext i
  fin_cases i <;> simp [flip1]

lemma flip1_norm (x : R3) : ‖flip1 x‖ = ‖x‖ := by
  rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
  congr 1
  rw [Fin.sum_univ_three, Fin.sum_univ_three]
  simp [flip1]

/-- The reflection `x ↦ (x₀, -x₁, x₃)`, as a linear isometry equivalence of `ℝ³`. -/
noncomputable def flip1LE : R3 ≃ₗᵢ[ℝ] R3 where
  toFun := flip1
  invFun := flip1
  left_inv := flip1_flip1
  right_inv := flip1_flip1
  map_add' := flip1_add
  map_smul' := flip1_smul
  norm_map' := flip1_norm

@[simp] lemma flip1LE_apply (v : R3) : flip1LE v = flip1 v := rfl
@[simp] lemma flip1LE_symm : (flip1LE : R3 ≃ₗᵢ[ℝ] R3).symm = flip1LE := rfl

/-- The coordinate action of `flip1`. -/
def flip1Coord : (Fin 3 → ℝ) → (Fin 3 → ℝ) := fun v => ![v 0, - v 1, v 2]

@[simp] lemma flip1Coord_zero (v : Fin 3 → ℝ) : flip1Coord v 0 = v 0 := rfl
@[simp] lemma flip1Coord_one (v : Fin 3 → ℝ) : flip1Coord v 1 = - v 1 := rfl
@[simp] lemma flip1Coord_two (v : Fin 3 → ℝ) : flip1Coord v 2 = v 2 := rfl

lemma flip1Coord_smul (c : ℝ) (a : Fin 3 → ℝ) : flip1Coord (c • a) = c • flip1Coord a := by
  funext i
  fin_cases i <;> simp [flip1Coord]


@[simp] lemma flip1_ofLp (x : R3) : (flip1 x).ofLp = flip1Coord x.ofLp := rfl

lemma flip1Coord_sub (a b : Fin 3 → ℝ) :
    flip1Coord (a - b) = flip1Coord a - flip1Coord b := by
  funext i
  fin_cases i <;> simp [flip1Coord] <;> ring

/-- `flip1` reverses the cross product. -/
lemma flip1Coord_cross (a b : Fin 3 → ℝ) :
    flip1Coord a ⨯₃ flip1Coord b = - flip1Coord (a ⨯₃ b) := by
  funext i
  fin_cases i <;> simp [flip1Coord, cross_apply] <;> ring

/-! ## An angle with prescribed cosine and sine -/

/-! ## Components of `rotLE` -/

@[simp] lemma rotLE_apply_zero (φ : ℝ) (x : R3) :
    (rotLE φ x) 0 = Real.cos φ * x 0 - Real.sin φ * x 1 := by
  simp [rotLE_apply, rotCoord]

@[simp] lemma rotLE_apply_one (φ : ℝ) (x : R3) :
    (rotLE φ x) 1 = Real.sin φ * x 0 + Real.cos φ * x 1 := by
  simp [rotLE_apply, rotCoord]

@[simp] lemma rotLE_apply_two (φ : ℝ) (x : R3) : (rotLE φ x) 2 = x 2 := by
  simp [rotLE_apply, rotCoord]

@[simp] lemma rotLE_zero_apply (x : R3) : rotLE 0 x = x := by
  ext i; fin_cases i <;> simp [rotLE_apply, rotCoord]

/-! ## The reflection and the cylindrical frame -/

lemma radial_flip1 (x : R3) : Work.Cyl.radial (flip1 x) = Work.Cyl.radial x := by
  simp only [Work.Cyl.radial, Work.Cyl.radSq, flip1_zero, flip1_one]
  ring_nf

lemma axial_flip1 (x : R3) : Work.Cyl.axial (flip1 x) = Work.Cyl.axial x := by
  simp [Work.Cyl.axial, flip1]

lemma angularVec_flip1 (x : R3) :
    Work.Cyl.angularVec (flip1 x) = - flip1 (Work.Cyl.angularVec x) := by
  ext i
  fin_cases i <;> simp [Work.Cyl.angularVec, flip1]

lemma eTheta_flip1 (x : R3) :
    Work.Cyl.eTheta (flip1 x) = - flip1 (Work.Cyl.eTheta x) := by
  rw [Work.Cyl.eTheta, Work.Cyl.eTheta, radial_flip1, angularVec_flip1, flip1_smul, smul_neg]

/-! ## The vorticity profile is equivariant -/

lemma omega_rotLE {ω : R3 → R3} {f : ℝ → ℝ → ℝ}
    (hω : ∀ x : R3, ω x = f (Work.Cyl.radial x) (Work.Cyl.axial x) • Work.Cyl.eTheta x)
    (φ : ℝ) (x : R3) : ω (rotLE φ x) = rotLE φ (ω x) := by
  rw [hω (rotLE φ x), hω x, radial_rotLE, axial_rotLE, eTheta_rotLE, map_smul]

lemma omega_flip1 {ω : R3 → R3} {f : ℝ → ℝ → ℝ}
    (hω : ∀ x : R3, ω x = f (Work.Cyl.radial x) (Work.Cyl.axial x) • Work.Cyl.eTheta x)
    (x : R3) : ω (flip1 x) = - flip1 (ω x) := by
  rw [hω (flip1 x), hω x, radial_flip1, axial_flip1, eTheta_flip1, flip1_smul, smul_neg]

/-! ## No-swirl axisymmetry from the rotation and reflection symmetries -/

/-- **A field equivariant under all rotations about the `x₃`-axis and invariant under the
reflection `x ↦ (x₀,-x₁,x₃)` is axisymmetric without swirl.**

Writing `B(x) = !₂[r(x), 0, x₃(x)]` for the point of the meridian `θ = 0` with the same `(ρ,x₃)`,
the profiles are `u_r(r,z) = (u B)₀` and `u_z(r,z) = (u B)₂`: the reflection identity kills the
second component of `u B` (`hbase1`), the rotation by `π` kills the first one on the axis
(`h0`), and on `r > 0` the rotation equivariance transports the meridian value to `x`. -/
theorem isAxiNoSwirl_of_rot_flip (u : R3 → R3)
    (hrot : ∀ (φ : ℝ) (x : R3), u (rotLE φ x) = rotLE φ (u x))
    (hflip : ∀ x : R3, u (flip1 x) = flip1 (u x))
    (hsurj : ∀ x : R3, 0 < Work.Cyl.radial x →
      ∃ φ : ℝ, rotLE φ !₂[Work.Cyl.radial x, 0, Work.Cyl.axial x] = x) :
    Work.Cyl.IsAxiNoSwirl u := by
  refine ⟨fun r z => u !₂[r, 0, z] 0, fun r z => u !₂[r, 0, z] 2, ?_⟩
  funext x
  have hbase1 : (u !₂[Work.Cyl.radial x, 0, Work.Cyl.axial x]) 1 = 0 := by
    have hflipB : flip1 (!₂[Work.Cyl.radial x, 0, Work.Cyl.axial x] : R3)
        = !₂[Work.Cyl.radial x, 0, Work.Cyl.axial x] := by
      ext i; fin_cases i <;> simp [flip1]
    have h := hflip (!₂[Work.Cyl.radial x, 0, Work.Cyl.axial x] : R3)
    rw [hflipB] at h
    have h' := congrArg (fun v : R3 => v 1) h
    have h2 : (u !₂[Work.Cyl.radial x, 0, Work.Cyl.axial x]) 1
        = - (u !₂[Work.Cyl.radial x, 0, Work.Cyl.axial x]) 1 := by
      simpa [flip1] using h'
    linarith
  by_cases hr : Work.Cyl.radial x = 0
  · have hx01 := (Work.Cyl.radial_eq_zero_iff x).mp hr
    have hx0 : x 0 = 0 := hx01.1
    have hx1 : x 1 = 0 := hx01.2
    have hfixπ : rotLE Real.pi x = x := by
      ext i; fin_cases i <;> simp [hx0, hx1]
    have h0 : (u x) 0 = 0 := by
      have h := hrot Real.pi x
      rw [hfixπ] at h
      have h' := congrArg (fun v : R3 => v 0) h
      have h2 : (u x) 0 = - (u x) 0 := by simpa [rotLE_apply_zero] using h'
      linarith
    have h1 : (u x) 1 = 0 := by
      have hflipx : flip1 x = x := by
        ext i; fin_cases i <;> simp [flip1, hx1]
      have h := hflip x
      rw [hflipx] at h
      have h' := congrArg (fun v : R3 => v 1) h
      have h2 : (u x) 1 = - (u x) 1 := by simpa [flip1] using h'
      linarith
    have hxeq : x = !₂[Work.Cyl.radial x, 0, Work.Cyl.axial x] := by
      ext i; fin_cases i <;> simp [hx0, hx1, hr, Work.Cyl.axial]
    have hxB : (u x) 2 = (u !₂[Work.Cyl.radial x, 0, Work.Cyl.axial x]) 2 :=
      congrArg (fun v : R3 => (u v) 2) hxeq
    have hc0 : (u x) 0 = (Work.Cyl.cylField (fun r z => u !₂[r, 0, z] 0)
        (fun r z => u !₂[r, 0, z] 2) x) 0 := by
      rw [Work.Cyl.cylField_zero, h0, hr]; simp
    have hc1 : (u x) 1 = (Work.Cyl.cylField (fun r z => u !₂[r, 0, z] 0)
        (fun r z => u !₂[r, 0, z] 2) x) 1 := by
      rw [Work.Cyl.cylField_one, h1, hr]; simp
    have hc2 : (u x) 2 = (Work.Cyl.cylField (fun r z => u !₂[r, 0, z] 0)
        (fun r z => u !₂[r, 0, z] 2) x) 2 := by
      rw [Work.Cyl.cylField_two]; exact hxB
    ext i; fin_cases i
    · exact hc0
    · exact hc1
    · exact hc2
  · have hrpos : 0 < Work.Cyl.radial x :=
      lt_of_le_of_ne (Work.Cyl.radial_nonneg x) (Ne.symm hr)
    obtain ⟨φ, hφ⟩ := hsurj x hrpos
    have hux : u x = rotLE φ (u !₂[Work.Cyl.radial x, 0, Work.Cyl.axial x]) := by
      have h := hrot φ (!₂[Work.Cyl.radial x, 0, Work.Cyl.axial x] : R3)
      rwa [hφ] at h
    have hx0 : Real.cos φ * Work.Cyl.radial x = x 0 := by
      have h := congrArg (fun v : R3 => v 0) hφ
      simpa [rotLE_apply_zero] using h
    have hx1 : Real.sin φ * Work.Cyl.radial x = x 1 := by
      have h := congrArg (fun v : R3 => v 1) hφ
      simpa [rotLE_apply_one] using h
    have hc0 : (u x) 0 = (Work.Cyl.cylField (fun r z => u !₂[r, 0, z] 0)
        (fun r z => u !₂[r, 0, z] 2) x) 0 := by
      rw [Work.Cyl.cylField_zero, hux, rotLE_apply_zero, hbase1, mul_zero, sub_zero, ← hx0]
      try field_simp
      try ring
    have hc1 : (u x) 1 = (Work.Cyl.cylField (fun r z => u !₂[r, 0, z] 0)
        (fun r z => u !₂[r, 0, z] 2) x) 1 := by
      rw [Work.Cyl.cylField_one, hux, rotLE_apply_one, hbase1, mul_zero, add_zero, ← hx1]
      try field_simp
      try ring
    have hc2 : (u x) 2 = (Work.Cyl.cylField (fun r z => u !₂[r, 0, z] 0)
        (fun r z => u !₂[r, 0, z] 2) x) 2 := by
      rw [Work.Cyl.cylField_two, hux, rotLE_apply_two]
    ext i; fin_cases i
    · exact hc0
    · exact hc1
    · exact hc2

/-- Given `a² + b² = 1` there is `φ` with `cos φ = a` and `sin φ = b`. -/
lemma exists_cos_sin {a b : ℝ} (h : a ^ 2 + b ^ 2 = 1) :
    ∃ φ : ℝ, Real.cos φ = a ∧ Real.sin φ = b := by
  set z : ℂ := (a : ℂ) + b * Complex.I with hz
  have hnormSq : Complex.normSq z = 1 := by
    rw [hz, Complex.normSq_apply]
    simp
    nlinarith [h]
  have hnorm : ‖z‖ = 1 := by
    have h2 : ‖z‖ ^ 2 = 1 := by rw [← Complex.normSq_eq_norm_sq]; exact hnormSq
    nlinarith [norm_nonneg z]
  have hz0 : z ≠ 0 := by
    intro h0
    rw [h0] at hnorm
    simp at hnorm
  refine ⟨z.arg, ?_, ?_⟩
  · rw [Complex.cos_arg hz0, hnorm, hz]; simp
  · rw [Complex.sin_arg, hnorm, hz]; simp

end Work.ConstructionInstance
end
end
-- ===== merged: Submission.Work.ConstructionInstance.Basic =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open FiniteTimeSingularity Set Gradient Matrix Filter Topology MeasureTheory
open scoped Topology Matrix NNReal ENNReal

namespace Work.ConstructionInstance

/-! ## The frame vector `e_θ` is bounded by one -/

theorem norm_eTheta_le_one (x : R3) : ‖Work.Cyl.eTheta x‖ ≤ 1 := by
  rcases eq_or_ne (Work.Cyl.radial x) 0 with h | h
  · have h1 : (1 : ℝ) / Work.Cyl.radial x = 0 := by rw [h, div_zero]
    have hz : Work.Cyl.eTheta x = 0 := by rw [Work.Cyl.eTheta, h1, zero_smul]
    rw [hz, norm_zero]; norm_num
  · rw [Work.Cyl.norm_eTheta x h]

/-! ## The profile bound -/

/-- **The `L^∞` bound of the profile** on the closed quadrant:
`|F(z,θ)| ≤ 20p·Γ(p/3,θ) + Cg` for `0 < p ≤ 1`, `z ≥ 0`, `θ ∈ [0,π/2]`. -/
theorem profile_abs_le {p : ℝ} (hp : 0 < p) (hp1 : p ≤ 1) {g : ℝ → ℝ → ℝ} {Cg : ℝ}
    (hg : ∀ z θ : ℝ, 0 ≤ z → θ ∈ Work.Spaces.Iθ → |g z θ| ≤ Cg)
    (z : ℝ) (hz : 0 ≤ z) (θ : ℝ) (hθ : θ ∈ Work.Spaces.Iθ) :
    |profile p g z θ| ≤ 20 * p * Gamma (p / 3) θ + Cg := by
  rw [profile_of_nonneg hθ.1]
  calc |Work.Construction.Fstar p z θ + g z θ|
      ≤ |Work.Construction.Fstar p z θ| + |g z θ| := abs_add_le _ _
    _ ≤ 20 * p * Gamma (p / 3) θ + Cg :=
        add_le_add (Fstar_abs_le hp hp1 hz hθ) (hg z θ hz hθ)

/-- **A global `L^∞` bound of the profile**, for `θ` in the range of `Work.Cyl.theta`
(`|θ| ≤ π/2`); the odd branch is reduced to the positive one by the definition of `profile`. -/
theorem profile_abs_le_of_abs {p : ℝ} (hp : 0 < p) (hp1 : p ≤ 1) {g : ℝ → ℝ → ℝ} {Cg : ℝ}
    (hg : ∀ z θ : ℝ, 0 ≤ z → θ ∈ Work.Spaces.Iθ → |g z θ| ≤ Cg)
    (z : ℝ) (hz : 0 ≤ z) (θ : ℝ) (hθ : |θ| ≤ Real.pi / 2) :
    |profile p g z θ| ≤ 20 * p * Gamma (p / 3) |θ| + Cg := by
  rcases lt_or_ge θ 0 with h | h
  · have h' : -θ ∈ Work.Spaces.Iθ := by
      rw [abs_of_neg h] at hθ
      exact ⟨by linarith, hθ⟩
    rw [profile_of_neg (not_le.mpr h), abs_neg, abs_of_neg h, ← profile_of_nonneg h'.1]
    exact profile_abs_le hp hp1 hg z hz (-θ) h'
  · rw [abs_of_nonneg h] at hθ ⊢
    exact profile_abs_le hp hp1 hg z hz θ ⟨h, hθ⟩

/-! ## The `L^∞` bound of the self-similar vorticity -/

/-- **`‖omegaS p g x‖ ≤ M`**: the profile bound times `‖e_θ‖ ≤ 1`, using that
`|Work.Cyl.theta x| ∈ [0,π/2]` and the bound `M` of the profile. -/
theorem omegaS_norm_le {p : ℝ} (hp : 0 < p) (hp1 : p ≤ 1) {g : ℝ → ℝ → ℝ} {Cg M : ℝ}
    (hg : ∀ z θ : ℝ, 0 ≤ z → θ ∈ Work.Spaces.Iθ → |g z θ| ≤ Cg) (hCg : 0 ≤ Cg)
    (hM : ∀ θ ∈ Work.Spaces.Iθ, 20 * p * Gamma (p / 3) θ + Cg ≤ M) (x : R3) :
    ‖omegaS p g x‖ ≤ M := by
  rw [omegaS_apply', norm_smul, Real.norm_eq_abs]
  have hθ_abs : |Work.Cyl.theta x| ≤ Real.pi / 2 := by
    rw [abs_le]
    exact ⟨le_of_lt (Real.neg_pi_div_two_lt_arctan _),
      le_of_lt (Real.arctan_lt_pi_div_two _)⟩
  have hθmem : |Work.Cyl.theta x| ∈ Work.Spaces.Iθ := ⟨abs_nonneg _, hθ_abs⟩
  have hbdd := profile_abs_le_of_abs (p := p) hp hp1 hg (Work.Cyl.rho x ^ p)
    (Real.rpow_nonneg (Real.sqrt_nonneg _) p) (Work.Cyl.theta x) hθ_abs
  have hnn : 0 ≤ 20 * p * Gamma (p / 3) |Work.Cyl.theta x| + Cg :=
    add_nonneg (mul_nonneg (mul_nonneg (by norm_num) hp.le) (Gamma_nonneg hθmem)) hCg
  calc |profile p g (Work.Cyl.rho x ^ p) (Work.Cyl.theta x)| * ‖Work.Cyl.eTheta x‖
      ≤ (20 * p * Gamma (p / 3) |Work.Cyl.theta x| + Cg) * 1 :=
        mul_le_mul hbdd (norm_eTheta_le_one x) (norm_nonneg _) hnn
    _ ≤ M := by
        have := hM _ hθmem
        linarith

/-! ## The pure `F_*` field is a multiple of the model field -/


/-- `θ(x) ≥ 0` on the closed half space `x₃ ≥ 0`. -/
theorem theta_nonneg_of_axial_nonneg {x : R3} (hx : 0 ≤ x 2) : 0 ≤ Work.Cyl.theta x := by
  rw [Work.Cyl.theta, Real.arctan_nonneg, Work.Cyl.axial]
  exact div_nonneg hx (Real.sqrt_nonneg _)


end Work.ConstructionInstance
end
end
-- ===== merged: Submission.Work.ConstructionInstance.GCompDefs =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open Set

namespace Work.ConstructionInstance

/-- **The corrected polar angle** `psi x = arccos (r x / ρ x)`, where `r = Cyl.radial` is the
distance to the symmetry axis and `ρ = Cyl.rho = ‖x‖`.  This lies in `[0, π/2]` and equals
`|Cyl.theta x|` whenever `r x > 0`. -/
def psi (x : R3) : ℝ := Real.arccos (Work.Cyl.radial x / Work.Cyl.rho x)

/-- `rho x = rhoP (radial x) (axial x)`: the `ℝ³` radius is the planar radius of the
`(r, x₃)`-coordinates. -/
theorem rho_eq_rhoP (x : R3) :
    Work.Cyl.rho x = Work.Cyl.rhoP (Work.Cyl.radial x) (Work.Cyl.axial x) := by
  rw [Work.Cyl.rho, Work.Cyl.rhoP]
  congr 1
  rw [Work.Cyl.radial_sq]

/-- The corrected angle lies in `[0, π/2]`. -/
theorem psi_mem_Iθ (x : R3) : psi x ∈ Work.Spaces.Iθ := by
  refine ⟨Real.arccos_nonneg _, ?_⟩
  rw [psi, Real.arccos_le_pi_div_two]
  exact div_nonneg (Work.Cyl.radial_nonneg x) (Work.Cyl.rho_nonneg x)

/-- `cos ψ = r / ρ`. -/
theorem cos_psi (x : R3) : Real.cos (psi x) = Work.Cyl.radial x / Work.Cyl.rho x := by
  rw [psi]
  exact Real.cos_arccos (by
      have h := div_nonneg (Work.Cyl.radial_nonneg x) (Work.Cyl.rho_nonneg x)
      linarith)
    (div_le_one_of_le₀ (Work.Cyl.radial_le_rho x) (Work.Cyl.rho_nonneg x))

/-- `sin ψ = |x₃| / ρ`. -/
theorem sin_psi {x : R3} (h : 0 < Work.Cyl.rho x) :
    Real.sin (psi x) = |x 2| / Work.Cyl.rho x := by
  rw [psi, Real.sin_arccos]
  have hρ : 0 < Work.Cyl.rho x := h
  have hkey : 1 - (Work.Cyl.radial x / Work.Cyl.rho x) ^ 2
      = ((x 2) / Work.Cyl.rho x) ^ 2 := by
    have h1 : Work.Cyl.radial x ^ 2 = Work.Cyl.radSq x := Work.Cyl.radial_sq x
    have h2 : Work.Cyl.rho x ^ 2 = Work.Cyl.radSq x + Work.Cyl.axial x ^ 2 :=
      Work.Cyl.rho_sq x
    have h3 : Work.Cyl.axial x = x 2 := rfl
    field_simp
    rw [h3] at h2
    linarith
  rw [hkey, Real.sqrt_sq_eq_abs, abs_div, abs_of_pos hρ]

/-- `cos θ = r / ρ` off the axis. -/
theorem cos_theta_eq {x : R3} (h : 0 < Work.Cyl.radial x) :
    Real.cos (Work.Cyl.theta x) = Work.Cyl.radial x / Work.Cyl.rho x := by
  have h1 : Work.Cyl.theta x = Work.Cyl.thetaP (Work.Cyl.radial x) (Work.Cyl.axial x) := rfl
  rw [h1, Work.Cyl.cos_thetaP h, rho_eq_rhoP]

/-- Off the axis the corrected angle is the absolute value of `theta`. -/
theorem psi_eq_abs_theta {x : R3} (h : 0 < Work.Cyl.radial x) :
    psi x = |Work.Cyl.theta x| := by
  have hθ : |Work.Cyl.theta x| ≤ Real.pi := by
    have h1 : -(Real.pi / 2) < Work.Cyl.theta x := Real.neg_pi_div_two_lt_arctan _
    have h2 : Work.Cyl.theta x < Real.pi / 2 := Real.arctan_lt_pi_div_two _
    rw [abs_le]
    constructor <;> linarith [Real.pi_pos]
  rw [psi, ← Real.arccos_cos (abs_nonneg _) hθ, Real.cos_abs, cos_theta_eq h]

end Work.ConstructionInstance
end
end
-- ===== merged: Submission.Work.ConstructionInstance.Meas =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open FiniteTimeSingularity Set Gradient Matrix Filter Topology MeasureTheory
open scoped Topology Matrix NNReal ENNReal

namespace Work.ConstructionInstance

theorem measurable_radial : Measurable (fun x : R3 => Work.Cyl.radial x) := by
  have h : Measurable (fun x : R3 => Work.Cyl.radSq x) := by
    show Measurable (fun x : R3 => x 0 ^ 2 + x 1 ^ 2)
    fun_prop
  exact h.sqrt

theorem measurable_angularVec : Measurable (fun x : R3 => Work.Cyl.angularVec x) := by
  have h : Continuous fun x : R3 => Work.Cyl.angularVec x := by
    show Continuous fun x : R3 => WithLp.toLp 2 (![-x 1, x 0, 0] : Fin 3 → ℝ)
    fun_prop
  exact h.measurable

/-- `Work.Cyl.eTheta` is measurable (though not continuous). -/
theorem measurable_eTheta : Measurable (fun x : R3 => Work.Cyl.eTheta x) := by
  have hscal : Measurable (fun x : R3 => (1 : ℝ) / Work.Cyl.radial x) :=
    measurable_const.div measurable_radial
  have hfun : (fun x : R3 => Work.Cyl.eTheta x)
      = fun x : R3 => (1 / Work.Cyl.radial x) • Work.Cyl.angularVec x := rfl
  rw [hfun]
  exact hscal.smul measurable_angularVec

/-- **The self-similar vorticity is measurable** as soon as its scalar profile is. -/
theorem aestronglyMeasurable_omegaS {p : ℝ} {g : ℝ → ℝ → ℝ}
    (hP : AEStronglyMeasurable
      (fun x : R3 => profile p g (Work.Cyl.Rc p x) (Work.Cyl.theta x)) volume) :
    AEStronglyMeasurable (omegaS p g) volume := by
  have h := hP.smul (measurable_eTheta.aestronglyMeasurable (μ := volume))
  exact h

end Work.ConstructionInstance
end
end
-- ===== merged: Submission.Work.ConstructionInstance.div_omegaS =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.ConstructionInstance

open FiniteTimeSingularity
open Work.Cyl

/-!
# `div (omegaS p g) = 0` off the symmetry axis

The self-similar vorticity `omegaS p g x = F(ρ(x)^p, θ(x)) • e_θ(x)` is an axisymmetric `e_θ`-field
with no swirl.  Such a field is divergence free away from the axis `r = 0`: its only nonvanishing
component is tangential, and the scalar prefactor is invariant under the rotation flow whose
generator is `e_θ`.

The proof below is the standard decomposition

`div (F • e_θ) x = F x · div e_θ x + (fderiv F x) (e_θ x)`

together with the two facts `div e_θ = 0` and `(fderiv F x) (e_θ x) = 0` (the latter a consequence
of `ρ` and `θ` having vanishing directional derivative along `e_θ`).
-/

/-! ## A helper: the derivative of an even function at `0` -/

/-- The derivative at `0` of a function that is even vanishes. -/
theorem deriv_zero_of_even {f : ℝ → ℝ} (he : ∀ t, f (-t) = f t) : deriv f 0 = 0 := by
  have h := deriv_comp_neg f 0
  simp only [neg_zero] at h
  have hev : (fun t : ℝ => f (-t)) = f := funext he
  rw [hev] at h
  linarith

/-! ## The product rule for the divergence -/

/-- **Divergence of a scalar multiple of a vector field**:
`div (F • v) x = F x · div v x + (fderiv F x) (v x)`.

This is the product rule for the trace of the Jacobian: `fderiv (F • v) x = F x • fderiv v x +
(fderiv F x).smulRight (v x)` and `trace ((fderiv F x).smulRight (v x)) = (fderiv F x) (v x)`. -/
theorem div_smul_eq (F : R3 → ℝ) (v : R3 → R3) (x : R3)
    (hF : DifferentiableAt ℝ F x) (hv : DifferentiableAt ℝ v x) :
    FiniteTimeSingularity.div (F • v) x
      = F x * FiniteTimeSingularity.div v x + fderiv ℝ F x (v x) := by
  have hsmul := fderiv_smul (𝕜 := ℝ) hF hv
  rw [FiniteTimeSingularity.div, FiniteTimeSingularity.div, hsmul]
  rw [ContinuousLinearMap.toLinearMap_add, ContinuousLinearMap.toLinearMap_smul,
    ContinuousLinearMap.coe_smulRight]
  rw [map_add, map_smul, LinearMap.trace_smulRight, ContinuousLinearMap.coe_coe]
  ring

/-! ## The line `t ↦ x + t • e_θ` -/

/-- Along `t ↦ x + t • e_θ(x)` the squared planar radius grows as `radSq x + t²`. -/
theorem radSq_add_smul_eTheta (x : R3) (hr : 0 < radial x) (t : ℝ) :
    radSq (x + t • eTheta x) = radSq x + t ^ 2 := by
  have hrne : radial x ≠ 0 := ne_of_gt hr
  have hx2 : x 0 ^ 2 + x 1 ^ 2 = radial x ^ 2 := (radial_sq x).symm
  rw [radSq, radSq]
  simp only [WithLp.ofLp_add, WithLp.ofLp_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
    eTheta_apply_zero, eTheta_apply_one]
  field_simp
  nlinarith [hx2]

/-- Along `t ↦ x + t • e_θ(x)` the axial coordinate is constant. -/
theorem axial_add_smul_eTheta (x : R3) (t : ℝ) : axial (x + t • eTheta x) = axial x := by
  simp only [axial, WithLp.ofLp_add, WithLp.ofLp_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
    eTheta_apply_two, mul_zero, add_zero]

/-- Along `t ↦ x + t • e_θ(x)` the planar radius is `√(radSq x + t²)`. -/
theorem radial_add_smul_eTheta (x : R3) (hr : 0 < radial x) (t : ℝ) :
    radial (x + t • eTheta x) = Real.sqrt (radSq x + t ^ 2) := by
  rw [radial, radSq_add_smul_eTheta x hr t]

/-- Along `t ↦ x + t • e_θ(x)` the three-dimensional radius is `√(rho x ² + t²)`. -/
theorem rho_add_smul_eTheta (x : R3) (hr : 0 < radial x) (t : ℝ) :
    rho (x + t • eTheta x) = Real.sqrt (rho x ^ 2 + t ^ 2) := by
  rw [rho, rho_sq]
  rw [radSq_add_smul_eTheta x hr t, axial_add_smul_eTheta x t]
  ring_nf

/-- Along `t ↦ x + t • e_θ(x)` the angle is `arctan (x₃ / √(radSq x + t²))`. -/
theorem theta_add_smul_eTheta (x : R3) (hr : 0 < radial x) (t : ℝ) :
    theta (x + t • eTheta x) = Real.arctan (axial x / Real.sqrt (radSq x + t ^ 2)) := by
  rw [theta, radial_add_smul_eTheta x hr t, axial_add_smul_eTheta x t]

/-! ## The vanishing directional derivatives along `e_θ` -/




/-- `1/radial` has vanishing directional derivative along `e_θ`. -/
theorem fderiv_radialInv_eTheta (x : R3) (hr : 0 < radial x) :
    fderiv ℝ (fun y => (radial y)⁻¹) x (eTheta x) = 0 := by
  rw [fderiv_apply_eq_deriv_line (fun y => (radial y)⁻¹) x (eTheta x)
    ((differentiableAt_radial x (ne_of_gt hr)).inv (ne_of_gt hr))]
  have hfun : (fun t : ℝ => (radial (x + t • eTheta x))⁻¹) =
      fun t => (Real.sqrt (radSq x + t ^ 2))⁻¹ :=
    funext (fun t => by rw [radial_add_smul_eTheta x hr t])
  rw [hfun]
  exact deriv_zero_of_even (fun t => by rw [neg_sq])

/-- `e_θ = radial • e_θ / radial`, so the same vanishing holds in the direction `angularVec = r e_θ`. -/
theorem fderiv_radialInv_angularVec (x : R3) (hr : 0 < radial x) :
    fderiv ℝ (fun y => (radial y)⁻¹) x (angularVec x) = 0 := by
  have h : angularVec x = radial x • eTheta x := by
    rw [eTheta, smul_smul, one_div, mul_inv_cancel₀ (ne_of_gt hr), one_smul]
  rw [h, map_smul, fderiv_radialInv_eTheta x hr, smul_zero]

/-! ## Differentiability of the profile composite and the vorticity direction -/


/-- `e_θ` is differentiable off the axis. -/
theorem differentiableAt_eTheta (x : R3) (hr : 0 < radial x) : DifferentiableAt ℝ eTheta x := by
  have hrne : radial x ≠ 0 := ne_of_gt hr
  have hinv : DifferentiableAt ℝ (fun y => (radial y)⁻¹) x :=
    (differentiableAt_radial x hrne).inv hrne
  have hvec : DifferentiableAt ℝ angularVec x := by
    have h : angularVec = fun y : R3 => (-y 1) • e0 + (y 0) • e1 := by
      funext y
      apply ext_coord <;>
        simp [angularVec, e0, e1, FiniteTimeSingularity.e]
    rw [h]; fun_prop
  have hfun : eTheta = (fun y => (radial y)⁻¹) • angularVec := by
    funext y
    show (1 / radial y) • angularVec y = (radial y)⁻¹ • angularVec y
    rw [one_div]
  rw [hfun]
  exact hinv.smul hvec

/-- `e_θ` is divergence free off the axis. -/
theorem div_eTheta (x : R3) (hr : 0 < radial x) : FiniteTimeSingularity.div eTheta x = 0 := by
  have hrne : radial x ≠ 0 := ne_of_gt hr
  have hinv : DifferentiableAt ℝ (fun y => (radial y)⁻¹) x :=
    (differentiableAt_radial x hrne).inv hrne
  have hvec : DifferentiableAt ℝ angularVec x := by
    have h : angularVec = fun y : R3 => (-y 1) • e0 + (y 0) • e1 := by
      funext y
      apply ext_coord <;>
        simp [angularVec, e0, e1, FiniteTimeSingularity.e]
    rw [h]; fun_prop
  have hdivAng : FiniteTimeSingularity.div angularVec x = 0 := by
    rw [div_eq_sum_partials angularVec x hvec, Fin.sum_univ_three]
    have h0 : (fun t : ℝ => (angularVec (x + t • basisVec 0)).ofLp 0) = fun _ => - x 1 := by
      funext t; rw [basisVec_zero, angularVec_apply_zero, add_smul_e0_apply_one]
    have h1 : (fun t : ℝ => (angularVec (x + t • basisVec 1)).ofLp 1) = fun _ => x 0 := by
      funext t; rw [basisVec_one, angularVec_apply_one, add_smul_e1_apply_zero]
    have h2 : (fun t : ℝ => (angularVec (x + t • basisVec 2)).ofLp 2) = fun _ => (0:ℝ) := by
      funext t; rw [angularVec_apply_two]
    rw [h0, h1, h2]
    simp
  have hfun : eTheta = (fun y => (radial y)⁻¹) • angularVec := by
    funext y
    show (1 / radial y) • angularVec y = (radial y)⁻¹ • angularVec y
    rw [one_div]
  rw [hfun, div_smul_eq (fun y => (radial y)⁻¹) angularVec x hinv hvec, hdivAng,
    fderiv_radialInv_angularVec x hr]
  ring

/-! ## The directional derivative of the profile along `e_θ` -/


/-! ## The main theorem -/


end Work.ConstructionInstance
end
-- ===== merged: Submission.Work.ConstructionInstance.exists_sqrt_two_mul_rpow =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.ConstructionInstance


end Work.ConstructionInstance
end
-- ===== merged: Submission.Work.ConstructionInstance.g_z_linear_bound =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open Set Filter
open scoped Topology

namespace Work.ConstructionInstance

/-- **Linear bound for the modulation `g` near `z = 0`.**

`g` is `C²` on the open rectangle `(-1,∞) × (-1, π/2+1)` and vanishes on the line `z = 0`
(`hquad0`).  Then `g` is dominated by a linear function of `z` on the whole strip
`z ∈ [0,1]`, `θ ∈ [0,π/2]`.

Proof.  On the compact box `Q = [0,1] × [0,π/2]`, which is contained in the open set on which
`g` is `C²`, the partial derivative `φ(z,θ) = ∂_z g(z,θ)` — realised as
`(fderiv ℝ (uncurry g) (z,θ)) (1,0)` — is continuous, hence bounded by some `B ≥ 0`.  For each
`θ`, the mean-value inequality applied to the slice `z ↦ g z θ` on `[0,z]` with `g 0 θ = 0`
gives `|g z θ| ≤ B z`. -/
theorem g_z_linear_bound {g : ℝ → ℝ → ℝ} (hquad0 : ∀ θ : ℝ, g 0 θ = 0)
    (hsm : ContDiffOn ℝ 2 (Function.uncurry g)
      (Set.Ioi (-1) ×ˢ Set.Ioo (-1) (Real.pi / 2 + 1))) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ θ : ℝ, θ ∈ Work.Spaces.Iθ → ∀ z : ℝ, z ∈ Set.Icc (0:ℝ) 1 →
      |g z θ| ≤ K * z := by
  have hopen : IsOpen (Set.Ioi (-1) ×ˢ Set.Ioo (-1) (Real.pi / 2 + 1) : Set (ℝ × ℝ)) :=
    isOpen_Ioi.prod isOpen_Ioo
  have hQU : (Set.Icc (0:ℝ) 1 ×ˢ Work.Spaces.Iθ)
      ⊆ (Set.Ioi (-1) ×ˢ Set.Ioo (-1) (Real.pi / 2 + 1) : Set (ℝ × ℝ)) := by
    rintro p ⟨hz, hθ⟩
    rw [Work.Spaces.Iθ] at hθ
    exact ⟨by rw [Set.mem_Ioi]; linarith [hz.1],
      by constructor <;> linarith [hθ.1, hθ.2, Real.pi_pos]⟩
  have hQcompact : IsCompact (Set.Icc (0:ℝ) 1 ×ˢ Work.Spaces.Iθ) :=
    isCompact_Icc.prod (by rw [Work.Spaces.Iθ]; exact isCompact_Icc)
  have hderiv : ContinuousOn (fderiv ℝ (Function.uncurry g))
      (Set.Ioi (-1) ×ˢ Set.Ioo (-1) (Real.pi / 2 + 1)) :=
    hsm.continuousOn_fderiv_of_isOpen hopen (by norm_num)
  have hφcont : ContinuousOn
      (fun p : ℝ × ℝ => (fderiv ℝ (Function.uncurry g) p) (1, 0))
      (Set.Icc (0:ℝ) 1 ×ˢ Work.Spaces.Iθ) := by
    have hcc : ContinuousOn (fun _ : ℝ × ℝ => ((1:ℝ), (0:ℝ)))
        (Set.Icc (0:ℝ) 1 ×ˢ Work.Spaces.Iθ) := continuousOn_const
    exact (hderiv.mono hQU).clm_apply hcc
  obtain ⟨B, hB⟩ := hQcompact.exists_bound_of_continuousOn hφcont
  refine ⟨max B 0, le_max_right _ _, ?_⟩
  intro θ hθ z hz
  have hderivAt : ∀ x ∈ Set.Icc (0:ℝ) z,
      HasDerivWithinAt (fun y => g y θ) ((fderiv ℝ (Function.uncurry g) (x, θ)) (1, 0))
        (Set.Icc (0:ℝ) z) x := by
    intro x hx
    have hx0 : (0:ℝ) ≤ x := hx.1
    have hx1 : x ≤ 1 := le_trans hx.2 hz.2
    have hxU : (x, θ) ∈ (Set.Ioi (-1) ×ˢ Set.Ioo (-1) (Real.pi / 2 + 1) : Set (ℝ × ℝ)) :=
      hQU ⟨⟨hx0, hx1⟩, hθ⟩
    have hd : DifferentiableAt ℝ (Function.uncurry g) (x, θ) :=
      (hsm.differentiableOn (by norm_num)).differentiableAt (hopen.mem_nhds hxU)
    have hcomp : HasFDerivAt ((Function.uncurry g) ∘ (fun y : ℝ => (y, θ)))
        ((fderiv ℝ (Function.uncurry g) (x, θ)) ∘SL (ContinuousLinearMap.inl ℝ ℝ ℝ)) x :=
      hd.hasFDerivAt.comp x (hasFDerivAt_prodMk_left x θ)
    have h1 : HasDerivAt ((Function.uncurry g) ∘ (fun y : ℝ => (y, θ)))
        ((fderiv ℝ (Function.uncurry g) (x, θ)) (1, 0)) x := by
      simpa [ContinuousLinearMap.inl_apply] using hcomp.hasDerivAt
    exact h1.hasDerivWithinAt
  have hbound : ∀ x ∈ Set.Ico (0:ℝ) z,
      ‖(fderiv ℝ (Function.uncurry g) (x, θ)) (1, 0)‖ ≤ max B 0 := by
    intro x hx
    have hx0 : (0:ℝ) ≤ x := hx.1
    have hx1 : x ≤ 1 := le_trans (le_of_lt hx.2) hz.2
    have hmem : (x, θ) ∈ (Set.Icc (0:ℝ) 1 ×ˢ Work.Spaces.Iθ) := ⟨⟨hx0, hx1⟩, hθ⟩
    exact le_trans (hB _ hmem) (le_max_left _ _)
  have hMVT := norm_image_sub_le_of_norm_deriv_le_segment'
      (f := fun y => g y θ)
      (f' := fun x => (fderiv ℝ (Function.uncurry g) (x, θ)) (1, 0))
      (a := 0) (b := z) (C := max B 0) hderivAt hbound
  have hzmem : z ∈ Set.Icc (0:ℝ) z := ⟨hz.1, le_rfl⟩
  have hfin := hMVT z hzmem
  rw [hquad0 θ, sub_zero, sub_zero, Real.norm_eq_abs] at hfin
  exact hfin

end Work.ConstructionInstance
end
-- ===== merged: Submission.Work.ConstructionInstance.holder_of_half_odd =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.ConstructionInstance

open scoped NNReal

/-- Extend a Hölder map from the closed half space `{x₂ ≥ 0}` to `ℝ³` along the odd reflection
`Cyl.reflZ = (x₀,x₁,-x₂)`: if `Φ` is `α`-Hölder and vanishes on the plane `{x₂ = 0}`, and `ω`
agrees with `Φ` on `{x₂ ≥ 0}` and satisfies `ω (reflZ x) = - ω x`, then `ω` is `α`-Hölder
(with constant `3 C_Φ`).

Intended proof.  Let `C` be a Hölder constant of `Φ`.  For `x,y`:
* `x₂, y₂ ≥ 0`:  `ω x - ω y = Φ x - Φ y`, so `‖ω x - ω y‖ ≤ C ‖x-y‖^α`.
* `x₂, y₂ < 0`:  reflect both (`reflZ` preserves `dist`, and `ω (reflZ z) = -ω z`).
* `x₂ ≥ 0 > y₂`:  put `ry = reflZ y` (so `(ry)₂ = -y₂ ≥ 0`) and `yp = !₂[y 0, y 1, 0]`
  (so `(yp)₂ = 0`). Then
  `ω x - ω y = ω x + ω ry = (Φ x - Φ ry) + 2 (Φ ry - Φ yp)` (using `Φ yp = 0`), whence
  `‖ω x - ω y‖ ≤ C ‖x - ry‖^α + 2 C ‖ry - yp‖^α`.  Now `‖x - ry‖ ≤ ‖x - y‖` and
  `‖ry - yp‖ = |y₂| ≤ ‖x - y‖` (both from `Work.Cyl.dist_sq_coords`, using `x₂ ≥ 0 > y₂`),
  so the bound is `≤ 3 C ‖x-y‖^α`.
* `x₂ < 0 ≤ y₂`: symmetric.
Finish with `Work.Stability.holderWith_of_dist_le` (or `AuxOmegaStar.holder_of_norm_le`). -/
theorem holder_of_half_odd {ω Φ : R3 → R3} {α : ℝ} (hα : 0 < α)
    (hΦ : Holder ⟨α, hα.le⟩ Φ)
    (hhalf : ∀ x : R3, 0 ≤ x 2 → ω x = Φ x)
    (hodd : ∀ x : R3, ω (Work.Cyl.reflZ x) = - ω x)
    (hplane : ∀ x : R3, x 2 = 0 → Φ x = 0) :
    Holder ⟨α, hα.le⟩ ω := by
  obtain ⟨C, hC⟩ := hΦ
  have hΦb : ∀ a b : R3, ‖Φ a - Φ b‖ ≤ (C : ℝ) * ‖a - b‖ ^ α := by
    intro a b
    rw [← dist_eq_norm, ← dist_eq_norm]
    exact hC.dist_le a b
  have hCnn : (0 : ℝ) ≤ (C : ℝ) := C.coe_nonneg
  have key : ∀ x y : R3, ‖ω x - ω y‖ ≤ 3 * (C : ℝ) * ‖x - y‖ ^ α := by
    intro x y
    have hxy : (0 : ℝ) ≤ ‖x - y‖ ^ α := Real.rpow_nonneg (norm_nonneg _) _
    have refl2 : ∀ z : R3, (Work.Cyl.reflZ z) 2 = - z 2 := by
      intro z; simp [Work.Cyl.reflZ]
    -- the two "mixed" configurations all start from the same decomposition of `Φ a + Φ b`
    rcases le_or_gt (0 : ℝ) (x 2) with hx | hx
    · rcases le_or_gt (0 : ℝ) (y 2) with hy | hy
      · -- both points in the closed half space
        rw [hhalf x hx, hhalf y hy]
        calc ‖Φ x - Φ y‖ ≤ (C : ℝ) * ‖x - y‖ ^ α := hΦb x y
          _ ≤ 3 * (C : ℝ) * ‖x - y‖ ^ α := by nlinarith
      · -- `x₂ ≥ 0 > y₂`
        have hy2 : 0 ≤ (Work.Cyl.reflZ y) 2 := by rw [refl2]; linarith
        have hry : ω (Work.Cyl.reflZ y) = Φ (Work.Cyl.reflZ y) := hhalf _ hy2
        have hwx : ω x = Φ x := hhalf x hx
        have hwy : ω y = - Φ (Work.Cyl.reflZ y) := by
          have h := hodd y
          rw [hry] at h
          rw [h]; simp
        have hmid : Φ (!₂[y 0, y 1, (0:ℝ)]) = 0 := hplane _ (by simp)
        have h1 := (Work.Cyl.dist_mid_neg_le hx hy).1
        have h2 := (Work.Cyl.dist_mid_neg_le hx hy).2
        have hpb : ‖Φ x + Φ (Work.Cyl.reflZ y)‖ ≤ 2 * (C : ℝ) * ‖x - y‖ ^ α := by
          have hdec : Φ x + Φ (Work.Cyl.reflZ y)
              = (Φ x - Φ (!₂[y 0, y 1, (0:ℝ)]))
                + (Φ (Work.Cyl.reflZ y) - Φ (!₂[y 0, y 1, (0:ℝ)])) := by
            rw [hmid]; abel
          rw [hdec]
          have htri := norm_add_le (Φ x - Φ (!₂[y 0, y 1, (0:ℝ)]))
            (Φ (Work.Cyl.reflZ y) - Φ (!₂[y 0, y 1, (0:ℝ)]))
          have ha : ‖Φ x - Φ (!₂[y 0, y 1, (0:ℝ)])‖ ≤ (C : ℝ) * ‖x - y‖ ^ α := by
            calc ‖Φ x - Φ (!₂[y 0, y 1, (0:ℝ)])‖
                ≤ (C : ℝ) * ‖x - !₂[y 0, y 1, (0:ℝ)]‖ ^ α := hΦb x _
              _ ≤ (C : ℝ) * ‖x - y‖ ^ α := by
                  apply mul_le_mul_of_nonneg_left _ hCnn
                  apply Real.rpow_le_rpow (norm_nonneg _) _ hα.le
                  rw [← dist_eq_norm, ← dist_eq_norm]
                  exact h1
          have hb : ‖Φ (Work.Cyl.reflZ y) - Φ (!₂[y 0, y 1, (0:ℝ)])‖
              ≤ (C : ℝ) * ‖x - y‖ ^ α := by
            calc ‖Φ (Work.Cyl.reflZ y) - Φ (!₂[y 0, y 1, (0:ℝ)])‖
                ≤ (C : ℝ) * ‖Work.Cyl.reflZ y - !₂[y 0, y 1, (0:ℝ)]‖ ^ α := hΦb _ _
              _ ≤ (C : ℝ) * ‖x - y‖ ^ α := by
                  apply mul_le_mul_of_nonneg_left _ hCnn
                  apply Real.rpow_le_rpow (norm_nonneg _) _ hα.le
                  rw [← dist_eq_norm, ← dist_eq_norm]
                  exact h2
          calc ‖(Φ x - Φ (!₂[y 0, y 1, (0:ℝ)]))
                  + (Φ (Work.Cyl.reflZ y) - Φ (!₂[y 0, y 1, (0:ℝ)]))‖
              ≤ _ := htri
            _ ≤ (C : ℝ) * ‖x - y‖ ^ α + (C : ℝ) * ‖x - y‖ ^ α := add_le_add ha hb
            _ = 2 * (C : ℝ) * ‖x - y‖ ^ α := by ring
        have hsplit : ω x - ω y = Φ x + Φ (Work.Cyl.reflZ y) := by rw [hwx, hwy]; abel
        rw [hsplit]
        calc ‖Φ x + Φ (Work.Cyl.reflZ y)‖ ≤ 2 * (C : ℝ) * ‖x - y‖ ^ α := hpb
          _ ≤ 3 * (C : ℝ) * ‖x - y‖ ^ α := by nlinarith
    · rcases le_or_gt (0 : ℝ) (y 2) with hy | hy
      · -- `x₂ < 0 ≤ y₂`
        have hx2 : 0 ≤ (Work.Cyl.reflZ x) 2 := by rw [refl2]; linarith
        have hrx : ω (Work.Cyl.reflZ x) = Φ (Work.Cyl.reflZ x) := hhalf _ hx2
        have hwx : ω x = - Φ (Work.Cyl.reflZ x) := by
          have h := hodd x
          rw [hrx] at h
          rw [h]; simp
        have hwy : ω y = Φ y := hhalf y hy
        have hmid : Φ (!₂[y 0, y 1, (0:ℝ)]) = 0 := hplane _ (by simp)
        have h1 := (Work.Cyl.dist_mid_pos_le hx hy).1
        have h2 := (Work.Cyl.dist_mid_pos_le hx hy).2
        have hpb : ‖Φ (Work.Cyl.reflZ x) + Φ y‖ ≤ 2 * (C : ℝ) * ‖x - y‖ ^ α := by
          have hdec : Φ (Work.Cyl.reflZ x) + Φ y
              = (Φ (Work.Cyl.reflZ x) - Φ (!₂[y 0, y 1, (0:ℝ)]))
                + (Φ y - Φ (!₂[y 0, y 1, (0:ℝ)])) := by
            rw [hmid]; abel
          rw [hdec]
          have htri := norm_add_le (Φ (Work.Cyl.reflZ x) - Φ (!₂[y 0, y 1, (0:ℝ)]))
            (Φ y - Φ (!₂[y 0, y 1, (0:ℝ)]))
          have ha : ‖Φ (Work.Cyl.reflZ x) - Φ (!₂[y 0, y 1, (0:ℝ)])‖
              ≤ (C : ℝ) * ‖x - y‖ ^ α := by
            calc ‖Φ (Work.Cyl.reflZ x) - Φ (!₂[y 0, y 1, (0:ℝ)])‖
                ≤ (C : ℝ) * ‖Work.Cyl.reflZ x - !₂[y 0, y 1, (0:ℝ)]‖ ^ α := hΦb _ _
              _ ≤ (C : ℝ) * ‖x - y‖ ^ α := by
                  apply mul_le_mul_of_nonneg_left _ hCnn
                  apply Real.rpow_le_rpow (norm_nonneg _) _ hα.le
                  rw [← dist_eq_norm, ← dist_eq_norm]
                  exact h1
          have hb : ‖Φ y - Φ (!₂[y 0, y 1, (0:ℝ)])‖ ≤ (C : ℝ) * ‖x - y‖ ^ α := by
            calc ‖Φ y - Φ (!₂[y 0, y 1, (0:ℝ)])‖
                ≤ (C : ℝ) * ‖y - !₂[y 0, y 1, (0:ℝ)]‖ ^ α := hΦb y _
              _ ≤ (C : ℝ) * ‖x - y‖ ^ α := by
                  apply mul_le_mul_of_nonneg_left _ hCnn
                  apply Real.rpow_le_rpow (norm_nonneg _) _ hα.le
                  rw [← dist_eq_norm, ← dist_eq_norm]
                  exact h2
          calc ‖(Φ (Work.Cyl.reflZ x) - Φ (!₂[y 0, y 1, (0:ℝ)]))
                  + (Φ y - Φ (!₂[y 0, y 1, (0:ℝ)]))‖
              ≤ _ := htri
            _ ≤ (C : ℝ) * ‖x - y‖ ^ α + (C : ℝ) * ‖x - y‖ ^ α := add_le_add ha hb
            _ = 2 * (C : ℝ) * ‖x - y‖ ^ α := by ring
        have hsplit : ω x - ω y = - (Φ (Work.Cyl.reflZ x) + Φ y) := by rw [hwx, hwy]; abel
        rw [hsplit, norm_neg]
        calc ‖Φ (Work.Cyl.reflZ x) + Φ y‖ ≤ 2 * (C : ℝ) * ‖x - y‖ ^ α := hpb
          _ ≤ 3 * (C : ℝ) * ‖x - y‖ ^ α := by nlinarith
      · -- both points below the plane
        have hx2 : 0 ≤ (Work.Cyl.reflZ x) 2 := by rw [refl2]; linarith
        have hy2 : 0 ≤ (Work.Cyl.reflZ y) 2 := by rw [refl2]; linarith
        have hrx : ω (Work.Cyl.reflZ x) = Φ (Work.Cyl.reflZ x) := hhalf _ hx2
        have hry : ω (Work.Cyl.reflZ y) = Φ (Work.Cyl.reflZ y) := hhalf _ hy2
        have hwx : ω x = - Φ (Work.Cyl.reflZ x) := by
          have h := hodd x
          rw [hrx] at h
          rw [h]; simp
        have hwy : ω y = - Φ (Work.Cyl.reflZ y) := by
          have h := hodd y
          rw [hry] at h
          rw [h]; simp
        have hsplit : ω x - ω y
            = - (Φ (Work.Cyl.reflZ x) - Φ (Work.Cyl.reflZ y)) := by rw [hwx, hwy]; abel
        rw [hsplit, norm_neg]
        calc ‖Φ (Work.Cyl.reflZ x) - Φ (Work.Cyl.reflZ y)‖
            ≤ (C : ℝ) * ‖Work.Cyl.reflZ x - Work.Cyl.reflZ y‖ ^ α := hΦb _ _
          _ ≤ (C : ℝ) * ‖x - y‖ ^ α := by
              apply mul_le_mul_of_nonneg_left _ hCnn
              apply Real.rpow_le_rpow (norm_nonneg _) _ hα.le
              rw [← dist_eq_norm, ← dist_eq_norm]
              exact Work.Cyl.dist_reflZ_le x y
          _ ≤ 3 * (C : ℝ) * ‖x - y‖ ^ α := by nlinarith
  refine ⟨3 * C, ?_⟩
  apply Work.Stability.holderWith_of_dist_le (C := 3 * C) (r := ⟨α, hα.le⟩)
  intro x y
  rw [dist_eq_norm, dist_eq_norm]
  have hco : ((3 * C : ℝ≥0) : ℝ) = 3 * (C : ℝ) := by push_cast; ring
  rw [hco]
  exact key x y

end Work.ConstructionInstance
end
-- ===== merged: Submission.Work.ConstructionInstance.isOddVorticity_omegaS =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The parity class of the self-similar vorticity `omegaS`

`Work.LWP.IsOddVorticity ω` is the axial-reflection parity `ω (reflZ x) = - flipZ (ω x)` of the
vorticity of an odd axisymmetric no-swirl velocity field (Elgindi, Annals **194** (2021),
§Setup).  The self-similar vorticity of the construction,

  `omegaS p g x = profile p g (ρ(x)^p) (θ(x)) • e_θ(x)`,

is a field of exactly that shape: an angular profile times `e_θ`.  Under the reflection
`x ↦ (x₀, x₁, -x₃)` we have `ρ ↦ ρ`, `θ ↦ -θ`, `e_θ ↦ e_θ`, and `flipZ` acts on a scalar multiple
of the axis-free vector `e_θ` as the identity; so the parity of `omegaS p g` is the parity of the
profile, which is odd in `θ` (`profile_odd`) precisely because `g` vanishes at `θ = 0`
(`Work.Spaces.VanishTheta`) and `p ≠ 0` (so that `F_*(z,0) = 0`).

This module proves that dictionary:  `isOddVorticity_omegaS`.
-/

namespace Work.ConstructionInstance

/-! ## The `Cyl` coordinate dictionary under the reflection `reflZ` -/

/-- The three dimensional radius is invariant under the reflection in the plane `x₃ = 0`. -/
private lemma rho_reflZ_prv (x : Work.Cyl.R3) : Work.Cyl.rho (Work.Cyl.reflZ x) = Work.Cyl.rho x := by
  simp [Work.Cyl.rho, Work.Cyl.radSq, Work.Cyl.axial, Work.Cyl.reflZ]

/-- The polar angle changes sign under the reflection in the plane `x₃ = 0`. -/
private lemma theta_reflZ (x : Work.Cyl.R3) :
    Work.Cyl.theta (Work.Cyl.reflZ x) = - Work.Cyl.theta x := by
  simp [Work.Cyl.theta, Work.Cyl.radial, Work.Cyl.radSq, Work.Cyl.axial, Work.Cyl.reflZ, neg_div,
    Real.arctan_neg]

/-- The angular frame vector `e_θ` is invariant under the reflection in the plane `x₃ = 0` (it
lies in that plane). -/
private lemma eTheta_reflZ (x : Work.Cyl.R3) :
    Work.Cyl.eTheta (Work.Cyl.reflZ x) = Work.Cyl.eTheta x := by
  simp [Work.Cyl.eTheta, Work.Cyl.radial, Work.Cyl.radSq, Work.Cyl.angularVec, Work.Cyl.reflZ]

/-- The flip of the third component commutes with scalar multiplication. -/
private lemma flipZ_smul_prv (c : ℝ) (v : Work.Cyl.R3) :
    Work.Cyl.flipZ (c • v) = c • Work.Cyl.flipZ v := by
  apply Work.Cyl.ext_coord <;> simp [Work.Cyl.flipZ]

/-- The flip of the third component fixes `e_θ`. -/
private lemma flipZ_eTheta (x : Work.Cyl.R3) : Work.Cyl.flipZ (Work.Cyl.eTheta x) = Work.Cyl.eTheta x := by
  apply Work.Cyl.ext_coord <;> simp [Work.Cyl.flipZ, Work.Cyl.eTheta]

/-! ## The parity class of `omegaS` -/

theorem isOddVorticity_omegaS {p : ℝ} (hp : p ≠ 0) {g : ℝ → ℝ → ℝ}
    (hvt : Work.Spaces.VanishTheta g) :
    Work.LWP.IsOddVorticity (Work.ConstructionInstance.omegaS p g) := by
  intro x
  have hg0 : ∀ z : ℝ, g z 0 = 0 := hvt.1
  show Work.ConstructionInstance.profile p g (Work.Cyl.Rc p (Work.Cyl.reflZ x))
        (Work.Cyl.theta (Work.Cyl.reflZ x)) • Work.Cyl.eTheta (Work.Cyl.reflZ x)
      = - Work.Cyl.flipZ (Work.ConstructionInstance.profile p g (Work.Cyl.Rc p x)
        (Work.Cyl.theta x) • Work.Cyl.eTheta x)
  simp only [Work.Cyl.Rc, rho_reflZ_prv, theta_reflZ, eTheta_reflZ]
  rw [Work.ConstructionInstance.profile_odd hp hg0, neg_smul, flipZ_smul_prv, flipZ_eTheta]

end Work.ConstructionInstance
end
-- ===== merged: Submission.Work.ConstructionInstance.norm_vorticity_le =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.ConstructionInstance

/-- The standard basis vectors `e i` of `ℝ³` are unit vectors. -/
private lemma norm_e (i : Fin 3) : ‖FiniteTimeSingularity.e i‖ = (1 : ℝ) := by
  simp [FiniteTimeSingularity.e]

/-- The Euclidean norm of a coordinate cross product: `‖a × b‖ ≤ ‖a‖ ‖b‖`.

`crossProduct` (`⨯₃`) is Mathlib's bilinear form on `Fin 3 → ℝ`, and
`InnerProductGeometry.norm_ofLp_crossProduct` computes `‖a × b‖ = ‖a‖ ‖b‖ sin∠(a,b)`. -/
private lemma norm_toLp_cross_le (a b : R3) :
    ‖WithLp.toLp 2 (crossProduct a b)‖ ≤ ‖a‖ * ‖b‖ := by
  rw [InnerProductGeometry.norm_ofLp_crossProduct a b]
  calc ‖a‖ * ‖b‖ * Real.sin (InnerProductGeometry.angle a b)
      ≤ ‖a‖ * ‖b‖ * 1 := mul_le_mul_of_nonneg_left (Real.sin_le_one _) (by positivity)
    _ = ‖a‖ * ‖b‖ := by ring

theorem norm_vorticity_le (u : Work.ConstructionInstance.R3 → Work.ConstructionInstance.R3)
    (x : Work.ConstructionInstance.R3) :
    ‖FiniteTimeSingularity.vorticity u x‖ ≤ 3 * ‖fderiv ℝ u x‖ := by
  -- Bring the `WithLp.toLp` inside the sum, so that the triangle inequality applies termwise.
  have hsplit : FiniteTimeSingularity.vorticity u x
      = ∑ i : Fin 3,
          WithLp.toLp 2 (crossProduct (FiniteTimeSingularity.e i)
            (fderiv ℝ u x (FiniteTimeSingularity.e i))) := by
    rw [show FiniteTimeSingularity.vorticity u x
        = WithLp.toLp 2 (∑ i : Fin 3,
            crossProduct (FiniteTimeSingularity.e i)
              (fderiv ℝ u x (FiniteTimeSingularity.e i))) from rfl]
    exact WithLp.toLp_sum 2 (Fin 3 → ℝ) Finset.univ _
  rw [hsplit]
  calc ‖∑ i : Fin 3, WithLp.toLp 2 (crossProduct (FiniteTimeSingularity.e i)
          (fderiv ℝ u x (FiniteTimeSingularity.e i)))‖
      ≤ ∑ i : Fin 3, ‖WithLp.toLp 2 (crossProduct (FiniteTimeSingularity.e i)
          (fderiv ℝ u x (FiniteTimeSingularity.e i)))‖ :=
        norm_sum_le _ _
    _ ≤ ∑ i : Fin 3, ‖FiniteTimeSingularity.e i‖ * ‖fderiv ℝ u x (FiniteTimeSingularity.e i)‖ :=
        Finset.sum_le_sum (fun i _ => norm_toLp_cross_le _ _)
    _ ≤ ∑ _i : Fin 3, ‖fderiv ℝ u x‖ := by
        apply Finset.sum_le_sum
        intro i _
        have h := ContinuousLinearMap.le_opNorm (fderiv ℝ u x) (FiniteTimeSingularity.e i)
        rw [norm_e i, mul_one] at h
        calc ‖FiniteTimeSingularity.e i‖ * ‖fderiv ℝ u x (FiniteTimeSingularity.e i)‖
            ≤ 1 * (‖fderiv ℝ u x‖ * 1) :=
              mul_le_mul (le_of_eq (norm_e i)) (by simpa using h) (norm_nonneg _) (by norm_num)
          _ = ‖fderiv ℝ u x‖ := by ring
    _ = 3 * ‖fderiv ℝ u x‖ := by simp

end Work.ConstructionInstance
end
-- ===== merged: Submission.Work.ConstructionInstance.omegaSz_ray_quad =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.ConstructionInstance

/-- **The self-similar vorticity on the ray `x = (t,0,t)`, at a prescribed self-similar variable.**

On this ray (`t > 0`) one has `r = t`, `θ = arctan 1 = π/4` and `e_θ = e₁ = (0,1,0)`, so
`omegaSz p g z x = profile p g z (θ x) • e_θ(x) = profile p g z (π/4) • e₁`. -/
theorem omegaSz_ray_quad {p z t : ℝ} (ht : 0 < t) (g : ℝ → ℝ → ℝ) :
    Work.ConstructionInstance.omegaSz p g z (!₂[t, 0, t] : Work.ConstructionInstance.R3)
      = Work.ConstructionInstance.profile p g z (Real.pi / 4)
        • (!₂[0, 1, 0] : Work.ConstructionInstance.R3) := by
  -- `θ = arctan(t/t) = arctan 1 = π/4`.
  have htheta : Work.Cyl.theta (!₂[t, 0, t] : R3) = Real.pi / 4 := by
    rw [Work.Cyl.theta, Work.Cyl.axial, Work.Cyl.radial, Work.Cyl.radSq]
    simp
    rw [Real.sqrt_sq ht.le, div_self (ne_of_gt ht)]
  -- `e_θ = (-x₁, x₀, 0)/r = (0,1,0) = e₁`.
  have he : Work.Cyl.eTheta (!₂[t, 0, t] : R3) = (!₂[0, 1, 0] : R3) := by
    refine Work.Cyl.ext_coord ?_ ?_ ?_ <;>
      simp [Work.Cyl.eTheta, Work.Cyl.angularVec, Work.Cyl.radial, Work.Cyl.radSq,
        Real.sqrt_sq ht.le, ht.ne']
  rw [omegaSz_apply, htheta, he]

end Work.ConstructionInstance
end
-- ===== merged: Submission.Work.ConstructionInstance.profile_abs_lower_one =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.ConstructionInstance

theorem profile_abs_lower_one {p : ℝ} (hp : 0 < p) (hp1 : p ≤ 1) {g : ℝ → ℝ → ℝ} {Cg : ℝ}
    (hgbdd : ∀ z θ : ℝ, 0 ≤ z → θ ∈ Work.Spaces.Iθ → |g z θ| ≤ Cg)
    (hsmall : Cg ≤ p * Work.Spaces.Gam p (Real.pi / 4) / (4 * Work.Spaces.c p)) :
    p * Work.Spaces.Gam p (Real.pi / 4) / (4 * Work.Spaces.c p)
      ≤ |Work.ConstructionInstance.profile p g 1 (Real.pi / 4)| := by
  -- The point `π/4` lies in the angular domain.
  have hpi4 : (Real.pi / 4) ∈ Work.Spaces.Iθ :=
    ⟨by positivity, by linarith [Real.pi_pos]⟩
  -- Positivity of the normalisation constant `c p`.
  have hcpos : 0 < Work.Spaces.c p := by
    have := (Work.Spaces.c_bounds p hp hp1).1; linarith
  -- Nonnegativity of `Gam p (π/4)`.
  have hGam0 : 0 ≤ Work.Spaces.Gam p (Real.pi / 4) := by
    rw [Work.Spaces.Gam]
    exact Real.rpow_nonneg (by
      have hs : 0 ≤ Real.sin (Real.pi / 4) :=
        Real.sin_nonneg_of_nonneg_of_le_pi (by positivity) (by linarith [Real.pi_pos])
      positivity) _
  -- The right-hand side constant `A = p·Gam p (π/4)/(4 c p)` is nonnegative.
  have hA0 : 0 ≤ p * Work.Spaces.Gam p (Real.pi / 4) / (4 * Work.Spaces.c p) :=
    div_nonneg (mul_nonneg hp.le hGam0) (by positivity)
  -- The profile value at `z = 1` is exactly twice `A` (since `2·1/(1+1)² = 1/2`).
  have hF : Work.Construction.Fstar p 1 (Real.pi / 4)
      = 2 * (p * Work.Spaces.Gam p (Real.pi / 4) / (4 * Work.Spaces.c p)) := by
    have hcne : Work.Spaces.c p ≠ 0 := ne_of_gt hcpos
    rw [Work.Construction.Fstar, Work.FM.Fstar]
    norm_num
    field_simp
    ring
  -- Unfold the (odd) profile at the nonnegative angle `π/4`.
  have hprof : profile p g 1 (Real.pi / 4)
      = Work.Construction.Fstar p 1 (Real.pi / 4) + g 1 (Real.pi / 4) := by
    rw [profile_of_nonneg (by positivity)]
  -- The bound on `g` transported to the point `(1, π/4)`.
  have hg : |g 1 (Real.pi / 4)| ≤ p * Work.Spaces.Gam p (Real.pi / 4) / (4 * Work.Spaces.c p) :=
    le_trans (hgbdd 1 (Real.pi / 4) (by norm_num) hpi4) hsmall
  rw [hprof, hF]
  -- Reverse triangle inequality: `|2A + g| ≥ |2A| - |g| = 2A - |g| ≥ A`.
  have key : |2 * (p * Work.Spaces.Gam p (Real.pi / 4) / (4 * Work.Spaces.c p))
        + g 1 (Real.pi / 4)|
      ≥ 2 * (p * Work.Spaces.Gam p (Real.pi / 4) / (4 * Work.Spaces.c p))
        - |g 1 (Real.pi / 4)| := by
    have h := abs_add_le (2 * (p * Work.Spaces.Gam p (Real.pi / 4) / (4 * Work.Spaces.c p))
        + g 1 (Real.pi / 4)) (-(g 1 (Real.pi / 4)))
    rw [abs_neg] at h
    have heq : 2 * (p * Work.Spaces.Gam p (Real.pi / 4) / (4 * Work.Spaces.c p))
        + g 1 (Real.pi / 4) + -(g 1 (Real.pi / 4))
        = 2 * (p * Work.Spaces.Gam p (Real.pi / 4) / (4 * Work.Spaces.c p)) := by ring
    rw [heq, abs_of_nonneg (by linarith)] at h
    linarith
  linarith [key, hg, hA0]

end Work.ConstructionInstance
end
-- ===== merged: Submission.Work.ConstructionInstance.profile_add_z_pz_abs_le =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

namespace Work.ConstructionInstance

/-! ## The `F_*` box: `|F_*(z,θ) + z ∂_z F_*(z,θ)| ≤ 20p`

The two `F_*` terms are combined *before* the triangle inequality: the sum collapses to
`p(Γ(θ)/c(p))·4z/(1+z)³`, which is bounded by `20p` uniformly in `z`. -/

/-- `F_*(z,θ) + z·∂_zF_*(z,θ) = p·(Γ(θ)/c(p))·4z/(1+z)³`. -/
theorem Fstar_add_zpz_eq {p : ℝ} (hp : 0 < p) (hp1 : p ≤ 1) {z θ : ℝ} (hz : -1 < z) :
    Work.Construction.Fstar p z θ + z * Work.Spaces.pz (Work.Construction.Fstar p) z θ
      = p * (Work.Spaces.Gam p θ / Work.Spaces.c p) * (4 * z / (1 + z) ^ 3) := by
  have hDz : z * Work.Spaces.pz (Work.Construction.Fstar p) z θ
      = p * (Work.Spaces.Gam p θ / Work.Spaces.c p) * (2 * z * (1 - z) / (1 + z) ^ 3) :=
    Work.Construction.Dz_Fstar_eq hp hz
  have hz1 : (1 + z) ^ 3 ≠ 0 := by
    have : (0 : ℝ) < 1 + z := by linarith
    positivity
  have hc : Work.Spaces.c p ≠ 0 := by
    have := (Work.Spaces.c_bounds p hp hp1).1; linarith
  rw [hDz, Work.Construction.Fstar, Work.FM.Fstar]
  field_simp
  ring

/-- **The `F_*` part of the `z`-derivative box.**  For `0 < p ≤ 1`, `z > 0`, `θ ∈ [0,π/2]`,
`|F_*(z,θ) + z∂_zF_*(z,θ)| ≤ 20p`. -/
theorem Fstar_add_zpz_abs_le {p : ℝ} (hp : 0 < p) (hp1 : p ≤ 1) {z θ : ℝ} (hz : 0 < z)
    (hθ : θ ∈ Work.Spaces.Iθ) :
    |Work.Construction.Fstar p z θ + z * Work.Spaces.pz (Work.Construction.Fstar p) z θ|
      ≤ 20 * p := by
  have hc := (Work.Spaces.c_bounds p hp hp1).1
  have hcpos : 0 < Work.Spaces.c p := by linarith
  have hG0 : 0 ≤ Work.Spaces.Gam p θ := (Work.Spaces.Gam_bounds p θ hp hθ).1
  have hG1 : Work.Spaces.Gam p θ ≤ 1 := (Work.Spaces.Gam_bounds p θ hp hθ).2
  have hz1 : (0 : ℝ) < (1 + z) ^ 3 := by positivity
  have hgc0 : 0 ≤ Work.Spaces.Gam p θ / Work.Spaces.c p := div_nonneg hG0 hcpos.le
  have h1 : Work.Spaces.Gam p θ / Work.Spaces.c p ≤ 10 := by
    rw [div_le_iff₀ hcpos]; nlinarith [hG1]
  have hfrac0 : 0 ≤ 4 * z / (1 + z) ^ 3 := by positivity
  have h2 : 4 * z / (1 + z) ^ 3 ≤ 1 := by
    rw [div_le_one hz1]
    nlinarith [sq_nonneg z, mul_nonneg (sq_nonneg z) hz.le]
  rw [Fstar_add_zpz_eq hp hp1 (by linarith)]
  calc |p * (Work.Spaces.Gam p θ / Work.Spaces.c p) * (4 * z / (1 + z) ^ 3)|
      = p * (Work.Spaces.Gam p θ / Work.Spaces.c p) * (4 * z / (1 + z) ^ 3) :=
        abs_of_nonneg (mul_nonneg (mul_nonneg hp.le hgc0) hfrac0)
    _ ≤ p * 10 * 1 := by
        apply mul_le_mul
        · exact mul_le_mul_of_nonneg_left h1 hp.le
        · exact h2
        · exact hfrac0
        · positivity
    _ = 10 * p := by ring
    _ ≤ 20 * p := by linarith [hp.le]

/-! ## Differentiability of `F_*` in `z` at fixed `θ` -/

/-- `z ↦ F_*(z,θ)` has derivative `∂_zF_*(z,θ)` for `z > -1`. -/
theorem hasDerivAt_Fstar_z {p : ℝ} (z θ : ℝ) (hz : -1 < z) :
    HasDerivAt (fun z' => Work.Construction.Fstar p z' θ)
      (Work.Spaces.pz (Work.Construction.Fstar p) z θ) z := by
  have h := (Work.FM.hasDerivAt_Fstar z hz).const_mul
    (p * (Work.Spaces.Gam p θ / Work.Spaces.c p))
  have hfun : (fun z' => Work.Construction.Fstar p z' θ)
      = fun z' => (p * (Work.Spaces.Gam p θ / Work.Spaces.c p)) * Work.FM.Fstar z' := by
    funext z'; rw [Work.Construction.Fstar]
  have hval : Work.Spaces.pz (Work.Construction.Fstar p) z θ
      = (p * (Work.Spaces.Gam p θ / Work.Spaces.c p)) * (2 * (1 - z) / (1 + z) ^ 3) := by
    rw [Work.Spaces.pz, hfun, deriv_const_mul_field, Work.FM.deriv_Fstar z hz]
  rw [hfun, hval]
  exact h

/-! ## Splitting `∂_zF` into `∂_zF_* + ∂_zg` -/

/-- **Splitting the `z`-derivative of the profile on the positive angular branch**:
for `θ ≥ 0`, differentiating `F = F_* + g` in `z` gives `∂_zF = ∂_zg + ∂_zF_*`.  The
hypothesis `hgdiff` (together with the differentiability of `F_*`) is what makes `g`
differentiable, so that `deriv` splits. -/
theorem pz_profile_eq_of_nonneg {p : ℝ} {g : ℝ → ℝ → ℝ} {z θ : ℝ} (hz : -1 < z) (hθ : 0 ≤ θ)
    (hgdiff : HasDerivAt (fun z' => profile p g z' θ) (Work.Spaces.pz (profile p g) z θ) z) :
    Work.Spaces.pz (profile p g) z θ
      = Work.Spaces.pz g z θ + Work.Spaces.pz (Work.Construction.Fstar p) z θ := by
  have hF := hasDerivAt_Fstar_z (p := p) z θ hz
  have hsub := hgdiff.sub hF
  have hfun : ((fun z' => profile p g z' θ) - fun z' => Work.Construction.Fstar p z' θ)
      = fun z' => g z' θ := by
    funext z'; simp only [Pi.sub_apply]; rw [profile_of_nonneg hθ]; ring
  rw [hfun] at hsub
  have hd := hsub.deriv
  simp only [Work.Spaces.pz] at hd ⊢
  linarith [hd]

/-- **Splitting the `z`-derivative of the profile on the negative angular branch**:
for `θ < 0`, `F(z,θ) = -(F_*(z,-θ) + g(z,-θ))`, so
`∂_zF(z,θ) = -(∂_zg(z,-θ) + ∂_zF_*(z,-θ))`. -/
theorem pz_profile_eq_of_neg {p : ℝ} {g : ℝ → ℝ → ℝ} {z θ : ℝ} (hz : -1 < z) (hθ : θ < 0)
    (hgdiff : HasDerivAt (fun z' => profile p g z' θ) (Work.Spaces.pz (profile p g) z θ) z) :
    Work.Spaces.pz (profile p g) z θ
      = -(Work.Spaces.pz g z (-θ) + Work.Spaces.pz (Work.Construction.Fstar p) z (-θ)) := by
  have hF := hasDerivAt_Fstar_z (p := p) z (-θ) hz
  have hEq : (fun z' => profile p g z' θ)
      = fun z' => -(Work.Construction.Fstar p z' (-θ) + g z' (-θ)) := by
    funext z'; rw [profile_of_neg (not_le.mpr hθ)]
  rw [hEq] at hgdiff
  have hneg : HasDerivAt (fun z' => Work.Construction.Fstar p z' (-θ) + g z' (-θ))
      (-(Work.Spaces.pz (profile p g) z θ)) z := by
    convert hgdiff.neg using 1
    funext z'; simp
  have hsub := hneg.sub hF
  have hfun : ((fun z' => Work.Construction.Fstar p z' (-θ) + g z' (-θ))
        - fun z' => Work.Construction.Fstar p z' (-θ)) = fun z' => g z' (-θ) := by
    funext z'; simp only [Pi.sub_apply]; ring
  rw [hfun] at hsub
  have hd := hsub.deriv
  simp only [Work.Spaces.pz] at hd ⊢
  linarith [hd]

/-! ## The `z`-derivative box -/

/-- **The `z`-derivative box of the profile.**  For `0 < p ≤ 1`, `z > 0`, `|θ| ≤ π/2`, with the
perturbation `g` bounded by `Cg` and its `z`-weighted derivative `z∂_z g` bounded by `Cg'`, and with
the profile `F = F_* + g` differentiable in `z` (hypothesis `hgdiff`, which is `HasDerivAt` with
the derivative *defined* to be `Work.Spaces.pz (profile p g) z θ`), we have

  `|F(z,θ) + z∂_zF(z,θ)| ≤ 20p + Cg + Cg'`.

The point of the statement is that the two `F_*` terms are combined *before* the triangle inequality:
`F_*(z,θ) + z∂_zF_*(z,θ) = p(Γ(θ)/c(p))·4z/(1+z)³`, which is bounded by `20p` uniformly in `z`,
whereas `|F_*|` and `|z∂_zF_*|` separately are bounded only by `20pΓ` and `5p`. -/
theorem profile_add_z_pz_abs_le {p : ℝ} (hp : 0 < p) (hp1 : p ≤ 1) {g : ℝ → ℝ → ℝ} {Cg Cg' : ℝ}
    (hgbdd : ∀ z θ : ℝ, 0 ≤ z → θ ∈ Work.Spaces.Iθ → |g z θ| ≤ Cg)
    (hg2 : ∀ z θ : ℝ, 0 ≤ z → θ ∈ Work.Spaces.Iθ → |z * Work.Spaces.pz g z θ| ≤ Cg')
    (hgdiff : ∀ z θ : ℝ, 0 < z →
      HasDerivAt (fun z' => profile p g z' θ) (Work.Spaces.pz (profile p g) z θ) z)
    {z θ : ℝ} (hz : 0 < z) (hθ : |θ| ≤ Real.pi / 2) :
    |profile p g z θ + z * Work.Spaces.pz (profile p g) z θ| ≤ 20 * p + Cg + Cg' := by
  have hz1 : -1 < z := by linarith
  -- the box for the perturbation `g`, on the positive branch
  have hgbox : ∀ φ : ℝ, φ ∈ Work.Spaces.Iθ →
      |g z φ + z * Work.Spaces.pz g z φ| ≤ Cg + Cg' := by
    intro φ hφ
    calc |g z φ + z * Work.Spaces.pz g z φ|
        ≤ |g z φ| + |z * Work.Spaces.pz g z φ| := abs_add_le _ _
      _ ≤ Cg + Cg' := add_le_add (hgbdd z φ hz.le hφ) (hg2 z φ hz.le hφ)
  rcases le_or_gt 0 θ with hθ0 | hθ0
  · -- positive branch
    have hθmem : θ ∈ Work.Spaces.Iθ :=
      ⟨hθ0, by rw [abs_of_nonneg hθ0] at hθ; exact hθ⟩
    have hsplit := pz_profile_eq_of_nonneg (p := p) (g := g) (z := z) (θ := θ) hz1 hθ0
      (hgdiff z θ hz)
    have hprof : profile p g z θ = Work.Construction.Fstar p z θ + g z θ := profile_of_nonneg hθ0
    have hkey : profile p g z θ + z * Work.Spaces.pz (profile p g) z θ
        = (Work.Construction.Fstar p z θ + z * Work.Spaces.pz (Work.Construction.Fstar p) z θ)
          + (g z θ + z * Work.Spaces.pz g z θ) := by
      rw [hprof, hsplit]; ring
    rw [hkey]
    calc |(Work.Construction.Fstar p z θ + z * Work.Spaces.pz (Work.Construction.Fstar p) z θ)
            + (g z θ + z * Work.Spaces.pz g z θ)|
        ≤ |Work.Construction.Fstar p z θ + z * Work.Spaces.pz (Work.Construction.Fstar p) z θ|
            + |g z θ + z * Work.Spaces.pz g z θ| := abs_add_le _ _
      _ ≤ 20 * p + (Cg + Cg') :=
          add_le_add (Fstar_add_zpz_abs_le hp hp1 hz hθmem) (hgbox θ hθmem)
      _ = 20 * p + Cg + Cg' := by ring
  · -- negative branch: reduce to `-θ > 0`
    have hθmem : -θ ∈ Work.Spaces.Iθ :=
      ⟨by linarith, by rw [abs_of_neg hθ0] at hθ; exact hθ⟩
    have hsplit := pz_profile_eq_of_neg (p := p) (g := g) (z := z) (θ := θ) hz1 hθ0
      (hgdiff z θ hz)
    have hprof : profile p g z θ
        = -(Work.Construction.Fstar p z (-θ) + g z (-θ)) := profile_of_neg (not_le.mpr hθ0)
    have hkey : profile p g z θ + z * Work.Spaces.pz (profile p g) z θ
        = -((Work.Construction.Fstar p z (-θ)
              + z * Work.Spaces.pz (Work.Construction.Fstar p) z (-θ))
            + (g z (-θ) + z * Work.Spaces.pz g z (-θ))) := by
      rw [hprof, hsplit]; ring
    rw [hkey, abs_neg]
    calc |(Work.Construction.Fstar p z (-θ) + z * Work.Spaces.pz (Work.Construction.Fstar p) z (-θ))
            + (g z (-θ) + z * Work.Spaces.pz g z (-θ))|
        ≤ |Work.Construction.Fstar p z (-θ) + z * Work.Spaces.pz (Work.Construction.Fstar p) z (-θ)|
            + |g z (-θ) + z * Work.Spaces.pz g z (-θ)| := abs_add_le _ _
      _ ≤ 20 * p + (Cg + Cg') :=
          add_le_add (Fstar_add_zpz_abs_le hp hp1 hz hθmem) (hgbox (-θ) hθmem)
      _ = 20 * p + Cg + Cg' := by ring

end Work.ConstructionInstance
end
end
-- ===== merged: Submission.Work.ConstructionInstance.selfSim_profile_eTheta_coord_eq_zero =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.ConstructionInstance

/-- The `j`-th coordinate of the `i`-th standard basis vector of `ℝ³` is `0` when `j ≠ i`. -/
lemma basisVec_apply_of_ne {i j : Fin 3} (h : j ≠ i) : (Work.Cyl.basisVec i) j = 0 := by
  simp only [Work.Cyl.basisVec, FiniteTimeSingularity.e, WithLp.ofLp_toLp, Pi.single_apply]
  exact ite_eq_right h

/-- Shifting along `basisVec i` with `i ≠ 2` does not change the axial coordinate. -/
lemma axial_add_smul_basisVec_of_ne_two {i : Fin 3} (hi : i ≠ 2) (x : R3) (t : ℝ) :
    Work.Cyl.axial (x + t • Work.Cyl.basisVec i) = Work.Cyl.axial x := by
  rw [Work.Cyl.axial, Work.Cyl.axial]
  simp only [WithLp.ofLp_add, WithLp.ofLp_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
    basisVec_apply_of_ne (Ne.symm hi), mul_zero, add_zero]

/-- Shifting along `basisVec i` with `i ≠ 2` keeps a point in the plane `x₃ = 0`: the polar
angle `θ` of the shifted point vanishes. -/
lemma theta_add_smul_basisVec_eq_zero_of_axial_eq_zero {i : Fin 3} (hi : i ≠ 2)
    {x : R3} (hx : Work.Cyl.axial x = 0) (t : ℝ) :
    Work.Cyl.theta (x + t • Work.Cyl.basisVec i) = 0 := by
  rw [Work.Cyl.theta, axial_add_smul_basisVec_of_ne_two hi x t, hx, zero_div, Real.arctan_zero]

/-- **The profile times the `i`-th coordinate of `e_θ` vanishes** for the point `x + t • eᵢ`
whenever `x` lies on the axis (`radial x = 0`) or in the plane `x₃ = 0` (`axial x = 0`).

The two vanishing mechanisms are complementary: if `x` is on the axis (`r = 0`) then the
`i`-th coordinate of `e_θ` vanishes at the shifted point (both because `e_θ` has no axial
component and because the relevant in-plane coordinate of the shifted point is inherited
from `x`); if `x` lies in the plane `x₃ = 0` and `i ≠ 2` the shift preserves `x₃ = 0`, so the
polar angle `θ` vanishes and the profile — which is odd in `θ` and vanishes at `θ = 0` by
`hg0` — is zero. -/
theorem selfSim_profile_eTheta_coord_eq_zero {p c : ℝ} (hp : p ≠ 0) {g : ℝ → ℝ → ℝ}
    (hg0 : ∀ z : ℝ, g z 0 = 0) {x : Work.ConstructionInstance.R3}
    (hx : Work.Cyl.radial x = 0 ∨ Work.Cyl.axial x = 0) (i : Fin 3) (t : ℝ) :
    Work.ConstructionInstance.profile p g (Work.Cyl.rho (x + t • Work.Cyl.basisVec i) ^ p / c)
        (Work.Cyl.theta (x + t • Work.Cyl.basisVec i))
      * (Work.Cyl.eTheta (x + t • Work.Cyl.basisVec i)) i = 0 := by
  rcases hx with hx | hx
  · -- `radial x = 0`: the `i`-th coordinate of `e_θ` at the shifted point vanishes.
    have hx0 : x 0 = 0 := ((Work.Cyl.radial_eq_zero_iff x).mp hx).1
    have hx1 : x 1 = 0 := ((Work.Cyl.radial_eq_zero_iff x).mp hx).2
    have h : (Work.Cyl.eTheta (x + t • Work.Cyl.basisVec i)) i = 0 := by
      fin_cases i <;>
        simp [Work.Cyl.eTheta, Work.Cyl.angularVec, Work.Cyl.basisVec, FiniteTimeSingularity.e,
          hx0, hx1]
    rw [h, mul_zero]
  · -- `axial x = 0`: if `i ≠ 2` the shift preserves `x₃ = 0`; if `i = 2` the axial component
    -- of `e_θ` vanishes.
    by_cases hi : i = 2
    · subst hi
      rw [Work.Cyl.eTheta_apply_two, mul_zero]
    · rw [theta_add_smul_basisVec_eq_zero_of_axial_eq_zero hi hx t,
        Work.ConstructionInstance.profile_zero hp hg0, zero_mul]

end Work.ConstructionInstance
end
-- ===== merged: Submission.Work.ConstructionInstance.selfSim_scalar_differentiableAt =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.ConstructionInstance

/-- **Differentiability of the scalar self-similar vorticity profile.**

At a point `x` off the axis (`0 < radial x`) at which the profile `F = profile p g` is
differentiable as a function of two variables at the self-similar point
`(ρ(x)^p / c, θ(x))`, the scalar field

  `y ↦ c⁻¹ * F (ρ(y)^p / c) (θ(y))`

is differentiable at `x`.

The proof is the chain rule: `ρ` is differentiable at `x` (`Work.Cyl.differentiableAt_rho_of_radial_pos`,
legitimate since `radial x > 0`), hence so is `y ↦ ρ(y)^p / c` (rpow with nonzero base
`ρ x ≠ 0`, then division by the constant `c`); together with the differentiability of `θ`
(`Work.Cyl.differentiableAt_theta_of_radial_ne`) this makes `y ↦ (ρ(y)^p / c, θ(y))`
differentiable at `x`, and composing with `hF` and multiplying by the constant `c⁻¹` gives the
claim. -/
theorem selfSim_scalar_differentiableAt {p c : ℝ} {g : ℝ → ℝ → ℝ} {x : Work.ConstructionInstance.R3}
    (hr : 0 < Work.Cyl.radial x)
    (hF : Work.Cyl.DiffAt2 (Work.ConstructionInstance.profile p g) (Work.Cyl.rho x ^ p / c)
      (Work.Cyl.theta x)) :
    DifferentiableAt ℝ
      (fun y : Work.ConstructionInstance.R3 =>
        c⁻¹ * Work.ConstructionInstance.profile p g (Work.Cyl.rho y ^ p / c)
          (Work.Cyl.theta y)) x := by
  have hrne : Work.Cyl.radial x ≠ 0 := ne_of_gt hr
  have hrho_ne : Work.Cyl.rho x ≠ 0 :=
    ne_of_gt (lt_of_lt_of_le hr (Work.Cyl.radial_le_rho x))
  have hpow : DifferentiableAt ℝ (fun y : Work.ConstructionInstance.R3 => Work.Cyl.rho y ^ p) x :=
    (Work.Cyl.differentiableAt_rho_of_radial_pos x hr).rpow_const (Or.inl hrho_ne)
  have hdiv : DifferentiableAt ℝ
      (fun y : Work.ConstructionInstance.R3 => Work.Cyl.rho y ^ p / c) x := by
    simpa only [div_eq_mul_inv] using hpow.mul_const c⁻¹
  have hpair : DifferentiableAt ℝ
      (fun y : Work.ConstructionInstance.R3 =>
        (Work.Cyl.rho y ^ p / c, Work.Cyl.theta y)) x :=
    hdiv.prodMk (Work.Cyl.differentiableAt_theta_of_radial_ne x hrne)
  exact (hF.comp x hpair).const_mul c⁻¹

end Work.ConstructionInstance
end
-- ===== merged: Submission.Work.ConstructionInstance.timeHolderOnBall_of_timeDeriv_le =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.ConstructionInstance

open Set Metric
open scoped Topology

/-- **A time-Lipschitz bound for the vorticity from a bound on `∂ₜω`.**

If, on the ball of radius `R`, every time slice `t ↦ ω z t` is differentiable on the window
`window S = [-1, S+1]` with derivative `∂ₜω z`, and `‖∂ₜω z t‖ ≤ Λ` there, then `ω` is
`α`-Hölder in time on that ball and window for every `0 < α ≤ 1`.

The proof is the mean value theorem (bounded derivative ⟹ `Λ`-Lipschitz in time, on the convex
window) followed by the elementary `|t-τ| ≤ max(S+2) 1 · |t-τ|^α` on a set of diameter `S+2`
(`Work.SolutionDelivery.Holder.self_le_max_mul_rpow`); the constant is
`H = Λ · max (S+2) 1`. -/
theorem timeHolderOnBall_of_timeDeriv_le {α Λ R S : ℝ} (hα0 : 0 < α) (hα1 : α ≤ 1)
    (hΛ : 0 ≤ Λ)
    {ω : Work.ConstructionInstance.R3 → ℝ → Work.ConstructionInstance.R3}
    (hdiff : ∀ z ∈ Metric.closedBall (0 : Work.ConstructionInstance.R3) R,
      ∀ s ∈ Work.StabilityFar.window S,
        HasDerivAt (fun t => ω z t) (FiniteTimeSingularity.timeDeriv ω z s) s)
    (hbd : ∀ z ∈ Metric.closedBall (0 : Work.ConstructionInstance.R3) R,
      ∀ s ∈ Work.StabilityFar.window S, ‖FiniteTimeSingularity.timeDeriv ω z s‖ ≤ Λ) :
    ∃ H : ℝ, 0 ≤ H ∧ Work.StabilityFar.TimeHolderOnBall α ω R S H := by
  refine ⟨Λ * max (S + 2) 1, mul_nonneg hΛ (le_trans (by norm_num) (le_max_right _ _)), ?_⟩
  intro z hz t ht τ hτ
  have hconv : Convex ℝ (Work.StabilityFar.window S) := by
    rw [Work.StabilityFar.window]; exact convex_Icc _ _
  have hderiv : ∀ x ∈ Work.StabilityFar.window S, DifferentiableAt ℝ (fun t => ω z t) x :=
    fun x hx => (hdiff z hz x hx).differentiableAt
  have hbnd : ∀ x ∈ Work.StabilityFar.window S, ‖deriv (fun t => ω z t) x‖ ≤ Λ := by
    intro x hx
    simpa only [FiniteTimeSingularity.timeDeriv] using hbd z hz x hx
  have hmvt : ‖ω z t - ω z τ‖ ≤ Λ * |t - τ| := by
    have h := Convex.norm_image_sub_le_of_norm_deriv_le hderiv hbnd hconv hτ ht
    simpa only [Real.norm_eq_abs] using h
  have hdt : |t - τ| ≤ S + 2 := by
    rw [abs_sub_le_iff]
    exact ⟨by linarith [ht.2, hτ.1], by linarith [hτ.2, ht.1]⟩
  have hkey := Work.SolutionDelivery.Holder.self_le_max_mul_rpow (d := |t - τ|) (D := S + 2)
    (α := α) (abs_nonneg _) hdt hα0.le hα1
  calc ‖ω z t - ω z τ‖ ≤ Λ * |t - τ| := hmvt
    _ ≤ Λ * (max (S + 2) 1 * |t - τ| ^ α) := mul_le_mul_of_nonneg_left hkey hΛ
    _ = (Λ * max (S + 2) 1) * |t - τ| ^ α := by ring

end Work.ConstructionInstance
end
-- ===== merged: Submission.Work.ConstructionInstance.zsq_pz_pz_profile_abs_le =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.ConstructionInstance

/-- If `H` is odd in its second variable then so is `pz H`: the `z`-derivative is taken
pointwise in `z`, so it commutes with the reflection `θ ↦ -θ` (`deriv.neg`). -/
theorem pz_odd_of_odd {H : ℝ → ℝ → ℝ} (hodd : ∀ z θ : ℝ, H z (-θ) = - H z θ) :
    ∀ z θ : ℝ, Work.Spaces.pz H z (-θ) = - Work.Spaces.pz H z θ := by
  intro z θ
  have h1 : (fun z' : ℝ => H z' (-θ)) = fun z' => -(H z' θ) := by
    funext z'; exact hodd z' θ
  rw [Work.Spaces.pz, h1, Work.Spaces.pz]
  exact deriv.neg

theorem zsq_pz_pz_profile_abs_le {p : ℝ} (hp : p ≠ 0) {g : ℝ → ℝ → ℝ} (hg0 : ∀ z : ℝ, g z 0 = 0) {Cg'' : ℝ}
    (hgdiff2 : ∀ z θ : ℝ, 0 < z → HasDerivAt
      (fun z' : ℝ => Work.Spaces.pz (Work.ConstructionInstance.profile p g) z' θ)
      (Work.Spaces.pz (Work.Spaces.pz (Work.ConstructionInstance.profile p g)) z θ) z)
    (hg3 : ∀ z θ : ℝ, 0 ≤ z → θ ∈ Work.Spaces.Iθ →
      |z ^ 2 * Work.Spaces.pz (Work.Spaces.pz (Work.ConstructionInstance.profile p g)) z θ| ≤ Cg'') :
    ∀ z θ : ℝ, 0 < z → |θ| ≤ Real.pi / 2 →
      |z ^ 2 * Work.Spaces.pz (Work.Spaces.pz (Work.ConstructionInstance.profile p g)) z θ|
        ≤ Cg'' := by
  -- the profile is odd in `θ`
  have hodd : ∀ z θ : ℝ, profile p g z (-θ) = - profile p g z θ := profile_odd hp hg0
  -- hence its two iterated `z`-derivatives are odd in `θ`
  have hodd1 : ∀ z θ : ℝ, Work.Spaces.pz (profile p g) z (-θ) = - Work.Spaces.pz (profile p g) z θ :=
    fun z θ => pz_odd_of_odd hodd z θ
  have hodd2 : ∀ z θ : ℝ,
      Work.Spaces.pz (Work.Spaces.pz (profile p g)) z (-θ)
        = - Work.Spaces.pz (Work.Spaces.pz (profile p g)) z θ :=
    fun z θ => pz_odd_of_odd hodd1 z θ
  intro z θ hz hθ
  have hb := abs_le.mp hθ
  by_cases hθ0 : 0 ≤ θ
  · exact hg3 z θ hz.le ⟨hθ0, hb.2⟩
  · have hθneg : θ < 0 := not_le.mp hθ0
    have hmem : -θ ∈ Work.Spaces.Iθ := ⟨by linarith, by linarith [hb.1]⟩
    have hP : z ^ 2 * Work.Spaces.pz (Work.Spaces.pz (profile p g)) z θ
        = -(z ^ 2 * Work.Spaces.pz (Work.Spaces.pz (profile p g)) z (-θ)) := by
      rw [hodd2 z θ]; ring
    rw [hP, abs_neg]
    exact hg3 z (-θ) hz.le hmem

end Work.ConstructionInstance
end
-- ===== merged: Submission.Work.CoreResiduals.exists_eps_min_lam =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.CoreResiduals

/-- **A local uniform positive lower bound for `λ̄` around any point of `preWindow T`.**

`preWindow T = Set.Ioo (-2) T` is *open*, so a point `t₀` of it has a symmetric neighbourhood
`Icc (t₀ - ε) (t₀ + ε)` still contained in `preWindow T`.  On `preWindow T` the modulation `λ̄` is
differentiable at every point, hence continuous at `t₀`, so `λ̄ s ≥ λ̄ t₀ / 2 > 0` on a small
symmetric neighbourhood of `t₀`.  Taking `ε` to be the smaller of the two radii gives a single
`ε > 0` with `Icc (t₀ - ε) (t₀ + ε) ⊆ preWindow T` and `λ̄ ≥ λ̄ t₀ / 2` throughout.

This is the *pointwise* companion of the global strip bounds `lam_pos_le_on_Icc` and
`exists_pos_le_lam_window`; it is used to localise the positivity of `λ̄` without a compactness
argument.  -/
theorem exists_eps_min_lam {T : ℝ} {lam : ℝ → ℝ}
    (hlam : ∀ t ∈ Work.ConstructionInstance.preWindow T, 0 < lam t)
    (hlamdif : ∀ t ∈ Work.ConstructionInstance.preWindow T, HasDerivAt lam (deriv lam t) t)
    {t₀ : ℝ} (ht₀ : t₀ ∈ Work.ConstructionInstance.preWindow T) :
    ∃ ε : ℝ, 0 < ε ∧ Set.Icc (t₀ - ε) (t₀ + ε) ⊆ Work.ConstructionInstance.preWindow T ∧
      ∃ m : ℝ, 0 < m ∧ ∀ s ∈ Set.Icc (t₀ - ε) (t₀ + ε), m ≤ lam s := by
  have ht1 : -2 < t₀ := ht₀.1
  have ht2 : t₀ < T := ht₀.2
  have hpos : 0 < lam t₀ := hlam t₀ ht₀
  -- continuity of `λ̄` at `t₀` (from differentiability) gives a symmetric `δ`-neighbourhood
  -- on which `|λ̄ s - λ̄ t₀| < λ̄ t₀ / 2`.
  have hcont : ContinuousAt lam t₀ := (hlamdif t₀ ht₀).continuousAt
  rw [Metric.continuousAt_iff] at hcont
  obtain ⟨δ, hδpos, hδ⟩ := hcont (lam t₀ / 2) (by linarith)
  -- `ε` is the smaller of: half the distance to `-2`, half the distance to `T`, and `δ/2`.
  refine ⟨min (min ((t₀ + 2) / 2) ((T - t₀) / 2)) (δ / 2), ?_, ?_, lam t₀ / 2, by linarith, ?_⟩
  · exact lt_min (lt_min (by linarith) (by linarith)) (by linarith)
  · -- `Icc (t₀ - ε) (t₀ + ε) ⊆ Ioo (-2) T`
    intro s hs
    constructor
    · have hle : min (min ((t₀ + 2) / 2) ((T - t₀) / 2)) (δ / 2) ≤ (t₀ + 2) / 2 :=
        le_trans (min_le_left _ _) (min_le_left _ _)
      linarith [hs.1]
    · have hle : min (min ((t₀ + 2) / 2) ((T - t₀) / 2)) (δ / 2) ≤ (T - t₀) / 2 :=
        le_trans (min_le_left _ _) (min_le_right _ _)
      linarith [hs.2]
  · -- `λ̄ ≥ λ̄ t₀ / 2` throughout the interval
    intro s hs
    have hεle : min (min ((t₀ + 2) / 2) ((T - t₀) / 2)) (δ / 2) ≤ δ / 2 := min_le_right _ _
    have habs : |s - t₀| ≤ min (min ((t₀ + 2) / 2) ((T - t₀) / 2)) (δ / 2) := by
      rw [abs_le]; exact ⟨by linarith [hs.1], by linarith [hs.2]⟩
    have hlt : |s - t₀| < δ := by
      have : |s - t₀| ≤ δ / 2 := le_trans habs hεle
      linarith
    have hd := hδ (x := s) (by rw [Real.dist_eq]; exact hlt)
    rw [Real.dist_eq] at hd
    have := (abs_lt.mp hd).1
    linarith

end Work.CoreResiduals
end
-- ===== merged: Submission.Work.FTS.EllipticEst.Blocks.logChiFamily =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.Blocks

open scoped Real Topology
open Set Filter

/-! ## Helper lemmas for the family `logChi`

Everything below is proved with the explicit formula
`logChi n z = Work.ChiExplicit.chi (Real.log z / Real.log ((n:ℝ)+2))`, where
`Work.ChiExplicit.chi t = Real.smoothTransition (2 - |t|)`. -/

/-- The explicit cut-off `Work.ChiExplicit.chi` is continuous (it is `smoothTransition`
composed with `t ↦ 2 - |t|`). -/
theorem chi_continuous_explicit : Continuous Work.ChiExplicit.chi :=
  (Real.smoothTransition.continuous.comp (continuous_const.sub continuous_abs)).congr
    (fun x => (Work.ChiExplicit.chi_apply_abs x).symm)

/-- **The derivative of the explicit cut-off is globally bounded**: `deriv chi` is continuous
(`chi` is `C^∞`), it vanishes strictly outside `[-2,2]` (where `chi` is locally `0`), and on the
compact interval `[-2,2]` it attains a maximum of `|·|`. -/
theorem exists_bound_deriv_chi :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ t : ℝ, |deriv Work.ChiExplicit.chi t| ≤ K := by
  have hcd : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Work.ChiExplicit.chi :=
    Work.ChiExplicit.chi_contDiff ⊤
  have hcont : Continuous (fun t : ℝ => |deriv Work.ChiExplicit.chi t|) :=
    (hcd.continuous_deriv (by simp)).abs
  -- `deriv chi` vanishes strictly outside `[-2,2]`, since `chi` is locally `0` there.
  have hzero_deriv : ∀ t : ℝ, 2 < |t| → deriv Work.ChiExplicit.chi t = 0 := by
    intro t ht
    have hopen : IsOpen {s : ℝ | (2 : ℝ) < |s|} := isOpen_lt continuous_const continuous_abs
    have hev : Work.ChiExplicit.chi =ᶠ[𝓝 t] (fun _ => (0 : ℝ)) := by
      filter_upwards [hopen.mem_nhds ht] with s hs
      exact Work.ChiExplicit.chi_eq_zero hs.le
    rw [hev.deriv_eq, deriv_const]
  -- A point of `[-2,2]` maximizing `|deriv chi|`.
  obtain ⟨x₀, -, hmax⟩ :=
    (isCompact_Icc (a := (-2 : ℝ)) (b := 2)).exists_isMaxOn
      (⟨(-2 : ℝ), by norm_num⟩ : (Set.Icc (-2 : ℝ) 2).Nonempty)
      (f := fun t : ℝ => |deriv Work.ChiExplicit.chi t|) hcont.continuousOn
  have hmax' : ∀ t ∈ Set.Icc (-2 : ℝ) 2,
      |deriv Work.ChiExplicit.chi t| ≤ |deriv Work.ChiExplicit.chi x₀| :=
    isMaxOn_iff.mp hmax
  refine ⟨|deriv Work.ChiExplicit.chi x₀|, abs_nonneg _, ?_⟩
  intro t
  by_cases ht : |t| ≤ 2
  · exact hmax' t (Set.mem_Icc.mpr (abs_le.mp ht))
  · rw [hzero_deriv t (lt_of_not_ge ht)]
    simp

/-- **The chain rule for the logarithmic cut-off**: for `z > 0`,
`(logChi n)'(z) = chi'(log z / log ((n:ℝ)+2)) · 1/(z · log ((n:ℝ)+2))`. -/
theorem deriv_logChi_eq (n : ℕ) {z : ℝ} (hz : 0 < z) :
    deriv (Work.FTS.EllipticEst.TT.logChi n) z =
      deriv Work.ChiExplicit.chi (Real.log z / Real.log ((n : ℝ) + 2)) *
        (1 / (z * Real.log ((n : ℝ) + 2))) := by
  have hc : 0 < Real.log ((n : ℝ) + 2) := Work.FTS.EllipticEst.TT.log_two_add_natCast_pos n
  have hgdiff : DifferentiableAt ℝ (fun w : ℝ => Real.log w / Real.log ((n : ℝ) + 2)) z :=
    (Real.differentiableAt_log (ne_of_gt hz)).div_const _
  have hchidiff : DifferentiableAt ℝ Work.ChiExplicit.chi
      (Real.log z / Real.log ((n : ℝ) + 2)) :=
    ((Work.ChiExplicit.chi_contDiff ⊤).differentiable (by simp)).differentiableAt
  have hderiv_g : deriv (fun w : ℝ => Real.log w / Real.log ((n : ℝ) + 2)) z =
      1 / (z * Real.log ((n : ℝ) + 2)) := by
    rw [deriv_div_const, Real.deriv_log]
    field_simp
  have hcomp : Work.FTS.EllipticEst.TT.logChi n =
      Work.ChiExplicit.chi ∘ (fun w : ℝ => Real.log w / Real.log ((n : ℝ) + 2)) := rfl
  rw [hcomp, deriv_comp z hchidiff hgdiff, hderiv_g]

/-- **The uniform-in-`n` commutator bound**: if `K` bounds `|chi'|` then `|z (logChi n)'(z)| ≤ K/log 2`
for every `n` and every `z > 0` (the factor `1/log ((n:ℝ)+2) ≤ 1/log 2` is what makes the bound
uniform). -/
theorem abs_mul_deriv_logChi_le {K : ℝ} (hK : 0 ≤ K)
    (hK' : ∀ t : ℝ, |deriv Work.ChiExplicit.chi t| ≤ K) (n : ℕ) {z : ℝ} (hz : 0 < z) :
    |z * deriv (Work.FTS.EllipticEst.TT.logChi n) z| ≤ K / Real.log 2 := by
  have hc : 0 < Real.log ((n : ℝ) + 2) := Work.FTS.EllipticEst.TT.log_two_add_natCast_pos n
  have h2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  set t := Real.log z / Real.log ((n : ℝ) + 2) with ht
  have heq : z * (deriv Work.ChiExplicit.chi t * (1 / (z * Real.log ((n : ℝ) + 2)))) =
      deriv Work.ChiExplicit.chi t / Real.log ((n : ℝ) + 2) := by
    field_simp
  rw [deriv_logChi_eq n hz, heq, abs_div, abs_of_pos hc]
  calc |deriv Work.ChiExplicit.chi t| / Real.log ((n : ℝ) + 2)
      ≤ K / Real.log ((n : ℝ) + 2) := div_le_div_of_nonneg_right (hK' t) hc.le
    _ ≤ K / Real.log 2 :=
        div_le_div_of_nonneg_left hK h2 (Work.FTS.EllipticEst.TT.log_two_le_log n)

/-- **Monotonicity in `n`**: `logChi n ≤ logChi (n+1)` pointwise on `(0,∞)`.  The denominator
`log ((n:ℝ)+2)` grows with `n`, so the argument `log z / log ((n:ℝ)+2)` shrinks in absolute value,
and `chi t = smoothTransition (2 - |t|)` increases as `|t|` shrinks. -/
theorem logChi_mono_succ (n : ℕ) (z : ℝ) :
    Work.FTS.EllipticEst.TT.logChi n z ≤ Work.FTS.EllipticEst.TT.logChi (n + 1) z := by
  have hc2 : 0 < Real.log ((n : ℝ) + 2) := Work.FTS.EllipticEst.TT.log_two_add_natCast_pos n
  have hc3 : 0 < Real.log (((n + 1 : ℕ) : ℝ) + 2) :=
    Work.FTS.EllipticEst.TT.log_two_add_natCast_pos (n + 1)
  have hle : Real.log ((n : ℝ) + 2) ≤ Real.log (((n + 1 : ℕ) : ℝ) + 2) := by
    apply Real.log_le_log (lt_trans one_pos (Work.FTS.EllipticEst.TT.one_lt_two_add_natCast n))
    push_cast
    linarith
  have ha : |Real.log z / Real.log (((n + 1 : ℕ) : ℝ) + 2)| ≤
      |Real.log z / Real.log ((n : ℝ) + 2)| := by
    rw [abs_div, abs_div, abs_of_pos hc2, abs_of_pos hc3]
    exact div_le_div_of_nonneg_left (abs_nonneg _) hc2 hle
  rw [Work.FTS.EllipticEst.TT.logChi_apply, Work.FTS.EllipticEst.TT.logChi_apply,
    Work.ChiExplicit.chi_apply_abs, Work.ChiExplicit.chi_apply_abs]
  exact Real.smoothTransition.monotone (sub_le_sub_left ha 2)

/-- **Pointwise convergence to `1`**: for `z > 0` the rescaled logarithm
`log z / log ((n:ℝ)+2)` tends to `0`, and `chi` is continuous at `0` with `chi 0 = 1`. -/
theorem logChi_tendsto_one (z : ℝ) (_hz : 0 < z) :
    Tendsto (fun n : ℕ => Work.FTS.EllipticEst.TT.logChi n z) atTop (nhds 1) := by
  have hden : Tendsto (fun n : ℕ => Real.log ((n : ℝ) + 2)) atTop atTop :=
    Real.tendsto_log_atTop.comp
      (Filter.tendsto_atTop_mono (fun n : ℕ => by
        have h : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
        linarith) tendsto_natCast_atTop_atTop)
  have h0 : Tendsto (fun n : ℕ => Real.log z / Real.log ((n : ℝ) + 2)) atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop hden
  have h1 : Tendsto
      (fun n : ℕ => Work.ChiExplicit.chi (Real.log z / Real.log ((n : ℝ) + 2)))
      atTop (nhds 1) := by
    have h := chi_continuous_explicit.continuousAt.tendsto.comp h0
    rwa [Work.ChiExplicit.chi_zero] at h
  exact h1.congr (fun n => (Work.FTS.EllipticEst.TT.logChi_apply n z).symm)

/-- **The logarithmic cut-off family `logChi` has a uniform `|z χ'|`-bound, is monotone in `n`,
and converges pointwise to `1` on `(0,∞)`.**

`Work.FTS.EllipticEst.TT.logChi n z = Work.ChiExplicit.chi (Real.log z / Real.log ((n:ℝ)+2))`
with `chi t = Real.smoothTransition (2 - |t|)` the explicit smooth bump (`= 1` on `[-1,1]`,
`= 0` off `(-2,2)`, values in `[0,1]`).  Everything else about this family is already proved in
`Submission/Work/FTS/EllipticEst/TT/logCutDefs.lean` (`logChi_mem_Icc`, `logChi_eq_zero_of_le`,
`logChi_eq_zero_of_ge`); this statement adds the four remaining facts needed to run a monotone
convergence argument:

* `C^∞` on `(0,∞)` (composition of the globally `C^∞` `chi` with `z ↦ log z / log((n:ℝ)+2)`,
  which is `C^∞` on `(0,∞)` because `log ((n:ℝ)+2) > 0`);
* a **uniform-in-`n`** commutator bound `|z χ_n'(z)| ≤ K` (`= |χ'(log z/log((n:ℝ)+2))| /
  log((n:ℝ)+2) ≤ K₀/log 2` with `K₀` a bound for `|χ'|`);
* **monotonicity in `n`**: `χ_n ≤ χ_{n+1}` pointwise on `(0,∞)`
  (`log((n:ℝ)+3) ≥ log((n:ℝ)+2)`, so `|log z|/log((n:ℝ)+3) ≤ |log z|/log((n:ℝ)+2)`, and
  `chi` is antitone in `|·|` — `Work.ChiExplicit.chi_antitoneOn : AntitoneOn chi (Ici 0)`);
* **pointwise convergence** `χ_n z → 1` for `z > 0`
  (`log z/log((n:ℝ)+2) → 0`, `chi` continuous at `0` with `chi 0 = 1`). -/
theorem logChiFamily : ∃ K : ℝ, 0 ≤ K ∧
    (∀ n : ℕ,
      ContDiffOn ℝ Work.Stability.smoothOrder (Work.FTS.EllipticEst.TT.logChi n) (Set.Ioi (0 : ℝ))) ∧
    (∀ n : ℕ, ∀ z : ℝ, 0 < z → |z * deriv (Work.FTS.EllipticEst.TT.logChi n) z| ≤ K) ∧
    (∀ n : ℕ, ∀ z : ℝ, 0 < z →
      Work.FTS.EllipticEst.TT.logChi n z ≤ Work.FTS.EllipticEst.TT.logChi (n + 1) z) ∧
    (∀ z : ℝ, 0 < z →
      Filter.Tendsto (fun n : ℕ => Work.FTS.EllipticEst.TT.logChi n z) Filter.atTop (nhds 1)) := by
  obtain ⟨K₀, hK₀0, hK₀⟩ := exists_bound_deriv_chi
  refine ⟨K₀ / Real.log 2, div_nonneg hK₀0 (Real.log_pos (by norm_num)).le, ?_, ?_, ?_, ?_⟩
  · intro n
    exact Work.FTS.EllipticEst.TT.logChi_contDiffOn n
  · intro n z hz
    exact abs_mul_deriv_logChi_le hK₀0 hK₀ n hz
  · intro n z _
    exact logChi_mono_succ n z
  · intro z hz
    exact logChi_tendsto_one z hz

end Work.FTS.EllipticEst.Blocks
end
-- ===== merged: Submission.Work.FTS.EllipticEst.H2W.AeProof.ae.VnRescaledBounds =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The rescaled bounds for the shifted cutoff family `Vn`

`Vn n z = ψ((n+1)z - 2)·χ(z/(n+1))` where `ψ = Real.smoothTransition` is the smooth step and
`χ = Work.Stability.chi` the bump (`0` off `(-2,2)`, `1` on `[-1,1]`).

The lemma proved here is that the rescaled first and second derivatives of `Vn n` are bounded
*uniformly in `n`*:

* `|z ∂_z Vn n z| ≤ 2M`,
* `|z² ∂_z² Vn n z| ≤ 4M²`,

for a single constant `M ≥ 1`.  Although the sup-norm of `∂_z²Vn n` grows like `n²`, the
two-scale structure (`∂_z` hits the `ψ`-part through the variable `u = (n+1)z - 2` and the
`χ`-part through `v = z/(n+1)`) means that only the *products* `u·ψ'(u)`, `u²·ψ''(u)` and
`v·χ'(v)`, `v²·χ''(v)` occur, and each of those is bounded uniformly (the derivatives of `ψ`
are supported in `[0,1]`, those of `χ` in `[-2,2]`).

The proof is the exact analogue of the sibling estimate `PropL2CutKids.Wc_deriv_bdd` for the
*unshifted* family `Wc n z = ψ((n+1)z)·χ(z/(n+1))`; the only difference is the shift `-2` in
the argument of `ψ`, which is why the auxiliary bounds are taken for the shifted functions
`t ↦ t·ψ'(t-2)` and `t ↦ t²·ψ''(t-2)`.
-/

noncomputable section

open scoped Real Topology ContDiff
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.H2W.AeProof.ae

set_option autoImplicit false

/-! ### The auxiliary bounds for the shifted step `ψ(· - 2)` -/



/-! ### Derivatives of an affinely rescaled function -/


/-! ### The two derivative formulas for `Vn` -/



/-! ### The two scaled bounds for `Vn` -/



/-! ### The result -/


end Work.FTS.EllipticEst.H2W.AeProof.ae
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.H2W.HardyPrimEta =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.H2W

open scoped Real Topology Interval
open MeasureTheory Set Filter

set_option autoImplicit false

noncomputable section

/-!
# Weighted Hardy inequality for the primitive, with the angular weight `sEta`

We prove that the primitive `F θ = ∫ t in 0..θ, g t` of a function `g` that is integrable
on `Iθ = [0, π/2]` with `g² sin(2θ)^{-η}` integrable satisfies

  `∫_{Iθ} F(θ)² · sin(2θ)^{-η} dθ ≤ K · ∫_{Iθ} g(θ)² · sin(2θ)^{-η} dθ`

with a universal constant `K`.

The argument is elementary but rather blunt.  Since `sin(2θ) ∈ [0,1]` on `Iθ` the weight
`σ θ = sin(2θ)^{-η}` is `≥ 1` on the interior of `Iθ`, hence `∫_{Iθ} σ θ dθ` is finite
(`Work.FTS.LocData.integral_sin_two_rpow_neg`) and dominates both `∫ g²` and `∫ g²σ`.  For
`θ ∈ Iθ` Cauchy–Schwarz on `[0,θ]` (with the constant test function `1`) gives

  `F(θ)² ≤ (π/2) · ∫_{Iθ} g²`,

so with `M² = (π/2)∫_{Iθ} g²` we get `∫ F²σ ≤ M² ∫ σ`; combining the two bounds produces the
constant `10⁶`.  No sharpness is intended: any constant would do for the applications.
-/

/-- `sEta` is nonnegative on `Iθ`. -/
private lemma sEta_nonneg_prv {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    0 ≤ Work.FTS.EllipticEst.sEta θ :=
  Real.rpow_nonneg
    (Real.sin_nonneg_of_mem_Icc ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩) _

/-- `sEta θ ≥ 1` at interior points of `Iθ`, because `sin(2θ) ∈ (0,1]` there. -/
private lemma one_le_sEta_of_mem_Ioo {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    (1 : ℝ) ≤ Work.FTS.EllipticEst.sEta θ := by
  have hsinpos : 0 < Real.sin (2 * θ) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2])
  have hsinle : Real.sin (2 * θ) ≤ 1 := Real.sin_le_one _
  have h := Real.rpow_le_rpow_of_nonpos hsinpos hsinle
    (show -(Work.Spaces.eta) ≤ 0 by norm_num [Work.Spaces.eta])
  rwa [Real.one_rpow] at h

/-- Almost every point of `Iθ` is an interior point (the two endpoints form a null set). -/
private lemma ae_mem_Ioo :
    ∀ᵐ θ ∂(volume.restrict Work.Spaces.Iθ), θ ∈ Set.Ioo 0 (Real.pi / 2) := by
  have hmeq : volume.restrict (Set.Ioo 0 (Real.pi / 2)) = volume.restrict Work.Spaces.Iθ :=
    Measure.restrict_congr_set Ioo_ae_eq_Icc
  rw [← hmeq]
  exact ae_restrict_mem measurableSet_Ioo

/-- `sEta` is integrable on `Iθ` (the singularity has exponent `η < 1`). -/
private lemma sEta_integrableOn :
    IntegrableOn Work.FTS.EllipticEst.sEta Work.Spaces.Iθ :=
  (Work.FTS.LocData.integral_sin_two_rpow_neg Work.Spaces.eta
    (by norm_num [Work.Spaces.eta]) (by norm_num [Work.Spaces.eta])).1

/-- A crude numerical bound for the integral of the weight. -/
private lemma integral_sEta_le_prv :
    ∫ θ in Work.Spaces.Iθ, Work.FTS.EllipticEst.sEta θ ≤ 10000 := by
  refine le_trans (Work.FTS.LocData.integral_sin_two_rpow_neg Work.Spaces.eta
    (by norm_num [Work.Spaces.eta]) (by norm_num [Work.Spaces.eta])).2 ?_
  norm_num [Work.Spaces.eta]

/-- `sEta` is Borel measurable: it is continuous on the conull interior of `Iθ`. -/
private lemma sEta_aestronglyMeasurable :
    AEStronglyMeasurable Work.FTS.EllipticEst.sEta (volume.restrict Work.Spaces.Iθ) := by
  have hsin_cont : ContinuousOn (fun θ : ℝ => Real.sin (2 * θ)) (Set.Ioo 0 (Real.pi / 2)) :=
    (by fun_prop : Continuous fun θ : ℝ => Real.sin (2 * θ)).continuousOn
  have hne : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2), Real.sin (2 * θ) ≠ 0 := by
    intro θ hθ
    exact ne_of_gt (Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2]))
  have hcont : ContinuousOn (fun θ : ℝ => Real.sin (2 * θ) ^ (-(Work.Spaces.eta)))
      (Set.Ioo 0 (Real.pi / 2)) :=
    hsin_cont.rpow_const (fun θ hθ => Or.inl (hne θ hθ))
  have h1 : AEStronglyMeasurable (fun θ : ℝ => Real.sin (2 * θ) ^ (-(Work.Spaces.eta)))
      (volume.restrict (Set.Ioo 0 (Real.pi / 2))) :=
    hcont.aestronglyMeasurable measurableSet_Ioo
  have hmeq : volume.restrict (Set.Ioo 0 (Real.pi / 2)) = volume.restrict Work.Spaces.Iθ :=
    Measure.restrict_congr_set Ioo_ae_eq_Icc
  rw [← hmeq]
  exact h1

/-- **Cauchy–Schwarz for the primitive.**  If `g` and `g²` are integrable on `Iθ` then the
primitive of `g` satisfies `(∫ t in 0..θ, g t)² ≤ (π/2) · ∫_{Iθ} g²` for every `θ ∈ Iθ`. -/
private theorem prim_sq_le {g : ℝ → ℝ} (hg : IntegrableOn g Work.Spaces.Iθ)
    (hg2 : IntegrableOn (fun θ => g θ ^ 2) Work.Spaces.Iθ) (θ : ℝ) (hθ : θ ∈ Work.Spaces.Iθ) :
    (∫ t in (0 : ℝ)..θ, g t) ^ 2 ≤ (Real.pi / 2) * ∫ x in Work.Spaces.Iθ, g x ^ 2 := by
  have hθ0 : (0 : ℝ) ≤ θ := hθ.1
  have hsub : Set.Icc (0 : ℝ) θ ⊆ Work.Spaces.Iθ := Set.Icc_subset_Icc_right hθ.2
  have hgI : IntegrableOn g (Set.Icc (0 : ℝ) θ) := hg.mono_set hsub
  have hg2I : IntegrableOn (fun t => g t ^ 2) (Set.Icc (0 : ℝ) θ) := hg2.mono_set hsub
  have hu : MemLp g 2 (volume.restrict (Set.Icc (0 : ℝ) θ)) :=
    (memLp_two_iff_integrable_sq hgI.aestronglyMeasurable).2 hg2I
  have hv : MemLp (fun _ : ℝ => (1 : ℝ)) 2 (volume.restrict (Set.Icc (0 : ℝ) θ)) :=
    memLp_const 1
  have hcs := Work.Spaces.cs_integral hu hv
  simp only [mul_one, one_pow] at hcs
  have hlen : (∫ x in Set.Icc (0 : ℝ) θ, (1 : ℝ)) = θ := by
    rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hθ0,
      intervalIntegral.integral_const]
    simp
  rw [hlen] at hcs
  have hgval : (∫ t in (0 : ℝ)..θ, g t) = ∫ t in Set.Icc (0 : ℝ) θ, g t := by
    rw [intervalIntegral.integral_of_le hθ0, ← integral_Icc_eq_integral_Ioc]
  rw [hgval]
  have hmono : (∫ x in Set.Icc (0 : ℝ) θ, g x ^ 2) ≤ ∫ x in Work.Spaces.Iθ, g x ^ 2 :=
    setIntegral_mono_set hg2 (Eventually.of_forall fun x => sq_nonneg _)
      (Eventually.of_forall fun x hx => hsub hx)
  have hgnn : 0 ≤ ∫ x in Work.Spaces.Iθ, g x ^ 2 :=
    integral_nonneg (fun x => sq_nonneg _)
  calc (∫ x in Set.Icc (0 : ℝ) θ, g x) ^ 2
      ≤ (∫ x in Set.Icc (0 : ℝ) θ, g x ^ 2) * θ := hcs
    _ ≤ (∫ x in Work.Spaces.Iθ, g x ^ 2) * (Real.pi / 2) := mul_le_mul hmono hθ.2 hθ0 hgnn
    _ = (Real.pi / 2) * ∫ x in Work.Spaces.Iθ, g x ^ 2 := by ring

theorem HardyPrimEta :
    ∃ K : ℝ, 0 < K ∧ ∀ g : ℝ → ℝ,
      MeasureTheory.IntegrableOn g Work.Spaces.Iθ →
      MeasureTheory.IntegrableOn (fun θ => (g θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
        Work.Spaces.Iθ →
      (∀ θ ∈ Set.Ioo 0 (Real.pi / 2), ContinuousAt g θ) →
      MeasureTheory.IntegrableOn
          (fun θ => (∫ t in (0 : ℝ)..θ, g t) ^ 2 * Work.FTS.EllipticEst.sEta θ)
          Work.Spaces.Iθ ∧
        (∫ θ in Work.Spaces.Iθ,
            (∫ t in (0 : ℝ)..θ, g t) ^ 2 * Work.FTS.EllipticEst.sEta θ)
          ≤ K * ∫ θ in Work.Spaces.Iθ,
              (g θ) ^ 2 * Work.FTS.EllipticEst.sEta θ := by
  refine ⟨(10 : ℝ) ^ 6, by norm_num, fun g hg hgs _hcont => ?_⟩
  clear _hcont
  -- `sEta ≥ 1` almost everywhere on `Iθ`.
  have hone : ∀ᵐ θ ∂(volume.restrict Work.Spaces.Iθ),
      (1 : ℝ) ≤ Work.FTS.EllipticEst.sEta θ := by
    filter_upwards [ae_mem_Ioo] with θ hθ
    exact one_le_sEta_of_mem_Ioo hθ
  have haeI : ∀ᵐ θ ∂(volume.restrict Work.Spaces.Iθ), θ ∈ Work.Spaces.Iθ :=
    ae_restrict_mem measurableSet_Icc
  -- Step 1: `g²` is integrable on `Iθ`, because `g² ≤ g² · sEta` a.e.
  have hg2 : IntegrableOn (fun θ => g θ ^ 2) Work.Spaces.Iθ := by
    refine hgs.mono' ?_ ?_
    · exact (hg.aestronglyMeasurable.mul hg.aestronglyMeasurable).congr
        (Eventually.of_forall fun θ => by simp [Pi.mul_apply, sq])
    · filter_upwards [hone] with θ hθ
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      calc g θ ^ 2 = g θ ^ 2 * 1 := by ring
        _ ≤ g θ ^ 2 * Work.FTS.EllipticEst.sEta θ :=
            mul_le_mul_of_nonneg_left hθ (sq_nonneg _)
  -- Step 2: the Cauchy–Schwarz bound for the primitive.
  set M2 : ℝ := (Real.pi / 2) * ∫ x in Work.Spaces.Iθ, g x ^ 2 with hM2def
  have hM2nn : 0 ≤ M2 := by
    rw [hM2def]
    exact mul_nonneg (by positivity) (integral_nonneg fun x => sq_nonneg _)
  have hpoint : ∀ θ ∈ Work.Spaces.Iθ, (∫ t in (0 : ℝ)..θ, g t) ^ 2 ≤ M2 := by
    intro θ hθ
    rw [hM2def]
    exact prim_sq_le hg hg2 θ hθ
  -- Step 3: measurability of the integrand.
  have hFcont : ContinuousOn (fun x : ℝ => ∫ t in (0 : ℝ)..x, g t) Work.Spaces.Iθ := by
    have h2 : IntegrableOn g (Set.uIcc (0 : ℝ) (Real.pi / 2)) := by
      rw [Set.uIcc_of_le (by linarith [Real.pi_pos])]
      exact hg
    have h := intervalIntegral.continuousOn_primitive_interval (a := (0 : ℝ))
      (b := Real.pi / 2) h2
    rwa [Set.uIcc_of_le (by linarith [Real.pi_pos])] at h
  have hFsq : AEStronglyMeasurable (fun θ => (∫ t in (0 : ℝ)..θ, g t) ^ 2)
      (volume.restrict Work.Spaces.Iθ) :=
    ((hFcont.aestronglyMeasurable measurableSet_Icc).mul
      (hFcont.aestronglyMeasurable measurableSet_Icc)).congr
      (Eventually.of_forall fun θ => by simp [Pi.mul_apply, sq])
  have hprod_aesm : AEStronglyMeasurable
      (fun θ => (∫ t in (0 : ℝ)..θ, g t) ^ 2 * Work.FTS.EllipticEst.sEta θ)
      (volume.restrict Work.Spaces.Iθ) :=
    (hFsq.mul sEta_aestronglyMeasurable).congr
      (Eventually.of_forall fun θ => by simp [Pi.mul_apply])
  -- Step 4: the two a.e. pointwise statements used for the integrals.
  have hbd : (fun θ => (∫ t in (0 : ℝ)..θ, g t) ^ 2 * Work.FTS.EllipticEst.sEta θ)
      ≤ᵐ[volume.restrict Work.Spaces.Iθ] fun θ => M2 * Work.FTS.EllipticEst.sEta θ := by
    filter_upwards [haeI] with θ hθ
    exact mul_le_mul_of_nonneg_right (hpoint θ hθ) (sEta_nonneg_prv hθ)
  have hnonneg : 0 ≤ᵐ[volume.restrict Work.Spaces.Iθ]
      (fun θ => (∫ t in (0 : ℝ)..θ, g t) ^ 2 * Work.FTS.EllipticEst.sEta θ) := by
    filter_upwards [haeI] with θ hθ
    exact mul_nonneg (sq_nonneg _) (sEta_nonneg_prv hθ)
  -- Step 5: integrability of the LHS integrand.
  have hM2σ : Integrable (fun θ => M2 * Work.FTS.EllipticEst.sEta θ)
      (volume.restrict Work.Spaces.Iθ) := sEta_integrableOn.const_mul M2
  have hintF : Integrable
      (fun θ => (∫ t in (0 : ℝ)..θ, g t) ^ 2 * Work.FTS.EllipticEst.sEta θ)
      (volume.restrict Work.Spaces.Iθ) := by
    refine hM2σ.mono' hprod_aesm ?_
    filter_upwards [haeI] with θ hθ
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sq_nonneg _) (sEta_nonneg_prv hθ))]
    exact mul_le_mul_of_nonneg_right (hpoint θ hθ) (sEta_nonneg_prv hθ)
  refine ⟨hintF, ?_⟩
  -- Step 6: the numerical estimates.
  have hgnnle : (∫ x in Work.Spaces.Iθ, g x ^ 2)
      ≤ ∫ x in Work.Spaces.Iθ, g x ^ 2 * Work.FTS.EllipticEst.sEta x := by
    refine integral_mono_ae hg2 hgs ?_
    filter_upwards [hone] with θ hθ
    calc g θ ^ 2 = g θ ^ 2 * 1 := by ring
      _ ≤ g θ ^ 2 * Work.FTS.EllipticEst.sEta θ := mul_le_mul_of_nonneg_left hθ (sq_nonneg _)
  have hA0 : 0 ≤ ∫ x in Work.Spaces.Iθ, g x ^ 2 * Work.FTS.EllipticEst.sEta x :=
    integral_nonneg_of_ae (by
      filter_upwards [haeI] with θ hθ
      exact mul_nonneg (sq_nonneg _) (sEta_nonneg_prv hθ))
  have hσ0 : 0 ≤ ∫ x in Work.Spaces.Iθ, Work.FTS.EllipticEst.sEta x :=
    integral_nonneg_of_ae (by
      filter_upwards [haeI] with θ hθ
      exact sEta_nonneg_prv hθ)
  have hstep : (∫ θ in Work.Spaces.Iθ,
        (∫ t in (0 : ℝ)..θ, g t) ^ 2 * Work.FTS.EllipticEst.sEta θ)
      ≤ M2 * ∫ x in Work.Spaces.Iθ, Work.FTS.EllipticEst.sEta x := by
    have h := integral_mono_of_nonneg hnonneg hM2σ hbd
    rwa [integral_const_mul] at h
  calc (∫ θ in Work.Spaces.Iθ,
        (∫ t in (0 : ℝ)..θ, g t) ^ 2 * Work.FTS.EllipticEst.sEta θ)
      ≤ M2 * ∫ x in Work.Spaces.Iθ, Work.FTS.EllipticEst.sEta x := hstep
    _ = ((Real.pi / 2) * (∫ x in Work.Spaces.Iθ, g x ^ 2))
          * (∫ x in Work.Spaces.Iθ, Work.FTS.EllipticEst.sEta x) := by rw [hM2def]
    _ ≤ ((Real.pi / 2) * (∫ x in Work.Spaces.Iθ, g x ^ 2 * Work.FTS.EllipticEst.sEta x))
          * 10000 := by
        refine mul_le_mul ?_ integral_sEta_le_prv hσ0 ?_
        · exact mul_le_mul_of_nonneg_left hgnnle (by positivity)
        · exact mul_nonneg (by positivity) hA0
    _ ≤ (10 : ℝ) ^ 6
          * (∫ x in Work.Spaces.Iθ, g x ^ 2 * Work.FTS.EllipticEst.sEta x) := by
        rw [show (Real.pi / 2)
              * (∫ x in Work.Spaces.Iθ, g x ^ 2 * Work.FTS.EllipticEst.sEta x) * 10000
            = ((Real.pi / 2) * 10000)
              * (∫ x in Work.Spaces.Iθ, g x ^ 2 * Work.FTS.EllipticEst.sEta x) from by ring]
        refine mul_le_mul_of_nonneg_right ?_ hA0
        nlinarith [Real.pi_lt_four]

end

end Work.FTS.EllipticEst.H2W
end
-- ===== merged: Submission.Work.FTS.EllipticEst.HkNorm_add_le =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst

set_option autoImplicit false
set_option maxHeartbeats 800000

/-! ## The open quadrant and the smoothness order -/

/-- The open quadrant `(0,∞) × (0,π/2)` on which the smoothness hypothesis of
`HkNorm_add_le` is imposed. -/
private abbrev quadV : Set (ℝ × ℝ) := Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)

private theorem isOpen_quadV : IsOpen quadV := isOpen_Ioi.prod isOpen_Ioo

private theorem smoothOrder_ne_zero : Work.Stability.smoothOrder ≠ 0 := by
  simp [Work.Stability.smoothOrder]

/-- `C^n` for every natural number `n` is the genuine smooth order `∞`. -/
private theorem contDiffOn_smoothOrder_of_forall_nat {f : ℝ × ℝ → ℝ} {s : Set (ℝ × ℝ)}
    (h : ∀ n : ℕ, ContDiffOn ℝ n f s) : ContDiffOn ℝ Work.Stability.smoothOrder f s := by
  intro x hx m _
  exact h m x hx m le_rfl

/-- Slices of a function smooth on the open quadrant are differentiable in `z`. -/
private theorem slice_diffAt_fst {h : ℝ → ℝ → ℝ}
    (hh : ContDiffOn ℝ Work.Stability.smoothOrder (Function.uncurry h) quadV)
    {z θ : ℝ} (hz : z ∈ Set.Ioi 0) (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    DifferentiableAt ℝ (fun z' => h z' θ) z :=
  ((Work.FTS.LocData.contDiffOn_slice_z (s := Set.Ioi 0) (t := Set.Ioo 0 (π / 2))
      hh hθ).differentiableOn smoothOrder_ne_zero).differentiableAt (isOpen_Ioi.mem_nhds hz)

/-- Slices of a function smooth on the open quadrant are differentiable in `θ`. -/
private theorem slice_diffAt_snd {h : ℝ → ℝ → ℝ}
    (hh : ContDiffOn ℝ Work.Stability.smoothOrder (Function.uncurry h) quadV)
    {z θ : ℝ} (hz : z ∈ Set.Ioi 0) (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    DifferentiableAt ℝ (fun θ' => h z θ') θ :=
  ((Work.FTS.LocData.contDiffOn_slice_θ (s := Set.Ioi 0) (t := Set.Ioo 0 (π / 2))
      hh hz).differentiableOn smoothOrder_ne_zero).differentiableAt (isOpen_Ioo.mem_nhds hθ)

/-! ## Additivity of the iterated operators on the open quadrant -/

/-- Two functions agreeing on the open quadrant have the same `D_z`-iterates there. -/
private theorem DzIter_congr_of_quad {F G : ℝ → ℝ → ℝ}
    (h : Set.EqOn (Function.uncurry F) (Function.uncurry G) quadV) (j : ℕ) :
    Set.EqOn (Function.uncurry (Work.Spaces.DzIter j F))
      (Function.uncurry (Work.Spaces.DzIter j G)) quadV := by
  induction j with
  | zero => exact h
  | succ n ih =>
      rintro ⟨z, θ⟩ ⟨hz, hθ⟩
      show z * deriv (fun z' => Work.Spaces.DzIter n F z' θ) z
          = z * deriv (fun z' => Work.Spaces.DzIter n G z' θ) z
      congr 1
      refine Filter.EventuallyEq.deriv_eq ?_
      filter_upwards [isOpen_Ioi.mem_nhds hz] with z' hz'
      exact ih (show (z', θ) ∈ quadV from ⟨hz', hθ⟩)

/-- The iterated operators `D_z^j` are additive on the open quadrant. -/
private theorem DzIter_add_of_contDiffOn {f g : ℝ → ℝ → ℝ}
    (hf : ContDiffOn ℝ Work.Stability.smoothOrder (Function.uncurry f) quadV)
    (hg : ContDiffOn ℝ Work.Stability.smoothOrder (Function.uncurry g) quadV) (j : ℕ) :
    Set.EqOn (Function.uncurry (Work.Spaces.DzIter j (fun z θ => f z θ + g z θ)))
      (Function.uncurry (fun z θ => Work.Spaces.DzIter j f z θ
        + Work.Spaces.DzIter j g z θ)) quadV := by
  induction j with
  | zero => rintro ⟨z, θ⟩ -; rfl
  | succ n ih =>
      rintro ⟨z, θ⟩ ⟨hz, hθ⟩
      have heq : (fun z' => Work.Spaces.DzIter n (fun z θ => f z θ + g z θ) z' θ) =ᶠ[𝓝 z]
          (fun z' => Work.Spaces.DzIter n f z' θ + Work.Spaces.DzIter n g z' θ) := by
        filter_upwards [isOpen_Ioi.mem_nhds hz] with z' hz'
        exact ih (show (z', θ) ∈ quadV from ⟨hz', hθ⟩)
      have h1 : DifferentiableAt ℝ (fun z' => Work.Spaces.DzIter n f z' θ) z :=
        slice_diffAt_fst (Work.FTS.LocData.contDiffOn_DzIter isOpen_quadV hf n) hz hθ
      have h2 : DifferentiableAt ℝ (fun z' => Work.Spaces.DzIter n g z' θ) z :=
        slice_diffAt_fst (Work.FTS.LocData.contDiffOn_DzIter isOpen_quadV hg n) hz hθ
      have hd : deriv (fun z' => Work.Spaces.DzIter n f z' θ + Work.Spaces.DzIter n g z' θ) z
          = deriv (fun z' => Work.Spaces.DzIter n f z' θ) z
            + deriv (fun z' => Work.Spaces.DzIter n g z' θ) z := deriv_add h1 h2
      show z * deriv (fun z' => Work.Spaces.DzIter n (fun z θ => f z θ + g z θ) z' θ) z
          = z * deriv (fun z' => Work.Spaces.DzIter n f z' θ) z
            + z * deriv (fun z' => Work.Spaces.DzIter n g z' θ) z
      rw [heq.deriv_eq, hd]
      ring

/-- The iterated operators `D_θ^i` are additive on the open quadrant. -/
private theorem DthIter_add_of_contDiffOn {f g : ℝ → ℝ → ℝ}
    (hf : ContDiffOn ℝ Work.Stability.smoothOrder (Function.uncurry f) quadV)
    (hg : ContDiffOn ℝ Work.Stability.smoothOrder (Function.uncurry g) quadV) (i : ℕ) :
    Set.EqOn (Function.uncurry (Work.Spaces.DthIter i (fun z θ => f z θ + g z θ)))
      (Function.uncurry (fun z θ => Work.Spaces.DthIter i f z θ
        + Work.Spaces.DthIter i g z θ)) quadV := by
  induction i with
  | zero => rintro ⟨z, θ⟩ -; rfl
  | succ n ih =>
      rintro ⟨z, θ⟩ ⟨hz, hθ⟩
      have heq : (fun θ' => Work.Spaces.DthIter n (fun z θ => f z θ + g z θ) z θ') =ᶠ[𝓝 θ]
          (fun θ' => Work.Spaces.DthIter n f z θ' + Work.Spaces.DthIter n g z θ') := by
        filter_upwards [isOpen_Ioo.mem_nhds hθ] with θ' hθ'
        exact ih (show (z, θ') ∈ quadV from ⟨hz, hθ'⟩)
      have h1 : DifferentiableAt ℝ (fun θ' => Work.Spaces.DthIter n f z θ') θ :=
        slice_diffAt_snd (Work.FTS.LocData.contDiffOn_DthIter isOpen_quadV hf n) hz hθ
      have h2 : DifferentiableAt ℝ (fun θ' => Work.Spaces.DthIter n g z θ') θ :=
        slice_diffAt_snd (Work.FTS.LocData.contDiffOn_DthIter isOpen_quadV hg n) hz hθ
      have hd : deriv (fun θ' => Work.Spaces.DthIter n f z θ' + Work.Spaces.DthIter n g z θ') θ
          = deriv (fun θ' => Work.Spaces.DthIter n f z θ') θ
            + deriv (fun θ' => Work.Spaces.DthIter n g z θ') θ := deriv_add h1 h2
      show Real.sin (2 * θ)
            * deriv (fun θ' => Work.Spaces.DthIter n (fun z θ => f z θ + g z θ) z θ') θ
          = Real.sin (2 * θ) * deriv (fun θ' => Work.Spaces.DthIter n f z θ') θ
            + Real.sin (2 * θ) * deriv (fun θ' => Work.Spaces.DthIter n g z θ') θ
      rw [heq.deriv_eq, hd]
      ring

/-- The mixed operators `D_z^j D_θ^i` are additive on the open quadrant. -/
private theorem mixed_add_of_contDiffOn {f g : ℝ → ℝ → ℝ}
    (hf : ContDiffOn ℝ Work.Stability.smoothOrder (Function.uncurry f) quadV)
    (hg : ContDiffOn ℝ Work.Stability.smoothOrder (Function.uncurry g) quadV) (j i : ℕ) :
    Set.EqOn (Function.uncurry (Work.Spaces.mixed j i (fun z θ => f z θ + g z θ)))
      (Function.uncurry (fun z θ => Work.Spaces.mixed j i f z θ
        + Work.Spaces.mixed j i g z θ)) quadV := by
  have hDth := DthIter_add_of_contDiffOn hf hg i
  have hcongr := DzIter_congr_of_quad hDth j
  have hadd := DzIter_add_of_contDiffOn
    (Work.FTS.LocData.contDiffOn_DthIter isOpen_quadV hf i)
    (Work.FTS.LocData.contDiffOn_DthIter isOpen_quadV hg i) j
  rintro ⟨z, θ⟩ hzθ
  exact (hcongr hzθ).trans (hadd hzθ)

/-! ## Vanishing of the integrand on the two boundary lines -/

/-- At `sin(2θ) = 0` every `D_θ`-iterate of positive order vanishes at that same `θ` (the
outermost `D_θ` carries the factor `sin(2θ)`). -/
private theorem DthIter_succ_eq_zero_of_sin (f : ℝ → ℝ → ℝ) {θ : ℝ} (hs : Real.sin (2 * θ) = 0)
    (m : ℕ) (z : ℝ) : Work.Spaces.DthIter (m + 1) f z θ = 0 := by
  simp only [Work.Spaces.DthIter_succ, Work.Spaces.Dth, Work.Spaces.pth, hs, zero_mul]

/-- A function whose `θ`-slice vanishes identically has vanishing `D_z`-iterates there. -/
private theorem DzIter_eq_zero_of_slice (f : ℝ → ℝ → ℝ) {θ : ℝ} (h : ∀ z, f z θ = 0) :
    ∀ (j : ℕ) (z : ℝ), Work.Spaces.DzIter j f z θ = 0 := by
  intro j
  induction j with
  | zero => intro z; exact h z
  | succ n ih =>
      intro z
      have hslice : (fun z' => Work.Spaces.DzIter n f z' θ) = fun _ => (0 : ℝ) := funext ih
      simp only [Work.Spaces.DzIter_succ, Work.Spaces.Dz, Work.Spaces.pz]
      rw [hslice]
      simp

/-- At `sin(2θ) = 0` every mixed derivative `D_z^j D_θ^i` with `i ≥ 1` vanishes at `(z,θ)`. -/
private theorem mixed_eq_zero_of_sin (f : ℝ → ℝ → ℝ) {θ : ℝ} (hs : Real.sin (2 * θ) = 0)
    {j i : ℕ} (hi : 1 ≤ i) (z : ℝ) : Work.Spaces.mixed j i f z θ = 0 := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : i ≠ 0)
  simp only [Work.Spaces.mixed]
  exact DzIter_eq_zero_of_slice (Work.Spaces.DthIter (m + 1) f) (θ := θ)
    (fun z' => DthIter_succ_eq_zero_of_sin f hs m z') j z

/-- On the angular boundary `sin(2θ) = 0` the `ℋ^k`-integrand vanishes: the first sum is killed
by the `1/sin(2θ)^{η/2}` factor and the second by the `D_θ`-factors of all its summands. -/
private theorem HkIntegrand_eq_zero_of_sin (α : ℝ) (k : ℕ) (f : ℝ → ℝ → ℝ) {z θ : ℝ}
    (hs : Real.sin (2 * θ) = 0) : Work.Spaces.HkIntegrand α k f z θ = 0 := by
  rw [Work.Spaces.HkIntegrand]
  have hsin : (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2) = 0 := by
    rw [hs, Real.zero_rpow (by norm_num [Work.Spaces.eta])]
  have h1 : (∑ i ∈ Finset.range (k + 1),
      (Work.Spaces.DzIter i f z θ
        * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2) = 0 := by
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [hsin, div_zero, mul_zero, zero_pow (by norm_num)]
  have h2 : (∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
      (if 1 ≤ i ∧ i + j ≤ k
        then (Work.Spaces.mixed j i f z θ * Work.Spaces.Wt α z θ) ^ 2 else 0)) = 0 := by
    refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ => ?_
    split_ifs with hc
    · rw [mixed_eq_zero_of_sin f hs hc.1 z, zero_mul, zero_pow (by norm_num)]
    · rfl
  rw [h1, h2, add_zero]

/-- On the radial boundary `z = 0` the `ℋ^k`-integrand vanishes, because the weight
`w 0 = (1+0)²/0² = 0` kills both sums. -/
private theorem HkIntegrand_eq_zero_of_z_eq_zero (α : ℝ) (k : ℕ) (f : ℝ → ℝ → ℝ) (θ : ℝ) :
    Work.Spaces.HkIntegrand α k f 0 θ = 0 := by
  rw [Work.Spaces.HkIntegrand]
  simp [Work.Spaces.w, Work.Spaces.Wt, Work.Spaces.wTheta]

/-! ## The algebraic core: sums of squares of sums -/

private theorem sum_sq_add_le {ι : Type*} (s : Finset ι) (x y : ι → ℝ) :
    (∑ i ∈ s, (x i + y i) ^ 2) ≤ 2 * (∑ i ∈ s, x i ^ 2) + 2 * (∑ i ∈ s, y i ^ 2) := by
  calc (∑ i ∈ s, (x i + y i) ^ 2)
      ≤ ∑ i ∈ s, (2 * x i ^ 2 + 2 * y i ^ 2) :=
        Finset.sum_le_sum fun i _ => by
          have h := add_sq_le (a := x i) (b := y i); linarith
    _ = 2 * (∑ i ∈ s, x i ^ 2) + 2 * (∑ i ∈ s, y i ^ 2) := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]

/-- The pointwise inequality for the integrand, given the additivity of the iterated operators
at `(z,θ)`. -/
private theorem HkIntegrand_add_le_pt (α : ℝ) (k : ℕ) (f g : ℝ → ℝ → ℝ) (z θ : ℝ)
    (hz : ∀ i, Work.Spaces.DzIter i (fun z θ => f z θ + g z θ) z θ
      = Work.Spaces.DzIter i f z θ + Work.Spaces.DzIter i g z θ)
    (hm : ∀ i j, Work.Spaces.mixed j i (fun z θ => f z θ + g z θ) z θ
      = Work.Spaces.mixed j i f z θ + Work.Spaces.mixed j i g z θ) :
    Work.Spaces.HkIntegrand α k (fun z θ => f z θ + g z θ) z θ
      ≤ 2 * Work.Spaces.HkIntegrand α k f z θ
        + 2 * Work.Spaces.HkIntegrand α k g z θ := by
  have hZ : (∑ i ∈ Finset.range (k + 1),
        (Work.Spaces.DzIter i (fun z θ => f z θ + g z θ) z θ
          * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
      ≤ 2 * (∑ i ∈ Finset.range (k + 1),
            (Work.Spaces.DzIter i f z θ
              * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
          + 2 * (∑ i ∈ Finset.range (k + 1),
            (Work.Spaces.DzIter i g z θ
              * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2) := by
    have h1 : (∑ i ∈ Finset.range (k + 1),
          (Work.Spaces.DzIter i (fun z θ => f z θ + g z θ) z θ
            * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
        = ∑ i ∈ Finset.range (k + 1),
          ((Work.Spaces.DzIter i f z θ
              * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)))
            + (Work.Spaces.DzIter i g z θ
              * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)))) ^ 2 := by
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hz i]; ring
    rw [h1]
    exact sum_sq_add_le _ _ _
  have hM : (∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
        (if 1 ≤ i ∧ i + j ≤ k
          then (Work.Spaces.mixed j i (fun z θ => f z θ + g z θ) z θ
            * Work.Spaces.Wt α z θ) ^ 2 else 0))
      ≤ 2 * (∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
            (if 1 ≤ i ∧ i + j ≤ k
              then (Work.Spaces.mixed j i f z θ * Work.Spaces.Wt α z θ) ^ 2 else 0))
          + 2 * (∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
            (if 1 ≤ i ∧ i + j ≤ k
              then (Work.Spaces.mixed j i g z θ * Work.Spaces.Wt α z θ) ^ 2 else 0)) := by
    set S : Finset (ℕ × ℕ) := ((Finset.range (k + 1)) ×ˢ (Finset.range (k + 1))).filter
      (fun p => 1 ≤ p.1 ∧ p.1 + p.2 ≤ k) with hS
    have e : ∀ u : ℝ → ℝ → ℝ,
        (∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
          (if 1 ≤ i ∧ i + j ≤ k
            then (Work.Spaces.mixed j i u z θ * Work.Spaces.Wt α z θ) ^ 2 else 0))
          = ∑ p ∈ S, (Work.Spaces.mixed p.2 p.1 u z θ * Work.Spaces.Wt α z θ) ^ 2 := by
      intro u
      rw [hS, Finset.sum_filter, Finset.sum_product]
    rw [e f, e g, e (fun z θ => f z θ + g z θ)]
    have hconv : (∑ p ∈ S,
          (Work.Spaces.mixed p.2 p.1 (fun z θ => f z θ + g z θ) z θ
            * Work.Spaces.Wt α z θ) ^ 2)
        = ∑ p ∈ S, ((Work.Spaces.mixed p.2 p.1 f z θ * Work.Spaces.Wt α z θ)
            + (Work.Spaces.mixed p.2 p.1 g z θ * Work.Spaces.Wt α z θ)) ^ 2 := by
      refine Finset.sum_congr rfl fun p _ => ?_
      rw [hm p.1 p.2]; ring
    rw [hconv]
    exact sum_sq_add_le _ _ _
  simp only [Work.Spaces.HkIntegrand]
  linarith [hZ, hM]

/-! ## The pointwise inequality on the closed quadrant -/

/-- **The pointwise inequality for the `ℋ^k`-integrand** on the whole closed quadrant: for
`(z,θ) ∈ [0,∞) × [0,π/2]`,

`HkIntegrand (f+g) ≤ 2·HkIntegrand f + 2·HkIntegrand g`.

On the interior this is additivity of the operators plus `(a+b)² ≤ 2a² + 2b²`; on the two
boundary lines both sides vanish, the left-hand side by the vanishing lemmas above and the
right-hand side because each summand does. -/
theorem HkIntegrand_add_le_of_contDiffOn (α : ℝ) (k : ℕ) {f g : ℝ → ℝ → ℝ}
    (hf : ContDiffOn ℝ Work.Stability.smoothOrder (Function.uncurry f) quadV)
    (hg : ContDiffOn ℝ Work.Stability.smoothOrder (Function.uncurry g) quadV) :
    ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
      Work.Spaces.HkIntegrand α k (fun z θ => f z θ + g z θ) z θ
        ≤ 2 * Work.Spaces.HkIntegrand α k f z θ
          + 2 * Work.Spaces.HkIntegrand α k g z θ := by
  intro z hz θ hθ
  by_cases hz0 : z = 0
  · rw [hz0, HkIntegrand_eq_zero_of_z_eq_zero]
    have h1 := Work.Spaces.HkIntegrand_nonneg α k f 0 θ
    have h2 := Work.Spaces.HkIntegrand_nonneg α k g 0 θ
    linarith
  by_cases hs : Real.sin (2 * θ) = 0
  · rw [HkIntegrand_eq_zero_of_sin α k (fun z θ => f z θ + g z θ) hs]
    have h1 := Work.Spaces.HkIntegrand_nonneg α k f z θ
    have h2 := Work.Spaces.HkIntegrand_nonneg α k g z θ
    linarith
  · have hzge : 0 ≤ z := by simpa only [Work.Spaces.Iz, Set.mem_Ici] using hz
    have hzpos : 0 < z := lt_of_le_of_ne hzge (Ne.symm hz0)
    have hbnd : 0 ≤ θ ∧ θ ≤ π / 2 := by
      simpa only [Work.Spaces.Iθ, Set.mem_Icc] using hθ
    have hθ1 : 0 < θ := by
      rcases eq_or_lt_of_le hbnd.1 with h' | h'
      · exact absurd (by rw [← h']; simp) hs
      · exact h'
    have hθ2 : θ < π / 2 := by
      rcases lt_or_eq_of_le hbnd.2 with h' | h'
      · exact h'
      · exact absurd (by rw [h', show (2 : ℝ) * (π / 2) = π from by ring, Real.sin_pi]) hs
    exact HkIntegrand_add_le_pt α k f g z θ
      (fun i => DzIter_add_of_contDiffOn hf hg i (show (z, θ) ∈ quadV from ⟨hzpos, hθ1, hθ2⟩))
      (fun i j => mixed_add_of_contDiffOn hf hg j i
        (show (z, θ) ∈ quadV from ⟨hzpos, hθ1, hθ2⟩))

/-! ## Lifting the pointwise inequality to `HkSq`, and then to the norm -/

/-- **Subadditivity of `HkSq`.**  Given the pointwise inequality for the integrands and the
honest integrability certificates (`HkMem`) for `f` and `g`, integrating over `θ` and then over
`z` gives

`HkSq α k (f+g) ≤ 2·HkSq α k f + 2·HkSq α k g`.

No integrability of `HkIntegrand (f+g)` is needed: `integral_mono_of_nonneg` asks only for the
*upper* function to be integrable, and the upper function is `2·HkIntegrand f + 2·HkIntegrand g`,
integrable by `hmf` and `hmg`. -/
theorem HkSq_add_le_of_pointwise (α : ℝ) (k : ℕ) {f g : ℝ → ℝ → ℝ}
    (hmf : Work.Spaces.HkMem α k f) (hmg : Work.Spaces.HkMem α k g)
    (hpt : ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
      Work.Spaces.HkIntegrand α k (fun z θ => f z θ + g z θ) z θ
        ≤ 2 * Work.Spaces.HkIntegrand α k f z θ + 2 * Work.Spaces.HkIntegrand α k g z θ) :
    Work.Spaces.HkSq α k (fun z θ => f z θ + g z θ)
      ≤ 2 * Work.Spaces.HkSq α k f + 2 * Work.Spaces.HkSq α k g := by
  have hinner : ∀ z ∈ Work.Spaces.Iz,
      (∫ θ in Work.Spaces.Iθ,
          Work.Spaces.HkIntegrand α k (fun z θ => f z θ + g z θ) z θ)
        ≤ 2 * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k f z θ)
          + 2 * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k g z θ) := by
    intro z hz
    have hmono := MeasureTheory.integral_mono_of_nonneg
      (μ := volume.restrict Work.Spaces.Iθ)
      (f := fun θ => Work.Spaces.HkIntegrand α k (fun z θ => f z θ + g z θ) z θ)
      (g := fun θ => 2 * Work.Spaces.HkIntegrand α k f z θ
        + 2 * Work.Spaces.HkIntegrand α k g z θ)
      (Eventually.of_forall fun θ => Work.Spaces.HkIntegrand_nonneg α k _ z θ)
      (((hmf.1 z hz).const_mul 2).add ((hmg.1 z hz).const_mul 2))
      (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc
        fun θ hθ => hpt z hz θ hθ)
    refine hmono.trans_eq ?_
    rw [MeasureTheory.integral_add ((hmf.1 z hz).const_mul 2)
          ((hmg.1 z hz).const_mul 2),
      MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul]
  rw [Work.Spaces.HkSq, Work.Spaces.HkSq, Work.Spaces.HkSq]
  have houter := MeasureTheory.integral_mono_of_nonneg
    (μ := volume.restrict Work.Spaces.Iz)
    (f := fun z => ∫ θ in Work.Spaces.Iθ,
        Work.Spaces.HkIntegrand α k (fun z θ => f z θ + g z θ) z θ)
    (g := fun z => 2 * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k f z θ)
      + 2 * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k g z θ))
    (Eventually.of_forall fun z => integral_nonneg fun θ =>
      Work.Spaces.HkIntegrand_nonneg α k _ z θ)
    ((hmf.2.const_mul 2).add (hmg.2.const_mul 2))
    (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ici fun z hz => hinner z hz)
  refine houter.trans_eq ?_
  rw [MeasureTheory.integral_add (hmf.2.const_mul 2) (hmg.2.const_mul 2),
    MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul]

/-- Subadditivity of the square root: `√(x+y) ≤ √x + √y` for `x,y ≥ 0`. -/
private theorem sqrt_add_le {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    Real.sqrt (x + y) ≤ Real.sqrt x + Real.sqrt y := by
  rw [Real.sqrt_le_iff]
  refine ⟨add_nonneg (Real.sqrt_nonneg x) (Real.sqrt_nonneg y), ?_⟩
  have h1 := Real.sq_sqrt hx
  have h2 := Real.sq_sqrt hy
  nlinarith [Real.sqrt_nonneg x, Real.sqrt_nonneg y]

/-- The `√2`-form used to pass from the squared estimate to the norm. -/
theorem sqrt_two_mul_add_le {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    Real.sqrt (2 * x + 2 * y) ≤ Real.sqrt 2 * (Real.sqrt x + Real.sqrt y) := by
  have hsum : Real.sqrt (2 * x + 2 * y) = Real.sqrt 2 * Real.sqrt (x + y) := by
    rw [show 2 * x + 2 * y = 2 * (x + y) by ring, Real.sqrt_mul (by norm_num)]
  rw [hsum]
  exact mul_le_mul_of_nonneg_left (sqrt_add_le hx hy) (Real.sqrt_nonneg 2)

/-! ## The statement -/

theorem HkNorm_add_le (α : ℝ) (k : ℕ) {f g : ℝ → ℝ → ℝ}
    (hf : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry f) (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)))
    (hg : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry g) (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)))
    (hmf : Work.Spaces.HkMem α k f) (hmg : Work.Spaces.HkMem α k g) :
    Work.Spaces.HkNorm α k (fun z θ => f z θ + g z θ)
      ≤ Real.sqrt 2 * (Work.Spaces.HkNorm α k f + Work.Spaces.HkNorm α k g) := by
  have hf' : ContDiffOn ℝ Work.Stability.smoothOrder (Function.uncurry f) quadV :=
    contDiffOn_smoothOrder_of_forall_nat hf
  have hg' : ContDiffOn ℝ Work.Stability.smoothOrder (Function.uncurry g) quadV :=
    contDiffOn_smoothOrder_of_forall_nat hg
  have hpt := HkIntegrand_add_le_of_contDiffOn α k hf' hg'
  have hsq := HkSq_add_le_of_pointwise α k hmf hmg hpt
  have hx : 0 ≤ Work.Spaces.HkSq α k f := Work.Spaces.HkSq_nonneg α k f
  have hy : 0 ≤ Work.Spaces.HkSq α k g := Work.Spaces.HkSq_nonneg α k g
  have hroot : Work.Spaces.HkNorm α k (fun z θ => f z θ + g z θ)
      ≤ Real.sqrt (2 * Work.Spaces.HkSq α k f + 2 * Work.Spaces.HkSq α k g) :=
    Real.sqrt_le_sqrt hsq
  refine le_trans hroot ?_
  have hsqrt : Real.sqrt (2 * Work.Spaces.HkSq α k f + 2 * Work.Spaces.HkSq α k g)
      = Real.sqrt 2 * Real.sqrt (Work.Spaces.HkSq α k f + Work.Spaces.HkSq α k g) := by
    rw [show 2 * Work.Spaces.HkSq α k f + 2 * Work.Spaces.HkSq α k g
        = 2 * (Work.Spaces.HkSq α k f + Work.Spaces.HkSq α k g) by ring,
      Real.sqrt_mul (by norm_num)]
  rw [hsqrt, Work.Spaces.HkNorm, Work.Spaces.HkNorm]
  exact mul_le_mul_of_nonneg_left (sqrt_add_le hx hy) (Real.sqrt_nonneg 2)

end Work.FTS.EllipticEst
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.Honest.zIBP_compact =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.Honest

open MeasureTheory Set Filter
open scoped Topology

theorem zIBP_compact (α : ℝ) (ω Φ : ℝ → ℝ) {a b : ℝ} (ha : 0 < a) (hab : a < b)
    (hω : ∀ z, z ∉ Set.Icc a b → ω z = 0)
    (hωd : ContDiffOn ℝ 2 ω (Set.Ioi 0)) (hΦd : ContDiffOn ℝ 2 Φ (Set.Ioi 0)) :
    (∫ z in Set.Ioi (0 : ℝ), ω z * (α ^ 2 * z ^ 2 * deriv (deriv Φ) z
        + (α * (5 + α) * z) * deriv Φ z) * Φ z)
      = -α ^ 2 * (∫ z in Set.Ioi (0 : ℝ), ω z * (z * deriv Φ z) ^ 2)
        + (α ^ 2 / 2) * (∫ z in Set.Ioi (0 : ℝ),
            deriv (deriv (fun z => z ^ 2 * ω z)) z * (Φ z) ^ 2)
        - (α * (5 + α) / 2) * (∫ z in Set.Ioi (0 : ℝ), deriv (fun z => z * ω z) z * (Φ z) ^ 2) := by
  have hsub : Set.Icc a b ⊆ Set.Ioi (0 : ℝ) := fun x hx => by
    simp only [Set.mem_Ioi]; linarith [hx.1, ha]
  -- ## 0. Vanishing off the support `[a,b]`
  have hω_off : ∀ z, z ∉ Set.Icc a b → ω =ᶠ[𝓝 z] (fun _ : ℝ => (0 : ℝ)) := by
    intro z hz
    have hz' : z < a ∨ b < z := by
      simpa only [Set.mem_Icc, not_and_or, not_le] using hz
    rcases hz' with hlt | hgt
    · filter_upwards [isOpen_Iio.mem_nhds hlt] with w hw
      exact hω w (by simp only [Set.mem_Icc, not_and_or, not_le]; exact Or.inl hw)
    · filter_upwards [isOpen_Ioi.mem_nhds hgt] with w hw
      exact hω w (by simp only [Set.mem_Icc, not_and_or, not_le]; exact Or.inr hw)
  have hW_off : ∀ z, z ∉ Set.Icc a b → deriv (fun y : ℝ => y ^ 2 * ω y) z = 0 := by
    intro z hz
    have hev : (fun y : ℝ => y ^ 2 * ω y) =ᶠ[𝓝 z] (fun _ : ℝ => (0 : ℝ)) := by
      filter_upwards [hω_off z hz] with y hy
      rw [hy]; ring
    rw [hev.deriv_eq]; simp
  have hddW_off : ∀ z, z ∉ Set.Icc a b →
      deriv (deriv (fun y : ℝ => y ^ 2 * ω y)) z = 0 := by
    intro z hz
    have hz' : z < a ∨ b < z := by
      simpa only [Set.mem_Icc, not_and_or, not_le] using hz
    have hev : deriv (fun y : ℝ => y ^ 2 * ω y) =ᶠ[𝓝 z] (fun _ : ℝ => (0 : ℝ)) := by
      rcases hz' with hlt | hgt
      · filter_upwards [isOpen_Iio.mem_nhds hlt] with w hw
        exact hW_off w (by simp only [Set.mem_Icc, not_and_or, not_le]; exact Or.inl hw)
      · filter_upwards [isOpen_Ioi.mem_nhds hgt] with w hw
        exact hW_off w (by simp only [Set.mem_Icc, not_and_or, not_le]; exact Or.inr hw)
    rw [hev.deriv_eq]; simp
  have hzω_off : ∀ z, z ∉ Set.Icc a b → deriv (fun y : ℝ => y * ω y) z = 0 := by
    intro z hz
    have hev : (fun y : ℝ => y * ω y) =ᶠ[𝓝 z] (fun _ : ℝ => (0 : ℝ)) := by
      filter_upwards [hω_off z hz] with y hy
      rw [hy]; ring
    rw [hev.deriv_eq]; simp
  -- ## 1. Smoothness bookkeeping
  have hW2ω : ContDiffOn ℝ 2 (fun y : ℝ => y ^ 2 * ω y) (Set.Ioi 0) :=
    ContDiffOn.mul (by fun_prop) hωd
  have hW2ω₁ : ContDiffOn ℝ 1 (deriv (fun y : ℝ => y ^ 2 * ω y)) (Set.Ioi 0) :=
    hW2ω.deriv_of_isOpen isOpen_Ioi (by norm_num)
  have hW1ω : ContDiffOn ℝ 2 (fun y : ℝ => y * ω y) (Set.Ioi 0) :=
    ContDiffOn.mul (by fun_prop) hωd
  have hΦ₁ : ContDiffOn ℝ 1 (deriv Φ) (Set.Ioi 0) :=
    hΦd.deriv_of_isOpen isOpen_Ioi (by norm_num)
  have hcontω : ContinuousOn ω (Set.Icc a b) := hωd.continuousOn.mono hsub
  have hcontΦ : ContinuousOn Φ (Set.Icc a b) := hΦd.continuousOn.mono hsub
  have hcontdΦ : ContinuousOn (deriv Φ) (Set.Icc a b) :=
    (hΦd.continuousOn_deriv_of_isOpen isOpen_Ioi (by norm_num)).mono hsub
  have hcontddΦ : ContinuousOn (deriv (deriv Φ)) (Set.Icc a b) :=
    (hΦ₁.continuousOn_deriv_of_isOpen isOpen_Ioi le_rfl).mono hsub
  have hcontdW : ContinuousOn (deriv (fun y : ℝ => y ^ 2 * ω y)) (Set.Icc a b) :=
    (hW2ω.continuousOn_deriv_of_isOpen isOpen_Ioi (by norm_num)).mono hsub
  have hcontddW : ContinuousOn (deriv (deriv (fun y : ℝ => y ^ 2 * ω y))) (Set.Icc a b) :=
    (hW2ω₁.continuousOn_deriv_of_isOpen isOpen_Ioi le_rfl).mono hsub
  have hcontdzω : ContinuousOn (deriv (fun y : ℝ => y * ω y)) (Set.Icc a b) :=
    (hW1ω.continuousOn_deriv_of_isOpen isOpen_Ioi (by norm_num)).mono hsub
  -- ## 2. Integrability (every integrand is continuous on `[a,b]` and zero off it)
  have hi1 : IntegrableOn (fun z : ℝ => z ^ 2 * ω z * Φ z * deriv (deriv Φ) z)
      (Set.Ioi 0) :=
    Work.FTS.EllipticEst.Blocks.integrableOn_Ioi_of_continuousOn_Icc_of_eq_zero_off
      ((((continuousOn_id.pow 2).mul hcontω).mul hcontΦ).mul hcontddΦ)
      (fun z hz => by rw [hω z hz]; ring)
  have hi2 : IntegrableOn
      (fun z : ℝ => deriv (fun y : ℝ => y ^ 2 * ω y) z * Φ z * deriv Φ z) (Set.Ioi 0) :=
    Work.FTS.EllipticEst.Blocks.integrableOn_Ioi_of_continuousOn_Icc_of_eq_zero_off
      ((hcontdW.mul hcontΦ).mul hcontdΦ)
      (fun z hz => by rw [hW_off z hz]; ring)
  have hi3 : IntegrableOn (fun z : ℝ => ω z * (z * deriv Φ z) ^ 2) (Set.Ioi 0) :=
    Work.FTS.EllipticEst.Blocks.integrableOn_Ioi_of_continuousOn_Icc_of_eq_zero_off
      (hcontω.mul ((continuousOn_id.mul hcontdΦ).pow 2))
      (fun z hz => by rw [hω z hz]; ring)
  have hi4 : IntegrableOn
      (fun z : ℝ => deriv (deriv (fun y : ℝ => y ^ 2 * ω y)) z * (Φ z) ^ 2) (Set.Ioi 0) :=
    Work.FTS.EllipticEst.Blocks.integrableOn_Ioi_of_continuousOn_Icc_of_eq_zero_off
      (hcontddW.mul (hcontΦ.pow 2))
      (fun z hz => by rw [hddW_off z hz]; ring)
  have hi1' : IntegrableOn (fun z : ℝ => ω z * z ^ 2 * deriv (deriv Φ) z * Φ z) (Set.Ioi 0) :=
    hi1.congr_fun (fun z _ => by ring) measurableSet_Ioi
  have hIntB0 : IntegrableOn (fun z : ℝ => ω z * z * deriv Φ z * Φ z) (Set.Ioi 0) :=
    Work.FTS.EllipticEst.Blocks.integrableOn_Ioi_of_continuousOn_Icc_of_eq_zero_off
      (((hcontω.mul continuousOn_id).mul hcontdΦ).mul hcontΦ)
      (fun z hz => by rw [hω z hz]; ring)
  have hIntB1 : IntegrableOn (fun z : ℝ => (z * ω z) * (2 * Φ z * deriv Φ z)) (Set.Ioi 0) :=
    Work.FTS.EllipticEst.Blocks.integrableOn_Ioi_of_continuousOn_Icc_of_eq_zero_off
      ((continuousOn_id.mul hcontω).mul (((continuous_const.continuousOn).mul hcontΦ).mul hcontdΦ))
      (fun z hz => by rw [hω z hz]; ring)
  have hIntB2 : IntegrableOn (fun z : ℝ => deriv (fun y : ℝ => y * ω y) z * (Φ z) ^ 2)
      (Set.Ioi 0) :=
    Work.FTS.EllipticEst.Blocks.integrableOn_Ioi_of_continuousOn_Icc_of_eq_zero_off
      (hcontdzω.mul (hcontΦ.pow 2))
      (fun z hz => by rw [hzω_off z hz]; ring)
  -- ## 3. Boundary terms
  have hb1 : Tendsto (fun z : ℝ => z ^ 2 * ω z * Φ z * deriv Φ z)
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have hev : (fun _ : ℝ => (0 : ℝ)) =ᶠ[𝓝[>] (0 : ℝ)]
        (fun z : ℝ => z ^ 2 * ω z * Φ z * deriv Φ z) := by
      filter_upwards [Ioo_mem_nhdsGT ha] with z hz
      rw [hω z (by simp only [Set.mem_Icc, not_and_or, not_le]; exact Or.inl hz.2)]
      ring
    exact tendsto_const_nhds.congr' hev
  have hb2 : Tendsto (fun z : ℝ => z ^ 2 * ω z * Φ z * deriv Φ z) atTop (𝓝 0) := by
    have hev : (fun _ : ℝ => (0 : ℝ)) =ᶠ[atTop]
        (fun z : ℝ => z ^ 2 * ω z * Φ z * deriv Φ z) := by
      filter_upwards [eventually_gt_atTop b] with z hz
      rw [hω z (by simp only [Set.mem_Icc, not_and_or, not_le]; exact Or.inr hz)]
      ring
    exact tendsto_const_nhds.congr' hev
  have hb3 : Tendsto (fun z : ℝ => deriv (fun y : ℝ => y ^ 2 * ω y) z * (Φ z) ^ 2)
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have hev : (fun _ : ℝ => (0 : ℝ)) =ᶠ[𝓝[>] (0 : ℝ)]
        (fun z : ℝ => deriv (fun y : ℝ => y ^ 2 * ω y) z * (Φ z) ^ 2) := by
      filter_upwards [Ioo_mem_nhdsGT ha] with z hz
      rw [hW_off z (by simp only [Set.mem_Icc, not_and_or, not_le]; exact Or.inl hz.2)]
      ring
    exact tendsto_const_nhds.congr' hev
  have hb4 : Tendsto (fun z : ℝ => deriv (fun y : ℝ => y ^ 2 * ω y) z * (Φ z) ^ 2)
      atTop (𝓝 0) := by
    have hev : (fun _ : ℝ => (0 : ℝ)) =ᶠ[atTop]
        (fun z : ℝ => deriv (fun y : ℝ => y ^ 2 * ω y) z * (Φ z) ^ 2) := by
      filter_upwards [eventually_gt_atTop b] with z hz
      rw [hW_off z (by simp only [Set.mem_Icc, not_and_or, not_le]; exact Or.inr hz)]
      ring
    exact tendsto_const_nhds.congr' hev
  have hb5 : Tendsto (fun z : ℝ => (z * ω z) * (Φ z) ^ 2) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have hev : (fun _ : ℝ => (0 : ℝ)) =ᶠ[𝓝[>] (0 : ℝ)]
        (fun z : ℝ => (z * ω z) * (Φ z) ^ 2) := by
      filter_upwards [Ioo_mem_nhdsGT ha] with z hz
      rw [hω z (by simp only [Set.mem_Icc, not_and_or, not_le]; exact Or.inl hz.2)]
      ring
    exact tendsto_const_nhds.congr' hev
  have hb6 : Tendsto (fun z : ℝ => (z * ω z) * (Φ z) ^ 2) atTop (𝓝 0) := by
    have hev : (fun _ : ℝ => (0 : ℝ)) =ᶠ[atTop] (fun z : ℝ => (z * ω z) * (Φ z) ^ 2) := by
      filter_upwards [eventually_gt_atTop b] with z hz
      rw [hω z (by simp only [Set.mem_Icc, not_and_or, not_le]; exact Or.inr hz)]
      ring
    exact tendsto_const_nhds.congr' hev
  -- ## 4. The two integrations by parts
  -- `∫ ω z² Φ'' Φ = (1/2)∫ (z²ω)'' Φ² - ∫ ω (zΦ')²`
  have key1 : (∫ z in Set.Ioi (0 : ℝ), ω z * z ^ 2 * deriv (deriv Φ) z * Φ z)
      = (1 / 2) * (∫ z in Set.Ioi (0 : ℝ),
            deriv (deriv (fun z : ℝ => z ^ 2 * ω z)) z * (Φ z) ^ 2)
        - (∫ z in Set.Ioi (0 : ℝ), ω z * (z * deriv Φ z) ^ 2) :=
    Work.FTS.EllipticEst.remov.ibpZZ ω Φ hωd hΦd hi1 hi2 hi3 hi4 hb1 hb2 hb3 hb4
  -- `∫ z ω Φ' Φ = -(1/2)∫ (zω)' Φ²`
  have hzv : ∀ z ∈ Set.Ioi (0 : ℝ),
      HasDerivAt (fun y : ℝ => y * ω y) (deriv (fun y : ℝ => y * ω y) z) z := by
    intro z hz
    exact (hW1ω.differentiableOn (by norm_num)).hasDerivAt (isOpen_Ioi.mem_nhds hz)
  have hΦ2 : ∀ z ∈ Set.Ioi (0 : ℝ),
      HasDerivAt (fun y : ℝ => (Φ y) ^ 2) (2 * Φ z * deriv Φ z) z := by
    intro z hz
    have hΦz : HasDerivAt Φ (deriv Φ z) z :=
      (hΦd.differentiableOn (by norm_num)).hasDerivAt (isOpen_Ioi.mem_nhds hz)
    convert hΦz.pow 2 using 1
    simp [pow_one, mul_assoc]
  have hIBP2 := MeasureTheory.integral_Ioi_mul_deriv_eq_deriv_mul
    (a := (0 : ℝ)) (a' := (0 : ℝ)) (b' := (0 : ℝ))
    (u := fun y : ℝ => y * ω y) (u' := fun y : ℝ => deriv (fun y : ℝ => y * ω y) y)
    (v := fun y : ℝ => (Φ y) ^ 2) (v' := fun y : ℝ => 2 * Φ y * deriv Φ y)
    hzv hΦ2 hIntB1 hIntB2 hb5 hb6
  have hIBP2' : (∫ z in Set.Ioi (0 : ℝ), (z * ω z) * (2 * Φ z * deriv Φ z))
      = -(∫ z in Set.Ioi (0 : ℝ), deriv (fun y : ℝ => y * ω y) z * (Φ z) ^ 2) := by
    simpa using hIBP2
  have key2 : (∫ z in Set.Ioi (0 : ℝ), ω z * z * deriv Φ z * Φ z)
      = -(1 / 2) * (∫ z in Set.Ioi (0 : ℝ),
            deriv (fun y : ℝ => y * ω y) z * (Φ z) ^ 2) := by
    have hcongr : (∫ z in Set.Ioi (0 : ℝ), (z * ω z) * (2 * Φ z * deriv Φ z))
        = 2 * (∫ z in Set.Ioi (0 : ℝ), ω z * z * deriv Φ z * Φ z) := by
      rw [show (∫ z in Set.Ioi (0 : ℝ), (z * ω z) * (2 * Φ z * deriv Φ z))
            = ∫ z in Set.Ioi (0 : ℝ), 2 * (ω z * z * deriv Φ z * Φ z) from
          setIntegral_congr_fun measurableSet_Ioi (fun z _ => by ring)]
      rw [integral_const_mul]
    rw [hcongr] at hIBP2'
    linarith
  -- ## 5. Assembly
  rw [show (∫ z in Set.Ioi (0 : ℝ), ω z * (α ^ 2 * z ^ 2 * deriv (deriv Φ) z
          + (α * (5 + α) * z) * deriv Φ z) * Φ z)
        = ∫ z in Set.Ioi (0 : ℝ), α ^ 2 * (ω z * z ^ 2 * deriv (deriv Φ) z * Φ z)
            + (α * (5 + α)) * (ω z * z * deriv Φ z * Φ z) from
      setIntegral_congr_fun measurableSet_Ioi (fun z _ => by ring)]
  rw [integral_add (hi1'.const_mul (α ^ 2)) (hIntB0.const_mul (α * (5 + α))),
    integral_const_mul, integral_const_mul, key1, key2]
  ring

end Work.FTS.EllipticEst.Honest
end
-- ===== merged: Submission.Work.FTS.Galerkin.Hilbert.HkMem_add =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.Galerkin.Hilbert

open MeasureTheory Set Filter
open scoped Real Topology


end Work.FTS.Galerkin.Hilbert
end
-- ===== merged: Submission.Work.FTS.H2.Qang_sq_leQ =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.H2

open MeasureTheory
open scoped Real Topology

/-- Cauchy–Schwarz in `θ` for the angular moment, in the interior class: for
`SmoothQuad g`, `HkMem α 4 g`, `j ≤ 4` and `z > 0`,

  `(Qang g j z)² ≤ (∫_θ Ktheta θ²)·(∫_θ (D_z^j g z θ)²)`,

`Qang g j z = ∫_θ Ktheta θ · D_z^j g z θ dθ`.  This is `Work.Elliptic.Qang_sq_le` with the
analyticity hypothesis `Work.Spaces.SmoothNbhd g` replaced by `SmoothQuad g`: both `θ`-slices are
measurable on `Iθ` (they are continuous on the open interval, `SmoothQuad` +
`Work.Spaces.aesm_slice_of_continuousOn_Qd`) and square-integrable there (`Ktheta` is continuous
on the compact `Iθ`; `(D_z^j g z ·)²` is dominated by `HkIntegrand α 4 g z ·` by
`Work.Spaces.sq_le_HkIntegrand_z` and `hmem.1`, on the full-measure open interval `Ioo 0 (π/2)`),
so the inequality is the standard Cauchy–Schwarz for the Bochner integral
(`MeasureTheory.integral_mul_le_Lp_mul_Lq`, or a version of
`Work.Spaces.hardyZ_interval_integral_mul_le_sqrt` for functions merely continuous on the open
interval); no continuity at the angular endpoints `θ = 0, π/2` is needed.  The hypothesis
`j ≤ 4` is needed: `sq_le_HkIntegrand_z` gives the domination only for `j ≤ 4`, and that is what
makes the second factor finite. -/
theorem Qang_sq_leQ (α : ℝ) (g : ℝ → ℝ → ℝ) (hsm : Work.FTS.LocData.SmoothQuad g)
    (hmem : Work.Spaces.HkMem α 4 g) (j : ℕ) (hj : j ≤ 4) {z : ℝ} (hz : 0 < z) :
    (Work.Elliptic.Qang g j z) ^ 2 ≤ (∫ θ in Work.Spaces.Iθ, Work.Elliptic.Ktheta θ ^ 2)
      * (∫ θ in Work.Spaces.Iθ, (Work.Spaces.DzIter j g z θ) ^ 2) := by
  -- `Iθ = Icc 0 (π/2)` and the open interval `Ioo 0 (π/2)` differ by the two endpoints, a null
  -- set: every integral below can be taken over the open interval, where the `θ`-slice of
  -- `D_z^j g` is continuous (`SmoothQuad` only gives smoothness on the *open* quadrant).
  have hIoo : (Set.Icc (0 : ℝ) (π / 2)) =ᵐ[volume] (Set.Ioo (0 : ℝ) (π / 2)) :=
    (MeasureTheory.Ioo_ae_eq_Icc (μ := volume) (a := 0) (b := π / 2)).symm
  have hQeq : Work.Elliptic.Qang g j z
      = ∫ θ in Set.Ioo (0 : ℝ) (π / 2),
          Work.Elliptic.Ktheta θ * Work.Spaces.DzIter j g z θ := by
    rw [Work.Elliptic.Qang]
    exact MeasureTheory.setIntegral_congr_set hIoo
  have hKeq : (∫ θ in Work.Spaces.Iθ, Work.Elliptic.Ktheta θ ^ 2)
      = ∫ θ in Set.Ioo (0 : ℝ) (π / 2), Work.Elliptic.Ktheta θ ^ 2 :=
    MeasureTheory.setIntegral_congr_set hIoo
  have hAeq : (∫ θ in Work.Spaces.Iθ, (Work.Spaces.DzIter j g z θ) ^ 2)
      = ∫ θ in Set.Ioo (0 : ℝ) (π / 2), (Work.Spaces.DzIter j g z θ) ^ 2 :=
    MeasureTheory.setIntegral_congr_set hIoo
  -- the `θ`-slice of `D_z^j g` at `z > 0` is continuous on `(0,π/2)`
  have hzIoi : z ∈ Set.Ioi (-1 : ℝ) := by simp only [Set.mem_Ioi]; linarith
  have hAcont : ContinuousOn (fun θ => Work.Spaces.DzIter j g z θ)
      (Set.Ioo (0 : ℝ) (π / 2)) :=
    ((hsm.DzIter j).curry_θ hzIoi).continuousOn
  -- `Ktheta` is continuous everywhere (hence on `Iθ` and on `Ioo 0 (π/2)`)
  have hKcont : Continuous (fun θ => Work.Elliptic.Ktheta θ) := by
    unfold Work.Elliptic.Ktheta
    fun_prop
  -- integrability of `Ktheta²` on the open interval (continuity on the compact closure)
  have hK2int : IntegrableOn (fun θ => Work.Elliptic.Ktheta θ ^ 2)
      (Set.Ioo (0 : ℝ) (π / 2)) :=
    ((hKcont.pow 2).continuousOn.integrableOn_compact isCompact_Icc).mono_set
      Set.Ioo_subset_Icc_self
  -- integrability of `HkIntegrand α 4 g z ·`, transported from `hmem` to the open interval
  have hHkint : IntegrableOn (fun θ => Work.Spaces.HkIntegrand α 4 g z θ)
      (Set.Ioo (0 : ℝ) (π / 2)) := by
    change Integrable (fun θ => Work.Spaces.HkIntegrand α 4 g z θ)
      (volume.restrict (Set.Ioo (0 : ℝ) (π / 2)))
    rw [← MeasureTheory.Measure.restrict_congr_set hIoo]
    simpa only [Work.Spaces.Iθ, IntegrableOn] using hmem.1 z (le_of_lt hz)
  -- a.e. strong measurability of the `θ`-slice
  have hAesm : AEStronglyMeasurable (fun θ => |Work.Spaces.DzIter j g z θ|)
      (volume.restrict (Set.Ioo (0 : ℝ) (π / 2))) := by
    simpa only [Real.norm_eq_abs] using (hAcont.aestronglyMeasurable measurableSet_Ioo).norm
  -- integrability of `(D_z^j g z ·)²`: dominated by the `ℋ⁴`-integrand on the open interval
  have hA2int : IntegrableOn (fun θ => |Work.Spaces.DzIter j g z θ| ^ 2)
      (Set.Ioo (0 : ℝ) (π / 2)) := by
    refine hHkint.mono' (hAesm.pow 2) ?_
    refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioo (fun θ hθ => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), sq_abs]
    exact Work.Elliptic.sq_DzIter_le_HkIntegrand_Qd α g hj hz hθ.1 hθ.2
  have hKesm : AEStronglyMeasurable (fun θ => |Work.Elliptic.Ktheta θ|)
      (volume.restrict (Set.Ioo (0 : ℝ) (π / 2))) := by
    simpa only [Real.norm_eq_abs] using hKcont.aestronglyMeasurable.norm
  have hKabs : IntegrableOn (fun θ => |Work.Elliptic.Ktheta θ| ^ 2)
      (Set.Ioo (0 : ℝ) (π / 2)) := by
    simpa only [sq_abs] using hK2int
  -- `L²`-membership of the two factors (`p = q = 2`)
  have hKmem : MemLp (fun θ => |Work.Elliptic.Ktheta θ|) (ENNReal.ofReal 2)
      (volume.restrict (Set.Ioo (0 : ℝ) (π / 2))) := by
    rw [show ENNReal.ofReal (2 : ℝ) = 2 by norm_num]
    exact (MeasureTheory.memLp_two_iff_integrable_sq hKesm).mpr hKabs
  have hAmem : MemLp (fun θ => |Work.Spaces.DzIter j g z θ|) (ENNReal.ofReal 2)
      (volume.restrict (Set.Ioo (0 : ℝ) (π / 2))) := by
    rw [show ENNReal.ofReal (2 : ℝ) = 2 by norm_num]
    exact (MeasureTheory.memLp_two_iff_integrable_sq hAesm).mpr hA2int
  -- Cauchy–Schwarz for the Bochner integral (`p = q = 2`, both factors nonnegative)
  have hcs := MeasureTheory.integral_mul_le_Lp_mul_Lq_of_nonneg
    (μ := volume.restrict (Set.Ioo (0 : ℝ) (π / 2)))
    (p := 2) (q := 2) (f := fun θ => |Work.Elliptic.Ktheta θ|)
    (g := fun θ => |Work.Spaces.DzIter j g z θ|)
    (by norm_num [Real.holderConjugate_iff])
    (Filter.Eventually.of_forall fun θ => abs_nonneg _)
    (Filter.Eventually.of_forall fun θ => abs_nonneg _) hKmem hAmem
  have hnQ : |∫ θ in Set.Ioo (0 : ℝ) (π / 2),
        Work.Elliptic.Ktheta θ * Work.Spaces.DzIter j g z θ|
      ≤ ∫ θ in Set.Ioo (0 : ℝ) (π / 2),
          |Work.Elliptic.Ktheta θ| * |Work.Spaces.DzIter j g z θ| := by
    have h := MeasureTheory.norm_integral_le_integral_norm
      (μ := volume.restrict (Set.Ioo (0 : ℝ) (π / 2)))
      (fun θ => Work.Elliptic.Ktheta θ * Work.Spaces.DzIter j g z θ)
    simpa only [Real.norm_eq_abs, abs_mul] using h
  have hKIsq : (∫ θ in Set.Ioo (0 : ℝ) (π / 2), |Work.Elliptic.Ktheta θ| ^ (2 : ℝ))
      = ∫ θ in Set.Ioo (0 : ℝ) (π / 2), Work.Elliptic.Ktheta θ ^ 2 :=
    MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun θ => by
      simp only [Real.rpow_two, sq_abs])
  have hAIsq : (∫ θ in Set.Ioo (0 : ℝ) (π / 2), |Work.Spaces.DzIter j g z θ| ^ (2 : ℝ))
      = ∫ θ in Set.Ioo (0 : ℝ) (π / 2), (Work.Spaces.DzIter j g z θ) ^ 2 :=
    MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun θ => by
      simp only [Real.rpow_two, sq_abs])
  have hK0 : 0 ≤ ∫ θ in Set.Ioo (0 : ℝ) (π / 2), Work.Elliptic.Ktheta θ ^ 2 :=
    MeasureTheory.integral_nonneg (fun θ => sq_nonneg _)
  have hA0 : 0 ≤ ∫ θ in Set.Ioo (0 : ℝ) (π / 2), (Work.Spaces.DzIter j g z θ) ^ 2 :=
    MeasureTheory.integral_nonneg (fun θ => sq_nonneg _)
  have hmain : (∫ θ in Set.Ioo (0 : ℝ) (π / 2),
        Work.Elliptic.Ktheta θ * Work.Spaces.DzIter j g z θ) ^ 2
      ≤ (∫ θ in Set.Ioo (0 : ℝ) (π / 2), Work.Elliptic.Ktheta θ ^ 2)
        * (∫ θ in Set.Ioo (0 : ℝ) (π / 2), (Work.Spaces.DzIter j g z θ) ^ 2) := by
    calc (∫ θ in Set.Ioo (0 : ℝ) (π / 2),
          Work.Elliptic.Ktheta θ * Work.Spaces.DzIter j g z θ) ^ 2
        = |∫ θ in Set.Ioo (0 : ℝ) (π / 2),
            Work.Elliptic.Ktheta θ * Work.Spaces.DzIter j g z θ| ^ 2 := by rw [sq_abs]
      _ ≤ (Real.sqrt (∫ θ in Set.Ioo (0 : ℝ) (π / 2), Work.Elliptic.Ktheta θ ^ 2)
            * Real.sqrt (∫ θ in Set.Ioo (0 : ℝ) (π / 2),
                (Work.Spaces.DzIter j g z θ) ^ 2)) ^ 2 := by
          apply pow_le_pow_left₀ (abs_nonneg _)
          calc |∫ θ in Set.Ioo (0 : ℝ) (π / 2),
                Work.Elliptic.Ktheta θ * Work.Spaces.DzIter j g z θ|
              ≤ ∫ θ in Set.Ioo (0 : ℝ) (π / 2),
                  |Work.Elliptic.Ktheta θ| * |Work.Spaces.DzIter j g z θ| := hnQ
            _ ≤ (∫ θ in Set.Ioo (0 : ℝ) (π / 2),
                    |Work.Elliptic.Ktheta θ| ^ (2 : ℝ)) ^ (1 / 2 : ℝ)
                * (∫ θ in Set.Ioo (0 : ℝ) (π / 2),
                    |Work.Spaces.DzIter j g z θ| ^ (2 : ℝ)) ^ (1 / 2 : ℝ) := hcs
            _ = Real.sqrt (∫ θ in Set.Ioo (0 : ℝ) (π / 2), Work.Elliptic.Ktheta θ ^ 2)
                * Real.sqrt (∫ θ in Set.Ioo (0 : ℝ) (π / 2),
                    (Work.Spaces.DzIter j g z θ) ^ 2) := by
                rw [hKIsq, hAIsq, Real.sqrt_eq_rpow, Real.sqrt_eq_rpow]
      _ = (∫ θ in Set.Ioo (0 : ℝ) (π / 2), Work.Elliptic.Ktheta θ ^ 2)
          * (∫ θ in Set.Ioo (0 : ℝ) (π / 2), (Work.Spaces.DzIter j g z θ) ^ 2) := by
          rw [mul_pow, Real.sq_sqrt hK0, Real.sq_sqrt hA0]
  rw [hQeq, hKeq, hAeq]
  exact hmain

end Work.FTS.H2
end
-- ===== merged: Submission.Work.FTS.LocData.DthIter_Gam_Pf =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.LocData

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false

/-! ## Derivative of the angular polynomials `Qf i` -/

private lemma hd_one_sub_sq (u : ℝ) : HasDerivAt (fun y : ℝ => 1 - y ^ 2) (-2 * u) u := by
  have h := (hasDerivAt_const (x := u) (1 : ℝ)).sub ((hasDerivAt_id u).pow 2)
  convert h using 1 <;> (try (funext y)) <;> simp <;> ring

private lemma hd_one_sub_three_sq (u : ℝ) :
    HasDerivAt (fun y : ℝ => 1 - 3 * y ^ 2) (-6 * u) u := by
  have h := (hasDerivAt_const (x := u) (1 : ℝ)).sub (((hasDerivAt_id u).pow 2).const_mul 3)
  convert h using 1 <;> (try (funext y)) <;> simp <;> ring

private lemma hd_id_sub_third (u : ℝ) : HasDerivAt (fun y : ℝ => y - 1 / 3) 1 u := by
  have h := (hasDerivAt_id u).sub_const (1 / 3)
  convert h using 1 <;> (try (funext y)) <;> simp <;> ring

private lemma hd_three_mul_sub_one (u : ℝ) : HasDerivAt (fun y : ℝ => 3 * y - 1) 3 u := by
  have h := ((hasDerivAt_id u).const_mul 3).sub_const 1
  convert h using 1 <;> (try (funext y)) <;> simp <;> ring

private lemma hd_Qf_zero (α u : ℝ) : HasDerivAt (fun v : ℝ => Qf 0 v α) (dQf 0 u α) u := by
  simp only [Qf_zero, dQf_zero]
  exact hasDerivAt_const (x := u) (1 : ℝ)

private lemma hd_Qf_one (α u : ℝ) : HasDerivAt (fun v : ℝ => Qf 1 v α) (dQf 1 u α) u := by
  simp only [Qf_one, dQf_one]
  have h := (hd_three_mul_sub_one u).div_const 3
  convert h using 1 <;> (try (funext y)) <;> simp <;> ring

private lemma hd_Qf_two (α u : ℝ) : HasDerivAt (fun v : ℝ => Qf 2 v α) (dQf 2 u α) u := by
  simp only [Qf_two, dQf_two]
  have hfun : (fun u : ℝ => -2 * (1 - u ^ 2) + α * (3 * u - 1) ^ 2 / 9)
      = (fun u : ℝ => -2 * (1 - u ^ 2)) + (fun u : ℝ => (α / 9) * (3 * u - 1) ^ 2) := by
    funext y; simp only [Pi.add_apply]; ring
  rw [hfun]
  have h1 : HasDerivAt (fun u : ℝ => -2 * (1 - u ^ 2)) (4 * u) u := by
    have h := ((hasDerivAt_const (x := u) (1 : ℝ)).sub ((hasDerivAt_id u).pow 2)).const_mul (-2)
    convert h using 1 <;> (try (funext y)) <;> simp <;> ring
  have h2 : HasDerivAt (fun u : ℝ => (α / 9) * (3 * u - 1) ^ 2) (2 * α * (u - 1 / 3)) u := by
    have h := ((((hasDerivAt_id u).const_mul 3).sub_const 1).pow 2).const_mul (α / 9)
    convert h using 1 <;> (try (funext y)) <;> simp <;> ring
  exact (h1.add h2).congr_deriv (by ring)

set_option maxHeartbeats 2000000 in
private lemma hd_Qf_three (α u : ℝ) : HasDerivAt (fun v : ℝ => Qf 3 v α) (dQf 3 u α) u := by
  simp only [Qf_three, dQf_three]
  have hfun : (fun u : ℝ => -8 * u * (1 - u ^ 2) - 6 * α * (u - 1 / 3) * (1 - u ^ 2)
        + α ^ 2 * (u - 1 / 3) ^ 3)
      = (fun u : ℝ => -8 * (u * (1 - u ^ 2)))
        + (fun u : ℝ => (-6 * α) * ((u - 1 / 3) * (1 - u ^ 2)))
        + (fun u : ℝ => α ^ 2 * (u - 1 / 3) ^ 3) := by
    funext y; simp only [Pi.add_apply]; ring
  rw [hfun]
  have hA : HasDerivAt (fun u : ℝ => -8 * (u * (1 - u ^ 2)))
      (-8 * (1 * (1 - u ^ 2) + u * (-2 * u))) u :=
    ((hasDerivAt_id u).mul (hd_one_sub_sq u)).const_mul (-8)
  have hB : HasDerivAt (fun u : ℝ => (-6 * α) * ((u - 1 / 3) * (1 - u ^ 2)))
      ((-6 * α) * (1 * (1 - u ^ 2) + (u - 1 / 3) * (-2 * u))) u :=
    ((hd_id_sub_third u).mul (hd_one_sub_sq u)).const_mul (-6 * α)
  have hC : HasDerivAt (fun u : ℝ => α ^ 2 * (u - 1 / 3) ^ 3)
      (α ^ 2 * (3 * (u - 1 / 3) ^ (3 - 1) * 1)) u :=
    ((hd_id_sub_third u).pow 3).const_mul (α ^ 2)
  exact ((hA.add hB).add hC).congr_deriv (by simp; ring)

set_option maxHeartbeats 4000000 in
private lemma hd_Qf_four (α u : ℝ) : HasDerivAt (fun v : ℝ => Qf 4 v α) (dQf 4 u α) u := by
  simp only [Qf_four, dQf_four]
  have hfun : (fun u : ℝ =>
        16 * (1 - u ^ 2) * (1 - 3 * u ^ 2) + 12 * α * (1 - u ^ 2) ^ 2
          - 32 * α * u * (u - 1 / 3) * (1 - u ^ 2)
          - 12 * α ^ 2 * (u - 1 / 3) ^ 2 * (1 - u ^ 2) + α ^ 3 * (u - 1 / 3) ^ 4)
      = (fun u : ℝ => 16 * ((1 - u ^ 2) * (1 - 3 * u ^ 2)))
        + (fun u : ℝ => (12 * α) * ((1 - u ^ 2) * (1 - u ^ 2)))
        + (fun u : ℝ => (-(32 * α)) * ((u * (u - 1 / 3)) * (1 - u ^ 2)))
        + (fun u : ℝ => (-(12 * α ^ 2)) * (((u - 1 / 3) * (u - 1 / 3)) * (1 - u ^ 2)))
        + (fun u : ℝ => α ^ 3 * (u - 1 / 3) ^ 4) := by
    funext y; simp only [Pi.add_apply]; ring
  rw [hfun]
  have h1 : HasDerivAt (fun u : ℝ => 16 * ((1 - u ^ 2) * (1 - 3 * u ^ 2)))
      (16 * ((-2 * u) * (1 - 3 * u ^ 2) + (1 - u ^ 2) * (-6 * u))) u :=
    ((hd_one_sub_sq u).mul (hd_one_sub_three_sq u)).const_mul 16
  have h2 : HasDerivAt (fun u : ℝ => (12 * α) * ((1 - u ^ 2) * (1 - u ^ 2)))
      ((12 * α) * ((-2 * u) * (1 - u ^ 2) + (1 - u ^ 2) * (-2 * u))) u :=
    ((hd_one_sub_sq u).mul (hd_one_sub_sq u)).const_mul (12 * α)
  have h3 : HasDerivAt (fun u : ℝ => (-(32 * α)) * ((u * (u - 1 / 3)) * (1 - u ^ 2)))
      ((-(32 * α)) * ((1 * (u - 1 / 3) + u * 1) * (1 - u ^ 2) + (u * (u - 1 / 3)) * (-2 * u))) u :=
    (((hasDerivAt_id u).mul (hd_id_sub_third u)).mul (hd_one_sub_sq u)).const_mul (-(32 * α))
  have h4 : HasDerivAt (fun u : ℝ => (-(12 * α ^ 2)) * (((u - 1 / 3) * (u - 1 / 3)) * (1 - u ^ 2)))
      ((-(12 * α ^ 2)) * ((1 * (u - 1 / 3) + (u - 1 / 3) * 1) * (1 - u ^ 2)
        + ((u - 1 / 3) * (u - 1 / 3)) * (-2 * u))) u :=
    (((hd_id_sub_third u).mul (hd_id_sub_third u)).mul (hd_one_sub_sq u)).const_mul (-(12 * α ^ 2))
  have h5 : HasDerivAt (fun u : ℝ => α ^ 3 * (u - 1 / 3) ^ 4)
      (α ^ 3 * (4 * (u - 1 / 3) ^ (4 - 1) * 1)) u :=
    ((hd_id_sub_third u).pow 4).const_mul (α ^ 3)
  exact ((((h1.add h2).add h3).add h4).add h5).congr_deriv (by simp; ring)

private lemma hd_Qf (i : ℕ) (hi : i ≤ 4) (α u : ℝ) :
    HasDerivAt (fun v : ℝ => Qf i v α) (dQf i u α) u := by
  interval_cases i
  · exact hd_Qf_zero α u
  · exact hd_Qf_one α u
  · exact hd_Qf_two α u
  · exact hd_Qf_three α u
  · exact hd_Qf_four α u

/-! ## The derivative of `θ ↦ Pf i (cos 2θ) α` -/

private lemma deriv_cos_two_mul (θ : ℝ) :
    deriv (fun t : ℝ => Real.cos (2 * t)) θ = -2 * Real.sin (2 * θ) := by
  have h : HasDerivAt (fun t : ℝ => Real.cos (2 * t)) (-Real.sin (2 * θ) * (2 * 1)) θ :=
    (Real.hasDerivAt_cos (2 * θ)).comp θ ((hasDerivAt_id θ).const_mul 2)
  rw [h.deriv]; ring

private lemma differentiableAt_cos_two_mul (θ : ℝ) :
    DifferentiableAt ℝ (fun t : ℝ => Real.cos (2 * t)) θ := by
  have h : HasDerivAt (fun t : ℝ => Real.cos (2 * t)) (-Real.sin (2 * θ) * (2 * 1)) θ :=
    (Real.hasDerivAt_cos (2 * θ)).comp θ ((hasDerivAt_id θ).const_mul 2)
  exact h.differentiableAt

private lemma Pf_cos_deriv' (i : ℕ) (hi : i ≤ 4) (α θ : ℝ) :
    deriv (fun t : ℝ => Pf i (Real.cos (2 * t)) α) θ
      = -(2 * Real.sin (2 * θ)) * (α * dQf i (Real.cos (2 * θ)) α) := by
  rcases Nat.eq_zero_or_pos i with h | h
  · subst h
    simp only [Pf_zero, dQf_zero, mul_zero]
    simp
  · have hi0 : i ≠ 0 := by omega
    have hfun : (fun t : ℝ => Pf i (Real.cos (2 * t)) α)
        = (fun t : ℝ => α * Qf i (Real.cos (2 * t)) α) := by
      funext t
      simp only [Pf, hi0, ↓reduceIte]
    rw [hfun]
    have hd1 : DifferentiableAt ℝ (fun t : ℝ => Real.cos (2 * t)) θ :=
      differentiableAt_cos_two_mul θ
    have hQ := hd_Qf i hi α (Real.cos (2 * θ))
    have hd2 : DifferentiableAt ℝ (fun u : ℝ => Qf i u α) (Real.cos (2 * θ)) :=
      hQ.differentiableAt
    rw [deriv_const_mul α (by
      have hc : (fun t : ℝ => Qf i (Real.cos (2 * t)) α)
          = ((fun u : ℝ => Qf i u α) ∘ fun t : ℝ => Real.cos (2 * t)) := rfl
      rw [hc]; exact hd2.comp θ hd1)]
    rw [show (fun t : ℝ => Qf i (Real.cos (2 * t)) α)
          = ((fun u : ℝ => Qf i u α) ∘ fun t : ℝ => Real.cos (2 * t)) from rfl]
    rw [deriv_comp θ hd2 hd1, hQ.deriv, deriv_cos_two_mul]
    ring

private lemma Pf_cos_diff (i : ℕ) (hi : i ≤ 4) (α θ : ℝ) :
    DifferentiableAt ℝ (fun t : ℝ => Pf i (Real.cos (2 * t)) α) θ := by
  rcases Nat.eq_zero_or_pos i with h | h
  · subst h
    have hconst : (fun t : ℝ => Pf 0 (Real.cos (2 * t)) α) = fun _ => (1 : ℝ) := by
      funext t; simp
    rw [hconst]
    exact differentiableAt_const (1 : ℝ)
  · have hfun : (fun t : ℝ => Pf i (Real.cos (2 * t)) α)
        = (fun t : ℝ => α * Qf i (Real.cos (2 * t)) α) := by
      funext t
      have hi0 : ¬ i = 0 := by omega
      simp only [Pf, hi0, ↓reduceIte]
    rw [hfun]
    have hQ : DifferentiableAt ℝ (fun u : ℝ => Qf i u α) (Real.cos (2 * θ)) :=
      (hd_Qf i hi α (Real.cos (2 * θ))).differentiableAt
    exact ((hQ.comp θ (differentiableAt_cos_two_mul θ)).const_mul α)

/-! ## `sin(2θ)·Γ' = α(cos 2θ - 1/3)Γ`, for every real `α` -/

private lemma Gam_sin_deriv (α θ : ℝ) (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    Real.sin (2 * θ) * deriv (fun t : ℝ => Work.Spaces.Gam α t) θ
      = α * (Real.cos (2 * θ) - 1 / 3) * Work.Spaces.Gam α θ := by
  have hθ0 : 0 < θ := hθ.1
  have hθ1 : θ < Real.pi / 2 := hθ.2
  have hsin : 0 < Real.sin θ := Real.sin_pos_of_pos_of_lt_pi hθ0 (by linarith [Real.pi_pos])
  have hcos : 0 < Real.cos θ := Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hθ1⟩
  have hG : 0 < Real.sin θ * Real.cos θ ^ 2 := by positivity
  have hprod : HasDerivAt (fun t => Real.sin t * Real.cos t ^ 2)
      (Real.cos θ * Real.cos θ ^ 2
        + Real.sin θ * (2 * Real.cos θ ^ (2 - 1) * (-Real.sin θ))) θ :=
    (Real.hasDerivAt_sin θ).mul ((Real.hasDerivAt_cos θ).pow 2)
  have hrpow := hprod.rpow_const (p := α / 3) (Or.inl (ne_of_gt hG))
  have hderiv : deriv (fun t => Work.Spaces.Gam α t) θ
      = (Real.cos θ * Real.cos θ ^ 2
          + Real.sin θ * (2 * Real.cos θ ^ (2 - 1) * (-Real.sin θ))) * (α / 3)
        * (Real.sin θ * Real.cos θ ^ 2) ^ (α / 3 - 1) := hrpow.deriv
  have hcos2 : Real.cos (2 * θ) = Real.cos θ ^ 2 - Real.sin θ ^ 2 := by
    rw [Real.cos_two_mul]
    linarith [Real.sin_sq_add_cos_sq θ]
  have hq2 : (2 / 3 : ℝ) * (Real.cos θ ^ 2 - 2 * Real.sin θ ^ 2)
      = Real.cos θ ^ 2 - Real.sin θ ^ 2 - 1 / 3 := by
    nlinarith [Real.sin_sq_add_cos_sq θ]
  have hdG : Real.cos θ * Real.cos θ ^ 2
        + Real.sin θ * (2 * Real.cos θ ^ (2 - 1) * (-Real.sin θ))
      = Real.cos θ * (Real.cos θ ^ 2 - 2 * Real.sin θ ^ 2) := by
    norm_num
    ring
  have hcoef : Real.sin (2 * θ) *
        ((Real.cos θ * Real.cos θ ^ 2
          + Real.sin θ * (2 * Real.cos θ ^ (2 - 1) * (-Real.sin θ))) * (α / 3))
      = α * (Real.cos (2 * θ) - 1 / 3) * (Real.sin θ * Real.cos θ ^ 2) := by
    rw [Real.sin_two_mul, hcos2, hdG]
    linear_combination (Real.sin θ * Real.cos θ ^ 2 * α) * hq2
  have hrpowg : (Real.sin θ * Real.cos θ ^ 2) ^ (α / 3)
      = (Real.sin θ * Real.cos θ ^ 2) ^ (α / 3 - 1) * (Real.sin θ * Real.cos θ ^ 2) := by
    conv_lhs => rw [show α / 3 = (α / 3 - 1) + 1 from by ring]
    rw [Real.rpow_add hG (α / 3 - 1) 1, Real.rpow_one]
  rw [hderiv]
  show Real.sin (2 * θ) *
        ((Real.cos θ * Real.cos θ ^ 2
            + Real.sin θ * (2 * Real.cos θ ^ (2 - 1) * (-Real.sin θ))) * (α / 3)
          * (Real.sin θ * Real.cos θ ^ 2) ^ (α / 3 - 1))
      = α * (Real.cos (2 * θ) - 1 / 3) * (Real.sin θ * Real.cos θ ^ 2) ^ (α / 3)
  rw [hrpowg]
  have e1 : Real.sin (2 * θ) *
        ((Real.cos θ * Real.cos θ ^ 2
            + Real.sin θ * (2 * Real.cos θ ^ (2 - 1) * (-Real.sin θ))) * (α / 3)
          * (Real.sin θ * Real.cos θ ^ 2) ^ (α / 3 - 1))
      = (Real.sin (2 * θ) * ((Real.cos θ * Real.cos θ ^ 2
            + Real.sin θ * (2 * Real.cos θ ^ (2 - 1) * (-Real.sin θ))) * (α / 3)))
        * (Real.sin θ * Real.cos θ ^ 2) ^ (α / 3 - 1) := by ring
  have e2 : α * (Real.cos (2 * θ) - 1 / 3) *
        ((Real.sin θ * Real.cos θ ^ 2) ^ (α / 3 - 1) * (Real.sin θ * Real.cos θ ^ 2))
      = (α * (Real.cos (2 * θ) - 1 / 3) * (Real.sin θ * Real.cos θ ^ 2))
        * (Real.sin θ * Real.cos θ ^ 2) ^ (α / 3 - 1) := by ring
  rw [e1, e2, hcoef]

/-! ## The recursion of the angular polynomials -/

private lemma Pf_rec_algebra (i : ℕ) (hi : i ≤ 3) (α θ : ℝ) :
    (α * (Real.cos (2 * θ) - 1 / 3) * Work.Spaces.Gam α θ) * Pf i (Real.cos (2 * θ)) α
      + Work.Spaces.Gam α θ
          * (-(2 * Real.sin (2 * θ) ^ 2) * (α * dQf i (Real.cos (2 * θ)) α))
      = Work.Spaces.Gam α θ * Pf (i + 1) (Real.cos (2 * θ)) α := by
  have hs : Real.sin (2 * θ) ^ 2 = 1 - Real.cos (2 * θ) ^ 2 := by
    have h := Real.sin_sq_add_cos_sq (2 * θ)
    linarith
  interval_cases i
  · simp only [Nat.reduceAdd, Pf_zero, Pf_one, dQf_zero, mul_zero, mul_one]
    ring
  · simp only [Nat.reduceAdd, Pf_one, Pf_two, dQf_one, Qf_two]
    rw [hs]; ring
  · simp only [Nat.reduceAdd, Pf_two, Pf_three, dQf_two, Qf_three]
    rw [hs]; ring
  · simp only [Nat.reduceAdd, Pf_three, Pf_four, dQf_three, Qf_four]
    rw [hs]; ring

/-! ## `DthIter` on functions of `θ` alone -/

private lemma DthIter_rad_eq_prv (i : ℕ) (g : ℝ → ℝ) :
    Work.Spaces.DthIter i (fun _ θ' => g θ') = fun z θ => Work.Spaces.dthU^[i] g θ := by
  induction i with
  | zero => rfl
  | succ i ih =>
      rw [Work.Spaces.DthIter_succ, ih]
      funext z θ
      simp only [Work.Spaces.Dth, Work.Spaces.pth, Work.Spaces.dthU_apply,
        Function.iterate_succ_apply']

/-! ## The jet formula on the open interval -/

private lemma dthU_iter_Gam_eq : ∀ (i : ℕ), i ≤ 4 → ∀ (α θ : ℝ), θ ∈ Set.Ioo 0 (π / 2) →
    Work.Spaces.dthU^[i] (fun t : ℝ => Work.Spaces.Gam α t) θ
      = Work.Spaces.Gam α θ * Pf i (Real.cos (2 * θ)) α := by
  intro i
  induction i with
  | zero => intro _ α θ _; simp
  | succ i ih =>
      intro hi α θ hθ
      have hi3 : i ≤ 3 := by omega
      have hi4 : i ≤ 4 := by omega
      rw [Function.iterate_succ_apply', Work.Spaces.dthU_apply]
      have hmem : Set.Ioo (0 : ℝ) (Real.pi / 2) ∈ 𝓝 θ := IsOpen.mem_nhds isOpen_Ioo hθ
      have hev : (Work.Spaces.dthU^[i] (fun t : ℝ => Work.Spaces.Gam α t))
          =ᶠ[𝓝 θ] ((fun t : ℝ => Work.Spaces.Gam α t)
            * (fun t : ℝ => Pf i (Real.cos (2 * t)) α)) := by
        filter_upwards [hmem] with t ht
        rw [Pi.mul_apply]
        exact ih (by omega) α t ht
      rw [hev.deriv_eq]
      have hG : DifferentiableAt ℝ (fun t : ℝ => Work.Spaces.Gam α t) θ :=
        Work.Spaces.Gam_differentiableAt α θ hθ.1 hθ.2
      have hP : DifferentiableAt ℝ (fun t : ℝ => Pf i (Real.cos (2 * t)) α) θ :=
        Pf_cos_diff i hi4 α θ
      rw [deriv_mul hG hP]
      rw [show Real.sin (2 * θ)
            * (deriv (fun t : ℝ => Work.Spaces.Gam α t) θ * Pf i (Real.cos (2 * θ)) α
              + Work.Spaces.Gam α θ * deriv (fun t : ℝ => Pf i (Real.cos (2 * t)) α) θ)
          = (Real.sin (2 * θ) * deriv (fun t : ℝ => Work.Spaces.Gam α t) θ)
              * Pf i (Real.cos (2 * θ)) α
            + Work.Spaces.Gam α θ
              * (Real.sin (2 * θ) * deriv (fun t : ℝ => Pf i (Real.cos (2 * t)) α) θ)
          from by ring]
      rw [Gam_sin_deriv α θ hθ, Pf_cos_deriv' i hi4 α θ, ← Pf_rec_algebra i hi3 α θ]
      ring

/-! ## The endpoints -/

private lemma Gam_eq_zero_of_endpoint {α θ : ℝ} (hα : α ≠ 0)
    (hθ : θ = 0 ∨ θ = Real.pi / 2) : Work.Spaces.Gam α θ = 0 := by
  have h : α / 3 ≠ 0 := div_ne_zero hα (by norm_num)
  rcases hθ with rfl | rfl
  · simp only [Work.Spaces.Gam, Real.sin_zero, Real.cos_zero, one_pow, mul_one]
    exact Real.zero_rpow h
  · have hc : Real.cos (Real.pi / 2) = 0 := Real.cos_pi_div_two
    simp only [Work.Spaces.Gam, Real.sin_pi_div_two, hc, zero_pow (by norm_num : (2 : ℕ) ≠ 0),
      one_mul, mul_zero]
    exact Real.zero_rpow h

/-- The angular jet formula at the two endpoints of `Iθ`. -/
private lemma dthU_iter_Gam_eq_endpoint (i : ℕ) (hi : i ≠ 0) (α θ : ℝ)
    (hθ : θ = 0 ∨ θ = Real.pi / 2) :
    Work.Spaces.dthU^[i] (fun t : ℝ => Work.Spaces.Gam α t) θ
      = Work.Spaces.Gam α θ * Pf i (Real.cos (2 * θ)) α := by
  have hsin : Real.sin (2 * θ) = 0 := by
    rcases hθ with rfl | rfl
    · simp
    · rw [show 2 * (Real.pi / 2) = Real.pi from by ring, Real.sin_pi]
  have hzero : Work.Spaces.dthU^[i] (fun t : ℝ => Work.Spaces.Gam α t) θ = 0 := by
    obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
    rw [Function.iterate_succ_apply', Work.Spaces.dthU_apply, hsin, zero_mul]
  rw [hzero]
  rcases eq_or_ne α 0 with hα | hα
  · subst hα
    have hG : Work.Spaces.Gam 0 θ = 1 := by
      simp only [Work.Spaces.Gam, zero_div, Real.rpow_zero]
    rw [hG, one_mul]
    simp only [Pf, hi, ↓reduceIte, zero_mul]
  · rw [Gam_eq_zero_of_endpoint hα hθ, zero_mul]

/-! ## The main statement -/

theorem DthIter_Gam_Pf (α : ℝ) (i : ℕ) (hi : i ≤ 4) (z θ : ℝ) (hθ : θ ∈ Work.Spaces.Iθ) :
    Work.Spaces.DthIter i (fun _ θ' => Work.Spaces.Gam α θ') z θ
      = Work.Spaces.Gam α θ * Pf i (Real.cos (2 * θ)) α := by
  rw [DthIter_rad_eq_prv i (fun t : ℝ => Work.Spaces.Gam α t)]
  rcases Nat.eq_zero_or_pos i with h | h
  · subst h
    simp only [Function.iterate_zero_apply, Pf_zero, mul_one]
  · rcases lt_or_eq_of_le hθ.1 with h0 | h0
    · rcases lt_or_eq_of_le hθ.2 with h1 | h1
      · exact dthU_iter_Gam_eq i hi α θ ⟨h0, h1⟩
      · exact dthU_iter_Gam_eq_endpoint i (by omega) α θ (Or.inr h1)
    · exact dthU_iter_Gam_eq_endpoint i (by omega) α θ (Or.inl h0.symm)

end Work.FTS.LocData
end
end
-- ===== merged: Submission.Work.FTS.MeridianDyn.Bridge.Pieces.L12_split_of_slice_integrable =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.MeridianDyn.Bridge.Pieces

theorem L12_split_of_slice_integrable {α : ℝ} {a b : ℝ → ℝ → ℝ}
    (ha : ∀ s : ℝ, 0 < s → MeasureTheory.IntegrableOn
      (fun θ => Work.Spaces.K θ * a s θ / s) Work.Spaces.Iθ)
    (hb : ∀ s : ℝ, 0 < s → MeasureTheory.IntegrableOn
      (fun θ => Work.Spaces.K θ * b s θ / s) Work.Spaces.Iθ)
    (hSum : MeasureTheory.IntegrableOn
      (Work.FM.L12dens Work.Spaces.K (fun z θ => a z θ + b z θ)) (Set.Ioi 0))
    (hA : MeasureTheory.IntegrableOn (Work.FM.L12dens Work.Spaces.K a) (Set.Ioi 0)) :
    ∀ z : ℝ, 0 ≤ z →
      Work.Construction.L12 (fun z θ => a z θ + b z θ) z
        = Work.Construction.L12 a z + Work.Construction.L12 b z := by
  intro z hz
  -- Restrict the two radial integrability hypotheses to `(z,∞)`: `z ≥ 0` gives `(z,∞) ⊆ (0,∞)`.
  have hA' : MeasureTheory.IntegrableOn (Work.FM.L12dens Work.Spaces.K a) (Set.Ioi z) :=
    hA.mono_set (Set.Ioi_subset_Ioi hz)
  -- The density of `b` is the difference of the densities of `a + b` and of `a` on `(z,∞)`:
  -- both of these are integrable there, so `L12dens K b` is too.
  have hB' : MeasureTheory.IntegrableOn (Work.FM.L12dens Work.Spaces.K b) (Set.Ioi z) := by
    refine ((hSum.sub hA).mono_set (Set.Ioi_subset_Ioi hz)).congr_fun ?_ measurableSet_Ioi
    intro s hs
    have hs0 : 0 < s := lt_of_le_of_lt hz hs
    have hadd := Work.FTS.LocData.L12dens_add_of_integrableOn Work.Spaces.K
      (ha s hs0) (hb s hs0)
    simp only [Pi.sub_apply]
    linarith
  -- The densities add pointwise on `(z,∞)`, and the two halves are integrable there.
  simp only [Work.Construction.L12, Work.FM.L12]
  rw [MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
    (fun s hs => Work.FTS.LocData.L12dens_add_of_integrableOn Work.Spaces.K
      (ha s (lt_of_le_of_lt hz hs)) (hb s (lt_of_le_of_lt hz hs)))]
  exact MeasureTheory.integral_add hA' hB'

end Work.FTS.MeridianDyn.Bridge.Pieces
end
-- ===== merged: Submission.Work.H2.T1Q.T1HardAesmQ =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.H2.T1Q

set_option autoImplicit false

/-! ## Almost-everywhere strong measurability of `T1Hard` in the interior class

`Work.FTS.H2.T1HardAesm` proves this for `Work.Spaces.SmoothNbhd` data (analyticity on a
neighbourhood of the closed quadrant).  The localisation chapter works instead with genuine
`C^∞` on the open quadrant, `Work.FTS.LocData.SmoothQuad` (`ContDiffOn ℝ smoothOrder`), which a
cut-off can satisfy.  The proof is the same one: every factor of

`T1Hard α f g z θ = f z θ · w(z)² · ( D_θ(D_z^4 g) · D_z^4 g · sin(2θ)^{-η}
  + (∑_{(j,i)} D_θ(D_z^jD_θ^i g) · D_z^jD_θ^i g) · sin(2θ)^{-γ} )`

is continuous on the open quadrant `(0,∞) × (0,π/2)`: `SmoothQuad` gives `C^∞`-continuity of
`f`, of `g` and of all its `D`-derivatives on the larger set `quadU = (-1,∞) × (0,π/2)`,
`w` is continuous off the axis `z = 0`, and `sin(2θ)^{-p}` is continuous where `sin(2θ) > 0`.
Since the product measure `(volume.restrict Iz).prod (volume.restrict Iθ)` is the planar
Lebesgue measure restricted to the quadrant up to a null set, continuity there gives
`AEStronglyMeasurable`. -/

/-- The open quadrant `(0,∞) × (0,π/2)`, on which all the factors of `T1Hard` are continuous. -/
private def Qd : Set (ℝ × ℝ) := Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)

private lemma mem_Qd {p : ℝ × ℝ} : p ∈ Qd ↔ 0 < p.1 ∧ 0 < p.2 ∧ p.2 < π / 2 := by
  simp only [Qd, Set.mem_prod, Set.mem_Ioi, Set.mem_Ioo]

private lemma Qd_subset_quadU : Qd ⊆ Work.Spaces.quadU := by
  intro p hp
  rw [mem_Qd] at hp
  simp only [Work.Spaces.quadU, Set.mem_prod, Set.mem_Ioi, Set.mem_Ioo]
  exact ⟨by linarith [hp.1], hp.2.1, hp.2.2⟩

private lemma sin_two_pos_of_mem_Qd {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    0 < Real.sin (2 * θ) :=
  Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])

/-! ## The individual factors -/

/-- Every `SmoothQuad` function is continuous on the open quadrant. -/
private lemma contOn_uncurry_of_smoothQuad {F : ℝ → ℝ → ℝ}
    (hF : Work.FTS.LocData.SmoothQuad F) :
    ContinuousOn (fun p : ℝ × ℝ => F p.1 p.2) Qd :=
  hF.continuousOn.mono Qd_subset_quadU




/-- A `D_z`-iterate of a `SmoothQuad` function is continuous on the open quadrant. -/
private lemma contOn_DzIter_Qd (g : ℝ → ℝ → ℝ) (hsmg : Work.FTS.LocData.SmoothQuad g)
    (j : ℕ) :
    ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.DzIter j g p.1 p.2) Qd :=
  contOn_uncurry_of_smoothQuad (hsmg.DzIter j)



/-! ## Joint continuity of `T1Hard` on the open quadrant -/


/-! ## The measurability statement -/


end Work.H2.T1Q
end
end
-- ===== merged: Submission.Work.R1G.AnG =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology NNReal ENNReal
open MeasureTheory Set Filter

namespace Work.R1G


/-! ## The two one-dimensional factors -/

/-- The radial factor `z ↦ z²/(1+z²)⁴`: analytic everywhere, vanishing to second order at `0`,
decaying like `z⁻⁶` at infinity. -/
def Zf (z : ℝ) : ℝ := z ^ 2 / (1 + z ^ 2) ^ 4

/-- The angular factor `θ ↦ sin (2θ)`: entire, vanishing at `0` and `π/2`. -/
def Tf (θ : ℝ) : ℝ := Real.sin (2 * θ)





/-- **The analytic perturbation** `gA z θ = Zf z · Tf θ`. -/
def gA (z θ : ℝ) : ℝ := Zf z * Tf θ





/-! ## Smoothness -/









/-! ## Elementary values and bounds for the radial factor -/









/-! ## Derivatives of the radial factor -/






/-! ## Elementary values, derivatives and bounds for the angular factor -/









/-! ## The iterated operators on the one-dimensional factors -/















/-! ## The two-dimensional perturbation `gA` -/








/-! ## Iterated plain derivatives of `gA` -/






end Work.R1G
end
end
-- ===== merged: Submission.Work.R1G.GTest =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open FiniteTimeSingularity Set Gradient Matrix Filter Topology MeasureTheory
open scoped Topology Matrix NNReal ENNReal

namespace Work.R1G

/-! ## The perturbation and its two factors -/





/-! ## The explicit derivatives -/










/-! ## The elementary derivative computations -/









/-! ## `∂_z` and `∂_θ` of the perturbation -/






/-! ## `D_z` and `D_θ` of the perturbation -/





/-! ## The mixed derivatives needed by `HkIntegrand` -/




/-! ## Vanishing and the visible point -/










end Work.R1G
end
end
-- ===== merged: Submission.Work.R1G.aesm_profile_of_continuous =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.R1G

open MeasureTheory



end Work.R1G
end
-- ===== merged: Submission.Work.SolutionDelivery.DatumOdd =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open FiniteTimeSingularity Set Gradient Matrix Filter Topology MeasureTheory
open scoped Topology Matrix NNReal ENNReal

namespace Work.SolutionDelivery

/-- **The `Cyl` parity dictionary for the Biot–Savart field.**  An axisymmetric no-swirl
Biot–Savart field of a vorticity of parity class `IsOddVorticity` is odd. -/
theorem isOdd_biotSavart_of_axiNoSwirl {ω : R3 → R3}
    (hω : Work.LWP.IsOddVorticity ω) (hax : Work.Cyl.IsAxiNoSwirl (Work.LWP.biotSavart ω)) :
    IsOdd (Work.LWP.biotSavart ω) :=
  Work.Cyl.isOdd_of_reflZ_invariant _ hax
    (fun x => Work.LWP.biotSavart_reflZ Work.LWP.biotSavartReflection_holds hω x)


end Work.SolutionDelivery
end
end
