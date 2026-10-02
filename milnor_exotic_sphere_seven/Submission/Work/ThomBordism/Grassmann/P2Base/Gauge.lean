import Mathlib
import Submission.Work.ThomBordism.Grassmann.Model
import Submission.Work.Projective.Basic
import Submission.Work.ThomBordism.Grassmann.P2Base.Frame
import Submission.Work.ThomBordism.Grassmann.PlaneEval
import Submission.Work.ThomBordism.Grassmann.PlaneCoord
import Submission.Work.ThomBordism.Grassmann.p1RatAux
import Submission.Work.Gen.Basic
import Submission.Work.Whitney.Basic
import Submission.Work.Thom.realification
import Submission.Work.Thom.manifoldP1
import Submission.Work.Gen.EulerToolkit

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3200000

/-!
# The gauge isomorphism `p2Map^*(γ) ≅ realification(L ⊕ L)`

`p2Map : ℂP⁴ → G̃r₄(ℝ¹²)` sends a complex line `[z]` of `ℂ⁵` to the oriented real `4`-plane
`ℝ-span{Λ(z), iΛ(z), Λ'(z), iΛ'(z)}` of `ℂ⁶ = ℝ¹²`, where `Λ(z) = (z₀,…,z₄,0)`,
`Λ'(z) = (0,z₀,…,z₄)`.  This module proves that the pullback `V4` of the tautological oriented
`4`-plane bundle along `p2Map` is the realification of the direct sum of two copies of the
tautological complex line bundle `L = O(-1)`:

`V4 ≅ Z4 = A4 ⊕_ℝ A4`,  `A4 = mapFibre equivC1R2 (realification L)`.

The comparison is the decomposition of a plane vector in the basis `(Λ(s_{t₁}), Λ'(s_{t₂}))` of
the plane of `x`, where `s_t` is the chart-`t` representative of `x` (`rep4 t x`); the
coefficients are extracted with the complex inner product of `ℂ⁶` (`aCoefL`, `bCoefL`).
-/

namespace Work.ThomBordism.Grassmann.P2Base

open Work.TangentClasses

noncomputable section

/-! ## 1. The chart representatives of `ℂP⁴` -/

/-- The chart-`t` representative of `x : ℂP⁴` as a vector of `ℂ⁵`: the `t`-th coordinate is `1`
and the other coordinates are the affine coordinates of `x` in the chart `t`. -/
def repF (t : Fin 5) (x : Work.Projective.CP 4) : Fin 5 → ℂ :=
  Fin.insertNth (α := fun _ => ℂ) t (1 : ℂ) (Work.Projective.chartFun t x)

/-- The chart-`t` representative of `x : ℂP⁴` as an element of `ℂ⁵ = E5`. -/
def rep4 (t : Fin 5) (x : Work.Projective.CP 4) : E5 := cfOf (repF t x)

theorem rep4_ofLp (t : Fin 5) (x : Work.Projective.CP 4) : (rep4 t x).ofLp = repF t x := rfl

theorem repF_self (t : Fin 5) (x : Work.Projective.CP 4) : repF t x t = 1 :=
  Fin.insertNth_apply_same (α := fun _ => ℂ) t (1 : ℂ) (Work.Projective.chartFun t x)

theorem rep4_ofLp_self (t : Fin 5) (x : Work.Projective.CP 4) : (rep4 t x).ofLp t = 1 :=
  repF_self t x

theorem repF_ne_zero (t : Fin 5) (x : Work.Projective.CP 4) : repF t x ≠ 0 :=
  Work.Projective.insertNth_one_ne_zero t (Work.Projective.chartFun t x)

theorem rep4_ne_zero (t : Fin 5) (x : Work.Projective.CP 4) : rep4 t x ≠ 0 :=
  cfOf_ne_zero (repF_ne_zero t x)

/-- The chart-`t` representative represents `x` on the chart `t`. -/
theorem cpMk_repF (t : Fin 5) (x : Work.Projective.CP 4) (hx : x ∈ Work.Projective.chartSet t) :
    Work.Projective.cpMk 4 ⟨repF t x, repF_ne_zero t x⟩ = x := by
  have h := Work.Projective.chartInv_chartFun t x hx
  rw [Work.Projective.chartInv_apply] at h
  exact h

/-- **The homogeneous coordinates are the coordinates of the chart representatives.** -/
theorem homCoord_repF (t j : Fin 5) (x : Work.Projective.CP 4) :
    Work.Gen.homCoord 4 t j x = repF t x j := by
  by_cases h : j = t
  · subst h
    rw [Work.Gen.homCoord_self, repF, Fin.insertNth_apply_same]
  · rw [Work.Gen.homCoord_of_ne h, repF, Work.Projective.insertNth_apply_of_ne t j h]

theorem continuousOn_repF (t : Fin 5) :
    ContinuousOn (fun x : Work.Projective.CP 4 => repF t x) (Work.Projective.chartSet t) :=
  (Work.Projective.continuous_insertNth_one (n := 4) t).continuousOn.comp
    (Work.Projective.continuousOn_chartFun t) (fun _ _ => Set.mem_univ _)

theorem continuousOn_rep4 (t : Fin 5) :
    ContinuousOn (fun x : Work.Projective.CP 4 => rep4 t x) (Work.Projective.chartSet t) :=
  (PiLp.continuous_toLp (p := 2) (β := fun _ : Fin 5 => ℂ)).continuousOn.comp
    (continuousOn_repF t) (fun _ _ => Set.mem_univ _)

/-- **Two chart representatives of the same point are proportional**, with proportionality factor
the homogeneous coordinate `homCoord 4 t t' x`. -/
theorem rep4_eq_smul (t t' : Fin 5) {x : Work.Projective.CP 4}
    (hx : x ∈ Work.Projective.chartSet t ∩ Work.Projective.chartSet t') :
    rep4 t x = Work.Gen.homCoord 4 t t' x • rep4 t' x := by
  have h1 : Work.Projective.cpMk 4 ⟨repF t x, repF_ne_zero t x⟩ =
      Work.Projective.cpMk 4 ⟨repF t' x, repF_ne_zero t' x⟩ := by
    rw [cpMk_repF t x hx.1, cpMk_repF t' x hx.2]
  obtain ⟨a, ha⟩ := (Work.Projective.cpMk_eq_iff 4 _ _).mp h1
  have h2 : a * repF t' x t' = repF t x t' := by
    simpa only [Pi.smul_apply, smul_eq_mul] using congrFun ha t'
  have hcoef : a = Work.Gen.homCoord 4 t t' x := by
    rw [repF_self, mul_one, ← homCoord_repF t t' x] at h2
    exact h2
  have h3 : repF t x = Work.Gen.homCoord 4 t t' x • repF t' x := by
    rw [← hcoef]
    exact ha.symm
  show cfOf (repF t x) = Work.Gen.homCoord 4 t t' x • cfOf (repF t' x)
  rw [h3, cfOf_smul]

/-! ## 2. The extraction of the coefficients in the basis `(Λ(s), Λ'(s))` -/

/-- The complex inner-product pairing `x ↦ (v ↦ ⟪x, v⟫)` of `ℂ⁶`, as a continuous `ℝ`-linear
functional. -/
def dualC (x : E6) : E6 →L[ℝ] ℂ := (innerSL ℂ x).restrictScalars ℝ

theorem dualC_apply (x v : E6) : dualC x v = inner ℂ x v := rfl

/-- **The coefficient of `Λ'(s)`** in the decomposition `v = a·Λ(s) + b·Λ'(s)`. -/
def bCoefL (s : E5) : E6 →L[ℝ] ℂ := ((‖wVec s‖ ^ 2)⁻¹) • dualC (wVec s)

/-- **The coefficient of `Λ(s)`** in the decomposition `v = a·Λ(s) + b·Λ'(s)`. -/
def aCoefL (s : E5) : E6 →L[ℝ] ℂ :=
  ((‖lamL s‖)⁻¹) • (dualC (lamUnit s) - (inner ℂ (lamUnit s) (lamR s)) • bCoefL s)

theorem bCoefL_apply (s : E5) (v : E6) :
    bCoefL s v = (((‖wVec s‖ ^ 2)⁻¹ : ℝ) : ℂ) * inner ℂ (wVec s) v := by
  show ((‖wVec s‖ ^ 2)⁻¹ : ℝ) • (inner ℂ (wVec s) v) = _
  rw [Complex.real_smul]

theorem aCoefL_apply (s : E5) (v : E6) :
    aCoefL s v = (((‖lamL s‖)⁻¹ : ℝ) : ℂ) *
      (inner ℂ (lamUnit s) v -
        (inner ℂ (lamUnit s) (lamR s)) * (bCoefL s v)) := by
  show ((‖lamL s‖)⁻¹ : ℝ) • (inner ℂ (lamUnit s) v -
      (inner ℂ (lamUnit s) (lamR s)) * (bCoefL s v)) = _
  rw [Complex.real_smul]

/-! ### Inner-product identities for the frame `(Λ, Λ')` -/

theorem lamL_eq_smul_lamUnit (s : E5) (hs : s ≠ 0) :
    lamL s = (‖lamL s‖ : ℂ) • lamUnit s := by
  have hne : ((‖lamL s‖ : ℝ) : ℂ) ≠ 0 := by
    have h : ‖lamL s‖ ≠ 0 := norm_ne_zero_iff.mpr (lamL_ne_zero (z := s) hs)
    exact_mod_cast h
  rw [lamUnit]
  rw [smul_smul, mul_inv_cancel₀ hne, one_smul]

theorem inner_wVec_lamL (s : E5) (hs : s ≠ 0) : inner ℂ (wVec s) (lamL s) = 0 := by
  rw [lamL_eq_smul_lamUnit s hs, inner_smul_right, inner_wVec_lamUnit s hs, mul_zero]

theorem inner_lamUnit_lamL (s : E5) (hs : s ≠ 0) :
    inner ℂ (lamUnit s) (lamL s) = (‖lamL s‖ : ℂ) := by
  conv_lhs => rw [lamL_eq_smul_lamUnit s hs]
  rw [inner_smul_right, inner_lamUnit_lamUnit s hs, mul_one]

theorem inner_wVec_lamR (s : E5) (hs : s ≠ 0) :
    inner ℂ (wVec s) (lamR s) = (‖wVec s‖ ^ 2 : ℝ) := by
  have h : lamR s = (inner ℂ (lamUnit s) (lamR s)) • lamUnit s + wVec s := by
    rw [wVec]; abel
  rw [h, inner_add_right, inner_smul_right, inner_wVec_lamUnit s hs, mul_zero, zero_add,
    inner_self_eq_norm_sq_to_K, Complex.ofReal_pow]
  rfl

/-- **The `Λ'(s)`-coefficient of a vector of the plane is the coordinate.** -/
theorem bCoefL_recon (s : E5) (hs : s ≠ 0) (a b : ℂ) :
    bCoefL s (a • lamL s + b • lamR s) = b := by
  have hw : wVec s ≠ 0 := wVec_ne_zero s hs
  have hr : ((‖wVec s‖ ^ 2 : ℝ) : ℂ) ≠ 0 := by
    have h : (‖wVec s‖ ^ 2 : ℝ) ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.mpr hw)
    exact_mod_cast h
  rw [bCoefL_apply, inner_add_right, inner_smul_right, inner_smul_right, inner_wVec_lamL s hs,
    inner_wVec_lamR s hs, mul_zero, zero_add, mul_comm b, ← mul_assoc, Complex.ofReal_inv,
    inv_mul_cancel₀ hr, one_mul]

/-- **The `Λ(s)`-coefficient of a vector of the plane is the coordinate.** -/
theorem aCoefL_recon (s : E5) (hs : s ≠ 0) (a b : ℂ) :
    aCoefL s (a • lamL s + b • lamR s) = a := by
  have hLn : ((‖lamL s‖ : ℝ) : ℂ) ≠ 0 := by
    have h : ‖lamL s‖ ≠ 0 := norm_ne_zero_iff.mpr (lamL_ne_zero (z := s) hs)
    exact_mod_cast h
  rw [aCoefL_apply, bCoefL_recon s hs a b, inner_add_right, inner_smul_right, inner_smul_right,
    inner_lamUnit_lamL s hs]
  rw [show a * (‖lamL s‖ : ℂ) + b * (inner ℂ (lamUnit s) (lamR s)) -
      (inner ℂ (lamUnit s) (lamR s)) * b = a * (‖lamL s‖ : ℂ) from by ring]
  rw [Complex.ofReal_inv, mul_comm a (↑‖lamL s‖), ← mul_assoc, inv_mul_cancel₀ hLn, one_mul]



/-! ## 5. The two bundles of the gauge -/

abbrev A4 : RealBundle (Work.Projective.CP 4) (EuclideanSpace ℝ (Fin 2)) (Fin 5) :=
  RealBundle.mapFibre equivC1R2 (Work.Thom.realification (Work.Gen.tautLine 4))

abbrev Z4 : RealBundle (Work.Projective.CP 4) (EuclideanSpace ℝ (Fin 4)) (Fin 5 × Fin 5) :=
  Work.Whitney.whitneySumR A4 A4

abbrev V4 : RealBundle (Work.Projective.CP 4) (EuclideanSpace ℝ (Fin 4)) (ChartIdx 4 8) :=
  Work.Thom.bundleComap (tautologicalBundle 4 8) p2Map

theorem A4_baseSet (t : Fin 5) : A4.baseSet t = Work.Projective.chartSet t := by
  rw [A4, RealBundle.mapFibre_baseSet, Work.Thom.realification_baseSet,
    Work.Gen.tautLine_baseSet]

theorem A4_coordChange_apply (t t' : Fin 5) (x : Work.Projective.CP 4)
    (d : EuclideanSpace ℝ (Fin 2)) :
    A4.coordChange t t' x d
      = equivC1R2 (Work.Gen.homCoord 4 t t' x • (equivC1R2.symm d)) := by
  rw [A4, RealBundle.mapFibre_coordChange]
  change equivC1R2 ((Work.Thom.realification (Work.Gen.tautLine 4)).coordChange t t' x
    (equivC1R2.symm d)) = equivC1R2 (Work.Gen.homCoord 4 t t' x • (equivC1R2.symm d))
  rw [Work.Thom.realification_coordChange, Work.Gen.tautLine_coordChange]
  rfl

theorem Z4_baseSet (t : Fin 5 × Fin 5) :
    Z4.baseSet t = Work.Projective.chartSet t.1 ∩ Work.Projective.chartSet t.2 := by
  rw [Z4, Work.Whitney.whitneySumR_baseSet, A4_baseSet, A4_baseSet]

theorem V4_baseSet (S : ChartIdx 4 8) : V4.baseSet S = p2Map ⁻¹' baseSet S := rfl

theorem V4_coordChange_apply (S S' : ChartIdx 4 8) (x : Work.Projective.CP 4)
    (c : EuclideanSpace ℝ (Fin 4)) :
    V4.coordChange S S' x c = coordChangeO S S' (p2Map x) c := rfl

/-- The element `1` of the one-dimensional complex model fibre. -/
def oneC : EuclideanSpace ℂ (Fin 1) := EuclideanSpace.single (𝕜 := ℂ) 0 1

/-- The image in the standard fibre `ℝ²` of a complex number. -/
def mkAmbC (a : ℂ) : EuclideanSpace ℝ (Fin 2) := equivC1R2 (a • oneC)

/-- The same, as a continuous linear map. -/
def mkAmbCCLM : ℂ →L[ℝ] EuclideanSpace ℝ (Fin 2) :=
  (equivC1R2 : EuclideanSpace ℂ (Fin 1) →L[ℝ] EuclideanSpace ℝ (Fin 2)).comp
    ((ContinuousLinearMap.id ℝ ℂ).smulRight oneC)

theorem mkAmbCCLM_apply (a : ℂ) : mkAmbCCLM a = mkAmbC a := rfl

/-- **The scalar action `a ↦ h·a` is the transition function of `A4`.** -/
theorem mkAmbC_coordChange (t t' : Fin 5) (x : Work.Projective.CP 4) (a : ℂ) :
    A4.coordChange t t' x (mkAmbC a) = mkAmbC (Work.Gen.homCoord 4 t t' x * a) := by
  rw [A4_coordChange_apply, mkAmbC, ContinuousLinearEquiv.symm_apply_apply, mkAmbC, smul_smul]

/-- **The transition function of `Z4` on the coordinates `(a, b)`.** -/
theorem Z4_coordChange_pair (t t' : Fin 5 × Fin 5) (x : Work.Projective.CP 4) (a b : ℂ) :
    Z4.coordChange t t' x (Work.Whitney.sumFibreR 2 2 (mkAmbC a, mkAmbC b))
      = Work.Whitney.sumFibreR 2 2 (mkAmbC (Work.Gen.homCoord 4 t.1 t'.1 x * a),
          mkAmbC (Work.Gen.homCoord 4 t.2 t'.2 x * b)) := by
  rw [Z4, Work.Whitney.whitneySumR_coordChange]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_prodMap',
    ContinuousLinearEquiv.coe_coe]
  rw [ContinuousLinearEquiv.symm_apply_apply]
  rw [show Prod.map (A4.coordChange t.1 t'.1 x) (A4.coordChange t.2 t'.2 x)
        (mkAmbC a, mkAmbC b)
      = (A4.coordChange t.1 t'.1 x (mkAmbC a), A4.coordChange t.2 t'.2 x (mkAmbC b))
      from rfl]
  rw [mkAmbC_coordChange, mkAmbC_coordChange]

end

end Work.ThomBordism.Grassmann.P2Base
