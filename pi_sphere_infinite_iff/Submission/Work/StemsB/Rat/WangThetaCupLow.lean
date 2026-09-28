import Mathlib
import Submission.Work.StemsB.Rat.WangThetaLow
import Submission.Work.StemsB.Rat.collarSigma_cup_low
import Submission.Work.StemsB.Rat.WangThetaCup
import Submission.Work.StemsB.Rat.wangTauSLow_value

/-!
# The multiplicativity of the low-degree Wang transgression

The transgression `θ_n : H^{n+b}(F) → H^{n+1}(F)` of a fibration over the sphere is a *derivation*
(`Work.StemsB.Rat.wangTheta_cup`, `WangThetaCup.lean`), and the blueprint's `C2` odd step needs it
for the **fundamental class of the fibre**, of degree `b - 1`.  This file transfers the collar
derivation `Work.StemsB.Rat.collarSigma_cup_low` (both factors of degree `b - 1`) to the
transgression:

  `θ_{2b-2}(x ⌣ x) = ((-1)^{b-1} + (-1)^{b(b-1)}) · x ⌣ θ_{b-1}(x)`,

with coefficient `2` for odd `b` (and `0` for even `b`, where `x ⌣ x = 0` by graded commutativity).
-/

open CategoryTheory CategoryTheory.Limits
open scoped Topology

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false

namespace Work.StemsB.Rat

noncomputable section

variable {E : Type} [TopologicalSpace E]

/-- **The multiplicativity of the low-degree Wang transgression**:
`θ_{2b-2}(x ⌣ x) = ((-1)^{b-1} + (-1)^{b(b-1)}) · x ⌣ θ_{b-1}(x)`.  For odd `b` the coefficient
is `2`. -/
theorem wangTheta_cup_low (b : ℕ) (hb : 2 ≤ b) (E : Type) [TopologicalSpace E]
    (p : C(E, SphModel b)) (d_G : ↥(sphLoopBig b))
    (hT_G : FibrewiseTrivial p (sphLoopBig b) d_G)
    (hT_O : FibrewiseTrivial p (sphLoopOuter b) (dOuter b))
    (x : Work.Thom.Coh ℚ (b - 1) ↥(p ⁻¹' {OnePoint.infty})) :
    transT ↥(p ⁻¹' {OnePoint.infty}) (by omega : (b - 2) + 1 = (b - 1) + 0)
        (wangTheta b hb p d_G hT_G hT_O (b - 2)
          (transT ↥(p ⁻¹' {OnePoint.infty}) (by omega : (b - 1) + (b - 1) = (b - 2) + b)
            (cupT ↥(p ⁻¹' {OnePoint.infty}) (b - 1) (b - 1) x x)))
      = (((-1 : ℚ) ^ (b - 1)) + ((-1 : ℚ) ^ ((b - 1) * (b - 1) + (b - 1)))) •
          cupT ↥(p ⁻¹' {OnePoint.infty}) (b - 1) 0 x
            (wangThetaLow b hb E p d_G hT_G hT_O x) := by
  have hb1 : 1 ≤ b := by omega
  have h2 : (b - 1) + (b - 1) = (b - 2) + b := by omega
  have h1 : (b - 2) + 1 = (b - 1) + 0 := by omega
  have hτ := wangSusT_thom b hb (wangFY b p d_G)
  have hs := wangSusS_trans b hb (wangFY b p d_G)
  have hssq := wangSusS_sq b hb (wangFY b p d_G)
  have hσ := wangSusS_sect b hb (wangFY b p d_G)
  -- the ring-map property of `λ_G^*`
  have hU : (collarLambdaGCoh b p d_G hT_G hT_O ((b - 1) + (b - 1))).hom
        (cupT ↥(p ⁻¹' {OnePoint.infty}) (b - 1) (b - 1) x x)
      = cupT ↥(sphLoopCollarProd b (wangFY b p d_G)) (b - 1) (b - 1)
          ((collarLambdaGCoh b p d_G hT_G hT_O (b - 1)).hom x)
          ((collarLambdaGCoh b p d_G hT_G hT_O (b - 1)).hom x) :=
    GCoh_cup b hb1 p d_G hT_G hT_O (b - 1) (b - 1) x x
  -- the collar derivation
  have hder := collarSigma_cup_low b hb (wangFY b p d_G) (wangSusT b hb (wangFY b p d_G))
    hτ (wangSusS b hb (wangFY b p d_G)) hs hssq hσ
    ((collarLambdaGCoh b p d_G hT_G hT_O (b - 1)).hom x)
    ((collarLambdaGCoh b p d_G hT_G hT_O (b - 1)).hom x)
  have hder' : transT (wangFY b p d_G) h1
        (collarSigma b (by omega) (Y := wangFY b p d_G) (wangSusT b hb (wangFY b p d_G)) hτ (b - 2)
          (transT ↥(sphLoopCollarProd b (wangFY b p d_G)) h2
            (cupT ↥(sphLoopCollarProd b (wangFY b p d_G)) (b - 1) (b - 1)
              ((collarLambdaGCoh b p d_G hT_G hT_O (b - 1)).hom x)
              ((collarLambdaGCoh b p d_G hT_G hT_O (b - 1)).hom x))))
      = (((-1 : ℚ) ^ (b - 1)) + ((-1 : ℚ) ^ ((b - 1) * (b - 1) + (b - 1)))) •
          cupT (wangFY b p d_G) (b - 1) 0
            ((Work.Thom.CohMap (collarSection (Y := wangFY b p d_G) b hb1) ℚ (b - 1)).hom
              ((collarLambdaGCoh b p d_G hT_G hT_O (b - 1)).hom x))
            (collarSigmaLow b hb1 (wangFY b p d_G) (wangSusT b hb (wangFY b p d_G)) hτ
              ((collarLambdaGCoh b p d_G hT_G hT_O (b - 1)).hom x)) := by
    rw [hder]
    simp only [transT_self]
    rw [← add_smul]
  -- the identification `ρ (σ^* (λ^* x)) = x`
  have hρσ : (rhoCoh b hb1 p d_G hT_G hT_O (b - 1)).hom
        ((Work.Thom.CohMap (collarSection (Y := wangFY b p d_G) b hb1) ℚ (b - 1)).hom
          ((collarLambdaGCoh b p d_G hT_G hT_O (b - 1)).hom x)) = x := by
    rw [show (Work.Thom.CohMap (collarSection (Y := wangFY b p d_G) b hb1) ℚ (b - 1)).hom
          ((collarLambdaGCoh b p d_G hT_G hT_O (b - 1)).hom x)
        = (lamPtCoh b hb1 p d_G hT_G hT_O (b - 1)).hom x from
      GCoh_sec b hb1 p d_G hT_G hT_O (b - 1) x]
    exact rho_lam b hb1 p d_G hT_G hT_O (b - 1) x
  -- the low-degree transgression of the product
  have hSig : collarSigma b (by omega) (Y := wangFY b p d_G) (wangSusT b hb (wangFY b p d_G)) hτ (b - 2)
        (transT ↥(sphLoopCollarProd b (wangFY b p d_G)) h2
          (cupT ↥(sphLoopCollarProd b (wangFY b p d_G)) (b - 1) (b - 1)
            ((collarLambdaGCoh b p d_G hT_G hT_O (b - 1)).hom x)
            ((collarLambdaGCoh b p d_G hT_G hT_O (b - 1)).hom x)))
      = transT (wangFY b p d_G) h1.symm
          ((((-1 : ℚ) ^ (b - 1)) + ((-1 : ℚ) ^ ((b - 1) * (b - 1) + (b - 1)))) •
            cupT (wangFY b p d_G) (b - 1) 0
              ((Work.Thom.CohMap (collarSection (Y := wangFY b p d_G) b hb1) ℚ (b - 1)).hom
                ((collarLambdaGCoh b p d_G hT_G hT_O (b - 1)).hom x))
              (collarSigmaLow b hb1 (wangFY b p d_G) (wangSusT b hb (wangFY b p d_G)) hτ
                ((collarLambdaGCoh b p d_G hT_G hT_O (b - 1)).hom x))) := by
    rw [transT_round h1 (collarSigma b (by omega) (Y := wangFY b p d_G)
      (wangSusT b hb (wangFY b p d_G)) hτ (b - 2)
      (transT ↥(sphLoopCollarProd b (wangFY b p d_G)) h2
        (cupT ↥(sphLoopCollarProd b (wangFY b p d_G)) (b - 1) (b - 1)
          ((collarLambdaGCoh b p d_G hT_G hT_O (b - 1)).hom x)
          ((collarLambdaGCoh b p d_G hT_G hT_O (b - 1)).hom x))))]
    rw [hder']
  -- the two `λ`-transports
  have hlam : (collarLambdaGCoh b p d_G hT_G hT_O ((b - 2) + b)).hom
        (transT ↥(p ⁻¹' {OnePoint.infty}) h2
          (cupT ↥(p ⁻¹' {OnePoint.infty}) (b - 1) (b - 1) x x))
      = transT ↥(sphLoopCollarProd b (wangFY b p d_G)) h2
          ((collarLambdaGCoh b p d_G hT_G hT_O ((b - 1) + (b - 1))).hom
            (cupT ↥(p ⁻¹' {OnePoint.infty}) (b - 1) (b - 1) x x)) :=
    GCoh_transT b hb1 p d_G hT_G hT_O h2 _
  have hmain : transT ↥(p ⁻¹' {OnePoint.infty}) h1
        (wangTheta b hb p d_G hT_G hT_O (b - 2)
          (transT ↥(p ⁻¹' {OnePoint.infty}) h2
            (cupT ↥(p ⁻¹' {OnePoint.infty}) (b - 1) (b - 1) x x)))
      = (((-1 : ℚ) ^ (b - 1)) + ((-1 : ℚ) ^ ((b - 1) * (b - 1) + (b - 1)))) •
          cupT ↥(p ⁻¹' {OnePoint.infty}) (b - 1) 0 x
            (wangThetaLow b hb E p d_G hT_G hT_O x) := by
    rw [wangTheta_apply]
    rw [hlam, hU]
    rw [hSig]
    rw [rho_transT]
    rw [map_smul]
    rw [rho_cup]
    rw [hρσ]
    rw [show (rhoCoh b hb1 p d_G hT_G hT_O 0).hom
          (collarSigmaLow b hb1 (wangFY b p d_G) (wangSusT b hb (wangFY b p d_G)) hτ
            ((collarLambdaGCoh b p d_G hT_G hT_O (b - 1)).hom x))
        = wangThetaLow b hb E p d_G hT_G hT_O x from wangThetaLow_apply b hb E p d_G hT_G hT_O x]
    rw [map_smul]
    rw [map_smul]
    congr 1
    exact (transT_comp h1.symm h1 _).trans (transT_self _ _)
  exact hmain

/-! ## The `C2`-odd input, in consumer form -/

/-- **For odd `b` the multiplicativity coefficient is `2`.** -/
theorem coeff_odd (b : ℕ) (hb : Odd b) :
    ((-1 : ℚ) ^ (b - 1)) + ((-1 : ℚ) ^ ((b - 1) * (b - 1) + (b - 1))) = 2 := by
  obtain ⟨k, rfl⟩ := hb
  have h1 : ((-1 : ℚ) ^ (2 * k + 1 - 1)) = 1 := by
    rw [show 2 * k + 1 - 1 = 2 * k from by omega, pow_mul]
    norm_num
  have h2 : ((-1 : ℚ) ^ ((2 * k + 1 - 1) * (2 * k + 1 - 1) + (2 * k + 1 - 1))) = 1 := by
    rw [show 2 * k + 1 - 1 = 2 * k from by omega]
    exact Even.neg_one_pow ⟨2 * k * k + k, by ring⟩
  rw [h1, h2]
  norm_num

/-- **The `C2`-odd input.**  Let `b ≥ 2` be odd, `E → S^b` a fibration over the sphere model that
is a Hurewicz fibration and is fibrewise trivial over the two discs (so that the Wang machinery
applies), `x ∈ H^{b-1}(F)` a **non-zero** class of the fibre, and suppose the total space is
`b`-connected (`H^{b-1}(E) = 0`).  Then

* the low-degree transgression `θ_{b-1}` does not kill `x` (`θ_{b-1}(x) ≠ 0`), and
* `θ_{2b-2}(x ⌣ x) = 2 · (x ⌣ θ_{b-1}(x))`.

For `b = n` odd and `x` the fundamental class of the fibre `ΩL_n = K(ℤ,n-1)` of the
`(n-1)`-connected cover `E_n` of `Sⁿ`, these are exactly the two inputs that kill the exceptional
degrees `2n-2`, `2n-1` of the classical computation of `H^*(K(ℤ,n);ℚ)`
(`Submission/Work/Stems/EM_C2_RANGE_FINDING.md` §3, route (A)). -/
theorem c2OddInput (b : ℕ) (hb : 2 ≤ b) (hbodd : Odd b) (E : Type) [TopologicalSpace E]
    (p : C(E, SphModel b)) (d_G : ↥(sphLoopBig b))
    (hT_G : FibrewiseTrivial p (sphLoopBig b) d_G)
    (hT_O : FibrewiseTrivial p (sphLoopOuter b) (dOuter b))
    (hE : Subsingleton (Work.Cohomology.singularCohomology ℚ (b - 1) (TopCat.of E)))
    {x : Work.Thom.Coh ℚ (b - 1) ↥(p ⁻¹' {OnePoint.infty})} (hx : x ≠ 0) :
    wangThetaLow b hb E p d_G hT_G hT_O x ≠ 0 ∧
      transT ↥(p ⁻¹' {OnePoint.infty}) (by omega : (b - 2) + 1 = (b - 1) + 0)
          (wangTheta b hb p d_G hT_G hT_O (b - 2)
            (transT ↥(p ⁻¹' {OnePoint.infty}) (by omega : (b - 1) + (b - 1) = (b - 2) + b)
              (cupT ↥(p ⁻¹' {OnePoint.infty}) (b - 1) (b - 1) x x)))
        = (2 : ℚ) • cupT ↥(p ⁻¹' {OnePoint.infty}) (b - 1) 0 x
            (wangThetaLow b hb E p d_G hT_G hT_O x) := by
  constructor
  · have hb1 : 1 ≤ b := by omega
    have h := wangCohThetaLowR_ne_zero_of_subsingleton ℚ (TopCat.of E) (wangA b p)
      (wangCohFsp b p) b (wangGammaExplicit b p hT_O) (wangTauSLow b hb E p hT_O d_G hT_G) hE hx
    rwa [show (wangCohThetaLowR ℚ (TopCat.of E) (wangA b p) (wangCohFsp b p) b
          (wangGammaExplicit b p hT_O) (wangTauSLow b hb E p hT_O d_G hT_G)).hom x
        = wangThetaLow b hb E p d_G hT_G hT_O x from
      wangTauSLow_value b hb E p hT_O d_G hT_G x] at h
  · rw [wangTheta_cup_low b hb E p d_G hT_G hT_O x, coeff_odd b hbodd]

end

end Work.StemsB.Rat
