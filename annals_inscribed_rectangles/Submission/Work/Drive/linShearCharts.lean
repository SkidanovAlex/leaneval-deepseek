import Mathlib
import Submission.Work.Drive.exists_hrank_hgen_trans
import Submission.Work.Drive.linStd_finrank
import Submission.Work.Drive.ProjectiveDefs

/-!
# The sheared linear charts `linBase A k` (the lead's `NOTES_LEAD_hodd_faces.md` §3)

The three coordinate-permutation charts `φ k = (coordPermCLM (coordPerms k)).trans A` of
`Work.Drive.exists_hrank_hgen_trans` have a **defect**: their planes
`ℓ_k = linSub ((coordPermCLM (coordPerms k)).trans A)` are the three coordinate hyperplanes
`{v : v (ρ_k 3) = 0}` with `ρ_k 3 ∈ {1,2,3}`, so `ℓ_0 ∩ ℓ_1 = span {e_0, e_3}` is a **line**: the two
fold curves of the two disk charts meet, and `PairReg lin₀ lin₁` fails at the resulting fold–fold meet
(`NOTES_LEAD_hodd_faces.md` §0.3).

The repair is to *shear* before the permutation: replace `x 2` by `x 2 + α_k · x 1`, with
`α = ![0,1,1]`.  This file provides the shear and the transport of the two clauses `hrank`, `hgen` from
the unsheared family:

* `Work.Drive.linShear k` — the shear `(x 0, x 1, x 2, x 3) ↦ (x 0, x 1, x 2 + α_k x 1, x 3)`;
* `Work.Drive.linShear_linVecC_ofReal` — on the **real** diameter the shear fixes the sphere lift
  `linVecC t` (its first coordinate is `t.im = 0`), which is why the non-collision clause `hgood` of
  `exists_trans_avoid_negParallel` transfers *verbatim*;
* `Work.Drive.linStd_map_linShear` / `Work.Drive.linSub_linShear_trans` — the shear preserves the
  standard plane `linStd = {v : v 3 = 0}` and hence the plane of every linear chart: `hrank` transfers
  and the common point is *the same*;
* `Work.Drive.linBase A k` — the repaired family `(linShear k).trans ((coordPermCLM (coordPerms k)).trans A)`;
* `Work.Drive.finrank_iInf_linSub_linBase`, `Work.Drive.linCommonPt_linBase`,
  `Work.Drive.hgen_linBase` — the transport of the general-position clauses to the repaired family.

The remaining piece of §3 is `Work.Drive.pairReg_linPlaneCharts_of_incidence` (the incidence criterion
for the repaired planes), delegated separately.
-/

namespace Work.Drive

open Manifold
open scoped Manifold ContDiff

noncomputable section

/-! ## 1. The shear `x 2 ↦ x 2 + α_k x 1` -/

/-- The shear coefficients `α = ![0, 1, 1]`: the first coordinate permutation is used without a shear
(its plane already misses the second one), the other two are sheared. -/
def linAlpha : Fin 3 → ℝ := ![0, 1, 1]

lemma linAlpha_zero : linAlpha 0 = 0 := rfl
lemma linAlpha_one : linAlpha 1 = 1 := rfl
lemma linAlpha_two : linAlpha 2 = 1 := rfl

/-- The basis vector `e₂` of `Eucl 3 = ℝ⁴`. -/
abbrev linE2 : Eucl 3 := (EuclideanSpace.single 2 (1 : ℝ) : Eucl 3)

/-- **The shear, as a function**: `x ↦ x + (α_k · x 1) • e₂`. -/
def linShearFun (k : Fin 3) (x : Eucl 3) : Eucl 3 :=
  x + (linAlpha k * x 1) • linE2

@[simp] lemma linShearFun_apply_zero (k : Fin 3) (x : Eucl 3) : linShearFun k x 0 = x 0 := by
  simp [linShearFun]

@[simp] lemma linShearFun_apply_one (k : Fin 3) (x : Eucl 3) : linShearFun k x 1 = x 1 := by
  simp [linShearFun]

@[simp] lemma linShearFun_apply_two (k : Fin 3) (x : Eucl 3) :
    linShearFun k x 2 = x 2 + linAlpha k * x 1 := by
  simp [linShearFun]

@[simp] lemma linShearFun_apply_three (k : Fin 3) (x : Eucl 3) : linShearFun k x 3 = x 3 := by
  simp [linShearFun]

/-- The shear is additive. -/
lemma linShearFun_add (k : Fin 3) (x y : Eucl 3) :
    linShearFun k (x + y) = linShearFun k x + linShearFun k y := by
  simp only [linShearFun, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
  rw [mul_add, add_smul]
  abel

/-- The shear commutes with scalar multiplication. -/
lemma linShearFun_smul (k : Fin 3) (a : ℝ) (x : Eucl 3) :
    linShearFun k (a • x) = a • linShearFun k x := by
  simp only [linShearFun, PiLp.smul_apply, smul_eq_mul]
  rw [smul_add, smul_smul]
  have hcoef : linAlpha k * (a * x.ofLp 1) = a * (linAlpha k * x.ofLp 1) := by ring
  rw [hcoef]

/-- The inverse shear `x ↦ x - (α_k · x 1) • e₂`. -/
def linShearInvFun (k : Fin 3) (x : Eucl 3) : Eucl 3 :=
  x - (linAlpha k * x 1) • linE2

@[simp] lemma linShearInvFun_apply_one (k : Fin 3) (x : Eucl 3) : linShearInvFun k x 1 = x 1 := by
  simp [linShearInvFun]

@[simp] lemma linShearInvFun_apply_three (k : Fin 3) (x : Eucl 3) : linShearInvFun k x 3 = x 3 := by
  simp [linShearInvFun]

lemma linShearFun_left_inv (k : Fin 3) (x : Eucl 3) :
    linShearFun k (linShearInvFun k x) = x := by
  ext i
  fin_cases i <;> simp [linShearFun, linShearInvFun]

lemma linShearFun_right_inv (k : Fin 3) (x : Eucl 3) :
    linShearInvFun k (linShearFun k x) = x := by
  ext i
  fin_cases i <;> simp [linShearFun, linShearInvFun]

/-- **The shear as a linear equivalence of `Eucl 3`.** -/
def linShearLin (k : Fin 3) : Eucl 3 ≃ₗ[ℝ] Eucl 3 where
  toFun := linShearFun k
  invFun := linShearInvFun k
  left_inv := linShearFun_right_inv k
  right_inv := linShearFun_left_inv k
  map_add' := linShearFun_add k
  map_smul' := linShearFun_smul k

/-- **The shear as a continuous linear equivalence of `Eucl 3`** (finite dimension). -/
def linShear (k : Fin 3) : Eucl 3 ≃L[ℝ] Eucl 3 := (linShearLin k).toContinuousLinearEquiv

@[simp] lemma linShear_apply (k : Fin 3) (x : Eucl 3) : linShear k x = linShearFun k x := rfl

/-! ## 2. The shear fixes the sphere lift on the real diameter -/

/-- **The shear fixes `linVecC t` for real `t`**: the lift `linVecC t = (t, 0, 1-t², 0)` has vanishing
first real coordinate (`im t = 0`), and the shear only moves the coordinate `1` into the coordinate `2`.

This is the reason the non-collision clause `hgood` of the *unsheared* family transfers to the sheared
one: `hgood` is only asked at the real zero locus of the weight `z ↦ z.im`. -/
theorem linShear_linVecC_ofReal (k : Fin 3) (t : ℝ) :
    linShear k (linVecC (t : ℂ)) = linVecC (t : ℂ) := by
  have h1 : (linVecC (t : ℂ)) 1 = 0 := by
    rw [linVecC, ofComplex, WithLp.ofLp_toLp]
    simp
  ext i
  fin_cases i <;> simp [linShearFun, h1]

/-! ## 3. The shear preserves the standard plane `linStd = {v : v 3 = 0}` -/

/-- The shear does not change the coordinate `3`. -/
lemma linShear_apply_three (k : Fin 3) (x : Eucl 3) : (linShear k x) 3 = x 3 :=
  linShearFun_apply_three k x

/-- **The shear preserves the standard plane.**  `linStd = {v : v 3 = 0}`
(`Work.Drive.linStd_eq_ker_coord`), and the shear fixes the coordinate `3` and is onto. -/
theorem linStd_map_linShear (k : Fin 3) :
    linStd.map (linShear k).toLinearEquiv.toLinearMap = linStd := by
  refine le_antisymm ?_ ?_
  · rintro w ⟨v, hv, rfl⟩
    rw [linStd_eq_ker_coord] at hv ⊢
    change linStdCoord v = 0 at hv
    change linStdCoord (linShear k v) = 0
    rw [linStdCoord_apply] at hv ⊢
    rw [linShear_apply_three]
    exact hv
  · intro v hv
    refine ⟨(linShear k).symm v, ?_, (linShear k).apply_symm_apply v⟩
    rw [linStd_eq_ker_coord] at hv ⊢
    change linStdCoord v = 0 at hv
    change linStdCoord ((linShear k).symm v) = 0
    rw [linStdCoord_apply] at hv ⊢
    have h := linShear_apply_three k ((linShear k).symm v)
    rw [ContinuousLinearEquiv.apply_symm_apply] at h
    rw [← h]
    exact hv

/-- **The shear preserves the plane of any linear chart**: `linSub (S.trans φ) = linSub φ`. -/
theorem linSub_linShear_trans (k : Fin 3) (φ : Eucl 3 ≃L[ℝ] Eucl 3) :
    linSub ((linShear k).trans φ) = linSub φ := by
  rw [linSub_trans]
  show (linSub (linShear k)).map φ.toLinearEquiv.toLinearMap = linSub φ
  rw [linSub, linStd_map_linShear]
  rfl

/-! ## 4. The repaired family `linBase A k` -/

/-- **The sheared (repaired) linear chart family**: shear first, then the coordinate permutation, then
`A`.  Its planes are those of `A ∘ (coordinate permutation)` (`Work.Drive.linSub_linShear_trans`), but
the shear removes the fold–fold incidence that makes `PairReg lin₀ lin₁` fail for the unsheared family
(`NOTES_LEAD_hodd_faces.md` §0.3). -/
abbrev linBase (A : Eucl 3 ≃L[ℝ] Eucl 3) (k : Fin 3) : Eucl 3 ≃L[ℝ] Eucl 3 :=
  (linShear k).trans ((coordPermCLM (coordPerms k)).trans A)

lemma linBase_apply (A : Eucl 3 ≃L[ℝ] Eucl 3) (k : Fin 3) (x : Eucl 3) :
    linBase A k x = A ((coordPermCLM (coordPerms k)) (linShear k x)) := rfl

/-- **The plane of the repaired family is the plane of the unsheared family.** -/
theorem linSub_linBase (A : Eucl 3 ≃L[ℝ] Eucl 3) (k : Fin 3) :
    linSub (linBase A k) = linSub ((coordPermCLM (coordPerms k)).trans A) :=
  linSub_linShear_trans k _

/-- **`hrank` for the repaired family** (transported from `Work.Drive.finrank_iInf_linSub_trans`). -/
theorem finrank_iInf_linSub_linBase (A : Eucl 3 ≃L[ℝ] Eucl 3) :
    Module.finrank ℝ ↥(⨅ k : Fin 3, linSub (linBase A k)) = 1 := by
  have h : (⨅ k : Fin 3, linSub (linBase A k))
      = (⨅ k : Fin 3, linSub ((coordPermCLM (coordPerms k)).trans A)) :=
    iInf_congr fun k => linSub_linBase A k
  rw [h]
  exact finrank_iInf_linSub_trans A

/-- **The common point of the repaired family is the common point of the unsheared family.** -/
theorem linCommonPt_linBase (A : Eucl 3 ≃L[ℝ] Eucl 3) (c : ℝ) (hc : 0 < c) :
    linCommonPt (fun k => linBase A k) c hc (finrank_iInf_linSub_linBase A)
      = linCommonPt (fun k => (coordPermCLM (coordPerms k)).trans A) c hc
          (finrank_iInf_linSub_trans A) := by
  refine eq_linCommonPt (fun k => (coordPermCLM (coordPerms k)).trans A) c hc _ ?_ ?_
  · exact level_linCommonPt (fun k => linBase A k) c hc _
  · intro k
    rw [← linSub_linBase A k]
    exact mem_projLine_linCommonPt (fun k => linBase A k) c hc _ k

/-! ## 5. The boundary avoidance `hgen` for the repaired family -/

/-- The real coordinate `0` of the sphere lift of a complex number. -/
lemma linVecC_apply_zero' (z : ℂ) : (linVecC z) 0 = z.re := by
  rw [linVecC, ofComplex, WithLp.ofLp_toLp]
  simp

/-- The real coordinate `1` of the sphere lift of a complex number. -/
lemma linVecC_apply_one' (z : ℂ) : (linVecC z) 1 = z.im := by
  rw [linVecC, ofComplex, WithLp.ofLp_toLp]
  simp

/-- The real coordinate `0` of the sheared lift. -/
lemma linShear_linVecC_zero (k : Fin 3) (z : ℂ) : (linShear k (linVecC z)) 0 = z.re := by
  rw [linShear_apply, linShearFun_apply_zero, linVecC_apply_zero']

/-- The real coordinate `1` of the sheared lift. -/
lemma linShear_linVecC_one (k : Fin 3) (z : ℂ) : (linShear k (linVecC z)) 1 = z.im := by
  rw [linShear_apply, linShearFun_apply_one, linVecC_apply_one']

/-- The real coordinate `3` of the sheared lift. -/
lemma linShear_linVecC_three (k : Fin 3) (z : ℂ) : (linShear k (linVecC z)) 3 = 0 := by
  rw [linShear_apply, linShearFun_apply_three, linVecC_apply_three]

/-- The index identities of the three coordinate permutations that the boundary argument uses. -/
lemma coordPerms_symm_one_one : (coordPerms 1).symm 1 = 0 := by decide
lemma coordPerms_symm_one_three : (coordPerms 1).symm 3 = 1 := by decide
lemma coordPerms_symm_two_one : (coordPerms 2).symm 1 = 0 := by decide
lemma coordPerms_symm_two_two : (coordPerms 2).symm 2 = 1 := by decide

/-- A coordinate of `EuclideanSpace.single 0 1` vanishes away from the index `0`. -/
lemma single_zero_one_apply_of_ne {j : Fin 4} (hj : j ≠ 0) :
    (EuclideanSpace.single 0 (1 : ℝ) : Eucl 3) j = 0 := by
  rw [PiLp.single_apply, if_neg hj]

/-- The index `0` coordinate of `EuclideanSpace.single 0 1`. -/
lemma single_zero_one_apply_zero :
    (EuclideanSpace.single 0 (1 : ℝ) : Eucl 3) 0 = 1 := by
  simp

/-- **The sheared boundary circle does not meet the line of the common point.**  For `‖z‖ = 1`, the
sheared lift `S_k (linVecC z)` is *not* a multiple of `single 0 1` after the permutation `ρ_k`: for
`k = 0` the coordinate `0` of `ρ_0 (S_0 (linVecC z))` is `(linVecC z) 2 = 1 - ‖z‖² = 0`, forcing the
multiplier to vanish; for `k = 1` the coordinates `1` and `3` give `z.re = z.im = 0`; for `k = 2` the
coordinates `1` and `2` do. -/
lemma linShear_ne_smul_single (k : Fin 3) {z : ℂ} (hz : ‖z‖ = 1) (a : ℝˣ) :
    a • (EuclideanSpace.single 0 (1 : ℝ) : Eucl 3)
      ≠ (coordPermCLM (coordPerms k)) (linShear k (linVecC z)) := by
  intro h
  have key : ∀ j : Fin 4, (a : ℝ) * (EuclideanSpace.single 0 (1 : ℝ) : Eucl 3) j
      = (linShear k (linVecC z)) ((coordPerms k).symm j) := by
    intro j
    have h' : (a • (EuclideanSpace.single 0 (1 : ℝ) : Eucl 3)) j
        = ((coordPermCLM (coordPerms k)) (linShear k (linVecC z))) j := by rw [h]
    rw [Units.smul_def, PiLp.smul_apply, smul_eq_mul, coordPermCLM_apply] at h'
    exact h'
  have hk : k = 0 ∨ k = 1 ∨ k = 2 := by fin_cases k <;> simp
  rcases hk with rfl | rfl | rfl
  · have htwo : (linShear 0 (linVecC z)) 2 = 0 := by
      rw [linShear_apply, linShearFun_apply_two, linAlpha_zero, zero_mul, add_zero,
        linVecC_apply_two, hz]
      norm_num
    have h0 := key 0
    rw [single_zero_one_apply_zero, mul_one, coordPerms_symm_zero, htwo] at h0
    have hz0 : linShear 0 (linVecC z) = 0 := by
      have h' : (coordPermCLM (coordPerms 0)) (linShear 0 (linVecC z)) = 0 := by
        rw [h.symm, Units.smul_def, h0, zero_smul]
      apply (coordPermCLM (coordPerms 0)).injective
      rw [map_zero]
      exact h'
    refine linVecC_ne_zero z ?_
    simpa [linShear_apply, linShearFun, linAlpha_zero] using hz0
  · have h1 := key 1
    have h3 := key 3
    rw [single_zero_one_apply_of_ne (show (1 : Fin 4) ≠ 0 by decide), mul_zero,
      coordPerms_symm_one_one, linShear_linVecC_zero] at h1
    rw [single_zero_one_apply_of_ne (show (3 : Fin 4) ≠ 0 by decide), mul_zero,
      coordPerms_symm_one_three, linShear_linVecC_one] at h3
    have hzre : z.re = 0 := h1.symm
    have hzim : z.im = 0 := h3.symm
    have hz0 : z = 0 := Complex.ext hzre hzim
    rw [hz0, norm_zero] at hz
    norm_num at hz
  · have h1 := key 1
    have h2 := key 2
    rw [single_zero_one_apply_of_ne (show (1 : Fin 4) ≠ 0 by decide), mul_zero,
      coordPerms_symm_two_one, linShear_linVecC_zero] at h1
    rw [single_zero_one_apply_of_ne (show (2 : Fin 4) ≠ 0 by decide), mul_zero,
      coordPerms_symm_two_two, linShear_linVecC_one] at h2
    have hzre : z.re = 0 := h1.symm
    have hzim : z.im = 0 := h2.symm
    have hz0 : z = 0 := Complex.ext hzre hzim
    rw [hz0, norm_zero] at hz
    norm_num at hz

/-- **The boundary avoidance `hgen` for the repaired family**: the repaired charts never attain the
common point of their planes on the boundary circle. -/
theorem hgen_linBase (A : Eucl 3 ≃L[ℝ] Eucl 3) (c : ℝ) (hc : 0 < c) :
    ∀ (k : Fin 3) (z : ℂ), ‖z‖ = 1 →
      linPlaneChart (linBase A k) c hc z
        ≠ linCommonPt (fun k => linBase A k) c hc (finrank_iInf_linSub_linBase A) := by
  intro k z hz heq
  rw [linCommonPt_linBase] at heq
  have hA : A (EuclideanSpace.single 0 (1 : ℝ) : Eucl 3) ≠ 0 := trans_hgenSingle_ne_zero A
  have hpt : cappingVecPoint c hc (A (EuclideanSpace.single 0 (1 : ℝ) : Eucl 3)) hA
      = linCommonPt (fun k => (coordPermCLM (coordPerms k)).trans A) c hc
          (finrank_iInf_linSub_trans A) := by
    refine eq_linCommonPt _ c hc _ (by rw [cappingSpaceHomeoProj_cappingVecPoint]) ?_
    intro j
    rw [cappingSpaceHomeoProj_cappingVecPoint]
    exact ⟨_, hA, mem_linSub_trans_hgenSingle A j, rfl⟩
  rw [← hpt] at heq
  have hcls := congrArg (fun p => (cappingSpaceHomeoProj p).2) heq
  rw [cappingSpaceHomeoProj_linPlaneChart, cappingSpaceHomeoProj_cappingVecPoint] at hcls
  obtain ⟨a, ha⟩ := (Projectivization.mk_eq_mk_iff ℝ
    (linBase A k (linVecC z)) (A (EuclideanSpace.single 0 (1 : ℝ) : Eucl 3))
    (phi_linVecC_ne_zero (linBase A k) z) hA).mp hcls
  have h2 : a • (EuclideanSpace.single 0 (1 : ℝ) : Eucl 3)
      = (coordPermCLM (coordPerms k)) (linShear k (linVecC z)) := by
    have h3 := congrArg (fun v : Eucl 3 => A.symm v) ha
    simpa [Units.smul_def, map_smul, linBase_apply, ContinuousLinearEquiv.symm_apply_apply] using h3
  exact linShear_ne_smul_single k hz a h2

/-! ## 6. The boundary line `linBdry` of a linear chart -/

/-- The basis vector `e₀` of `Eucl 3 = ℝ⁴`. -/
abbrev linE0 : Eucl 3 := (EuclideanSpace.single 0 (1 : ℝ) : Eucl 3)

/-- The basis vector `e₁` of `Eucl 3 = ℝ⁴`. -/
abbrev linE1 : Eucl 3 := (EuclideanSpace.single 1 (1 : ℝ) : Eucl 3)

/-- **The boundary line of a linear chart**: the image of the line `span {e₀, e₁}` under `Φ`.  It is
the span of the image of the boundary circle `‖z‖ = 1` of the disk model (`(z, 0) ∈ ℂ²`, `‖z‖ = 1`,
spans `span {e₀, e₁}`).  The two *boundary lines* of two charts are what the incidence criterion
`pairReg_linPlaneCharts_of_incidence` controls: the fold directions of the two disk charts lie on them,
so a common point that is a fold point of both charts is a failure of `PairReg` unless the two
boundary lines meet only in `0`. -/
def linBdry (Φ : Eucl 3 ≃L[ℝ] Eucl 3) : Submodule ℝ (Eucl 3) :=
  (Submodule.span ℝ ({linE0, linE1} : Set (Eucl 3))).map Φ.toLinearEquiv.toLinearMap

/-- The shear moves the boundary line: `S_k (span {e₀, e₁}) = span {e₀, e₁ + α_k e₂}`. -/
lemma linShear_span_eq (k : Fin 3) :
    (Submodule.span ℝ ({linE0, linE1} : Set (Eucl 3))).map (linShear k).toLinearEquiv.toLinearMap
      = Submodule.span ℝ
          ({linE0, linE1 + linAlpha k • linE2} : Set (Eucl 3)) := by
  have h0 : (linShear k).toLinearEquiv.toLinearMap linE0 = linE0 := by
    show linShearFun k linE0 = linE0
    ext i
    fin_cases i <;> simp [linShearFun, linE0, linE1, linE2]
  have h1 : (linShear k).toLinearEquiv.toLinearMap linE1 = linE1 + linAlpha k • linE2 := by
    show linShearFun k linE1 = linE1 + linAlpha k • linE2
    ext i
    fin_cases i <;> simp [linShearFun, linE0, linE1, linE2, PiLp.smul_apply, smul_eq_mul]
  rw [Submodule.map_span]
  rw [show ((linShear k).toLinearEquiv.toLinearMap) '' ({linE0, linE1} : Set (Eucl 3))
      = ({linE0, linE1 + linAlpha k • linE2} : Set (Eucl 3)) from by
    rw [Set.image_pair, h0, h1]]

end

end Work.Drive
