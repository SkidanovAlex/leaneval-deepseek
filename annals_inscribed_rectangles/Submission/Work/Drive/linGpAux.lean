import Mathlib
import Submission.Work.Drive.linGpDefs
import Submission.Work.Drive.linPlaneChartNormals
import Submission.Work.Drive.hVNormalForm

/-!
# The general-position clause of the transported linear family: the coordinate dictionary

This module turns the general-position clause of `Work.Drive.rowCD_linTrans_generalPosition_openDense`
into the non-vanishing of the three determinants `Work.Drive.gpDet A k`:

* `mem_span_linE0_linE1_iff`, `linVecC_eq_of_norm_one` — the boundary plane `span {e₀, e₁}` is the
  set of vectors with vanishing last two coordinates, and the image of the unit circle is the unit
  sphere of that plane;
* `gp_iInf_ker_gpFun` — the common kernel of the four functionals `gpFun A k t` is
  `(⨅ j, linSub (Ψ j)) ⊓ ker (coord 2 of (Ψ k)⁻¹)`;
* `gpMat_eq_toMatrix`, `gpLambda_ker`, `gpDet_ne_zero_iff_linIndependent` — `gpDet A k t ≠ 0` is
  exactly the linear independence of the four functionals (through
  `LinearMap.det_eq_zero_iff_ker_ne_bot` and
  `Work.Drive.iInf_ker_eq_bot_iff_linearIndependent`);
* `gp_linPlaneChart_eq_linCommonPt`, `gp_linFun_eq_zero_of_linPlaneChart_eq` — the dictionary between
  the value of the `k`-th linear plane chart and the common point of the three planes.
-/

namespace Work.Drive

open Manifold Set
open scoped Manifold ContDiff Topology

noncomputable section

/-! ## 1. Coordinates on `Eucl 3 = ℝ⁴` and the standard basis -/

/-- The coordinate `i` of `toLp4 w`. -/
lemma toLp4_coord (w : Fin 4 → ℝ) (i : Fin 4) : (toLp4 w).ofLp i = w i := by
  simp [toLp4]

/-- The coordinate `i` of `toLp4.toLinearMap w`. -/
lemma toLp4_coord' (w : Fin 4 → ℝ) (i : Fin 4) : (toLp4.toLinearMap w).ofLp i = w i := by
  simp [toLp4]

/-- The standard orthonormal basis of `Eucl 3 = ℝ⁴`, as a `Basis`. -/
abbrev gpBasis : Module.Basis (Fin 4) ℝ (Eucl 3) := (EuclideanSpace.basisFun (Fin 4) ℝ).toBasis

lemma gpBasis_apply (j : Fin 4) : gpBasis j = gpStdVec j := by
  rw [gpBasis, OrthonormalBasis.coe_toBasis, EuclideanSpace.basisFun_apply, gpStdVec]

lemma gpBasis_repr (v : Eucl 3) (i : Fin 4) : gpBasis.repr v i = v i := by
  rw [gpBasis, OrthonormalBasis.coe_toBasis_repr_apply, EuclideanSpace.basisFun_repr]

/-- **Membership in the boundary plane**: `span {e₀, e₁}` is the set of vectors whose last two
coordinates vanish. -/
lemma mem_span_linE0_linE1_iff (v : Eucl 3) :
    v ∈ Submodule.span ℝ ({linE0, linE1} : Set (Eucl 3)) ↔ v 2 = 0 ∧ v 3 = 0 := by
  constructor
  · intro hv
    have hle : Submodule.span ℝ ({linE0, linE1} : Set (Eucl 3))
        ≤ (coordFun 2).ker ⊓ (coordFun 3).ker := by
      rw [Submodule.span_le]
      intro x hx
      change x ∈ (coordFun 2).ker ⊓ (coordFun 3).ker
      rw [Submodule.mem_inf]
      rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl
      · exact ⟨by simp [coordFun, linE0], by simp [coordFun, linE0]⟩
      · exact ⟨by simp [coordFun, linE1], by simp [coordFun, linE1]⟩
    have h := hle hv
    rw [Submodule.mem_inf, LinearMap.mem_ker, LinearMap.mem_ker, coordFun_apply,
      coordFun_apply] at h
    exact h
  · rintro ⟨h2, h3⟩
    have hv : v = v 0 • linE0 + v 1 • linE1 := by
      ext i
      fin_cases i <;>
        simp [linE0, linE1, h2, h3, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
    rw [hv]
    exact Submodule.add_mem _
      (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
      (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))

/-- **The image of the unit circle is the unit sphere of the boundary plane.** -/
lemma linVecC_eq_of_norm_one {z : ℂ} (hz : ‖z‖ = 1) :
    linVecC z = z.re • linE0 + z.im • linE1 := by
  ext i
  fin_cases i <;>
    simp [linE0, linE1, linVecC_apply_zero', linVecC_apply_one', linVecC_apply_two,
      linVecC_apply_three, hz, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]

/-! ## 2. The common kernel of the four functionals -/

/-- **The common kernel of the four functionals of the `k`-th quadruple.** -/
lemma gp_iInf_ker_gpFun (A : Eucl 3 ≃L[ℝ] Eucl 3) (k : Fin 3)
    (t : EuclideanSpace ℝ (Fin 12)) :
    (⨅ i : Fin 4, (gpFun A k t i).ker)
      = (⨅ j : Fin 3, linSub (gpPsi A j t)) ⊓ (gpCoordPull 2 (gpPsi A k t)).ker := by
  ext v
  simp only [Submodule.mem_iInf, Submodule.mem_inf, LinearMap.mem_ker, ← ker_linFun]
  constructor
  · intro hv
    refine ⟨?_, hv 3⟩
    intro j
    fin_cases j
    · exact hv 0
    · exact hv 1
    · exact hv 2
  · rintro ⟨hV, hM⟩ i
    fin_cases i
    · exact hV 0
    · exact hV 1
    · exact hV 2
    · exact hM

/-! ## 3. The determinant as a linear-map determinant -/

/-- **The matrix of the four functionals is the matrix of `gpLambda`** in the standard basis. -/
lemma gpMat_eq_toMatrix (A : Eucl 3 ≃L[ℝ] Eucl 3) (k : Fin 3)
    (t : EuclideanSpace ℝ (Fin 12)) :
    gpMat A k t = LinearMap.toMatrix gpBasis gpBasis (gpLambda A k t) := by
  ext i j
  simp only [gpMat_apply, LinearMap.toMatrix_apply, gpBasis_repr, gpBasis_apply, gpLambda,
    LinearMap.comp_apply, toLp4_coord, toLp4_coord', LinearMap.pi_apply]

/-- The kernel of `toLp4` is trivial. -/
lemma gp_ker_toLp4 : toLp4.toLinearMap.ker = ⊥ := by
  rw [LinearMap.ker_eq_bot']
  intro w hw
  ext i
  have h := congrArg (fun x : Eucl 3 => x i) hw
  simpa [toLp4_coord, toLp4_coord'] using h

/-- **The kernel of `gpLambda` is the common kernel of the four functionals.** -/
lemma gpLambda_ker (A : Eucl 3 ≃L[ℝ] Eucl 3) (k : Fin 3)
    (t : EuclideanSpace ℝ (Fin 12)) :
    (gpLambda A k t).ker = ⨅ i : Fin 4, (gpFun A k t i).ker := by
  rw [gpLambda, LinearMap.ker_comp, gp_ker_toLp4]
  show (LinearMap.pi (gpFun A k t)).ker = ⨅ i : Fin 4, (gpFun A k t i).ker
  rw [LinearMap.ker_pi]

/-- The cardinality of the index type of `gpFun`. -/
lemma gpFun_card : Fintype.card (Fin 4) = Module.finrank ℝ (Eucl 3) := by
  simp [finrank_euclideanSpace]

/-- **The general-position determinant vanishes exactly when the four functionals are dependent.** -/
theorem gpDet_ne_zero_iff_linIndependent (A : Eucl 3 ≃L[ℝ] Eucl 3) (k : Fin 3)
    (t : EuclideanSpace ℝ (Fin 12)) :
    gpDet A k t ≠ 0 ↔ LinearIndependent ℝ (gpFun A k t) := by
  have hdet : gpDet A k t = (LinearMap.det (gpLambda A k t)) := by
    rw [gpDet, gpMat_eq_toMatrix]
    exact LinearMap.det_toMatrix gpBasis (gpLambda A k t)
  rw [hdet, ne_eq, not_congr (LinearMap.det_eq_zero_iff_ker_ne_bot (f := gpLambda A k t)),
    not_not, gpLambda_ker]
  exact iInf_ker_eq_bot_iff_linearIndependent (gpFun A k t) gpFun_card

/-! ## 4. The dictionary between the chart value and the common point -/

/-- If the `k`-th chart value lies on all three planes, it **is** the common point. -/
lemma gp_linPlaneChart_eq_linCommonPt (Φ : Fin 3 → Eucl 3 ≃L[ℝ] Eucl 3) (cl : ℝ)
    (hcl : 0 < cl) (hrank : Module.finrank ℝ ↥(⨅ k : Fin 3, linSub (Φ k)) = 1) {k : Fin 3}
    {z : ℂ} (_hz : ‖z‖ = 1) (hvanish : ∀ j : Fin 3, linFun (Φ j) (Φ k (linVecC z)) = 0) :
    linPlaneChart (Φ k) cl hcl z = linCommonPt Φ cl hcl hrank := by
  refine eq_linCommonPt Φ cl hcl hrank (level_linPlaneChart (Φ k) cl hcl z) (fun j => ?_)
  rw [cappingSpaceHomeoProj_linPlaneChart (Φ k) cl hcl z]
  refine ⟨Φ k (linVecC z), phi_linVecC_ne_zero (Φ k) z, ?_, rfl⟩
  rw [← ker_linFun (Φ j)]
  exact LinearMap.mem_ker.mpr (hvanish j)

/-- Conversely, if the `k`-th chart value is the common point, then all three normal functionals
vanish on `Φ k (linVecC z)`. -/
lemma gp_linFun_eq_zero_of_linPlaneChart_eq (Φ : Fin 3 → Eucl 3 ≃L[ℝ] Eucl 3) (cl : ℝ)
    (hcl : 0 < cl) (hrank : Module.finrank ℝ ↥(⨅ k : Fin 3, linSub (Φ k)) = 1) {k : Fin 3}
    {z : ℂ} (_hz : ‖z‖ = 1) (heq : linPlaneChart (Φ k) cl hcl z = linCommonPt Φ cl hcl hrank)
    (j : Fin 3) : linFun (Φ j) (Φ k (linVecC z)) = 0 := by
  have hmem : (cappingSpaceHomeoProj (linPlaneChart (Φ k) cl hcl z)).2 ∈ projLine (linSub (Φ j)) := by
    rw [heq]
    exact mem_projLine_linCommonPt Φ cl hcl hrank j
  rw [cappingSpaceHomeoProj_linPlaneChart (Φ k) cl hcl z] at hmem
  have hmk : Φ k (linVecC z) ∈ linSub (Φ j) := by
    obtain ⟨v, hv, hvU, heq2⟩ := hmem
    obtain ⟨a, ha⟩ := (Projectivization.mk_eq_mk_iff ℝ (Φ k (linVecC z)) v
      (phi_linVecC_ne_zero (Φ k) z) hv).mp heq2
    rw [← ha]
    exact Submodule.smul_mem _ (a : ℝ) hvU
  rw [← ker_linFun (Φ j)] at hmk
  exact LinearMap.mem_ker.mp hmk

end

end Work.Drive
