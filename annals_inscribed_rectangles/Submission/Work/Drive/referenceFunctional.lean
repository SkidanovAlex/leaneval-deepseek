import Mathlib
import Submission.Work.Drive.generic_regularization_gen
import Submission.Work.Drive.linearPlaneChart
import Submission.Work.Drive.chartPertData

/-!
# Realising a nonzero functional as the normal functional of a plane chart

The reference factor `(F1)` of `hn2` (`Work.Drive.odd_coreSideCountPt_reference`,
`referenceClassCount.lean`) needs, besides the genericity of the *functional* (the reference plane
`projLine (linSub φ)` in general position with respect to the class loop, delegated as
`Work.Drive.exists_generic_functional`), the realisation of that functional by a *plane chart*: the
factor's plane is presented by `Work.Drive.linPlaneChart φ lam hlam`, whose normal functional is
`Work.Drive.linFun φ v = (φ⁻¹ v) 3`.  This file supplies the realisation:

* **`Work.Drive.exists_linFun_eq`** — every nonzero functional `ℓ` of `Eucl 3 = ℝ⁴` is `linFun φ` for
  some linear equivalence `φ`.  The construction is the shear `S v = v + (ℓ v - v 3) • w` with `w`
  satisfying `w 3 = 1` and `ℓ w ≠ 0`: it is a linear automorphism (with explicit inverse
  `v ↦ v - (ℓ w)⁻¹ (ℓ v - v 3) • w`) whose third coordinate functional is `ℓ`, and one takes
  `φ := S⁻¹`.
-/

namespace Work.Drive

open scoped ContDiff Manifold
open Set

noncomputable section

/-- The third coordinate vector of `Eucl 3 = ℝ⁴`. -/
def e3 : Eucl 3 := WithLp.toLp 2 (![0, 0, 0, (1 : ℝ)] : Fin 4 → ℝ)

@[simp] lemma e3_apply_three : (e3 : Eucl 3) 3 = 1 := by
  simp [e3, WithLp.ofLp_toLp]

/-- **A vector meeting the constraint `w 3 = 1`, `ℓ w ≠ 0`.**  Such a `w` exists for every nonzero
functional `ℓ`: if `ℓ` does not vanish on the affine hyperplane `{w 3 = 1}` take such a `w`, and
otherwise `ℓ` is a multiple of the coordinate functional and `w = e3` works. -/
lemma exists_w (ℓ : Eucl 3 →L[ℝ] ℝ) (hℓ : ℓ ≠ 0) :
    ∃ w : Eucl 3, w 3 = (1 : ℝ) ∧ ℓ w ≠ 0 := by
  obtain ⟨v₀, hv₀⟩ : ∃ v₀ : Eucl 3, ℓ v₀ ≠ 0 := by
    by_contra h
    refine hℓ (ContinuousLinearMap.ext fun v => ?_)
    by_contra hv
    exact h ⟨v, hv⟩
  by_cases hc : v₀ 3 = 0
  · by_cases he : ℓ e3 ≠ 0
    · exact ⟨e3, e3_apply_three, he⟩
    · refine ⟨e3 + v₀, ?_, ?_⟩
      · simp [hc]
      · rw [map_add, not_not.mp he, zero_add]; exact hv₀
  · refine ⟨(v₀ 3)⁻¹ • v₀, ?_, ?_⟩
    · simp [hc]
    · rw [map_smul, smul_eq_mul]
      exact mul_ne_zero (inv_ne_zero hc) hv₀

/-- **Every nonzero functional of `Eucl 3` is the normal functional of a linear plane chart.** -/
theorem exists_linFun_eq (ℓ : Eucl 3 →L[ℝ] ℝ) (hℓ : ℓ ≠ 0) :
    ∃ φ : Eucl 3 ≃L[ℝ] Eucl 3, ∀ v : Eucl 3, linFun φ v = ℓ v := by
  classical
  obtain ⟨w, hw3, hℓw⟩ := exists_w ℓ hℓ
  set μ : Eucl 3 →ₗ[ℝ] ℝ := ℓ.toLinearMap - (cproj (3 : Fin 4)).toLinearMap with hμdef
  set S : Eucl 3 →ₗ[ℝ] Eucl 3 := LinearMap.id + μ.smulRight w with hSdef
  set T : Eucl 3 →ₗ[ℝ] Eucl 3
    := LinearMap.id - (ℓ w)⁻¹ • μ.smulRight w with hTdef
  have hSapp : ∀ v : Eucl 3, S v = v + (ℓ v - v 3) • w := by
    intro v
    rw [hSdef, LinearMap.add_apply, LinearMap.id_apply, LinearMap.smulRight_apply μ w v,
      hμdef, LinearMap.sub_apply, ContinuousLinearMap.coe_coe]
    rfl
  have hTapp : ∀ v : Eucl 3, T v = v - ((ℓ w)⁻¹ * (ℓ v - v 3)) • w := by
    intro v
    rw [hTdef, LinearMap.sub_apply, LinearMap.id_apply, LinearMap.smul_apply,
      LinearMap.smulRight_apply μ w v, hμdef, LinearMap.sub_apply, ContinuousLinearMap.coe_coe,
      smul_smul]
    rfl
  have hS3 : ∀ v : Eucl 3, (S v) 3 = ℓ v := by
    intro v
    rw [hSapp v, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, hw3, mul_one]
    ring
  have hℓS : ∀ v : Eucl 3, ℓ (S v) = ℓ v + (ℓ v - v 3) * ℓ w := by
    intro v
    rw [hSapp v, map_add, map_smul, smul_eq_mul]
  have hT3 : ∀ v : Eucl 3, (T v) 3 = v 3 - (ℓ w)⁻¹ * (ℓ v - v 3) := by
    intro v
    rw [hTapp v, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul, hw3, mul_one]
  have hℓT : ∀ v : Eucl 3, ℓ (T v) = ℓ v - ((ℓ w)⁻¹ * (ℓ v - v 3)) * ℓ w := by
    intro v
    rw [hTapp v, map_sub, map_smul, smul_eq_mul]
  have hST : ∀ v : Eucl 3, S (T v) = v := by
    intro v
    have hscal : ℓ (T v) - (T v) 3 = (ℓ w)⁻¹ * (ℓ v - v 3) := by
      rw [hℓT v, hT3 v]
      field_simp
      ring
    rw [hSapp (T v), hscal, hTapp v]
    module
  have hTS : ∀ v : Eucl 3, T (S v) = v := by
    intro v
    have hscal : (ℓ w)⁻¹ * (ℓ (S v) - (S v) 3) = ℓ v - v 3 := by
      calc (ℓ w)⁻¹ * (ℓ (S v) - (S v) 3)
          = (ℓ w)⁻¹ * ((ℓ v - v 3) * ℓ w) := by rw [hℓS v, hS3 v]; ring
        _ = ℓ v - v 3 := by
              rw [mul_comm (ℓ v - v 3) (ℓ w), ← mul_assoc, inv_mul_cancel₀ hℓw, one_mul]
    rw [hTapp (S v), hscal, hSapp v]
    module
  have hinj : Function.Injective S := fun a b hab => by
    rw [← hTS a, ← hTS b, hab]
  have hsurj : Function.Surjective S := fun v => ⟨T v, hST v⟩
  refine ⟨((LinearEquiv.ofBijective S ⟨hinj, hsurj⟩).toContinuousLinearEquiv).symm, fun v => ?_⟩
  rw [linFun_apply, ContinuousLinearEquiv.symm_symm]
  exact hS3 v

end

end Work.Drive
