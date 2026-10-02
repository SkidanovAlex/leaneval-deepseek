import Mathlib
import Submission.Work.PTGeometric.RieszProj.Defs

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.PTGeometric

/-- For an orthogonal projection `Q` of rank `k` (i.e. `Q ∈ Gr n k`, the set of self-adjoint
idempotents of trace `k`), there is a linear map `ℓ : ℝⁿ → ℝᵏ` injective on the plane
`im Q = {z | Q z = z}`. -/
theorem existsCoordInjOnGr {n k : ℕ} (Q : Amb n →L[ℝ] Amb n) (hQ : Q ∈ Gr n k) :
    ∃ ℓ : Amb n →L[ℝ] Amb k, ∀ z : Amb n, Q z = z → ℓ z = 0 → z = 0 := by
  -- `Q` is idempotent, as an operator and as a linear map
  have hQidem : Q * Q = Q := hQ.2.1
  have hcomp : ∀ x : Amb n, Q (Q x) = Q x := by
    intro x
    have h : (Q * Q : Amb n →L[ℝ] Amb n) x = Q x := by rw [hQidem]
    simpa using h
  -- the plane `im Q` has dimension the trace of `Q`, namely `k`
  have hQfin : Module.finrank ℝ (LinearMap.range (Q : Amb n →ₗ[ℝ] Amb n)) = k := by
    have hQidem_lin : (Q : Amb n →ₗ[ℝ] Amb n) * (Q : Amb n →ₗ[ℝ] Amb n)
        = (Q : Amb n →ₗ[ℝ] Amb n) := by
      refine LinearMap.ext fun y => ?_
      rw [Module.End.mul_eq_comp, LinearMap.comp_apply]
      exact hcomp y
    have hproj : LinearMap.IsProj (LinearMap.range (Q : Amb n →ₗ[ℝ] Amb n))
        (Q : Amb n →ₗ[ℝ] Amb n) :=
      (LinearMap.isProj_range_iff_isIdempotentElem (Q : Amb n →ₗ[ℝ] Amb n)).mpr hQidem_lin
    have h1 : LinearMap.trace ℝ (Amb n) (Q : Amb n →ₗ[ℝ] Amb n)
        = (Module.finrank ℝ (LinearMap.range (Q : Amb n →ₗ[ℝ] Amb n)) : ℝ) := hproj.trace
    have h2 : LinearMap.trace ℝ (Amb n) (Q : Amb n →ₗ[ℝ] Amb n) = (k : ℝ) := hQ.2.2
    have h3 : (Module.finrank ℝ (LinearMap.range (Q : Amb n →ₗ[ℝ] Amb n)) : ℝ) = (k : ℝ) := by
      rw [← h1, h2]
    exact Nat.cast_injective h3
  -- the plane, as a submodule
  set V : Submodule ℝ (Amb n) := LinearMap.range (Q : Amb n →ₗ[ℝ] Amb n) with hV
  have hVfin : Module.finrank ℝ V = k := hQfin
  -- a linear isomorphism `V ≅ ℝᵏ` (both are `k`-dimensional) and its underlying linear map
  let ee : V ≃ₗ[ℝ] Amb k := LinearEquiv.ofFinrankEq V (Amb k) (by
    rw [hVfin, finrank_euclideanSpace]; simp)
  let E : V →ₗ[ℝ] Amb k := ee.toLinearMap
  have hEinj : Function.Injective E := by
    rw [show E = ee.toLinearMap from rfl]
    exact ee.injective
  -- `ℓ` is `E` composed with `Q`, which lands in the plane `V`; it is continuous as `ℝⁿ` is finite
  -- dimensional
  let p : Amb n →ₗ[ℝ] V := (Q : Amb n →ₗ[ℝ] Amb n).codRestrict V
    (fun x => by rw [hV]; exact LinearMap.mem_range_self _ x)
  let g : Amb n →ₗ[ℝ] Amb k := E.comp p
  let ℓ : Amb n →L[ℝ] Amb k := ⟨g, g.continuous_of_finiteDimensional⟩
  have hval : ∀ z : Amb n, ℓ z = g z := fun z => rfl
  have hg : ∀ z : Amb n, g z = E (p z) := fun z => rfl
  refine ⟨ℓ, ?_⟩
  intro z hz hℓ
  have hzV : z ∈ V := by
    rw [hV, LinearMap.mem_range]
    exact ⟨z, hz⟩
  have hpz : p z = (⟨z, hzV⟩ : V) := by
    refine Subtype.ext ?_
    rw [LinearMap.codRestrict_apply V (Q : Amb n →ₗ[ℝ] Amb n) z]
    exact hz
  -- `ℓ z = 0` forces `E (Q z) = 0`, and `E` is injective
  have h3 : E (⟨z, hzV⟩ : V) = 0 := by
    have hgz : g z = 0 := by rw [← hval z]; exact hℓ
    rw [hg z, hpz] at hgz
    exact hgz
  have h4 : (⟨z, hzV⟩ : V) = 0 := hEinj (by rw [h3, map_zero])
  simpa using congrArg Subtype.val h4

end Work.PTGeometric
