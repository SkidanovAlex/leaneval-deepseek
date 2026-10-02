import Mathlib

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.PTGeometric

/-- **Any nonzero linear functional on `ℝⁿ` is a coordinate after a linear change of variables.**
For `f : ℝⁿ →L[ℝ] ℝ` with `f ≠ 0` there is a continuous linear automorphism `T` of `ℝⁿ` whose
`0`-th coordinate functional is `f`, i.e. `(T z) 0 = f z` for all `z`.

Explicitly, one picks a vector `u` with `u 0 = 1` and `f u ≠ 0` (possible since `f ≠ 0`) and sets
`T z = z + (f z - z 0) • u`; then `T = 1 + g ⊗ u` with `g = f - e₀^*`, `g u = f u - 1`, so `T` is
invertible with inverse `1 - (1 + g u)⁻¹ • (g ⊗ u)`, and `(T z) 0 = z 0 + (f z - z 0) = f z`. -/
theorem linearCoordEquiv {n : ℕ} [NeZero n] (f : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) (hf : f ≠ 0) :
    ∃ T : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n), ∀ z, (T z) 0 = f z := by
  -- a vector on which `f` does not vanish
  obtain ⟨v, hv⟩ : ∃ v : EuclideanSpace ℝ (Fin n), f v ≠ 0 := by
    by_contra h
    push Not at h
    exact hf (ContinuousLinearMap.ext fun x => by simp [h x])
  -- the first standard basis vector `e₀` and an auxiliary `h = v - (v 0) • e₀` with `h 0 = 0`
  let e₀ : EuclideanSpace ℝ (Fin n) := EuclideanSpace.single 0 1
  let w : EuclideanSpace ℝ (Fin n) := v - (v 0) • e₀
  have hw0 : w 0 = 0 := by simp [w, e₀]
  -- `u := e₀ + s • w` has `u 0 = 1` and `f u ≠ 0`
  let s : ℝ := if f e₀ = 0 then 1 else 0
  let u : EuclideanSpace ℝ (Fin n) := e₀ + s • w
  have hu0 : u 0 = 1 := by
    have h : u 0 = e₀ 0 + s * (w 0) := by simp [u, smul_eq_mul]
    rw [h, hw0, mul_zero, add_zero]
    simp [e₀]
  have hfu_eq : f u = f e₀ + s * f w := by simp [u, map_add, map_smul, smul_eq_mul]
  have hfw : f w = f v - (v 0) * f e₀ := by simp [w, map_sub, map_smul, smul_eq_mul]
  have hfu : f u ≠ 0 := by
    rw [hfu_eq]
    by_cases hc : f e₀ = 0
    · have hs : s = 1 := by simp [s, hc]
      rw [hs, one_mul, hfw, hc, mul_zero, sub_zero, zero_add]
      exact hv
    · have hs : s = 0 := by simp [s, hc]
      rw [hs, zero_mul, add_zero]
      exact hc
  -- the coordinate functional `z ↦ z 0` and `g := f - z ↦ z 0`
  let coordF : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ := PiLp.proj 2 (fun _ : Fin n => ℝ) 0
  have hcoord : ∀ z : EuclideanSpace ℝ (Fin n), coordF z = z 0 := fun z => rfl
  let g : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ := f - coordF
  have hgu : g u = f u - 1 := by simp [g, hcoord u, hu0]
  -- `T := 1 + g ⊗ u` and its inverse `S := 1 - (1 + g u)⁻¹ • (g ⊗ u)`
  let c : ℝ := (1 + g u)⁻¹
  have hden : 1 + g u ≠ 0 := by
    have h1 : (1:ℝ) + g u = f u := by rw [hgu]; ring
    rw [h1]; exact hfu
  have hc : c * (1 + g u) = 1 := by
    rw [show c = (1 + g u)⁻¹ from rfl]
    exact inv_mul_cancel₀ hden
  let T : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) := 1 + g.smulRight u
  let S : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) := 1 - (c • g).smulRight u
  have hT : ∀ z : EuclideanSpace ℝ (Fin n), T z = z + g z • u := by
    intro z; simp [T, ContinuousLinearMap.smulRight_apply]
  have hS : ∀ y : EuclideanSpace ℝ (Fin n), S y = y - (c * g y) • u := by
    intro y; simp [S, ContinuousLinearMap.smulRight_apply, smul_eq_mul]
  -- `T` and `S` are mutually inverse
  have hST : ∀ z : EuclideanSpace ℝ (Fin n), S (T z) = z := by
    intro z
    rw [hT z, hS]
    have h3 : g (z + g z • u) = g z + g z * g u := by simp [map_add, map_smul, smul_eq_mul]
    rw [h3]
    have hcoef : g z - c * (g z + g z * g u) = 0 := by
      have hcz : c * (g z + g z * g u) = g z := by
        rw [show c * (g z + g z * g u) = g z * (c * (1 + g u)) from by ring, hc, mul_one]
      rw [hcz, sub_self]
    rw [add_sub_assoc, ← sub_smul, hcoef, zero_smul, add_zero]
  have hTS : ∀ y : EuclideanSpace ℝ (Fin n), T (S y) = y := by
    intro y
    rw [hS y, hT]
    have h3 : g (y - (c * g y) • u) = g y - (c * g y) * g u := by
      simp [map_sub, map_smul, smul_eq_mul]
    rw [h3]
    have hcoef : g y - (c * g y) * g u - c * g y = 0 := by
      have hcz : (c * g y) * g u + c * g y = g y := by
        rw [show (c * g y) * g u + c * g y = g y * (c * (1 + g u)) from by ring, hc, mul_one]
      linarith
    rw [sub_add_eq_add_sub, add_sub_assoc, ← sub_smul, hcoef, zero_smul, add_zero]
  refine ⟨ContinuousLinearEquiv.equivOfInverse T S hST hTS, ?_⟩
  intro z
  rw [ContinuousLinearEquiv.equivOfInverse_apply, hT z]
  have hcomp : (z + g z • u) 0 = z 0 + g z * (u 0) := by simp [smul_eq_mul]
  rw [hcomp, hu0, mul_one]
  have hgz : g z = f z - z 0 := by simp [g, hcoord z]
  rw [hgz]
  ring

end Work.PTGeometric
