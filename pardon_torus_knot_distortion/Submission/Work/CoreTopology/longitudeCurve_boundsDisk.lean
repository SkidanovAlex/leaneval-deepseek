import Mathlib
import Submission.Work.CoreTopology.Disk

namespace Work.CoreTopology

open LeanEval.KnotTheory.PardonDistortion
open Set

/-- The embedded disc bounding the longitude circle: the closed northern hemisphere
of the sphere of radius `3`.  A point `z` of the closed unit disc of `ℂ` is sent to
`3 * (z.re, z.im, √(1 - ‖z‖²))`.  (Auxiliary map used to prove
`longitudeCurve_boundsDisk`.) -/
noncomputable def northDisc : C(Metric.closedBall (0 : ℂ) 1, R3) where
  toFun z := WithLp.toLp 2 (fun i : Fin 3 =>
    if i.val = 0 then 3 * (z : ℂ).re
    else if i.val = 1 then 3 * (z : ℂ).im
    else 3 * Real.sqrt (1 - ‖(z : ℂ)‖ ^ 2))
  continuous_toFun := by
    apply (PiLp.continuous_toLp (p := 2) (β := fun _ : Fin 3 => ℝ)).comp
    apply continuous_pi
    intro i
    fin_cases i <;> simp <;> fun_prop

theorem northDisc_injective : Function.Injective northDisc := by
  intro z w hzw
  have h0 : (z : ℂ).re = (w : ℂ).re := by
    have hh := congrArg (fun v : R3 => v 0) hzw
    simp [northDisc] at hh
    linarith
  have h1 : (z : ℂ).im = (w : ℂ).im := by
    have hh := congrArg (fun v : R3 => v 1) hzw
    simp [northDisc] at hh
    linarith
  exact Subtype.ext (Complex.ext h0 h1)

theorem northDisc_circle (θ : ℝ) :
    northDisc (circlePoint θ) = longitudeCurve standard 0 θ := by
  ext i
  simp only [northDisc, longitudeCurve_apply, standard_psi, Work.Core.torusMap]
  fin_cases i <;> norm_num

theorem northDisc_not_mem_carrier (z : Metric.closedBall (0 : ℂ) 1)
    (hz : ‖(z : ℂ)‖ < 1) : northDisc z ∉ standard.carrier := by
  intro hmem
  rw [standard_carrier, Set.mem_range] at hmem
  obtain ⟨⟨θ, φ⟩, hp⟩ := hmem
  have e0 : (2 + Real.cos φ) * Real.cos θ = 3 * (z : ℂ).re := by
    have hh := congrArg (fun v : R3 => v 0) hp
    simpa [northDisc, Work.Core.torusMap] using hh
  have e1 : (2 + Real.cos φ) * Real.sin θ = 3 * (z : ℂ).im := by
    have hh := congrArg (fun v : R3 => v 1) hp
    simpa [northDisc, Work.Core.torusMap] using hh
  have e2 : Real.sin φ = 3 * Real.sqrt (1 - ‖(z : ℂ)‖ ^ 2) := by
    have hh := congrArg (fun v : R3 => v 2) hp
    simpa [northDisc, Work.Core.torusMap] using hh
  have hnorm : 9 * ‖(z : ℂ)‖ ^ 2 = (2 + Real.cos φ) ^ 2 := by
    have key : (3 * (z : ℂ).re) ^ 2 + (3 * (z : ℂ).im) ^ 2 = (2 + Real.cos φ) ^ 2 := by
      rw [← e0, ← e1]
      nlinarith [Real.cos_sq_add_sin_sq θ]
    have key2 : (3 * (z : ℂ).re) ^ 2 + (3 * (z : ℂ).im) ^ 2 = 9 * ‖(z : ℂ)‖ ^ 2 := by
      rw [Complex.sq_norm, Complex.normSq_apply]; ring
    linarith
  have hx : 0 ≤ 1 - ‖(z : ℂ)‖ ^ 2 := by
    have hle : ‖(z : ℂ)‖ ^ 2 ≤ 1 := pow_le_one₀ (norm_nonneg _) (le_of_lt hz)
    linarith
  have hsq : Real.sin φ ^ 2 = 9 * (1 - ‖(z : ℂ)‖ ^ 2) := by
    have h := congrArg (fun x : ℝ => x ^ 2) e2
    rw [mul_pow, Real.sq_sqrt hx] at h
    nlinarith [h]
  have hmain : Real.sin φ ^ 2 = 9 - (2 + Real.cos φ) ^ 2 := by
    rw [hsq]; linarith
  have hcos : Real.cos φ = 1 := by
    nlinarith [Real.sin_sq φ, hmain]
  have hlt : ‖(z : ℂ)‖ ^ 2 < 1 := pow_lt_one₀ (norm_nonneg _) hz (by norm_num)
  have hnorm1 : ‖(z : ℂ)‖ ^ 2 = 1 := by
    rw [hcos] at hnorm; nlinarith
  linarith

/-- The longitude circle `{φ = 0}` of the standard torus of revolution (the circle of radius `3` in the plane `z = 0`) is the boundary of an embedded disc outside the torus: for `z` in the closed unit disc of `ℂ`, put `e z = 3 * (z.re, z.im, Real.sqrt (1 - ‖z‖^2))`, whose image is the closed northern hemisphere of the sphere of radius `3`. Then `e` is injective, maps the unit circle `θ' ↦ exp(iθ')` to `longitudeCurve standard 0`, and no point of the open unit disc maps into the torus surface (whose points of norm `3` all have third coordinate `0`). Hence the longitude circle bounds a disc in the complement of `F`. -/
theorem longitudeCurve_boundsDisk :
    BoundsDiskInComplement standard (longitudeCurve standard 0) :=
  ⟨northDisc, northDisc_injective, northDisc_circle, northDisc_not_mem_carrier⟩

end Work.CoreTopology
