import Mathlib
import Submission.Work.RPB.B5.LagData

/-!
# `rho_zero_surj`: the middle reparametrisation at `τ = 0` hits every `v ∈ (0, π²/4]`

The chord parameter `rho 0 · t` of the middle region `-√2 ≤ x ≤ 0` runs continuously from
`rho 0 (-√2) t = 0` (the blown-up diagonal, `σ = 0`) to `rho 0 0 t = π²/4` (the boundary of the
`ρ = r²`-chart at radius `r = π/2`).  Hence by the intermediate value theorem on the *closed*
interval `[-√2, 0]` it is surjective onto `[0, π²/4]`; since the value `π²/4` is attained at the
right endpoint `x = 0`, every `v ∈ (0, π²/4]` is attained at some `x ∈ (-√2, 0]`.

Only two of the `LagData` fields are used: continuity of `rho` (`hrhosm`) and the two endpoint
values (`hrhom`, `hrho0`).  In particular no monotonicity of `rho` is needed.
-/

namespace Work.RPB.B5

theorem rho_zero_surj (CI : Work.RPV.CurveIsotopy) (a : ℝ → ℝ → ℝ → ℝ)
    (D : Work.RPB.B5.LagData CI a) (t : ℝ) :
    ∀ v : ℝ, 0 < v → v ≤ Real.pi ^ 2 / 4 →
      ∃ x : ℝ, -Real.sqrt 2 < x ∧ x ≤ 0 ∧ D.rho 0 x t = v := by
  intro v hv0 hvle
  -- `0 ∈ Icc 0 1`, so the two endpoint normalisations of `LagData` apply.
  have hmem : (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := ⟨le_refl 0, zero_le_one⟩
  -- `rho 0 · t` is continuous (it is a slice of the `C⁸` function `rho`).
  have hcont : Continuous (fun x : ℝ => D.rho 0 x t) :=
    D.hrhosm.continuous.comp (continuous_const.prodMk (continuous_id.prodMk continuous_const))
  rcases eq_or_lt_of_le hvle with hv | hv
  · -- the boundary value `v = π²/4` is attained at `x = 0`.
    exact ⟨0, by have := Real.sqrt_pos.2 (show (0 : ℝ) < 2 by norm_num); linarith, le_refl 0,
      (D.hrho0 0 hmem t).trans hv.symm⟩
  · -- otherwise `0 < v < π²/4` and the IVT on `(-√2, 0]` applies.
    have hle : -Real.sqrt 2 ≤ 0 := by
      have := Real.sqrt_nonneg 2; linarith
    have hmem2 : v ∈ Set.Ioc ((fun x : ℝ => D.rho 0 x t) (-Real.sqrt 2))
        ((fun x : ℝ => D.rho 0 x t) 0) := by
      change v ∈ Set.Ioc (D.rho 0 (-Real.sqrt 2) t) (D.rho 0 0 t)
      rw [D.hrhom 0 hmem t, D.hrho0 0 hmem t]
      exact ⟨hv0, hv.le⟩
    obtain ⟨c, hc, hfc⟩ := intermediate_value_Ioc hle hcont.continuousOn hmem2
    exact ⟨c, hc.1, hc.2, hfc⟩

end Work.RPB.B5
