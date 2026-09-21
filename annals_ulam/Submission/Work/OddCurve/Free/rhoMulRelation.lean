import Mathlib

open Set Filter
open scoped Topology

namespace Work.OddCurve.Free

/-- Differentiating the relation `ρ v * √(1 - v²) = f (ρ v * v)` at `u` and eliminating
the square root yields a purely algebraic relation between `ρ u`, `ρ' u`, `f (ρ u * u)`
and `f' (ρ u * u)`. -/
theorem rhoMulRelation {ρ f : ℝ → ℝ} {u : ℝ}
    (hρ : ContDiffOn ℝ 2 ρ (Set.Ioo (-1 : ℝ) 1))
    (hf : ContDiffOn ℝ 2 f (Set.Ioo (-1 : ℝ) 1))
    (hw : ∀ v ∈ Set.Ioo (-1 : ℝ) 1, ρ v * v ∈ Set.Ioo (-1 : ℝ) 1)
    (heq : ∀ v ∈ Set.Ioo (-1 : ℝ) 1, ρ v * Real.sqrt (1 - v ^ 2) = f (ρ v * v))
    (hu : u ∈ Set.Ioo (-1 : ℝ) 1) :
    deriv ρ u * (f (ρ u * u) * (f (ρ u * u) - (ρ u * u) * deriv f (ρ u * u))) =
      (ρ u) ^ 2 * (ρ u * u + f (ρ u * u) * deriv f (ρ u * u)) := by
  obtain ⟨hu1, hu2⟩ := hu
  have hmem : Set.Ioo (-1 : ℝ) 1 ∈ 𝓝 u := Ioo_mem_nhds hu1 hu2
  have hwmem : ρ u * u ∈ Set.Ioo (-1 : ℝ) 1 := hw u ⟨hu1, hu2⟩
  have hwmem' : Set.Ioo (-1 : ℝ) 1 ∈ 𝓝 (ρ u * u) := Ioo_mem_nhds hwmem.1 hwmem.2
  -- differentiability of `ρ` and `f` at the relevant points
  have hρd : HasDerivAt ρ (deriv ρ u) u :=
    ((hρ.contDiffAt hmem).differentiableAt (by norm_num)).hasDerivAt
  have hfd : HasDerivAt f (deriv f (ρ u * u)) (ρ u * u) :=
    ((hf.contDiffAt hwmem').differentiableAt (by norm_num)).hasDerivAt
  have hu2pos : (0 : ℝ) < 1 - u ^ 2 := by nlinarith
  have hsne : Real.sqrt (1 - u ^ 2) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hu2pos)
  have hgu : (1 : ℝ) - u ^ 2 ≠ 0 := ne_of_gt hu2pos
  -- derivative of `v ↦ 1 - v ^ 2`
  have hg : HasDerivAt (fun v : ℝ => 1 - v ^ 2) (-(2 * u)) u := by
    have h1 : HasDerivAt (fun v : ℝ => v ^ 2) (2 * u) u := by
      have := hasDerivAt_pow 2 u
      simpa using this
    simpa using h1.const_sub (1 : ℝ)
  -- derivative of `v ↦ √(1 - v ^ 2)`
  have hb : HasDerivAt (fun v : ℝ => Real.sqrt (1 - v ^ 2))
      ((-(2 * u)) / (2 * Real.sqrt (1 - u ^ 2))) u := hg.sqrt hgu
  -- derivative of the left-hand side `v ↦ ρ v * √(1 - v ^ 2)`
  have hA : HasDerivAt (fun v : ℝ => ρ v * Real.sqrt (1 - v ^ 2))
      (deriv ρ u * Real.sqrt (1 - u ^ 2) +
        ρ u * ((-(2 * u)) / (2 * Real.sqrt (1 - u ^ 2)))) u := by
    have h := hρd.mul hb
    convert h using 1 <;> try rfl
  -- derivative of `v ↦ ρ v * v`
  have hg2 : HasDerivAt (fun v : ℝ => ρ v * v) (deriv ρ u * u + ρ u) u := by
    have h := hρd.mul (hasDerivAt_id u)
    convert h using 1 <;> try rfl
    simp
  -- derivative of the right-hand side `v ↦ f (ρ v * v)`
  have hB : HasDerivAt (fun v : ℝ => f (ρ v * v))
      (deriv f (ρ u * u) * (deriv ρ u * u + ρ u)) u := by
    have h := HasDerivAt.comp (h := fun v : ℝ => ρ v * v) u hfd hg2
    simpa [Function.comp_def] using h
  -- the two sides agree in a neighbourhood of `u`
  have hev : (fun v : ℝ => ρ v * Real.sqrt (1 - v ^ 2)) =ᶠ[𝓝 u]
      (fun v : ℝ => f (ρ v * v)) := by
    filter_upwards [hmem] with v hv
    exact heq v hv
  have hA' : HasDerivAt (fun v : ℝ => f (ρ v * v))
      (deriv ρ u * Real.sqrt (1 - u ^ 2) +
        ρ u * ((-(2 * u)) / (2 * Real.sqrt (1 - u ^ 2)))) u :=
    hA.congr_of_eventuallyEq hev.symm
  -- hence the derivatives coincide at `u`
  have hder : deriv ρ u * Real.sqrt (1 - u ^ 2) +
        ρ u * ((-(2 * u)) / (2 * Real.sqrt (1 - u ^ 2)))
      = deriv f (ρ u * u) * (deriv ρ u * u + ρ u) := hA'.unique hB
  -- and `f (ρ u * u) = ρ u * √(1 - u ^ 2)`
  have hFs : f (ρ u * u) = ρ u * Real.sqrt (1 - u ^ 2) := (heq u ⟨hu1, hu2⟩).symm
  rw [hFs]
  have hderm : deriv ρ u * (Real.sqrt (1 - u ^ 2)) ^ 2 - ρ u * u
      = deriv f (ρ u * u) * (deriv ρ u * u + ρ u) * Real.sqrt (1 - u ^ 2) := by
    rw [← hder]
    field_simp
    ring
  linear_combination (ρ u) ^ 2 * hderm

end Work.OddCurve.Free
