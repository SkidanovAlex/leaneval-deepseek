import Mathlib

namespace Work.WilE9G.Sard

/-- **Derivative of the "replace one coordinate by a function of the point" map.**  If `h` has
Fr\'echet derivative `a` at `x₀`, then `z ↦ Function.update z i (h z)` has derivative
`1 + (a - proj i).smulRight (Pi.single i 1)` at `x₀`; as a formula, its linear part sends `w` to
`Function.update w i (a w)`. -/
theorem hasFDerivAt_update {n : ℕ} {h : (Fin n → ℝ) → ℝ} {x₀ : Fin n → ℝ}
    {a : (Fin n → ℝ) →L[ℝ] ℝ} (i : Fin n) (hh : HasFDerivAt h a x₀) :
    HasFDerivAt (fun z => Function.update z i (h z))
      ((1 : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ)) +
        (a - ContinuousLinearMap.proj i).smulRight (Pi.single i 1)) x₀ := by
  -- The map `z ↦ Function.update z i (h z)` equals `z ↦ z + (h z - z i) • eᵢ`.
  have hproj : HasFDerivAt (fun z : Fin n → ℝ => z i) (ContinuousLinearMap.proj i) x₀ :=
    ContinuousLinearMap.hasFDerivAt (ContinuousLinearMap.proj i : (Fin n → ℝ) →L[ℝ] ℝ)
  have hsub : HasFDerivAt (fun z : Fin n → ℝ => h z - z i)
      (a - ContinuousLinearMap.proj i) x₀ := hh.sub hproj
  have hsl : HasFDerivAt (fun z : Fin n → ℝ => (h z - z i) • (Pi.single i (1 : ℝ)))
      ((a - ContinuousLinearMap.proj i).smulRight (Pi.single i 1)) x₀ := hsub.smul_const _
  have hfun : (fun z : Fin n → ℝ => Function.update z i (h z))
      = id + (fun z : Fin n → ℝ => (h z - z i) • (Pi.single i (1 : ℝ))) := by
    funext z
    show Function.update z i (h z) = id z + (h z - z i) • (Pi.single i (1 : ℝ))
    ext j
    rw [Function.update_apply, Pi.add_apply, id_eq, Pi.smul_apply, Pi.single_apply]
    by_cases hj : j = i
    · subst hj; simp
    · simp [hj]
  rw [hfun]
  exact (hasFDerivAt_id x₀).add hsl

end Work.WilE9G.Sard
