import Mathlib
import Submission.Work.WilE9.Defs
import Submission.Work.WilE9.Psi.hasDerivAt_psi

namespace Work.WilE9.Psi

/-- The directional derivative of the coordinatewise `psi`: the `i`-th coordinate of the
`i`-direction is `psig (x i) ^ 3`, the others are `0`. -/
theorem fderiv_psiV {n : ℕ} (x : Fin n → ℝ) (i : Fin n) :
    fderiv ℝ WilkiesDesign.E.psiV x (Pi.single i (1 : ℝ))
      = Pi.single i (Work.WilE9.psig (x i) ^ 3) := by
  -- The `j`-th coordinate of `psiV` is `psi ∘ (coordinates j)`, with derivative
  -- `(psig (x j))^3 • proj j`.
  have hpi : ∀ j : Fin n, HasFDerivAt (fun y : Fin n → ℝ => WilkiesDesign.E.psi (y j))
      ((Work.WilE9.psig (x j) ^ 3) • (ContinuousLinearMap.proj j : (Fin n → ℝ) →L[ℝ] ℝ)) x := by
    intro j
    have h1 : HasFDerivAt (fun y : Fin n → ℝ => y j) (ContinuousLinearMap.proj j) x :=
      hasFDerivAt_apply (𝕜 := ℝ) (F' := fun _ : Fin n => ℝ) j x
    have h2 : HasFDerivAt WilkiesDesign.E.psi
        (ContinuousLinearMap.toSpanSingleton ℝ (Work.WilE9.psig (x j) ^ 3)) (x j) :=
      (Work.WilE9.Psi.hasDerivAt_psi (x j)).hasFDerivAt
    have h3 := h2.comp x h1
    convert h3 using 1
    · ext v; simp
    · ext v; simp [ContinuousLinearMap.toSpanSingleton, mul_comm]
  -- Assemble the coordinatewise derivative into a single `HasFDerivAt` for `psiV`.
  have hV : HasFDerivAt WilkiesDesign.E.psiV
      (ContinuousLinearMap.pi fun j => (Work.WilE9.psig (x j) ^ 3) •
        (ContinuousLinearMap.proj j : (Fin n → ℝ) →L[ℝ] ℝ)) x := by
    rw [hasFDerivAt_pi]
    intro j
    simpa [WilkiesDesign.E.psiV] using hpi j
  rw [hV.fderiv]
  -- Evaluate the diagonal derivative on the basis direction `single i 1`.
  ext j
  rw [ContinuousLinearMap.pi_apply, smul_apply, ContinuousLinearMap.proj_apply,
    Pi.single_apply, Pi.single_apply]
  by_cases h : j = i
  · subst h; simp
  · simp [h]

end Work.WilE9.Psi
