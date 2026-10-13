/-
# `Work.FTS.BSSwirl.contDiff_vorticity_and_support`

The vorticity `∇×Ψ` of a *smooth, compactly supported* field `Ψ : ℝ³ → ℝ³` is again smooth and
compactly supported:

  `(∀ n, ContDiff ℝ n (vorticity Ψ)) ∧ HasCompactSupport (vorticity Ψ)`.

Both halves are purely formal consequences of the shape of `FiniteTimeSingularity.vorticity`:

* **regularity.**  `vorticity Ψ x = ∑ᵢ eᵢ ×₃ (DΨ(x) eᵢ)` is a *fixed continuous linear function of the
  derivative* `DΨ`, isolated as `Work.FTS.Physical.Pressure.curlCLM`
  (`vorticity_eq_curlCLM`).  A continuous linear map is smooth, and `DΨ` is `Cⁿ` as soon as `Ψ` is
  `C^{n+1}` (`ContDiff.fderiv_right`); the chain rule `ContDiff.comp` then gives `vorticity Ψ` of
  class `Cⁿ`.

* **support.**  Where `Ψ` is locally zero its derivative vanishes
  (`Filter.EventuallyEq.fderiv_eq` + `fderiv_const`), hence so does the vorticity; this gives
  `support (vorticity Ψ) ⊆ tsupport Ψ`, so
  `tsupport (vorticity Ψ) ⊆ tsupport Ψ` is compact.  (Note that the sharper
  `support (vorticity Ψ) ⊆ support Ψ` is *false*: a smooth compactly supported field may have a
  nonzero derivative at a point where it vanishes, e.g. `Ψ(x) = x` near the origin, where
  `0 ∉ support Ψ` but `DΨ(0) = 1`.  The support must be closed up first, which is what `tsupport`
  does.)
-/
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.InnerProductSpace.PiL2
import Submission.Work.FTS.BSSwirl.Defs
import Submission.Work.FTS.Physical.Pressure.CurlCLM

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open FiniteTimeSingularity Set Filter Topology

namespace Work.FTS.BSSwirl

noncomputable section

/-- **The vorticity of a smooth, compactly supported field is smooth and compactly supported.**

`vorticity Ψ` is the fixed continuous linear function `curlCLM` of the derivative `DΨ`, so the
`Cⁿ`-clause follows from `ContDiff.fderiv_right` and `ContDiff.comp`; and the vorticity vanishes
wherever `Ψ` is locally constant (in particular off `tsupport Ψ`), which gives the compact
support. -/
theorem contDiff_vorticity_and_support {Ψ : Work.FTS.BSSwirl.R3 → Work.FTS.BSSwirl.R3}
    (hΨ : ∀ n : ℕ, ContDiff ℝ n Ψ) (hc : HasCompactSupport Ψ) :
    (∀ n : ℕ, ContDiff ℝ n (fun x => FiniteTimeSingularity.vorticity Ψ x)) ∧
      HasCompactSupport (fun x => FiniteTimeSingularity.vorticity Ψ x) := by
  -- the vorticity is the fixed continuous linear map `curlCLM` evaluated at the derivative
  have hcurlv : (fun x : R3 => FiniteTimeSingularity.vorticity Ψ x)
      = fun x => Work.FTS.Physical.Pressure.curlCLM (fderiv ℝ Ψ x) :=
    funext fun x => Work.FTS.Physical.Pressure.vorticity_eq_curlCLM Ψ x
  -- the vorticity vanishes where `Ψ` is locally zero
  have hsub : Function.support (fun x : R3 => FiniteTimeSingularity.vorticity Ψ x) ⊆ tsupport Ψ := by
    intro x hx
    by_contra hxt
    -- `x` is in the complement of the closed set `tsupport Ψ`, an open neighbourhood of `x` ...
    have hnhds : (Function.support Ψ)ᶜ ∈ 𝓝 x :=
      mem_of_superset (((isClosed_tsupport Ψ).isOpen_compl).mem_nhds hxt)
        (compl_subset_compl.mpr subset_closure)
    -- ... on which `Ψ` therefore vanishes
    have hev : Ψ =ᶠ[𝓝 x] Function.const R3 0 := by
      filter_upwards [hnhds] with y hy
      have : Ψ y = 0 := by
        by_contra h
        exact hy (Function.mem_support.mpr h)
      simpa using this
    have hfd : fderiv ℝ Ψ x = 0 := by
      rw [hev.fderiv_eq]
      simp
    exact hx (by rw [hcurlv]; simp [hfd])
  refine ⟨fun n => ?_, ?_⟩
  · rw [hcurlv]
    exact (Work.FTS.Physical.Pressure.curlCLM.contDiff).comp
      ((hΨ (n + 1)).fderiv_right (by norm_num))
  · exact hc.isCompact.of_isClosed_subset (isClosed_tsupport _)
      (closure_minimal hsub (isClosed_tsupport Ψ))

end

end Work.FTS.BSSwirl
