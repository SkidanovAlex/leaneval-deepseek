import Mathlib
import Submission.Work.Kernels.Kernels
import Submission.Work.Kernels.ClassicalFacts.DeltaFun_basic
import Submission.Work.Kernels.ClassicalFacts.E2Fun_mem_InP
import Submission.Work.Kernels.ClassicalFacts.E4Fun_mem_InP
import Submission.Work.Kernels.ClassicalFacts.E6Fun_mem_InP

open UpperHalfPlane ModularForm ModularGroup Matrix
open scoped MatrixGroups ModularForm Modular Manifold Bundle Topology

namespace Work.Asymptotics.MiddleRange

/-! ## Continuity of the cusp atoms `f_k`

The functions `f_k` (`Work.Kernels.fk`) of CKMRV Section 4.4 are

  `f_{-2} = E₁₀/Δ`, `f_0 = 1`, `f_2 = E₁₄/Δ`, `f_4 = E₄`, `f_6 = E₆`, `f_8 = E₈`,
  `f_{10} = E₁₀`, `f_{12} = Δ`, `f_{14} = E₁₄`,

and `0` off those weights.  Each of these is continuous on `ℍ`: the Eisenstein series `E₄, E₆`
are modular forms (hence holomorphic, hence continuous), `Δ` is a cusp form with the same
property, `E₈ = E₄²`, `E₁₀ = E₄E₆`, `E₁₄ = E₄²E₆` are monomials in `E₄, E₆`, and the two
quotients `E₁₀/Δ`, `E₁₄/Δ` are continuous because `Δ` is nowhere vanishing
(`Work.Kernels.ClassicalFacts.DeltaFun_ne_zero`). -/

/-- The function `f_k` is continuous on `ℍ` for every `k : ℤ`. -/
lemma continuous_fk (k : ℤ) : Continuous (Work.Kernels.fk k) := by
  have hE4 : Continuous (Work.Kernels.E4Fun : UpperHalfPlane → ℂ) :=
    (Work.Kernels.ClassicalFacts.E4Fun_mem_InP.1).continuous
  have hE6 : Continuous (Work.Kernels.E6Fun : UpperHalfPlane → ℂ) :=
    (Work.Kernels.ClassicalFacts.E6Fun_mem_InP.1).continuous
  have hD : Continuous (Work.Kernels.DeltaFun : UpperHalfPlane → ℂ) :=
    (CuspFormClass.holo CuspForm.discriminant).continuous
  have hE8 : Continuous (Work.Kernels.E8Fun : UpperHalfPlane → ℂ) := hE4.pow 2
  have hE10 : Continuous (Work.Kernels.E10Fun : UpperHalfPlane → ℂ) := hE4.mul hE6
  have hE14 : Continuous (Work.Kernels.E14Fun : UpperHalfPlane → ℂ) := (hE4.pow 2).mul hE6
  have hq10 : Continuous
      (fun τ : UpperHalfPlane => Work.Kernels.E10Fun τ / Work.Kernels.DeltaFun τ) :=
    hE10.div hD (fun τ => Work.Kernels.ClassicalFacts.DeltaFun_ne_zero τ)
  have hq14 : Continuous
      (fun τ : UpperHalfPlane => Work.Kernels.E14Fun τ / Work.Kernels.DeltaFun τ) :=
    hE14.div hD (fun τ => Work.Kernels.ClassicalFacts.DeltaFun_ne_zero τ)
  unfold Work.Kernels.fk
  split_ifs
  · exact hq10
  · exact continuous_const
  · exact hq14
  · exact hE4
  · exact hE6
  · exact hE8
  · exact hE10
  · exact hD
  · exact hE14
  · exact continuous_const

/-- `fk k` is continuous on `ℍ` for every `k : ℤ` (a quotient by the nowhere vanishing `Δ`
in the cases `k = -2, 2`, and a polynomial in `E₄, E₆, Δ` otherwise), hence bounded on every
compact set. -/
theorem exists_bound_fk (K : Set UpperHalfPlane) (hK : IsCompact K) (k : ℤ) :
    ∃ B : ℝ, 0 < B ∧ ∀ z ∈ K, ‖Work.Kernels.fk k z‖ ≤ B := by
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn (continuous_fk k).continuousOn
  exact ⟨max C 0 + 1, by positivity,
    fun z hz => le_trans (hC z hz) (by linarith [le_max_left C 0])⟩

end Work.Asymptotics.MiddleRange
