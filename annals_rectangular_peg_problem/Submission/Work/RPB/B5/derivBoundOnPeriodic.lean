import Mathlib
import Submission.Work.RPA3.periodic_mem_Icc
import Submission.Work.RPB.B3.boundsOnCompactBox
import Submission.Work.RPB.B3.UniformInverseAux

/-!
# B5: a uniform bound for `∂_σ S` on the periodic slab

Let `S : ℝ → ℝ → ℝ → ℝ` be a `C⁸` family which is `2π`-periodic in its second variable.
We show that its partial derivative in the third variable,
`∂₃ S (τ,t,σ) = deriv (fun s ↦ S τ t s) σ`, is bounded uniformly on the slab
`τ ∈ [0,1]`, `t ∈ ℝ`, `|σ| ≤ 1/4`.

The proof has three ingredients.

* `pdsR S τ t s` is `∂₃ S` written through `fderiv` (evaluating `fderiv ℝ S` at the vector
  `(0,(0,1))`), which makes its joint continuity immediate.
* `pdsR_eq_deriv` identifies this with the ordinary one-variable derivative.
* `Work.RPA3.periodic_mem_Icc` reduces an arbitrary `t ∈ ℝ` to a point `t₀ ∈ [0,2π]`, and on the
  compact box `[0,1] × [0,2π] × [-1/4,1/4]` the continuous function `∂₃ S` is bounded.

The hypothesis `hneg` is not needed for this statement (only readability of the derivative is
hypothesised, and the bound is deduced from smoothness and compactness).
-/

open scoped ContDiff

set_option autoImplicit false
set_option linter.unusedVariables false

namespace Work.RPB.B5

noncomputable section

/-- The partial derivative `∂₃ S` of a family `S : ℝ → ℝ → ℝ → ℝ`, written through `fderiv` so
that its joint continuity is immediate. -/
def pdsR (S : ℝ → ℝ → ℝ → ℝ) (τ t s : ℝ) : ℝ :=
  (fderiv ℝ (fun z : ℝ × (ℝ × ℝ) => S z.1 z.2.1 z.2.2) (τ, (t, s)))
    ((0 : ℝ), ((0 : ℝ), (1 : ℝ)))

/-- `pdsR S τ t s` coincides with the ordinary derivative `deriv (fun u ↦ S τ t u) s`. -/
lemma pdsR_eq_deriv (S : ℝ → ℝ → ℝ → ℝ)
    (hS : ContDiff ℝ 8 (fun z : ℝ × (ℝ × ℝ) => S z.1 z.2.1 z.2.2)) (τ t s : ℝ) :
    pdsR S τ t s = deriv (fun u : ℝ => S τ t u) s := by
  have hF : HasFDerivAt (fun z : ℝ × (ℝ × ℝ) => S z.1 z.2.1 z.2.2)
      (fderiv ℝ (fun z : ℝ × (ℝ × ℝ) => S z.1 z.2.1 z.2.2) (τ, (t, s))) (τ, (t, s)) :=
    ((hS.differentiable (by norm_num)).differentiableAt).hasFDerivAt
  have hφ : HasDerivAt (fun u : ℝ => (τ, (t, u))) ((0 : ℝ), ((0 : ℝ), (1 : ℝ))) s :=
    (hasDerivAt_const (c := τ) s).prodMk
      ((hasDerivAt_const (c := t) s).prodMk (hasDerivAt_id s))
  have hcomp : HasDerivAt
      ((fun z : ℝ × (ℝ × ℝ) => S z.1 z.2.1 z.2.2) ∘ fun u : ℝ => (τ, (t, u)))
      (fderiv ℝ (fun z : ℝ × (ℝ × ℝ) => S z.1 z.2.1 z.2.2) (τ, (t, s))
        ((0 : ℝ), ((0 : ℝ), (1 : ℝ)))) s :=
    hF.comp_hasDerivAt s hφ
  have hcomp' : HasDerivAt (fun u : ℝ => S τ t u)
      (fderiv ℝ (fun z : ℝ × (ℝ × ℝ) => S z.1 z.2.1 z.2.2) (τ, (t, s))
        ((0 : ℝ), ((0 : ℝ), (1 : ℝ)))) s := hcomp
  unfold pdsR
  exact hcomp'.deriv.symm

/-- Joint continuity of `∂₃ S` for a `C⁸` family. -/
lemma continuous_pdsR (S : ℝ → ℝ → ℝ → ℝ)
    (hS : ContDiff ℝ 8 (fun z : ℝ × (ℝ × ℝ) => S z.1 z.2.1 z.2.2)) :
    Continuous (fun z : ℝ × (ℝ × ℝ) => pdsR S z.1 z.2.1 z.2.2) := by
  have hcont : Continuous
      (fun z : ℝ × (ℝ × ℝ) => fderiv ℝ (fun w : ℝ × (ℝ × ℝ) => S w.1 w.2.1 w.2.2) z) :=
    hS.continuous_fderiv (by norm_num)
  have hv : Continuous (fun _ : ℝ × (ℝ × ℝ) => ((0 : ℝ), ((0 : ℝ), (1 : ℝ)))) :=
    continuous_const
  have h := hcont.clm_apply hv
  convert h using 1
  ext z
  simp [pdsR]

theorem derivBoundOnPeriodic (S : ℝ → ℝ → ℝ → ℝ)
    (hS : ContDiff ℝ 8 (fun z : ℝ × (ℝ × ℝ) => S z.1 z.2.1 z.2.2))
    (hper : ∀ τ t σ, S τ (t + 2 * Real.pi) σ = S τ t σ)
    (hneg : ∀ τ ∈ Set.Icc (0 : ℝ) 1, ∀ t : ℝ, ∀ σ : ℝ, |σ| ≤ 1 / 4 →
      deriv (fun s : ℝ => S τ t s) σ < 0) :
    ∃ M : ℝ, 0 < M ∧ ∀ τ ∈ Set.Icc (0 : ℝ) 1, ∀ t : ℝ, ∀ σ : ℝ, |σ| ≤ 1 / 4 →
      |deriv (fun s : ℝ => S τ t s) σ| ≤ M := by
  have hGcont : Continuous (fun z : ℝ × (ℝ × ℝ) => pdsR S z.1 z.2.1 z.2.2) :=
    continuous_pdsR S hS
  have hK : IsCompact (Set.Icc (0:ℝ) 1 ×ˢ (Set.Icc (0:ℝ) (2 * Real.pi) ×ˢ
      Set.Icc (-(1 / 4 : ℝ)) (1 / 4))) :=
    isCompact_Icc.prod (isCompact_Icc.prod isCompact_Icc)
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hGcont.continuousOn
  refine ⟨max C 1, lt_of_lt_of_le zero_lt_one (le_max_right C 1), ?_⟩
  intro τ hτ t σ hσ
  -- reduce `t` modulo `2π` to a point of `[0,2π]`
  have hperf : Function.Periodic (fun t : ℝ => fun s : ℝ => S τ t s) (2 * Real.pi) := by
    intro t
    funext s
    exact hper τ t s
  obtain ⟨t0, ht0, heq⟩ :=
    Work.RPA3.periodic_mem_Icc Real.two_pi_pos (fun t : ℝ => fun s : ℝ => S τ t s) hperf t
  have hfun : (fun s : ℝ => S τ t s) = (fun s : ℝ => S τ t0 s) := heq
  have hmem : (τ, (t0, σ)) ∈ Set.Icc (0:ℝ) 1 ×ˢ (Set.Icc (0:ℝ) (2 * Real.pi) ×ˢ
      Set.Icc (-(1 / 4 : ℝ)) (1 / 4)) := by
    refine ⟨hτ, ?_, ?_⟩
    · exact ht0
    · rw [Set.mem_Icc]
      exact abs_le.mp hσ
  have hbound : |pdsR S τ t0 σ| ≤ C := by
    have h := hC (τ, (t0, σ)) hmem
    rwa [Real.norm_eq_abs] at h
  calc |deriv (fun s : ℝ => S τ t s) σ|
      = |deriv (fun s : ℝ => S τ t0 s) σ| := by rw [hfun]
    _ = |pdsR S τ t0 σ| := by rw [pdsR_eq_deriv S hS τ t0 σ]
    _ ≤ C := hbound
    _ ≤ max C 1 := le_max_left C 1

end

end Work.RPB.B5
