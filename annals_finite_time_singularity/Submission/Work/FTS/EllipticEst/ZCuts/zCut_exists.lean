/-
Copyright: work module for the Elgindi finite-time singularity project.

# `zCut_exists`: the log-scale bump of the weighted Hardy inequality `zHardy_sq_le`

The lemma proved here is

  `theorem zCut_exists : ∃ φ : ℝ → ℝ, ∃ K : ℝ, Work.FTS.EllipticEst.IsZCut φ K`

with (`Submission/Work/FTS/EllipticEst/zHardyCutDefs.lean`)

  `IsZCut φ K := ContDiff ℝ smoothOrder φ ∧ (∀ t, |t| ≤ 1 → φ t = 1) ∧
                (∀ t, 2 ≤ |t| → φ t = 0) ∧ (∀ t, 0 ≤ φ t ∧ φ t ≤ 1) ∧ 0 ≤ K ∧
                ∀ t, |deriv φ t| ≤ K`.

## The `⊤`/`∞` trap (why `IsZCut` had to be repaired)

The order parameter of `ContDiff 𝕜 n f` is `n : ℕ∞ω = WithTop ℕ∞`, in which
`∞ = ((⊤ : ℕ∞) : WithTop ℕ∞)` is `C^∞` and `⊤ : ℕ∞ω = ω` is **analyticity**
(`Mathlib/Analysis/Calculus/ContDiff/Defs.lean`: "the parameter `n` belongs to `ℕ∞ω`; for
`n = ω` we require the function to be analytic").  The first version of `IsZCut` used the
literal `⊤` for "a `C^∞` bump", which therefore demanded *analyticity* and was
**unsatisfiable**: an analytic function which is `1` on `[-1,1]` and `0` outside `(-2,2)` is
identically `0` by the identity theorem, applied at `3` where the function vanishes on the
neighbourhood `(2,3)`.  The same trap is documented in `Submission/Work/Stability/Cutoff.lean`,
where `Work.Spaces.SmoothNbhd` — defined with `⊤` — turned out to be a globally analytic class.
`IsZCut` now uses `Work.FTS.EllipticEst.smoothOrder = ∞`, so it says what its docstring says.

## The witness

`φ t = Work.ChiExplicit.chi t = Real.smoothTransition (2 - |t|)`: `C^∞`, `= 1` on `[-1,1]`,
`= 0` for `|t| ≥ 2`, values in `[0,1]`, with bounded derivative (`deriv χ` is continuous and
vanishes strictly outside the compact set `[-2,2]`, hence is bounded by its maximum over
`[-2,2]`, which exists because `[-2,2]` is compact and `deriv χ` is continuous).
-/
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.InnerProductSpace.Basic
import Submission.Work.FTS.EllipticEst.zHardyCutDefs
import Submission.Work.ChiExplicit.Defs
import Submission.Work.ChiExplicit.chi_contDiff

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped ContDiff Topology
open Set Filter

namespace Work.FTS.EllipticEst.ZCuts

/-- **The bump is smooth with bounded derivative.**  The witness is
`φ t = Work.ChiExplicit.chi t = Real.smoothTransition (2 - |t|)` and `K` is the maximum of
`|φ'|` over `[-2,2]` (`φ'` vanishes outside that interval). -/
theorem zCut_exists_smooth :
    ∃ φ : ℝ → ℝ, ∃ K : ℝ,
      ContDiff ℝ Work.FTS.EllipticEst.smoothOrder φ ∧ (∀ t, |t| ≤ 1 → φ t = 1) ∧
        (∀ t, 2 ≤ |t| → φ t = 0) ∧ (∀ t, 0 ≤ φ t ∧ φ t ≤ 1) ∧ 0 ≤ K ∧
          ∀ t, |deriv φ t| ≤ K := by
  -- `chi` is `C^∞` (`chi_contDiff`), the value facts are its interface.
  have hcd : ContDiff ℝ Work.FTS.EllipticEst.smoothOrder Work.ChiExplicit.chi :=
    Work.ChiExplicit.chi_contDiff ⊤
  have hcont : Continuous (fun t : ℝ => |deriv Work.ChiExplicit.chi t|) :=
    (hcd.continuous_deriv (by simp [Work.FTS.EllipticEst.smoothOrder])).abs
  -- `deriv chi` vanishes strictly outside `[-2,2]`, since `chi` is locally `0` there.
  have hzero_deriv : ∀ t : ℝ, 2 < |t| → deriv Work.ChiExplicit.chi t = 0 := by
    intro t ht
    have hopen : IsOpen {s : ℝ | (2 : ℝ) < |s|} := isOpen_lt continuous_const continuous_abs
    have hev : Work.ChiExplicit.chi =ᶠ[𝓝 t] (fun _ => (0 : ℝ)) := by
      filter_upwards [hopen.mem_nhds ht] with s hs
      exact Work.ChiExplicit.chi_eq_zero hs.le
    rw [hev.deriv_eq, deriv_const]
  -- A point of `[-2,2]` maximizing `|deriv chi|`.
  obtain ⟨x₀, -, hmax⟩ :=
    (isCompact_Icc (a := (-2 : ℝ)) (b := 2)).exists_isMaxOn
      (⟨(-2 : ℝ), by norm_num⟩ : (Set.Icc (-2 : ℝ) 2).Nonempty)
      (f := fun t : ℝ => |deriv Work.ChiExplicit.chi t|) hcont.continuousOn
  have hmax' : ∀ t ∈ Set.Icc (-2 : ℝ) 2,
      |deriv Work.ChiExplicit.chi t| ≤ |deriv Work.ChiExplicit.chi x₀| :=
    isMaxOn_iff.mp hmax
  refine ⟨Work.ChiExplicit.chi, |deriv Work.ChiExplicit.chi x₀|, hcd, ?_, ?_, ?_,
    abs_nonneg _, ?_⟩
  · intro t ht; exact Work.ChiExplicit.chi_eq_one ht
  · intro t ht; exact Work.ChiExplicit.chi_eq_zero ht
  · intro t; exact ⟨Work.ChiExplicit.chi_nonneg t, Work.ChiExplicit.chi_le_one t⟩
  · intro t
    by_cases ht : |t| ≤ 2
    · exact hmax' t (Set.mem_Icc.mpr (abs_le.mp ht))
    · rw [hzero_deriv t (lt_of_not_ge ht)]
      simpa using abs_nonneg (deriv Work.ChiExplicit.chi x₀)

/-- **The logarithmic bump exists.**  This is `zCut_exists_smooth` with the defining
conjunction of `IsZCut` unfolded (after the repair `⊤ → ∞` of the order parameter). -/
theorem zCut_exists : ∃ φ : ℝ → ℝ, ∃ K : ℝ, Work.FTS.EllipticEst.IsZCut φ K := by
  obtain ⟨φ, K, h⟩ := zCut_exists_smooth
  exact ⟨φ, K, h⟩

end Work.FTS.EllipticEst.ZCuts
