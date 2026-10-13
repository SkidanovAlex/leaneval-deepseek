import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Mathlib.Topology.UniformSpace.Uniformizable
import Submission.Work.FTS.PressureOn.PoissonAux.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open Metric Set
open scoped Topology

namespace Work.FTS.PressureOn.PoissonAux

/-!
# A uniform bound for `ρ_ε''`

We prove that the second derivative of the cutoff profile `rhoProfile ε` is bounded by a
*universal* constant divided by `ε²`:

`∃ B ≥ 0, ∀ ε > 0, ∀ r, |(rhoProfile ε)'' r| ≤ B / ε²`.

The mechanism is the scaling identity `rhoProfile ε r = rhoProfile 1 (r / ε)` together with the
chain-rule relation for rescalings `r ↦ g (r/ε)` (namely `(g(r/ε))'' = g''(r/ε)/ε²`).  The
universal constant is the sup of `|(rhoProfile 1)''|`, which exists because `rhoProfile 1` is
`C²` and has compact support (it equals `1` as soon as `r² ≥ 2`).
-/

/-- The profile `rhoProfile 1` is `C²`. -/
theorem contDiff_rhoProfile_one : ContDiff ℝ 2 (rhoProfile 1) :=
  contDiff_const.sub ((contDiff_radialCut 2).comp
    (((contDiff_id (𝕜 := ℝ)).pow 2).div_const (1 ^ 2)))

/-- `rhoProfile ε` is the rescaling `r ↦ rhoProfile 1 (r / ε)` of `rhoProfile 1`. -/
theorem rhoProfile_eq_rescale (ε r : ℝ) : rhoProfile ε r = rhoProfile 1 (r / ε) := by
  rw [rhoProfile_apply, rhoProfile_apply, one_pow, div_one, div_pow]

/-- **Chain rule for the second derivative of a rescaling.**  If `g` is `C²`, then
`(fun r => g (r / ε))'' r = g'' (r / ε) / ε²`. -/
theorem deriv_deriv_rescale (g : ℝ → ℝ) (hg : ContDiff ℝ 2 g) (ε r : ℝ) :
    deriv (deriv (fun s : ℝ => g (s / ε))) r = deriv (deriv g) (r / ε) / ε ^ 2 := by
  have hDiffg : Differentiable ℝ g := hg.differentiable (by norm_num)
  have hDiffdg : Differentiable ℝ (deriv g) := hg.differentiable_deriv_two
  have hGfun : deriv (fun s : ℝ => g (s / ε)) = fun s => deriv g (s / ε) * (1 / ε) := by
    funext s
    have h1 : HasDerivAt (fun t : ℝ => t / ε) (1 / ε) s := (hasDerivAt_id s).div_const ε
    have h2 : HasDerivAt g (deriv g (s / ε)) (s / ε) :=
      (hDiffg.differentiableAt (x := s / ε)).hasDerivAt
    have h3 : HasDerivAt (fun t : ℝ => g (t / ε)) (deriv g (s / ε) * (1 / ε)) s :=
      h2.comp_of_eq s h1 rfl
    rw [h3.deriv]
  rw [hGfun]
  have h1 : HasDerivAt (fun t : ℝ => t / ε) (1 / ε) r := (hasDerivAt_id r).div_const ε
  have h2 : HasDerivAt (deriv g) (deriv (deriv g) (r / ε)) (r / ε) :=
    (hDiffdg.differentiableAt (x := r / ε)).hasDerivAt
  have h3 : HasDerivAt (fun t : ℝ => deriv g (t / ε) * (1 / ε))
      ((deriv (deriv g) (r / ε) * (1 / ε)) * (1 / ε)) r :=
    (h2.comp_of_eq r h1 rfl).mul_const (1 / ε)
  rw [h3.deriv]
  rw [mul_assoc, div_mul_div_comm, one_mul, pow_two]
  ring

/-- The second derivative of the rescaled profile `rhoProfile ε`, in terms of `rhoProfile 1`. -/
theorem deriv_deriv_rhoProfile_eq (ε r : ℝ) :
    deriv (deriv (rhoProfile ε)) r = deriv (deriv (rhoProfile 1)) (r / ε) / ε ^ 2 := by
  have hfun : rhoProfile ε = fun s : ℝ => rhoProfile 1 (s / ε) := by
    funext s
    exact rhoProfile_eq_rescale ε s
  rw [hfun]
  exact deriv_deriv_rescale (rhoProfile 1) contDiff_rhoProfile_one ε r

/-- For `|s| > 2` the profile `rhoProfile 1` is *locally constant* (equal to `1`), so its
derivative vanishes there: the derivative of `rhoProfile 1` is supported in the ball of radius
`2`.  (Note that `rhoProfile 1` itself is *not* compactly supported — it equals `1` for large
`|s|` — which is why we go through the derivative.) -/
theorem support_deriv_rhoProfile_one_subset :
    Function.support (deriv (rhoProfile 1)) ⊆ closedBall (0 : ℝ) 2 := by
  intro s hs
  rw [mem_closedBall, dist_eq_norm, sub_zero, Real.norm_eq_abs]
  by_contra h
  rw [not_le] at h
  have h2 : (2 : ℝ) < s ^ 2 := by nlinarith [sq_abs s]
  have hset : {t : ℝ | (2 : ℝ) < t ^ 2} ∈ 𝓝 s :=
    (isOpen_lt continuous_const
      ((continuous_id : Continuous fun t : ℝ => t).pow 2)).mem_nhds h2
  have hev : rhoProfile 1 =ᶠ[𝓝 s] (fun _ : ℝ => (1 : ℝ)) := by
    filter_upwards [hset] with t ht
    exact rhoProfile_eq_one (ε := 1) (by norm_num) (by nlinarith [ht])
  have hzero : deriv (rhoProfile 1) s = 0 := by
    rw [hev.deriv_eq, deriv_const]
  exact (Function.mem_support.mp hs) hzero

/-- The second derivative of `rhoProfile 1` has compact support. -/
theorem hasCompactSupport_deriv_deriv_rhoProfile_one :
    HasCompactSupport (deriv (deriv (rhoProfile 1))) :=
  (HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall (0 : ℝ) 2)
    support_deriv_rhoProfile_one_subset).deriv

/-- **The second derivative of `rhoProfile 1` is bounded.** -/
theorem exists_bound_deriv_deriv_rhoProfile_one :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ r : ℝ, |deriv (deriv (rhoProfile 1)) r| ≤ B := by
  have hcs2 := hasCompactSupport_deriv_deriv_rhoProfile_one
  have hcont : Continuous (deriv (deriv (rhoProfile 1))) := by
    have hcd : ContDiff ℝ 1 (deriv (rhoProfile 1)) := by
      simpa only [Nat.reduceAdd] using contDiff_rhoProfile_one.deriv'
    exact hcd.continuous_deriv_one
  obtain ⟨C, hC⟩ := hcont.bounded_above_of_compact_support hcs2
  exact ⟨C, le_trans (norm_nonneg _) (hC 0), fun r => by
    rw [← Real.norm_eq_abs]; exact hC r⟩

theorem exists_bound_deriv_deriv_rhoProfile :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ (ε : ℝ), 0 < ε → ∀ r : ℝ,
      |deriv (deriv (Work.FTS.PressureOn.rhoProfile ε)) r| ≤ B / ε ^ 2 := by
  obtain ⟨B, hB0, hB⟩ := exists_bound_deriv_deriv_rhoProfile_one
  refine ⟨B, hB0, fun ε hε r => ?_⟩
  have hε2 : 0 < ε ^ 2 := pow_pos hε 2
  rw [deriv_deriv_rhoProfile_eq ε r, abs_div, abs_of_pos hε2]
  exact div_le_div_of_nonneg_right (hB (r / ε)) (le_of_lt hε2)

end Work.FTS.PressureOn.PoissonAux
