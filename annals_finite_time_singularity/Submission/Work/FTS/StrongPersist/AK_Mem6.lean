/-
# `Work.FTS.StrongPersist.AK_Mem6` — `AK α` is `ℋ⁶`-honest with an `α`-uniform norm bound

The auxiliary block `AK α z θ = (Γ(θ)/c α)·2z²/(1+z)³` of the `g`-equation
(`Construction.AK`) is a *fixed* datum of the construction: its `ℋ⁶`-norm enters the level-six
estimates of the strong-solution route (`StrongPersist.L3RhsPriced`), and it must be bounded by
a constant **independent of `α ∈ (0,1]`**.

## Route

`AK α` is separable, `AK α = Γ(θ)·(2z²/(1+z)³/c α)`, so the whole content is the
factorisation of the `ℋ⁶`-integrand of a separated datum (`L6Aux.HkIntegrandSepLeGen`) plus
the two one-dimensional bounds:

* **radial** (`AK6.akRho_jet_bound6`): `(D_z^j ρ · w)² ≤ R/(1+z)²` for `j ≤ 6`, `ρ = 2z²/(1+z)³`;
* **angular** (`AK6.Sharp6`): `Γ ≤ 1`, `Γ² ≤ sin(2θ)^{2α/5}` and — the point —
  `|D_θ^iΓ| ≤ α·10⁵·Γ` for `1 ≤ i ≤ 6`.  The explicit factor `α` (from
  `Spaces.dthU_iter_Gam_abs_bound`) is exactly what makes the `γ`-weighted angular block
  *uniformly* integrable: after `Γ² ≤ sin(2θ)^{2α/5}` it becomes
  `α²·sin(2θ)^{2α/5-γ} ≤ (α+sin 2θ)²·sin(2θ)^{2α/5-γ}`, whose `θ`-integral is bounded by
  `700` uniformly in `α` (`Elliptic.WtoH_Angular`) — the paper's `W^{2,∞} → ℋ⁶` mechanism.

The pointwise bound `AK6.AK_integrand_le6` is then integrated with
`AK6.hkSq_le_of_integrand_le6` (`≤ 2·(A·10⁴ + B·700)`), and `HkMem` comes from
`AK6.HkMem_AK6` (the `angMaj` majorant route).
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS.StrongPersist.AK6.Sharp6
import Submission.Work.FTS.StrongPersist.AK6.akRho_jet_bound6
import Submission.Work.FTS.StrongPersist.AK6.hkSq_le_of_integrand_le6
import Submission.Work.FTS.StrongPersist.AK6.HkMem_AK6

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongPersist

theorem AK_Mem6 : ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ), 0 < α → α ≤ 1 →
    Work.Spaces.HkMem α 6 (Work.Construction.AK α) ∧
    Work.Spaces.HkNorm α 6 (Work.Construction.AK α) ≤ C := by
  obtain ⟨R, hR0, hrad⟩ := Work.FTS.StrongPersist.AK6.akRho_jet_bound6
  refine ⟨max 1 (Real.sqrt (2 * (700 * R * 10 ^ 4 + 49 * 10 ^ 12 * R * 700))), ?_, ?_⟩
  · exact lt_max_of_lt_left one_pos
  · intro α hα hα1
    refine ⟨Work.FTS.StrongPersist.AK6.HkMem_AK6 α hα hα1 hR0 hrad, ?_⟩
    have hpt := Work.FTS.StrongPersist.AK6.AK_integrand_le6 hR0 hrad α hα hα1
    have hsq := Work.FTS.StrongPersist.AK6.hkSq_le_of_integrand_le6 (α := α)
      (A := 700 * R) (B := 49 * 10 ^ 12 * R) hα hα1 (by positivity) (by positivity)
      (fun z hz θ hθ => hpt z hz θ hθ)
    calc Work.Spaces.HkNorm α 6 (Work.Construction.AK α)
        = Real.sqrt (Work.Spaces.HkSq α 6 (Work.Construction.AK α)) := rfl
      _ ≤ Real.sqrt (2 * (700 * R * 10 ^ 4 + 49 * 10 ^ 12 * R * 700)) :=
          Real.sqrt_le_sqrt hsq
      _ ≤ max 1 (Real.sqrt (2 * (700 * R * 10 ^ 4 + 49 * 10 ^ 12 * R * 700))) :=
          le_max_right _ _

end Work.FTS.StrongPersist
