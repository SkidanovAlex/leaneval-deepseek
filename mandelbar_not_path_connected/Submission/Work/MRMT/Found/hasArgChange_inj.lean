import Mathlib
import Submission.Work.MRMT.QC.plane_surjective

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.MRMT.Found

/-!
# Uniqueness of the argument change of a loop avoiding `0`

`Work.MRMT.QC.HasArgChange γ k` says that the loop `γ` admits a continuous argument function
`Θ : ℝ → ℝ` on `[0,1]` (so `γ t = ‖γ t‖ * exp (Θ t * I)`) whose total change is `Θ 1 - Θ 0 = 2πk`.

If `γ` never vanishes on `[0,1]`, such an argument function is unique up to an additive
`2πℤ`, and any two of them take values differing by an integral multiple of `2π` at every point
(`Work.MRMT.QC.argFun_diff_mem_multiples`).  The difference is then a continuous function of `t`
taking values in `2πℤ`, so it is constant on the connected set `[0,1]`
(`Work.MRMT.QC.eq_endpoints_of_multiples`): in particular `Θ 1 - Θ 0` is independent of the choice
of `Θ`.  Hence `k` is determined by `γ`: the argument change of `γ` is well defined.
-/

theorem hasArgChange_inj {γ : ℝ → ℂ} (hne : ∀ t ∈ Set.Icc (0 : ℝ) 1, γ t ≠ 0) {k k' : ℤ}
    (h : Work.MRMT.QC.HasArgChange γ k) (h' : Work.MRMT.QC.HasArgChange γ k') : k = k' := by
  obtain ⟨Θ₁, hA₁, hΔ₁⟩ := h
  obtain ⟨Θ₀, hA₀, hΔ₀⟩ := h'
  -- Any two argument functions differ, pointwise, by an integral multiple of `2π`.
  have hmult := Work.MRMT.QC.argFun_diff_mem_multiples hA₁ hA₀ hne
  -- A continuous function with values in `2πℤ` has equal values at the two endpoints of `[0,1]`.
  have hcont : ContinuousOn (fun t => Θ₁ t - Θ₀ t) (Set.Icc (0 : ℝ) 1) := hA₁.1.sub hA₀.1
  have hend : Θ₁ 1 - Θ₀ 1 = Θ₁ 0 - Θ₀ 0 := Work.MRMT.QC.eq_endpoints_of_multiples hcont hmult
  -- Comparing total changes: `2πk = (Θ₁ 1 - Θ₁ 0) = (Θ₀ 1 - Θ₀ 0) = 2πk'`.
  have h1 : 2 * Real.pi * (k : ℝ) = 2 * Real.pi * (k' : ℝ) := by linarith [hΔ₁, hΔ₀, hend]
  have h2 : (k : ℝ) = (k' : ℝ) :=
    mul_left_cancel₀ (by positivity : (2 * Real.pi : ℝ) ≠ 0) h1
  exact_mod_cast h2

end Work.MRMT.Found
