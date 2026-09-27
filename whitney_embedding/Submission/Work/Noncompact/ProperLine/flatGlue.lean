import Mathlib

/-!
# Gluing `C^∞` pieces that are flat at the junctions
-/

open Set Filter Asymptotics
open scoped Topology ContDiff

namespace Work.Noncompact.ProperLine

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

private theorem le_top_withTop (n : ℕ) : ((n : ℕ∞) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) :=
  WithTop.coe_le_coe.mpr le_top

/-- **Taylor's theorem for a function flat at `t₀`.**  If `U` is `C^∞` on the convex set `s`,
`t₀ ∈ s`, and all derivatives of `U` of order `≥ 1` (within `s`) vanish at `t₀`, then the Taylor
polynomial of order `n` at `t₀` is the constant `U t₀`, hence `U t - U t₀ = o((t - t₀)^n)`. -/
theorem isLittleO_flatWithin {U : ℝ → F} {t₀ : ℝ} {s : Set ℝ} (hs : Convex ℝ s) (ht : t₀ ∈ s)
    (hU : ContDiffOn ℝ ∞ U s)
    (hf : ∀ k : ℕ, 0 < k → iteratedDerivWithin k U s t₀ = 0) (n : ℕ) :
    (fun t => U t - U t₀) =o[𝓝[s] t₀] (fun t => (t - t₀) ^ n) := by
  have h := taylor_isLittleO hs ht (hU.of_le (le_top_withTop n))
  have hte : ∀ t : ℝ, taylorWithinEval U n s t₀ t = U t₀ := by
    intro t
    rw [taylor_within_apply]
    refine (Finset.sum_eq_single 0 ?_ ?_).trans ?_
    · intro k hk hk0
      have hk' : 0 < k := Nat.pos_of_ne_zero hk0
      rw [hf k hk', smul_zero]
    · intro h0
      exact absurd (Finset.mem_range.mpr (Nat.lt_succ_of_le (Nat.zero_le n))) h0
    · simp
  simpa [hte] using h

end Work.Noncompact.ProperLine
