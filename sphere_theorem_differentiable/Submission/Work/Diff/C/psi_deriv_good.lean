import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

open scoped Topology

namespace Work.Diff.C

/-- If a smooth function `ψ : ℝ → ℝ` agrees with the identity on the closed half-line
`[-1 + 2c, ∞)`, then its first derivative is `1` and its second derivative vanishes there.

The argument is two-sided in nature: on the *open* half-line `(-1 + 2c, ∞)` the function agrees
with `id` on a whole neighbourhood of each point, so the derivative is `1` and the second
derivative is `0` there.  At the boundary point `-1 + 2c` only a one-sided neighbourhood is
available, but smoothness (hence continuity of the first and second derivatives) lets us take
the limit: the set where `deriv ψ = 1` (resp. `iteratedDeriv 2 ψ = 0`) is closed, contains the
open half-line, and therefore contains its closure, which includes `-1 + 2c`. -/
theorem psi_deriv_good {c : ℝ} {ψ : ℝ → ℝ} (hψC : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hid : ∀ s : ℝ, -1 + 2 * c ≤ s → ψ s = s) :
    (∀ s : ℝ, -1 + 2 * c ≤ s → deriv ψ s = 1) ∧
      (∀ s : ℝ, -1 + 2 * c ≤ s → iteratedDeriv 2 ψ s = 0) := by
  -- On the open half-line each point has a neighbourhood on which `ψ` coincides with the identity.
  have hev : ∀ s : ℝ, -1 + 2 * c < s → ψ =ᶠ[𝓝 s] (fun x : ℝ => x) := by
    intro s hs
    filter_upwards [Ici_mem_nhds hs] with x hx
    exact hid x hx
  -- Consequently the derivatives have the expected values on the open half-line.
  have hderiv_lt : ∀ s : ℝ, -1 + 2 * c < s → deriv ψ s = 1 := by
    intro s hs
    have h := (hev s hs).deriv_eq
    simpa [deriv_id''] using h
  have hiter_lt : ∀ s : ℝ, -1 + 2 * c < s → iteratedDeriv 2 ψ s = 0 := by
    intro s hs
    have h := (hev s hs).iteratedDeriv_eq 2
    have h2 : iteratedDeriv 2 (fun x : ℝ => x) s = 0 := by
      rw [show (fun x : ℝ => x) = id from rfl, iteratedDeriv_id]
      norm_num
    rw [h2] at h
    exact h
  -- Continuity of the first and second derivatives, from smoothness.
  have htwo : ((2 : ℕ) : WithTop ℕ∞) < ((⊤ : ℕ∞) : WithTop ℕ∞) :=
    WithTop.coe_lt_coe.mpr (ENat.natCast_lt_top 2)
  have hone : ((1 : ℕ) : WithTop ℕ∞) < ((⊤ : ℕ∞) : WithTop ℕ∞) :=
    WithTop.coe_lt_coe.mpr (ENat.natCast_lt_top 1)
  have hcont1 : Continuous (iteratedDeriv 1 ψ) := (hψC.differentiable_iteratedDeriv 1 hone).continuous
  have hcont2 : Continuous (iteratedDeriv 2 ψ) := (hψC.differentiable_iteratedDeriv 2 htwo).continuous
  -- Boundary values, by closedness and `closure (Ioi a) = Ici a`.
  have hderiv0 : deriv ψ (-1 + 2 * c) = 1 := by
    have hcf : Continuous (deriv ψ) := by simpa [iteratedDeriv_one] using hcont1
    have hclosed : IsClosed {x : ℝ | deriv ψ x = 1} := isClosed_eq hcf continuous_const
    have hsub : Set.Ioi (-1 + 2 * c) ⊆ {x : ℝ | deriv ψ x = 1} := fun x hx => hderiv_lt x hx
    have hmem : (-1 + 2 * c) ∈ closure (Set.Ioi (-1 + 2 * c)) := by
      rw [closure_Ioi]; simp
    exact hclosed.closure_subset_iff.mpr hsub hmem
  have hiter0 : iteratedDeriv 2 ψ (-1 + 2 * c) = 0 := by
    have hclosed : IsClosed {x : ℝ | iteratedDeriv 2 ψ x = 0} := isClosed_eq hcont2 continuous_const
    have hsub : Set.Ioi (-1 + 2 * c) ⊆ {x : ℝ | iteratedDeriv 2 ψ x = 0} :=
      fun x hx => hiter_lt x hx
    have hmem : (-1 + 2 * c) ∈ closure (Set.Ioi (-1 + 2 * c)) := by
      rw [closure_Ioi]; simp
    exact hclosed.closure_subset_iff.mpr hsub hmem
  constructor
  · intro s hs
    rcases lt_or_eq_of_le hs with h | h
    · exact hderiv_lt s h
    · rw [← h]; exact hderiv0
  · intro s hs
    rcases lt_or_eq_of_le hs with h | h
    · exact hiter_lt s h
    · rw [← h]; exact hiter0

end Work.Diff.C
