import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS.RegPkgGal.Defs
import Submission.Work.FTS.RegPkgGal.Basic
import Submission.Work.FTS.RegPkgGal.RVocab
import Submission.Work.FTS.Regularity.Defs
import Submission.Work.FTS.Galerkin.Defs
import Submission.Work.Elliptic.Defs
import Submission.Work.Construction.Defs
import Submission.Work.Spaces.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.FTS.RegPkgGal.R5.dtg_eq_rhs` — the pointwise identification `∂_τ g̃ = dynLin + dynRHS`

`extG g` extends the family `g` to negative fake time by the *first-order Taylor jet* of
`s ↦ g z θ s` at `s = 0`:

`extG g z θ s = 0` for `z ≤ 0`; `= g z θ 0 + s·∂_τg(z,θ,0)` for `s < 0`; `= g z θ s` otherwise.

For `z > 0` and `τ ≥ 0` we therefore have `extG g z θ τ = g z θ τ`, and the derivative of
`s ↦ extG g z θ s` is the derivative of `s ↦ g z θ s`:

* at `τ > 0` this is immediate, because `Ioi 0` is a neighbourhood of `τ` (the two functions
  agree there), and the equation is only needed on `Ici 0` (its `HasDerivWithinAt` form, which
  converts to `HasDerivAt` at any `τ > 0`);
* at `τ = 0` the negative branch of `extG` is *exactly* the linearisation of `g` at `0`, so the
  left difference quotients of `g̃` and those of `g` agree, and the two one-sided derivatives glue
  (`HasDerivWithinAt.union` on `Iic 0 ∪ Ici 0 = univ`).  This is where the hypothesis
  `h0` — the *two-sided* derivative of `τ ↦ g z θ τ` at `0` — is consumed.

Notably no use is made of the regularity package `hmin`: the two ingredients that carry the
derivative are the equation `hsol.2` (on `Ici 0`) and `h0` (the two-sided derivative at `0`).
-/

namespace Work.FTS.RegPkgGal.R5

open Set Filter Topology

/-- **The derivative of `g̃` at `τ = 0`.**  If `G = s ↦ g z θ s` has a two-sided derivative `c` at
`0` and `0 < z`, then so does `s ↦ extG g z θ s`: on `Iic 0` the extension is *identically* the
affine function `s ↦ g z θ 0 + s·c` (the negative branch being the Taylor jet, and at `s = 0` the
branch test `s < 0` fails with the same value), while on `Ici 0` it *is* `G`; the two one-sided
derivatives therefore coincide and glue over `Iic 0 ∪ Ici 0 = univ`. -/
theorem hasDerivAt_extG_of_zero {g : ℝ → ℝ → ℝ → ℝ} {z θ c : ℝ} (hz : 0 < z)
    (h : HasDerivAt (fun s => g z θ s) c 0) :
    HasDerivAt (fun s => extG g z θ s) c 0 := by
  have hderiv : deriv (fun s => g z θ s) 0 = c := h.deriv
  -- pointwise description of the extension at `z > 0`
  have hpt : ∀ s : ℝ, extG g z θ s = if s < 0 then g z θ 0 + s * c else g z θ s := by
    intro s
    by_cases hs : s < 0
    · rw [extG_of_neg hz hs, hderiv, if_pos hs]
    · rw [extG_of_pos hz (not_lt.mp hs), if_neg hs]
  -- the right piece: `extG` agrees with `g` on `Ici 0`
  have hR : HasDerivWithinAt (fun s => extG g z θ s) c (Set.Ici 0) 0 :=
    (h.hasDerivWithinAt (s := Set.Ici 0)).congr
      (fun y hy => extG_of_pos hz hy)
      (extG_of_pos hz le_rfl)
  -- the left piece: `extG` is the affine jet on `Iic 0`
  have hA : HasDerivAt (fun s : ℝ => g z θ 0 + s * c) c 0 := by
    have h1 : HasDerivAt (fun s : ℝ => s * c) (1 * c) 0 := (hasDerivAt_id (0 : ℝ)).mul_const c
    have h2 : HasDerivAt (fun s : ℝ => s * c) c 0 := by simpa using h1
    simpa using h2.const_add (g z θ 0)
  have hL : HasDerivWithinAt (fun s => extG g z θ s) c (Set.Iic 0) 0 :=
    hA.hasDerivWithinAt.congr
      (fun y hy => by
        rw [hpt y]
        by_cases hy' : y < 0
        · rw [if_pos hy']
        · rw [if_neg hy']
          have hy0 : y = 0 := le_antisymm hy (not_lt.mp hy')
          subst hy0
          simp)
      (by rw [hpt 0, if_neg (not_lt.mpr le_rfl)]; simp)
  have hU : HasDerivWithinAt (fun s => extG g z θ s) c (Set.Iic 0 ∪ Set.Ici 0) 0 := hL.union hR
  rw [Set.Iic_union_Ici] at hU
  exact hasDerivWithinAt_univ.mp hU

/-- **The derivative of `g̃` at `τ > 0`.**  For `z > 0` and `τ > 0` the extension agrees with `g`
on the neighbourhood `Ioi 0` of `τ`, so the two functions have the same derivative there. -/
theorem hasDerivAt_extG_of_pos {g : ℝ → ℝ → ℝ → ℝ} {z θ τ c : ℝ} (hz : 0 < z) (hτ : 0 < τ)
    (h : HasDerivAt (fun s => g z θ s) c τ) :
    HasDerivAt (fun s => extG g z θ s) c τ :=
  h.congr_of_eventuallyEq <| by
    filter_upwards [Ioi_mem_nhds hτ] with s hs
    exact extG_of_pos hz hs.le

/-- **`∂_τ g̃ = dynLin + dynRHS`** on the fake-time strip: for `τ ∈ [0,S]` and `z > 0`, `(z,θ) ∈ Qd`,
the derivative of `s ↦ extG g z θ s` at `τ` is the dynamic right-hand side at `τ`.

At `τ > 0` this is the one-sided equation `IsDynEqOn` (`hsol.2`), whose `HasDerivWithinAt` form on
`Ici 0` upgrades to `HasDerivAt` since `Ici 0` is a neighbourhood of `τ`; at `τ = 0` it is the
two-sided hypothesis `h0`, transported across the Taylor-jet branch of `extG`
(`hasDerivAt_extG_of_zero`). -/
theorem dtg_eq_rhs {α S : ℝ} (hS : 0 < S)
    {g Φ : ℝ → ℝ → ℝ → ℝ}
    (hmin : Work.FTS.RegPkgGal.RegPkgMin (Work.FTS.Regularity.pExp α) g)
    (hsol : Work.FTS.Galerkin.IsDynGSolWith (Work.Elliptic.IsBslSol (Work.FTS.Regularity.pExp α))
      (Work.FTS.Regularity.pExp α) Φ g)
    (h0 : ∀ z θ : ℝ, 0 < z → (z, θ) ∈ Work.Construction.Qd →
      HasDerivAt (fun s => g z θ s)
        (Work.FTS.Galerkin.dynLin (Work.FTS.Regularity.pExp α) g 0 z θ
          + Work.FTS.Galerkin.dynRHS (Work.FTS.Regularity.pExp α) Φ g 0 z θ) 0) :
    ∀ τ ∈ Set.Icc 0 S, ∀ z θ : ℝ, 0 < z → (z, θ) ∈ Work.Construction.Qd →
      deriv (fun s => Work.FTS.RegPkgGal.extG g z θ s) τ
        = Work.FTS.Galerkin.dynLin (Work.FTS.Regularity.pExp α) g τ z θ
          + Work.FTS.Galerkin.dynRHS (Work.FTS.Regularity.pExp α) Φ g τ z θ := by
  intro τ hτ z θ hz hQd
  have hLeq : HasDerivWithinAt (fun s => g z θ s)
      (Work.FTS.Galerkin.dynLin (Work.FTS.Regularity.pExp α) g τ z θ
        + Work.FTS.Galerkin.dynRHS (Work.FTS.Regularity.pExp α) Φ g τ z θ) (Set.Ici 0) τ :=
    hsol.2 z θ τ hτ.1 hQd
  rcases eq_or_lt_of_le hτ.1 with hzero | hpos
  · subst hzero
    exact (hasDerivAt_extG_of_zero hz (h0 z θ hz hQd)).deriv
  · exact (hasDerivAt_extG_of_pos hz hpos (hLeq.hasDerivAt (Ici_mem_nhds hpos))).deriv

end Work.FTS.RegPkgGal.R5
