/-
# Injectivity of the outer chart `Θ_v` on the collar `½ ≤ ‖p‖∞ ≤ 1`

The outer chart of blueprint §1 is

  `Θ_v(p, y) = (x, s)`,  `x = u(p) σ_v + y₂ λ₂ + y₃ λ₃ = cuspX v (u p) y`,
  `s = β(x)^{2‖p‖∞−1} s_J^{2−2‖p‖∞} = collarS v p y`,

a map `E2 × E2 → E4` from the filling square (layer parameter `p`, torus coordinate `y`) to the UHS
coordinates `(x, s)`.  On the collar `½ ≤ ‖p‖∞ ≤ 1` it is injective, and the proof has three
independent steps.

* **The cusp coordinate determines the torus coordinate.**  `(u, y) ↦ u σ_v + y₂λ₂ + y₃λ₃` is a
  linear isomorphism `ℝ × ℝ² → ℝ³` because `(σ_v, λ₂, λ₃) = (κ_{v,1} + b_vκ_{v,2} + c_vκ_{v,3},
  κ_{v,2}, κ_{v,3})` is a basis of `ℝ³`.  Hence `x` recovers `u(p)` and `y`
  (`Work.Cusp.cuspX_injOn`).

* **The height determines the layer parameter.**  With `b = β(x)` fixed, the height is
  `collarHeight t b = exp(2t(log b − log s_J) + (log s_J − log b))`, which is *strictly decreasing*
  in `t` as soon as `b < s_J` (`collarHeight_strictAntiOn`).  The ceiling always satisfies
  `0 < β x ≤ βMax = 3/2 < s_J = e^{1/2}` (`beta_pos`, `beta_le_max`, `betaMax_lt_sJ`), so the
  height `s` recovers `t = ‖p‖∞`.

* **The layer and perimeter parameters determine the point.**  `p ↦ (‖p‖∞, u(p))` is injective on
  the filling square `Sq = [-1,1]²` (`nrm_u_injOn`), and `nrm p ≤ 1` already forces `p ∈ Sq`.
-/
import Mathlib
import Submission.Work.Cusp.Basic
import Submission.Work.Cusp.cuspX_injOn
import Submission.Work.Cusp.nrm_u_injOn
import Submission.Work.Cusp.beta_le_max
import Submission.Work.Cusp.beta_pos
import Submission.Work.Cusp.betaMax_lt_sJ
import Submission.Work.Cusp.collarHeight_strictAntiOn

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


noncomputable section

namespace Work.Cusp

open scoped Real InnerProductSpace

/-! ### The coordinates of the outer chart -/

/-- The first three coordinates of `ThetaOuter v p y` are the cusp coordinates
`x = cuspX v (u p) y = u(p)σ_v + y₂λ₂ + y₃λ₃` of the point: they do not involve the height
`collarS`, which is the fourth coordinate. -/
theorem ThetaOuter_apply_cuspX (v : Fin 5) (p y : E2) (i : Fin 3) :
    (ThetaOuter v p y) (Fin.castSucc i) = cuspX v (u p) y i := by
  fin_cases i <;> simp [ThetaOuter]

/-- The fourth coordinate of `ThetaOuter v p y` is the collar height `collarS v p y`. -/
theorem ThetaOuter_apply_three (v : Fin 5) (p y : E2) :
    (ThetaOuter v p y) 3 = collarS v p y := by
  simp [ThetaOuter]

/-! ### Injectivity on the collar -/

/-- **The outer chart `Θ_v` is injective on the collar `½ ≤ ‖p‖∞ ≤ 1`.**  Since `Θ_v` is given in
the UHS coordinates `(x, s)`, the cusp coordinate `x` recovers `u(p)` and `y` (the map
`cuspX v` is injective) and the height `s = collarHeight ‖p‖∞ (β x)` recovers `‖p‖∞` (strict
monotonicity, because `β x < s_J`); finally `(‖p‖∞, u(p))` is a coordinate system on the filling
square. -/
theorem ThetaOuter_injOn (v : Fin 5) :
    Set.InjOn (fun z : E2 × E2 => ThetaOuter v z.1 z.2)
      {z | 1/2 ≤ nrm z.1 ∧ nrm z.1 ≤ 1} := by
  intro z1 hz1 z2 hz2 h
  obtain ⟨p1, y1⟩ := z1
  obtain ⟨p2, y2⟩ := z2
  change ThetaOuter v p1 y1 = ThetaOuter v p2 y2 at h
  -- `nrm p ≤ 1` already puts `p` in the filling square `Sq = [-1,1]²`.
  have hSq1 : p1 ∈ Sq :=
    ⟨le_trans (le_max_left |p1 0| |p1 1|) hz1.2, le_trans (le_max_right |p1 0| |p1 1|) hz1.2⟩
  have hSq2 : p2 ∈ Sq :=
    ⟨le_trans (le_max_left |p2 0| |p2 1|) hz2.2, le_trans (le_max_right |p2 0| |p2 1|) hz2.2⟩
  -- the two cusp coordinates and the two heights agree
  have hx : cuspX v (u p1) y1 = cuspX v (u p2) y2 := by
    ext i
    have h' := congrArg (fun w : E4 => w (Fin.castSucc i)) h
    simpa only [ThetaOuter_apply_cuspX] using h'
  have hs : collarS v p1 y1 = collarS v p2 y2 := by
    have h' := congrArg (fun w : E4 => w 3) h
    simpa only [ThetaOuter_apply_three] using h'
  -- the cusp coordinate recovers `u(p)` and `y`
  obtain ⟨hu, hy⟩ : u p1 = u p2 ∧ y1 = y2 := by
    have h' := cuspX_injOn v (Set.mem_univ (u p1, y1)) (Set.mem_univ (u p2, y2)) hx
    exact ⟨congrArg Prod.fst h', congrArg Prod.snd h'⟩
  -- the height recovers `‖p‖∞`
  have hn : nrm p1 = nrm p2 := by
    have hcol : collarHeight (nrm p1) (beta (cuspX v (u p1) y1))
        = collarHeight (nrm p2) (beta (cuspX v (u p1) y1)) := by
      have hs' := hs
      simp only [collarS] at hs'
      rw [← hu, ← hy] at hs'
      exact hs'
    exact (collarHeight_strictAntiOn _ (beta_pos _)
      (lt_of_le_of_lt (beta_le_max _) betaMax_lt_sJ)).injOn
      (Set.mem_univ _) (Set.mem_univ _) hcol
  -- the layer and perimeter parameters recover `p`
  have hp : p1 = p2 :=
    nrm_u_injOn hSq1 hSq2 (by ext <;> simp [hn, hu])
  rw [hp, hy]

end Work.Cusp
