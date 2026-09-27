import Mathlib
import Submission.Work.Mostow.horSpec
import Submission.Work.Mostow.levYcFormula

/-!
# The flat action of a group acting cocompactly on a horosphere is orbitwise bounded

Let `ξ ∈ Sph n` be a boundary point, `D > 0` a level, and `G ≤ PO n 1` a subgroup whose
elements preserve the Busemann level `lev ξ ·` (`hlev`).  Suppose moreover that the action of
`G` on the level-`D` horosphere is *cocompact*: there is a compact `K` such that every point
`u` with `lev ξ u = D` is moved into `K` by some element of `G` (`hcoc`).

Then the induced flat action on the horosphere is bounded on orbits: there is a single constant
`R` such that, for every flat coordinate `y ∈ ξ^⊥`, some `g ∈ G` brings the point
`hptOf ξ y D` (the point of the horosphere of level `D` with flat coordinate `y`) to a point
whose normalised flat coordinate `yc ξ ·` has norm at most `R`.

The proof is a two-line compactness argument.  The coordinate map `v ↦ ‖yc ξ v‖` is continuous
(`lev ξ v > 0` everywhere on `Sph n`, so the inverse in `yc ξ v = (lev ξ v)⁻¹ • wc ξ v` is
harmless), hence bounded by some `R` on the compact `K`.  Given `y ⊥ ξ`, the point
`hptOf ξ y D` has level `D`, so `hcoc` moves it into `K`; the bound on `K` gives the claim.
No use is made of `hlev` beyond its role in the geometric setting.
-/

namespace Work.Mostow

open Submission.Mostow LeanEval.Geometry.MostowRigidity

set_option linter.unusedVariables false

theorem flatActCocompact (n : ℕ) (hI : Submission.Mostow.HypIsometryProp n)
    (ξ : Submission.Mostow.E n) (hξ : ξ ∈ Submission.Mostow.Sph n) (D : ℝ) (hD : 0 < D)
    (G : Subgroup (LeanEval.Geometry.MostowRigidity.PO n 1))
    (hlev : ∀ g ∈ G, ∀ u : Submission.Mostow.E n,
      Work.Mostow.lev ξ ((g : LeanEval.Geometry.MostowRigidity.PO n 1) • u) = Work.Mostow.lev ξ u)
    (hcoc : ∃ K : Set (Submission.Mostow.E n), IsCompact K ∧ ∀ u : Submission.Mostow.E n,
      Work.Mostow.lev ξ u = D → ∃ g : G, (g : LeanEval.Geometry.MostowRigidity.PO n 1) • u ∈ K) :
    ∃ R : ℝ, ∀ y : Submission.Mostow.E n, inner ℝ y ξ = 0 → ∃ g : G,
      ‖Work.Mostow.yc ξ ((g : LeanEval.Geometry.MostowRigidity.PO n 1) • Work.Mostow.hptOf ξ y D)‖ ≤ R := by
  -- `lev ξ ·` is continuous.
  have hlev_c : Continuous fun v : Submission.Mostow.E n => Work.Mostow.lev ξ v := by
    unfold Work.Mostow.lev Submission.Mostow.tpart; fun_prop
  -- the `ξ^⊥`-component is continuous.
  have hwc_c : Continuous fun v : Submission.Mostow.E n => Work.Mostow.wc ξ v := by
    unfold Work.Mostow.wc; fun_prop
  -- hence so is the norm of the flat coordinate (`lev ξ v > 0` everywhere).
  have hyc_c : Continuous fun v : Submission.Mostow.E n => ‖Work.Mostow.yc ξ v‖ := by
    have hyc : Continuous fun v : Submission.Mostow.E n => Work.Mostow.yc ξ v := by
      show Continuous fun v : Submission.Mostow.E n => (Work.Mostow.lev ξ v)⁻¹ • Work.Mostow.wc ξ v
      exact (hlev_c.inv₀ (fun v => ne_of_gt (Work.Mostow.lev_pos ξ hξ v))).smul hwc_c
    exact hyc.norm
  obtain ⟨K, hKc, hK⟩ := hcoc
  -- boundedness of `‖yc ξ ·‖` on the compact set `K`.
  obtain ⟨R, hR⟩ := hKc.exists_bound_of_continuousOn hyc_c.continuousOn
  refine ⟨R, fun y hy => ?_⟩
  -- `hptOf ξ y D` has level `D`, so `hcoc` moves it into `K`.
  obtain ⟨hg, hgle⟩ := hK (Work.Mostow.hptOf ξ y D)
    (Work.Mostow.hptOf_level ξ hξ D hD y hy).1
  exact ⟨hg, by simpa using hR ((hg : LeanEval.Geometry.MostowRigidity.PO n 1) • Work.Mostow.hptOf ξ y D) hgle⟩

end Work.Mostow
