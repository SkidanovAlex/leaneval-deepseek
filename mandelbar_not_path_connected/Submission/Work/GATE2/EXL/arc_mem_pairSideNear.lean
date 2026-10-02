import Mathlib
import Submission.Work.GATE2.Inputs
import Submission.Work.GATE2.EXL.nearArc_of_mem_pairSideNear
import Submission.Work.GATE2.EXL.shrinks_esc
import Submission.Work.ELTop.mem_pairSideNear_of_nearArc
import Submission.Work.ELNest.bAng_range

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open Classical Filter Set
open scoped Topology

set_option linter.unusedVariables false

noncomputable section

namespace Work.GATE2.EXL

/-!
# `Work.GATE2.EXL.arc_mem_pairSideNear`

The equipotential *arc* of the case (ii) exit loop: every ray point of an angle
`θ ∈ [θ₀, α₁)` at a level `t > 1`, where `θ₀` lies in the certificate window
`(βₙ, α₁) = (bAng n, α₁)` of the level-`n` nest, lies in **both** near sides
`pairSideNear P0` and `pairSideNear (Q n)`.

This is a pure angle-arithmetic statement on top of `Work.ELTop.mem_pairSideNear_of_nearArc`
(which turns "the angle lies in the near arc `(P.b, P.a + 1)`" into "the ray point lies in the
near side of `P`").  With the angle identifications of the certificate

* `P0 = (α₁, α₂)`     (`nest.P0_spec`),
* `Q n = (βₙ', βₙ + 1)` (`hQa`, `hQb`),

the near arcs are `(α₂, α₁ + 1)` for `P0` and `(βₙ + 1, βₙ' + 1)` for `Q n`, and

* `α₁ - 1 < βₙ < θ < α₁ < α₂ < βₙ'` (`bAng_range`) immediately gives
  `θ + 1 ∈ (α₂, α₁ + 1)` and `θ + 1 ∈ (βₙ + 1, βₙ' + 1)`.

The shift by `1` (a harmless `rayPt_add_int`) is what makes the *literal* interval membership
available even when `θ` lies below `α₂`: the near arc of `P0` from `α₂` to `α₁ + 1` wraps through
the angle `0`, and `θ ∈ (α₁ - 1, α₁)` is exactly `θ + 1 ∈ (α₂, α₁ + 1)`.
-/

theorem arc_mem_pairSideNear {c : ℂ} {φ : ℂ → ℂ} (hN : Work.EL.DynB c φ) (z₁ : ℂ)
    (Pa : Set ℂ) (nest : Work.EL.Z1Nest hN z₁ Pa)
    (hQa : ∀ n : ℕ, (nest.Q n).a = Work.ELNest.bAng' n)
    (hQb : ∀ n : ℕ, (nest.Q n).b = Work.ELNest.bAng n + 1)
    (n : ℕ) {θ₀ θ t : ℝ} (hθ₀ : θ₀ ∈ Set.Ioo (Work.ELNest.bAng n) Work.EL.alpha1)
    (hθ : θ ∈ Set.Ico θ₀ Work.EL.alpha1) (ht : 1 < t) :
    Work.EL.rayPt hN θ t ∈ Work.EL.pairSideNear nest.P0 ∧
      Work.EL.rayPt hN θ t ∈ Work.EL.pairSideNear (nest.Q n) := by
  -- ### angle arithmetic
  have hr := Work.ELNest.bAng_range n
  have hbpos : (0 : ℝ) < Work.ELNest.bAng n := hr.1.1
  have hα1eq : Work.EL.alpha1 = Work.ELNest.alpha1 := rfl
  have hα2eq : Work.EL.alpha2 = Work.ELNest.alpha2 := rfl
  have hα12 : Work.ELNest.alpha1 < Work.ELNest.alpha2 := by
    norm_num [Work.ELNest.alpha1, Work.ELNest.alpha2]
  have hP0ab : Work.EL.alpha1 < Work.EL.alpha2 := by
    rw [hα1eq, hα2eq]; exact hα12
  -- `α₁ < βₙ'`
  have hbAng' : Work.EL.alpha1 < Work.ELNest.bAng' n := by
    have h1 : Work.ELNest.alpha2 < Work.ELNest.bAng' n := hr.2.1
    rw [hα1eq]
    linarith
  -- the range of `θ`: `βₙ < θ < α₁`
  have hθlo : Work.ELNest.bAng n < θ := lt_of_lt_of_le hθ₀.1 hθ.1
  have hθhi : θ < Work.EL.alpha1 := hθ.2
  have hθpos : 0 < θ := lt_of_lt_of_le (lt_trans hbpos hθ₀.1) hθ.1
  have hα2lt1 : Work.EL.alpha2 < 1 := by norm_num [Work.EL.alpha2]
  -- the shift by `1` does not change the ray point
  have hper : Work.EL.rayPt hN (θ + 1) t = Work.EL.rayPt hN θ t := by
    have h := Work.ELTop.rayPt_add_int hN θ t 1
    simpa using h
  refine ⟨?_, ?_⟩
  · -- the near side of `P0 = (α₁, α₂)`, whose near arc is `(α₂, α₁ + 1)`
    have hab : nest.P0.a < nest.P0.b := by
      rw [nest.P0_spec.1, nest.P0_spec.2.1]; exact hP0ab
    have harc : θ + 1 ∈ Set.Ioo nest.P0.b (nest.P0.a + 1) := by
      rw [Set.mem_Ioo, nest.P0_spec.2.1, nest.P0_spec.1]
      exact ⟨by linarith, by linarith⟩
    have hmem : Work.EL.rayPt hN (θ + 1) t ∈ Work.EL.pairSideNear nest.P0 :=
      Work.ELTop.mem_pairSideNear_of_nearArc hN nest.P0 hab harc ht
    rwa [hper] at hmem
  · -- the near side of `Q n = (βₙ', βₙ + 1)`, whose near arc is `(βₙ + 1, βₙ' + 1)`
    have hab : (nest.Q n).a < (nest.Q n).b := by
      rw [hQa n, hQb n]
      exact bAng'_lt_bAng_add_one n
    have harc : θ + 1 ∈ Set.Ioo (nest.Q n).b ((nest.Q n).a + 1) := by
      rw [Set.mem_Ioo, hQa n, hQb n]
      exact ⟨by linarith, by linarith⟩
    have hmem : Work.EL.rayPt hN (θ + 1) t ∈ Work.EL.pairSideNear (nest.Q n) :=
      Work.ELTop.mem_pairSideNear_of_nearArc hN (nest.Q n) hab harc ht
    rwa [hper] at hmem

end Work.GATE2.EXL
