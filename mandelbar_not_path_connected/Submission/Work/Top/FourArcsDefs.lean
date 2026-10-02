/-
# Gluing four arcs end to end: the parametrisation

This file contains the technical definition underlying `Work.Top.four_arcs_jordan`: given four
continuous maps `γ₁ γ₂ γ₃ γ₄ : C(unitInterval, ℂ)`, the map

`fourArcs γ₁ γ₂ γ₃ γ₄ : ℝ → ℂ`

runs through `γ₁` on `[0, 1/4]`, `γ₂` on `[1/4, 1/2]`, `γ₃` on `[1/2, 3/4]` and `γ₄` on
`[3/4, 1]` (each reparametrised affinely, with the argument clamped into `unitInterval`; outside
`[0,1]` the formula is irrelevant).

The point of this definition is that it is *continuous on all of `ℝ`* as soon as consecutive
pieces match up (`γ₁ 1 = γ₂ 0`, `γ₂ 1 = γ₃ 0`, `γ₃ 1 = γ₄ 0`), so that
`AddCircle.liftIco 0 1 (fourArcs …)` (which agrees with `fourArcs` on `[0,1)`) is a continuous
map of the circle; if moreover `γ₄ 1 = γ₁ 0`, this map is a closed loop.
-/
import Mathlib
import Submission.Work.Top.Defs
import Submission.Work.Top.Jordan

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open Classical Set
open scoped Topology

noncomputable section

namespace Work.Top

/-! ## The clamping map `ℝ → unitInterval` -/

/-- The projection of `ℝ` onto `unitInterval = [0,1]`, sending a real number to the nearest
point of `[0,1]`. -/
def clamp (x : ℝ) : ℝ := max 0 (min x 1)

theorem clamp_mem (x : ℝ) : clamp x ∈ unitInterval := by
  rw [unitInterval, Set.mem_Icc]
  exact ⟨le_max_left _ _, max_le zero_le_one (min_le_right _ _)⟩

theorem clamp_eq_self {x : ℝ} (h : x ∈ unitInterval) : clamp x = x := by
  rw [unitInterval, Set.mem_Icc] at h
  simp only [clamp, min_eq_left h.2, max_eq_right h.1]

theorem continuous_clamp : Continuous clamp := by
  show Continuous fun x : ℝ => max 0 (min x 1)
  fun_prop

/-! ## Applying an arc to a real parameter -/

/-- The arc `γ` evaluated at the real number `c`, its argument being clamped into
`unitInterval` first.  On `[0,1]` this is just `γ`. -/
def arcPt (γ : C(unitInterval, ℂ)) (c : ℝ) : ℂ := γ ⟨clamp c, clamp_mem c⟩

theorem continuous_arcPt (γ : C(unitInterval, ℂ)) : Continuous (arcPt γ) :=
  γ.continuous.comp (Continuous.subtype_mk continuous_clamp clamp_mem)

theorem arcPt_of_mem (γ : C(unitInterval, ℂ)) {c : ℝ} (h : c ∈ unitInterval) :
    arcPt γ c = γ ⟨c, h⟩ :=
  congrArg γ (Subtype.ext (clamp_eq_self h))

theorem arcPt_zero (γ : C(unitInterval, ℂ)) : arcPt γ 0 = γ 0 :=
  arcPt_of_mem γ (by rw [unitInterval, Set.mem_Icc]; norm_num)

theorem arcPt_one (γ : C(unitInterval, ℂ)) : arcPt γ 1 = γ 1 :=
  arcPt_of_mem γ (by rw [unitInterval, Set.mem_Icc]; norm_num)

theorem arcPt_mem_range (γ : C(unitInterval, ℂ)) (c : ℝ) : arcPt γ c ∈ Set.range γ :=
  ⟨⟨clamp c, clamp_mem c⟩, rfl⟩

/-! ## The four-arc parametrisation -/

/-- The concatenation of the four arcs `γ₁ γ₂ γ₃ γ₄` as a map `ℝ → ℂ`: on `[0,1/4]` it is `γ₁`
(reparametrised by `t ↦ 4t`), on `[1/4,1/2]` it is `γ₂` (reparametrised by `t ↦ 4t - 1`), on
`[1/2,3/4]` it is `γ₃` (reparametrised by `t ↦ 4t - 2`) and on `[3/4,1]` it is `γ₄`
(reparametrised by `t ↦ 4t - 3`). -/
def fourArcs (γ₁ γ₂ γ₃ γ₄ : C(unitInterval, ℂ)) (t : ℝ) : ℂ :=
  if t ≤ 1/4 then arcPt γ₁ (4*t)
  else if t ≤ 1/2 then arcPt γ₂ (4*t-1)
  else if t ≤ 3/4 then arcPt γ₃ (4*t-2)
  else arcPt γ₄ (4*t-3)

/-- The concatenation of four arcs whose consecutive endpoints match is continuous. -/
theorem continuous_fourArcs {γ₁ γ₂ γ₃ γ₄ : C(unitInterval, ℂ)}
    (h₁₂ : γ₁ 1 = γ₂ 0) (h₂₃ : γ₂ 1 = γ₃ 0) (h₃₄ : γ₃ 1 = γ₄ 0) :
    Continuous (fourArcs γ₁ γ₂ γ₃ γ₄) := by
  have h34 : Continuous fun t : ℝ =>
      if t ≤ 3/4 then arcPt γ₃ (4*t-2) else arcPt γ₄ (4*t-3) :=
    Continuous.if_le (continuous_arcPt γ₃ |>.comp (by fun_prop))
      (continuous_arcPt γ₄ |>.comp (by fun_prop)) continuous_id continuous_const
      (by intro t ht; subst ht; norm_num; rw [arcPt_one, arcPt_zero]; exact h₃₄)
  have h234 : Continuous fun t : ℝ => if t ≤ 1/2 then arcPt γ₂ (4*t-1)
      else (if t ≤ 3/4 then arcPt γ₃ (4*t-2) else arcPt γ₄ (4*t-3)) :=
    Continuous.if_le (continuous_arcPt γ₂ |>.comp (by fun_prop)) h34 continuous_id continuous_const
      (by intro t ht; subst ht
          norm_num [show (1:ℝ)/2 ≤ 3/4 by norm_num]
          rw [arcPt_one, arcPt_zero]; exact h₂₃)
  exact Continuous.if_le (continuous_arcPt γ₁ |>.comp (by fun_prop)) h234 continuous_id
    continuous_const
    (by intro t ht; subst ht
        norm_num [show (1:ℝ)/4 ≤ 1/2 by norm_num]
        rw [arcPt_one, arcPt_zero]; exact h₁₂)

/-! ## The four branches -/

theorem fourArcs_eq_arcPt₁ (γ₁ γ₂ γ₃ γ₄ : C(unitInterval, ℂ)) {t : ℝ} (ht : t ≤ 1/4) :
    fourArcs γ₁ γ₂ γ₃ γ₄ t = arcPt γ₁ (4*t) := by
  simp only [fourArcs]
  rw [ite_eq_left ht]

theorem fourArcs_eq_arcPt₂ (γ₁ γ₂ γ₃ γ₄ : C(unitInterval, ℂ)) {t : ℝ}
    (h1 : 1/4 < t) (h2 : t ≤ 1/2) :
    fourArcs γ₁ γ₂ γ₃ γ₄ t = arcPt γ₂ (4*t-1) := by
  simp only [fourArcs]
  rw [ite_eq_right (not_le.mpr h1), ite_eq_left h2]

theorem fourArcs_eq_arcPt₃ (γ₁ γ₂ γ₃ γ₄ : C(unitInterval, ℂ)) {t : ℝ}
    (h1 : 1/2 < t) (h2 : t ≤ 3/4) :
    fourArcs γ₁ γ₂ γ₃ γ₄ t = arcPt γ₃ (4*t-2) := by
  simp only [fourArcs]
  rw [ite_eq_right (not_le.mpr (by linarith : (1:ℝ)/4 < t)), ite_eq_right (not_le.mpr h1),
    ite_eq_left h2]

theorem fourArcs_eq_arcPt₄ (γ₁ γ₂ γ₃ γ₄ : C(unitInterval, ℂ)) {t : ℝ} (h1 : 3/4 < t) :
    fourArcs γ₁ γ₂ γ₃ γ₄ t = arcPt γ₄ (4*t-3) := by
  simp only [fourArcs]
  rw [ite_eq_right (not_le.mpr (by linarith : (1:ℝ)/4 < t)),
    ite_eq_right (not_le.mpr (by linarith : (1:ℝ)/2 < t)), ite_eq_right (not_le.mpr h1)]

theorem fourArcs_zero (γ₁ γ₂ γ₃ γ₄ : C(unitInterval, ℂ)) :
    fourArcs γ₁ γ₂ γ₃ γ₄ 0 = γ₁ 0 := by
  rw [fourArcs_eq_arcPt₁ _ _ _ _ (by norm_num), show (4:ℝ)*0 = 0 by norm_num, arcPt_zero]

theorem fourArcs_one (γ₁ γ₂ γ₃ γ₄ : C(unitInterval, ℂ)) :
    fourArcs γ₁ γ₂ γ₃ γ₄ 1 = γ₄ 1 := by
  rw [fourArcs_eq_arcPt₄ _ _ _ _ (by norm_num), show (4:ℝ)*1 - 3 = 1 by norm_num, arcPt_one]

end Work.Top
