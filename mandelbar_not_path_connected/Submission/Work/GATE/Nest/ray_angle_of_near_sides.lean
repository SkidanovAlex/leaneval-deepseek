/-
# `Work.GATE.Nest.ray_angle_of_near_sides` — the nest-angle lemma `A1`

A point `z` off the filled Julia set which lies in the *near side* of a co-landing pair cannot
have its external angle in the *closed far arc* of that pair: the far side of the pair is the
side through the far arc (`Work.EL.PairSides.paramRay_far`), and the two sides are disjoint
(`Work.EL.PairSides.disjoint`).

Here this is applied to two pairs whose angles nest around the two root angles
`α₁ = 371/1023 < α₂ = 404/1023`:

* `P0`, with angles `P0.a = α₁`, `P0.b = α₂`;
* `Q`, with angles `Q.a = β'`, `Q.b = β + 1`, where `0 < β < α₁ < α₂ < β' < 1`.

If `z ∉ K c` lies in *both* near sides, then the external angle `ϑ₀` of `z` (the representative
in `[0,1)` of the angle of the Böttcher coordinate) satisfies

* `ϑ₀ ∉ (α₁, α₂)`: an angle strictly between the two root angles would put the ray of `z` in the
  far side of `P0`, against `z ∈ pairSideNear P0`;
* `β ≤ ϑ₀`: otherwise the angle `ϑ₀ + 1` (the same ray, shifted by `1`; the ray of an angle is
  `1`-periodic, `paramRay_add_one`) lies in the far arc `(β', β + 1)` of `Q`, again putting the
  ray in the far side of `Q`, against `z ∈ pairSideNear Q`;
* `ϑ₀ ≤ β'`: an angle `> β'` is in the far arc of `Q`, the same contradiction.

Hence `ϑ₀ ∈ [β, α₁] ∪ [α₂, β']`, which is the conclusion.  This is the angular form `A1` of
§2.2 of the design (`Submission/Work/NOTES_LEAD_mandelbar_residuals.md`); it is used in
`Work.GATE.Nest.nest_angle_window` to turn the angle of the level-`n` nest pair into the
`δ`-windows of `α₁` and `α₂`.
-/
import Mathlib
import Submission.Work.ELRig.Defs
import Submission.Work.Top.mem_paramRay_extAngle

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

namespace Work.GATE.Nest

/-! ## Periodicity of the rays in the angle -/

/-- The ray point of level `t` is `1`-periodic in the angle: `rayPoint (θ + 1) t = rayPoint θ t`
(the exponential `exp (2 π i (θ + 1)) = exp (2 π i θ)`). -/
theorem rayPoint_add_one (θ t : ℝ) :
    Work.Top.NakaneData.rayPoint (θ + 1) t = Work.Top.NakaneData.rayPoint θ t := by
  rw [Work.Top.NakaneData.rayPoint, Work.Top.NakaneData.rayPoint]
  have h : (2 * (Real.pi : ℂ) * ((θ + 1 : ℝ) : ℂ) * Complex.I)
      = 2 * (Real.pi : ℂ) * (θ : ℂ) * Complex.I + 2 * (Real.pi : ℂ) * Complex.I := by
    push_cast; ring
  rw [h, Complex.exp_add, Complex.exp_two_pi_mul_I, mul_one]

/-- The parameter ray depends on the angle only modulo `ℤ`: `paramRay (θ + 1) = paramRay θ`. -/
theorem paramRay_add_one {c : ℂ} {φ : ℂ → ℂ} (hN : Work.EL.DynB c φ) (θ : ℝ) :
    Work.EL.paramRay hN (θ + 1) = Work.EL.paramRay hN θ := by
  ext z
  constructor
  · rintro ⟨hzK, t, ht, hΦ⟩
    exact ⟨hzK, t, ht, by rw [rayPoint_add_one θ t] at hΦ; exact hΦ⟩
  · rintro ⟨hzK, t, ht, hΦ⟩
    exact ⟨hzK, t, ht, by rw [rayPoint_add_one θ t]; exact hΦ⟩

/-! ## Angles in an honest interval are in the corresponding cyclic arc -/

/-- An angle `θ` in the honest interval `(a, b)`, with `b < a + 1`, lies in the open cyclic arc
`(a, b)`. -/
theorem inArc_of_mem_Ioo {θ a b : ℝ} (h1 : a < θ) (h2 : θ < b) (h3 : b < a + 1) :
    Work.EL.InArc θ a b := by
  rw [Work.EL.InArc]
  have harc : Work.EL.arcLen a b = b - a := by
    rw [Work.EL.arcLen, Int.fract_eq_self.mpr ⟨by linarith, by linarith⟩]
  have hf : Int.fract (θ - a) = θ - a :=
    Int.fract_eq_self.mpr ⟨by linarith, by linarith⟩
  rw [hf, harc]
  exact ⟨by linarith, by linarith⟩

/-! ## The nest-angle lemma -/

theorem ray_angle_of_near_sides {c : ℂ} {φ : ℂ → ℂ} (hN : Work.EL.DynB c φ)
    (P0 Q : Work.EL.CoPair hN) {β β' : ℝ}
    (hP0a : P0.a = Work.EL.alpha1) (hP0b : P0.b = Work.EL.alpha2)
    (hQa : Q.a = β') (hQb : Q.b = β + 1)
    (hβ : 0 < β) (hβ₁ : β < Work.EL.alpha1) (h₁₂ : Work.EL.alpha1 < Work.EL.alpha2)
    (h₂β' : Work.EL.alpha2 < β') (hβ'1 : β' < 1)
    (hPs : Work.EL.PairSides hN P0) (hQs : Work.EL.PairSides hN Q)
    (hcover : ∀ z ∉ Work.EL.K c, ∃ ϑ : ℝ, z ∈ Work.EL.paramRay hN ϑ)
    {z : ℂ} (hzK : z ∉ Work.EL.K c)
    (hzP : z ∈ Work.EL.pairSideNear P0) (hzQ : z ∈ Work.EL.pairSideNear Q) :
    ∃ ϑ : ℝ, z ∈ Work.EL.paramRay hN ϑ ∧
      ((β ≤ ϑ ∧ ϑ ≤ Work.EL.alpha1) ∨ (Work.EL.alpha2 ≤ ϑ ∧ ϑ ≤ β')) := by
  -- the external angle of `z`, in `[0, 1)`
  let ϑ₀ : ℝ := Work.Top.NakaneData.extAngle (Work.EL.dynPhi c φ) z
  have hmem : z ∈ Work.EL.paramRay hN ϑ₀ := Work.Top.mem_paramRay_extAngle hN hzK
  have hϑ0 : 0 ≤ ϑ₀ := (Work.Top.NakaneData.extAngle_mem_Ico (Work.EL.dynPhi c φ) z).1
  have hϑ1 : ϑ₀ < 1 := (Work.Top.NakaneData.extAngle_mem_Ico (Work.EL.dynPhi c φ) z).2
  have hββ' : β < β' := lt_trans hβ₁ (lt_trans h₁₂ h₂β')
  have hα₁0 : 0 < Work.EL.alpha1 := lt_trans hβ hβ₁
  have hα₂1 : Work.EL.alpha2 < 1 := lt_trans h₂β' hβ'1
  -- the far arc of a pair is disjoint from the near side
  have hnotInArcP : ∀ θ : ℝ, z ∈ Work.EL.paramRay hN θ → ¬ Work.EL.InArc θ P0.a P0.b := by
    intro θ hθ hIn
    exact Set.disjoint_left.mp hPs.disjoint (hPs.paramRay_far θ hIn hθ) hzP
  have hnotInArcQ : ∀ θ : ℝ, z ∈ Work.EL.paramRay hN θ → ¬ Work.EL.InArc θ Q.a Q.b := by
    intro θ hθ hIn
    exact Set.disjoint_left.mp hQs.disjoint (hQs.paramRay_far θ hIn hθ) hzQ
  -- `β ≤ ϑ₀`: otherwise the ray, seen at the angle `ϑ₀ + 1`, lies in the far arc of `Q`
  have hβle : β ≤ ϑ₀ := by
    by_contra hlt
    rw [not_le] at hlt
    have hIn : Work.EL.InArc (ϑ₀ + 1) Q.a Q.b := by
      rw [hQa, hQb]
      exact inArc_of_mem_Ioo (by linarith) (by linarith) (by linarith)
    have hmem1 : z ∈ Work.EL.paramRay hN (ϑ₀ + 1) := by
      rw [paramRay_add_one hN ϑ₀]; exact hmem
    exact hnotInArcQ (ϑ₀ + 1) hmem1 hIn
  -- `ϑ₀ ≤ β'`
  have hϑβ' : ϑ₀ ≤ β' := by
    by_contra hlt
    rw [not_le] at hlt
    have hIn : Work.EL.InArc ϑ₀ Q.a Q.b := by
      rw [hQa, hQb]
      exact inArc_of_mem_Ioo hlt (by linarith) (by linarith)
    exact hnotInArcQ ϑ₀ hmem hIn
  -- `ϑ₀ ∉ (α₁, α₂)`
  have hα : ϑ₀ ≤ Work.EL.alpha1 ∨ Work.EL.alpha2 ≤ ϑ₀ := by
    by_contra hcon
    rw [not_or] at hcon
    obtain ⟨h1, h2⟩ := hcon
    rw [not_le] at h1 h2
    have hIn : Work.EL.InArc ϑ₀ P0.a P0.b := by
      rw [hP0a, hP0b]
      exact inArc_of_mem_Ioo h1 h2 (by linarith)
    exact hnotInArcP ϑ₀ hmem hIn
  rcases hα with hα | hα
  · exact ⟨ϑ₀, hmem, Or.inl ⟨hβle, hα⟩⟩
  · exact ⟨ϑ₀, hmem, Or.inr ⟨hα, hϑβ'⟩⟩

end Work.GATE.Nest
