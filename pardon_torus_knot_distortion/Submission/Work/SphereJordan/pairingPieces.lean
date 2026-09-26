import Mathlib
import Submission.Work.SphereJordan.pairingSetup
import Submission.Work.SphereJordan.argIncrement
import Submission.Work.Smooth.SphereJordan.windNumberCircleCurve

/-!
# The four-arc curves as parameter intervals

This module rewrites the loops of the four four-arc curves of the two-cuts configuration as
increments over parameter intervals (`Work.SphereJordan.incOn`) of the simple model curves: the
outer circle, the two crosscut lines and `γ` itself.  The three identities of
`Work.SphereJordan.windNumber_pairing_identities` then become bookkeeping with
`Work.SphereJordan.incOn_add` and `Work.SphereJordan.incOn_rev`.
-/

open Set
open Classical

namespace Work.SphereJordan

noncomputable section

variable {γ : Work.Smooth.Jordan.PlaneCurve}

/-! ## Bridging `incr'` with `pathIncTot` -/

theorem incr'_eq_pathIncTot (c : C(unitInterval, ℂ)) : incr' c = pathIncTot c := by
  by_cases h : ∀ t, c t ≠ 0
  · rw [incr'_eq h, pathIncTot_of_ne c h]
    rfl
  · rw [incr'_zero h, pathIncTot, dif_neg h]

/-- Two paths that agree pointwise have the same increment over the corresponding intervals. -/
theorem incOn_eq_of_forall {γ δ : ℝ → ℂ} (hγ : Continuous γ) (hδ : Continuous δ) {z : ℂ}
    {a b c d : ℝ} (h : ∀ t : unitInterval, γ (a + (t : ℝ) * (b - a)) = δ (c + (t : ℝ) * (d - c))) :
    incOn γ hγ z a b = incOn δ hδ z c d := by
  rw [incOn, incOn]
  refine pathIncTot_congr (fun t => ?_)
  simp only [ContinuousMap.coe_mk]
  rw [h t]

/-! ## The model curves -/

section Model

variable {hh : Work.Smooth.SphereJordan.PlaneHypothesis} {hs : γ.IsSimple}
  {hball : ∀ θ : ℝ, ‖γ.γ θ‖ < 1} {S : Work.Smooth.Jordan.PlaneSchoenflies γ}

/-- The outer circle, traversed counter-clockwise from `cutDir S` with parameter equal to the
angle. -/
def outerC (S : Work.Smooth.Jordan.PlaneSchoenflies γ) : ℝ → ℂ :=
  fun r => Work.Smooth.SphereJordan.cutDir S * Complex.exp (((r : ℂ)) * Complex.I)

theorem continuous_outerC (S : Work.Smooth.Jordan.PlaneSchoenflies γ) : Continuous (outerC S) := by
  unfold outerC
  fun_prop

theorem outerC_periodic (S : Work.Smooth.Jordan.PlaneSchoenflies γ) :
    Function.Periodic (outerC S) (2 * Real.pi) := by
  intro r
  unfold outerC
  rw [show ((r + 2 * Real.pi : ℝ) : ℂ) = (r : ℂ) + ((2 * Real.pi : ℝ) : ℂ) from by
      push_cast; ring,
    add_mul, Complex.exp_add]
  rw [show Complex.exp ((((2 * Real.pi : ℝ)) : ℂ) * Complex.I) = 1 from by
    rw [show ((((2 * Real.pi : ℝ)) : ℂ)) = (2 : ℂ) * (Real.pi : ℂ) from by push_cast; ring]
    exact Complex.exp_two_pi_mul_I]
  ring

/-- The straight line carrying the first crosscut as its `[0,1]`-arc. -/
def cutC₁ (H : SpanHyp hh hs hball S) : ℝ → ℂ :=
  fun r => (Work.Smooth.SphereJordan.base S : ℂ) +
    (((H.s₁ + r * (H.t₁ - H.s₁) : ℝ)) : ℂ) * Work.Smooth.SphereJordan.cutDir S

/-- The straight line carrying the second crosscut as its `[0,1]`-arc. -/
def cutC₂ (H : SpanHyp hh hs hball S) : ℝ → ℂ :=
  fun r => (Work.Smooth.SphereJordan.base S : ℂ) -
    (((H.s₂ + r * (H.t₂ - H.s₂) : ℝ)) : ℂ) * Work.Smooth.SphereJordan.cutDir S

theorem continuous_cutC₁ (H : SpanHyp hh hs hball S) : Continuous (cutC₁ H) := by
  unfold cutC₁; fun_prop

theorem continuous_cutC₂ (H : SpanHyp hh hs hball S) : Continuous (cutC₂ H) := by
  unfold cutC₂; fun_prop

theorem cutC₁_apply (H : SpanHyp hh hs hball S) (r : ℝ) :
    cutC₁ H r = Work.Smooth.SphereJordan.tgtCut₁ S H.t₁ H.s₁ r := rfl

theorem cutC₂_apply (H : SpanHyp hh hs hball S) (r : ℝ) :
    cutC₂ H r = Work.Smooth.SphereJordan.tgtCut₂ S H.t₂ H.s₂ r := rfl

end Model

/-! ## Elementary constants -/

theorem pi_sub_pi_half_nonneg : (0 : ℝ) ≤ Real.pi - Real.pi / 2 := by linarith [Real.pi_pos]

theorem three_pi_half_sub_pi_nonneg : (0 : ℝ) ≤ 3 * Real.pi / 2 - Real.pi := by
  linarith [Real.pi_pos]

theorem two_pi_sub_three_pi_half_nonneg : (0 : ℝ) ≤ 2 * Real.pi - 3 * Real.pi / 2 := by
  linarith [Real.pi_pos]

theorem pi_half_div_self : Real.pi / 2 / (Real.pi / 2) = 1 :=
  div_self (by positivity : (Real.pi / 2 : ℝ) ≠ 0)

theorem pi_sub_pi_half_div : (Real.pi - Real.pi / 2) / (Real.pi / 2) = 1 := by
  rw [show Real.pi - Real.pi / 2 = Real.pi / 2 from by ring,
    div_self (by positivity : (Real.pi / 2 : ℝ) ≠ 0)]

theorem three_pi_half_sub_pi_div : (3 * Real.pi / 2 - Real.pi) / (Real.pi / 2) = 1 := by
  rw [show 3 * Real.pi / 2 - Real.pi = Real.pi / 2 from by ring,
    div_self (by positivity : (Real.pi / 2 : ℝ) ≠ 0)]

theorem perPt_two_pi : Work.Smooth.SphereJordan.perPt (2 * Real.pi) = 0 := by
  rw [Work.Smooth.SphereJordan.perPt, div_self (by positivity : (2 * Real.pi : ℝ) ≠ 0),
    Int.floor_one]
  norm_num

/-! ## The ten quarter intervals -/

section Intervals

variable {hh : Work.Smooth.SphereJordan.PlaneHypothesis} {hs : γ.IsSimple}
  {hball : ∀ θ : ℝ, ‖γ.γ θ‖ < 1} {S : Work.Smooth.Jordan.PlaneSchoenflies γ}

/-- The first quarter of the upper curve is the upper outer semicircle. -/
theorem up_incr_first (H : SpanHyp hh hs hball S) (b : Bool) (x : ℂ) :
    incOn (H.upPC b).γ (H.upPC b).cont x 0 (Real.pi / 2) =
      incOn (outerC S) (continuous_outerC S) x 0 Real.pi := by
  refine incOn_eq_of_forall _ _ (fun t => ?_)
  show Work.Smooth.SphereJordan.tgtUpB S H.t₁ H.s₁ H.t₂ H.s₂ b H.θ₁ H.θ₂
      (0 + (t : ℝ) * (Real.pi / 2 - 0)) = outerC S (0 + (t : ℝ) * (Real.pi - 0))
  set σ : ℝ := (t : ℝ) * (Real.pi / 2) with hσdef
  have hσmem : σ ∈ Set.Ico (0 : ℝ) (2 * Real.pi) :=
    ⟨by rw [hσdef]; exact mul_nonneg t.2.1 (by positivity),
      by rw [hσdef]; nlinarith [t.2.2, Real.pi_pos]⟩
  have hle : σ ≤ Real.pi / 2 := by rw [hσdef]; nlinarith [t.2.2, Real.pi_pos]
  rw [show (0 : ℝ) + (t : ℝ) * (Real.pi / 2 - 0) = σ from by rw [hσdef]; ring,
    show (0 : ℝ) + (t : ℝ) * (Real.pi - 0) = (t : ℝ) * Real.pi from by ring,
    Work.SphereJordan.tgtUpB_eq, Work.SphereJordan.perPt_self hσmem,
    Work.SphereJordan.tgtUpBun, if_pos hle]
  unfold Work.Smooth.SphereJordan.srcOuterUp outerC
  have harg : (((Real.pi * (σ / (Real.pi / 2)) : ℝ)) : ℂ) = (((t : ℝ) * Real.pi : ℝ)) := by
    rw [hσdef]
    have h2 : (t : ℝ) * (Real.pi / 2) / (Real.pi / 2) = (t : ℝ) :=
      div_eq_iff (by positivity : (Real.pi / 2 : ℝ) ≠ 0)
        |>.mpr (by ring)
    rw [h2]; push_cast; ring
  rw [harg]

/-- The second quarter of the upper curve is the second crosscut, inward. -/
theorem up_incr_second (H : SpanHyp hh hs hball S) (b : Bool) (x : ℂ) :
    incOn (H.upPC b).γ (H.upPC b).cont x (Real.pi / 2) Real.pi =
      incOn (cutC₂ H) (continuous_cutC₂ H) x 0 1 := by
  refine incOn_eq_of_forall _ _ (fun t => ?_)
  show Work.Smooth.SphereJordan.tgtUpB S H.t₁ H.s₁ H.t₂ H.s₂ b H.θ₁ H.θ₂
      (Real.pi / 2 + (t : ℝ) * (Real.pi - Real.pi / 2)) = cutC₂ H (0 + (t : ℝ) * (1 - 0))
  set σ : ℝ := Real.pi / 2 + (t : ℝ) * (Real.pi - Real.pi / 2) with hσdef
  have hσmem : σ ∈ Set.Ico (0 : ℝ) (2 * Real.pi) :=
    ⟨by rw [hσdef]; nlinarith [t.2.1, Real.pi_pos],
      by rw [hσdef]; nlinarith [t.2.2, Real.pi_pos]⟩
  have hσle : σ ≤ Real.pi := by rw [hσdef]; nlinarith [t.2.2, Real.pi_pos]
  rw [show (0 : ℝ) + (t : ℝ) * (1 - 0) = (t : ℝ) from by ring,
    Work.SphereJordan.tgtUpB_eq, Work.SphereJordan.perPt_self hσmem]
  by_cases h : σ ≤ Real.pi / 2
  · rw [Work.SphereJordan.tgtUpBun, if_pos h]
    have hσ : σ = Real.pi / 2 := le_antisymm h (by rw [hσdef]; nlinarith [t.2.1, Real.pi_pos])
    have ht : (t : ℝ) = 0 := by rw [hσdef] at hσ; nlinarith [hσ, t.2.1, Real.pi_pos]
    rw [show σ / (Real.pi / 2) = 1 from by rw [hσ, pi_half_div_self],
      Work.SphereJordan.srcOuterUp_one]
    unfold cutC₂
    rw [ht, show H.s₂ + (0 : ℝ) * (H.t₂ - H.s₂) = H.s₂ from by ring, ← H.hout₂]
  · rw [Work.SphereJordan.tgtUpBun, if_neg h, if_pos hσle]
    have harg : (σ - Real.pi / 2) / (Real.pi / 2) = (t : ℝ) := by
      rw [hσdef]; field_simp; ring
    rw [harg]
    rfl

/-- The third quarter of the upper curve, `b = true`: the arc from `θ₂` to `θ₁`. -/
theorem up_incr_third_true (H : SpanHyp hh hs hball S) (x : ℂ) :
    incOn (H.upPC true).γ (H.upPC true).cont x Real.pi (3 * Real.pi / 2) =
      incOn γ.γ γ.cont x H.θ₂ H.θ₁ := by
  refine incOn_eq_of_forall _ _ (fun t => ?_)
  show Work.Smooth.SphereJordan.tgtUpB S H.t₁ H.s₁ H.t₂ H.s₂ true H.θ₁ H.θ₂
      (Real.pi + (t : ℝ) * (3 * Real.pi / 2 - Real.pi)) =
    γ.γ (H.θ₂ + (t : ℝ) * (H.θ₁ - H.θ₂))
  set σ : ℝ := Real.pi + (t : ℝ) * (3 * Real.pi / 2 - Real.pi) with hσdef
  have hσmem : σ ∈ Set.Ico (0 : ℝ) (2 * Real.pi) :=
    ⟨by rw [hσdef]; nlinarith [t.2.1, Real.pi_pos],
      by rw [hσdef]; nlinarith [t.2.2, Real.pi_pos]⟩
  have hσ3 : σ ≤ 3 * Real.pi / 2 := by rw [hσdef]; nlinarith [t.2.2, Real.pi_pos]
  have hσ2 : σ ≤ Real.pi / 2 → False := by
    intro h
    have h1 : Real.pi ≤ σ := by
      rw [hσdef]
      have hp := mul_nonneg t.2.1 three_pi_half_sub_pi_nonneg
      linarith [hp]
    linarith [h, h1, Real.pi_pos]
  rw [Work.SphereJordan.tgtUpB_eq, Work.SphereJordan.perPt_self hσmem]
  by_cases h : σ ≤ Real.pi
  · rw [Work.SphereJordan.tgtUpBun, if_neg hσ2, if_pos h]
    have hσ : σ = Real.pi := le_antisymm h (by rw [hσdef]; nlinarith [t.2.1, Real.pi_pos])
    have ht : (t : ℝ) = 0 := by rw [hσdef] at hσ; nlinarith [hσ, t.2.1, Real.pi_pos]
    rw [show (σ - Real.pi / 2) / (Real.pi / 2) = 1 from by
        rw [hσ, pi_sub_pi_half_div],
      Work.SphereJordan.tgtCut₂_one,
      show H.θ₂ + (t : ℝ) * (H.θ₁ - H.θ₂) = H.θ₂ from by rw [ht]; ring, ← H.hθ₂]
  · rw [Work.SphereJordan.tgtUpBun, if_neg hσ2, if_neg h, if_pos hσ3]
    have harg : (σ - Real.pi) / (Real.pi / 2) = (t : ℝ) := by
      rw [hσdef]; field_simp; ring
    rw [harg]
    rfl

/-- The third quarter of the upper curve, `b = false`: the complementary arc from `θ₂` down to
`θ₁ - 2π`. -/
theorem up_incr_third_false (H : SpanHyp hh hs hball S) (x : ℂ) :
    incOn (H.upPC false).γ (H.upPC false).cont x Real.pi (3 * Real.pi / 2) =
      incOn γ.γ γ.cont x H.θ₂ (H.θ₁ - 2 * Real.pi) := by
  refine incOn_eq_of_forall _ _ (fun t => ?_)
  show Work.Smooth.SphereJordan.tgtUpB S H.t₁ H.s₁ H.t₂ H.s₂ false H.θ₁ H.θ₂
      (Real.pi + (t : ℝ) * (3 * Real.pi / 2 - Real.pi)) =
    γ.γ (H.θ₂ + (t : ℝ) * (H.θ₁ - 2 * Real.pi - H.θ₂))
  set σ : ℝ := Real.pi + (t : ℝ) * (3 * Real.pi / 2 - Real.pi) with hσdef
  have hσmem : σ ∈ Set.Ico (0 : ℝ) (2 * Real.pi) :=
    ⟨by rw [hσdef]; nlinarith [t.2.1, Real.pi_pos],
      by rw [hσdef]; nlinarith [t.2.2, Real.pi_pos]⟩
  have hσ3 : σ ≤ 3 * Real.pi / 2 := by rw [hσdef]; nlinarith [t.2.2, Real.pi_pos]
  have hσ2 : σ ≤ Real.pi / 2 → False := by
    intro h
    have h1 : Real.pi ≤ σ := by
      rw [hσdef]
      have hp := mul_nonneg t.2.1 three_pi_half_sub_pi_nonneg
      linarith [hp]
    linarith [h, h1, Real.pi_pos]
  rw [Work.SphereJordan.tgtUpB_eq, Work.SphereJordan.perPt_self hσmem]
  by_cases h : σ ≤ Real.pi
  · rw [Work.SphereJordan.tgtUpBun, if_neg hσ2, if_pos h]
    have hσ : σ = Real.pi := le_antisymm h (by rw [hσdef]; nlinarith [t.2.1, Real.pi_pos])
    have ht : (t : ℝ) = 0 := by rw [hσdef] at hσ; nlinarith [hσ, t.2.1, Real.pi_pos]
    rw [show (σ - Real.pi / 2) / (Real.pi / 2) = 1 from by
        rw [hσ, pi_sub_pi_half_div],
      Work.SphereJordan.tgtCut₂_one,
      show H.θ₂ + (t : ℝ) * (H.θ₁ - 2 * Real.pi - H.θ₂) = H.θ₂ from by rw [ht]; ring,
      ← H.hθ₂]
  · rw [Work.SphereJordan.tgtUpBun, if_neg hσ2, if_neg h, if_pos hσ3,
      if_neg (by simp : ¬ (false = true))]
    have harg : (σ - Real.pi) / (Real.pi / 2) = (t : ℝ) := by
      rw [hσdef]; field_simp; ring
    rw [harg]
    ring_nf

/-- The fourth quarter of the upper curve is the first crosscut, outward. -/
theorem up_incr_fourth (H : SpanHyp hh hs hball S) (b : Bool) (x : ℂ) :
    incOn (H.upPC b).γ (H.upPC b).cont x (3 * Real.pi / 2) (2 * Real.pi) =
      incOn (cutC₁ H) (continuous_cutC₁ H) x 1 0 := by
  refine incOn_eq_of_forall _ _ (fun t => ?_)
  show Work.Smooth.SphereJordan.tgtUpB S H.t₁ H.s₁ H.t₂ H.s₂ b H.θ₁ H.θ₂
      (3 * Real.pi / 2 + (t : ℝ) * (2 * Real.pi - 3 * Real.pi / 2)) =
    cutC₁ H (1 + (t : ℝ) * (0 - 1))
  set σ : ℝ := 3 * Real.pi / 2 + (t : ℝ) * (2 * Real.pi - 3 * Real.pi / 2) with hσdef
  have hσle : σ ≤ 2 * Real.pi := by rw [hσdef]; nlinarith [t.2.2, Real.pi_pos]
  have hσ2 : σ ≤ Real.pi / 2 → False := by
    intro h
    have h1 : 3 * Real.pi / 2 ≤ σ := by
      rw [hσdef]
      have hp := mul_nonneg t.2.1 two_pi_sub_three_pi_half_nonneg
      linarith [hp]
    linarith [h, h1, Real.pi_pos]
  have hσπ : σ ≤ Real.pi → False := by
    intro h
    have h1 : 3 * Real.pi / 2 ≤ σ := by
      rw [hσdef]
      have hp := mul_nonneg t.2.1 two_pi_sub_three_pi_half_nonneg
      linarith [hp]
    linarith [h, h1, Real.pi_pos]
  rw [show (1 : ℝ) + (t : ℝ) * (0 - 1) = 1 - (t : ℝ) from by ring]
  by_cases h : σ ≤ 3 * Real.pi / 2
  · -- `t = 0`: the value is `γ θ₁` on both sides
    have hσ : σ = 3 * Real.pi / 2 :=
      le_antisymm h (by rw [hσdef]; nlinarith [t.2.1, Real.pi_pos])
    rw [Work.SphereJordan.tgtUpB_eq,
      Work.SphereJordan.perPt_self ⟨by rw [hσ]; linarith [Real.pi_pos],
        by rw [hσ]; linarith [Real.pi_pos]⟩]
    rw [Work.SphereJordan.tgtUpBun, if_neg hσ2, if_neg hσπ, if_pos h]
    have ht : (t : ℝ) = 0 := by rw [hσdef] at hσ; nlinarith [hσ, t.2.1, Real.pi_pos]
    rw [show (σ - Real.pi) / (Real.pi / 2) = 1 from by rw [hσ, three_pi_half_sub_pi_div]]
    cases b
    · rw [if_neg (by simp : ¬ (false = true)),
        show H.θ₂ + (1 : ℝ) * (H.θ₁ - H.θ₂ - 2 * Real.pi) = H.θ₁ - 2 * Real.pi from by ring,
        show γ.γ (H.θ₁ - 2 * Real.pi) = γ.γ H.θ₁ from by
          have hper := γ.periodic_apply (H.θ₁ - 2 * Real.pi)
          rw [show H.θ₁ - 2 * Real.pi + 2 * Real.pi = H.θ₁ from by ring] at hper
          exact hper.symm]
      unfold cutC₁
      rw [ht, show H.s₁ + (1 - (0 : ℝ)) * (H.t₁ - H.s₁) = H.t₁ from by ring, ← H.hθ₁]
    · rw [if_pos (by simp : (true = true)),
        show H.θ₂ + (1 : ℝ) * (H.θ₁ - H.θ₂) = H.θ₁ from by ring]
      unfold cutC₁
      rw [ht, show H.s₁ + (1 - (0 : ℝ)) * (H.t₁ - H.s₁) = H.t₁ from by ring, ← H.hθ₁]
  · rcases eq_or_lt_of_le t.2.2 with ht1 | ht1
    · -- `t = 1`: the value is `cutDir S` on both sides
      have hσ : σ = 2 * Real.pi := by rw [hσdef, ht1]; ring
      rw [hσ, Work.SphereJordan.tgtUpB_eq, perPt_two_pi]
      rw [Work.SphereJordan.tgtUpBun,
        if_pos (by linarith [Real.pi_pos] : (0 : ℝ) ≤ Real.pi / 2)]
      rw [show (0 : ℝ) / (Real.pi / 2) = 0 from by simp, Work.SphereJordan.srcOuterUp_zero]
      unfold cutC₁
      rw [ht1, show H.s₁ + (1 - (1 : ℝ)) * (H.t₁ - H.s₁) = H.s₁ from by ring]
      exact H.hout₁.symm
    · -- `0 < t < 1`: the fourth branch is the crosscut
      have hσlt : σ < 2 * Real.pi := by rw [hσdef]; nlinarith [ht1, Real.pi_pos]
      rw [Work.SphereJordan.tgtUpB_eq,
        Work.SphereJordan.perPt_self ⟨by rw [hσdef]; nlinarith [t.2.1, Real.pi_pos], hσlt⟩]
      rw [Work.SphereJordan.tgtUpBun, if_neg hσ2, if_neg hσπ, if_neg h]
      have harg : 1 - (σ - 3 * Real.pi / 2) / (Real.pi / 2) = 1 - (t : ℝ) := by
        rw [hσdef]; field_simp; ring
      rw [harg]
      rfl

/-- The first quarter of the lower curve is the lower outer semicircle. -/
theorem dn_incr_first (H : SpanHyp hh hs hball S) (b : Bool) (x : ℂ) :
    incOn (H.dnPC b).γ (H.dnPC b).cont x 0 (Real.pi / 2) =
      incOn (outerC S) (continuous_outerC S) x Real.pi (2 * Real.pi) := by
  refine incOn_eq_of_forall _ _ (fun t => ?_)
  show Work.Smooth.SphereJordan.tgtDnB S H.t₁ H.s₁ H.t₂ H.s₂ b H.θ₁ H.θ₂
      (0 + (t : ℝ) * (Real.pi / 2 - 0)) = outerC S (Real.pi + (t : ℝ) * (2 * Real.pi - Real.pi))
  set σ : ℝ := (t : ℝ) * (Real.pi / 2) with hσdef
  have hσmem : σ ∈ Set.Ico (0 : ℝ) (2 * Real.pi) :=
    ⟨by rw [hσdef]; exact mul_nonneg t.2.1 (by positivity),
      by rw [hσdef]; nlinarith [t.2.2, Real.pi_pos]⟩
  have hle : σ ≤ Real.pi / 2 := by rw [hσdef]; nlinarith [t.2.2, Real.pi_pos]
  rw [show (0 : ℝ) + (t : ℝ) * (Real.pi / 2 - 0) = σ from by rw [hσdef]; ring,
    show Real.pi + (t : ℝ) * (2 * Real.pi - Real.pi) = Real.pi + (t : ℝ) * Real.pi from by ring,
    Work.SphereJordan.tgtDnB_eq, Work.SphereJordan.perPt_self hσmem,
    Work.SphereJordan.tgtDnBun, if_pos hle]
  unfold Work.Smooth.SphereJordan.srcOuterDn outerC
  have harg : (((Real.pi * (σ / (Real.pi / 2)) : ℝ)) : ℂ) = (((t : ℝ) * Real.pi : ℝ)) := by
    rw [hσdef]
    have h2 : (t : ℝ) * (Real.pi / 2) / (Real.pi / 2) = (t : ℝ) :=
      div_eq_iff (by positivity : (Real.pi / 2 : ℝ) ≠ 0)
        |>.mpr (by ring)
    rw [h2]; push_cast; ring
  have harg2 : (((Real.pi + (t : ℝ) * Real.pi : ℝ)) : ℂ) =
      (Real.pi : ℂ) + (((t : ℝ) * Real.pi : ℝ)) := by push_cast; ring
  rw [harg, harg2, add_mul, Complex.exp_add, Complex.exp_pi_mul_I]
  ring

/-- The second quarter of the lower curve is the first crosscut, inward. -/
theorem dn_incr_second (H : SpanHyp hh hs hball S) (b : Bool) (x : ℂ) :
    incOn (H.dnPC b).γ (H.dnPC b).cont x (Real.pi / 2) Real.pi =
      incOn (cutC₁ H) (continuous_cutC₁ H) x 0 1 := by
  refine incOn_eq_of_forall _ _ (fun t => ?_)
  show Work.Smooth.SphereJordan.tgtDnB S H.t₁ H.s₁ H.t₂ H.s₂ b H.θ₁ H.θ₂
      (Real.pi / 2 + (t : ℝ) * (Real.pi - Real.pi / 2)) = cutC₁ H (0 + (t : ℝ) * (1 - 0))
  set σ : ℝ := Real.pi / 2 + (t : ℝ) * (Real.pi - Real.pi / 2) with hσdef
  have hσmem : σ ∈ Set.Ico (0 : ℝ) (2 * Real.pi) :=
    ⟨by rw [hσdef]; nlinarith [t.2.1, Real.pi_pos],
      by rw [hσdef]; nlinarith [t.2.2, Real.pi_pos]⟩
  have hσle : σ ≤ Real.pi := by rw [hσdef]; nlinarith [t.2.2, Real.pi_pos]
  rw [show (0 : ℝ) + (t : ℝ) * (1 - 0) = (t : ℝ) from by ring,
    Work.SphereJordan.tgtDnB_eq, Work.SphereJordan.perPt_self hσmem]
  by_cases h : σ ≤ Real.pi / 2
  · rw [Work.SphereJordan.tgtDnBun, if_pos h]
    have hσ : σ = Real.pi / 2 := le_antisymm h (by rw [hσdef]; nlinarith [t.2.1, Real.pi_pos])
    have ht : (t : ℝ) = 0 := by rw [hσdef] at hσ; nlinarith [hσ, t.2.1, Real.pi_pos]
    rw [show σ / (Real.pi / 2) = 1 from by rw [hσ, pi_half_div_self],
      Work.SphereJordan.srcOuterDn_one]
    unfold cutC₁
    rw [ht, show H.s₁ + (0 : ℝ) * (H.t₁ - H.s₁) = H.s₁ from by ring]
    exact H.hout₁.symm
  · rw [Work.SphereJordan.tgtDnBun, if_neg h, if_pos hσle]
    have harg : (σ - Real.pi / 2) / (Real.pi / 2) = (t : ℝ) := by
      rw [hσdef]; field_simp; ring
    rw [harg]
    rfl

/-- The third quarter of the lower curve, `b = true`: the complementary arc from `θ₁ - 2π` to
`θ₂`. -/
theorem dn_incr_third_true (H : SpanHyp hh hs hball S) (x : ℂ) :
    incOn (H.dnPC true).γ (H.dnPC true).cont x Real.pi (3 * Real.pi / 2) =
      incOn γ.γ γ.cont x (H.θ₁ - 2 * Real.pi) H.θ₂ := by
  refine incOn_eq_of_forall _ _ (fun t => ?_)
  show Work.Smooth.SphereJordan.tgtDnB S H.t₁ H.s₁ H.t₂ H.s₂ true H.θ₁ H.θ₂
      (Real.pi + (t : ℝ) * (3 * Real.pi / 2 - Real.pi)) =
    γ.γ (H.θ₁ - 2 * Real.pi + (t : ℝ) * (H.θ₂ - (H.θ₁ - 2 * Real.pi)))
  set σ : ℝ := Real.pi + (t : ℝ) * (3 * Real.pi / 2 - Real.pi) with hσdef
  have hσmem : σ ∈ Set.Ico (0 : ℝ) (2 * Real.pi) :=
    ⟨by rw [hσdef]; nlinarith [t.2.1, Real.pi_pos],
      by rw [hσdef]; nlinarith [t.2.2, Real.pi_pos]⟩
  have hσ3 : σ ≤ 3 * Real.pi / 2 := by rw [hσdef]; nlinarith [t.2.2, Real.pi_pos]
  have hσ2 : σ ≤ Real.pi / 2 → False := by
    intro h
    have h1 : Real.pi ≤ σ := by
      rw [hσdef]
      have hp := mul_nonneg t.2.1 three_pi_half_sub_pi_nonneg
      linarith [hp]
    linarith [h, h1, Real.pi_pos]
  rw [Work.SphereJordan.tgtDnB_eq, Work.SphereJordan.perPt_self hσmem]
  by_cases h : σ ≤ Real.pi
  · rw [Work.SphereJordan.tgtDnBun, if_neg hσ2, if_pos h]
    have hσ : σ = Real.pi := le_antisymm h (by rw [hσdef]; nlinarith [t.2.1, Real.pi_pos])
    have ht : (t : ℝ) = 0 := by rw [hσdef] at hσ; nlinarith [hσ, t.2.1, Real.pi_pos]
    rw [show (σ - Real.pi / 2) / (Real.pi / 2) = 1 from by
        rw [hσ, pi_sub_pi_half_div],
      Work.SphereJordan.tgtCut₁_one,
      show H.θ₁ - 2 * Real.pi + (t : ℝ) * (H.θ₂ - (H.θ₁ - 2 * Real.pi)) =
        H.θ₁ - 2 * Real.pi from by rw [ht]; ring,
      show γ.γ (H.θ₁ - 2 * Real.pi) = γ.γ H.θ₁ from by
        have hper := γ.periodic_apply (H.θ₁ - 2 * Real.pi)
        rw [show H.θ₁ - 2 * Real.pi + 2 * Real.pi = H.θ₁ from by ring] at hper
        exact hper.symm,
      ← H.hθ₁]
  · rw [Work.SphereJordan.tgtDnBun, if_neg hσ2, if_neg h, if_pos hσ3,
      if_pos (by simp : (true = true))]
    have harg : (σ - Real.pi) / (Real.pi / 2) = (t : ℝ) := by
      rw [hσdef]; field_simp; ring
    rw [harg]
    ring_nf

/-- The third quarter of the lower curve, `b = false`: the arc from `θ₁` to `θ₂`. -/
theorem dn_incr_third_false (H : SpanHyp hh hs hball S) (x : ℂ) :
    incOn (H.dnPC false).γ (H.dnPC false).cont x Real.pi (3 * Real.pi / 2) =
      incOn γ.γ γ.cont x H.θ₁ H.θ₂ := by
  refine incOn_eq_of_forall _ _ (fun t => ?_)
  show Work.Smooth.SphereJordan.tgtDnB S H.t₁ H.s₁ H.t₂ H.s₂ false H.θ₁ H.θ₂
      (Real.pi + (t : ℝ) * (3 * Real.pi / 2 - Real.pi)) =
    γ.γ (H.θ₁ + (t : ℝ) * (H.θ₂ - H.θ₁))
  set σ : ℝ := Real.pi + (t : ℝ) * (3 * Real.pi / 2 - Real.pi) with hσdef
  have hσmem : σ ∈ Set.Ico (0 : ℝ) (2 * Real.pi) :=
    ⟨by rw [hσdef]; nlinarith [t.2.1, Real.pi_pos],
      by rw [hσdef]; nlinarith [t.2.2, Real.pi_pos]⟩
  have hσ3 : σ ≤ 3 * Real.pi / 2 := by rw [hσdef]; nlinarith [t.2.2, Real.pi_pos]
  have hσ2 : σ ≤ Real.pi / 2 → False := by
    intro h
    have h1 : Real.pi ≤ σ := by
      rw [hσdef]
      have hp := mul_nonneg t.2.1 three_pi_half_sub_pi_nonneg
      linarith [hp]
    linarith [h, h1, Real.pi_pos]
  rw [Work.SphereJordan.tgtDnB_eq, Work.SphereJordan.perPt_self hσmem]
  by_cases h : σ ≤ Real.pi
  · rw [Work.SphereJordan.tgtDnBun, if_neg hσ2, if_pos h]
    have hσ : σ = Real.pi := le_antisymm h (by rw [hσdef]; nlinarith [t.2.1, Real.pi_pos])
    have ht : (t : ℝ) = 0 := by rw [hσdef] at hσ; nlinarith [hσ, t.2.1, Real.pi_pos]
    rw [show (σ - Real.pi / 2) / (Real.pi / 2) = 1 from by
        rw [hσ, pi_sub_pi_half_div],
      Work.SphereJordan.tgtCut₁_one,
      show H.θ₁ + (t : ℝ) * (H.θ₂ - H.θ₁) = H.θ₁ from by rw [ht]; ring, ← H.hθ₁]
  · rw [Work.SphereJordan.tgtDnBun, if_neg hσ2, if_neg h, if_pos hσ3,
      if_neg (by simp : ¬ (false = true))]
    have harg : (σ - Real.pi) / (Real.pi / 2) = (t : ℝ) := by
      rw [hσdef]; field_simp; ring
    rw [harg]

/-- The fourth quarter of the lower curve is the second crosscut, outward. -/
theorem dn_incr_fourth (H : SpanHyp hh hs hball S) (b : Bool) (x : ℂ) :
    incOn (H.dnPC b).γ (H.dnPC b).cont x (3 * Real.pi / 2) (2 * Real.pi) =
      incOn (cutC₂ H) (continuous_cutC₂ H) x 1 0 := by
  refine incOn_eq_of_forall _ _ (fun t => ?_)
  show Work.Smooth.SphereJordan.tgtDnB S H.t₁ H.s₁ H.t₂ H.s₂ b H.θ₁ H.θ₂
      (3 * Real.pi / 2 + (t : ℝ) * (2 * Real.pi - 3 * Real.pi / 2)) =
    cutC₂ H (1 + (t : ℝ) * (0 - 1))
  set σ : ℝ := 3 * Real.pi / 2 + (t : ℝ) * (2 * Real.pi - 3 * Real.pi / 2) with hσdef
  have hσle : σ ≤ 2 * Real.pi := by rw [hσdef]; nlinarith [t.2.2, Real.pi_pos]
  have hσ2 : σ ≤ Real.pi / 2 → False := by
    intro h
    have h1 : 3 * Real.pi / 2 ≤ σ := by
      rw [hσdef]
      have hp := mul_nonneg t.2.1 two_pi_sub_three_pi_half_nonneg
      linarith [hp]
    linarith [h, h1, Real.pi_pos]
  have hσπ : σ ≤ Real.pi → False := by
    intro h
    have h1 : 3 * Real.pi / 2 ≤ σ := by
      rw [hσdef]
      have hp := mul_nonneg t.2.1 two_pi_sub_three_pi_half_nonneg
      linarith [hp]
    linarith [h, h1, Real.pi_pos]
  rw [show (1 : ℝ) + (t : ℝ) * (0 - 1) = 1 - (t : ℝ) from by ring]
  by_cases h : σ ≤ 3 * Real.pi / 2
  · have hσ : σ = 3 * Real.pi / 2 :=
      le_antisymm h (by rw [hσdef]; nlinarith [t.2.1, Real.pi_pos])
    rw [Work.SphereJordan.tgtDnB_eq,
      Work.SphereJordan.perPt_self ⟨by rw [hσ]; linarith [Real.pi_pos],
        by rw [hσ]; linarith [Real.pi_pos]⟩]
    rw [Work.SphereJordan.tgtDnBun, if_neg hσ2, if_neg hσπ, if_pos h]
    have ht : (t : ℝ) = 0 := by rw [hσdef] at hσ; nlinarith [hσ, t.2.1, Real.pi_pos]
    rw [show (σ - Real.pi) / (Real.pi / 2) = 1 from by rw [hσ, three_pi_half_sub_pi_div]]
    cases b
    · rw [if_neg (by simp : ¬ (false = true)),
        show H.θ₁ + (1 : ℝ) * (H.θ₂ - H.θ₁) = H.θ₂ from by ring]
      unfold cutC₂
      rw [ht, show H.s₂ + (1 - (0 : ℝ)) * (H.t₂ - H.s₂) = H.t₂ from by ring, ← H.hθ₂]
    · rw [if_pos (by simp : (true = true)),
        show H.θ₁ - 2 * Real.pi + (1 : ℝ) * (H.θ₂ - H.θ₁ + 2 * Real.pi) = H.θ₂ from by ring]
      unfold cutC₂
      rw [ht, show H.s₂ + (1 - (0 : ℝ)) * (H.t₂ - H.s₂) = H.t₂ from by ring, ← H.hθ₂]
  · rcases eq_or_lt_of_le t.2.2 with ht1 | ht1
    · have hσ : σ = 2 * Real.pi := by rw [hσdef, ht1]; ring
      rw [hσ, Work.SphereJordan.tgtDnB_eq, perPt_two_pi]
      rw [Work.SphereJordan.tgtDnBun,
        if_pos (by linarith [Real.pi_pos] : (0 : ℝ) ≤ Real.pi / 2)]
      rw [show (0 : ℝ) / (Real.pi / 2) = 0 from by simp, Work.SphereJordan.srcOuterDn_zero]
      unfold cutC₂
      rw [ht1, show H.s₂ + (1 - (1 : ℝ)) * (H.t₂ - H.s₂) = H.s₂ from by ring]
      exact H.hout₂.symm
    · have hσlt : σ < 2 * Real.pi := by rw [hσdef]; nlinarith [ht1, Real.pi_pos]
      rw [Work.SphereJordan.tgtDnB_eq,
        Work.SphereJordan.perPt_self ⟨by rw [hσdef]; nlinarith [t.2.1, Real.pi_pos], hσlt⟩]
      rw [Work.SphereJordan.tgtDnBun, if_neg hσ2, if_neg hσπ, if_neg h]
      have harg : 1 - (σ - 3 * Real.pi / 2) / (Real.pi / 2) = 1 - (t : ℝ) := by
        rw [hσdef]; field_simp; ring
      rw [harg]
      rfl

/-! ## Avoidance of the test point -/

section Avoid

variable {hh : Work.Smooth.SphereJordan.PlaneHypothesis} {hs : γ.IsSimple}
  {hball : ∀ θ : ℝ, ‖γ.γ θ‖ < 1} {S : Work.Smooth.Jordan.PlaneSchoenflies γ}

theorem norm_outerC (S : Work.Smooth.Jordan.PlaneSchoenflies γ) (r : ℝ) :
    ‖outerC S r‖ = 1 := by
  rw [outerC, norm_mul, Work.Smooth.SphereJordan.norm_cutDir, one_mul,
    Complex.norm_exp_ofReal_mul_I]

theorem outerC_ne {x : ℂ} (hx : ‖x‖ < 1) (r : ℝ) : outerC S r ≠ x := by
  intro h
  have h1 := norm_outerC S r
  rw [h] at h1
  rw [h1] at hx
  exact lt_irrefl 1 hx

theorem cutC₁_ne (H : SpanHyp hh hs hball S) {x : ℂ} (hx : x ∈ S.V) {r : ℝ}
    (hr : r ∈ Set.Icc (0 : ℝ) 1) : cutC₁ H r ≠ x :=
  tgtCut₁_ne H hx hr

theorem cutC₂_ne (H : SpanHyp hh hs hball S) {x : ℂ} (hx : x ∈ S.V) {r : ℝ}
    (hr : r ∈ Set.Icc (0 : ℝ) 1) : cutC₂ H r ≠ x :=
  tgtCut₂_ne H hx hr

theorem gamma_ne' (S : Work.Smooth.Jordan.PlaneSchoenflies γ) {x : ℂ} (hx : x ∈ S.V)
    (r : ℝ) : γ.γ r ≠ x := gamma_ne S hx r

/-- The upper four-arc curve avoids `x` on one period. -/
theorem upCurve_avoid (H : SpanHyp hh hs hball S) {x : ℂ} (hx : x ∈ S.V) (b : Bool) :
    ∀ r ∈ Set.Icc (0 : ℝ) (2 * Real.pi), (H.upPC b).γ r ≠ x := by
  intro r hr h
  have hr' : r / (2 * Real.pi) ∈ Set.Icc (0 : ℝ) 1 :=
    ⟨div_nonneg hr.1 (by positivity), by rw [div_le_one (by positivity)]; exact hr.2⟩
  have h1 := upLoop_ne H hx b ⟨r / (2 * Real.pi), hr'⟩
  have h2 : (H.upPC b).γ (2 * Real.pi * (r / (2 * Real.pi))) - x = 0 := by
    rw [show 2 * Real.pi * (r / (2 * Real.pi)) = r from by
      rw [mul_div_cancel₀ _ (by positivity : (2 * Real.pi : ℝ) ≠ 0)]]
    exact sub_eq_zero.mpr h
  exact h1 h2

/-- The lower four-arc curve avoids `x` on one period. -/
theorem dnCurve_avoid (H : SpanHyp hh hs hball S) {x : ℂ} (hx : x ∈ S.V) (b : Bool) :
    ∀ r ∈ Set.Icc (0 : ℝ) (2 * Real.pi), (H.dnPC b).γ r ≠ x := by
  intro r hr h
  have hr' : r / (2 * Real.pi) ∈ Set.Icc (0 : ℝ) 1 :=
    ⟨div_nonneg hr.1 (by positivity), by rw [div_le_one (by positivity)]; exact hr.2⟩
  have h1 := dnLoop_ne H hx b ⟨r / (2 * Real.pi), hr'⟩
  have h2 : (H.dnPC b).γ (2 * Real.pi * (r / (2 * Real.pi))) - x = 0 := by
    rw [show 2 * Real.pi * (r / (2 * Real.pi)) = r from by
      rw [mul_div_cancel₀ _ (by positivity : (2 * Real.pi : ℝ) ≠ 0)]]
    exact sub_eq_zero.mpr h
  exact h1 h2

end Avoid

/-! ## The outer circle loop: increment `2πi` -/

section LoopFacts

/-- The increment is additive over pointwise products of nowhere vanishing paths. -/
theorem incr'_mul (u v : C(unitInterval, ℂ)) (hu : ∀ t, u t ≠ 0) (hv : ∀ t, v t ≠ 0) :
    incr' (u * v) = incr' u + incr' v := by
  have huv : ∀ t, (u * v) t ≠ 0 := fun t => mul_ne_zero (hu t) (hv t)
  rw [incr'_eq huv, incr'_eq hu, incr'_eq hv]
  have hlift : ∀ t, Complex.exp ((liftOf hu + liftOf hv) t) = (u * v) t := by
    intro t
    rw [ContinuousMap.add_apply, Complex.exp_add, exp_liftOf hu t, exp_liftOf hv t,
      ContinuousMap.mul_apply]
  have h1 := incr_spec huv (liftOf hu + liftOf hv) hlift
  rw [← h1, incr, incr]
  simp only [ContinuousMap.add_apply]
  ring

theorem expLoop_ne : ∀ t : unitInterval, expLoop t ≠ 0 := by
  intro t h
  have h1 : ‖expLoop t‖ = 1 := by
    show ‖Complex.exp ((((2 * Real.pi * (t : ℝ) : ℝ)) : ℂ) * Complex.I)‖ = 1
    exact Complex.norm_exp_ofReal_mul_I (2 * Real.pi * (t : ℝ))
  rw [h, norm_zero] at h1
  exact one_ne_zero h1.symm

theorem expLoop_closed : expLoop 0 = expLoop 1 := by
  show Complex.exp ((((2 * Real.pi * ((0 : unitInterval) : ℝ) : ℝ)) : ℂ) * Complex.I) =
      Complex.exp ((((2 * Real.pi * ((1 : unitInterval) : ℝ) : ℝ)) : ℂ) * Complex.I)
  rw [show ((0 : unitInterval) : ℝ) = 0 from rfl, show ((1 : unitInterval) : ℝ) = 1 from rfl,
    mul_zero, mul_one, Complex.ofReal_zero, zero_mul, Complex.exp_zero,
    show (((2 * Real.pi : ℝ)) : ℂ) = 2 * (Real.pi : ℂ) from by push_cast; ring,
    Complex.exp_two_pi_mul_I]

theorem loopIndex_expLoop : Work.Smooth.SphereJordan.loopIndex expLoop = 1 := by
  let Λ : C(unitInterval, ℂ) :=
    ⟨fun t => (((2 * Real.pi * (t : ℝ) : ℝ)) : ℂ) * Complex.I, by fun_prop⟩
  have hΛ : ∀ t, Complex.exp (Λ t) = expLoop t := fun t => rfl
  have hspec : Λ 1 - Λ 0 = ((Work.Smooth.SphereJordan.loopIndex expLoop : ℂ)) * kappa :=
    Work.Smooth.SphereJordan.loopIndex_spec expLoop expLoop_ne expLoop_closed Λ hΛ
  have hval : Λ 1 - Λ 0 = kappa := by
    show (((2 * Real.pi * ((1 : unitInterval) : ℝ) : ℝ)) : ℂ) * Complex.I -
        (((2 * Real.pi * ((0 : unitInterval) : ℝ) : ℝ)) : ℂ) * Complex.I = kappa
    rw [show ((1 : unitInterval) : ℝ) = 1 from rfl, show ((0 : unitInterval) : ℝ) = 0 from rfl,
      mul_zero, mul_one, Complex.ofReal_zero, zero_mul, sub_zero, kappa,
      show (((2 * Real.pi : ℝ)) : ℂ) = 2 * (Real.pi : ℂ) from by push_cast; ring]
  have heq : ((Work.Smooth.SphereJordan.loopIndex expLoop : ℂ)) * kappa = 1 * kappa := by
    rw [← hspec, hval, one_mul]
  have h2 := mul_right_cancel₀ kappa_ne_zero heq
  exact_mod_cast h2

theorem incr'_expLoop : incr' expLoop = kappa := by
  rw [incr'_eq_loopIndex expLoop_ne expLoop_closed, loopIndex_expLoop]
  ring

end LoopFacts

/-! ## The "small" loop and the outer circle loop -/

section Outer

variable {hh : Work.Smooth.SphereJordan.PlaneHypothesis} {hs : γ.IsSimple}
  {hball : ∀ θ : ℝ, ‖γ.γ θ‖ < 1} {S : Work.Smooth.Jordan.PlaneSchoenflies γ}

theorem exp_neg_two_pi_I : Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I)) = 1 := by
  rw [Complex.exp_neg, Complex.exp_two_pi_mul_I, inv_one]

theorem starLoop_ne (H : SpanHyp hh hs hball S) {x : ℂ} (hx : ‖x‖ < 1) :
    ∀ t, starLoop H x t ≠ 0 := by
  intro t h
  have h1 : ‖starLoop H x t‖ = 0 := by rw [h, norm_zero]
  have h2 : 1 - ‖x‖ ≤ ‖starLoop H x t‖ := by
    show 1 - ‖x‖ ≤ ‖Work.Smooth.SphereJordan.cutDir S -
      x * Complex.exp ((((-(2 * Real.pi * (t : ℝ)) : ℝ)) : ℂ) * Complex.I)‖
    have hc : ‖Work.Smooth.SphereJordan.cutDir S‖ = 1 :=
      Work.Smooth.SphereJordan.norm_cutDir S
    have hx1 : ‖x * Complex.exp ((((-(2 * Real.pi * (t : ℝ)) : ℝ)) : ℂ) * Complex.I)‖ = ‖x‖ := by
      rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one]
    calc 1 - ‖x‖ = ‖Work.Smooth.SphereJordan.cutDir S‖ -
          ‖x * Complex.exp ((((-(2 * Real.pi * (t : ℝ)) : ℝ)) : ℂ) * Complex.I)‖ := by
          rw [hc, hx1]
      _ ≤ ‖Work.Smooth.SphereJordan.cutDir S -
          x * Complex.exp ((((-(2 * Real.pi * (t : ℝ)) : ℝ)) : ℂ) * Complex.I)‖ :=
        norm_sub_norm_le _ _
  linarith [h1, h2, hx]

theorem starLoop_closed (H : SpanHyp hh hs hball S) (x : ℂ) :
    starLoop H x 0 = starLoop H x 1 := by
  have haround0 : ((((-(2 * Real.pi * ((0 : unitInterval) : ℝ)) : ℝ)) : ℂ) * Complex.I) = 0 := by
    rw [show ((0 : unitInterval) : ℝ) = 0 from rfl]
    push_cast
    ring
  have haround1 : ((((-(2 * Real.pi * ((1 : unitInterval) : ℝ)) : ℝ)) : ℂ) * Complex.I) =
      -(2 * (Real.pi : ℂ) * Complex.I) := by
    rw [show ((1 : unitInterval) : ℝ) = 1 from rfl]
    push_cast
    ring
  show (Work.Smooth.SphereJordan.cutDir S -
      x * Complex.exp ((((-(2 * Real.pi * ((0 : unitInterval) : ℝ)) : ℝ)) : ℂ) * Complex.I)) =
    (Work.Smooth.SphereJordan.cutDir S -
      x * Complex.exp ((((-(2 * Real.pi * ((1 : unitInterval) : ℝ)) : ℝ)) : ℂ) * Complex.I))
  rw [haround0, haround1, Complex.exp_zero, exp_neg_two_pi_I]

theorem loopIndex_starLoop (H : SpanHyp hh hs hball S) {x : ℂ} (hx : ‖x‖ < 1) :
    Work.Smooth.SphereJordan.loopIndex (starLoop H x) = 0 := by
  have hne := starLoop_ne H hx
  refine Work.Smooth.SphereJordan.loopIndex_eq_zero_of_avoids_ray (starLoop H x) hne
    (starLoop_closed H x)
    (ω := Complex.I * Work.Smooth.SphereJordan.cutDir S)
    (mul_ne_zero Complex.I_ne_zero (Work.Smooth.SphereJordan.cutDir_ne_zero S)) ?_
  intro t r hr hcon
  have h := hcon
  simp only [starLoop, ContinuousMap.coe_mk] at h
  have hxE : x * Complex.exp ((((-(2 * Real.pi * (t : ℝ)) : ℝ)) : ℂ) * Complex.I) =
      (1 - (r : ℂ) * Complex.I) * Work.Smooth.SphereJordan.cutDir S := by
    have h' : x * Complex.exp ((((-(2 * Real.pi * (t : ℝ)) : ℝ)) : ℂ) * Complex.I) =
        Work.Smooth.SphereJordan.cutDir S -
          (r : ℂ) * (Complex.I * Work.Smooth.SphereJordan.cutDir S) := by
      linear_combination (norm := skip) -h
      ring
    rw [h']
    ring
  have hnorm : ‖x‖ = ‖(1 : ℂ) - (r : ℂ) * Complex.I‖ := by
    have h2 := congrArg norm hxE
    rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, norm_mul,
      Work.Smooth.SphereJordan.norm_cutDir, mul_one] at h2
    exact h2
  have hge : 1 ≤ ‖(1 : ℂ) - (r : ℂ) * Complex.I‖ := by
    have hre : ((1 : ℂ) - (r : ℂ) * Complex.I).re = 1 := by
      simp [Complex.sub_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
        Complex.I_re, Complex.I_im]
    have h3 := Complex.abs_re_le_norm ((1 : ℂ) - (r : ℂ) * Complex.I)
    rw [hre] at h3
    simpa using h3
  rw [hnorm] at hx
  linarith [hx, hge]

theorem incr'_starLoop (H : SpanHyp hh hs hball S) {x : ℂ} (hx : ‖x‖ < 1) :
    incr' (starLoop H x) = 0 := by
  rw [incr'_eq_loopIndex (starLoop_ne H hx) (starLoop_closed H x), loopIndex_starLoop H hx]
  rw [Int.cast_zero, zero_mul]

theorem outerLoop_eq_curveLoop (H : SpanHyp hh hs hball S) (x : ℂ) :
    outerLoop H x = Work.Smooth.SphereJordan.curveLoop (fun t => outerC S t - x)
      ((continuous_outerC S).sub continuous_const) := by
  ext t
  simp only [outerLoop, Work.Smooth.SphereJordan.curveLoop, outerC, ContinuousMap.coe_mk]

theorem outerLoop_eq_mul (H : SpanHyp hh hs hball S) (x : ℂ) (t : unitInterval) :
    outerLoop H x t = (expLoop * starLoop H x) t := by
  show Work.Smooth.SphereJordan.cutDir S *
      Complex.exp ((((2 * Real.pi * (t : ℝ) : ℝ)) : ℂ) * Complex.I) - x =
    Complex.exp ((((2 * Real.pi * (t : ℝ) : ℝ)) : ℂ) * Complex.I) *
      (Work.Smooth.SphereJordan.cutDir S -
        x * Complex.exp ((((-(2 * Real.pi * (t : ℝ)) : ℝ)) : ℂ) * Complex.I))
  have hEin : Complex.exp ((((-(2 * Real.pi * (t : ℝ)) : ℝ)) : ℂ) * Complex.I) =
      (Complex.exp ((((2 * Real.pi * (t : ℝ) : ℝ)) : ℂ) * Complex.I))⁻¹ := by
    rw [show (((-(2 * Real.pi * (t : ℝ)) : ℝ)) : ℂ) =
      -(((2 * Real.pi * (t : ℝ) : ℝ)) : ℂ) from by push_cast; ring,
      show (-(((2 * Real.pi * (t : ℝ) : ℝ)) : ℂ)) * Complex.I =
        -((((2 * Real.pi * (t : ℝ) : ℝ)) : ℂ) * Complex.I) from by ring,
      Complex.exp_neg]
  rw [hEin]
  have hcancel : Complex.exp ((((2 * Real.pi * (t : ℝ) : ℝ)) : ℂ) * Complex.I) *
      (x * (Complex.exp ((((2 * Real.pi * (t : ℝ) : ℝ)) : ℂ) * Complex.I))⁻¹) = x := by
    rw [← mul_assoc, mul_comm (Complex.exp ((((2 * Real.pi * (t : ℝ) : ℝ)) : ℂ) * Complex.I)) x,
      mul_assoc, mul_inv_cancel₀ (Complex.exp_ne_zero _), mul_one]
  rw [mul_sub, hcancel]
  ring

theorem incr'_outerLoop (H : SpanHyp hh hs hball S) {x : ℂ} (hx : ‖x‖ < 1) :
    incr' (outerLoop H x) = kappa := by
  rw [incr'_congr (outerLoop_eq_mul H x),
    incr'_mul expLoop (starLoop H x) expLoop_ne (starLoop_ne H hx), incr'_expLoop,
    incr'_starLoop H hx]
  ring

/-- **The outer circle winds once about every point of the bounded side.** -/
theorem windNumber_outerC (H : SpanHyp hh hs hball S) {x : ℂ} (hx : ‖x‖ < 1) :
    Work.Smooth.SphereJordan.windNumber (outerC S) (continuous_outerC S) x = 1 := by
  have hne : ∀ t, outerLoop H x t ≠ 0 := by
    intro t h
    have h1 : outerLoop H x t = outerC S (2 * Real.pi * (t : ℝ)) - x := by
      simp only [outerLoop, outerC, ContinuousMap.coe_mk]
    rw [h1] at h
    exact (outerC_ne hx _) (sub_eq_zero.mp h)
  have hcl : outerLoop H x 0 = outerLoop H x 1 := by
    have haround0 : (((2 * Real.pi * ((0 : unitInterval) : ℝ) : ℝ)) : ℂ) * Complex.I = 0 := by
      rw [show ((0 : unitInterval) : ℝ) = 0 from rfl]
      push_cast
      ring
    have haround1 : (((2 * Real.pi * ((1 : unitInterval) : ℝ) : ℝ)) : ℂ) * Complex.I =
        2 * (Real.pi : ℂ) * Complex.I := by
      rw [show ((1 : unitInterval) : ℝ) = 1 from rfl]
      push_cast
      ring
    show Work.Smooth.SphereJordan.cutDir S *
        Complex.exp ((((2 * Real.pi * ((0 : unitInterval) : ℝ) : ℝ)) : ℂ) * Complex.I) - x =
      Work.Smooth.SphereJordan.cutDir S *
        Complex.exp ((((2 * Real.pi * ((1 : unitInterval) : ℝ) : ℝ)) : ℂ) * Complex.I) - x
    rw [haround0, haround1, Complex.exp_zero, Complex.exp_two_pi_mul_I]
  have h1 : ((Work.Smooth.SphereJordan.loopIndex (outerLoop H x) : ℂ)) * kappa = 1 * kappa := by
    rw [← incr'_eq_loopIndex hne hcl, incr'_outerLoop H hx, one_mul]
  have h2 : Work.Smooth.SphereJordan.loopIndex (outerLoop H x) = 1 := by
    have h3 := mul_right_cancel₀ kappa_ne_zero h1
    exact_mod_cast h3
  have h4 : Work.Smooth.SphereJordan.windNumber (outerC S) (continuous_outerC S) x =
      Work.Smooth.SphereJordan.loopIndex (outerLoop H x) := by
    rw [outerLoop_eq_curveLoop H x]
    rfl
  rw [h4, h2]

end Outer

/-! ## The loops of the four-arc curves as sums of interval increments -/

section Decomp

variable {hh : Work.Smooth.SphereJordan.PlaneHypothesis} {hs : γ.IsSimple}
  {hball : ∀ θ : ℝ, ‖γ.γ θ‖ < 1} {S : Work.Smooth.Jordan.PlaneSchoenflies γ}

theorem upLoop_incr (H : SpanHyp hh hs hball S) (x : ℂ) (b : Bool) :
    incr' (upLoop H x b) = incOn (H.upPC b).γ (H.upPC b).cont x 0 (2 * Real.pi) := by
  rw [incr'_eq_pathIncTot, incOn]
  refine pathIncTot_congr (fun t => ?_)
  simp only [upLoop, Work.Smooth.SphereJordan.curveLoop, ContinuousMap.coe_mk]
  congr 1
  ring

theorem dnLoop_incr (H : SpanHyp hh hs hball S) (x : ℂ) (b : Bool) :
    incr' (dnLoop H x b) = incOn (H.dnPC b).γ (H.dnPC b).cont x 0 (2 * Real.pi) := by
  rw [incr'_eq_pathIncTot, incOn]
  refine pathIncTot_congr (fun t => ?_)
  simp only [dnLoop, Work.Smooth.SphereJordan.curveLoop, ContinuousMap.coe_mk]
  congr 1
  ring

theorem upLoop_closed (H : SpanHyp hh hs hball S) (x : ℂ) (b : Bool) :
    upLoop H x b 0 = upLoop H x b 1 := by
  show (H.upPC b).γ (2 * Real.pi * ((0 : unitInterval) : ℝ)) - x =
    (H.upPC b).γ (2 * Real.pi * ((1 : unitInterval) : ℝ)) - x
  rw [show ((0 : unitInterval) : ℝ) = 0 from rfl, show ((1 : unitInterval) : ℝ) = 1 from rfl,
    mul_zero, mul_one]
  rw [show 2 * Real.pi = 0 + 2 * Real.pi from by ring, (H.upPC b).periodic_apply 0]

theorem dnLoop_closed (H : SpanHyp hh hs hball S) (x : ℂ) (b : Bool) :
    dnLoop H x b 0 = dnLoop H x b 1 := by
  show (H.dnPC b).γ (2 * Real.pi * ((0 : unitInterval) : ℝ)) - x =
    (H.dnPC b).γ (2 * Real.pi * ((1 : unitInterval) : ℝ)) - x
  rw [show ((0 : unitInterval) : ℝ) = 0 from rfl, show ((1 : unitInterval) : ℝ) = 1 from rfl,
    mul_zero, mul_one]
  rw [show 2 * Real.pi = 0 + 2 * Real.pi from by ring, (H.dnPC b).periodic_apply 0]

theorem upLoop_decomp_true (H : SpanHyp hh hs hball S) {x : ℂ} (hx : x ∈ S.V) :
    incr' (upLoop H x true) =
      incOn (outerC S) (continuous_outerC S) x 0 Real.pi +
        incOn (cutC₂ H) (continuous_cutC₂ H) x 0 1 +
        incOn γ.γ γ.cont x H.θ₂ H.θ₁ +
        incOn (cutC₁ H) (continuous_cutC₁ H) x 1 0 := by
  have hav := upCurve_avoid H hx true
  have e1 := incOn_add (H.upPC true).cont (a := 0) (b := Real.pi / 2) (c := 2 * Real.pi)
    (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos]) hav
  have e2 := incOn_add (H.upPC true).cont (a := Real.pi / 2) (b := Real.pi) (c := 2 * Real.pi)
    (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos])
    (fun t ht => hav t ⟨by linarith [ht.1, Real.pi_pos], ht.2⟩)
  have e3 := incOn_add (H.upPC true).cont (a := Real.pi) (b := 3 * Real.pi / 2) (c := 2 * Real.pi)
    (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos])
    (fun t ht => hav t ⟨by linarith [ht.1, Real.pi_pos], ht.2⟩)
  rw [upLoop_incr, e1, e2, e3, up_incr_first H true x, up_incr_second H true x,
    up_incr_third_true H x, up_incr_fourth H true x]
  ring_nf

theorem upLoop_decomp_false (H : SpanHyp hh hs hball S) {x : ℂ} (hx : x ∈ S.V) :
    incr' (upLoop H x false) =
      incOn (outerC S) (continuous_outerC S) x 0 Real.pi +
        incOn (cutC₂ H) (continuous_cutC₂ H) x 0 1 +
        incOn γ.γ γ.cont x H.θ₂ (H.θ₁ - 2 * Real.pi) +
        incOn (cutC₁ H) (continuous_cutC₁ H) x 1 0 := by
  have hav := upCurve_avoid H hx false
  have e1 := incOn_add (H.upPC false).cont (a := 0) (b := Real.pi / 2) (c := 2 * Real.pi)
    (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos]) hav
  have e2 := incOn_add (H.upPC false).cont (a := Real.pi / 2) (b := Real.pi) (c := 2 * Real.pi)
    (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos])
    (fun t ht => hav t ⟨by linarith [ht.1, Real.pi_pos], ht.2⟩)
  have e3 := incOn_add (H.upPC false).cont (a := Real.pi) (b := 3 * Real.pi / 2) (c := 2 * Real.pi)
    (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos])
    (fun t ht => hav t ⟨by linarith [ht.1, Real.pi_pos], ht.2⟩)
  rw [upLoop_incr, e1, e2, e3, up_incr_first H false x, up_incr_second H false x,
    up_incr_third_false H x, up_incr_fourth H false x]
  ring_nf

theorem dnLoop_decomp_true (H : SpanHyp hh hs hball S) {x : ℂ} (hx : x ∈ S.V) :
    incr' (dnLoop H x true) =
      incOn (outerC S) (continuous_outerC S) x Real.pi (2 * Real.pi) +
        incOn (cutC₁ H) (continuous_cutC₁ H) x 0 1 +
        incOn γ.γ γ.cont x (H.θ₁ - 2 * Real.pi) H.θ₂ +
        incOn (cutC₂ H) (continuous_cutC₂ H) x 1 0 := by
  have hav := dnCurve_avoid H hx true
  have e1 := incOn_add (H.dnPC true).cont (a := 0) (b := Real.pi / 2) (c := 2 * Real.pi)
    (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos]) hav
  have e2 := incOn_add (H.dnPC true).cont (a := Real.pi / 2) (b := Real.pi) (c := 2 * Real.pi)
    (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos])
    (fun t ht => hav t ⟨by linarith [ht.1, Real.pi_pos], ht.2⟩)
  have e3 := incOn_add (H.dnPC true).cont (a := Real.pi) (b := 3 * Real.pi / 2) (c := 2 * Real.pi)
    (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos])
    (fun t ht => hav t ⟨by linarith [ht.1, Real.pi_pos], ht.2⟩)
  rw [dnLoop_incr, e1, e2, e3, dn_incr_first H true x, dn_incr_second H true x,
    dn_incr_third_true H x, dn_incr_fourth H true x]
  ring_nf

theorem dnLoop_decomp_false (H : SpanHyp hh hs hball S) {x : ℂ} (hx : x ∈ S.V) :
    incr' (dnLoop H x false) =
      incOn (outerC S) (continuous_outerC S) x Real.pi (2 * Real.pi) +
        incOn (cutC₁ H) (continuous_cutC₁ H) x 0 1 +
        incOn γ.γ γ.cont x H.θ₁ H.θ₂ +
        incOn (cutC₂ H) (continuous_cutC₂ H) x 1 0 := by
  have hav := dnCurve_avoid H hx false
  have e1 := incOn_add (H.dnPC false).cont (a := 0) (b := Real.pi / 2) (c := 2 * Real.pi)
    (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos]) hav
  have e2 := incOn_add (H.dnPC false).cont (a := Real.pi / 2) (b := Real.pi) (c := 2 * Real.pi)
    (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos])
    (fun t ht => hav t ⟨by linarith [ht.1, Real.pi_pos], ht.2⟩)
  have e3 := incOn_add (H.dnPC false).cont (a := Real.pi) (b := 3 * Real.pi / 2) (c := 2 * Real.pi)
    (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos])
    (fun t ht => hav t ⟨by linarith [ht.1, Real.pi_pos], ht.2⟩)
  rw [dnLoop_incr, e1, e2, e3, dn_incr_first H false x, dn_incr_second H false x,
    dn_incr_third_false H x, dn_incr_fourth H false x]
  ring_nf

end Decomp

/-! ## The pairing identities at the level of increments -/

section Pairing

variable {hh : Work.Smooth.SphereJordan.PlaneHypothesis} {hs : γ.IsSimple}
  {hball : ∀ θ : ℝ, ‖γ.γ θ‖ < 1} {S : Work.Smooth.Jordan.PlaneSchoenflies γ}

theorem incr_outer_pair (H : SpanHyp hh hs hball S) {x : ℂ} (hx : x ∈ S.V) :
    incOn (outerC S) (continuous_outerC S) x 0 Real.pi +
      incOn (outerC S) (continuous_outerC S) x Real.pi (2 * Real.pi) = kappa := by
  have hxlt := norm_lt_one_of_mem_V S hball hx
  have hav : ∀ t ∈ Set.Icc (0 : ℝ) (2 * Real.pi), outerC S t ≠ x :=
    fun t _ => outerC_ne hxlt t
  have hper := incOn_period (continuous_outerC S) (outerC_periodic S) x
    (fun t => outerC_ne hxlt t) 0
  rw [show (0 : ℝ) + 2 * Real.pi = 2 * Real.pi from by ring] at hper
  rw [← incOn_add (continuous_outerC S) (a := 0) (b := Real.pi) (c := 2 * Real.pi)
      (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos]) hav,
    hper, windNumber_outerC H hxlt, Int.cast_one, one_mul, kappa]

theorem incr_cut₁_pair (H : SpanHyp hh hs hball S) {x : ℂ} (hx : x ∈ S.V) :
    incOn (cutC₁ H) (continuous_cutC₁ H) x 1 0 +
      incOn (cutC₁ H) (continuous_cutC₁ H) x 0 1 = 0 := by
  rw [incOn_rev (continuous_cutC₁ H) (by norm_num) (fun t ht => cutC₁_ne H hx ht)]
  ring

theorem incr_cut₂_pair (H : SpanHyp hh hs hball S) {x : ℂ} (hx : x ∈ S.V) :
    incOn (cutC₂ H) (continuous_cutC₂ H) x 0 1 +
      incOn (cutC₂ H) (continuous_cutC₂ H) x 1 0 = 0 := by
  rw [incOn_rev (continuous_cutC₂ H) (by norm_num) (fun t ht => cutC₂_ne H hx ht)]
  ring

theorem incr_gamma_pair_A (H : SpanHyp hh hs hball S) {x : ℂ} (hx : x ∈ S.V) :
    incOn γ.γ γ.cont x H.θ₂ H.θ₁ + incOn γ.γ γ.cont x H.θ₁ H.θ₂ = 0 := by
  rw [incOn_rev γ.cont H.hθ.le (fun t _ => gamma_ne S hx t)]
  ring

theorem incr_gamma_pair_B (H : SpanHyp hh hs hball S) {x : ℂ} (hx : x ∈ S.V) :
    incOn γ.γ γ.cont x H.θ₂ (H.θ₁ - 2 * Real.pi) +
      incOn γ.γ γ.cont x (H.θ₁ - 2 * Real.pi) H.θ₂ = 0 := by
  rw [incOn_rev γ.cont (by linarith [H.hθ']) (fun t _ => gamma_ne S hx t)]
  ring

theorem incr_gamma_pair_C (H : SpanHyp hh hs hball S) {x : ℂ} (hx : x ∈ S.V) :
    incOn γ.γ γ.cont x H.θ₂ H.θ₁ + incOn γ.γ γ.cont x (H.θ₁ - 2 * Real.pi) H.θ₂ =
      (Work.Smooth.SphereJordan.windNumber γ.γ γ.cont x : ℂ) * kappa := by
  have hper := incOn_period γ.cont γ.periodic x (fun t => gamma_ne S hx t) (H.θ₁ - 2 * Real.pi)
  rw [show H.θ₁ - 2 * Real.pi + 2 * Real.pi = H.θ₁ from by ring] at hper
  rw [add_comm,
    ← incOn_add γ.cont (a := H.θ₁ - 2 * Real.pi) (b := H.θ₂) (c := H.θ₁)
      (by linarith [H.hθ']) H.hθ.le (fun t _ => gamma_ne S hx t),
    hper, kappa]

/-- **The arithmetic conclusion**: two closed loops whose increments sum to `k * 2πi` have winding
numbers summing to `k`. -/
theorem loopIndex_pair_eq {c d : C(unitInterval, ℂ)} (hc : ∀ t, c t ≠ 0) (hd : ∀ t, d t ≠ 0)
    (hcl : c 0 = c 1) (hdl : d 0 = d 1) {k : ℤ}
    (h : incr' c + incr' d = (k : ℂ) * kappa) :
    Work.Smooth.SphereJordan.loopIndex c + Work.Smooth.SphereJordan.loopIndex d = k := by
  rw [incr'_eq_loopIndex hc hcl, incr'_eq_loopIndex hd hdl] at h
  have h2 : (((Work.Smooth.SphereJordan.loopIndex c + Work.Smooth.SphereJordan.loopIndex d : ℤ)) : ℂ)
      * kappa = (k : ℂ) * kappa := by
    rw [← h]
    push_cast
    ring
  exact_mod_cast (mul_right_cancel₀ kappa_ne_zero h2)

end Pairing

end Intervals

end

end Work.SphereJordan
