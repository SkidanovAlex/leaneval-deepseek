import Mathlib
import Submission.Work.SphereJordan.SpanHyp
import Submission.Work.SphereJordan.incrOn
import Submission.Work.SphereJordan.argIncrement
import Submission.Work.SphereJordan.pairingSetup
import Submission.Work.SphereJordan.tgtUpPC_isSimple
import Submission.Work.Smooth.SphereJordan.windNumberCircleCurve
import Submission.Work.Smooth.SphereJordan.loopIndex_eq_of_homotopy

/-!
# The three winding-number identities of the two-cuts pairing

This module proves `Work.SphereJordan.windIdentitiesProof`: for the four four-arc curves
`H.upPC true`, `H.upPC false`, `H.dnPC true`, `H.dnPC false` of the two-cuts configuration and every
point `x` of the bounded side `S.V` of `γ`,

`a + d = 1`, `b + c = 1`, `a + b = 1 + e`,

where `a, b, c, d` are the winding numbers of the four curves and `e` is the winding number of `γ`.

The proof is the "argument increment" bookkeeping: each of the four loops is the concatenation of
its four quarter arcs, its increment is the sum of the four quarter increments (the increment is
additive over concatenation), and the three identities are obtained by cancelling the arcs that the
two loops of a pair traverse in opposite directions.  What survives is either the unit circle
(contribution `kappa = 2πI`, i.e. winding number `1`) or one full period of `γ` (contribution
`kappa * windNumber γ.γ γ.cont x`).
-/

open Set
open Classical

namespace Work.SphereJordan

noncomputable section

variable {γ : Work.Smooth.Jordan.PlaneCurve}

/-! ## Elementary increment bookkeeping -/

/-- The one-period parameter of `2π` is `0`. -/
theorem wi_perPt_two_pi : Work.Smooth.SphereJordan.perPt (2 * Real.pi) = 0 := by
  rw [Work.Smooth.SphereJordan.perPt,
    div_self (by positivity : (2 : ℝ) * Real.pi ≠ 0)]
  norm_num

/-- `incr'` of a nowhere vanishing path is the total increment of its argument. -/
theorem wi_incr'_eq_pathIncTot {p : C(unitInterval, ℂ)} (hp : ∀ t, p t ≠ 0) :
    incr' p = pathIncTot p := by
  rw [incr'_eq hp, pathIncTot_eq_of_lift p hp (liftOf hp) (exp_liftOf hp)]
  rfl

/-- **Splitting the increment of a path into two consecutive pieces.** -/
theorem wi_incr'_split {c : C(unitInterval, ℂ)} (hc : ∀ t, c t ≠ 0)
    {σ τ : C(unitInterval, unitInterval)} (hσ0 : σ 0 = 0) (hτ1 : τ 1 = 1)
    (hj : σ 1 = τ 0) :
    incr' (c.comp σ) + incr' (c.comp τ) = incr' c := by
  have h1 : incr' (c.comp σ) = liftOf hc (σ 1) - liftOf hc (σ 0) := incr'_comp hc σ
  have h2 : incr' (c.comp τ) = liftOf hc (τ 1) - liftOf hc (τ 0) := incr'_comp hc τ
  have h3 : incr' c = liftOf hc 1 - liftOf hc 0 := by rw [incr'_eq hc]; rfl
  rw [h1, h2, h3, hσ0, hτ1, hj]
  ring

/-- **Splitting the increment of a path into its four quarters.** -/
theorem wi_incr'_quarter {c : C(unitInterval, ℂ)} (hc : ∀ t, c t ≠ 0) :
    incr' c = incr' (c.comp q1) + incr' (c.comp q2) + incr' (c.comp q3) + incr' (c.comp q4) := by
  rw [incr'_eq hc, incr_quarter hc]
  rw [incr'_eq (c := c.comp q1) (fun t => hc (q1 t)),
    incr'_eq (c := c.comp q2) (fun t => hc (q2 t)),
    incr'_eq (c := c.comp q3) (fun t => hc (q3 t)),
    incr'_eq (c := c.comp q4) (fun t => hc (q4 t))]

/-! ## The four branches of the unfolded target curves on their quarters -/

theorem wi_tgtUpBun_quarter1 {h : Work.Smooth.SphereJordan.PlaneHypothesis} {hs : γ.IsSimple}
    {hball : ∀ θ : ℝ, ‖γ.γ θ‖ < 1} {S : Work.Smooth.Jordan.PlaneSchoenflies γ}
    (H : SpanHyp h hs hball S) (b : Bool) {σ : ℝ}
    (hσ : σ ∈ Set.Icc (0 : ℝ) (Real.pi / 2)) :
    tgtUpBun S H.t₁ H.s₁ H.t₂ H.s₂ b H.θ₁ H.θ₂ σ =
      Work.Smooth.SphereJordan.srcOuterUp S (σ / (Real.pi / 2)) := by
  simp only [tgtUpBun]
  rw [if_pos hσ.2]

theorem wi_tgtUpBun_quarter2 {h : Work.Smooth.SphereJordan.PlaneHypothesis} {hs : γ.IsSimple}
    {hball : ∀ θ : ℝ, ‖γ.γ θ‖ < 1} {S : Work.Smooth.Jordan.PlaneSchoenflies γ}
    (H : SpanHyp h hs hball S) (b : Bool) {σ : ℝ}
    (hσ : σ ∈ Set.Icc (Real.pi / 2) Real.pi) :
    tgtUpBun S H.t₁ H.s₁ H.t₂ H.s₂ b H.θ₁ H.θ₂ σ =
      Work.Smooth.SphereJordan.tgtCut₂ S H.t₂ H.s₂ ((σ - Real.pi / 2) / (Real.pi / 2)) := by
  by_cases hσa : σ ≤ Real.pi / 2
  · have hσeq : σ = Real.pi / 2 := le_antisymm hσa hσ.1
    subst hσeq
    have hL : Work.Smooth.SphereJordan.srcOuterUp S (Real.pi / 2 / (Real.pi / 2)) =
        -Work.Smooth.SphereJordan.cutDir S := by
      rw [div_self (by positivity : Real.pi / 2 ≠ 0), srcOuterUp_one]
    have hR : Work.Smooth.SphereJordan.tgtCut₂ S H.t₂ H.s₂
        ((Real.pi / 2 - Real.pi / 2) / (Real.pi / 2)) =
        -Work.Smooth.SphereJordan.cutDir S := by
      rw [sub_self, zero_div, tgtCut₂_zero, H.hout₂]
    simp only [tgtUpBun]
    rw [if_pos le_rfl, hL, hR]
  · simp only [tgtUpBun]
    rw [if_neg hσa, if_pos hσ.2]

theorem wi_tgtUpBun_quarter3 {h : Work.Smooth.SphereJordan.PlaneHypothesis} {hs : γ.IsSimple}
    {hball : ∀ θ : ℝ, ‖γ.γ θ‖ < 1} {S : Work.Smooth.Jordan.PlaneSchoenflies γ}
    (H : SpanHyp h hs hball S) (b : Bool) {σ : ℝ}
    (hσ : σ ∈ Set.Icc Real.pi (3 * Real.pi / 2)) :
    tgtUpBun S H.t₁ H.s₁ H.t₂ H.s₂ b H.θ₁ H.θ₂ σ =
      (if b then γ.γ (H.θ₂ + ((σ - Real.pi) / (Real.pi / 2)) * (H.θ₁ - H.θ₂))
        else γ.γ (H.θ₂ + ((σ - Real.pi) / (Real.pi / 2)) * (H.θ₁ - H.θ₂ - 2 * Real.pi))) := by
  by_cases hσa : σ ≤ Real.pi / 2
  · have : Real.pi ≤ Real.pi / 2 := le_trans hσ.1 hσa
    linarith [Real.pi_pos]
  · by_cases hσb : σ ≤ Real.pi
    · have hσeq : σ = Real.pi := le_antisymm hσb hσ.1
      subst hσeq
      have hR : Work.Smooth.SphereJordan.tgtCut₂ S H.t₂ H.s₂
          ((Real.pi - Real.pi / 2) / (Real.pi / 2)) =
          (Work.Smooth.SphereJordan.base S : ℂ) -
            (H.t₂ : ℂ) * Work.Smooth.SphereJordan.cutDir S := by
        rw [show (Real.pi - Real.pi / 2) / (Real.pi / 2) = 1 from by
          rw [div_eq_one_iff_eq (by positivity)]; ring, tgtCut₂_one]
      have hb1 : H.θ₂ + ((Real.pi - Real.pi) / (Real.pi / 2)) * (H.θ₁ - H.θ₂) = H.θ₂ := by
        ring
      have hb2 : H.θ₂ + ((Real.pi - Real.pi) / (Real.pi / 2)) *
          (H.θ₁ - H.θ₂ - 2 * Real.pi) = H.θ₂ := by ring
      simp only [tgtUpBun]
      rw [if_neg (by linarith [Real.pi_pos] : ¬ ((Real.pi : ℝ) ≤ Real.pi / 2)),
        if_pos le_rfl, hR]
      simp only [hb1, hb2]
      by_cases hb : b = true
      · rw [if_pos hb]; exact H.hθ₂.symm
      · rw [if_neg hb]; exact H.hθ₂.symm
    · simp only [tgtUpBun]
      rw [if_neg hσa, if_neg hσb, if_pos hσ.2]

theorem wi_tgtUpBun_quarter4 {h : Work.Smooth.SphereJordan.PlaneHypothesis} {hs : γ.IsSimple}
    {hball : ∀ θ : ℝ, ‖γ.γ θ‖ < 1} {S : Work.Smooth.Jordan.PlaneSchoenflies γ}
    (H : SpanHyp h hs hball S) (b : Bool) {σ : ℝ}
    (hσ : σ ∈ Set.Icc (3 * Real.pi / 2) (2 * Real.pi)) :
    tgtUpBun S H.t₁ H.s₁ H.t₂ H.s₂ b H.θ₁ H.θ₂ σ =
      Work.Smooth.SphereJordan.tgtCut₁ S H.t₁ H.s₁
        (1 - (σ - 3 * Real.pi / 2) / (Real.pi / 2)) := by
  by_cases hσa : σ ≤ Real.pi / 2
  · have : 3 * Real.pi / 2 ≤ Real.pi / 2 := le_trans hσ.1 hσa
    linarith [Real.pi_pos]
  · by_cases hσb : σ ≤ Real.pi
    · have : 3 * Real.pi / 2 ≤ Real.pi := le_trans hσ.1 hσb
      linarith [Real.pi_pos]
    · by_cases hσc : σ ≤ 3 * Real.pi / 2
      · have hσeq : σ = 3 * Real.pi / 2 := le_antisymm hσc hσ.1
        subst hσeq
        have hratio : (3 * Real.pi / 2 - Real.pi) / (Real.pi / 2) = 1 := by
          rw [div_eq_one_iff_eq (by positivity)]; ring
        have hDv : Work.Smooth.SphereJordan.tgtCut₁ S H.t₁ H.s₁
            (1 - (3 * Real.pi / 2 - 3 * Real.pi / 2) / (Real.pi / 2)) = γ.γ H.θ₁ := by
          rw [sub_self, zero_div, sub_zero, tgtCut₁_one, H.hθ₁]
        simp only [tgtUpBun]
        rw [if_neg (by linarith [Real.pi_pos] : ¬ ((3 * Real.pi / 2 : ℝ) ≤ Real.pi / 2)),
          if_neg (by linarith [Real.pi_pos] : ¬ ((3 * Real.pi / 2 : ℝ) ≤ Real.pi)),
          if_pos le_rfl, hDv, hratio]
        by_cases hb : b = true
        · rw [if_pos hb, show H.θ₂ + 1 * (H.θ₁ - H.θ₂) = H.θ₁ from by ring]
        · rw [if_neg hb,
            show H.θ₂ + 1 * (H.θ₁ - H.θ₂ - 2 * Real.pi) = H.θ₁ - 2 * Real.pi from by ring]
          have hper := γ.apply_add_int_mul (H.θ₁ - 2 * Real.pi) 1
          rw [show H.θ₁ - 2 * Real.pi + (1 : ℤ) * (2 * Real.pi) = H.θ₁ from by
            push_cast; ring] at hper
          exact hper.symm
      · simp only [tgtUpBun]
        rw [if_neg hσa, if_neg hσb, if_neg hσc]

theorem wi_tgtDnBun_quarter1 {h : Work.Smooth.SphereJordan.PlaneHypothesis} {hs : γ.IsSimple}
    {hball : ∀ θ : ℝ, ‖γ.γ θ‖ < 1} {S : Work.Smooth.Jordan.PlaneSchoenflies γ}
    (H : SpanHyp h hs hball S) (b : Bool) {σ : ℝ}
    (hσ : σ ∈ Set.Icc (0 : ℝ) (Real.pi / 2)) :
    tgtDnBun S H.t₁ H.s₁ H.t₂ H.s₂ b H.θ₁ H.θ₂ σ =
      Work.Smooth.SphereJordan.srcOuterDn S (σ / (Real.pi / 2)) := by
  simp only [tgtDnBun]
  rw [if_pos hσ.2]

theorem wi_tgtDnBun_quarter2 {h : Work.Smooth.SphereJordan.PlaneHypothesis} {hs : γ.IsSimple}
    {hball : ∀ θ : ℝ, ‖γ.γ θ‖ < 1} {S : Work.Smooth.Jordan.PlaneSchoenflies γ}
    (H : SpanHyp h hs hball S) (b : Bool) {σ : ℝ}
    (hσ : σ ∈ Set.Icc (Real.pi / 2) Real.pi) :
    tgtDnBun S H.t₁ H.s₁ H.t₂ H.s₂ b H.θ₁ H.θ₂ σ =
      Work.Smooth.SphereJordan.tgtCut₁ S H.t₁ H.s₁ ((σ - Real.pi / 2) / (Real.pi / 2)) := by
  by_cases hσa : σ ≤ Real.pi / 2
  · have hσeq : σ = Real.pi / 2 := le_antisymm hσa hσ.1
    subst hσeq
    have hL : Work.Smooth.SphereJordan.srcOuterDn S (Real.pi / 2 / (Real.pi / 2)) =
        Work.Smooth.SphereJordan.cutDir S := by
      rw [div_self (by positivity : Real.pi / 2 ≠ 0), srcOuterDn_one]
    have hR : Work.Smooth.SphereJordan.tgtCut₁ S H.t₁ H.s₁
        ((Real.pi / 2 - Real.pi / 2) / (Real.pi / 2)) =
        Work.Smooth.SphereJordan.cutDir S := by
      rw [sub_self, zero_div, tgtCut₁_zero, H.hout₁]
    simp only [tgtDnBun]
    rw [if_pos le_rfl, hL, hR]
  · simp only [tgtDnBun]
    rw [if_neg hσa, if_pos hσ.2]

theorem wi_tgtDnBun_quarter3 {h : Work.Smooth.SphereJordan.PlaneHypothesis} {hs : γ.IsSimple}
    {hball : ∀ θ : ℝ, ‖γ.γ θ‖ < 1} {S : Work.Smooth.Jordan.PlaneSchoenflies γ}
    (H : SpanHyp h hs hball S) (b : Bool) {σ : ℝ}
    (hσ : σ ∈ Set.Icc Real.pi (3 * Real.pi / 2)) :
    tgtDnBun S H.t₁ H.s₁ H.t₂ H.s₂ b H.θ₁ H.θ₂ σ =
      (if b then γ.γ (H.θ₁ - 2 * Real.pi +
          ((σ - Real.pi) / (Real.pi / 2)) * (H.θ₂ - H.θ₁ + 2 * Real.pi))
        else γ.γ (H.θ₁ + ((σ - Real.pi) / (Real.pi / 2)) * (H.θ₂ - H.θ₁))) := by
  by_cases hσa : σ ≤ Real.pi / 2
  · have : Real.pi ≤ Real.pi / 2 := le_trans hσ.1 hσa
    linarith [Real.pi_pos]
  · by_cases hσb : σ ≤ Real.pi
    · have hσeq : σ = Real.pi := le_antisymm hσb hσ.1
      subst hσeq
      have hR : Work.Smooth.SphereJordan.tgtCut₁ S H.t₁ H.s₁
          ((Real.pi - Real.pi / 2) / (Real.pi / 2)) =
          (Work.Smooth.SphereJordan.base S : ℂ) +
            (H.t₁ : ℂ) * Work.Smooth.SphereJordan.cutDir S := by
        rw [show (Real.pi - Real.pi / 2) / (Real.pi / 2) = 1 from by
          rw [div_eq_one_iff_eq (by positivity)]; ring, tgtCut₁_one]
      have hb1 : H.θ₁ - 2 * Real.pi + ((Real.pi - Real.pi) / (Real.pi / 2)) *
          (H.θ₂ - H.θ₁ + 2 * Real.pi) = H.θ₁ - 2 * Real.pi := by ring
      have hb2 : H.θ₁ + ((Real.pi - Real.pi) / (Real.pi / 2)) * (H.θ₂ - H.θ₁) = H.θ₁ := by
        ring
      have hun1 : γ.γ (H.θ₁ - 2 * Real.pi) = γ.γ H.θ₁ := by
        have hper := γ.apply_add_int_mul (H.θ₁ - 2 * Real.pi) 1
        rw [show H.θ₁ - 2 * Real.pi + (1 : ℤ) * (2 * Real.pi) = H.θ₁ from by
          push_cast; ring] at hper
        exact hper.symm
      simp only [tgtDnBun]
      rw [if_neg (by linarith [Real.pi_pos] : ¬ ((Real.pi : ℝ) ≤ Real.pi / 2)),
        if_pos le_rfl, hR]
      by_cases hb : b = true
      · rw [if_pos hb, hb1, hun1]; exact H.hθ₁.symm
      · rw [if_neg hb, hb2]; exact H.hθ₁.symm
    · simp only [tgtDnBun]
      rw [if_neg hσa, if_neg hσb, if_pos hσ.2]

theorem wi_tgtDnBun_quarter4 {h : Work.Smooth.SphereJordan.PlaneHypothesis} {hs : γ.IsSimple}
    {hball : ∀ θ : ℝ, ‖γ.γ θ‖ < 1} {S : Work.Smooth.Jordan.PlaneSchoenflies γ}
    (H : SpanHyp h hs hball S) (b : Bool) {σ : ℝ}
    (hσ : σ ∈ Set.Icc (3 * Real.pi / 2) (2 * Real.pi)) :
    tgtDnBun S H.t₁ H.s₁ H.t₂ H.s₂ b H.θ₁ H.θ₂ σ =
      Work.Smooth.SphereJordan.tgtCut₂ S H.t₂ H.s₂
        (1 - (σ - 3 * Real.pi / 2) / (Real.pi / 2)) := by
  by_cases hσa : σ ≤ Real.pi / 2
  · have : 3 * Real.pi / 2 ≤ Real.pi / 2 := le_trans hσ.1 hσa
    linarith [Real.pi_pos]
  · by_cases hσb : σ ≤ Real.pi
    · have : 3 * Real.pi / 2 ≤ Real.pi := le_trans hσ.1 hσb
      linarith [Real.pi_pos]
    · by_cases hσc : σ ≤ 3 * Real.pi / 2
      · have hσeq : σ = 3 * Real.pi / 2 := le_antisymm hσc hσ.1
        subst hσeq
        have hratio : (3 * Real.pi / 2 - Real.pi) / (Real.pi / 2) = 1 := by
          rw [div_eq_one_iff_eq (by positivity)]; ring
        have hDv : Work.Smooth.SphereJordan.tgtCut₂ S H.t₂ H.s₂
            (1 - (3 * Real.pi / 2 - 3 * Real.pi / 2) / (Real.pi / 2)) =
            (Work.Smooth.SphereJordan.base S : ℂ) -
              (H.t₂ : ℂ) * Work.Smooth.SphereJordan.cutDir S := by
          rw [sub_self, zero_div, sub_zero, tgtCut₂_one]
        simp only [tgtDnBun]
        rw [if_neg (by linarith [Real.pi_pos] : ¬ ((3 * Real.pi / 2 : ℝ) ≤ Real.pi / 2)),
          if_neg (by linarith [Real.pi_pos] : ¬ ((3 * Real.pi / 2 : ℝ) ≤ Real.pi)),
          if_pos le_rfl, hDv, hratio]
        by_cases hb : b = true
        · rw [if_pos hb,
            show H.θ₁ - 2 * Real.pi + 1 * (H.θ₂ - H.θ₁ + 2 * Real.pi) = H.θ₂ from by ring,
            H.hθ₂]
        · rw [if_neg hb, show H.θ₁ + 1 * (H.θ₂ - H.θ₁) = H.θ₂ from by ring, H.hθ₂]
      · simp only [tgtDnBun]
        rw [if_neg hσa, if_neg hσb, if_neg hσc]


/-! ## The four quarter pieces of the two loops -/

theorem wi_upLoop_q1 {h : Work.Smooth.SphereJordan.PlaneHypothesis} {hs : γ.IsSimple}
    {hball : ∀ θ : ℝ, ‖γ.γ θ‖ < 1} {S : Work.Smooth.Jordan.PlaneSchoenflies γ}
    (H : SpanHyp h hs hball S) (x : ℂ) (b : Bool) :
    ∀ t : unitInterval, upLoop H x b (q1 t) = upP1 H x t := by
  intro t
  have hσ1 : 2 * Real.pi * ((q1 t : unitInterval) : ℝ) ∈ Set.Icc (0 : ℝ) (Real.pi / 2) := by
    rw [two_pi_q1]
    constructor <;> nlinarith [t.2.1, t.2.2, Real.pi_pos]
  have hlt : 2 * Real.pi * ((q1 t : unitInterval) : ℝ) ∈ Set.Ico (0 : ℝ) (2 * Real.pi) :=
    ⟨hσ1.1, by linarith [hσ1.2, Real.pi_pos]⟩
  have harg : (2 * Real.pi * ((q1 t : unitInterval) : ℝ)) / (Real.pi / 2) = (t : ℝ) := by
    rw [two_pi_q1]; field_simp
  show Work.Smooth.SphereJordan.tgtUpB S H.t₁ H.s₁ H.t₂ H.s₂ b H.θ₁ H.θ₂
      (2 * Real.pi * ((q1 t : unitInterval) : ℝ)) - x
    = Work.Smooth.SphereJordan.srcOuterUp S ((t : unitInterval) : ℝ) - x
  rw [tgtUpB_eq, perPt_self hlt, wi_tgtUpBun_quarter1 H b hσ1, harg]

theorem wi_upLoop_q2 {h : Work.Smooth.SphereJordan.PlaneHypothesis} {hs : γ.IsSimple}
    {hball : ∀ θ : ℝ, ‖γ.γ θ‖ < 1} {S : Work.Smooth.Jordan.PlaneSchoenflies γ}
    (H : SpanHyp h hs hball S) (x : ℂ) (b : Bool) :
    ∀ t : unitInterval, upLoop H x b (q2 t) = upP2 H x t := by
  intro t
  have hσ1 : 2 * Real.pi * ((q2 t : unitInterval) : ℝ) ∈ Set.Icc (Real.pi / 2) Real.pi := by
    rw [two_pi_q2]
    constructor <;> nlinarith [t.2.1, t.2.2, Real.pi_pos]
  have hlt : 2 * Real.pi * ((q2 t : unitInterval) : ℝ) ∈ Set.Ico (0 : ℝ) (2 * Real.pi) :=
    ⟨by linarith [hσ1.1, Real.pi_pos], by linarith [hσ1.2, Real.pi_pos]⟩
  have harg : (2 * Real.pi * ((q2 t : unitInterval) : ℝ) - Real.pi / 2) / (Real.pi / 2)
      = (t : ℝ) := by
    rw [two_pi_q2]; field_simp; ring
  show Work.Smooth.SphereJordan.tgtUpB S H.t₁ H.s₁ H.t₂ H.s₂ b H.θ₁ H.θ₂
      (2 * Real.pi * ((q2 t : unitInterval) : ℝ)) - x
    = Work.Smooth.SphereJordan.tgtCut₂ S H.t₂ H.s₂ ((t : unitInterval) : ℝ) - x
  rw [tgtUpB_eq, perPt_self hlt, wi_tgtUpBun_quarter2 H b hσ1, harg]

theorem wi_upLoop_q3 {h : Work.Smooth.SphereJordan.PlaneHypothesis} {hs : γ.IsSimple}
    {hball : ∀ θ : ℝ, ‖γ.γ θ‖ < 1} {S : Work.Smooth.Jordan.PlaneSchoenflies γ}
    (H : SpanHyp h hs hball S) (x : ℂ) (b : Bool) :
    ∀ t : unitInterval, upLoop H x b (q3 t) = upP3 H x b t := by
  intro t
  have hσ1 : 2 * Real.pi * ((q3 t : unitInterval) : ℝ) ∈ Set.Icc Real.pi (3 * Real.pi / 2) := by
    rw [two_pi_q3]
    constructor <;> nlinarith [t.2.1, t.2.2, Real.pi_pos]
  have hlt : 2 * Real.pi * ((q3 t : unitInterval) : ℝ) ∈ Set.Ico (0 : ℝ) (2 * Real.pi) :=
    ⟨by linarith [hσ1.1, Real.pi_pos], by linarith [hσ1.2, Real.pi_pos]⟩
  have harg : (2 * Real.pi * ((q3 t : unitInterval) : ℝ) - Real.pi) / (Real.pi / 2)
      = (t : ℝ) := by
    rw [two_pi_q3]; field_simp; ring
  show Work.Smooth.SphereJordan.tgtUpB S H.t₁ H.s₁ H.t₂ H.s₂ b H.θ₁ H.θ₂
      (2 * Real.pi * ((q3 t : unitInterval) : ℝ)) - x
    = (if b then γ.γ (H.θ₂ + ((t : unitInterval) : ℝ) * (H.θ₁ - H.θ₂))
        else γ.γ (H.θ₂ + ((t : unitInterval) : ℝ) * (H.θ₁ - H.θ₂ - 2 * Real.pi))) - x
  rw [tgtUpB_eq, perPt_self hlt, wi_tgtUpBun_quarter3 H b hσ1, harg]

theorem wi_upLoop_q4 {h : Work.Smooth.SphereJordan.PlaneHypothesis} {hs : γ.IsSimple}
    {hball : ∀ θ : ℝ, ‖γ.γ θ‖ < 1} {S : Work.Smooth.Jordan.PlaneSchoenflies γ}
    (H : SpanHyp h hs hball S) (x : ℂ) (b : Bool) :
    ∀ t : unitInterval, upLoop H x b (q4 t) = upP4 H x t := by
  intro t
  rcases lt_or_eq_of_le t.2.2 with ht | ht
  · have hσ1 : 2 * Real.pi * ((q4 t : unitInterval) : ℝ) ∈
        Set.Icc (3 * Real.pi / 2) (2 * Real.pi) := by
      rw [q4_val]
      constructor <;> nlinarith [t.2.1, ht, Real.pi_pos]
    have hlt2 : 2 * Real.pi * ((q4 t : unitInterval) : ℝ) < 2 * Real.pi := by
      rw [q4_val]; nlinarith [ht, Real.pi_pos]
    have hlt : 2 * Real.pi * ((q4 t : unitInterval) : ℝ) ∈ Set.Ico (0 : ℝ) (2 * Real.pi) :=
      ⟨by linarith [hσ1.1, Real.pi_pos], hlt2⟩
    have harg : 1 - (2 * Real.pi * ((q4 t : unitInterval) : ℝ) - 3 * Real.pi / 2) /
        (Real.pi / 2) = 1 - (t : ℝ) := by
      rw [q4_val]; field_simp; ring
    show Work.Smooth.SphereJordan.tgtUpB S H.t₁ H.s₁ H.t₂ H.s₂ b H.θ₁ H.θ₂
        (2 * Real.pi * ((q4 t : unitInterval) : ℝ)) - x
      = Work.Smooth.SphereJordan.tgtCut₁ S H.t₁ H.s₁
        (1 - ((t : unitInterval) : ℝ)) - x
    rw [tgtUpB_eq, perPt_self hlt, wi_tgtUpBun_quarter4 H b hσ1, harg]
  · have hq4 : ((q4 t : unitInterval) : ℝ) = 1 := by rw [q4_val, ht]; norm_num
    have h2pi : 2 * Real.pi * ((q4 t : unitInterval) : ℝ) = 2 * Real.pi := by
      rw [hq4]; ring
    have hone : ((t : unitInterval) : ℝ) = 1 := ht
    show Work.Smooth.SphereJordan.tgtUpB S H.t₁ H.s₁ H.t₂ H.s₂ b H.θ₁ H.θ₂
        (2 * Real.pi * ((q4 t : unitInterval) : ℝ)) - x
      = Work.Smooth.SphereJordan.tgtCut₁ S H.t₁ H.s₁
        (1 - ((t : unitInterval) : ℝ)) - x
    rw [h2pi, tgtUpB_eq, wi_perPt_two_pi, hone, sub_self,
      wi_tgtUpBun_quarter1 H b (⟨le_rfl, by positivity⟩ : (0 : ℝ) ∈ Set.Icc (0 : ℝ) (Real.pi / 2)),
      zero_div, srcOuterUp_zero, tgtCut₁_zero, H.hout₁]

theorem wi_dnLoop_q1 {h : Work.Smooth.SphereJordan.PlaneHypothesis} {hs : γ.IsSimple}
    {hball : ∀ θ : ℝ, ‖γ.γ θ‖ < 1} {S : Work.Smooth.Jordan.PlaneSchoenflies γ}
    (H : SpanHyp h hs hball S) (x : ℂ) (b : Bool) :
    ∀ t : unitInterval, dnLoop H x b (q1 t) = dnP1 H x t := by
  intro t
  have hσ1 : 2 * Real.pi * ((q1 t : unitInterval) : ℝ) ∈ Set.Icc (0 : ℝ) (Real.pi / 2) := by
    rw [two_pi_q1]
    constructor <;> nlinarith [t.2.1, t.2.2, Real.pi_pos]
  have hlt : 2 * Real.pi * ((q1 t : unitInterval) : ℝ) ∈ Set.Ico (0 : ℝ) (2 * Real.pi) :=
    ⟨hσ1.1, by linarith [hσ1.2, Real.pi_pos]⟩
  have harg : (2 * Real.pi * ((q1 t : unitInterval) : ℝ)) / (Real.pi / 2) = (t : ℝ) := by
    rw [two_pi_q1]; field_simp
  show Work.Smooth.SphereJordan.tgtDnB S H.t₁ H.s₁ H.t₂ H.s₂ b H.θ₁ H.θ₂
      (2 * Real.pi * ((q1 t : unitInterval) : ℝ)) - x
    = Work.Smooth.SphereJordan.srcOuterDn S ((t : unitInterval) : ℝ) - x
  rw [tgtDnB_eq, perPt_self hlt, wi_tgtDnBun_quarter1 H b hσ1, harg]

theorem wi_dnLoop_q2 {h : Work.Smooth.SphereJordan.PlaneHypothesis} {hs : γ.IsSimple}
    {hball : ∀ θ : ℝ, ‖γ.γ θ‖ < 1} {S : Work.Smooth.Jordan.PlaneSchoenflies γ}
    (H : SpanHyp h hs hball S) (x : ℂ) (b : Bool) :
    ∀ t : unitInterval, dnLoop H x b (q2 t) = dnP2 H x t := by
  intro t
  have hσ1 : 2 * Real.pi * ((q2 t : unitInterval) : ℝ) ∈ Set.Icc (Real.pi / 2) Real.pi := by
    rw [two_pi_q2]
    constructor <;> nlinarith [t.2.1, t.2.2, Real.pi_pos]
  have hlt : 2 * Real.pi * ((q2 t : unitInterval) : ℝ) ∈ Set.Ico (0 : ℝ) (2 * Real.pi) :=
    ⟨by linarith [hσ1.1, Real.pi_pos], by linarith [hσ1.2, Real.pi_pos]⟩
  have harg : (2 * Real.pi * ((q2 t : unitInterval) : ℝ) - Real.pi / 2) / (Real.pi / 2)
      = (t : ℝ) := by
    rw [two_pi_q2]; field_simp; ring
  show Work.Smooth.SphereJordan.tgtDnB S H.t₁ H.s₁ H.t₂ H.s₂ b H.θ₁ H.θ₂
      (2 * Real.pi * ((q2 t : unitInterval) : ℝ)) - x
    = Work.Smooth.SphereJordan.tgtCut₁ S H.t₁ H.s₁ ((t : unitInterval) : ℝ) - x
  rw [tgtDnB_eq, perPt_self hlt, wi_tgtDnBun_quarter2 H b hσ1, harg]

theorem wi_dnLoop_q3 {h : Work.Smooth.SphereJordan.PlaneHypothesis} {hs : γ.IsSimple}
    {hball : ∀ θ : ℝ, ‖γ.γ θ‖ < 1} {S : Work.Smooth.Jordan.PlaneSchoenflies γ}
    (H : SpanHyp h hs hball S) (x : ℂ) (b : Bool) :
    ∀ t : unitInterval, dnLoop H x b (q3 t) = dnP3 H x b t := by
  intro t
  have hσ1 : 2 * Real.pi * ((q3 t : unitInterval) : ℝ) ∈ Set.Icc Real.pi (3 * Real.pi / 2) := by
    rw [two_pi_q3]
    constructor <;> nlinarith [t.2.1, t.2.2, Real.pi_pos]
  have hlt : 2 * Real.pi * ((q3 t : unitInterval) : ℝ) ∈ Set.Ico (0 : ℝ) (2 * Real.pi) :=
    ⟨by linarith [hσ1.1, Real.pi_pos], by linarith [hσ1.2, Real.pi_pos]⟩
  have harg : (2 * Real.pi * ((q3 t : unitInterval) : ℝ) - Real.pi) / (Real.pi / 2)
      = (t : ℝ) := by
    rw [two_pi_q3]; field_simp; ring
  show Work.Smooth.SphereJordan.tgtDnB S H.t₁ H.s₁ H.t₂ H.s₂ b H.θ₁ H.θ₂
      (2 * Real.pi * ((q3 t : unitInterval) : ℝ)) - x
    = (if b then γ.γ (H.θ₁ - 2 * Real.pi + ((t : unitInterval) : ℝ) *
          (H.θ₂ - H.θ₁ + 2 * Real.pi))
        else γ.γ (H.θ₁ + ((t : unitInterval) : ℝ) * (H.θ₂ - H.θ₁))) - x
  rw [tgtDnB_eq, perPt_self hlt, wi_tgtDnBun_quarter3 H b hσ1, harg]

theorem wi_dnLoop_q4 {h : Work.Smooth.SphereJordan.PlaneHypothesis} {hs : γ.IsSimple}
    {hball : ∀ θ : ℝ, ‖γ.γ θ‖ < 1} {S : Work.Smooth.Jordan.PlaneSchoenflies γ}
    (H : SpanHyp h hs hball S) (x : ℂ) (b : Bool) :
    ∀ t : unitInterval, dnLoop H x b (q4 t) = dnP4 H x t := by
  intro t
  rcases lt_or_eq_of_le t.2.2 with ht | ht
  · have hσ1 : 2 * Real.pi * ((q4 t : unitInterval) : ℝ) ∈
        Set.Icc (3 * Real.pi / 2) (2 * Real.pi) := by
      rw [q4_val]
      constructor <;> nlinarith [t.2.1, ht, Real.pi_pos]
    have hlt2 : 2 * Real.pi * ((q4 t : unitInterval) : ℝ) < 2 * Real.pi := by
      rw [q4_val]; nlinarith [ht, Real.pi_pos]
    have hlt : 2 * Real.pi * ((q4 t : unitInterval) : ℝ) ∈ Set.Ico (0 : ℝ) (2 * Real.pi) :=
      ⟨by linarith [hσ1.1, Real.pi_pos], hlt2⟩
    have harg : 1 - (2 * Real.pi * ((q4 t : unitInterval) : ℝ) - 3 * Real.pi / 2) /
        (Real.pi / 2) = 1 - (t : ℝ) := by
      rw [q4_val]; field_simp; ring
    show Work.Smooth.SphereJordan.tgtDnB S H.t₁ H.s₁ H.t₂ H.s₂ b H.θ₁ H.θ₂
        (2 * Real.pi * ((q4 t : unitInterval) : ℝ)) - x
      = Work.Smooth.SphereJordan.tgtCut₂ S H.t₂ H.s₂
        (1 - ((t : unitInterval) : ℝ)) - x
    rw [tgtDnB_eq, perPt_self hlt, wi_tgtDnBun_quarter4 H b hσ1, harg]
  · have hq4 : ((q4 t : unitInterval) : ℝ) = 1 := by rw [q4_val, ht]; norm_num
    have h2pi : 2 * Real.pi * ((q4 t : unitInterval) : ℝ) = 2 * Real.pi := by
      rw [hq4]; ring
    have hone : ((t : unitInterval) : ℝ) = 1 := ht
    show Work.Smooth.SphereJordan.tgtDnB S H.t₁ H.s₁ H.t₂ H.s₂ b H.θ₁ H.θ₂
        (2 * Real.pi * ((q4 t : unitInterval) : ℝ)) - x
      = Work.Smooth.SphereJordan.tgtCut₂ S H.t₂ H.s₂
        (1 - ((t : unitInterval) : ℝ)) - x
    rw [h2pi, tgtDnB_eq, wi_perPt_two_pi, hone, sub_self,
      wi_tgtDnBun_quarter1 H b (⟨le_rfl, by positivity⟩ : (0 : ℝ) ∈ Set.Icc (0 : ℝ) (Real.pi / 2)),
      zero_div, srcOuterDn_zero, tgtCut₂_zero, H.hout₂]

/-! ## The four loops are closed, and the crosscut pieces cancel in pairs -/

theorem wi_upLoop_closed {h : Work.Smooth.SphereJordan.PlaneHypothesis} {hs : γ.IsSimple}
    {hball : ∀ θ : ℝ, ‖γ.γ θ‖ < 1} {S : Work.Smooth.Jordan.PlaneSchoenflies γ}
    (H : SpanHyp h hs hball S) (x : ℂ) (b : Bool) : upLoop H x b 0 = upLoop H x b 1 := by
  have h0 : 2 * Real.pi * ((0 : unitInterval) : ℝ) = 0 := by simp
  have h2 : 2 * Real.pi * ((1 : unitInterval) : ℝ) = 2 * Real.pi := by simp
  have hper : Work.Smooth.SphereJordan.tgtUpB S H.t₁ H.s₁ H.t₂ H.s₂ b H.θ₁ H.θ₂ 0 =
      Work.Smooth.SphereJordan.tgtUpB S H.t₁ H.s₁ H.t₂ H.s₂ b H.θ₁ H.θ₂ (2 * Real.pi) := by
    simpa using ((H.upPC b).periodic_apply 0).symm
  show Work.Smooth.SphereJordan.tgtUpB S H.t₁ H.s₁ H.t₂ H.s₂ b H.θ₁ H.θ₂
      (2 * Real.pi * ((0 : unitInterval) : ℝ)) - x
    = Work.Smooth.SphereJordan.tgtUpB S H.t₁ H.s₁ H.t₂ H.s₂ b H.θ₁ H.θ₂
      (2 * Real.pi * ((1 : unitInterval) : ℝ)) - x
  rw [h0, h2, hper]

theorem wi_dnLoop_closed {h : Work.Smooth.SphereJordan.PlaneHypothesis} {hs : γ.IsSimple}
    {hball : ∀ θ : ℝ, ‖γ.γ θ‖ < 1} {S : Work.Smooth.Jordan.PlaneSchoenflies γ}
    (H : SpanHyp h hs hball S) (x : ℂ) (b : Bool) : dnLoop H x b 0 = dnLoop H x b 1 := by
  have h0 : 2 * Real.pi * ((0 : unitInterval) : ℝ) = 0 := by simp
  have h2 : 2 * Real.pi * ((1 : unitInterval) : ℝ) = 2 * Real.pi := by simp
  have hper : Work.Smooth.SphereJordan.tgtDnB S H.t₁ H.s₁ H.t₂ H.s₂ b H.θ₁ H.θ₂ 0 =
      Work.Smooth.SphereJordan.tgtDnB S H.t₁ H.s₁ H.t₂ H.s₂ b H.θ₁ H.θ₂ (2 * Real.pi) := by
    simpa using ((H.dnPC b).periodic_apply 0).symm
  show Work.Smooth.SphereJordan.tgtDnB S H.t₁ H.s₁ H.t₂ H.s₂ b H.θ₁ H.θ₂
      (2 * Real.pi * ((0 : unitInterval) : ℝ)) - x
    = Work.Smooth.SphereJordan.tgtDnB S H.t₁ H.s₁ H.t₂ H.s₂ b H.θ₁ H.θ₂
      (2 * Real.pi * ((1 : unitInterval) : ℝ)) - x
  rw [h0, h2, hper]

theorem wi_incr'_cut_pair {h : Work.Smooth.SphereJordan.PlaneHypothesis} {hs : γ.IsSimple}
    {hball : ∀ θ : ℝ, ‖γ.γ θ‖ < 1} {S : Work.Smooth.Jordan.PlaneSchoenflies γ}
    (H : SpanHyp h hs hball S) (x : ℂ) :
    (incr' (upP2 H x) + incr' (dnP4 H x) = 0) ∧
      (incr' (dnP2 H x) + incr' (upP4 H x) = 0) := by
  constructor
  · have hcongr : ∀ t : unitInterval, dnP4 H x t = (upP2 H x).comp revI t := by
      intro t
      simp only [ContinuousMap.comp_apply]
      show Work.Smooth.SphereJordan.tgtCut₂ S H.t₂ H.s₂ (1 - (t : ℝ)) - x =
        Work.Smooth.SphereJordan.tgtCut₂ S H.t₂ H.s₂ ((revI t : unitInterval) : ℝ) - x
      rw [revI_val]
    rw [incr'_congr hcongr, incr'_rev]
    ring
  · have hcongr : ∀ t : unitInterval, upP4 H x t = (dnP2 H x).comp revI t := by
      intro t
      simp only [ContinuousMap.comp_apply]
      show Work.Smooth.SphereJordan.tgtCut₁ S H.t₁ H.s₁ (1 - (t : ℝ)) - x =
        Work.Smooth.SphereJordan.tgtCut₁ S H.t₁ H.s₁ ((revI t : unitInterval) : ℝ) - x
      rw [revI_val]
    rw [incr'_congr hcongr, incr'_rev]
    ring


/-! ## The two outer semicircles and the unit circle -/

/-- The unit circle, traversed once from `cutDir S`. -/
def wiStdLoop (S : Work.Smooth.Jordan.PlaneSchoenflies γ) : C(unitInterval, ℂ) :=
  ⟨fun t => Work.Smooth.SphereJordan.cutDir S *
      Complex.exp ((((2 * Real.pi * ((t : unitInterval) : ℝ) : ℝ)) : ℂ) * Complex.I),
    by fun_prop⟩

theorem wi_std_norm (S : Work.Smooth.Jordan.PlaneSchoenflies γ) (t : unitInterval) :
    ‖wiStdLoop S t‖ = 1 := by
  show ‖Work.Smooth.SphereJordan.cutDir S * Complex.exp
      ((((2 * Real.pi * ((t : unitInterval) : ℝ) : ℝ)) : ℂ) * Complex.I)‖ = 1
  rw [norm_mul, Work.Smooth.SphereJordan.norm_cutDir, one_mul,
    Complex.norm_exp_ofReal_mul_I]

theorem wi_std_closed (S : Work.Smooth.Jordan.PlaneSchoenflies γ) :
    wiStdLoop S 0 = wiStdLoop S 1 := by
  have h0c : ((((2 * Real.pi * ((0 : unitInterval) : ℝ) : ℝ)) : ℂ) * Complex.I) = 0 := by
    rw [show 2 * Real.pi * ((0 : unitInterval) : ℝ) = 0 from by simp]
    simp
  have h1c : ((((2 * Real.pi * ((1 : unitInterval) : ℝ) : ℝ)) : ℂ) * Complex.I)
      = 2 * (Real.pi : ℂ) * Complex.I := by
    rw [show 2 * Real.pi * ((1 : unitInterval) : ℝ) = 2 * Real.pi from by simp]
    push_cast
    ring
  show Work.Smooth.SphereJordan.cutDir S * Complex.exp
      ((((2 * Real.pi * ((0 : unitInterval) : ℝ) : ℝ)) : ℂ) * Complex.I)
    = Work.Smooth.SphereJordan.cutDir S * Complex.exp
      ((((2 * Real.pi * ((1 : unitInterval) : ℝ) : ℝ)) : ℂ) * Complex.I)
  rw [h0c, h1c, Complex.exp_zero, Complex.exp_two_pi_mul_I]

theorem wi_loopIndex_std (S : Work.Smooth.Jordan.PlaneSchoenflies γ) :
    Work.Smooth.SphereJordan.loopIndex (wiStdLoop S) = 1 := by
  have hne : ∀ t : unitInterval, wiStdLoop S t ≠ 0 := by
    intro t h
    have h1 : ‖wiStdLoop S t‖ = 1 := wi_std_norm S t
    rw [h, norm_zero] at h1
    exact one_ne_zero h1.symm
  have hcl : wiStdLoop S 0 = wiStdLoop S 1 := wi_std_closed S
  set Λ : C(unitInterval, ℂ) :=
    ⟨fun t => Complex.log (Work.Smooth.SphereJordan.cutDir S) +
      ((((2 * Real.pi * ((t : unitInterval) : ℝ) : ℝ)) : ℂ) * Complex.I), by fun_prop⟩ with hΛ
  have hlift : ∀ t : unitInterval, Complex.exp (Λ t) = wiStdLoop S t := by
    intro t
    show Complex.exp (Complex.log (Work.Smooth.SphereJordan.cutDir S) +
      ((((2 * Real.pi * ((t : unitInterval) : ℝ) : ℝ)) : ℂ) * Complex.I)) =
      Work.Smooth.SphereJordan.cutDir S * Complex.exp
        ((((2 * Real.pi * ((t : unitInterval) : ℝ) : ℝ)) : ℂ) * Complex.I)
    rw [Complex.exp_add, Complex.exp_log (Work.Smooth.SphereJordan.cutDir_ne_zero S)]
  have hspec := Work.Smooth.SphereJordan.loopIndex_spec (wiStdLoop S) hne hcl Λ hlift
  have hsub : Λ 1 - Λ 0 = ((((2 * Real.pi * ((1 : unitInterval) : ℝ) : ℝ)) : ℂ) * Complex.I) -
      ((((2 * Real.pi * ((0 : unitInterval) : ℝ) : ℝ)) : ℂ) * Complex.I) := by
    show (Complex.log (Work.Smooth.SphereJordan.cutDir S) +
        ((((2 * Real.pi * ((1 : unitInterval) : ℝ) : ℝ)) : ℂ) * Complex.I)) -
      (Complex.log (Work.Smooth.SphereJordan.cutDir S) +
        ((((2 * Real.pi * ((0 : unitInterval) : ℝ) : ℝ)) : ℂ) * Complex.I)) = _
    ring
  have hval : ((((2 * Real.pi * ((1 : unitInterval) : ℝ) : ℝ)) : ℂ) * Complex.I) -
      ((((2 * Real.pi * ((0 : unitInterval) : ℝ) : ℝ)) : ℂ) * Complex.I)
      = 2 * (Real.pi : ℂ) * Complex.I := by
    rw [show 2 * Real.pi * ((1 : unitInterval) : ℝ) = 2 * Real.pi from by simp,
      show 2 * Real.pi * ((0 : unitInterval) : ℝ) = 0 from by simp]
    push_cast
    ring
  rw [hsub, hval] at hspec
  have h4 : (((Work.Smooth.SphereJordan.loopIndex (wiStdLoop S) : ℤ)) : ℂ)
      * (2 * (Real.pi : ℂ) * Complex.I) = 2 * (Real.pi : ℂ) * Complex.I := hspec.symm
  have h5 : ((((Work.Smooth.SphereJordan.loopIndex (wiStdLoop S) : ℤ)) : ℂ) - 1)
      * (2 * (Real.pi : ℂ) * Complex.I) = 0 := by
    rw [sub_mul, one_mul, h4, sub_self]
  rcases mul_eq_zero.mp h5 with h | h
  · have h6 : ((Work.Smooth.SphereJordan.loopIndex (wiStdLoop S) : ℤ) : ℂ) = 1 := by
      linear_combination h
    exact_mod_cast h6
  · exact absurd h (Work.Smooth.SphereJordan.two_pi_I_ne_zero)

/-- The loop of the unit circle about `x` is the standard loop translated by `x`. -/
theorem wi_outerLoop_eq_std {h : Work.Smooth.SphereJordan.PlaneHypothesis} {hs : γ.IsSimple}
    {hball : ∀ θ : ℝ, ‖γ.γ θ‖ < 1} {S : Work.Smooth.Jordan.PlaneSchoenflies γ}
    (H : SpanHyp h hs hball S) (x : ℂ) (t : unitInterval) :
    outerLoop H x t = wiStdLoop S t - x := rfl

theorem wi_outerLoop_closed {h : Work.Smooth.SphereJordan.PlaneHypothesis} {hs : γ.IsSimple}
    {hball : ∀ θ : ℝ, ‖γ.γ θ‖ < 1} {S : Work.Smooth.Jordan.PlaneSchoenflies γ}
    (H : SpanHyp h hs hball S) (x : ℂ) : outerLoop H x 0 = outerLoop H x 1 := by
  rw [wi_outerLoop_eq_std H x 0, wi_outerLoop_eq_std H x 1, wi_std_closed S]

theorem wi_outerLoop_ne {h : Work.Smooth.SphereJordan.PlaneHypothesis} {hs : γ.IsSimple}
    {hball : ∀ θ : ℝ, ‖γ.γ θ‖ < 1} {S : Work.Smooth.Jordan.PlaneSchoenflies γ}
    (H : SpanHyp h hs hball S) {x : ℂ} (hx : x ∈ S.V) : ∀ t, outerLoop H x t ≠ 0 := by
  intro t hcon
  have hxlt : ‖x‖ < 1 := norm_lt_one_of_mem_V S hball hx
  have h1 : wiStdLoop S t = x := by
    have h2 : wiStdLoop S t - x = 0 := by rw [← wi_outerLoop_eq_std H x t]; exact hcon
    exact sub_eq_zero.mp h2
  have h2 : ‖x‖ = 1 := by rw [← h1, wi_std_norm S t]
  linarith

theorem wi_loopIndex_outer {h : Work.Smooth.SphereJordan.PlaneHypothesis} {hs : γ.IsSimple}
    {hball : ∀ θ : ℝ, ‖γ.γ θ‖ < 1} {S : Work.Smooth.Jordan.PlaneSchoenflies γ}
    (H : SpanHyp h hs hball S) {x : ℂ} (hx : x ∈ S.V) :
    Work.Smooth.SphereJordan.loopIndex (outerLoop H x) = 1 := by
  have hxlt : ‖x‖ < 1 := norm_lt_one_of_mem_V S hball hx
  have hne0 : ∀ t : unitInterval, wiStdLoop S t ≠ 0 := by
    intro t h
    have h1 : ‖wiStdLoop S t‖ = 1 := wi_std_norm S t
    rw [h, norm_zero] at h1
    exact one_ne_zero h1.symm
  have hne1 : ∀ t : unitInterval, outerLoop H x t ≠ 0 := wi_outerLoop_ne H hx
  set Hs : C(unitInterval × unitInterval, ℂ) :=
    ⟨fun p => wiStdLoop S p.1 - ((((p.2 : unitInterval) : ℝ)) : ℂ) * x, by fun_prop⟩ with hHs
  have happ : ∀ p : unitInterval × unitInterval, Hs p =
      wiStdLoop S p.1 - ((((p.2 : unitInterval) : ℝ)) : ℂ) * x := fun p => rfl
  have hHne : ∀ p : unitInterval × unitInterval, Hs p ≠ 0 := by
    rintro ⟨t, s⟩ hcon
    rw [happ] at hcon
    have hEq : wiStdLoop S t = ((((s : unitInterval) : ℝ)) : ℂ) * x := sub_eq_zero.mp hcon
    have h1 : ‖wiStdLoop S t‖ = 1 := wi_std_norm S t
    have h2 : ‖((((s : unitInterval) : ℝ)) : ℂ) * x‖ = 1 := by rw [← hEq, h1]
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg s.2.1] at h2
    nlinarith [norm_nonneg x, hxlt, h2, s.2.1, s.2.2]
  have hH0 : ∀ t : unitInterval, Hs (t, 0) = wiStdLoop S t := by
    intro t
    rw [happ]
    simp
  have hH1 : ∀ t : unitInterval, Hs (t, 1) = outerLoop H x t := by
    intro t
    rw [happ, wi_outerLoop_eq_std H x t]
    simp
  have hHloop : ∀ s : unitInterval, Hs (0, s) = Hs (1, s) := by
    intro s
    rw [happ, happ]
    rw [wi_std_closed S]
  have h := Work.Smooth.SphereJordan.loopIndex_eq_of_homotopy hne0 hne1 Hs hHne hH0 hH1 hHloop
  exact h.symm.trans (wi_loopIndex_std S)

theorem wi_incr'_outer {h : Work.Smooth.SphereJordan.PlaneHypothesis} {hs : γ.IsSimple}
    {hball : ∀ θ : ℝ, ‖γ.γ θ‖ < 1} {S : Work.Smooth.Jordan.PlaneSchoenflies γ}
    (H : SpanHyp h hs hball S) {x : ℂ} (hx : x ∈ S.V) : incr' (outerLoop H x) = kappa := by
  have hne : ∀ t, outerLoop H x t ≠ 0 := wi_outerLoop_ne H hx
  have hcl : outerLoop H x 0 = outerLoop H x 1 := wi_outerLoop_closed H x
  rw [incr'_eq_loopIndex hne hcl, wi_loopIndex_outer H hx]
  ring

/-- The first half of the standard loop is the upper outer semicircle. -/
theorem wi_outerLoop_half1 {h : Work.Smooth.SphereJordan.PlaneHypothesis} {hs : γ.IsSimple}
    {hball : ∀ θ : ℝ, ‖γ.γ θ‖ < 1} {S : Work.Smooth.Jordan.PlaneSchoenflies γ}
    (H : SpanHyp h hs hball S) (x : ℂ) (t : unitInterval) :
    outerLoop H x (half1 t) = upP1 H x t := by
  have hreal : 2 * Real.pi * ((half1 t : unitInterval) : ℝ) = Real.pi * ((t : unitInterval) : ℝ) := by
    rw [half1_val]; ring
  show Work.Smooth.SphereJordan.cutDir S * Complex.exp
      ((((2 * Real.pi * ((half1 t : unitInterval) : ℝ) : ℝ)) : ℂ) * Complex.I) - x
    = Work.Smooth.SphereJordan.srcOuterUp S ((t : unitInterval) : ℝ) - x
  rw [hreal, Work.Smooth.SphereJordan.srcOuterUp]

/-- The second half of the standard loop is the lower outer semicircle. -/
theorem wi_outerLoop_half2 {h : Work.Smooth.SphereJordan.PlaneHypothesis} {hs : γ.IsSimple}
    {hball : ∀ θ : ℝ, ‖γ.γ θ‖ < 1} {S : Work.Smooth.Jordan.PlaneSchoenflies γ}
    (H : SpanHyp h hs hball S) (x : ℂ) (t : unitInterval) :
    outerLoop H x (half2 t) = dnP1 H x t := by
  have hreal : 2 * Real.pi * ((half2 t : unitInterval) : ℝ)
      = Real.pi * ((t : unitInterval) : ℝ) + Real.pi := by
    rw [half2_val]; ring
  have hsplit : ((((Real.pi * ((t : unitInterval) : ℝ) + Real.pi : ℝ)) : ℂ) * Complex.I)
      = (((Real.pi * ((t : unitInterval) : ℝ) : ℝ)) : ℂ) * Complex.I + (Real.pi : ℂ) * Complex.I := by
    push_cast; ring
  show Work.Smooth.SphereJordan.cutDir S * Complex.exp
      ((((2 * Real.pi * ((half2 t : unitInterval) : ℝ) : ℝ)) : ℂ) * Complex.I) - x
    = Work.Smooth.SphereJordan.srcOuterDn S ((t : unitInterval) : ℝ) - x
  rw [hreal, hsplit, Complex.exp_add, Complex.exp_pi_mul_I,
    Work.Smooth.SphereJordan.srcOuterDn]
  ring

/-- **The two outer semicircles account for the unit circle, hence for `kappa`.** -/
theorem wi_incr'_semi {h : Work.Smooth.SphereJordan.PlaneHypothesis} {hs : γ.IsSimple}
    {hball : ∀ θ : ℝ, ‖γ.γ θ‖ < 1} {S : Work.Smooth.Jordan.PlaneSchoenflies γ}
    (H : SpanHyp h hs hball S) {x : ℂ} (hx : x ∈ S.V) :
    incr' (upP1 H x) + incr' (dnP1 H x) = kappa := by
  have hne : ∀ t, outerLoop H x t ≠ 0 := wi_outerLoop_ne H hx
  have hs := wi_incr'_split (c := outerLoop H x) hne (σ := half1) (τ := half2)
    half1_zero half2_one (half1_one.trans half2_zero.symm)
  have h1 : incr' ((outerLoop H x).comp half1) = incr' (upP1 H x) :=
    incr'_congr (fun t => wi_outerLoop_half1 H x t)
  have h2 : incr' ((outerLoop H x).comp half2) = incr' (dnP1 H x) :=
    incr'_congr (fun t => wi_outerLoop_half2 H x t)
  exact (h1 ▸ h2 ▸ hs).trans (wi_incr'_outer H hx)

/-! ## The `γ`-arc pieces -/

theorem wi_incr'_upP3_true_eq_incOn {h : Work.Smooth.SphereJordan.PlaneHypothesis}
    {hs : γ.IsSimple} {hball : ∀ θ : ℝ, ‖γ.γ θ‖ < 1}
    {S : Work.Smooth.Jordan.PlaneSchoenflies γ}
    (H : SpanHyp h hs hball S) {x : ℂ} (hx : x ∈ S.V) :
    incr' (upP3 H x true) = incOn γ.γ γ.cont x H.θ₂ H.θ₁ := by
  rw [wi_incr'_eq_pathIncTot (upP3_ne H hx true)]
  exact pathIncTot_congr (fun t => rfl)

theorem wi_incr'_dnP3_true_eq_incOn {h : Work.Smooth.SphereJordan.PlaneHypothesis}
    {hs : γ.IsSimple} {hball : ∀ θ : ℝ, ‖γ.γ θ‖ < 1}
    {S : Work.Smooth.Jordan.PlaneSchoenflies γ}
    (H : SpanHyp h hs hball S) {x : ℂ} (hx : x ∈ S.V) :
    incr' (dnP3 H x true) = incOn γ.γ γ.cont x (H.θ₁ - 2 * Real.pi) H.θ₂ := by
  rw [wi_incr'_eq_pathIncTot (dnP3_ne H hx true)]
  refine pathIncTot_congr (fun t => ?_)
  show γ.γ (H.θ₁ - 2 * Real.pi + ((t : unitInterval) : ℝ) * (H.θ₂ - H.θ₁ + 2 * Real.pi)) - x
      = γ.γ (H.θ₁ - 2 * Real.pi +
          ((t : unitInterval) : ℝ) * (H.θ₂ - (H.θ₁ - 2 * Real.pi))) - x
  congr 1
  ring

/-- **The two `γ`-arc pieces of `(upPC true, dnPC true)` make up one full period of `γ`.** -/
theorem wi_incr'_gamma_TT {h : Work.Smooth.SphereJordan.PlaneHypothesis} {hs : γ.IsSimple}
    {hball : ∀ θ : ℝ, ‖γ.γ θ‖ < 1} {S : Work.Smooth.Jordan.PlaneSchoenflies γ}
    (H : SpanHyp h hs hball S) {x : ℂ} (hx : x ∈ S.V) :
    incr' (upP3 H x true) + incr' (dnP3 H x true)
      = (Work.Smooth.SphereJordan.windNumber γ.γ γ.cont x : ℂ) * kappa := by
  have hz : ∀ t : ℝ, γ.γ t ≠ x := fun t => gamma_ne S hx t
  have hav : ∀ t ∈ Set.Icc (H.θ₁ - 2 * Real.pi) H.θ₁, γ.γ t ≠ x := fun t _ => hz t
  have hθ : H.θ₁ - 2 * Real.pi ≤ H.θ₂ := by linarith [H.hθ, H.hθ']
  have hθ' : H.θ₂ ≤ H.θ₁ := le_of_lt H.hθ
  have hadd := incOn_add γ.cont hθ hθ' hav
  have hper := incOn_period γ.cont γ.periodic x hz (H.θ₁ - 2 * Real.pi)
  have hk : H.θ₁ - 2 * Real.pi + 2 * Real.pi = H.θ₁ := by ring
  rw [hk] at hper
  rw [wi_incr'_upP3_true_eq_incOn H hx, wi_incr'_dnP3_true_eq_incOn H hx, kappa, ← hper,
    hadd]
  ring

/-- The short `γ`-arcs of `(upPC true, dnPC false)` cancel. -/
theorem wi_incr'_gamma_TF {h : Work.Smooth.SphereJordan.PlaneHypothesis} {hs : γ.IsSimple}
    {hball : ∀ θ : ℝ, ‖γ.γ θ‖ < 1} {S : Work.Smooth.Jordan.PlaneSchoenflies γ}
    (H : SpanHyp h hs hball S) (x : ℂ) :
    incr' (upP3 H x true) + incr' (dnP3 H x false) = 0 := by
  have hcongr : ∀ t : unitInterval, dnP3 H x false t = (upP3 H x true).comp revI t := by
    intro t
    simp only [upP3, dnP3, ContinuousMap.comp_apply, ContinuousMap.coe_mk, revI_val,
      reduceIte, Bool.false_eq_true]
    congr 1
    ring
  rw [incr'_congr hcongr, incr'_rev]
  ring

/-- The complementary `γ`-arcs of `(upPC false, dnPC true)` cancel. -/
theorem wi_incr'_gamma_FT {h : Work.Smooth.SphereJordan.PlaneHypothesis} {hs : γ.IsSimple}
    {hball : ∀ θ : ℝ, ‖γ.γ θ‖ < 1} {S : Work.Smooth.Jordan.PlaneSchoenflies γ}
    (H : SpanHyp h hs hball S) (x : ℂ) :
    incr' (upP3 H x false) + incr' (dnP3 H x true) = 0 := by
  have hcongr : ∀ t : unitInterval, dnP3 H x true t = (upP3 H x false).comp revI t := by
    intro t
    simp only [upP3, dnP3, ContinuousMap.comp_apply, ContinuousMap.coe_mk, revI_val,
      reduceIte, Bool.false_eq_true]
    congr 1
    ring
  rw [incr'_congr hcongr, incr'_rev]
  ring


/-! ## The winding number as the sum of the four quarter increments -/

theorem wi_wind_up_eq {h : Work.Smooth.SphereJordan.PlaneHypothesis} {hs : γ.IsSimple}
    {hball : ∀ θ : ℝ, ‖γ.γ θ‖ < 1} {S : Work.Smooth.Jordan.PlaneSchoenflies γ}
    (H : SpanHyp h hs hball S) {x : ℂ} (hx : x ∈ S.V) (b : Bool) :
    (Work.Smooth.SphereJordan.windNumber (H.upPC b).γ (H.upPC b).cont x : ℂ) * kappa
      = incr' (upP1 H x) + incr' (upP2 H x) + incr' (upP3 H x b) + incr' (upP4 H x) := by
  have hc : ∀ t : unitInterval, upLoop H x b t ≠ 0 := upLoop_ne H hx b
  have hcl : upLoop H x b 0 = upLoop H x b 1 := wi_upLoop_closed H x b
  have h1 : incr' (upLoop H x b) =
      (Work.Smooth.SphereJordan.loopIndex (upLoop H x b) : ℂ) * kappa :=
    incr'_eq_loopIndex hc hcl
  rw [windNumber_upLoop, ← h1, wi_incr'_quarter hc]
  rw [incr'_congr (c := (upLoop H x b).comp q1) (d := upP1 H x)
        (fun t => wi_upLoop_q1 H x b t),
      incr'_congr (c := (upLoop H x b).comp q2) (d := upP2 H x)
        (fun t => wi_upLoop_q2 H x b t),
      incr'_congr (c := (upLoop H x b).comp q3) (d := upP3 H x b)
        (fun t => wi_upLoop_q3 H x b t),
      incr'_congr (c := (upLoop H x b).comp q4) (d := upP4 H x)
        (fun t => wi_upLoop_q4 H x b t)]

theorem wi_wind_dn_eq {h : Work.Smooth.SphereJordan.PlaneHypothesis} {hs : γ.IsSimple}
    {hball : ∀ θ : ℝ, ‖γ.γ θ‖ < 1} {S : Work.Smooth.Jordan.PlaneSchoenflies γ}
    (H : SpanHyp h hs hball S) {x : ℂ} (hx : x ∈ S.V) (b : Bool) :
    (Work.Smooth.SphereJordan.windNumber (H.dnPC b).γ (H.dnPC b).cont x : ℂ) * kappa
      = incr' (dnP1 H x) + incr' (dnP2 H x) + incr' (dnP3 H x b) + incr' (dnP4 H x) := by
  have hc : ∀ t : unitInterval, dnLoop H x b t ≠ 0 := dnLoop_ne H hx b
  have hcl : dnLoop H x b 0 = dnLoop H x b 1 := wi_dnLoop_closed H x b
  have h1 : incr' (dnLoop H x b) =
      (Work.Smooth.SphereJordan.loopIndex (dnLoop H x b) : ℂ) * kappa :=
    incr'_eq_loopIndex hc hcl
  rw [windNumber_dnLoop, ← h1, wi_incr'_quarter hc]
  rw [incr'_congr (c := (dnLoop H x b).comp q1) (d := dnP1 H x)
        (fun t => wi_dnLoop_q1 H x b t),
      incr'_congr (c := (dnLoop H x b).comp q2) (d := dnP2 H x)
        (fun t => wi_dnLoop_q2 H x b t),
      incr'_congr (c := (dnLoop H x b).comp q3) (d := dnP3 H x b)
        (fun t => wi_dnLoop_q3 H x b t),
      incr'_congr (c := (dnLoop H x b).comp q4) (d := dnP4 H x)
        (fun t => wi_dnLoop_q4 H x b t)]

/-! ## The three identities -/

theorem windIdentitiesProof {γ : Work.Smooth.Jordan.PlaneCurve}
    (h : Work.Smooth.SphereJordan.PlaneHypothesis) (hs : γ.IsSimple)
    (hball : ∀ θ : ℝ, ‖γ.γ θ‖ < 1) (S : Work.Smooth.Jordan.PlaneSchoenflies γ)
    (H : Work.SphereJordan.SpanHyp h hs hball S) :
    ∀ x : ℂ, x ∈ S.V →
      (Work.Smooth.SphereJordan.windNumber (H.upPC true).γ (H.upPC true).cont x
        + Work.Smooth.SphereJordan.windNumber (H.dnPC false).γ (H.dnPC false).cont x = 1) ∧
      (Work.Smooth.SphereJordan.windNumber (H.upPC false).γ (H.upPC false).cont x
        + Work.Smooth.SphereJordan.windNumber (H.dnPC true).γ (H.dnPC true).cont x = 1) ∧
      (Work.Smooth.SphereJordan.windNumber (H.upPC true).γ (H.upPC true).cont x
        + Work.Smooth.SphereJordan.windNumber (H.dnPC true).γ (H.dnPC true).cont x
        = 1 + Work.Smooth.SphereJordan.windNumber γ.γ γ.cont x) := by
  intro x hx
  have hupT := wi_wind_up_eq H hx true
  have hdnT := wi_wind_dn_eq H hx true
  have hupF := wi_wind_up_eq H hx false
  have hdnF := wi_wind_dn_eq H hx false
  have hsemi : incr' (upP1 H x) + incr' (dnP1 H x) = kappa := wi_incr'_semi H hx
  obtain ⟨hcut1, hcut2⟩ := wi_incr'_cut_pair H x
  have hcut2' : incr' (upP4 H x) + incr' (dnP2 H x) = 0 := by rw [add_comm]; exact hcut2
  have hgTF := wi_incr'_gamma_TF H x
  have hgFT := wi_incr'_gamma_FT H x
  have hgTT := wi_incr'_gamma_TT H hx
  set a : ℤ := Work.Smooth.SphereJordan.windNumber (H.upPC true).γ (H.upPC true).cont x
    with ha
  set b : ℤ := Work.Smooth.SphereJordan.windNumber (H.dnPC true).γ (H.dnPC true).cont x
    with hb
  set c : ℤ := Work.Smooth.SphereJordan.windNumber (H.upPC false).γ (H.upPC false).cont x
    with hc
  set d : ℤ := Work.Smooth.SphereJordan.windNumber (H.dnPC false).γ (H.dnPC false).cont x
    with hd
  set e : ℤ := Work.Smooth.SphereJordan.windNumber γ.γ γ.cont x with he
  refine ⟨?_, ?_, ?_⟩
  · have key : ((a : ℂ) + d) * kappa = kappa := by
      rw [add_mul, hupT, hdnF]
      linear_combination hsemi + hcut1 + hgTF + hcut2'
    have hkey : (a : ℂ) + d = 1 := by
      refine mul_right_cancel₀ kappa_ne_zero ?_
      rw [key, one_mul]
    have hcast : ((a + d : ℤ) : ℂ) = 1 := by
      push_cast
      exact hkey
    exact_mod_cast hcast
  · have key : ((c : ℂ) + b) * kappa = kappa := by
      rw [add_mul, hupF, hdnT]
      linear_combination hsemi + hcut1 + hgFT + hcut2'
    have hkey : (c : ℂ) + b = 1 := by
      refine mul_right_cancel₀ kappa_ne_zero ?_
      rw [key, one_mul]
    have hcast : ((c + b : ℤ) : ℂ) = 1 := by
      push_cast
      exact hkey
    have hres : c + b = 1 := by exact_mod_cast hcast
    linarith
  · have key : ((a : ℂ) + b) * kappa = (1 + (e : ℂ)) * kappa := by
      rw [add_mul, hupT, hdnT]
      linear_combination hsemi + hcut1 + hgTT + hcut2'
    have hkey : (a : ℂ) + b = 1 + (e : ℂ) := mul_right_cancel₀ kappa_ne_zero key
    have hcast : ((a + b : ℤ) : ℂ) = ((1 + e : ℤ) : ℂ) := by
      push_cast
      exact hkey
    exact_mod_cast hcast
end

end Work.SphereJordan
