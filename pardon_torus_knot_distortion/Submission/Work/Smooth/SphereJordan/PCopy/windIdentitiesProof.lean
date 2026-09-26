import Mathlib
import Submission.Work.Smooth.SphereJordan.PCopy.SpanHyp
import Submission.Work.SphereJordan.incrOn
import Submission.Work.SphereJordan.argIncrement
import Submission.Work.Smooth.SphereJordan.PCopy.pairingSetup
import Submission.Work.Smooth.SphereJordan.PCopy.tgtUpPC_isSimple
import Submission.Work.Smooth.SphereJordan.PCopy.windNumberCircleCurve
import Submission.Work.Smooth.SphereJordan.loopIndex_eq_of_homotopy

/-!
# The three winding-number identities of the two-pccuts pairing

This module proves `Work.SphereJordan.pcwindIdentitiesProof`: for the four four-arc curves
`H.pcupPC true`, `H.pcupPC false`, `H.pcdnPC true`, `H.pcdnPC false` of the two-pccuts configuration and every
point `x` of the bounded side `S.V` of `γ`,

`a + d = 1`, `b + c = 1`, `a + b = 1 + e`,

where `a, b, c, d` are the winding numbers of the four curves and `e` is the winding number of `γ`.

The proof is the "argument increment" bookkeeping: each of the four loops is the concatenation of
its four quarter arcs, its increment is the sum of the four quarter increments (the increment is
additive over concatenation), and the three identities are obtained by cancelling the arcs that the
two loops of a pair traverse in opposite directions.  What survives is either the unit circle
(contribution `pckappa = 2πI`, i.e. winding number `1`) or one full period of `γ` (contribution
`pckappa * windNumber γ.γ γ.cont x`).
-/

open Set
open Classical

namespace Work.SphereJordan

noncomputable section

variable {γ : Work.Smooth.Jordan.PlaneCurve}

/-! ## Elementary increment bookkeeping -/

/-- The one-period parameter of `2π` is `0`. -/
theorem pcwi_perPt_two_pi : Work.Smooth.SphereJordan.pcperPt (2 * Real.pi) = 0 := by
  rw [Work.Smooth.SphereJordan.pcperPt,
    div_self (by positivity : (2 : ℝ) * Real.pi ≠ 0)]
  norm_num

/-- `pcincr'` of a nowhere vanishing path is the total increment of its argument. -/
theorem pcwi_incr'_eq_pathIncTot {p : C(unitInterval, ℂ)} (hp : ∀ t, p t ≠ 0) :
    pcincr' p = pathIncTot p := by
  rw [pcincr'_eq hp, pathIncTot_eq_of_lift p hp (liftOf hp) (exp_liftOf hp)]
  rfl

/-- **Splitting the increment of a path into two consecutive pieces.** -/
theorem pcwi_incr'_split {c : C(unitInterval, ℂ)} (hc : ∀ t, c t ≠ 0)
    {σ τ : C(unitInterval, unitInterval)} (hσ0 : σ 0 = 0) (hτ1 : τ 1 = 1)
    (hj : σ 1 = τ 0) :
    pcincr' (c.comp σ) + pcincr' (c.comp τ) = pcincr' c := by
  have h1 : pcincr' (c.comp σ) = liftOf hc (σ 1) - liftOf hc (σ 0) := pcincr'_comp hc σ
  have h2 : pcincr' (c.comp τ) = liftOf hc (τ 1) - liftOf hc (τ 0) := pcincr'_comp hc τ
  have h3 : pcincr' c = liftOf hc 1 - liftOf hc 0 := by rw [pcincr'_eq hc]; rfl
  rw [h1, h2, h3, hσ0, hτ1, hj]
  ring

/-- **Splitting the increment of a path into its four quarters.** -/
theorem pcwi_incr'_quarter {c : C(unitInterval, ℂ)} (hc : ∀ t, c t ≠ 0) :
    pcincr' c = pcincr' (c.comp q1) + pcincr' (c.comp q2) + pcincr' (c.comp q3) + pcincr' (c.comp q4) := by
  rw [pcincr'_eq hc, incr_quarter hc]
  rw [pcincr'_eq (c := c.comp q1) (fun t => hc (q1 t)),
    pcincr'_eq (c := c.comp q2) (fun t => hc (q2 t)),
    pcincr'_eq (c := c.comp q3) (fun t => hc (q3 t)),
    pcincr'_eq (c := c.comp q4) (fun t => hc (q4 t))]

/-! ## The four branches of the unfolded target curves on their quarters -/

theorem pcwi_tgtUpBun_quarter1 {h : Work.Smooth.SphereJordan.PlaneHypothesis} {hs : γ.IsSimple}
    {hball : ∀ θ : ℝ, ‖γ.γ θ‖ < 1} {S : Work.Smooth.Jordan.PlaneSchoenflies γ}
    (H : pcSpanHyp h hs hball S) (b : Bool) {σ : ℝ}
    (hσ : σ ∈ Set.Icc (0 : ℝ) (Real.pi / 2)) :
    pctgtUpBun S H.t₁ H.s₁ H.t₂ H.s₂ b H.θ₁ H.θ₂ σ =
      Work.Smooth.SphereJordan.pcsrcOuterUp S (σ / (Real.pi / 2)) := by
  simp only [pctgtUpBun]
  rw [if_pos hσ.2]

theorem pcwi_tgtUpBun_quarter2 {h : Work.Smooth.SphereJordan.PlaneHypothesis} {hs : γ.IsSimple}
    {hball : ∀ θ : ℝ, ‖γ.γ θ‖ < 1} {S : Work.Smooth.Jordan.PlaneSchoenflies γ}
    (H : pcSpanHyp h hs hball S) (b : Bool) {σ : ℝ}
    (hσ : σ ∈ Set.Icc (Real.pi / 2) Real.pi) :
    pctgtUpBun S H.t₁ H.s₁ H.t₂ H.s₂ b H.θ₁ H.θ₂ σ =
      Work.Smooth.SphereJordan.pctgtCut₂ S H.t₂ H.s₂ ((σ - Real.pi / 2) / (Real.pi / 2)) := by
  by_cases hσa : σ ≤ Real.pi / 2
  · have hσeq : σ = Real.pi / 2 := le_antisymm hσa hσ.1
    subst hσeq
    have hL : Work.Smooth.SphereJordan.pcsrcOuterUp S (Real.pi / 2 / (Real.pi / 2)) =
        -Work.Smooth.SphereJordan.pccutDir S := by
      rw [div_self (by positivity : Real.pi / 2 ≠ 0), pcsrcOuterUp_one]
    have hR : Work.Smooth.SphereJordan.pctgtCut₂ S H.t₂ H.s₂
        ((Real.pi / 2 - Real.pi / 2) / (Real.pi / 2)) =
        -Work.Smooth.SphereJordan.pccutDir S := by
      rw [sub_self, zero_div, pctgtCut₂_zero, H.hout₂]
    simp only [pctgtUpBun]
    rw [if_pos le_rfl, hL, hR]
  · simp only [pctgtUpBun]
    rw [if_neg hσa, if_pos hσ.2]

theorem pcwi_tgtUpBun_quarter3 {h : Work.Smooth.SphereJordan.PlaneHypothesis} {hs : γ.IsSimple}
    {hball : ∀ θ : ℝ, ‖γ.γ θ‖ < 1} {S : Work.Smooth.Jordan.PlaneSchoenflies γ}
    (H : pcSpanHyp h hs hball S) (b : Bool) {σ : ℝ}
    (hσ : σ ∈ Set.Icc Real.pi (3 * Real.pi / 2)) :
    pctgtUpBun S H.t₁ H.s₁ H.t₂ H.s₂ b H.θ₁ H.θ₂ σ =
      (if b then γ.γ (H.θ₂ + ((σ - Real.pi) / (Real.pi / 2)) * (H.θ₁ - H.θ₂))
        else γ.γ (H.θ₂ + ((σ - Real.pi) / (Real.pi / 2)) * (H.θ₁ - H.θ₂ - 2 * Real.pi))) := by
  by_cases hσa : σ ≤ Real.pi / 2
  · have : Real.pi ≤ Real.pi / 2 := le_trans hσ.1 hσa
    linarith [Real.pi_pos]
  · by_cases hσb : σ ≤ Real.pi
    · have hσeq : σ = Real.pi := le_antisymm hσb hσ.1
      subst hσeq
      have hR : Work.Smooth.SphereJordan.pctgtCut₂ S H.t₂ H.s₂
          ((Real.pi - Real.pi / 2) / (Real.pi / 2)) =
          (Work.Smooth.SphereJordan.pcbase S : ℂ) -
            (H.t₂ : ℂ) * Work.Smooth.SphereJordan.pccutDir S := by
        rw [show (Real.pi - Real.pi / 2) / (Real.pi / 2) = 1 from by
          rw [div_eq_one_iff_eq (by positivity)]; ring, pctgtCut₂_one]
      have hb1 : H.θ₂ + ((Real.pi - Real.pi) / (Real.pi / 2)) * (H.θ₁ - H.θ₂) = H.θ₂ := by
        ring
      have hb2 : H.θ₂ + ((Real.pi - Real.pi) / (Real.pi / 2)) *
          (H.θ₁ - H.θ₂ - 2 * Real.pi) = H.θ₂ := by ring
      simp only [pctgtUpBun]
      rw [if_neg (by linarith [Real.pi_pos] : ¬ ((Real.pi : ℝ) ≤ Real.pi / 2)),
        if_pos le_rfl, hR]
      simp only [hb1, hb2]
      by_cases hb : b = true
      · rw [if_pos hb]; exact H.hθ₂.symm
      · rw [if_neg hb]; exact H.hθ₂.symm
    · simp only [pctgtUpBun]
      rw [if_neg hσa, if_neg hσb, if_pos hσ.2]

theorem pcwi_tgtUpBun_quarter4 {h : Work.Smooth.SphereJordan.PlaneHypothesis} {hs : γ.IsSimple}
    {hball : ∀ θ : ℝ, ‖γ.γ θ‖ < 1} {S : Work.Smooth.Jordan.PlaneSchoenflies γ}
    (H : pcSpanHyp h hs hball S) (b : Bool) {σ : ℝ}
    (hσ : σ ∈ Set.Icc (3 * Real.pi / 2) (2 * Real.pi)) :
    pctgtUpBun S H.t₁ H.s₁ H.t₂ H.s₂ b H.θ₁ H.θ₂ σ =
      Work.Smooth.SphereJordan.pctgtCut₁ S H.t₁ H.s₁
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
        have hDv : Work.Smooth.SphereJordan.pctgtCut₁ S H.t₁ H.s₁
            (1 - (3 * Real.pi / 2 - 3 * Real.pi / 2) / (Real.pi / 2)) = γ.γ H.θ₁ := by
          rw [sub_self, zero_div, sub_zero, pctgtCut₁_one, H.hθ₁]
        simp only [pctgtUpBun]
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
      · simp only [pctgtUpBun]
        rw [if_neg hσa, if_neg hσb, if_neg hσc]

theorem pcwi_tgtDnBun_quarter1 {h : Work.Smooth.SphereJordan.PlaneHypothesis} {hs : γ.IsSimple}
    {hball : ∀ θ : ℝ, ‖γ.γ θ‖ < 1} {S : Work.Smooth.Jordan.PlaneSchoenflies γ}
    (H : pcSpanHyp h hs hball S) (b : Bool) {σ : ℝ}
    (hσ : σ ∈ Set.Icc (0 : ℝ) (Real.pi / 2)) :
    pctgtDnBun S H.t₁ H.s₁ H.t₂ H.s₂ b H.θ₁ H.θ₂ σ =
      Work.Smooth.SphereJordan.pcsrcOuterDn S (σ / (Real.pi / 2)) := by
  simp only [pctgtDnBun]
  rw [if_pos hσ.2]

theorem pcwi_tgtDnBun_quarter2 {h : Work.Smooth.SphereJordan.PlaneHypothesis} {hs : γ.IsSimple}
    {hball : ∀ θ : ℝ, ‖γ.γ θ‖ < 1} {S : Work.Smooth.Jordan.PlaneSchoenflies γ}
    (H : pcSpanHyp h hs hball S) (b : Bool) {σ : ℝ}
    (hσ : σ ∈ Set.Icc (Real.pi / 2) Real.pi) :
    pctgtDnBun S H.t₁ H.s₁ H.t₂ H.s₂ b H.θ₁ H.θ₂ σ =
      Work.Smooth.SphereJordan.pctgtCut₁ S H.t₁ H.s₁ ((σ - Real.pi / 2) / (Real.pi / 2)) := by
  by_cases hσa : σ ≤ Real.pi / 2
  · have hσeq : σ = Real.pi / 2 := le_antisymm hσa hσ.1
    subst hσeq
    have hL : Work.Smooth.SphereJordan.pcsrcOuterDn S (Real.pi / 2 / (Real.pi / 2)) =
        Work.Smooth.SphereJordan.pccutDir S := by
      rw [div_self (by positivity : Real.pi / 2 ≠ 0), pcsrcOuterDn_one]
    have hR : Work.Smooth.SphereJordan.pctgtCut₁ S H.t₁ H.s₁
        ((Real.pi / 2 - Real.pi / 2) / (Real.pi / 2)) =
        Work.Smooth.SphereJordan.pccutDir S := by
      rw [sub_self, zero_div, pctgtCut₁_zero, H.hout₁]
    simp only [pctgtDnBun]
    rw [if_pos le_rfl, hL, hR]
  · simp only [pctgtDnBun]
    rw [if_neg hσa, if_pos hσ.2]

theorem pcwi_tgtDnBun_quarter3 {h : Work.Smooth.SphereJordan.PlaneHypothesis} {hs : γ.IsSimple}
    {hball : ∀ θ : ℝ, ‖γ.γ θ‖ < 1} {S : Work.Smooth.Jordan.PlaneSchoenflies γ}
    (H : pcSpanHyp h hs hball S) (b : Bool) {σ : ℝ}
    (hσ : σ ∈ Set.Icc Real.pi (3 * Real.pi / 2)) :
    pctgtDnBun S H.t₁ H.s₁ H.t₂ H.s₂ b H.θ₁ H.θ₂ σ =
      (if b then γ.γ (H.θ₁ - 2 * Real.pi +
          ((σ - Real.pi) / (Real.pi / 2)) * (H.θ₂ - H.θ₁ + 2 * Real.pi))
        else γ.γ (H.θ₁ + ((σ - Real.pi) / (Real.pi / 2)) * (H.θ₂ - H.θ₁))) := by
  by_cases hσa : σ ≤ Real.pi / 2
  · have : Real.pi ≤ Real.pi / 2 := le_trans hσ.1 hσa
    linarith [Real.pi_pos]
  · by_cases hσb : σ ≤ Real.pi
    · have hσeq : σ = Real.pi := le_antisymm hσb hσ.1
      subst hσeq
      have hR : Work.Smooth.SphereJordan.pctgtCut₁ S H.t₁ H.s₁
          ((Real.pi - Real.pi / 2) / (Real.pi / 2)) =
          (Work.Smooth.SphereJordan.pcbase S : ℂ) +
            (H.t₁ : ℂ) * Work.Smooth.SphereJordan.pccutDir S := by
        rw [show (Real.pi - Real.pi / 2) / (Real.pi / 2) = 1 from by
          rw [div_eq_one_iff_eq (by positivity)]; ring, pctgtCut₁_one]
      have hb1 : H.θ₁ - 2 * Real.pi + ((Real.pi - Real.pi) / (Real.pi / 2)) *
          (H.θ₂ - H.θ₁ + 2 * Real.pi) = H.θ₁ - 2 * Real.pi := by ring
      have hb2 : H.θ₁ + ((Real.pi - Real.pi) / (Real.pi / 2)) * (H.θ₂ - H.θ₁) = H.θ₁ := by
        ring
      have hun1 : γ.γ (H.θ₁ - 2 * Real.pi) = γ.γ H.θ₁ := by
        have hper := γ.apply_add_int_mul (H.θ₁ - 2 * Real.pi) 1
        rw [show H.θ₁ - 2 * Real.pi + (1 : ℤ) * (2 * Real.pi) = H.θ₁ from by
          push_cast; ring] at hper
        exact hper.symm
      simp only [pctgtDnBun]
      rw [if_neg (by linarith [Real.pi_pos] : ¬ ((Real.pi : ℝ) ≤ Real.pi / 2)),
        if_pos le_rfl, hR]
      by_cases hb : b = true
      · rw [if_pos hb, hb1, hun1]; exact H.hθ₁.symm
      · rw [if_neg hb, hb2]; exact H.hθ₁.symm
    · simp only [pctgtDnBun]
      rw [if_neg hσa, if_neg hσb, if_pos hσ.2]

theorem pcwi_tgtDnBun_quarter4 {h : Work.Smooth.SphereJordan.PlaneHypothesis} {hs : γ.IsSimple}
    {hball : ∀ θ : ℝ, ‖γ.γ θ‖ < 1} {S : Work.Smooth.Jordan.PlaneSchoenflies γ}
    (H : pcSpanHyp h hs hball S) (b : Bool) {σ : ℝ}
    (hσ : σ ∈ Set.Icc (3 * Real.pi / 2) (2 * Real.pi)) :
    pctgtDnBun S H.t₁ H.s₁ H.t₂ H.s₂ b H.θ₁ H.θ₂ σ =
      Work.Smooth.SphereJordan.pctgtCut₂ S H.t₂ H.s₂
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
        have hDv : Work.Smooth.SphereJordan.pctgtCut₂ S H.t₂ H.s₂
            (1 - (3 * Real.pi / 2 - 3 * Real.pi / 2) / (Real.pi / 2)) =
            (Work.Smooth.SphereJordan.pcbase S : ℂ) -
              (H.t₂ : ℂ) * Work.Smooth.SphereJordan.pccutDir S := by
          rw [sub_self, zero_div, sub_zero, pctgtCut₂_one]
        simp only [pctgtDnBun]
        rw [if_neg (by linarith [Real.pi_pos] : ¬ ((3 * Real.pi / 2 : ℝ) ≤ Real.pi / 2)),
          if_neg (by linarith [Real.pi_pos] : ¬ ((3 * Real.pi / 2 : ℝ) ≤ Real.pi)),
          if_pos le_rfl, hDv, hratio]
        by_cases hb : b = true
        · rw [if_pos hb,
            show H.θ₁ - 2 * Real.pi + 1 * (H.θ₂ - H.θ₁ + 2 * Real.pi) = H.θ₂ from by ring,
            H.hθ₂]
        · rw [if_neg hb, show H.θ₁ + 1 * (H.θ₂ - H.θ₁) = H.θ₂ from by ring, H.hθ₂]
      · simp only [pctgtDnBun]
        rw [if_neg hσa, if_neg hσb, if_neg hσc]


/-! ## The four quarter pieces of the two loops -/

theorem pcwi_upLoop_q1 {h : Work.Smooth.SphereJordan.PlaneHypothesis} {hs : γ.IsSimple}
    {hball : ∀ θ : ℝ, ‖γ.γ θ‖ < 1} {S : Work.Smooth.Jordan.PlaneSchoenflies γ}
    (H : pcSpanHyp h hs hball S) (x : ℂ) (b : Bool) :
    ∀ t : unitInterval, pcupLoop H x b (q1 t) = pcupP1 H x t := by
  intro t
  have hσ1 : 2 * Real.pi * ((q1 t : unitInterval) : ℝ) ∈ Set.Icc (0 : ℝ) (Real.pi / 2) := by
    rw [pctwo_pi_q1]
    constructor <;> nlinarith [t.2.1, t.2.2, Real.pi_pos]
  have hlt : 2 * Real.pi * ((q1 t : unitInterval) : ℝ) ∈ Set.Ico (0 : ℝ) (2 * Real.pi) :=
    ⟨hσ1.1, by linarith [hσ1.2, Real.pi_pos]⟩
  have harg : (2 * Real.pi * ((q1 t : unitInterval) : ℝ)) / (Real.pi / 2) = (t : ℝ) := by
    rw [pctwo_pi_q1]; field_simp
  show Work.Smooth.SphereJordan.pctgtUpB S H.t₁ H.s₁ H.t₂ H.s₂ b H.θ₁ H.θ₂
      (2 * Real.pi * ((q1 t : unitInterval) : ℝ)) - x
    = Work.Smooth.SphereJordan.pcsrcOuterUp S ((t : unitInterval) : ℝ) - x
  rw [pctgtUpB_eq, pcperPt_self hlt, pcwi_tgtUpBun_quarter1 H b hσ1, harg]

theorem pcwi_upLoop_q2 {h : Work.Smooth.SphereJordan.PlaneHypothesis} {hs : γ.IsSimple}
    {hball : ∀ θ : ℝ, ‖γ.γ θ‖ < 1} {S : Work.Smooth.Jordan.PlaneSchoenflies γ}
    (H : pcSpanHyp h hs hball S) (x : ℂ) (b : Bool) :
    ∀ t : unitInterval, pcupLoop H x b (q2 t) = pcupP2 H x t := by
  intro t
  have hσ1 : 2 * Real.pi * ((q2 t : unitInterval) : ℝ) ∈ Set.Icc (Real.pi / 2) Real.pi := by
    rw [pctwo_pi_q2]
    constructor <;> nlinarith [t.2.1, t.2.2, Real.pi_pos]
  have hlt : 2 * Real.pi * ((q2 t : unitInterval) : ℝ) ∈ Set.Ico (0 : ℝ) (2 * Real.pi) :=
    ⟨by linarith [hσ1.1, Real.pi_pos], by linarith [hσ1.2, Real.pi_pos]⟩
  have harg : (2 * Real.pi * ((q2 t : unitInterval) : ℝ) - Real.pi / 2) / (Real.pi / 2)
      = (t : ℝ) := by
    rw [pctwo_pi_q2]; field_simp; ring
  show Work.Smooth.SphereJordan.pctgtUpB S H.t₁ H.s₁ H.t₂ H.s₂ b H.θ₁ H.θ₂
      (2 * Real.pi * ((q2 t : unitInterval) : ℝ)) - x
    = Work.Smooth.SphereJordan.pctgtCut₂ S H.t₂ H.s₂ ((t : unitInterval) : ℝ) - x
  rw [pctgtUpB_eq, pcperPt_self hlt, pcwi_tgtUpBun_quarter2 H b hσ1, harg]

theorem pcwi_upLoop_q3 {h : Work.Smooth.SphereJordan.PlaneHypothesis} {hs : γ.IsSimple}
    {hball : ∀ θ : ℝ, ‖γ.γ θ‖ < 1} {S : Work.Smooth.Jordan.PlaneSchoenflies γ}
    (H : pcSpanHyp h hs hball S) (x : ℂ) (b : Bool) :
    ∀ t : unitInterval, pcupLoop H x b (q3 t) = pcupP3 H x b t := by
  intro t
  have hσ1 : 2 * Real.pi * ((q3 t : unitInterval) : ℝ) ∈ Set.Icc Real.pi (3 * Real.pi / 2) := by
    rw [pctwo_pi_q3]
    constructor <;> nlinarith [t.2.1, t.2.2, Real.pi_pos]
  have hlt : 2 * Real.pi * ((q3 t : unitInterval) : ℝ) ∈ Set.Ico (0 : ℝ) (2 * Real.pi) :=
    ⟨by linarith [hσ1.1, Real.pi_pos], by linarith [hσ1.2, Real.pi_pos]⟩
  have harg : (2 * Real.pi * ((q3 t : unitInterval) : ℝ) - Real.pi) / (Real.pi / 2)
      = (t : ℝ) := by
    rw [pctwo_pi_q3]; field_simp; ring
  show Work.Smooth.SphereJordan.pctgtUpB S H.t₁ H.s₁ H.t₂ H.s₂ b H.θ₁ H.θ₂
      (2 * Real.pi * ((q3 t : unitInterval) : ℝ)) - x
    = (if b then γ.γ (H.θ₂ + ((t : unitInterval) : ℝ) * (H.θ₁ - H.θ₂))
        else γ.γ (H.θ₂ + ((t : unitInterval) : ℝ) * (H.θ₁ - H.θ₂ - 2 * Real.pi))) - x
  rw [pctgtUpB_eq, pcperPt_self hlt, pcwi_tgtUpBun_quarter3 H b hσ1, harg]

theorem pcwi_upLoop_q4 {h : Work.Smooth.SphereJordan.PlaneHypothesis} {hs : γ.IsSimple}
    {hball : ∀ θ : ℝ, ‖γ.γ θ‖ < 1} {S : Work.Smooth.Jordan.PlaneSchoenflies γ}
    (H : pcSpanHyp h hs hball S) (x : ℂ) (b : Bool) :
    ∀ t : unitInterval, pcupLoop H x b (q4 t) = pcupP4 H x t := by
  intro t
  rcases lt_or_eq_of_le t.2.2 with ht | ht
  · have hσ1 : 2 * Real.pi * ((q4 t : unitInterval) : ℝ) ∈
        Set.Icc (3 * Real.pi / 2) (2 * Real.pi) := by
      rw [pcq4_val]
      constructor <;> nlinarith [t.2.1, ht, Real.pi_pos]
    have hlt2 : 2 * Real.pi * ((q4 t : unitInterval) : ℝ) < 2 * Real.pi := by
      rw [pcq4_val]; nlinarith [ht, Real.pi_pos]
    have hlt : 2 * Real.pi * ((q4 t : unitInterval) : ℝ) ∈ Set.Ico (0 : ℝ) (2 * Real.pi) :=
      ⟨by linarith [hσ1.1, Real.pi_pos], hlt2⟩
    have harg : 1 - (2 * Real.pi * ((q4 t : unitInterval) : ℝ) - 3 * Real.pi / 2) /
        (Real.pi / 2) = 1 - (t : ℝ) := by
      rw [pcq4_val]; field_simp; ring
    show Work.Smooth.SphereJordan.pctgtUpB S H.t₁ H.s₁ H.t₂ H.s₂ b H.θ₁ H.θ₂
        (2 * Real.pi * ((q4 t : unitInterval) : ℝ)) - x
      = Work.Smooth.SphereJordan.pctgtCut₁ S H.t₁ H.s₁
        (1 - ((t : unitInterval) : ℝ)) - x
    rw [pctgtUpB_eq, pcperPt_self hlt, pcwi_tgtUpBun_quarter4 H b hσ1, harg]
  · have hq4 : ((q4 t : unitInterval) : ℝ) = 1 := by rw [pcq4_val, ht]; norm_num
    have h2pi : 2 * Real.pi * ((q4 t : unitInterval) : ℝ) = 2 * Real.pi := by
      rw [hq4]; ring
    have hone : ((t : unitInterval) : ℝ) = 1 := ht
    show Work.Smooth.SphereJordan.pctgtUpB S H.t₁ H.s₁ H.t₂ H.s₂ b H.θ₁ H.θ₂
        (2 * Real.pi * ((q4 t : unitInterval) : ℝ)) - x
      = Work.Smooth.SphereJordan.pctgtCut₁ S H.t₁ H.s₁
        (1 - ((t : unitInterval) : ℝ)) - x
    rw [h2pi, pctgtUpB_eq, pcwi_perPt_two_pi, hone, sub_self,
      pcwi_tgtUpBun_quarter1 H b (⟨le_rfl, by positivity⟩ : (0 : ℝ) ∈ Set.Icc (0 : ℝ) (Real.pi / 2)),
      zero_div, pcsrcOuterUp_zero, pctgtCut₁_zero, H.hout₁]

theorem pcwi_dnLoop_q1 {h : Work.Smooth.SphereJordan.PlaneHypothesis} {hs : γ.IsSimple}
    {hball : ∀ θ : ℝ, ‖γ.γ θ‖ < 1} {S : Work.Smooth.Jordan.PlaneSchoenflies γ}
    (H : pcSpanHyp h hs hball S) (x : ℂ) (b : Bool) :
    ∀ t : unitInterval, pcdnLoop H x b (q1 t) = pcdnP1 H x t := by
  intro t
  have hσ1 : 2 * Real.pi * ((q1 t : unitInterval) : ℝ) ∈ Set.Icc (0 : ℝ) (Real.pi / 2) := by
    rw [pctwo_pi_q1]
    constructor <;> nlinarith [t.2.1, t.2.2, Real.pi_pos]
  have hlt : 2 * Real.pi * ((q1 t : unitInterval) : ℝ) ∈ Set.Ico (0 : ℝ) (2 * Real.pi) :=
    ⟨hσ1.1, by linarith [hσ1.2, Real.pi_pos]⟩
  have harg : (2 * Real.pi * ((q1 t : unitInterval) : ℝ)) / (Real.pi / 2) = (t : ℝ) := by
    rw [pctwo_pi_q1]; field_simp
  show Work.Smooth.SphereJordan.pctgtDnB S H.t₁ H.s₁ H.t₂ H.s₂ b H.θ₁ H.θ₂
      (2 * Real.pi * ((q1 t : unitInterval) : ℝ)) - x
    = Work.Smooth.SphereJordan.pcsrcOuterDn S ((t : unitInterval) : ℝ) - x
  rw [pctgtDnB_eq, pcperPt_self hlt, pcwi_tgtDnBun_quarter1 H b hσ1, harg]

theorem pcwi_dnLoop_q2 {h : Work.Smooth.SphereJordan.PlaneHypothesis} {hs : γ.IsSimple}
    {hball : ∀ θ : ℝ, ‖γ.γ θ‖ < 1} {S : Work.Smooth.Jordan.PlaneSchoenflies γ}
    (H : pcSpanHyp h hs hball S) (x : ℂ) (b : Bool) :
    ∀ t : unitInterval, pcdnLoop H x b (q2 t) = pcdnP2 H x t := by
  intro t
  have hσ1 : 2 * Real.pi * ((q2 t : unitInterval) : ℝ) ∈ Set.Icc (Real.pi / 2) Real.pi := by
    rw [pctwo_pi_q2]
    constructor <;> nlinarith [t.2.1, t.2.2, Real.pi_pos]
  have hlt : 2 * Real.pi * ((q2 t : unitInterval) : ℝ) ∈ Set.Ico (0 : ℝ) (2 * Real.pi) :=
    ⟨by linarith [hσ1.1, Real.pi_pos], by linarith [hσ1.2, Real.pi_pos]⟩
  have harg : (2 * Real.pi * ((q2 t : unitInterval) : ℝ) - Real.pi / 2) / (Real.pi / 2)
      = (t : ℝ) := by
    rw [pctwo_pi_q2]; field_simp; ring
  show Work.Smooth.SphereJordan.pctgtDnB S H.t₁ H.s₁ H.t₂ H.s₂ b H.θ₁ H.θ₂
      (2 * Real.pi * ((q2 t : unitInterval) : ℝ)) - x
    = Work.Smooth.SphereJordan.pctgtCut₁ S H.t₁ H.s₁ ((t : unitInterval) : ℝ) - x
  rw [pctgtDnB_eq, pcperPt_self hlt, pcwi_tgtDnBun_quarter2 H b hσ1, harg]

theorem pcwi_dnLoop_q3 {h : Work.Smooth.SphereJordan.PlaneHypothesis} {hs : γ.IsSimple}
    {hball : ∀ θ : ℝ, ‖γ.γ θ‖ < 1} {S : Work.Smooth.Jordan.PlaneSchoenflies γ}
    (H : pcSpanHyp h hs hball S) (x : ℂ) (b : Bool) :
    ∀ t : unitInterval, pcdnLoop H x b (q3 t) = pcdnP3 H x b t := by
  intro t
  have hσ1 : 2 * Real.pi * ((q3 t : unitInterval) : ℝ) ∈ Set.Icc Real.pi (3 * Real.pi / 2) := by
    rw [pctwo_pi_q3]
    constructor <;> nlinarith [t.2.1, t.2.2, Real.pi_pos]
  have hlt : 2 * Real.pi * ((q3 t : unitInterval) : ℝ) ∈ Set.Ico (0 : ℝ) (2 * Real.pi) :=
    ⟨by linarith [hσ1.1, Real.pi_pos], by linarith [hσ1.2, Real.pi_pos]⟩
  have harg : (2 * Real.pi * ((q3 t : unitInterval) : ℝ) - Real.pi) / (Real.pi / 2)
      = (t : ℝ) := by
    rw [pctwo_pi_q3]; field_simp; ring
  show Work.Smooth.SphereJordan.pctgtDnB S H.t₁ H.s₁ H.t₂ H.s₂ b H.θ₁ H.θ₂
      (2 * Real.pi * ((q3 t : unitInterval) : ℝ)) - x
    = (if b then γ.γ (H.θ₁ - 2 * Real.pi + ((t : unitInterval) : ℝ) *
          (H.θ₂ - H.θ₁ + 2 * Real.pi))
        else γ.γ (H.θ₁ + ((t : unitInterval) : ℝ) * (H.θ₂ - H.θ₁))) - x
  rw [pctgtDnB_eq, pcperPt_self hlt, pcwi_tgtDnBun_quarter3 H b hσ1, harg]

theorem pcwi_dnLoop_q4 {h : Work.Smooth.SphereJordan.PlaneHypothesis} {hs : γ.IsSimple}
    {hball : ∀ θ : ℝ, ‖γ.γ θ‖ < 1} {S : Work.Smooth.Jordan.PlaneSchoenflies γ}
    (H : pcSpanHyp h hs hball S) (x : ℂ) (b : Bool) :
    ∀ t : unitInterval, pcdnLoop H x b (q4 t) = pcdnP4 H x t := by
  intro t
  rcases lt_or_eq_of_le t.2.2 with ht | ht
  · have hσ1 : 2 * Real.pi * ((q4 t : unitInterval) : ℝ) ∈
        Set.Icc (3 * Real.pi / 2) (2 * Real.pi) := by
      rw [pcq4_val]
      constructor <;> nlinarith [t.2.1, ht, Real.pi_pos]
    have hlt2 : 2 * Real.pi * ((q4 t : unitInterval) : ℝ) < 2 * Real.pi := by
      rw [pcq4_val]; nlinarith [ht, Real.pi_pos]
    have hlt : 2 * Real.pi * ((q4 t : unitInterval) : ℝ) ∈ Set.Ico (0 : ℝ) (2 * Real.pi) :=
      ⟨by linarith [hσ1.1, Real.pi_pos], hlt2⟩
    have harg : 1 - (2 * Real.pi * ((q4 t : unitInterval) : ℝ) - 3 * Real.pi / 2) /
        (Real.pi / 2) = 1 - (t : ℝ) := by
      rw [pcq4_val]; field_simp; ring
    show Work.Smooth.SphereJordan.pctgtDnB S H.t₁ H.s₁ H.t₂ H.s₂ b H.θ₁ H.θ₂
        (2 * Real.pi * ((q4 t : unitInterval) : ℝ)) - x
      = Work.Smooth.SphereJordan.pctgtCut₂ S H.t₂ H.s₂
        (1 - ((t : unitInterval) : ℝ)) - x
    rw [pctgtDnB_eq, pcperPt_self hlt, pcwi_tgtDnBun_quarter4 H b hσ1, harg]
  · have hq4 : ((q4 t : unitInterval) : ℝ) = 1 := by rw [pcq4_val, ht]; norm_num
    have h2pi : 2 * Real.pi * ((q4 t : unitInterval) : ℝ) = 2 * Real.pi := by
      rw [hq4]; ring
    have hone : ((t : unitInterval) : ℝ) = 1 := ht
    show Work.Smooth.SphereJordan.pctgtDnB S H.t₁ H.s₁ H.t₂ H.s₂ b H.θ₁ H.θ₂
        (2 * Real.pi * ((q4 t : unitInterval) : ℝ)) - x
      = Work.Smooth.SphereJordan.pctgtCut₂ S H.t₂ H.s₂
        (1 - ((t : unitInterval) : ℝ)) - x
    rw [h2pi, pctgtDnB_eq, pcwi_perPt_two_pi, hone, sub_self,
      pcwi_tgtDnBun_quarter1 H b (⟨le_rfl, by positivity⟩ : (0 : ℝ) ∈ Set.Icc (0 : ℝ) (Real.pi / 2)),
      zero_div, pcsrcOuterDn_zero, pctgtCut₂_zero, H.hout₂]

/-! ## The four loops are closed, and the crosscut pieces cancel in pairs -/

theorem pcwi_upLoop_closed {h : Work.Smooth.SphereJordan.PlaneHypothesis} {hs : γ.IsSimple}
    {hball : ∀ θ : ℝ, ‖γ.γ θ‖ < 1} {S : Work.Smooth.Jordan.PlaneSchoenflies γ}
    (H : pcSpanHyp h hs hball S) (x : ℂ) (b : Bool) : pcupLoop H x b 0 = pcupLoop H x b 1 := by
  have h0 : 2 * Real.pi * ((0 : unitInterval) : ℝ) = 0 := by simp
  have h2 : 2 * Real.pi * ((1 : unitInterval) : ℝ) = 2 * Real.pi := by simp
  have hper : Work.Smooth.SphereJordan.pctgtUpB S H.t₁ H.s₁ H.t₂ H.s₂ b H.θ₁ H.θ₂ 0 =
      Work.Smooth.SphereJordan.pctgtUpB S H.t₁ H.s₁ H.t₂ H.s₂ b H.θ₁ H.θ₂ (2 * Real.pi) := by
    simpa using ((H.pcupPC b).periodic_apply 0).symm
  show Work.Smooth.SphereJordan.pctgtUpB S H.t₁ H.s₁ H.t₂ H.s₂ b H.θ₁ H.θ₂
      (2 * Real.pi * ((0 : unitInterval) : ℝ)) - x
    = Work.Smooth.SphereJordan.pctgtUpB S H.t₁ H.s₁ H.t₂ H.s₂ b H.θ₁ H.θ₂
      (2 * Real.pi * ((1 : unitInterval) : ℝ)) - x
  rw [h0, h2, hper]

theorem pcwi_dnLoop_closed {h : Work.Smooth.SphereJordan.PlaneHypothesis} {hs : γ.IsSimple}
    {hball : ∀ θ : ℝ, ‖γ.γ θ‖ < 1} {S : Work.Smooth.Jordan.PlaneSchoenflies γ}
    (H : pcSpanHyp h hs hball S) (x : ℂ) (b : Bool) : pcdnLoop H x b 0 = pcdnLoop H x b 1 := by
  have h0 : 2 * Real.pi * ((0 : unitInterval) : ℝ) = 0 := by simp
  have h2 : 2 * Real.pi * ((1 : unitInterval) : ℝ) = 2 * Real.pi := by simp
  have hper : Work.Smooth.SphereJordan.pctgtDnB S H.t₁ H.s₁ H.t₂ H.s₂ b H.θ₁ H.θ₂ 0 =
      Work.Smooth.SphereJordan.pctgtDnB S H.t₁ H.s₁ H.t₂ H.s₂ b H.θ₁ H.θ₂ (2 * Real.pi) := by
    simpa using ((H.pcdnPC b).periodic_apply 0).symm
  show Work.Smooth.SphereJordan.pctgtDnB S H.t₁ H.s₁ H.t₂ H.s₂ b H.θ₁ H.θ₂
      (2 * Real.pi * ((0 : unitInterval) : ℝ)) - x
    = Work.Smooth.SphereJordan.pctgtDnB S H.t₁ H.s₁ H.t₂ H.s₂ b H.θ₁ H.θ₂
      (2 * Real.pi * ((1 : unitInterval) : ℝ)) - x
  rw [h0, h2, hper]

theorem pcwi_incr'_cut_pair {h : Work.Smooth.SphereJordan.PlaneHypothesis} {hs : γ.IsSimple}
    {hball : ∀ θ : ℝ, ‖γ.γ θ‖ < 1} {S : Work.Smooth.Jordan.PlaneSchoenflies γ}
    (H : pcSpanHyp h hs hball S) (x : ℂ) :
    (pcincr' (pcupP2 H x) + pcincr' (pcdnP4 H x) = 0) ∧
      (pcincr' (pcdnP2 H x) + pcincr' (pcupP4 H x) = 0) := by
  constructor
  · have hcongr : ∀ t : unitInterval, pcdnP4 H x t = (pcupP2 H x).comp revI t := by
      intro t
      simp only [ContinuousMap.comp_apply]
      show Work.Smooth.SphereJordan.pctgtCut₂ S H.t₂ H.s₂ (1 - (t : ℝ)) - x =
        Work.Smooth.SphereJordan.pctgtCut₂ S H.t₂ H.s₂ ((revI t : unitInterval) : ℝ) - x
      rw [pcrevI_val]
    rw [pcincr'_congr hcongr, pcincr'_rev]
    ring
  · have hcongr : ∀ t : unitInterval, pcupP4 H x t = (pcdnP2 H x).comp revI t := by
      intro t
      simp only [ContinuousMap.comp_apply]
      show Work.Smooth.SphereJordan.pctgtCut₁ S H.t₁ H.s₁ (1 - (t : ℝ)) - x =
        Work.Smooth.SphereJordan.pctgtCut₁ S H.t₁ H.s₁ ((revI t : unitInterval) : ℝ) - x
      rw [pcrevI_val]
    rw [pcincr'_congr hcongr, pcincr'_rev]
    ring


/-! ## The two outer semicircles and the unit circle -/

/-- The unit circle, traversed once from `pccutDir S`. -/
def pcwiStdLoop (S : Work.Smooth.Jordan.PlaneSchoenflies γ) : C(unitInterval, ℂ) :=
  ⟨fun t => Work.Smooth.SphereJordan.pccutDir S *
      Complex.exp ((((2 * Real.pi * ((t : unitInterval) : ℝ) : ℝ)) : ℂ) * Complex.I),
    by fun_prop⟩

theorem pcwi_std_norm (S : Work.Smooth.Jordan.PlaneSchoenflies γ) (t : unitInterval) :
    ‖pcwiStdLoop S t‖ = 1 := by
  show ‖Work.Smooth.SphereJordan.pccutDir S * Complex.exp
      ((((2 * Real.pi * ((t : unitInterval) : ℝ) : ℝ)) : ℂ) * Complex.I)‖ = 1
  rw [norm_mul, Work.Smooth.SphereJordan.pcnorm_cutDir, one_mul,
    Complex.norm_exp_ofReal_mul_I]

theorem pcwi_std_closed (S : Work.Smooth.Jordan.PlaneSchoenflies γ) :
    pcwiStdLoop S 0 = pcwiStdLoop S 1 := by
  have h0c : ((((2 * Real.pi * ((0 : unitInterval) : ℝ) : ℝ)) : ℂ) * Complex.I) = 0 := by
    rw [show 2 * Real.pi * ((0 : unitInterval) : ℝ) = 0 from by simp]
    simp
  have h1c : ((((2 * Real.pi * ((1 : unitInterval) : ℝ) : ℝ)) : ℂ) * Complex.I)
      = 2 * (Real.pi : ℂ) * Complex.I := by
    rw [show 2 * Real.pi * ((1 : unitInterval) : ℝ) = 2 * Real.pi from by simp]
    push_cast
    ring
  show Work.Smooth.SphereJordan.pccutDir S * Complex.exp
      ((((2 * Real.pi * ((0 : unitInterval) : ℝ) : ℝ)) : ℂ) * Complex.I)
    = Work.Smooth.SphereJordan.pccutDir S * Complex.exp
      ((((2 * Real.pi * ((1 : unitInterval) : ℝ) : ℝ)) : ℂ) * Complex.I)
  rw [h0c, h1c, Complex.exp_zero, Complex.exp_two_pi_mul_I]

theorem pcwi_loopIndex_std (S : Work.Smooth.Jordan.PlaneSchoenflies γ) :
    Work.Smooth.SphereJordan.loopIndex (pcwiStdLoop S) = 1 := by
  have hne : ∀ t : unitInterval, pcwiStdLoop S t ≠ 0 := by
    intro t h
    have h1 : ‖pcwiStdLoop S t‖ = 1 := pcwi_std_norm S t
    rw [h, norm_zero] at h1
    exact one_ne_zero h1.symm
  have hcl : pcwiStdLoop S 0 = pcwiStdLoop S 1 := pcwi_std_closed S
  set Λ : C(unitInterval, ℂ) :=
    ⟨fun t => Complex.log (Work.Smooth.SphereJordan.pccutDir S) +
      ((((2 * Real.pi * ((t : unitInterval) : ℝ) : ℝ)) : ℂ) * Complex.I), by fun_prop⟩ with hΛ
  have hlift : ∀ t : unitInterval, Complex.exp (Λ t) = pcwiStdLoop S t := by
    intro t
    show Complex.exp (Complex.log (Work.Smooth.SphereJordan.pccutDir S) +
      ((((2 * Real.pi * ((t : unitInterval) : ℝ) : ℝ)) : ℂ) * Complex.I)) =
      Work.Smooth.SphereJordan.pccutDir S * Complex.exp
        ((((2 * Real.pi * ((t : unitInterval) : ℝ) : ℝ)) : ℂ) * Complex.I)
    rw [Complex.exp_add, Complex.exp_log (Work.Smooth.SphereJordan.pccutDir_ne_zero S)]
  have hspec := Work.Smooth.SphereJordan.loopIndex_spec (pcwiStdLoop S) hne hcl Λ hlift
  have hsub : Λ 1 - Λ 0 = ((((2 * Real.pi * ((1 : unitInterval) : ℝ) : ℝ)) : ℂ) * Complex.I) -
      ((((2 * Real.pi * ((0 : unitInterval) : ℝ) : ℝ)) : ℂ) * Complex.I) := by
    show (Complex.log (Work.Smooth.SphereJordan.pccutDir S) +
        ((((2 * Real.pi * ((1 : unitInterval) : ℝ) : ℝ)) : ℂ) * Complex.I)) -
      (Complex.log (Work.Smooth.SphereJordan.pccutDir S) +
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
  have h4 : (((Work.Smooth.SphereJordan.loopIndex (pcwiStdLoop S) : ℤ)) : ℂ)
      * (2 * (Real.pi : ℂ) * Complex.I) = 2 * (Real.pi : ℂ) * Complex.I := hspec.symm
  have h5 : ((((Work.Smooth.SphereJordan.loopIndex (pcwiStdLoop S) : ℤ)) : ℂ) - 1)
      * (2 * (Real.pi : ℂ) * Complex.I) = 0 := by
    rw [sub_mul, one_mul, h4, sub_self]
  rcases mul_eq_zero.mp h5 with h | h
  · have h6 : ((Work.Smooth.SphereJordan.loopIndex (pcwiStdLoop S) : ℤ) : ℂ) = 1 := by
      linear_combination h
    exact_mod_cast h6
  · exact absurd h (Work.Smooth.SphereJordan.two_pi_I_ne_zero)

/-- The loop of the unit circle about `x` is the standard loop translated by `x`. -/
theorem pcwi_outerLoop_eq_std {h : Work.Smooth.SphereJordan.PlaneHypothesis} {hs : γ.IsSimple}
    {hball : ∀ θ : ℝ, ‖γ.γ θ‖ < 1} {S : Work.Smooth.Jordan.PlaneSchoenflies γ}
    (H : pcSpanHyp h hs hball S) (x : ℂ) (t : unitInterval) :
    pcouterLoop H x t = pcwiStdLoop S t - x := rfl

theorem pcwi_outerLoop_closed {h : Work.Smooth.SphereJordan.PlaneHypothesis} {hs : γ.IsSimple}
    {hball : ∀ θ : ℝ, ‖γ.γ θ‖ < 1} {S : Work.Smooth.Jordan.PlaneSchoenflies γ}
    (H : pcSpanHyp h hs hball S) (x : ℂ) : pcouterLoop H x 0 = pcouterLoop H x 1 := by
  rw [pcwi_outerLoop_eq_std H x 0, pcwi_outerLoop_eq_std H x 1, pcwi_std_closed S]

theorem pcwi_outerLoop_ne {h : Work.Smooth.SphereJordan.PlaneHypothesis} {hs : γ.IsSimple}
    {hball : ∀ θ : ℝ, ‖γ.γ θ‖ < 1} {S : Work.Smooth.Jordan.PlaneSchoenflies γ}
    (H : pcSpanHyp h hs hball S) {x : ℂ} (hx : x ∈ S.V) : ∀ t, pcouterLoop H x t ≠ 0 := by
  intro t hcon
  have hxlt : ‖x‖ < 1 := pcnorm_lt_one_of_mem_V S hball hx
  have h1 : pcwiStdLoop S t = x := by
    have h2 : pcwiStdLoop S t - x = 0 := by rw [← pcwi_outerLoop_eq_std H x t]; exact hcon
    exact sub_eq_zero.mp h2
  have h2 : ‖x‖ = 1 := by rw [← h1, pcwi_std_norm S t]
  linarith

theorem pcwi_loopIndex_outer {h : Work.Smooth.SphereJordan.PlaneHypothesis} {hs : γ.IsSimple}
    {hball : ∀ θ : ℝ, ‖γ.γ θ‖ < 1} {S : Work.Smooth.Jordan.PlaneSchoenflies γ}
    (H : pcSpanHyp h hs hball S) {x : ℂ} (hx : x ∈ S.V) :
    Work.Smooth.SphereJordan.loopIndex (pcouterLoop H x) = 1 := by
  have hxlt : ‖x‖ < 1 := pcnorm_lt_one_of_mem_V S hball hx
  have hne0 : ∀ t : unitInterval, pcwiStdLoop S t ≠ 0 := by
    intro t h
    have h1 : ‖pcwiStdLoop S t‖ = 1 := pcwi_std_norm S t
    rw [h, norm_zero] at h1
    exact one_ne_zero h1.symm
  have hne1 : ∀ t : unitInterval, pcouterLoop H x t ≠ 0 := pcwi_outerLoop_ne H hx
  set Hs : C(unitInterval × unitInterval, ℂ) :=
    ⟨fun p => pcwiStdLoop S p.1 - ((((p.2 : unitInterval) : ℝ)) : ℂ) * x, by fun_prop⟩ with hHs
  have happ : ∀ p : unitInterval × unitInterval, Hs p =
      pcwiStdLoop S p.1 - ((((p.2 : unitInterval) : ℝ)) : ℂ) * x := fun p => rfl
  have hHne : ∀ p : unitInterval × unitInterval, Hs p ≠ 0 := by
    rintro ⟨t, s⟩ hcon
    rw [happ] at hcon
    have hEq : pcwiStdLoop S t = ((((s : unitInterval) : ℝ)) : ℂ) * x := sub_eq_zero.mp hcon
    have h1 : ‖pcwiStdLoop S t‖ = 1 := pcwi_std_norm S t
    have h2 : ‖((((s : unitInterval) : ℝ)) : ℂ) * x‖ = 1 := by rw [← hEq, h1]
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg s.2.1] at h2
    nlinarith [norm_nonneg x, hxlt, h2, s.2.1, s.2.2]
  have hH0 : ∀ t : unitInterval, Hs (t, 0) = pcwiStdLoop S t := by
    intro t
    rw [happ]
    simp
  have hH1 : ∀ t : unitInterval, Hs (t, 1) = pcouterLoop H x t := by
    intro t
    rw [happ, pcwi_outerLoop_eq_std H x t]
    simp
  have hHloop : ∀ s : unitInterval, Hs (0, s) = Hs (1, s) := by
    intro s
    rw [happ, happ]
    rw [pcwi_std_closed S]
  have h := Work.Smooth.SphereJordan.loopIndex_eq_of_homotopy hne0 hne1 Hs hHne hH0 hH1 hHloop
  exact h.symm.trans (pcwi_loopIndex_std S)

theorem pcwi_incr'_outer {h : Work.Smooth.SphereJordan.PlaneHypothesis} {hs : γ.IsSimple}
    {hball : ∀ θ : ℝ, ‖γ.γ θ‖ < 1} {S : Work.Smooth.Jordan.PlaneSchoenflies γ}
    (H : pcSpanHyp h hs hball S) {x : ℂ} (hx : x ∈ S.V) : pcincr' (pcouterLoop H x) = pckappa := by
  have hne : ∀ t, pcouterLoop H x t ≠ 0 := pcwi_outerLoop_ne H hx
  have hcl : pcouterLoop H x 0 = pcouterLoop H x 1 := pcwi_outerLoop_closed H x
  rw [pcincr'_eq_loopIndex hne hcl, pcwi_loopIndex_outer H hx]
  ring

/-- The first half of the standard loop is the upper outer semicircle. -/
theorem pcwi_outerLoop_half1 {h : Work.Smooth.SphereJordan.PlaneHypothesis} {hs : γ.IsSimple}
    {hball : ∀ θ : ℝ, ‖γ.γ θ‖ < 1} {S : Work.Smooth.Jordan.PlaneSchoenflies γ}
    (H : pcSpanHyp h hs hball S) (x : ℂ) (t : unitInterval) :
    pcouterLoop H x (pchalf1 t) = pcupP1 H x t := by
  have hreal : 2 * Real.pi * ((pchalf1 t : unitInterval) : ℝ) = Real.pi * ((t : unitInterval) : ℝ) := by
    rw [pchalf1_val]; ring
  show Work.Smooth.SphereJordan.pccutDir S * Complex.exp
      ((((2 * Real.pi * ((pchalf1 t : unitInterval) : ℝ) : ℝ)) : ℂ) * Complex.I) - x
    = Work.Smooth.SphereJordan.pcsrcOuterUp S ((t : unitInterval) : ℝ) - x
  rw [hreal, Work.Smooth.SphereJordan.pcsrcOuterUp]

/-- The second half of the standard loop is the lower outer semicircle. -/
theorem pcwi_outerLoop_half2 {h : Work.Smooth.SphereJordan.PlaneHypothesis} {hs : γ.IsSimple}
    {hball : ∀ θ : ℝ, ‖γ.γ θ‖ < 1} {S : Work.Smooth.Jordan.PlaneSchoenflies γ}
    (H : pcSpanHyp h hs hball S) (x : ℂ) (t : unitInterval) :
    pcouterLoop H x (pchalf2 t) = pcdnP1 H x t := by
  have hreal : 2 * Real.pi * ((pchalf2 t : unitInterval) : ℝ)
      = Real.pi * ((t : unitInterval) : ℝ) + Real.pi := by
    rw [pchalf2_val]; ring
  have hsplit : ((((Real.pi * ((t : unitInterval) : ℝ) + Real.pi : ℝ)) : ℂ) * Complex.I)
      = (((Real.pi * ((t : unitInterval) : ℝ) : ℝ)) : ℂ) * Complex.I + (Real.pi : ℂ) * Complex.I := by
    push_cast; ring
  show Work.Smooth.SphereJordan.pccutDir S * Complex.exp
      ((((2 * Real.pi * ((pchalf2 t : unitInterval) : ℝ) : ℝ)) : ℂ) * Complex.I) - x
    = Work.Smooth.SphereJordan.pcsrcOuterDn S ((t : unitInterval) : ℝ) - x
  rw [hreal, hsplit, Complex.exp_add, Complex.exp_pi_mul_I,
    Work.Smooth.SphereJordan.pcsrcOuterDn]
  ring

/-- **The two outer semicircles account for the unit circle, hence for `pckappa`.** -/
theorem pcwi_incr'_semi {h : Work.Smooth.SphereJordan.PlaneHypothesis} {hs : γ.IsSimple}
    {hball : ∀ θ : ℝ, ‖γ.γ θ‖ < 1} {S : Work.Smooth.Jordan.PlaneSchoenflies γ}
    (H : pcSpanHyp h hs hball S) {x : ℂ} (hx : x ∈ S.V) :
    pcincr' (pcupP1 H x) + pcincr' (pcdnP1 H x) = pckappa := by
  have hne : ∀ t, pcouterLoop H x t ≠ 0 := pcwi_outerLoop_ne H hx
  have hs := pcwi_incr'_split (c := pcouterLoop H x) hne (σ := pchalf1) (τ := pchalf2)
    pchalf1_zero pchalf2_one (pchalf1_one.trans pchalf2_zero.symm)
  have h1 : pcincr' ((pcouterLoop H x).comp pchalf1) = pcincr' (pcupP1 H x) :=
    pcincr'_congr (fun t => pcwi_outerLoop_half1 H x t)
  have h2 : pcincr' ((pcouterLoop H x).comp pchalf2) = pcincr' (pcdnP1 H x) :=
    pcincr'_congr (fun t => pcwi_outerLoop_half2 H x t)
  exact (h1 ▸ h2 ▸ hs).trans (pcwi_incr'_outer H hx)

/-! ## The `γ`-arc pieces -/

theorem pcwi_incr'_upP3_true_eq_incOn {h : Work.Smooth.SphereJordan.PlaneHypothesis}
    {hs : γ.IsSimple} {hball : ∀ θ : ℝ, ‖γ.γ θ‖ < 1}
    {S : Work.Smooth.Jordan.PlaneSchoenflies γ}
    (H : pcSpanHyp h hs hball S) {x : ℂ} (hx : x ∈ S.V) :
    pcincr' (pcupP3 H x true) = incOn γ.γ γ.cont x H.θ₂ H.θ₁ := by
  rw [pcwi_incr'_eq_pathIncTot (pcupP3_ne H hx true)]
  exact pathIncTot_congr (fun t => rfl)

theorem pcwi_incr'_dnP3_true_eq_incOn {h : Work.Smooth.SphereJordan.PlaneHypothesis}
    {hs : γ.IsSimple} {hball : ∀ θ : ℝ, ‖γ.γ θ‖ < 1}
    {S : Work.Smooth.Jordan.PlaneSchoenflies γ}
    (H : pcSpanHyp h hs hball S) {x : ℂ} (hx : x ∈ S.V) :
    pcincr' (pcdnP3 H x true) = incOn γ.γ γ.cont x (H.θ₁ - 2 * Real.pi) H.θ₂ := by
  rw [pcwi_incr'_eq_pathIncTot (pcdnP3_ne H hx true)]
  refine pathIncTot_congr (fun t => ?_)
  show γ.γ (H.θ₁ - 2 * Real.pi + ((t : unitInterval) : ℝ) * (H.θ₂ - H.θ₁ + 2 * Real.pi)) - x
      = γ.γ (H.θ₁ - 2 * Real.pi +
          ((t : unitInterval) : ℝ) * (H.θ₂ - (H.θ₁ - 2 * Real.pi))) - x
  congr 1
  ring

/-- **The two `γ`-arc pieces of `(pcupPC true, pcdnPC true)` make up one full period of `γ`.** -/
theorem pcwi_incr'_gamma_TT {h : Work.Smooth.SphereJordan.PlaneHypothesis} {hs : γ.IsSimple}
    {hball : ∀ θ : ℝ, ‖γ.γ θ‖ < 1} {S : Work.Smooth.Jordan.PlaneSchoenflies γ}
    (H : pcSpanHyp h hs hball S) {x : ℂ} (hx : x ∈ S.V) :
    pcincr' (pcupP3 H x true) + pcincr' (pcdnP3 H x true)
      = (Work.Smooth.SphereJordan.windNumber γ.γ γ.cont x : ℂ) * pckappa := by
  have hz : ∀ t : ℝ, γ.γ t ≠ x := fun t => pcgamma_ne S hx t
  have hav : ∀ t ∈ Set.Icc (H.θ₁ - 2 * Real.pi) H.θ₁, γ.γ t ≠ x := fun t _ => hz t
  have hθ : H.θ₁ - 2 * Real.pi ≤ H.θ₂ := by linarith [H.hθ, H.hθ']
  have hθ' : H.θ₂ ≤ H.θ₁ := le_of_lt H.hθ
  have hadd := incOn_add γ.cont hθ hθ' hav
  have hper := incOn_period γ.cont γ.periodic x hz (H.θ₁ - 2 * Real.pi)
  have hk : H.θ₁ - 2 * Real.pi + 2 * Real.pi = H.θ₁ := by ring
  rw [hk] at hper
  rw [pcwi_incr'_upP3_true_eq_incOn H hx, pcwi_incr'_dnP3_true_eq_incOn H hx, pckappa, ← hper,
    hadd]
  ring

/-- The short `γ`-arcs of `(pcupPC true, pcdnPC false)` cancel. -/
theorem pcwi_incr'_gamma_TF {h : Work.Smooth.SphereJordan.PlaneHypothesis} {hs : γ.IsSimple}
    {hball : ∀ θ : ℝ, ‖γ.γ θ‖ < 1} {S : Work.Smooth.Jordan.PlaneSchoenflies γ}
    (H : pcSpanHyp h hs hball S) (x : ℂ) :
    pcincr' (pcupP3 H x true) + pcincr' (pcdnP3 H x false) = 0 := by
  have hcongr : ∀ t : unitInterval, pcdnP3 H x false t = (pcupP3 H x true).comp revI t := by
    intro t
    simp only [pcupP3, pcdnP3, ContinuousMap.comp_apply, ContinuousMap.coe_mk, pcrevI_val,
      reduceIte, Bool.false_eq_true]
    congr 1
    ring
  rw [pcincr'_congr hcongr, pcincr'_rev]
  ring

/-- The complementary `γ`-arcs of `(pcupPC false, pcdnPC true)` cancel. -/
theorem pcwi_incr'_gamma_FT {h : Work.Smooth.SphereJordan.PlaneHypothesis} {hs : γ.IsSimple}
    {hball : ∀ θ : ℝ, ‖γ.γ θ‖ < 1} {S : Work.Smooth.Jordan.PlaneSchoenflies γ}
    (H : pcSpanHyp h hs hball S) (x : ℂ) :
    pcincr' (pcupP3 H x false) + pcincr' (pcdnP3 H x true) = 0 := by
  have hcongr : ∀ t : unitInterval, pcdnP3 H x true t = (pcupP3 H x false).comp revI t := by
    intro t
    simp only [pcupP3, pcdnP3, ContinuousMap.comp_apply, ContinuousMap.coe_mk, pcrevI_val,
      reduceIte, Bool.false_eq_true]
    congr 1
    ring
  rw [pcincr'_congr hcongr, pcincr'_rev]
  ring


/-! ## The winding number as the sum of the four quarter increments -/

theorem pcwi_wind_up_eq {h : Work.Smooth.SphereJordan.PlaneHypothesis} {hs : γ.IsSimple}
    {hball : ∀ θ : ℝ, ‖γ.γ θ‖ < 1} {S : Work.Smooth.Jordan.PlaneSchoenflies γ}
    (H : pcSpanHyp h hs hball S) {x : ℂ} (hx : x ∈ S.V) (b : Bool) :
    (Work.Smooth.SphereJordan.windNumber (H.pcupPC b).γ (H.pcupPC b).cont x : ℂ) * pckappa
      = pcincr' (pcupP1 H x) + pcincr' (pcupP2 H x) + pcincr' (pcupP3 H x b) + pcincr' (pcupP4 H x) := by
  have hc : ∀ t : unitInterval, pcupLoop H x b t ≠ 0 := pcupLoop_ne H hx b
  have hcl : pcupLoop H x b 0 = pcupLoop H x b 1 := pcwi_upLoop_closed H x b
  have h1 : pcincr' (pcupLoop H x b) =
      (Work.Smooth.SphereJordan.loopIndex (pcupLoop H x b) : ℂ) * pckappa :=
    pcincr'_eq_loopIndex hc hcl
  rw [pcwindNumber_upLoop, ← h1, pcwi_incr'_quarter hc]
  rw [pcincr'_congr (c := (pcupLoop H x b).comp q1) (d := pcupP1 H x)
        (fun t => pcwi_upLoop_q1 H x b t),
      pcincr'_congr (c := (pcupLoop H x b).comp q2) (d := pcupP2 H x)
        (fun t => pcwi_upLoop_q2 H x b t),
      pcincr'_congr (c := (pcupLoop H x b).comp q3) (d := pcupP3 H x b)
        (fun t => pcwi_upLoop_q3 H x b t),
      pcincr'_congr (c := (pcupLoop H x b).comp q4) (d := pcupP4 H x)
        (fun t => pcwi_upLoop_q4 H x b t)]

theorem pcwi_wind_dn_eq {h : Work.Smooth.SphereJordan.PlaneHypothesis} {hs : γ.IsSimple}
    {hball : ∀ θ : ℝ, ‖γ.γ θ‖ < 1} {S : Work.Smooth.Jordan.PlaneSchoenflies γ}
    (H : pcSpanHyp h hs hball S) {x : ℂ} (hx : x ∈ S.V) (b : Bool) :
    (Work.Smooth.SphereJordan.windNumber (H.pcdnPC b).γ (H.pcdnPC b).cont x : ℂ) * pckappa
      = pcincr' (pcdnP1 H x) + pcincr' (pcdnP2 H x) + pcincr' (pcdnP3 H x b) + pcincr' (pcdnP4 H x) := by
  have hc : ∀ t : unitInterval, pcdnLoop H x b t ≠ 0 := pcdnLoop_ne H hx b
  have hcl : pcdnLoop H x b 0 = pcdnLoop H x b 1 := pcwi_dnLoop_closed H x b
  have h1 : pcincr' (pcdnLoop H x b) =
      (Work.Smooth.SphereJordan.loopIndex (pcdnLoop H x b) : ℂ) * pckappa :=
    pcincr'_eq_loopIndex hc hcl
  rw [pcwindNumber_dnLoop, ← h1, pcwi_incr'_quarter hc]
  rw [pcincr'_congr (c := (pcdnLoop H x b).comp q1) (d := pcdnP1 H x)
        (fun t => pcwi_dnLoop_q1 H x b t),
      pcincr'_congr (c := (pcdnLoop H x b).comp q2) (d := pcdnP2 H x)
        (fun t => pcwi_dnLoop_q2 H x b t),
      pcincr'_congr (c := (pcdnLoop H x b).comp q3) (d := pcdnP3 H x b)
        (fun t => pcwi_dnLoop_q3 H x b t),
      pcincr'_congr (c := (pcdnLoop H x b).comp q4) (d := pcdnP4 H x)
        (fun t => pcwi_dnLoop_q4 H x b t)]

/-! ## The three identities -/

theorem pcwindIdentitiesProof {γ : Work.Smooth.Jordan.PlaneCurve}
    (h : Work.Smooth.SphereJordan.PlaneHypothesis) (hs : γ.IsSimple)
    (hball : ∀ θ : ℝ, ‖γ.γ θ‖ < 1) (S : Work.Smooth.Jordan.PlaneSchoenflies γ)
    (H : Work.SphereJordan.pcSpanHyp h hs hball S) :
    ∀ x : ℂ, x ∈ S.V →
      (Work.Smooth.SphereJordan.windNumber (H.pcupPC true).γ (H.pcupPC true).cont x
        + Work.Smooth.SphereJordan.windNumber (H.pcdnPC false).γ (H.pcdnPC false).cont x = 1) ∧
      (Work.Smooth.SphereJordan.windNumber (H.pcupPC false).γ (H.pcupPC false).cont x
        + Work.Smooth.SphereJordan.windNumber (H.pcdnPC true).γ (H.pcdnPC true).cont x = 1) ∧
      (Work.Smooth.SphereJordan.windNumber (H.pcupPC true).γ (H.pcupPC true).cont x
        + Work.Smooth.SphereJordan.windNumber (H.pcdnPC true).γ (H.pcdnPC true).cont x
        = 1 + Work.Smooth.SphereJordan.windNumber γ.γ γ.cont x) := by
  intro x hx
  have hupT := pcwi_wind_up_eq H hx true
  have hdnT := pcwi_wind_dn_eq H hx true
  have hupF := pcwi_wind_up_eq H hx false
  have hdnF := pcwi_wind_dn_eq H hx false
  have hsemi : pcincr' (pcupP1 H x) + pcincr' (pcdnP1 H x) = pckappa := pcwi_incr'_semi H hx
  obtain ⟨hcut1, hcut2⟩ := pcwi_incr'_cut_pair H x
  have hcut2' : pcincr' (pcupP4 H x) + pcincr' (pcdnP2 H x) = 0 := by rw [add_comm]; exact hcut2
  have hgTF := pcwi_incr'_gamma_TF H x
  have hgFT := pcwi_incr'_gamma_FT H x
  have hgTT := pcwi_incr'_gamma_TT H hx
  set a : ℤ := Work.Smooth.SphereJordan.windNumber (H.pcupPC true).γ (H.pcupPC true).cont x
    with ha
  set b : ℤ := Work.Smooth.SphereJordan.windNumber (H.pcdnPC true).γ (H.pcdnPC true).cont x
    with hb
  set c : ℤ := Work.Smooth.SphereJordan.windNumber (H.pcupPC false).γ (H.pcupPC false).cont x
    with hc
  set d : ℤ := Work.Smooth.SphereJordan.windNumber (H.pcdnPC false).γ (H.pcdnPC false).cont x
    with hd
  set e : ℤ := Work.Smooth.SphereJordan.windNumber γ.γ γ.cont x with he
  refine ⟨?_, ?_, ?_⟩
  · have key : ((a : ℂ) + d) * pckappa = pckappa := by
      rw [add_mul, hupT, hdnF]
      linear_combination hsemi + hcut1 + hgTF + hcut2'
    have hkey : (a : ℂ) + d = 1 := by
      refine mul_right_cancel₀ pckappa_ne_zero ?_
      rw [key, one_mul]
    have hcast : ((a + d : ℤ) : ℂ) = 1 := by
      push_cast
      exact hkey
    exact_mod_cast hcast
  · have key : ((c : ℂ) + b) * pckappa = pckappa := by
      rw [add_mul, hupF, hdnT]
      linear_combination hsemi + hcut1 + hgFT + hcut2'
    have hkey : (c : ℂ) + b = 1 := by
      refine mul_right_cancel₀ pckappa_ne_zero ?_
      rw [key, one_mul]
    have hcast : ((c + b : ℤ) : ℂ) = 1 := by
      push_cast
      exact hkey
    have hres : c + b = 1 := by exact_mod_cast hcast
    linarith
  · have key : ((a : ℂ) + b) * pckappa = (1 + (e : ℂ)) * pckappa := by
      rw [add_mul, hupT, hdnT]
      linear_combination hsemi + hcut1 + hgTT + hcut2'
    have hkey : (a : ℂ) + b = 1 + (e : ℂ) := mul_right_cancel₀ pckappa_ne_zero key
    have hcast : ((a + b : ℤ) : ℂ) = ((1 + e : ℤ) : ℂ) := by
      push_cast
      exact hkey
    exact_mod_cast hcast
end

end Work.SphereJordan
