import Mathlib
import Submission.Work.OddVolterra.Free.FreeSetup
import Submission.Work.OddVolterra.Free.envelopeLeft_gap_dev_orders_two
import Submission.Work.OddVolterra.Free.wideProfileXOneThird

/-!
# The left-branch deviation at orders `k ≤ 2`, parametrised by the slope

This file proves `Work.OddVolterra.Free.envelopeLeftWideDevOrdersTwo`.

It is the *slope-parametrised* companion of
`Work.OddVolterra.Free.envelopeLeft_gap_dev_orders_two`: instead of testing the profile at a point
`-ξ` with `ξ ∈ (tStar, cStar)`, it tests it at the point `-(X σ)` for a *given* slope `σ ∈ [7/10,1]`
(the range, twice as wide as the gap window, on which the chord-curve hypotheses are available), and
it takes the data of the bump `h` at `σ` only (rather than `L^∞` bounds).

The proof has the same shape as the gap version: with `ξ := X σ` and `σ₁ := √(1-ξ²)/ξ` (the slope
of the *semicircle* chord through `ξ`),

* `envelopeProfile h X Y (-ξ) = σ · ξ - h σ` while `semicircle (-ξ) = σ₁ · ξ`, so the value
  deviation is `(σ - σ₁) ξ - h σ`;
* `deriv (envelopeProfile h X Y) (-ξ) = -(ξ + σ X'σ - h'σ)/X'σ` while
  `deriv semicircle (-ξ) = 1/σ₁`;
* `deriv (deriv (envelopeProfile h X Y)) (-ξ) = (2 X'σ² - ξ X''σ - h''σ X'σ + h'σ X''σ)/X'σ³`
  while `deriv (deriv semicircle) (-ξ) = Ψ₀ σ₁` with `Ψ₀ s = -(1/(s·profileX s)³)`.

Both slopes lie in the *wide* interval `[2/3, 1]` (because `ξ ≤ X (7/10) ≤ 41/50 + 1/100 < profileX
(2/3)` and `ξ ≥ X 1 = profileX 1`), so the numerical input is the Lipschitz machinery for `profileX`
on `[2/3,1]`, isolated in the namespace `WideAux` below (and, for the sharpest piece,
`|profileX'| ≥ 1/3`, imported from `wideProfileXOneThird`).
-/

namespace Work.OddVolterra.Free

open Work.OddCurve.LowSlope
open Work.OddVolterra.Free.LeftGapAux

set_option maxHeartbeats 8000000

/-! ## Numerical facts for `profileX` on the wide interval `[2/3, 1]` -/

namespace WideAux

/-- `|profileX''| ≤ 1` on `[2/3, 1]`. -/
theorem deriv2_le_one {s : ℝ} (h1 : 2 / 3 ≤ s) (h2 : s ≤ 1) :
    |deriv (deriv Work.OddEnvelope.profileX) s| ≤ 1 := by
  rw [(Work.OddEnvelope.Close.profileX_deriv_formulas s).2.1]
  have hspos : 0 < s := by linarith
  have hp1 : Work.OddEnvelope.profileX s ≤ 1 :=
    le_of_lt (Work.OddEnvelope.profileX_lt_one hspos)
  have hp0 : 0 ≤ Work.OddEnvelope.profileX s := le_of_lt (Work.OddEnvelope.profileX_pos s)
  have h3 : |2 * s ^ 2 - 1| ≤ 1 := by
    rw [abs_le]; constructor <;> nlinarith
  have h4 : |Work.OddEnvelope.profileX s ^ 5| ≤ 1 := by
    rw [abs_of_nonneg (by positivity)]
    exact pow_le_one₀ hp0 hp1
  rw [abs_mul]
  calc |2 * s ^ 2 - 1| * |Work.OddEnvelope.profileX s ^ 5| ≤ 1 * 1 :=
        mul_le_mul h3 h4 (abs_nonneg _) (by norm_num)
    _ = 1 := by ring

/-- Lipschitz bound for `profileX'` on the wide interval `[2/3, 1]`. -/
theorem deriv_lipschitz {a b : ℝ} (ha : a ∈ Set.Icc (2 / 3 : ℝ) 1)
    (hb : b ∈ Set.Icc (2 / 3 : ℝ) 1) :
    |deriv Work.OddEnvelope.profileX a - deriv Work.OddEnvelope.profileX b| ≤ |a - b| := by
  have hdiff : ∀ x ∈ Set.Icc (2 / 3 : ℝ) 1,
      DifferentiableAt ℝ (deriv Work.OddEnvelope.profileX) x :=
    fun x _ => differentiableAt_deriv_profileX x
  have hbound : ∀ x ∈ Set.Icc (2 / 3 : ℝ) 1,
      ‖deriv (deriv Work.OddEnvelope.profileX) x‖ ≤ 1 := by
    intro x hx
    rw [Real.norm_eq_abs]
    exact deriv2_le_one hx.1 hx.2
  have h := Convex.norm_image_sub_le_of_norm_deriv_le hdiff hbound (convex_Icc _ _) ha hb
  rw [Real.norm_eq_abs, Real.norm_eq_abs, one_mul] at h
  linarith [h, abs_sub_comm (deriv Work.OddEnvelope.profileX a)
    (deriv Work.OddEnvelope.profileX b), abs_sub_comm a b]

/-- Lipschitz bound for `s ↦ s * profileX s` on the wide interval `[2/3, 1]`. -/
theorem mul_lipschitz {a b : ℝ} (ha : a ∈ Set.Icc (2 / 3 : ℝ) 1)
    (hb : b ∈ Set.Icc (2 / 3 : ℝ) 1) :
    |a * Work.OddEnvelope.profileX a - b * Work.OddEnvelope.profileX b| ≤ |a - b| := by
  have hdiff : ∀ x ∈ Set.Icc (2 / 3 : ℝ) 1,
      DifferentiableAt ℝ (fun s : ℝ => s * Work.OddEnvelope.profileX s) x :=
    fun x _ => differentiableAt_mul_profileX x
  have hbound : ∀ x ∈ Set.Icc (2 / 3 : ℝ) 1,
      ‖deriv (fun s : ℝ => s * Work.OddEnvelope.profileX s) x‖ ≤ 1 := by
    intro x hx
    have hx0 : 0 < x := by linarith [hx.1]
    rw [Real.norm_eq_abs]
    have hd : deriv (fun s : ℝ => s * Work.OddEnvelope.profileX s) x
        = Work.OddEnvelope.profileX x ^ 3 := by
      change deriv ((id : ℝ → ℝ) * Work.OddEnvelope.profileX) x
        = Work.OddEnvelope.profileX x ^ 3
      have h := deriv_mul (x := x) differentiableAt_id (differentiableAt_profileX x)
      simp only [Pi.mul_apply, id_eq] at h
      rw [h, show deriv (id : ℝ → ℝ) x = 1 from by simp, one_mul]
      exact (Work.OddEnvelope.Close.profileX_deriv_formulas x).2.2.1
    rw [hd, abs_of_nonneg (pow_nonneg (le_of_lt (Work.OddEnvelope.profileX_pos x)) 3)]
    exact pow_le_one₀ (le_of_lt (Work.OddEnvelope.profileX_pos x))
      (le_of_lt (Work.OddEnvelope.profileX_lt_one hx0))
  have h := Convex.norm_image_sub_le_of_norm_deriv_le hdiff hbound (convex_Icc _ _) ha hb
  rw [Real.norm_eq_abs, Real.norm_eq_abs, one_mul] at h
  linarith [h, abs_sub_comm (a * Work.OddEnvelope.profileX a)
    (b * Work.OddEnvelope.profileX b), abs_sub_comm a b]

/-- `a * profileX a ≥ 1/2` for `a ∈ [2/3, 1]`. -/
theorem one_half_le_mul {a : ℝ} (h1 : 2 / 3 ≤ a) (h2 : a ≤ 1) :
    1 / 2 ≤ a * Work.OddEnvelope.profileX a := by
  have ha0 : 0 < a := by linarith
  have hpa : 0 < Work.OddEnvelope.profileX a := Work.OddEnvelope.profileX_pos a
  have hsq : (a * Work.OddEnvelope.profileX a) ^ 2 = a ^ 2 / (1 + a ^ 2) := by
    rw [mul_pow, Work.OddEnvelope.profileX_sq]; field_simp
  have hge : ((1 : ℝ) / 2) ^ 2 ≤ (a * Work.OddEnvelope.profileX a) ^ 2 := by
    rw [hsq, le_div_iff₀ (by positivity : (0 : ℝ) < 1 + a ^ 2)]
    nlinarith
  have hnn : 0 ≤ a * Work.OddEnvelope.profileX a := le_of_lt (mul_pos ha0 hpa)
  have h' := sq_le_sq.mp hge
  rwa [abs_of_nonneg hnn, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)] at h'

/-- **Reverse Lipschitz bound for `profileX` on `[2/3, 1]`**: the mean value theorem with
`|profileX'| ≥ 1/3` there turns a bound on the values into a bound on the arguments. -/
theorem reverse_lipschitz {a b : ℝ} (ha : 2 / 3 ≤ a) (ha' : a ≤ 1) (hb : 2 / 3 ≤ b)
    (hb' : b ≤ 1) :
    |a - b| ≤ 3 * |Work.OddEnvelope.profileX a - Work.OddEnvelope.profileX b| := by
  have key : ∀ {u v : ℝ}, 2 / 3 ≤ u → v ≤ 1 → u < v →
      v - u ≤ 3 * |Work.OddEnvelope.profileX v - Work.OddEnvelope.profileX u| := by
    intro u v hu hv' huv
    have hcont : ContinuousOn Work.OddEnvelope.profileX (Set.Icc u v) :=
      contDiffOn_profileX_Ioi.continuousOn.mono
        (fun x hx => lt_of_lt_of_le (by linarith : (0 : ℝ) < u) hx.1)
    have hdiff : DifferentiableOn ℝ Work.OddEnvelope.profileX (Set.Ioo u v) :=
      (contDiffOn_profileX_Ioi.differentiableOn (by simp)).mono
        (fun x hx => lt_of_lt_of_le (by linarith : (0 : ℝ) < u) hx.1.le)
    obtain ⟨ξ, hξ, hξeq⟩ := exists_deriv_eq_slope Work.OddEnvelope.profileX huv hcont hdiff
    have huv0 : 0 < v - u := by linarith
    have hd : 1 / 3 ≤ |deriv Work.OddEnvelope.profileX ξ| :=
      wideProfileXOneThird ξ (le_trans hu hξ.1.le) (le_trans hξ.2.le hv')
    have hmain : |Work.OddEnvelope.profileX v - Work.OddEnvelope.profileX u|
        = |deriv Work.OddEnvelope.profileX ξ| * (v - u) := by
      rw [hξeq, abs_div, abs_of_pos huv0, div_mul_cancel₀ _ (ne_of_gt huv0)]
    rw [hmain]; nlinarith [hd, huv0]
  rcases lt_trichotomy a b with hlt | heq | hgt
  · have h := key ha hb' hlt
    rw [abs_of_neg (by linarith : a - b < 0), abs_sub_comm]
    linarith
  · rw [heq, sub_self, abs_zero]; positivity
  · have h := key hb ha' hgt
    rw [abs_of_pos (by linarith : (0 : ℝ) < a - b)]
    linarith

/-- **Lipschitz bound for `H s = ξ / profileX' s + s`** on `[2/3, 1]`. -/
theorem gapH_lipschitz {ξ : ℝ} (hξ : |ξ| ≤ 1) {a b : ℝ}
    (ha : 2 / 3 ≤ a) (ha' : a ≤ 1) (hb : 2 / 3 ≤ b) (hb' : b ≤ 1) :
    |(ξ / deriv Work.OddEnvelope.profileX a + a)
      - (ξ / deriv Work.OddEnvelope.profileX b + b)| ≤ 10 * |a - b| := by
  have hpd := deriv_lipschitz ⟨ha, ha'⟩ ⟨hb, hb'⟩
  have ha3 : 1 / 3 ≤ |deriv Work.OddEnvelope.profileX a| := wideProfileXOneThird a ha ha'
  have hb3 : 1 / 3 ≤ |deriv Work.OddEnvelope.profileX b| := wideProfileXOneThird b hb hb'
  have hpa : 0 < |deriv Work.OddEnvelope.profileX a| := by linarith
  have hpb : 0 < |deriv Work.OddEnvelope.profileX b| := by linarith
  have hne_a : deriv Work.OddEnvelope.profileX a ≠ 0 := abs_pos.mp hpa
  have hne_b : deriv Work.OddEnvelope.profileX b ≠ 0 := abs_pos.mp hpb
  have h1 : |1 / deriv Work.OddEnvelope.profileX a - 1 / deriv Work.OddEnvelope.profileX b|
      ≤ 9 * |a - b| := by
    have hkey : 1 / deriv Work.OddEnvelope.profileX a
          - 1 / deriv Work.OddEnvelope.profileX b
        = (deriv Work.OddEnvelope.profileX b - deriv Work.OddEnvelope.profileX a)
          / (deriv Work.OddEnvelope.profileX a * deriv Work.OddEnvelope.profileX b) := by
      field_simp
    rw [hkey, abs_div, abs_mul]
    rw [div_le_iff₀ (mul_pos hpa hpb)]
    have hd' : |deriv Work.OddEnvelope.profileX b - deriv Work.OddEnvelope.profileX a|
        ≤ |a - b| := by
      rw [abs_sub_comm]; exact hpd
    have hprod : (1 / 9 : ℝ) ≤ |deriv Work.OddEnvelope.profileX a|
        * |deriv Work.OddEnvelope.profileX b| := by
      have h := mul_le_mul ha3 hb3 (by norm_num : (0 : ℝ) ≤ 1 / 3) (le_of_lt hpa)
      norm_num at h
      exact h
    calc |deriv Work.OddEnvelope.profileX b - deriv Work.OddEnvelope.profileX a|
        ≤ |a - b| := hd'
      _ = 9 * |a - b| * (1 / 9) := by ring
      _ ≤ 9 * |a - b| * (|deriv Work.OddEnvelope.profileX a|
            * |deriv Work.OddEnvelope.profileX b|) :=
          mul_le_mul_of_nonneg_left hprod (by positivity)
  have h2 : |(ξ / deriv Work.OddEnvelope.profileX a + a)
      - (ξ / deriv Work.OddEnvelope.profileX b + b)|
      ≤ |ξ| * |1 / deriv Work.OddEnvelope.profileX a
          - 1 / deriv Work.OddEnvelope.profileX b| + |a - b| := by
    have hsplit : (ξ / deriv Work.OddEnvelope.profileX a + a)
        - (ξ / deriv Work.OddEnvelope.profileX b + b)
        = ξ * (1 / deriv Work.OddEnvelope.profileX a
            - 1 / deriv Work.OddEnvelope.profileX b) + (a - b) := by
      field_simp
      ring
    rw [hsplit]
    calc |ξ * (1 / deriv Work.OddEnvelope.profileX a
            - 1 / deriv Work.OddEnvelope.profileX b) + (a - b)|
        ≤ |ξ * (1 / deriv Work.OddEnvelope.profileX a
            - 1 / deriv Work.OddEnvelope.profileX b)| + |a - b| := abs_add_le _ _
      _ = |ξ| * |1 / deriv Work.OddEnvelope.profileX a
            - 1 / deriv Work.OddEnvelope.profileX b| + |a - b| := by rw [abs_mul]
  have h3 : |ξ| * |1 / deriv Work.OddEnvelope.profileX a
      - 1 / deriv Work.OddEnvelope.profileX b| ≤ 9 * |a - b| := by
    calc |ξ| * |1 / deriv Work.OddEnvelope.profileX a
          - 1 / deriv Work.OddEnvelope.profileX b|
        ≤ 1 * (9 * |a - b|) := mul_le_mul hξ h1 (abs_nonneg _) (by norm_num)
      _ = 9 * |a - b| := by ring
  linarith [h2, h3, abs_nonneg (a - b)]

/-- **Lipschitz bound for `Ψ₀ s = -(1/(s · profileX s)³)`** on `[2/3, 1]`. -/
theorem gapPsi0_lipschitz {a b : ℝ} (ha : 2 / 3 ≤ a) (ha' : a ≤ 1) (hb : 2 / 3 ≤ b)
    (hb' : b ≤ 1) :
    |gapPsi0 a - gapPsi0 b| ≤ 200 * |a - b| := by
  have hA := mul_lipschitz ⟨ha, ha'⟩ ⟨hb, hb'⟩
  have ha0 : 0 < a := by linarith
  have hb0 : 0 < b := by linarith
  have hpa : 1 / 2 ≤ a * Work.OddEnvelope.profileX a := one_half_le_mul ha ha'
  have hpb : 1 / 2 ≤ b * Work.OddEnvelope.profileX b := one_half_le_mul hb hb'
  have hAmax : a * Work.OddEnvelope.profileX a ≤ 1 := by
    have := Work.OddEnvelope.profileX_lt_one ha0
    nlinarith [ha']
  have hBmax : b * Work.OddEnvelope.profileX b ≤ 1 := by
    have := Work.OddEnvelope.profileX_lt_one hb0
    nlinarith [hb']
  have hcube := abs_inv_cube_sub_le hpa hAmax hpb hBmax
  have heq : gapPsi0 a - gapPsi0 b
      = -(1 / (a * Work.OddEnvelope.profileX a) ^ 3
          - 1 / (b * Work.OddEnvelope.profileX b) ^ 3) := by
    simp only [gapPsi0]; ring
  rw [heq, abs_neg]
  nlinarith [hcube, abs_nonneg (a - b), hA]

end WideAux

/-- **The left-branch deviation at orders `k ≤ 2`, slope-parametrised form.**

Specialising `Work.OddVolterra.Free.envelopeLeftWideDevOrdersTwo` to the point `-X σ` of the
envelope profile does not change the statement: for `σ ∈ [7/10, 1]` the chord-curve data of `X` and
the bump data of `h` at `σ` control the value, the first and the second derivative of the left
branch at `-(X σ)` up to `C (η + ε)`. -/
theorem envelopeLeftWideDevOrdersTwo (n : ℕ) (hn : 1 ≤ n) :
    ∃ C : ℝ, 0 < C ∧ ∀ {ε η σ : ℝ} {h X Y : ℝ → ℝ},
      0 ≤ η → η ≤ 1 / 100 →
      Work.OddEnvelope.IsEnvelopeCurve h X Y →
      7 / 10 ≤ σ → σ ≤ 1 →
      (∀ s : ℝ, 7 / 10 ≤ s → s ≤ 1 →
        |X s - Work.OddEnvelope.profileX s| ≤ η ∧
        |deriv X s - deriv Work.OddEnvelope.profileX s| ≤ η ∧
        |deriv (deriv X) s - deriv (deriv Work.OddEnvelope.profileX) s| ≤ η) →
      (|h σ| ≤ ε ∧ |deriv h σ| ≤ ε ∧ |deriv (deriv h) σ| ≤ ε) →
      ∀ k : ℕ, k ≤ 2 →
        |iteratedDeriv k (Work.OddEnvelope.envelopeProfile h X Y) (-(X σ)) -
          iteratedDeriv k Work.OddEnvelope.semicircle (-(X σ))| ≤ C * (η + ε) := by
  refine ⟨1000000, by norm_num, ?_⟩
  intro ε η σ h X Y hη0 hη100 H hσlo hσhi hclose hh k hk
  -- ### elementary data
  have hε0 : 0 ≤ ε := le_trans (abs_nonneg _) hh.1
  have hσpos : 0 < σ := by linarith
  have hσ23 : (2 / 3 : ℝ) ≤ σ := by linarith
  have hσI : σ ∈ Set.Icc (2 / 3 : ℝ) 1 := ⟨hσ23, hσhi⟩
  have hxpos : 0 < X σ := H.toChordCurve_x.pos hσpos
  have hxlt1 : X σ < 1 := H.toChordCurve_x.lt_one hσpos
  have hxI : X σ ∈ Set.Ioo (0 : ℝ) 1 := ⟨hxpos, hxlt1⟩
  have hxabs : |X σ| ≤ 1 := abs_le.mpr ⟨by linarith, le_of_lt hxlt1⟩
  have hξ2pos : 0 < 1 - (X σ) ^ 2 := by nlinarith
  -- ### the semicircle slope `σ₁` through `X σ`
  set σ₁ : ℝ := Real.sqrt (1 - (X σ) ^ 2) / (X σ) with hσ₁def
  have hσ₁pos : 0 < σ₁ := div_pos (Real.sqrt_pos.mpr hξ2pos) hxpos
  have hσ₁ξ : σ₁ * (X σ) = Real.sqrt (1 - (X σ) ^ 2) := by
    rw [hσ₁def]; field_simp
  have hprofσ₁ : Work.OddEnvelope.profileX σ₁ = X σ := by
    have hsq : σ₁ ^ 2 = (1 - (X σ) ^ 2) / (X σ) ^ 2 := by
      rw [hσ₁def, div_pow, Real.sq_sqrt (le_of_lt hξ2pos)]
    rw [Work.OddEnvelope.profileX,
      show (1 : ℝ) + σ₁ ^ 2 = (1 / (X σ)) ^ 2 by rw [hsq]; field_simp; ring,
      Real.sqrt_sq (le_of_lt (one_div_pos.mpr hxpos))]
    field_simp
  -- ### the two slopes both lie in the wide interval `[2/3, 1]`
  have hp7 : Work.OddEnvelope.profileX (7 / 10) ≤ 41 / 50 := by
    have hsq : Work.OddEnvelope.profileX (7 / 10) ^ 2 ≤ ((41 : ℝ) / 50) ^ 2 := by
      rw [Work.OddEnvelope.profileX_sq]; norm_num
    have h := sq_le_sq.mp hsq
    rwa [abs_of_nonneg (le_of_lt (Work.OddEnvelope.profileX_pos _)),
      abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 41 / 50)] at h
  have h83 : (83 : ℝ) / 100 < Work.OddEnvelope.profileX (2 / 3) := by
    have hsq : ((83 : ℝ) / 100) ^ 2 < Work.OddEnvelope.profileX (2 / 3) ^ 2 := by
      rw [Work.OddEnvelope.profileX_sq]; norm_num
    have h := sq_lt_sq.mp hsq
    rwa [abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 83 / 100),
      abs_of_nonneg (le_of_lt (Work.OddEnvelope.profileX_pos _))] at h
  have hX7 : X (7 / 10) ≤ Work.OddEnvelope.profileX (7 / 10) + η := by
    have h := hclose (7 / 10) (by norm_num) (by norm_num)
    linarith [(abs_le.mp h.1).2]
  have hξ_le : X σ ≤ Work.OddEnvelope.profileX (7 / 10) + η := by
    have hle : X σ ≤ X (7 / 10) := by
      rcases lt_or_eq_of_le hσlo with hlt | heq
      · exact le_of_lt (H.toChordCurve_x.strictAntiOn (by norm_num : (0 : ℝ) < 7 / 10) hσpos hlt)
      · rw [heq]
    linarith
  have hξ_lt_p23 : X σ < Work.OddEnvelope.profileX (2 / 3) := by
    have h : X σ ≤ (41 : ℝ) / 50 + 1 / 100 := by linarith [hξ_le, hp7]
    have h2 : (41 : ℝ) / 50 + 1 / 100 = 83 / 100 := by norm_num
    rw [h2] at h
    linarith
  have hσ₁_gt : (2 / 3 : ℝ) < σ₁ := by
    by_contra hcon
    push Not at hcon
    rcases lt_or_eq_of_le hcon with hlt | heq
    · have h := Work.OddEnvelope.profileX_strictAntiOn hσ₁pos (by norm_num : (0 : ℝ) < 2 / 3) hlt
      rw [hprofσ₁] at h
      linarith
    · rw [heq] at hprofσ₁
      linarith
  have hσ₁_le : σ₁ ≤ 1 := by
    by_contra hcon
    push Not at hcon
    have h := Work.OddEnvelope.profileX_strictAntiOn (by norm_num : (0 : ℝ) < 1) hσ₁pos hcon
    rw [hprofσ₁] at h
    -- `h : profileX 1 < X σ`
    have hξge : Work.OddEnvelope.profileX 1 ≤ X σ := by
      have hX1 : X 1 = Work.OddEnvelope.profileX 1 :=
        H.x_tail 1 (by norm_num [Work.OddEnvelope.tau])
      rcases lt_or_eq_of_le hσhi with hlt | heq
      · have h2 := H.toChordCurve_x.strictAntiOn hσpos (by norm_num : (0 : ℝ) < 1) hlt
        rw [hX1] at h2
        exact le_of_lt h2
      · rw [heq, hX1]
    linarith
  -- ### the jet data at `σ`
  have hd0 : |X σ - Work.OddEnvelope.profileX σ| ≤ η := (hclose σ hσlo hσhi).1
  have hd1 : |deriv X σ - deriv Work.OddEnvelope.profileX σ| ≤ η := (hclose σ hσlo hσhi).2.1
  have hd2 : |deriv (deriv X) σ - deriv (deriv Work.OddEnvelope.profileX) σ| ≤ η :=
    (hclose σ hσlo hσhi).2.2
  have hp1 : |Work.OddEnvelope.profileX σ| ≤ 1 := by
    rw [abs_of_pos (Work.OddEnvelope.profileX_pos σ)]
    exact le_of_lt (Work.OddEnvelope.profileX_lt_one hσpos)
  have hp2 : |deriv (deriv Work.OddEnvelope.profileX) σ| ≤ 1 := WideAux.deriv2_le_one hσI.1 hσI.2
  have hpX : |deriv (deriv Work.OddEnvelope.profileX) σ - deriv (deriv X) σ| ≤ η := by
    rw [abs_sub_comm]; exact hd2
  have hX2' : |deriv (deriv X) σ| ≤ 3 / 2 := by
    have h := abs_add_le (deriv (deriv X) σ - deriv (deriv Work.OddEnvelope.profileX) σ)
      (deriv (deriv Work.OddEnvelope.profileX) σ)
    have h'' : |deriv (deriv X) σ|
        ≤ |deriv (deriv X) σ - deriv (deriv Work.OddEnvelope.profileX) σ|
          + |deriv (deriv Work.OddEnvelope.profileX) σ| := by simpa using h
    linarith [h'', hd2, hp2, hη100]
  have hv₀lo : 1 / 3 ≤ |deriv Work.OddEnvelope.profileX σ| := wideProfileXOneThird σ hσI.1 hσI.2
  have hv₀hi : |deriv Work.OddEnvelope.profileX σ| ≤ 1 := profileX_deriv_abs_le_one hσpos
  have hvlo : 1 / 4 ≤ |deriv X σ| := by
    have h := abs_add_le (deriv Work.OddEnvelope.profileX σ - deriv X σ) (deriv X σ)
    have h'' : |deriv Work.OddEnvelope.profileX σ|
        ≤ |deriv Work.OddEnvelope.profileX σ - deriv X σ| + |deriv X σ| := by simpa using h
    have h3 : |deriv Work.OddEnvelope.profileX σ - deriv X σ| ≤ η := by
      rw [abs_sub_comm]; exact hd1
    linarith [h'', h3, hv₀lo, hη100]
  have hvhi : |deriv X σ| ≤ 3 / 2 := by
    have h := abs_add_le (deriv X σ - deriv Work.OddEnvelope.profileX σ)
      (deriv Work.OddEnvelope.profileX σ)
    have h'' : |deriv X σ|
        ≤ |deriv X σ - deriv Work.OddEnvelope.profileX σ|
          + |deriv Work.OddEnvelope.profileX σ| := by simpa using h
    linarith [h'', hd1, hv₀hi, hη100]
  have hξp : |X σ - Work.OddEnvelope.profileX σ| ≤ η := hd0
  -- ### the slope difference
  have hσdiff : |σ - σ₁| ≤ 3 * η := by
    have h := WideAux.reverse_lipschitz hσI.1 hσI.2 (le_of_lt hσ₁_gt) hσ₁_le
    have h2 : |Work.OddEnvelope.profileX σ - Work.OddEnvelope.profileX σ₁| ≤ η := by
      rw [hprofσ₁, abs_sub_comm]
      exact hd0
    linarith [h, h2]
  -- ### the semicircle identity for `σ₁`
  have hHσ₁ : X σ / deriv Work.OddEnvelope.profileX σ₁ + σ₁ = -1 / σ₁ := by
    have hd : deriv Work.OddEnvelope.profileX σ₁ = -σ₁ * (X σ) ^ 3 := by
      rw [(Work.OddEnvelope.Close.profileX_deriv_formulas σ₁).1, hprofσ₁]
    have hsq : σ₁ ^ 2 * (X σ) ^ 2 = 1 - (X σ) ^ 2 := by
      rw [← mul_pow, hσ₁ξ, Real.sq_sqrt (le_of_lt hξ2pos)]
    rw [hd]
    field_simp
    nlinarith [hsq]
  have hH : |(X σ / deriv Work.OddEnvelope.profileX σ + σ) + 1 / σ₁| ≤ 10 * |σ - σ₁| := by
    have h := WideAux.gapH_lipschitz hxabs hσI.1 hσI.2 (le_of_lt hσ₁_gt) hσ₁_le
    rw [hHσ₁] at h
    have h' : (X σ / deriv Work.OddEnvelope.profileX σ + σ) - (-1 / σ₁)
        = (X σ / deriv Work.OddEnvelope.profileX σ + σ) + 1 / σ₁ := by ring
    rwa [h'] at h
  -- ### estimate 1: the values
  have hval1 : |Work.OddEnvelope.envelopeProfile h X Y (-(X σ))
      - Work.OddEnvelope.semicircle (-(X σ))| ≤ 1000000 * (η + ε) := by
    have ht : (-(X σ)) ∈ Set.Ioo (-1 : ℝ) 0 := ⟨by linarith, by linarith⟩
    have hval_slope : Work.OddEnvelope.envelopeProfile h X Y (-(X σ)) = σ * (X σ) - h σ := by
      rw [Work.OddEnvelope.envelopeProfile_of_neg ht, Work.OddEnvelope.envelopeLeft]
      have hsl : Work.OddEnvelope.slopeLeft X (-(X σ)) = σ := by
        rw [Work.OddEnvelope.slopeLeft, neg_neg]
        exact (slopeRight_eq_of_chord H.toChordCurve_x hσpos rfl).symm
      rw [hsl]; ring
    have hsem_val : Work.OddEnvelope.semicircle (-(X σ)) = σ₁ * (X σ) := by
      rw [Work.OddEnvelope.semicircle_even, Work.OddEnvelope.semicircle, ← hσ₁ξ]
    rw [hval_slope, hsem_val]
    have h := gap_value_dev (a := σ) (b := σ₁) (ξ := X σ) (w := h σ) hσdiff hxabs hh.1
    linarith [h, hη0, hε0]
  -- ### estimate 2: the first derivatives
  have hder1 : |deriv (Work.OddEnvelope.envelopeProfile h X Y) (-(X σ))
      - deriv Work.OddEnvelope.semicircle (-(X σ))| ≤ 1000000 * (η + ε) := by
    have ht : (-(X σ)) ∈ Set.Ioo (-1 : ℝ) 0 := ⟨by linarith, by linarith⟩
    have hprof_deriv : deriv (Work.OddEnvelope.envelopeProfile h X Y) (-(X σ))
        = -(X σ + σ * deriv X σ - deriv h σ) / deriv X σ := by
      rw [Work.OddEnvelope.deriv_envelopeProfile_of_neg H ht]
      have hsl : Work.OddEnvelope.slopeRight X (-(-(X σ))) = σ := by
        rw [neg_neg]
        exact (slopeRight_eq_of_chord H.toChordCurve_x hσpos rfl).symm
      rw [hsl, Work.OddEnvelope.kSlope, Work.OddEnvelope.deriv_negH]
      ring_nf
    have hsemi_deriv : deriv Work.OddEnvelope.semicircle (-(X σ)) = 1 / σ₁ := by
      rw [Work.OddEnvelope.Semicircle.deriv_semicircle ⟨by linarith, by linarith⟩, neg_neg,
        Work.OddEnvelope.semicircle_even, Work.OddEnvelope.semicircle, ← hσ₁ξ]
      field_simp
    rw [hprof_deriv, hsemi_deriv]
    have heq : (-(X σ + σ * deriv X σ - deriv h σ)) / deriv X σ - 1 / σ₁
        = -(X σ + σ * deriv X σ) / deriv X σ + deriv h σ / deriv X σ - 1 / σ₁ := by
      field_simp; ring
    rw [heq]
    have h := gap_deriv_dev (a := σ) (b := σ₁) (ξ := X σ) (v := deriv X σ)
      (v₀ := deriv Work.OddEnvelope.profileX σ) (w := deriv h σ) hη0 hε0 hH hσdiff hxabs
      hd1 hvlo hv₀lo hh.2.1
    linarith [h, hη0, hε0]
  -- ### estimate 3: the second derivatives
  have hder2 : |deriv (deriv (Work.OddEnvelope.envelopeProfile h X Y)) (-(X σ))
      - deriv (deriv Work.OddEnvelope.semicircle) (-(X σ))| ≤ 1000000 * (η + ε) := by
    have hprof2 : deriv (deriv (Work.OddEnvelope.envelopeProfile h X Y)) (-(X σ))
        = (2 * (deriv X σ) ^ 2 - X σ * deriv (deriv X) σ - deriv (deriv h) σ * deriv X σ
            + deriv h σ * deriv (deriv X) σ) / (deriv X σ) ^ 3 := by
      have hσdef' : σ = Work.OddEnvelope.slopeRight X (X σ) :=
        slopeRight_eq_of_chord H.toChordCurve_x hσpos rfl
      rw [deriv_deriv_envelopeProfile_of_neg H hxI hσdef']
    have hsemi2 : deriv (deriv Work.OddEnvelope.semicircle) (-(X σ)) = gapPsi0 σ₁ := by
      rw [deriv_deriv_semicircle ⟨by linarith, by linarith⟩]
      have hL : Work.OddEnvelope.semicircle (-(X σ)) = σ₁ * (X σ) := by
        rw [Work.OddEnvelope.semicircle_even, Work.OddEnvelope.semicircle, ← hσ₁ξ]
      have hR : gapPsi0 σ₁ = -(1 / (σ₁ * (X σ)) ^ 3) := by simp only [gapPsi0, hprofσ₁]
      rw [hL, hR]
    rw [hprof2, hsemi2]
    have hdata : |(2 * (deriv X σ) ^ 2 - deriv (deriv h) σ * deriv X σ
          - (X σ - deriv h σ) * deriv (deriv X) σ) / (deriv X σ) ^ 3
        - (2 * (deriv Work.OddEnvelope.profileX σ) ^ 2
            - Work.OddEnvelope.profileX σ * deriv (deriv Work.OddEnvelope.profileX) σ)
          / (deriv Work.OddEnvelope.profileX σ) ^ 3| ≤ 40000 * (η + ε) :=
      gap_second_dev (v := deriv X σ) (v₀ := deriv Work.OddEnvelope.profileX σ)
        (X2 := deriv (deriv X) σ) (p2 := deriv (deriv Work.OddEnvelope.profileX) σ)
        (ξ := X σ) (p := Work.OddEnvelope.profileX σ) (h₁ := deriv h σ)
        (h₂ := deriv (deriv h) σ) hη0 hε0 hvlo hvhi hv₀lo hv₀hi hd1 hX2' hp2 hp1 hξp hpX
        hh.2.1 hh.2.2
    have hpsi : |(2 * (deriv X σ) ^ 2 - X σ * deriv (deriv X) σ
          - deriv (deriv h) σ * deriv X σ + deriv h σ * deriv (deriv X) σ)
          / (deriv X σ) ^ 3 - gapPsi0 σ| ≤ 40000 * (η + ε) := by
      rw [← profileX_slope_second hσpos]
      have heq : (2 * (deriv X σ) ^ 2 - deriv (deriv h) σ * deriv X σ
            - (X σ - deriv h σ) * deriv (deriv X) σ)
          = (2 * (deriv X σ) ^ 2 - X σ * deriv (deriv X) σ - deriv (deriv h) σ * deriv X σ
              + deriv h σ * deriv (deriv X) σ) := by ring
      rw [← heq]
      exact hdata
    have hlip : |gapPsi0 σ - gapPsi0 σ₁| ≤ 200 * |σ - σ₁| :=
      WideAux.gapPsi0_lipschitz hσI.1 hσI.2 (le_of_lt hσ₁_gt) hσ₁_le
    have hsplit : (2 * (deriv X σ) ^ 2 - X σ * deriv (deriv X) σ - deriv (deriv h) σ * deriv X σ
          + deriv h σ * deriv (deriv X) σ) / (deriv X σ) ^ 3 - gapPsi0 σ₁
        = (((2 * (deriv X σ) ^ 2 - X σ * deriv (deriv X) σ - deriv (deriv h) σ * deriv X σ
              + deriv h σ * deriv (deriv X) σ) / (deriv X σ) ^ 3 - gapPsi0 σ)
            + (gapPsi0 σ - gapPsi0 σ₁)) := by ring
    rw [hsplit]
    have hsum := abs_add_le ((2 * (deriv X σ) ^ 2 - X σ * deriv (deriv X) σ
        - deriv (deriv h) σ * deriv X σ + deriv h σ * deriv (deriv X) σ)
        / (deriv X σ) ^ 3 - gapPsi0 σ) (gapPsi0 σ - gapPsi0 σ₁)
    linarith [hsum, hpsi, hlip, hσdiff, hη0, hε0]
  -- ### dispatch on `k ≤ 2`
  have hk' : k = 0 ∨ k = 1 ∨ k = 2 := by omega
  rcases hk' with rfl | rfl | rfl
  · simpa [iteratedDeriv_zero] using hval1
  · simpa [iteratedDeriv_one] using hder1
  · have e1 : iteratedDeriv 2 (Work.OddEnvelope.envelopeProfile h X Y)
        = deriv (deriv (Work.OddEnvelope.envelopeProfile h X Y)) := by
      rw [show (2 : ℕ) = 1 + 1 by norm_num, iteratedDeriv_succ, iteratedDeriv_one]
    have e2 : iteratedDeriv 2 Work.OddEnvelope.semicircle
        = deriv (deriv Work.OddEnvelope.semicircle) := by
      rw [show (2 : ℕ) = 1 + 1 by norm_num, iteratedDeriv_succ, iteratedDeriv_one]
    rw [e1, e2]
    exact hder2


end Work.OddVolterra.Free
