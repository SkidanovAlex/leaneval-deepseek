import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.FTS.PhiStar.Series.BmodeBase
import Submission.Work.FTS.PhiStar.Gegenbauer.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology BigOperators
open MeasureTheory Set Filter

namespace Work.FTS.PhiStar.Series

local notation "Iθ" => Work.Spaces.Iθ
local notation "eF" => Work.FTS.PhiStar.Gegenbauer.eFam

/-! # The commutator term of the cutoff argument

Let `χ δ` be a cutoff family (`1` on `[δ, π/2-δ]`, vanishing outside `(δ/2, π/2-δ/2)`, with
`|(χ δ)'| ≤ K₁/δ`, `|(χ δ)''| ≤ K₂/δ²` and `(χ δ)' = (χ δ)'' = 0` *outside the two layers*
`(δ/2,δ) ∪ (π/2-δ, π/2-δ/2)`).  For a function `ψ` that is small on a pair of boundary
layers, the commutator integral

`∫_{Iθ} ψ · (-(χ'' e) - 2 (χ' e') + tan θ · χ' · e) · cos θ`

tends to `0` along `δ = 1/(n+1)`.  This is the estimate that lets the cutoff be removed from
the weak identity `λ_m ∫ ψ χ e cos = ∫ Γ̄ χ e cos` (`BmodeCoeff.coeff_eq`).

The integrand vanishes outside the layers (so only an interval of total length `2δ` matters),
and on the layers each of the three terms gains a factor `δ` (from `e = eFam m` vanishing at
the endpoints and from `sin θ cos²θ ≤ δ` resp. `cos θ ≤ 1`), which cancels the `1/δ`,
`1/δ²` growth of the derivatives of the cutoff. -/

/-! ## The pointwise bound for the bracket -/

/-- Pointwise bound for `(χ'' e + 2 χ' e' - tan θ χ' e) · cos θ`.  The two summands coming
from `χ''` and `χ'` are estimated with `e · cos` and `e' · cos`; the `tan`-summand uses
`|tan θ cos θ| ≤ 1` together with `|e θ| ≤ A cos θ`. -/
theorem bracket_cos_bound {χ : ℝ → ℝ → ℝ} {e de : ℝ → ℝ} {K₁ K₂ A B δ θ : ℝ}
    (hd : |deriv (χ δ) θ| ≤ K₁ / δ) (hdd : |deriv (deriv (χ δ)) θ| ≤ K₂ / δ ^ 2)
    (he : |e θ| ≤ A * Real.cos θ)
    (he2 : |e θ * Real.cos θ| ≤ A * Real.sin θ * Real.cos θ ^ 2)
    (hde : |de θ * Real.cos θ| ≤ B + A) :
    |(-(deriv (deriv (χ δ)) θ * e θ) - 2 * (deriv (χ δ) θ * de θ)
        + Real.tan θ * deriv (χ δ) θ * e θ) * Real.cos θ|
      ≤ (K₂ / δ ^ 2) * (A * Real.sin θ * Real.cos θ ^ 2) + 2 * (K₁ / δ) * (B + A)
        + (K₁ / δ) * (A * Real.cos θ) := by
  have hdd0 : 0 ≤ K₂ / δ ^ 2 := le_trans (abs_nonneg _) hdd
  have hd0 : 0 ≤ K₁ / δ := le_trans (abs_nonneg _) hd
  have h1 : |deriv (deriv (χ δ)) θ * e θ * Real.cos θ|
      ≤ (K₂ / δ ^ 2) * (A * Real.sin θ * Real.cos θ ^ 2) := by
    rw [mul_assoc, abs_mul]
    exact mul_le_mul hdd he2 (abs_nonneg _) hdd0
  have h2 : |deriv (χ δ) θ * de θ * Real.cos θ| ≤ (K₁ / δ) * (B + A) := by
    rw [mul_assoc, abs_mul]
    exact mul_le_mul hd hde (abs_nonneg _) hd0
  have htan : |Real.tan θ * Real.cos θ| ≤ 1 := by
    have h := abs_tan_mul_cos_le (1 : ℝ) θ
    rwa [mul_one, abs_one] at h
  have h3 : |Real.tan θ * deriv (χ δ) θ * e θ * Real.cos θ|
      ≤ (K₁ / δ) * (A * Real.cos θ) := by
    have hstep : Real.tan θ * deriv (χ δ) θ * e θ * Real.cos θ
        = (Real.tan θ * Real.cos θ) * (deriv (χ δ) θ * e θ) := by ring
    rw [hstep, abs_mul]
    have hY : |deriv (χ δ) θ * e θ| ≤ (K₁ / δ) * (A * Real.cos θ) := by
      rw [abs_mul]
      exact mul_le_mul hd he (abs_nonneg _) hd0
    calc |Real.tan θ * Real.cos θ| * |deriv (χ δ) θ * e θ|
        ≤ 1 * ((K₁ / δ) * (A * Real.cos θ)) :=
          mul_le_mul htan hY (abs_nonneg _) (by norm_num)
      _ = (K₁ / δ) * (A * Real.cos θ) := one_mul _
  have hsplit : (-(deriv (deriv (χ δ)) θ * e θ) - 2 * (deriv (χ δ) θ * de θ)
        + Real.tan θ * deriv (χ δ) θ * e θ) * Real.cos θ
      = -(deriv (deriv (χ δ)) θ * e θ * Real.cos θ)
        - 2 * (deriv (χ δ) θ * de θ * Real.cos θ)
        + Real.tan θ * deriv (χ δ) θ * e θ * Real.cos θ := by ring
  rw [hsplit]
  have ha : |-(deriv (deriv (χ δ)) θ * e θ * Real.cos θ)|
      + |2 * (deriv (χ δ) θ * de θ * Real.cos θ)|
      ≤ (K₂ / δ ^ 2) * (A * Real.sin θ * Real.cos θ ^ 2) + 2 * ((K₁ / δ) * (B + A)) := by
    have hb : |2 * (deriv (χ δ) θ * de θ * Real.cos θ)| ≤ 2 * ((K₁ / δ) * (B + A)) := by
      rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
      exact mul_le_mul_of_nonneg_left h2 (by norm_num)
    exact add_le_add (by rwa [abs_neg]) hb
  calc |-(deriv (deriv (χ δ)) θ * e θ * Real.cos θ)
        - 2 * (deriv (χ δ) θ * de θ * Real.cos θ)
        + Real.tan θ * deriv (χ δ) θ * e θ * Real.cos θ|
      ≤ |-(deriv (deriv (χ δ)) θ * e θ * Real.cos θ)
          - 2 * (deriv (χ δ) θ * de θ * Real.cos θ)|
        + |Real.tan θ * deriv (χ δ) θ * e θ * Real.cos θ| := abs_add_le _ _
    _ ≤ (|-(deriv (deriv (χ δ)) θ * e θ * Real.cos θ)|
          + |2 * (deriv (χ δ) θ * de θ * Real.cos θ)|)
        + |Real.tan θ * deriv (χ δ) θ * e θ * Real.cos θ| :=
        add_le_add (abs_sub _ _) le_rfl
    _ ≤ ((K₂ / δ ^ 2) * (A * Real.sin θ * Real.cos θ ^ 2) + 2 * ((K₁ / δ) * (B + A)))
        + (K₁ / δ) * (A * Real.cos θ) := add_le_add ha h3
    _ = (K₂ / δ ^ 2) * (A * Real.sin θ * Real.cos θ ^ 2) + 2 * (K₁ / δ) * (B + A)
        + (K₁ / δ) * (A * Real.cos θ) := by ring

/-! ## The derivative of `eFam m` against `cos` -/

/-- `|(eFam m)' θ · cos θ| ≤ B + A` on `Iθ`, from the bound `B` on the derivative of the
product `eFam m · cos` and the bound `A` on `eFam m`. -/
theorem efam_deriv_cos_le (m : ℕ) {A B : ℝ} (hA : 0 < A)
    (hAe : ∀ θ ∈ Iθ, |eF m θ| ≤ A * Real.cos θ)
    (hBe : ∀ θ : ℝ, |deriv (fun t : ℝ => eF m t * Real.cos t) θ| ≤ B) :
    ∀ θ ∈ Iθ, |deriv (eF m) θ * Real.cos θ| ≤ B + A := by
  intro θ hθ
  have hd : HasDerivAt (eF m) (deriv (eF m) θ) θ :=
    (((contDiff_eF m).differentiable (by norm_num)).differentiableAt).hasDerivAt
  have hcos : HasDerivAt Real.cos (-Real.sin θ) θ := Real.hasDerivAt_cos θ
  have h1 : deriv (fun t : ℝ => eF m t * Real.cos t) θ
      = deriv (eF m) θ * Real.cos θ - eF m θ * Real.sin θ := by
    rw [show (fun t : ℝ => eF m t * Real.cos t) = eF m * Real.cos from rfl,
      deriv_mul hd.differentiableAt hcos.differentiableAt, hd.deriv, hcos.deriv]
    ring
  have h2 : deriv (eF m) θ * Real.cos θ
      = deriv (fun t : ℝ => eF m t * Real.cos t) θ + eF m θ * Real.sin θ := by
    linarith [h1]
  rw [h2]
  have hcos1 : Real.cos θ ≤ 1 := Real.cos_le_one θ
  have hs1 : |Real.sin θ| ≤ 1 := abs_le.mpr (Real.sin_mem_Icc θ)
  have hA0 : 0 ≤ A * Real.cos θ := le_trans (abs_nonneg _) (hAe θ hθ)
  have h3 : |eF m θ * Real.sin θ| ≤ A := by
    rw [abs_mul]
    calc |eF m θ| * |Real.sin θ| ≤ (A * Real.cos θ) * 1 :=
          mul_le_mul (hAe θ hθ) hs1 (abs_nonneg _) hA0
      _ = A * Real.cos θ := by ring
      _ ≤ A * 1 := mul_le_mul_of_nonneg_left hcos1 hA.le
      _ = A := mul_one A
  calc |deriv (fun t : ℝ => eF m t * Real.cos t) θ + eF m θ * Real.sin θ|
      ≤ |deriv (fun t : ℝ => eF m t * Real.cos t) θ| + |eF m θ * Real.sin θ| :=
        abs_add_le _ _
    _ ≤ B + A := add_le_add (hBe θ) h3

/-! ## The layers -/

private lemma layer_sin_cos_sq_le_left {δ θ : ℝ} (hδ4 : δ ≤ 1 / 4) (h1 : δ / 2 < θ)
    (h2 : θ < δ) : Real.sin θ * Real.cos θ ^ 2 ≤ δ := by
  have hθ0 : 0 < θ := by linarith
  have hs : Real.sin θ ≤ θ := Real.sin_le hθ0.le
  have hsnn : 0 ≤ Real.sin θ :=
    Real.sin_nonneg_of_mem_Icc ⟨hθ0.le, by linarith [h2, hδ4, Real.pi_gt_three]⟩
  have hc2 : Real.cos θ ^ 2 ≤ 1 := by
    nlinarith [sq_nonneg (Real.sin θ), Real.sin_sq_add_cos_sq θ]
  nlinarith [hs, hsnn, hc2, h2]

private lemma layer_sin_cos_sq_le_right {δ θ : ℝ} (hδ4 : δ ≤ 1 / 4)
    (h1 : Real.pi / 2 - δ < θ) (h2 : θ < Real.pi / 2 - δ / 2) :
    Real.sin θ * Real.cos θ ^ 2 ≤ δ := by
  have hδpos : 0 < δ := by linarith [h1, h2]
  have hθ0 : 0 < θ := by linarith [h1, hδ4, Real.pi_gt_three]
  have hθpi : θ < Real.pi / 2 := by linarith [h2, hδ4]
  have hc0 : 0 ≤ Real.cos θ :=
    le_of_lt (Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hθpi⟩)
  have hc1 : Real.cos θ ≤ 1 := Real.cos_le_one θ
  have hcle : Real.cos θ ≤ Real.pi / 2 - θ := by
    have h := Real.sin_le (show (0 : ℝ) ≤ Real.pi / 2 - θ by linarith)
    rwa [Real.sin_pi_div_two_sub] at h
  have hs1 : Real.sin θ ≤ 1 := Real.sin_le_one θ
  have hsq : Real.sin θ * Real.cos θ ^ 2 ≤ Real.cos θ ^ 2 := by nlinarith [hs1, hc0]
  have hsq2 : Real.cos θ ^ 2 ≤ Real.cos θ := by nlinarith [hc0, hc1]
  linarith

/-! ## The limit -/

theorem bmcut_commutator_tendsto (χ : ℝ → ℝ → ℝ) (K₁ K₂ A B : ℝ)
    (hK₁ : 0 < K₁) (hK₂ : 0 < K₂) (hA : 0 < A) (hB : 0 < B)
    (hχd : ∀ δ : ℝ, 0 < δ → ∀ θ : ℝ, |deriv (χ δ) θ| ≤ K₁ / δ)
    (hχdd : ∀ δ : ℝ, 0 < δ → ∀ θ : ℝ, |deriv (deriv (χ δ)) θ| ≤ K₂ / δ ^ 2)
    (hχsupp : ∀ δ : ℝ, 0 < δ → ∀ θ : ℝ,
        (θ ∉ Set.Ioo (δ / 2) δ ∧ θ ∉ Set.Ioo (Real.pi / 2 - δ) (Real.pi / 2 - δ / 2)) →
        deriv (χ δ) θ = 0 ∧ deriv (deriv (χ δ)) θ = 0)
    (m : ℕ)
    (hAe : ∀ θ ∈ Iθ, |eF m θ| ≤ A * Real.cos θ)
    (hAe2 : ∀ θ ∈ Iθ, |eF m θ * Real.cos θ| ≤ A * Real.sin θ * Real.cos θ ^ 2)
    (hBe : ∀ θ : ℝ, |deriv (fun t : ℝ => eF m t * Real.cos t) θ| ≤ B)
    (ψ : ℝ → ℝ)
    (hsmall : ∀ ε : ℝ, 0 < ε → ∃ ρ : ℝ, 0 < ρ ∧ ∀ θ : ℝ,
        (θ ∈ Set.Icc 0 ρ ∨ θ ∈ Set.Icc (Real.pi / 2 - ρ) (Real.pi / 2)) → |ψ θ| < ε) :
    Filter.Tendsto (fun n : ℕ => ∫ θ in Iθ, ψ θ *
        (-(deriv (deriv (χ (1 / ((n : ℝ) + 1)))) θ * eF m θ)
          - 2 * (deriv (χ (1 / ((n : ℝ) + 1))) θ * deriv (eF m) θ)
          + Real.tan θ * deriv (χ (1 / ((n : ℝ) + 1))) θ * eF m θ) * Real.cos θ)
      Filter.atTop (nhds 0) := by
  set Cp : ℝ := K₂ * A + 2 * K₁ * (B + A) + K₁ * A with hCpdef
  have hCp0 : 0 ≤ Cp := by rw [hCpdef]; positivity
  refine Metric.tendsto_atTop.mpr (fun ε hε => ?_)
  set P : ℝ := ε / (2 * (Cp + 1)) with hPdef
  have hPpos : 0 < P := by rw [hPdef]; positivity
  obtain ⟨ρ, hρpos, hρ⟩ := hsmall P hPpos
  have hρmin : 0 < min ρ (1 / 4 : ℝ) := lt_min hρpos (by norm_num)
  obtain ⟨N, hN⟩ := eventually_atTop.mp
    ((tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).eventually
      (eventually_le_nhds hρmin))
  refine ⟨N, fun n hn => ?_⟩
  set δ : ℝ := 1 / ((n : ℝ) + 1) with hδdef
  have hδpos : 0 < δ := by rw [hδdef]; positivity
  have hδle : δ ≤ min ρ (1 / 4 : ℝ) := hN n hn
  have hδρ : δ ≤ ρ := le_trans hδle (min_le_left _ _)
  have hδ4 : δ ≤ 1 / 4 := le_trans hδle (min_le_right _ _)
  set L : Set ℝ := Set.Ioo (δ / 2) δ ∪ Set.Ioo (Real.pi / 2 - δ) (Real.pi / 2 - δ / 2)
    with hLdef
  set F : ℝ → ℝ := fun θ => ψ θ *
    (-(deriv (deriv (χ δ)) θ * eF m θ)
      - 2 * (deriv (χ δ) θ * deriv (eF m) θ)
      + Real.tan θ * deriv (χ δ) θ * eF m θ) * Real.cos θ with hFdef
  have hde : ∀ θ ∈ Iθ, |deriv (eF m) θ * Real.cos θ| ≤ B + A :=
    efam_deriv_cos_le m hA hAe hBe
  have hlayer : ∀ θ ∈ L, |F θ| ≤ P * Cp / δ := by
    intro θ hθL
    have hθL' := hθL
    rw [hLdef] at hθL
    have hθI : θ ∈ Iθ := by
      rcases hθL with h | h
      · exact ⟨by linarith [h.1], by linarith [h.2, hδ4, Real.pi_gt_three]⟩
      · exact ⟨by linarith [h.1, hδ4, Real.pi_gt_three], by linarith [h.2, hδ4]⟩
    have hψb : |ψ θ| < P := by
      refine hρ θ ?_
      rcases hθL with h | h
      · exact Or.inl ⟨by linarith [h.1], le_trans h.2.le hδρ⟩
      · exact Or.inr ⟨by linarith [h.1, hδρ], by linarith [h.2, hδ4]⟩
    have hsc_le : Real.sin θ * Real.cos θ ^ 2 ≤ δ := by
      rcases hθL with h | h
      · exact layer_sin_cos_sq_le_left hδ4 h.1 h.2
      · exact layer_sin_cos_sq_le_right hδ4 h.1 h.2
    have hc1 : Real.cos θ ≤ 1 := Real.cos_le_one θ
    have hbr := bracket_cos_bound (χ := χ) (e := eF m) (de := deriv (eF m))
      (θ := θ) (hχd δ hδpos θ) (hχdd δ hδpos θ) (hAe θ hθI) (hAe2 θ hθI) (hde θ hθI)
    have hbr' : |(-(deriv (deriv (χ δ)) θ * eF m θ)
        - 2 * (deriv (χ δ) θ * deriv (eF m) θ)
        + Real.tan θ * deriv (χ δ) θ * eF m θ) * Real.cos θ| ≤ Cp / δ := by
      refine le_trans hbr ?_
      have hK10 : (0 : ℝ) ≤ K₁ / δ := by positivity
      have hK20 : (0 : ℝ) ≤ K₂ / δ ^ 2 := by positivity
      have e1 : (K₂ / δ ^ 2) * (A * Real.sin θ * Real.cos θ ^ 2) ≤ (K₂ / δ ^ 2) * (A * δ) :=
        mul_le_mul_of_nonneg_left (by nlinarith [hsc_le, hA]) hK20
      have e2 : (K₁ / δ) * (A * Real.cos θ) ≤ (K₁ / δ) * A :=
        mul_le_mul_of_nonneg_left (by nlinarith [hc1, hA]) hK10
      have e3 : (K₂ / δ ^ 2) * (A * δ) + 2 * (K₁ / δ) * (B + A) + (K₁ / δ) * A
          = Cp / δ := by
        rw [hCpdef]
        field_simp
      linarith [e1, e2, e3]
    show |ψ θ * (-(deriv (deriv (χ δ)) θ * eF m θ)
        - 2 * (deriv (χ δ) θ * deriv (eF m) θ)
        + Real.tan θ * deriv (χ δ) θ * eF m θ) * Real.cos θ| ≤ P * Cp / δ
    rw [show ψ θ * (-(deriv (deriv (χ δ)) θ * eF m θ)
        - 2 * (deriv (χ δ) θ * deriv (eF m) θ)
        + Real.tan θ * deriv (χ δ) θ * eF m θ) * Real.cos θ
      = ψ θ * ((-(deriv (deriv (χ δ)) θ * eF m θ)
        - 2 * (deriv (χ δ) θ * deriv (eF m) θ)
        + Real.tan θ * deriv (χ δ) θ * eF m θ) * Real.cos θ) from by ring]
    rw [abs_mul]
    calc |ψ θ| * |(-(deriv (deriv (χ δ)) θ * eF m θ)
          - 2 * (deriv (χ δ) θ * deriv (eF m) θ)
          + Real.tan θ * deriv (χ δ) θ * eF m θ) * Real.cos θ|
        ≤ P * (Cp / δ) := mul_le_mul hψb.le hbr' (abs_nonneg _) hPpos.le
      _ = P * Cp / δ := by ring
  have hzero : ∀ θ ∈ Iθ \ L, F θ = 0 := by
    intro θ hθ
    obtain ⟨hθI, hθnotL⟩ := hθ
    have h1 : θ ∉ Set.Ioo (δ / 2) δ := fun hm => hθnotL (by rw [hLdef]; exact Or.inl hm)
    have h2 : θ ∉ Set.Ioo (Real.pi / 2 - δ) (Real.pi / 2 - δ / 2) :=
      fun hm => hθnotL (by rw [hLdef]; exact Or.inr hm)
    obtain ⟨hd0, hdd0⟩ := hχsupp δ hδpos θ ⟨h1, h2⟩
    show ψ θ * (-(deriv (deriv (χ δ)) θ * eF m θ)
      - 2 * (deriv (χ δ) θ * deriv (eF m) θ)
      + Real.tan θ * deriv (χ δ) θ * eF m θ) * Real.cos θ = 0
    rw [hd0, hdd0]
    ring
  have hsub : L ⊆ Iθ := by
    intro θ hθ
    rw [hLdef] at hθ
    rcases hθ with h | h
    · exact ⟨by linarith [h.1], by linarith [h.2, hδ4, Real.pi_gt_three]⟩
    · exact ⟨by linarith [h.1, hδ4, Real.pi_gt_three], by linarith [h.2, hδ4]⟩
  have hfin : volume L < ⊤ := by
    refine lt_of_le_of_lt (measure_mono hsub) ?_
    rw [Work.Spaces.Iθ, Real.volume_Icc]
    exact ENNReal.ofReal_lt_top
  have hmeasL : volume.real L ≤ δ := by
    rw [hLdef]
    have h1 : volume.real (Set.Ioo (δ / 2) δ) ≤ δ / 2 := by
      rw [Real.volume_real_Ioo_of_le (by linarith : δ / 2 ≤ δ)]
      linarith
    have h2 : volume.real (Set.Ioo (Real.pi / 2 - δ) (Real.pi / 2 - δ / 2)) ≤ δ / 2 := by
      rw [Real.volume_real_Ioo_of_le (by linarith : Real.pi / 2 - δ ≤ Real.pi / 2 - δ / 2)]
      linarith
    have hun := MeasureTheory.measureReal_union_le (μ := (volume : Measure ℝ))
      (Set.Ioo (δ / 2) δ) (Set.Ioo (Real.pi / 2 - δ) (Real.pi / 2 - δ / 2))
    linarith
  rw [Real.dist_eq, sub_zero]
  have hsplit : (∫ θ in Iθ, F θ) = ∫ θ in L, F θ :=
    setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Iθ hsub hzero
  rw [hsplit]
  have hboundL : ∀ θ ∈ L, ‖F θ‖ ≤ P * Cp / δ := fun θ hθ => hlayer θ hθ
  calc |∫ θ in L, F θ|
      ≤ P * Cp / δ * volume.real L :=
        norm_setIntegral_le_of_norm_le_const hfin hboundL
    _ ≤ P * Cp / δ * δ := by
        refine mul_le_mul_of_nonneg_left hmeasL ?_
        rw [hCpdef]
        positivity
    _ = P * Cp := by
        rw [div_mul_cancel₀ (P * Cp) (ne_of_gt hδpos)]
    _ = ε * Cp / (2 * (Cp + 1)) := by rw [hPdef]; ring
    _ < ε := by
        rw [div_lt_iff₀ (by positivity : (0 : ℝ) < 2 * (Cp + 1))]
        nlinarith [hCp0, hε]

end Work.FTS.PhiStar.Series
