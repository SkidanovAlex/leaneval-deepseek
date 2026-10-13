/-
# `Work.FTS.PhiStar.Honesty.rgA_value_bound` — the value bound on the forward primitive

`rgA α m c z = ∫_0^z c t · t^{q-1} dt` with `q = rgQ α m = (2m+5)/α > 0`.  If the source is
dominated near `0` by `ε·t^{3/2}` — `|c t| ≤ ε·t^{3/2}` for `0 < t ≤ δ` — then the integrand is
dominated by `ε·t^{q+1/2}`, whose primitive vanishing at `0` is `ε·z^{q+3/2}/(q+3/2)`.  Hence

  `|rgA α m c z| ≤ ε·z^{q+3/2}/(q+3/2)`   for `0 < z ≤ δ`,

with the *sharp* constant `1/(q+3/2)`.  The only arithmetic input is `q > 0` (so that both
`t^{q+1/2}` is integrable at `0` and the denominator `q+3/2` is positive).
-/
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Submission.Work.FTS.EllExist.RadGreenDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real
open MeasureTheory Set Filter

namespace Work.FTS.PhiStar.Honesty

set_option autoImplicit false

local notation "rgQ" => Work.FTS.EllExist.rgQ
local notation "rgF1" => Work.FTS.EllExist.rgF1

/-- **Interval-integral comparison with a pointwise majorant.**  If `|f| ≤ g` on `Ioc a b` and
`g` is interval integrable there, then `|∫_a^b f| ≤ ∫_a^b g`. -/
private theorem abs_intervalIntegral_le {f g : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (h : ∀ t ∈ Set.Ioc a b, |f t| ≤ g t) (hg : IntervalIntegrable g volume a b) :
    |∫ t in a..b, f t| ≤ ∫ t in a..b, g t := by
  have h' : ∀ᵐ t ∂volume, t ∈ Set.Ioc a b → ‖f t‖ ≤ g t :=
    Eventually.of_forall fun t ht => by simpa [Real.norm_eq_abs] using h t ht
  have h2 := intervalIntegral.norm_integral_le_of_norm_le hab h' hg
  simpa [Real.norm_eq_abs] using h2

theorem rgA_value_bound {α : ℝ} {m : ℕ} {c : ℝ → ℝ} {ε δ : ℝ}
    (hα : 0 < α) (hδ : 0 < δ) (hε : 0 ≤ ε)
    (hvy : ∀ t : ℝ, 0 < t → t ≤ δ → |c t| ≤ ε * t ^ ((3 : ℝ) / 2)) :
    ∀ z : ℝ, 0 < z → z ≤ δ →
      |Work.FTS.EllExist.rgA α m c z|
        ≤ ε * z ^ (Work.FTS.EllExist.rgQ α m + 3 / 2) / (Work.FTS.EllExist.rgQ α m + 3 / 2) := by
  intro z hz hzδ
  have hq : 0 < rgQ α m := Work.FTS.EllExist.rgQ_pos hα m
  have hq12 : (-1 : ℝ) < rgQ α m + 1 / 2 := by linarith
  have hq32 : rgQ α m + 3 / 2 ≠ 0 := by positivity
  -- the pointwise domination of the integrand by `ε · t^{q+1/2}`
  have hpt : ∀ t ∈ Set.Ioc (0 : ℝ) z, |rgF1 α m c t| ≤ ε * t ^ (rgQ α m + 1 / 2) := by
    intro t ht
    have ht0 : 0 < t := ht.1
    have htz : t ≤ δ := le_trans ht.2 hzδ
    have hc : |c t| ≤ ε * t ^ ((3 : ℝ) / 2) := hvy t ht0 htz
    have hp1 : 0 < t ^ (rgQ α m - 1) := Real.rpow_pos_of_pos ht0 _
    simp only [Work.FTS.EllExist.rgF1]
    rw [abs_mul, abs_of_pos hp1]
    calc |c t| * t ^ (rgQ α m - 1) ≤ (ε * t ^ ((3 : ℝ) / 2)) * t ^ (rgQ α m - 1) :=
          mul_le_mul_of_nonneg_right hc (le_of_lt hp1)
      _ = ε * t ^ (rgQ α m + 1 / 2) := by
          rw [show ε * t ^ ((3 : ℝ) / 2) * t ^ (rgQ α m - 1)
                = ε * (t ^ ((3 : ℝ) / 2) * t ^ (rgQ α m - 1)) from by ring,
            ← Real.rpow_add ht0,
            show (3 : ℝ) / 2 + (rgQ α m - 1) = rgQ α m + 1 / 2 from by ring]
  -- the majorant is interval integrable
  have hII : IntervalIntegrable (fun t : ℝ => ε * t ^ (rgQ α m + 1 / 2)) volume (0 : ℝ) z :=
    (intervalIntegral.intervalIntegrable_rpow' hq12).const_mul ε
  have hstep : |∫ t in (0 : ℝ)..z, rgF1 α m c t| ≤ ∫ t in (0 : ℝ)..z, ε * t ^ (rgQ α m + 1 / 2) :=
    abs_intervalIntegral_le hz.le hpt hII
  -- the explicit value of the majorant integral
  have hval : ∫ t in (0 : ℝ)..z, ε * t ^ (rgQ α m + 1 / 2)
      = ε * z ^ (rgQ α m + 3 / 2) / (rgQ α m + 3 / 2) := by
    rw [intervalIntegral.integral_const_mul]
    have h := integral_rpow (a := (0 : ℝ)) (b := z) (r := rgQ α m + 1 / 2) (Or.inl hq12)
    rw [show rgQ α m + 1 / 2 + 1 = rgQ α m + 3 / 2 from by ring,
      Real.zero_rpow hq32] at h
    rw [h]
    ring
  rw [Work.FTS.EllExist.rgA]
  exact le_trans hstep (le_of_eq hval)

end Work.FTS.PhiStar.Honesty
