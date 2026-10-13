/-
# `Work.FTS.ClassC.rgA_growth` — growth of the forward primitive `rgA` at `+∞`

`rgA α m c z = ∫_0^z c t · t^{q-1} dt` with `q = rgQ α m = (2m+5)/α ≥ 20` for `α ≤ 1/4`
(the forward primitive of the decaying indicial branch of the radial Green function).

The decay hypothesis `|c t| ≤ K/t` (`t ≥ 1`) makes the integrand `c t·t^{q-1}` grow at most
like `K·t^{q-2}`, whose primitive is `K·z^{q-1}/(q-1)`.  The `O(1)` hypothesis on the part
`(0,1]` — integrability of `c t·t^{q-1}` there — is *not* needed quantitatively: only that the
integral over `(0,1]` is some finite number, which is absorbed into the constant `CA`.  Hence

  `|rgA α m c z| ≤ CA·z^{q-1}`   for every `z ≥ 1`.

The proof splits `∫_0^z = ∫_0^1 + ∫_1^z` (needing interval integrability on both pieces, whence
the integrability hypothesis), bounds the second piece by `K·z^{q-1}/(q-1)` via the pointwise
majorant `K·t^{q-2}`, and uses `z^{q-1} ≥ 1` to absorb the constant `|∫_0^1|` into `CA·z^{q-1}`.
-/
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Submission.Work.FTS.EllExist.RadGreenDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.ClassC

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

theorem rgA_growth {α : ℝ} (hα : 0 < α) (hα4 : α ≤ 1 / 4) (m : ℕ) {c : ℝ → ℝ}
    (hcont : ContinuousOn c (Set.Ioi 0))
    (hdec : ∃ K : ℝ, 0 < K ∧ ∀ t : ℝ, 1 ≤ t → |c t| ≤ K / t)
    (h0 : MeasureTheory.IntegrableOn (fun t => c t * t ^ ((2 * (m : ℝ) + 5) / α - 1))
      (Set.Ioo 0 1)) :
    ∃ CA : ℝ, 0 ≤ CA ∧ ∀ z : ℝ, 1 ≤ z →
      |Work.FTS.EllExist.rgA α m c z| ≤ CA * z ^ (Work.FTS.EllExist.rgQ α m - 1) := by
  obtain ⟨K, hKpos, hKdec⟩ := hdec
  -- the exponent `q - 1` is positive
  have hq1 : 1 < rgQ α m := by
    rw [Work.FTS.EllExist.rgQ, lt_div_iff₀ hα]
    have hm : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
    nlinarith
  have hqm : 0 < rgQ α m - 1 := by linarith
  have hKq : 0 ≤ K / (rgQ α m - 1) := le_of_lt (div_pos hKpos hqm)
  have h0' : MeasureTheory.IntegrableOn (rgF1 α m c) (Set.Ioo 0 1) := h0
  have hcontF : ContinuousOn (rgF1 α m c) (Set.Ioi 0) :=
    hcont.mul (continuousOn_id.rpow_const (fun t ht => Or.inl (ne_of_gt ht)))
  -- the pointwise bound on `[1,∞)` coming from `|c t| ≤ K/t`
  have hpt : ∀ t : ℝ, 1 ≤ t → |rgF1 α m c t| ≤ K * t ^ (rgQ α m - 2) := by
    intro t ht1
    have ht0 : 0 < t := lt_of_lt_of_le zero_lt_one ht1
    have hp1 : 0 < t ^ (rgQ α m - 1) := Real.rpow_pos_of_pos ht0 _
    rw [Work.FTS.EllExist.rgF1, abs_mul, abs_of_pos hp1]
    calc |c t| * t ^ (rgQ α m - 1) ≤ (K / t) * t ^ (rgQ α m - 1) :=
          mul_le_mul_of_nonneg_right (hKdec t ht1) (le_of_lt hp1)
      _ = K * t ^ (rgQ α m - 2) := by
          rw [div_eq_mul_inv, ← Real.rpow_neg_one t, mul_assoc,
            ← Real.rpow_add ht0, show (-1 : ℝ) + (rgQ α m - 1) = rgQ α m - 2 from by ring]
  refine ⟨|∫ t in (0:ℝ)..1, rgF1 α m c t| + K / (rgQ α m - 1) + 1,
      add_nonneg (add_nonneg (abs_nonneg _) hKq) zero_le_one, ?_⟩
  intro z hz1
  have hzp : 1 ≤ z ^ (rgQ α m - 1) := Real.one_le_rpow hz1 (le_of_lt hqm)
  -- interval integrability of the two pieces of the split
  have hII01 : IntervalIntegrable (rgF1 α m c) volume (0:ℝ) 1 := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (0:ℝ) ≤ 1)]
    exact h0'.congr_set_ae (MeasureTheory.Ioo_ae_eq_Ioc (μ := volume)).symm
  have hII1z : IntervalIntegrable (rgF1 α m c) volume (1:ℝ) z := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hz1]
    refine Integrable.mono' (g := fun t => K * t ^ (rgQ α m - 2)) ?_ ?_ ?_
    · exact ((intervalIntegral.intervalIntegrable_rpow' (r := rgQ α m - 2)
        (by linarith : (-1:ℝ) < rgQ α m - 2)).const_mul K).1
    · exact (hcontF.mono
        (fun t ht => lt_of_lt_of_le zero_lt_one (le_of_lt ht.1))).aestronglyMeasurable
        measurableSet_Ioc
    · filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
      exact hpt t (le_of_lt ht.1)
  -- the tail piece `∫_1^z`
  have htail : |∫ t in (1:ℝ)..z, rgF1 α m c t| ≤ K * z ^ (rgQ α m - 1) / (rgQ α m - 1) := by
    have hgII : IntervalIntegrable (fun t => K * t ^ (rgQ α m - 2)) volume (1:ℝ) z :=
      (intervalIntegral.intervalIntegrable_rpow' (r := rgQ α m - 2)
        (by linarith : (-1:ℝ) < rgQ α m - 2)).const_mul K
    have hb := abs_intervalIntegral_le hz1 (f := rgF1 α m c)
      (g := fun t => K * t ^ (rgQ α m - 2)) (fun t ht => hpt t (le_of_lt ht.1)) hgII
    have hval : ∫ t in (1:ℝ)..z, K * t ^ (rgQ α m - 2)
        = K * (z ^ (rgQ α m - 1) - 1) / (rgQ α m - 1) := by
      rw [intervalIntegral.integral_const_mul]
      have h := integral_rpow (a := (1:ℝ)) (b := z) (r := rgQ α m - 2)
        (Or.inl (by linarith : (-1:ℝ) < rgQ α m - 2))
      rw [show rgQ α m - 2 + 1 = rgQ α m - 1 from by ring, Real.one_rpow] at h
      rw [h]
      ring
    calc |∫ t in (1:ℝ)..z, rgF1 α m c t| ≤ ∫ t in (1:ℝ)..z, K * t ^ (rgQ α m - 2) := hb
      _ = K * (z ^ (rgQ α m - 1) - 1) / (rgQ α m - 1) := hval
      _ ≤ K * z ^ (rgQ α m - 1) / (rgQ α m - 1) := by
          have h2 : (z ^ (rgQ α m - 1) - 1) / (rgQ α m - 1)
              ≤ z ^ (rgQ α m - 1) / (rgQ α m - 1) :=
            div_le_div_of_nonneg_right (by linarith) (le_of_lt hqm)
          calc K * (z ^ (rgQ α m - 1) - 1) / (rgQ α m - 1)
              = K * ((z ^ (rgQ α m - 1) - 1) / (rgQ α m - 1)) := by ring
            _ ≤ K * (z ^ (rgQ α m - 1) / (rgQ α m - 1)) :=
                mul_le_mul_of_nonneg_left h2 (le_of_lt hKpos)
            _ = K * z ^ (rgQ α m - 1) / (rgQ α m - 1) := by ring
  have hsplit : (∫ t in (0:ℝ)..1, rgF1 α m c t) + (∫ t in (1:ℝ)..z, rgF1 α m c t)
      = ∫ t in (0:ℝ)..z, rgF1 α m c t :=
    intervalIntegral.integral_add_adjacent_intervals hII01 hII1z
  have hfin : |∫ t in (0:ℝ)..z, rgF1 α m c t|
      ≤ (|∫ t in (0:ℝ)..1, rgF1 α m c t| + K / (rgQ α m - 1) + 1) * z ^ (rgQ α m - 1) := by
    have h1 : |(∫ t in (0:ℝ)..1, rgF1 α m c t) + ∫ t in (1:ℝ)..z, rgF1 α m c t|
        ≤ |∫ t in (0:ℝ)..1, rgF1 α m c t| + |∫ t in (1:ℝ)..z, rgF1 α m c t| :=
      abs_add_le _ _
    have h2 : |∫ t in (0:ℝ)..1, rgF1 α m c t| + |∫ t in (1:ℝ)..z, rgF1 α m c t|
        ≤ |∫ t in (0:ℝ)..1, rgF1 α m c t| + K * z ^ (rgQ α m - 1) / (rgQ α m - 1) :=
      add_le_add le_rfl htail
    have h3 : |∫ t in (0:ℝ)..1, rgF1 α m c t| + K * z ^ (rgQ α m - 1) / (rgQ α m - 1)
        ≤ (|∫ t in (0:ℝ)..1, rgF1 α m c t| + K / (rgQ α m - 1) + 1) * z ^ (rgQ α m - 1) := by
      have hAz : |∫ t in (0:ℝ)..1, rgF1 α m c t|
          ≤ |∫ t in (0:ℝ)..1, rgF1 α m c t| * z ^ (rgQ α m - 1) :=
        le_mul_of_one_le_right (abs_nonneg _) hzp
      have hKz : K / (rgQ α m - 1) ≤ K / (rgQ α m - 1) * z ^ (rgQ α m - 1) :=
        le_mul_of_one_le_right hKq hzp
      have hEq : K * z ^ (rgQ α m - 1) / (rgQ α m - 1)
          = (K / (rgQ α m - 1)) * z ^ (rgQ α m - 1) := by ring
      rw [hEq]
      nlinarith [hAz, hKz]
    calc |∫ t in (0:ℝ)..z, rgF1 α m c t|
        = |(∫ t in (0:ℝ)..1, rgF1 α m c t) + ∫ t in (1:ℝ)..z, rgF1 α m c t| := by
          rw [← hsplit]
      _ ≤ |∫ t in (0:ℝ)..1, rgF1 α m c t| + |∫ t in (1:ℝ)..z, rgF1 α m c t| := h1
      _ ≤ |∫ t in (0:ℝ)..1, rgF1 α m c t| + K * z ^ (rgQ α m - 1) / (rgQ α m - 1) := h2
      _ ≤ (|∫ t in (0:ℝ)..1, rgF1 α m c t| + K / (rgQ α m - 1) + 1) * z ^ (rgQ α m - 1) := h3
  rw [Work.FTS.EllExist.rgA]
  exact hfin

end Work.FTS.ClassC
