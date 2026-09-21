import Mathlib
import Submission.Work.OddVolterra.Free.FreeSetup
import Submission.Work.OddVolterra.Free.glueA_eq_inversion
import Submission.Work.OddVolterra.Free.gap_inversion_bounds_free
import Submission.Work.OddCurve.LowSlope.GlueDataDefs
import Submission.Work.OddCurve.LowSlope.anchorPhiData_eq_ballData
import Submission.Work.OddCurve.LowSlope.anchorPsiData_eq_zero
import Submission.Work.OddCurve.LowSlope.QuantDefs
import Submission.Work.OddCurve.LowSlope.waistRadial_eq_one
import Submission.Work.OddCurve.LowSlope.waistData
import Submission.Work.OddCurve.LowSlope.gapKernel_derivs
import Submission.Work.OddCurve.LowSlope.abel_integral_trig_substitution_no_hyp
import Submission.Work.OddRadon.radonInverse_radonPhi_local
import Submission.Work.OddRadon.radonInverse_radonPsi_local
import Submission.Work.OddCurve.LowSlope.radonInverse_radonPhi
import Submission.Work.OddVolterra.Free.radonInverseGapDeriv
import Submission.Work.OddVolterra.Free.nearRegionGlueBounds
import Submission.Work.OddVolterra.Free.farRegionGlueBounds
import Submission.Work.Analysis.Calculus.contDiff_intervalIntegral_fixed

namespace Work.OddVolterra.Free

open MeasureTheory Set Filter
open scoped Topology ContDiff Interval

noncomputable section

/-! ## Elementary bounds for the profile deviations -/

/-- `|x ^ m - 1| ≤ m * 2 ^ (m-1) * δ` for `|x - 1| ≤ δ ≤ 1`. -/
lemma pow_sub_one_abs_le {m : ℕ} {x δ : ℝ} (h : |x - 1| ≤ δ) (hδ : δ ≤ 1) :
    |x ^ m - (1 : ℝ)| ≤ (m : ℝ) * 2 ^ (m - 1) * δ := by
  have h1 : |x ^ m - (1 : ℝ) ^ m| ≤ |x - 1| * (m : ℝ) * max |x| |(1 : ℝ)| ^ (m - 1) :=
    abs_pow_sub_pow_le x 1 m
  rw [one_pow, abs_one] at h1
  have hx1 : |x| ≤ 1 + δ := by
    have h2 : |x| ≤ |x - 1| + 1 := by simpa using abs_sub_abs_le_abs_sub x (1 : ℝ)
    linarith
  have hmax : max |x| (1:ℝ) ≤ 2 := max_le (by linarith) (by norm_num)
  have hmax0 : (0:ℝ) ≤ max |x| (1:ℝ) := le_trans (by norm_num) (le_max_right _ _)
  have hpow : (max |x| (1:ℝ)) ^ (m - 1) ≤ (2:ℝ) ^ (m - 1) := pow_le_pow_left₀ hmax0 hmax _
  have hm0 : (0:ℝ) ≤ (m:ℝ) := Nat.cast_nonneg m
  have h2 : |x - 1| * (m:ℝ) * (max |x| (1:ℝ)) ^ (m - 1) ≤ δ * (m:ℝ) * 2 ^ (m - 1) := by
    have hle : (0:ℝ) ≤ |x - 1| * (m:ℝ) := mul_nonneg (abs_nonneg _) hm0
    calc |x - 1| * ↑m * (max |x| (1:ℝ)) ^ (m - 1) ≤ |x - 1| * ↑m * (2:ℝ) ^ (m - 1) :=
          mul_le_mul_of_nonneg_left hpow hle
      _ ≤ δ * ↑m * (2:ℝ) ^ (m - 1) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h hm0) (by positivity)
  have h3 : δ * (m:ℝ) * (2:ℝ) ^ (m - 1) = (m:ℝ) * 2 ^ (m - 1) * δ := by ring
  linarith [h1, h2, h3]

/-- `|a - b| ≤ |a| + |b|`. -/
lemma abs_sub_le_abs_add' (a b : ℝ) : |a - b| ≤ |a| + |b| := by
  have := abs_add_le a (-b)
  simpa [sub_eq_add_neg, abs_neg] using this

/-- The bound on the first deviation profile `gammaDev` on the gap window. -/
lemma gammaDev_abs_le (n : ℕ) {ρ : ℝ → ℝ} {u C₁ ε : ℝ}
    (hu : |u| ≤ 1) (hρ : |ρ u - 1| ≤ C₁ * ε) (hρ' : |ρ (-u) - 1| ≤ C₁ * ε)
    (hε : C₁ * ε ≤ 1) :
    |Work.OddCurve.LowSlope.gammaDev n ρ u|
      ≤ ((2 * n + 2 : ℕ) : ℝ) * 2 ^ (2 * n + 2) * (C₁ * ε) := by
  have hδ0 : (0 : ℝ) ≤ C₁ * ε := by
    have h := pow_sub_one_abs_le (m := 2 * n + 2) (x := ρ u) (δ := C₁ * ε) hρ hε
    have h1 : (0 : ℝ) ≤ (↑(2 * n + 2) : ℝ) * 2 ^ (2 * n + 1) * (C₁ * ε) := by
      rw [show (2 * n + 2 - 1) = 2 * n + 1 from by omega] at h
      exact le_trans (abs_nonneg _) h
    have h1' : (0 : ℝ) ≤ (C₁ * ε) * ((↑(2 * n + 2) : ℝ) * 2 ^ (2 * n + 1)) := by
      rw [show (C₁ * ε) * ((↑(2 * n + 2) : ℝ) * 2 ^ (2 * n + 1))
        = (↑(2 * n + 2) : ℝ) * 2 ^ (2 * n + 1) * (C₁ * ε) by ring]
      exact h1
    exact nonneg_of_mul_nonneg_left h1' (by positivity)
  have hb := pow_sub_one_abs_le (m := 2 * n + 2) (x := ρ u) (δ := C₁ * ε) hρ hε
  have hb' := pow_sub_one_abs_le (m := 2 * n + 2) (x := ρ (-u)) (δ := C₁ * ε) hρ' hε
  have he : 2 * n + 2 - 1 = 2 * n + 1 := by omega
  rw [he] at hb hb'
  have hu2 : u ^ 2 ≤ 1 := by nlinarith [abs_le.mp hu]
  have hsplit : Work.OddCurve.LowSlope.gammaDev n ρ u
      = u ^ 2 * ((ρ u ^ (2 * n + 2) - 1) + (ρ (-u) ^ (2 * n + 2) - 1)) / 2 := by
    simp only [Work.OddCurve.LowSlope.gammaDev]; ring
  have h2 : |(ρ u ^ (2 * n + 2) - 1) + (ρ (-u) ^ (2 * n + 2) - 1)|
      ≤ 2 * ((↑(2 * n + 2) : ℝ) * 2 ^ (2 * n + 1) * (C₁ * ε)) := by
    have h := abs_add_le (ρ u ^ (2 * n + 2) - 1) (ρ (-u) ^ (2 * n + 2) - 1)
    linarith [hb, hb', h]
  have hmid : |Work.OddCurve.LowSlope.gammaDev n ρ u|
      ≤ (↑(2 * n + 2) : ℝ) * 2 ^ (2 * n + 1) * (C₁ * ε) := by
    rw [hsplit, abs_div, abs_mul, abs_of_nonneg (sq_nonneg u),
      abs_of_pos (by norm_num : (0 : ℝ) < 2), div_le_iff₀ (by norm_num : (0 : ℝ) < 2)]
    have h3 : u ^ 2 * |(ρ u ^ (2 * n + 2) - 1) + (ρ (-u) ^ (2 * n + 2) - 1)|
        ≤ 2 * ((↑(2 * n + 2) : ℝ) * 2 ^ (2 * n + 1) * (C₁ * ε)) := by
      have h := mul_le_mul hu2 h2 (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)
      simpa using h
    linarith [h3]
  refine hmid.trans ?_
  have hp : (2:ℝ) ^ (2 * n + 1) ≤ 2 ^ (2 * n + 2) :=
    pow_le_pow_right₀ (by norm_num) (by omega)
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hp (Nat.cast_nonneg _)) hδ0

/-- The bound on the second deviation profile `gammaPsi` on the gap window. -/
lemma gammaPsi_abs_le (n : ℕ) {ρ : ℝ → ℝ} {u C₁ ε : ℝ}
    (hu : |u| ≤ 1) (hρ : |ρ u - 1| ≤ C₁ * ε) (hρ' : |ρ (-u) - 1| ≤ C₁ * ε)
    (hε : C₁ * ε ≤ 1) :
    |Work.OddCurve.LowSlope.gammaPsi n ρ u|
      ≤ ((2 * n + 2 : ℕ) : ℝ) * 2 ^ (2 * n + 2) * (C₁ * ε) := by
  have hδ0 : (0 : ℝ) ≤ C₁ * ε := by
    have h := pow_sub_one_abs_le (m := 2 * n + 1) (x := ρ u) (δ := C₁ * ε) hρ hε
    have h1 : (0 : ℝ) ≤ (↑(2 * n + 1) : ℝ) * 2 ^ (2 * n) * (C₁ * ε) := by
      rw [show (2 * n + 1 - 1) = 2 * n from by omega] at h
      exact le_trans (abs_nonneg _) h
    have h1' : (0 : ℝ) ≤ (C₁ * ε) * ((↑(2 * n + 1) : ℝ) * 2 ^ (2 * n)) := by
      rw [show (C₁ * ε) * ((↑(2 * n + 1) : ℝ) * 2 ^ (2 * n))
        = (↑(2 * n + 1) : ℝ) * 2 ^ (2 * n) * (C₁ * ε) by ring]
      exact h1
    exact nonneg_of_mul_nonneg_left h1' (by positivity)
  have hb := pow_sub_one_abs_le (m := 2 * n + 1) (x := ρ u) (δ := C₁ * ε) hρ hε
  have hb' := pow_sub_one_abs_le (m := 2 * n + 1) (x := ρ (-u)) (δ := C₁ * ε) hρ' hε
  have he : 2 * n + 1 - 1 = 2 * n := by omega
  rw [he] at hb hb'
  have hsplit : Work.OddCurve.LowSlope.gammaPsi n ρ u
      = u * ((ρ u ^ (2 * n + 1) - 1) - (ρ (-u) ^ (2 * n + 1) - 1)) / 2 := by
    simp only [Work.OddCurve.LowSlope.gammaPsi]; ring
  have h2 : |(ρ u ^ (2 * n + 1) - 1) - (ρ (-u) ^ (2 * n + 1) - 1)|
      ≤ 2 * ((↑(2 * n + 1) : ℝ) * 2 ^ (2 * n) * (C₁ * ε)) := by
    have h := abs_sub_le_abs_add' (ρ u ^ (2 * n + 1) - 1) (ρ (-u) ^ (2 * n + 1) - 1)
    linarith [hb, hb', h]
  have hmid : |Work.OddCurve.LowSlope.gammaPsi n ρ u|
      ≤ (↑(2 * n + 1) : ℝ) * 2 ^ (2 * n) * (C₁ * ε) := by
    rw [hsplit, abs_div, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2),
      div_le_iff₀ (by norm_num : (0 : ℝ) < 2)]
    have h3 : |u| * |(ρ u ^ (2 * n + 1) - 1) - (ρ (-u) ^ (2 * n + 1) - 1)|
        ≤ 2 * ((↑(2 * n + 1) : ℝ) * 2 ^ (2 * n) * (C₁ * ε)) := by
      have h := mul_le_mul hu h2 (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)
      simpa using h
    linarith [h3]
  refine hmid.trans ?_
  have hk : (↑(2 * n + 1) : ℝ) ≤ ↑(2 * n + 2) := by
    have : 2 * n + 1 ≤ 2 * n + 2 := by omega
    exact_mod_cast this
  have hp : (2:ℝ) ^ (2 * n) ≤ 2 ^ (2 * n + 2) :=
    pow_le_pow_right₀ (by norm_num) (by omega)
  have hmain : (↑(2 * n + 1) : ℝ) * 2 ^ (2 * n) ≤ ((2 * n + 2 : ℕ) : ℝ) * 2 ^ (2 * n + 2) :=
    mul_le_mul hk hp (by positivity) (Nat.cast_nonneg _)
  exact mul_le_mul_of_nonneg_right hmain hδ0

/-! ## The waist of the anchor's radial function -/

/-- The radial point of an anchor's radial function stays inside `(-1,1)`. -/
private lemma anchorRadial_radial_point {h X Y ρ : ℝ → ℝ}
    (hρpos : ∀ u ∈ Set.Ioo (-1 : ℝ) 1, 0 < ρ u)
    (hgraph : ∀ u ∈ Set.Ioo (-1 : ℝ) 1,
      ρ u * Real.sqrt (1 - u ^ 2) = Work.OddEnvelope.envelopeProfile h X Y (ρ u * u)) :
    ∀ u ∈ Set.Ioo (-1 : ℝ) 1, ρ u * u ∈ Set.Ioo (-1 : ℝ) 1 := by
  intro u hu
  have hspos : 0 < Real.sqrt (1 - u ^ 2) := Real.sqrt_pos.mpr (by nlinarith [hu.1, hu.2])
  have hfu : Work.OddEnvelope.envelopeProfile h X Y (ρ u * u) = ρ u * Real.sqrt (1 - u ^ 2) :=
    (hgraph u hu).symm
  have hne : Work.OddEnvelope.envelopeProfile h X Y (ρ u * u) ≠ 0 := by
    rw [hfu]; exact ne_of_gt (mul_pos (hρpos u hu) hspos)
  have hIcc : ρ u * u ∈ Set.Icc (-1 : ℝ) 1 :=
    Work.OddEnvelope.envelopeProfile_support (Function.mem_support.mpr hne)
  have hne1 : Work.OddEnvelope.envelopeProfile h X Y 1 = 0 := Work.OddEnvelope.envelopeProfile_right_end
  have hnem1 : Work.OddEnvelope.envelopeProfile h X Y (-1) = 0 := Work.OddEnvelope.envelopeProfile_left_end
  refine ⟨?_, ?_⟩
  · rcases eq_or_lt_of_le hIcc.1 with hq | hq
    · exfalso
      rw [← hq, hnem1] at hfu
      exact absurd (mul_pos (hρpos u hu) hspos) (by rw [hfu]; norm_num)
    · exact hq
  · rcases eq_or_lt_of_le hIcc.2 with hq | hq
    · exfalso
      rw [hq, hne1] at hfu
      exact absurd (mul_pos (hρpos u hu) hspos) (by rw [hfu]; norm_num)
    · exact hq

/-- **The waist of the anchor's radial function**: `ρ = 1` on `|u| < tStar`, and the radial
points stay inside `(-1,1)`. -/
private lemma anchorRadial_waist {h X Y ρ : ℝ → ℝ}
    (H : Work.OddEnvelope.IsEnvelopeCurve h X Y)
    (hρ : Work.OddVolterra.Free.IsAnchorRadial h X Y ρ) :
    (∀ u ∈ Set.Ioo (-1 : ℝ) 1, ρ u * u ∈ Set.Ioo (-1 : ℝ) 1) ∧
    (∀ u : ℝ, |u| < Work.OddEnvelope.tStar → ρ u = 1) := by
  obtain ⟨hρpos, hρsm, hρmono, hgraph, hρ0⟩ := hρ
  have hbound := anchorRadial_radial_point hρpos hgraph
  refine ⟨hbound, fun u hu => ?_⟩
  exact Work.OddCurve.LowSlope.waistRadial_eq_one H hρpos hρ0 hgraph hbound hu
/-! ## The glued deviations as Radon profiles of the profile deviations -/

/-- Linearity of `radonProfile` in the profile. -/
private lemma radonProfile_sub' {d : ℕ} {γ₁ γ₂ : ℝ → ℝ} {c : ℝ}
    (h₁ : IntervalIntegrable (fun s : ℝ => (1 - s ^ 2) ^ ((d : ℝ) / 2 - 2) * γ₁ (c * s))
      volume (-1 : ℝ) 1)
    (h₂ : IntervalIntegrable (fun s : ℝ => (1 - s ^ 2) ^ ((d : ℝ) / 2 - 2) * γ₂ (c * s))
      volume (-1 : ℝ) 1) :
    Work.OddRadon.radonProfile d (γ₁ - γ₂) c
      = Work.OddRadon.radonProfile d γ₁ c - Work.OddRadon.radonProfile d γ₂ c := by
  simp only [Work.OddRadon.radonProfile]
  rw [← mul_sub]
  congr 1
  have hL : (∫ s in (-1 : ℝ)..1, (1 - s ^ 2) ^ ((d : ℝ) / 2 - 2) * (γ₁ - γ₂) (c * s))
      = ∫ s in (-1 : ℝ)..1, ((1 - s ^ 2) ^ ((d : ℝ) / 2 - 2) * γ₁ (c * s)
          - (1 - s ^ 2) ^ ((d : ℝ) / 2 - 2) * γ₂ (c * s)) := by
    apply intervalIntegral.integral_congr
    intro s _
    simp only [Pi.sub_apply]
    ring
  rw [hL]
  exact intervalIntegral.integral_sub h₁ h₂

/-- The first glued deviation on the cap is the Radon profile of the profile deviation. -/
private lemma deltaA_eq_radonProfile_cap (n : ℕ) (hn : 1 ≤ n) {ρ : ℝ → ℝ}
    (hρ : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ρ (Set.Ioo (-1 : ℝ) 1)) :
    ∀ c ∈ Set.Ioo (0 : ℝ) (4 / 5),
      Work.OddCurve.LowSlope.deltaA n ρ c
        = Work.OddRadon.radonProfile (2 * n + 1) (Work.OddCurve.LowSlope.gammaDev n ρ) c := by
  intro c hc
  have hcpos : 0 < c := hc.1
  have hcabs : |c| < 1 := by rw [abs_of_pos hcpos]; linarith [hc.2]
  have hGlue : Work.OddCurve.LowSlope.deltaA n ρ c
      = Work.OddCurve.LowSlope.radonPhi n ρ c - Work.OddCurve.LowSlope.ballPhiData n c := by
    simp only [Work.OddCurve.LowSlope.deltaA, Work.OddCurve.LowSlope.GlueF]
    rw [abs_of_pos hcpos, Work.OddCurve.LowSlope.gluedPhi_of_lt hcpos.le hc.2]
  rw [hGlue]
  have hcomp : ∀ a : ℝ, |a| < 1 → ContinuousOn (fun s : ℝ => (a * s) ^ 2 * ρ (a * s) ^ (2 * n + 2))
      (Set.uIcc (-1 : ℝ) 1) :=
    fun a ha => Work.OddCurve.LowSlope.continuousOn_profile_comp_mul n ha hρ
  have htriv : ((fun u : ℝ => u ^ 2 / 2 * (ρ u ^ (2 * n + 2) + ρ (-u) ^ (2 * n + 2)))
        - fun u : ℝ => u ^ 2) = Work.OddCurve.LowSlope.gammaDev n ρ := by
    funext x
    simp only [Pi.sub_apply, Work.OddCurve.LowSlope.gammaDev]
    ring
  have hcont1'' : ContinuousOn (fun s : ℝ => (-(c * s)) ^ 2 * ρ (-(c * s)) ^ (2 * n + 2))
      (Set.uIcc (-1 : ℝ) 1) := by
    have h := hcomp (-c) (by simpa using hcabs)
    refine h.congr ?_
    intro s _
    simp only []
    rw [show -c * s = -(c * s) by ring]
  have hint1 := Work.OddCurve.LowSlope.intervalIntegrable_radonKernel_mul n hn (hcomp c hcabs)
  have hint1'' := Work.OddCurve.LowSlope.intervalIntegrable_radonKernel_mul n hn hcont1''
  have hint2 := Work.OddCurve.LowSlope.intervalIntegrable_radonKernel_mul n hn
    (by fun_prop : ContinuousOn (fun s : ℝ => (c * s) ^ 2) (Set.uIcc (-1 : ℝ) 1))
  have hPhi : Work.OddCurve.LowSlope.radonPhi n ρ c
      = Work.OddRadon.radonProfile (2 * n + 1)
          (fun u : ℝ => u ^ 2 / 2 * (ρ u ^ (2 * n + 2) + ρ (-u) ^ (2 * n + 2))) c := by
    have h := Work.OddCurve.LowSlope.radonProfile_evenPart (2 * n + 1)
      (γ := fun u : ℝ => u ^ 2 * ρ u ^ (2 * n + 2)) (c := c) hint1 hint1''
    refine h.trans ?_
    congr 1
    funext u
    ring
  have hBall : Work.OddCurve.LowSlope.ballPhiData n c
      = Work.OddRadon.radonProfile (2 * n + 1) (fun u : ℝ => u ^ 2) c := rfl
  rw [hPhi, hBall]
  have hcontA : ContinuousOn
      (fun s : ℝ => (c * s) ^ 2 / 2 * (ρ (c * s) ^ (2 * n + 2) + ρ (-(c * s)) ^ (2 * n + 2)))
      (Set.uIcc (-1 : ℝ) 1) := by
    have hsum := (hcomp c hcabs).add hcont1''
    have hdiv := hsum.div_const 2
    refine hdiv.congr ?_
    intro s _
    simp only [Pi.add_apply]
    ring_nf
  have hintA := Work.OddCurve.LowSlope.intervalIntegrable_radonKernel_mul n hn hcontA
  have hsub := radonProfile_sub' (d := 2 * n + 1)
    (γ₁ := fun u : ℝ => u ^ 2 / 2 * (ρ u ^ (2 * n + 2) + ρ (-u) ^ (2 * n + 2)))
    (γ₂ := fun u : ℝ => u ^ 2) (c := c) hintA hint2
  rw [← hsub, htriv]

/-- The second glued deviation on the cap is the Radon profile of `gammaPsi`. -/
private lemma deltaB_eq_radonProfile_cap (n : ℕ) (hn : 1 ≤ n) {ρ : ℝ → ℝ}
    (hρ : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ρ (Set.Ioo (-1 : ℝ) 1)) :
    ∀ c ∈ Set.Ioo (0 : ℝ) (4 / 5),
      Work.OddCurve.LowSlope.deltaB n ρ c
        = Work.OddRadon.radonProfile (2 * n + 1) (Work.OddCurve.LowSlope.gammaPsi n ρ) c := by
  intro c hc
  have hcpos : 0 < c := hc.1
  have hcabs : |c| < 1 := by rw [abs_of_pos hcpos]; linarith [hc.2]
  have hGlue : Work.OddCurve.LowSlope.deltaB n ρ c = Work.OddCurve.LowSlope.radonPsi n ρ c := by
    simp only [Work.OddCurve.LowSlope.deltaB, Work.OddCurve.LowSlope.GlueG]
    rw [abs_of_pos hcpos, Work.OddCurve.LowSlope.gluedPsi_of_lt hcpos.le hc.2]
  rw [hGlue]
  have hcomp : ∀ a : ℝ, |a| < 1 → ContinuousOn (fun s : ℝ => (a * s) * ρ (a * s) ^ (2 * n + 1))
      (Set.uIcc (-1 : ℝ) 1) :=
    fun a ha => Work.OddRadon.continuousOn_weight_comp_mul_of_contDiffOn n hρ ha
  have htriv : (fun u : ℝ => (u * ρ u ^ (2 * n + 1) + (-u) * ρ (-u) ^ (2 * n + 1)) / 2)
      = Work.OddCurve.LowSlope.gammaPsi n ρ := by
    funext x
    simp only [Work.OddCurve.LowSlope.gammaPsi]
    ring
  have hcont1'' : ContinuousOn (fun s : ℝ => (-(c * s)) * ρ (-(c * s)) ^ (2 * n + 1))
      (Set.uIcc (-1 : ℝ) 1) := by
    have h := hcomp (-c) (by simpa using hcabs)
    refine h.congr ?_
    intro s _
    simp only []
    rw [show -c * s = -(c * s) by ring]
  have hint1 := Work.OddCurve.LowSlope.intervalIntegrable_radonKernel_mul n hn (hcomp c hcabs)
  have hint1'' := Work.OddCurve.LowSlope.intervalIntegrable_radonKernel_mul n hn hcont1''
  have hPsi : Work.OddCurve.LowSlope.radonPsi n ρ c
      = Work.OddRadon.radonProfile (2 * n + 1)
          (fun u : ℝ => (u * ρ u ^ (2 * n + 1) + (-u) * ρ (-u) ^ (2 * n + 1)) / 2) c := by
    have h := Work.OddCurve.LowSlope.radonProfile_evenPart (2 * n + 1)
      (γ := fun u : ℝ => u * ρ u ^ (2 * n + 1)) (c := c) hint1 hint1''
    refine h.trans ?_
    rfl
  rw [hPsi, htriv]

/-! ## The junction of the anchor's data with the ball's, on a window past `4/5`

On the slopes `(71/100, 4/5)` the bump vanishes with its derivative and the anchor satisfies the
two moment equations (`71/100 > 1 - 3τ = 7/10`), so the anchor's Radon data are the ball's there.
In the `c = (√(1+s²))⁻¹` variable this is the window `(cStar, c')` with
`c' = (√(1+(71/100)²))⁻¹ > 4/5` — past the glue point, which is what makes the value of the
glued datum's inverse at `4/5` computable by locality. -/

/-- **The junction, with a window extending past `c = 4/5`.** -/
private lemma anchorData_junction_wide (n : ℕ) (hn : 1 ≤ n) {ε : ℝ} {h X Y ρ : ℝ → ℝ}
    (hclass : Work.OddVolterra.Free.IsSmallFlatBumpClass n (2 * n + 2) ε h)
    (H : Work.OddEnvelope.IsEnvelopeCurve h X Y)
    (hρ : Work.OddVolterra.Free.IsAnchorRadial h X Y ρ)
    (hA : ∀ s : ℝ, 1 - 3 * Work.OddVolterra.tau < s → s ≤ 1 →
      Work.OddCurve.momentA n h X Y (Work.OddEnvelope.envelopeProfile h X Y) s =
        Work.OddCurve.refConst n / Real.sqrt (1 + s ^ 2))
    (hB : ∀ s : ℝ, 1 - 3 * Work.OddVolterra.tau < s → s ≤ 1 →
      Work.OddCurve.momentB n h X Y (Work.OddEnvelope.envelopeProfile h X Y) s = 0) :
    ∃ c' : ℝ, 4 / 5 < c' ∧ c' < 1 ∧
      (∀ c ∈ Set.Ioo Work.OddCurve.LowSlope.cStar c',
        Work.OddCurve.LowSlope.radonPhi n ρ c = Work.OddCurve.LowSlope.ballPhiData n c ∧
        Work.OddCurve.LowSlope.radonPsi n ρ c = 0) := by
  obtain ⟨hdiff, hsupp, hjets, hflat⟩ := hclass
  obtain ⟨hρpos, hρsm, hρmono, hgraph, hρ0⟩ := hρ
  have hτ1 : (1 : ℝ) - 2 * Work.OddVolterra.tau = 4 / 5 := by norm_num [Work.OddVolterra.tau]
  have hτ2 : (1 : ℝ) - 3 * Work.OddVolterra.tau = 7 / 10 := by norm_num [Work.OddVolterra.tau]
  set a : ℝ := 71 / 100 with hadef
  have hapos : 0 < a := by rw [hadef]; norm_num
  have ha2 : a < 3 / 4 := by rw [hadef]; norm_num
  have ha1 : 7 / 10 < a := by rw [hadef]; norm_num
  have hasq : a ^ 2 = 5041 / 10000 := by rw [hadef]; norm_num
  have hzero_le : ∀ x : ℝ, x ≤ 4 / 5 → h x = 0 := by
    intro x hx
    by_contra hne
    have h1 : x ∈ Function.support h := Function.mem_support.mpr hne
    have h2 := hsupp h1
    rw [Set.mem_Ioo] at h2
    rw [hτ1] at h2
    linarith [h2.1, hx]
  have hzero : ∀ s ∈ Set.Icc a (4 / 5), h s = 0 := fun s hs => by
    rw [Set.mem_Icc] at hs
    exact hzero_le s hs.2
  have hder0 : ∀ s ∈ Set.Icc a (4 / 5), deriv h s = 0 := by
    intro s hs
    rw [Set.mem_Icc] at hs
    have hnb : h =ᶠ[𝓝 s] 0 := by
      rcases lt_or_eq_of_le hs.2 with hlt | heq
      · filter_upwards [isOpen_Ioo.mem_nhds
          (show s ∈ Set.Ioo (s - 1) ((4 / 5 : ℝ)) from ⟨by linarith, hlt⟩)] with x hx
        exact hzero_le x (le_of_lt hx.2)
      · subst heq
        obtain ⟨η, hηpos, hη⟩ := hflat
        filter_upwards [Ioo_mem_nhds (by norm_num : (4 / 5 : ℝ) - 1 < 4 / 5)
          (by linarith : (4 / 5 : ℝ) < 4 / 5 + η)] with x hx
        rcases lt_or_ge x (4 / 5) with hx' | hx'
        · exact hzero_le x (le_of_lt hx')
        · exact hη x (by rw [hτ1]; exact hx') (by linarith [hx.2])
    have h := Filter.EventuallyEq.deriv_eq hnb
    simpa using h
  have hA' : ∀ t ∈ Set.Icc a (4 / 5),
      Work.OddCurve.momentA n h X Y (Work.OddEnvelope.envelopeProfile h X Y) t =
        Work.OddCurve.refConst n / Real.sqrt (1 + t ^ 2) := by
    intro t ht
    rw [Set.mem_Icc] at ht
    refine hA t ?_ (by linarith [ht.2])
    rw [hτ2]; exact lt_of_lt_of_le ha1 ht.1
  have hB' : ∀ t ∈ Set.Icc a (4 / 5),
      Work.OddCurve.momentB n h X Y (Work.OddEnvelope.envelopeProfile h X Y) t = 0 := by
    intro t ht
    rw [Set.mem_Icc] at ht
    refine hB t ?_ (by linarith [ht.2])
    rw [hτ2]; exact lt_of_lt_of_le ha1 ht.1
  have hρsm1 : ContDiffOn ℝ 1 ρ (Set.Ioo (-1 : ℝ) 1) := hρsm.of_le (by simp)
  have hs2 : 0 < Real.sqrt (1 + a ^ 2) := Real.sqrt_pos.mpr (by positivity)
  have hsq : (Real.sqrt (1 + a ^ 2)) ^ 2 = 1 + a ^ 2 := Real.sq_sqrt (by positivity)
  refine ⟨(Real.sqrt (1 + a ^ 2))⁻¹, ?_, ?_, ?_⟩
  · rw [inv_eq_one_div, lt_div_iff₀ hs2]
    have h2 : ((4 / 5 : ℝ) * Real.sqrt (1 + a ^ 2)) ^ 2 < 1 ^ 2 := by
      rw [mul_pow, hsq]; nlinarith [hasq]
    nlinarith [h2, mul_pos (by norm_num : (0 : ℝ) < 4 / 5) hs2]
  · rw [inv_lt_one_iff₀]
    right
    nlinarith [hsq, hs2, hapos]
  · intro c hc
    obtain ⟨hc1, hc2⟩ := hc
    have hcpos : 0 < c := lt_trans Work.OddCurve.LowSlope.cStar_pos hc1
    have hc1pos : 0 < 1 - c ^ 2 := by
      have h2 : c < 1 := lt_trans hc2 (by
        rw [inv_lt_one_iff₀]
        right
        nlinarith [hsq, hs2, hapos])
      nlinarith [hcpos, h2]
    set s : ℝ := Real.sqrt (1 - c ^ 2) / c with hsdef
    have hs_sq : s ^ 2 = (1 - c ^ 2) / c ^ 2 := by
      rw [hsdef, div_pow, Real.sq_sqrt (le_of_lt hc1pos)]
    have hs_pos : 0 < s := by
      rw [hsdef]; exact div_pos (Real.sqrt_pos.mpr hc1pos) hcpos
    have hcsq' : (1 + a ^ 2) * c ^ 2 < 1 := by
      have h2 : c * Real.sqrt (1 + a ^ 2) < 1 := by
        have h := hc2
        rw [inv_eq_one_div, lt_div_iff₀ hs2] at h
        exact h
      have h3 : (c * Real.sqrt (1 + a ^ 2)) ^ 2 < 1 ^ 2 := by
        nlinarith [h2, mul_nonneg hcpos.le hs2.le]
      rw [mul_pow, hsq] at h3
      linarith [h3]
    have hcsq'' : Work.OddCurve.LowSlope.cStar ^ 2 < c ^ 2 := by
      nlinarith [hc1, hcpos, Work.OddCurve.LowSlope.cStar_pos]
    have hs_lo : a < s := by
      have h : a ^ 2 < s ^ 2 := by
        rw [hs_sq, lt_div_iff₀ (by positivity : (0 : ℝ) < c ^ 2)]
        nlinarith [hcsq']
      nlinarith [h, hs_pos, hapos]
    have hs_hi : s < 4 / 5 := by
      have h : s ^ 2 < (4 / 5 : ℝ) ^ 2 := by
        rw [hs_sq, div_lt_iff₀ (by positivity : (0 : ℝ) < c ^ 2)]
        have hcs : 25 / 41 < c ^ 2 := by
          have h3 := Work.OddVolterra.Free.cStar_sq
          linarith [h3, hcsq'']
        nlinarith [hcs]
      nlinarith [h, hs_pos]
    have hcs : (Real.sqrt (1 + s ^ 2))⁻¹ = c := by
      have h1 : 1 + s ^ 2 = 1 / c ^ 2 := by
        rw [hs_sq]; field_simp; ring
      have h2 : Real.sqrt (1 + s ^ 2) = 1 / c := by
        rw [Real.sqrt_eq_iff_eq_sq (by positivity) (by positivity), h1]
        ring
      rw [h2, one_div, inv_inv]
    have hφ := Work.OddCurve.LowSlope.anchorPhiData_eq_ballData n hn H hρpos hρsm1 hρmono hgraph
      hapos (by linarith [ha2]) hzero hder0 hA' hB' s ⟨hs_lo, hs_hi⟩
    rw [hcs] at hφ
    have hψ := Work.OddCurve.LowSlope.anchorPsiData_eq_zero n hn H hρpos hρsm1 hρmono hgraph
      hapos (by linarith [ha2]) hzero hder0 hB' s ⟨hs_lo, hs_hi⟩
    rw [hcs] at hψ
    exact ⟨hφ, hψ⟩

/-- The junction on the original window `(cStar, 4/5)`, as a consequence of the wide one. -/
private lemma anchorData_junction_free (n : ℕ) (hn : 1 ≤ n) {ε : ℝ} {h X Y ρ : ℝ → ℝ}
    (hclass : Work.OddVolterra.Free.IsSmallFlatBumpClass n (2 * n + 2) ε h)
    (H : Work.OddEnvelope.IsEnvelopeCurve h X Y)
    (hρ : Work.OddVolterra.Free.IsAnchorRadial h X Y ρ)
    (hA : ∀ s : ℝ, 1 - 3 * Work.OddVolterra.tau < s → s ≤ 1 →
      Work.OddCurve.momentA n h X Y (Work.OddEnvelope.envelopeProfile h X Y) s =
        Work.OddCurve.refConst n / Real.sqrt (1 + s ^ 2))
    (hB : ∀ s : ℝ, 1 - 3 * Work.OddVolterra.tau < s → s ≤ 1 →
      Work.OddCurve.momentB n h X Y (Work.OddEnvelope.envelopeProfile h X Y) s = 0) :
    ∀ c ∈ Set.Ioo Work.OddCurve.LowSlope.cStar (4 / 5),
      Work.OddCurve.LowSlope.radonPhi n ρ c = Work.OddCurve.LowSlope.ballPhiData n c ∧
      Work.OddCurve.LowSlope.radonPsi n ρ c = 0 := by
  obtain ⟨c', hc'1, hc'2, hjunc⟩ := anchorData_junction_wide n hn hclass H hρ hA hB
  exact fun c hc => hjunc c ⟨hc.1, lt_trans hc.2 hc'1⟩

/-! ## The glued deviations: support, smoothness, and their Radon profile on the gap -/

/-- The first glued deviation vanishes below `tStar`. -/
private lemma deltaA_zero_left (n : ℕ) {ρ : ℝ → ℝ}
    (hwaist : ∀ u : ℝ, |u| < Work.OddEnvelope.tStar → ρ u = 1) :
    ∀ c ∈ Set.Ioo (0 : ℝ) 1, c < Work.OddEnvelope.tStar →
      Work.OddCurve.LowSlope.deltaA n ρ c = 0 := by
  intro c hc hct
  have hcpos : 0 < c := hc.1
  have hc4 : c < 4 / 5 :=
    lt_trans hct (lt_trans Work.OddCurve.LowSlope.tStar_lt_cStar
      Work.OddCurve.LowSlope.cStar_lt_four_fifths)
  rw [Work.OddCurve.LowSlope.deltaA_def, Work.OddCurve.LowSlope.GlueF]
  rw [abs_of_pos hcpos, Work.OddCurve.LowSlope.gluedPhi_of_lt hcpos.le hc4,
    Work.OddCurve.LowSlope.radonPhi_eq_ballPhiData_of_waist hwaist hcpos hct]
  ring

/-- The second glued deviation vanishes below `tStar`. -/
private lemma deltaB_zero_left (n : ℕ) {ρ : ℝ → ℝ}
    (hwaist : ∀ u : ℝ, |u| < Work.OddEnvelope.tStar → ρ u = 1) :
    ∀ c ∈ Set.Ioo (0 : ℝ) 1, c < Work.OddEnvelope.tStar →
      Work.OddCurve.LowSlope.deltaB n ρ c = 0 := by
  intro c hc hct
  have hcpos : 0 < c := hc.1
  have hc4 : c < 4 / 5 :=
    lt_trans hct (lt_trans Work.OddCurve.LowSlope.tStar_lt_cStar
      Work.OddCurve.LowSlope.cStar_lt_four_fifths)
  rw [Work.OddCurve.LowSlope.deltaB_def, Work.OddCurve.LowSlope.GlueG]
  rw [abs_of_pos hcpos, Work.OddCurve.LowSlope.gluedPsi_of_lt hcpos.le hc4,
    Work.OddCurve.LowSlope.radonPsi_eq_zero_of_waist hwaist hcpos hct]

/-- The first glued deviation vanishes above `cStar`. -/
private lemma deltaA_zero_right (n : ℕ) {ρ : ℝ → ℝ}
    (hjunc : ∀ c ∈ Set.Ioo Work.OddCurve.LowSlope.cStar (4 / 5),
      Work.OddCurve.LowSlope.radonPhi n ρ c = Work.OddCurve.LowSlope.ballPhiData n c) :
    ∀ c : ℝ, Work.OddCurve.LowSlope.cStar < c → Work.OddCurve.LowSlope.deltaA n ρ c = 0 := by
  intro c hc
  have hcpos : 0 < c := lt_trans Work.OddCurve.LowSlope.cStar_pos hc
  rw [Work.OddCurve.LowSlope.deltaA_def, Work.OddCurve.LowSlope.GlueF, abs_of_pos hcpos]
  by_cases h4 : 4 / 5 ≤ c
  · rw [Work.OddCurve.LowSlope.gluedPhi_of_ge hcpos.le h4]
    ring
  · have hlt : c < 4 / 5 := lt_of_not_ge h4
    rw [Work.OddCurve.LowSlope.gluedPhi_of_lt hcpos.le hlt, hjunc c ⟨hc, hlt⟩]
    ring

/-- The second glued deviation vanishes above `cStar`. -/
private lemma deltaB_zero_right (n : ℕ) {ρ : ℝ → ℝ}
    (hjuncB : ∀ c ∈ Set.Ioo Work.OddCurve.LowSlope.cStar (4 / 5),
      Work.OddCurve.LowSlope.radonPsi n ρ c = 0) :
    ∀ c : ℝ, Work.OddCurve.LowSlope.cStar < c → Work.OddCurve.LowSlope.deltaB n ρ c = 0 := by
  intro c hc
  have hcpos : 0 < c := lt_trans Work.OddCurve.LowSlope.cStar_pos hc
  rw [Work.OddCurve.LowSlope.deltaB_def, Work.OddCurve.LowSlope.GlueG, abs_of_pos hcpos]
  by_cases h4 : 4 / 5 ≤ c
  · rw [Work.OddCurve.LowSlope.gluedPsi_of_ge hcpos.le h4]
  · have hlt : c < 4 / 5 := lt_of_not_ge h4
    rw [Work.OddCurve.LowSlope.gluedPsi_of_lt hcpos.le hlt, hjuncB c ⟨hc, hlt⟩]

/-- The first glued deviation is `C^∞` on `(0,1)`. -/
private lemma contDiffOn_deltaA (n : ℕ) (hn : 1 ≤ n) {ρ : ℝ → ℝ}
    (hρ : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ρ (Set.Ioo (-1 : ℝ) 1))
    (hjunc : ∀ c ∈ Set.Ioo Work.OddCurve.LowSlope.cStar (4 / 5),
      Work.OddCurve.LowSlope.radonPhi n ρ c = Work.OddCurve.LowSlope.ballPhiData n c) :
    ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Work.OddCurve.LowSlope.deltaA n ρ)
      (Set.Ioo (0 : ℝ) 1) := by
  have hg : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun c : ℝ => Work.OddCurve.LowSlope.radonPhi n ρ c - Work.OddCurve.LowSlope.ballPhiData n c)
      (Set.Ioo (0 : ℝ) (4 / 5)) :=
    ((Work.OddCurve.LowSlope.contDiffOn_radonPhi_Icc n hn (b := 4 / 5) (by norm_num) hρ).mono
      (fun x hx => ⟨le_of_lt hx.1, le_of_lt hx.2⟩)).sub
      ((Work.OddCurve.LowSlope.contDiffOn_ballPhiData n hn).mono
        (fun x hx => ⟨hx.1, lt_trans hx.2 (by norm_num)⟩))
  intro x hx
  rcases lt_or_ge x (4 / 5) with hlt | hge
  · have hx45 : x ∈ Set.Ioo (0 : ℝ) (4 / 5) := ⟨hx.1, hlt⟩
    have hnb : (fun c : ℝ => Work.OddCurve.LowSlope.deltaA n ρ c)
        =ᶠ[𝓝[Set.Ioo (0 : ℝ) 1] x]
        (fun c : ℝ => Work.OddCurve.LowSlope.radonPhi n ρ c
          - Work.OddCurve.LowSlope.ballPhiData n c) := by
      filter_upwards [mem_nhdsWithin_of_mem_nhds (isOpen_Ioo.mem_nhds hx45)] with c hc
      simp only [Work.OddCurve.LowSlope.deltaA_def, Work.OddCurve.LowSlope.GlueF]
      rw [abs_of_pos hc.1, Work.OddCurve.LowSlope.gluedPhi_of_lt hc.1.le hc.2]
    refine ((hg.contDiffAt (isOpen_Ioo.mem_nhds hx45)).contDiffWithinAt).congr_of_eventuallyEq
      hnb ?_
    simp only [Work.OddCurve.LowSlope.deltaA_def, Work.OddCurve.LowSlope.GlueF]
    rw [abs_of_pos hx.1, Work.OddCurve.LowSlope.gluedPhi_of_lt hx.1.le hlt]
  · have hxcs : Work.OddCurve.LowSlope.cStar < x :=
      lt_of_lt_of_le Work.OddCurve.LowSlope.cStar_lt_four_fifths hge
    have hnb : (fun c : ℝ => Work.OddCurve.LowSlope.deltaA n ρ c)
        =ᶠ[𝓝[Set.Ioo (0 : ℝ) 1] x] 0 := by
      have hmem : Set.Ioo ((Work.OddCurve.LowSlope.cStar + x) / 2) 1
          ∈ 𝓝[Set.Ioo (0 : ℝ) 1] x :=
        mem_nhdsWithin_of_mem_nhds (isOpen_Ioo.mem_nhds
          (show x ∈ Set.Ioo ((Work.OddCurve.LowSlope.cStar + x) / 2) 1 from
            ⟨by linarith, hx.2⟩))
      filter_upwards [hmem] with c hc
      exact deltaA_zero_right n hjunc c (by linarith [hc.1])
    refine (contDiffWithinAt_const (x := x) (s := Set.Ioo (0 : ℝ) 1) (c := (0 : ℝ))).congr_of_eventuallyEq
      hnb ?_
    exact deltaA_zero_right n hjunc x hxcs


/-! ## Local smoothness of the second Radon datum -/

/-- The odd weight `u ↦ u * ρ u ^ (2n+1)` is `C^∞` on `(-1,1)`. -/
private lemma contDiffOn_weight (n : ℕ) {ρ : ℝ → ℝ}
    (hρ : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ρ (Set.Ioo (-1 : ℝ) 1)) :
    ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun u : ℝ => u * ρ u ^ (2 * n + 1))
      (Set.Ioo (-1 : ℝ) 1) :=
  contDiffOn_id.mul (hρ.pow (2 * n + 1))

/-- The trigonometric form of `radonPsi`, valid for every `c`. -/
private lemma radonPsi_eq_cos (n : ℕ) (hn : 1 ≤ n) (ρ : ℝ → ℝ) (c : ℝ) :
    Work.OddCurve.LowSlope.radonPsi n ρ c
      = Work.OddRadon.sphereArea (2 * n - 2) *
        (∫ θ in (-(Real.pi / 2))..(Real.pi / 2),
          Real.cos θ ^ (2 * n - 2) * ((c * Real.sin θ) * ρ (c * Real.sin θ) ^ (2 * n + 1))) := by
  rw [Work.OddCurve.LowSlope.radonPsi,
    Work.OddCurve.LowSlope.radonProfile_eq_cos_any n hn (fun u : ℝ => u * ρ u ^ (2 * n + 1)) c]

/-- **The second Radon datum is `C^∞` on `[0,b]`** for every `b < 1`, from `ρ ∈ C^∞(-1,1)`
alone (the analogue of `Work.OddCurve.LowSlope.contDiffOn_radonPhi_Icc`). -/
private lemma contDiffOn_radonPsi_Icc (n : ℕ) (hn : 1 ≤ n) {ρ : ℝ → ℝ} {b : ℝ}
    (hb : b < 1) (hρ : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ρ (Set.Ioo (-1 : ℝ) 1)) :
    ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun c : ℝ => Work.OddCurve.LowSlope.radonPsi n ρ c) (Set.Icc 0 b) := by
  rw [contDiffOn_infty]
  intro N
  refine contDiffOn_of_locally_contDiffOn (fun x hx => ?_)
  obtain ⟨hx0, hxb⟩ := hx
  have hx1 : x < 1 := lt_of_le_of_lt hxb hb
  set R : ℝ := (x + 1) / 2 with hR
  have hxR : x < R := by rw [hR]; linarith
  have hR1 : R < 1 := by rw [hR]; linarith
  have hRpos : 0 < R := by rw [hR]; linarith
  refine ⟨Set.Ioo (-R) R, isOpen_Ioo, ⟨by linarith, hxR⟩, ?_⟩
  have hsub : Set.Icc (-R) R ⊆ Set.Ioo (-1 : ℝ) 1 := fun t ht =>
    ⟨by linarith [ht.1, hR1], by linarith [ht.2, hR1]⟩
  have hγ : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun u : ℝ => u * ρ u ^ (2 * n + 1)) (Set.Ioo (-1 : ℝ) 1) := contDiffOn_weight n hρ
  have hγR : ContDiffOn ℝ ((N : ℕ∞) : WithTop ℕ∞)
      (fun u : ℝ => u * ρ u ^ (2 * n + 1)) (Set.Icc (-R) R) :=
    (hγ.mono hsub).of_le (by exact_mod_cast (le_top : (N : ℕ∞) ≤ (⊤ : ℕ∞)))
  obtain ⟨G, hGsm, hGeq⟩ : ∃ G : ℝ → ℝ, ContDiff ℝ ((N : ℕ∞) : WithTop ℕ∞) G ∧
      Set.EqOn G (fun u : ℝ => u * ρ u ^ (2 * n + 1)) (Set.Icc (-R) R) :=
    ⟨Commons.Analysis.Calculus.taylorExtend (fun u : ℝ => u * ρ u ^ (2 * n + 1)) N (-R) R,
      Commons.Analysis.Calculus.contDiff_taylorExtend N (by linarith) hγR,
      Commons.Analysis.Calculus.taylorExtend_eqOn_Icc⟩
  set F : ℝ → ℝ → ℝ := fun c θ => Real.cos θ ^ (2 * n - 2) * G (c * Real.sin θ) with hF
  have hFsm : ContDiff ℝ ((N : ℕ∞) : WithTop ℕ∞) (fun p : ℝ × ℝ => F p.1 p.2) := by
    rw [hF]
    exact ((Real.contDiff_cos.comp contDiff_snd).pow (2 * n - 2)).mul
      (hGsm.comp (contDiff_fst.mul (Real.contDiff_sin.comp contDiff_snd)))
  have hK : ContDiff ℝ ((N : ℕ∞) : WithTop ℕ∞)
      (fun c : ℝ => ∫ θ in (-(Real.pi / 2))..(Real.pi / 2), F c θ) :=
    Work.Analysis.Calculus.contDiff_intervalIntegral_fixed N hFsm
  refine ((hK.const_smul (Work.OddRadon.sphereArea (2 * n - 2))).contDiffOn).congr
    (fun c hc => ?_)
  obtain ⟨hc1, hc2⟩ := hc
  have hcR : c < R := hc2.2
  rw [radonPsi_eq_cos n hn ρ c]
  congr 1
  apply intervalIntegral.integral_congr
  intro θ _
  rw [hF]
  simp only []
  have hsin : |Real.sin θ| ≤ 1 := by
    rw [abs_le]; exact ⟨Real.neg_one_le_sin θ, Real.sin_le_one θ⟩
  have hcabs : |c| < R := abs_lt.mpr ⟨hc2.1, hc2.2⟩
  have hle : |c * Real.sin θ| ≤ R := by
    rw [abs_mul]
    calc |c| * |Real.sin θ| ≤ R * 1 :=
          mul_le_mul (le_of_lt hcabs) hsin (abs_nonneg _) (le_of_lt hRpos)
      _ = R := by ring
  rw [hGeq (Set.mem_Icc.mpr ⟨neg_le_of_abs_le hle, le_of_abs_le hle⟩)]

/-- The second glued deviation is `C^∞` on `(0,1)`. -/
private lemma contDiffOn_deltaB (n : ℕ) (hn : 1 ≤ n) {ρ : ℝ → ℝ}
    (hρ : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ρ (Set.Ioo (-1 : ℝ) 1))
    (hjuncB : ∀ c ∈ Set.Ioo Work.OddCurve.LowSlope.cStar (4 / 5),
      Work.OddCurve.LowSlope.radonPsi n ρ c = 0) :
    ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Work.OddCurve.LowSlope.deltaB n ρ)
      (Set.Ioo (0 : ℝ) 1) := by
  have hg : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun c : ℝ => Work.OddCurve.LowSlope.radonPsi n ρ c) (Set.Ioo (0 : ℝ) (4 / 5)) :=
    (contDiffOn_radonPsi_Icc n hn (b := 4 / 5) (by norm_num) hρ).mono
      (fun x hx => ⟨le_of_lt hx.1, le_of_lt hx.2⟩)
  intro x hx
  rcases lt_or_ge x (4 / 5) with hlt | hge
  · have hx45 : x ∈ Set.Ioo (0 : ℝ) (4 / 5) := ⟨hx.1, hlt⟩
    have hnb : (fun c : ℝ => Work.OddCurve.LowSlope.deltaB n ρ c)
        =ᶠ[𝓝[Set.Ioo (0 : ℝ) 1] x] (fun c : ℝ => Work.OddCurve.LowSlope.radonPsi n ρ c) := by
      filter_upwards [mem_nhdsWithin_of_mem_nhds (isOpen_Ioo.mem_nhds hx45)] with c hc
      simp only [Work.OddCurve.LowSlope.deltaB_def, Work.OddCurve.LowSlope.GlueG]
      rw [abs_of_pos hc.1, Work.OddCurve.LowSlope.gluedPsi_of_lt hc.1.le hc.2]
    refine ((hg.contDiffAt (isOpen_Ioo.mem_nhds hx45)).contDiffWithinAt).congr_of_eventuallyEq
      hnb ?_
    simp only [Work.OddCurve.LowSlope.deltaB_def, Work.OddCurve.LowSlope.GlueG]
    rw [abs_of_pos hx.1, Work.OddCurve.LowSlope.gluedPsi_of_lt hx.1.le hlt]
  · have hxcs : Work.OddCurve.LowSlope.cStar < x :=
      lt_of_lt_of_le Work.OddCurve.LowSlope.cStar_lt_four_fifths hge
    have hnb : (fun c : ℝ => Work.OddCurve.LowSlope.deltaB n ρ c)
        =ᶠ[𝓝[Set.Ioo (0 : ℝ) 1] x] 0 := by
      have hmem : Set.Ioo ((Work.OddCurve.LowSlope.cStar + x) / 2) 1
          ∈ 𝓝[Set.Ioo (0 : ℝ) 1] x :=
        mem_nhdsWithin_of_mem_nhds (isOpen_Ioo.mem_nhds
          (show x ∈ Set.Ioo ((Work.OddCurve.LowSlope.cStar + x) / 2) 1 from
            ⟨by linarith, hx.2⟩))
      filter_upwards [hmem] with c hc
      exact deltaB_zero_right n hjuncB c (by linarith [hc.1])
    refine (contDiffWithinAt_const (x := x) (s := Set.Ioo (0 : ℝ) 1) (c := (0 : ℝ))).congr_of_eventuallyEq
      hnb ?_
    exact deltaB_zero_right n hjuncB x hxcs

/-! ## The cap identity for the glued deviation, and its value at `4/5` -/

/-- On the cap `(0,4/5)` the inverse of the first glued deviation is the anchor's power
combination: `2 R_A(c)/c² = ρ(c)^{2n+2} + ρ(-c)^{2n+2} - 2`. -/
private lemma two_mul_radonInverse_deltaA_cap (n : ℕ) (hn : 1 ≤ n) {ρ : ℝ → ℝ}
    (hρ : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ρ (Set.Ioo (-1 : ℝ) 1)) :
    ∀ c ∈ Set.Ioo (0 : ℝ) (4 / 5),
      2 * Work.OddRadon.radonInverse n (Work.OddCurve.LowSlope.deltaA n ρ) c / c ^ 2
        = ρ c ^ (2 * n + 2) + ρ (-c) ^ (2 * n + 2) - 2 := by
  intro c hc
  have hc4 : c < 1 := lt_trans hc.2 (by norm_num)
  have hcos : Real.cos (Real.arccos c) = c := Real.cos_arccos (by linarith [hc.1]) hc4.le
  have hcos_lt : Real.cos (Real.arccos c) < 4 / 5 := by rw [hcos]; exact hc.2
  have hcos_pos : 0 < Real.cos (Real.arccos c) := by rw [hcos]; exact hc.1
  have h := Work.OddVolterra.Free.glueA_eq_inversion n hn hρ (Real.arccos c) hcos_pos
    (ne_of_lt hcos_lt)
  rw [Work.OddCurve.LowSlope.glueA_of_lt hcos_lt, hcos] at h
  exact h.symm

/-- **The value at `4/5`**: `2 R_A(4/5)/(4/5)²` is the anchor's power combination there. -/
private lemma two_mul_radonInverse_deltaA_at (n : ℕ) (hn : 1 ≤ n) {ρ : ℝ → ℝ}
    (hρ : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ρ (Set.Ioo (-1 : ℝ) 1))
    (hcont : ContinuousAt
      (fun c : ℝ => 2 * Work.OddRadon.radonInverse n (Work.OddCurve.LowSlope.deltaA n ρ) c / c ^ 2)
      (4 / 5)) :
    2 * Work.OddRadon.radonInverse n (Work.OddCurve.LowSlope.deltaA n ρ) (4 / 5) / (4 / 5) ^ 2
      = ρ (4 / 5) ^ (2 * n + 2) + ρ (-(4 / 5)) ^ (2 * n + 2) - 2 := by
  have hcap := two_mul_radonInverse_deltaA_cap n hn hρ
  -- the two one-sided limits
  have htend1 : Filter.Tendsto
      (fun c : ℝ => 2 * Work.OddRadon.radonInverse n (Work.OddCurve.LowSlope.deltaA n ρ) c / c ^ 2)
      (𝓝[<] (4 / 5))
      (𝓝 (2 * Work.OddRadon.radonInverse n (Work.OddCurve.LowSlope.deltaA n ρ) (4 / 5) / (4 / 5) ^ 2)) :=
    hcont.tendsto.mono_left nhdsWithin_le_nhds
  have htend2 : Filter.Tendsto
      (fun c : ℝ => 2 * Work.OddRadon.radonInverse n (Work.OddCurve.LowSlope.deltaA n ρ) c / c ^ 2)
      (𝓝[<] (4 / 5))
      (𝓝 (ρ (4 / 5) ^ (2 * n + 2) + ρ (-(4 / 5)) ^ (2 * n + 2) - 2)) := by
    have hcontG : ContinuousAt
        (fun c : ℝ => ρ c ^ (2 * n + 2) + ρ (-c) ^ (2 * n + 2) - 2) (4 / 5) := by
      have h1 : ContinuousAt ρ (4 / 5) :=
        hρ.continuousOn.continuousAt (isOpen_Ioo.mem_nhds (by norm_num))
      have h2 : ContinuousAt ρ (-(4 / 5)) :=
        hρ.continuousOn.continuousAt (isOpen_Ioo.mem_nhds (by norm_num))
      exact ((h1.pow _).add ((h2.comp continuous_neg.continuousAt).pow _)).sub continuousAt_const
    have heq : (fun c : ℝ => 2 * Work.OddRadon.radonInverse n (Work.OddCurve.LowSlope.deltaA n ρ) c / c ^ 2)
        =ᶠ[𝓝[<] (4 / 5)] (fun c : ℝ => ρ c ^ (2 * n + 2) + ρ (-c) ^ (2 * n + 2) - 2) := by
      filter_upwards [mem_nhdsWithin_of_mem_nhds (isOpen_Ioi.mem_nhds (by norm_num : (0:ℝ) < 4 / 5)),
        self_mem_nhdsWithin] with c hc1 hc2
      exact hcap c ⟨hc1, hc2⟩
    exact Filter.Tendsto.congr' heq.symm (hcontG.tendsto.mono_left nhdsWithin_le_nhds)
  exact tendsto_nhds_unique htend1 htend2

/-- **The value of `glueA` at `arccos(4/5)`**, from the junction past `4/5`. -/
private lemma glueA_at_arccos (n : ℕ) (hn : 1 ≤ n) {ρ : ℝ → ℝ}
    (hρ : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ρ (Set.Ioo (-1 : ℝ) 1))
    {c' : ℝ} (hc'1 : 4 / 5 < c') (hc'2 : c' < 1)
    (hjunc : ∀ c ∈ Set.Ioo Work.OddCurve.LowSlope.cStar c',
      Work.OddCurve.LowSlope.radonPhi n ρ c = Work.OddCurve.LowSlope.ballPhiData n c) :
    Work.OddCurve.LowSlope.glueA n ρ (Real.arccos (4 / 5))
      = ρ (4 / 5) ^ (2 * n + 2) + ρ (-(4 / 5)) ^ (2 * n + 2) - 2 := by
  have hcos : Real.cos (Real.arccos (4 / 5)) = 4 / 5 := Real.cos_arccos (by norm_num) (by norm_num)
  -- `GlueF = radonPhi` on `(0,c')`, hence the two inverses agree at `4/5`
  have hGeq : Set.EqOn (Work.OddCurve.LowSlope.GlueF n ρ) (Work.OddCurve.LowSlope.radonPhi n ρ)
      (Set.Ioo (0 : ℝ) c') := by
    intro c hc
    rw [Work.OddCurve.LowSlope.GlueF]
    rcases lt_or_ge c (4 / 5) with hlt | hge
    · rw [abs_of_pos hc.1, Work.OddCurve.LowSlope.gluedPhi_of_lt hc.1.le hlt]
    · have hcS : Work.OddCurve.LowSlope.cStar < c :=
        lt_of_lt_of_le Work.OddCurve.LowSlope.cStar_lt_four_fifths hge
      rw [abs_of_pos hc.1, Work.OddCurve.LowSlope.gluedPhi_of_ge hc.1.le hge,
        (hjunc c ⟨hcS, hc.2⟩).symm]
  have hRloc : Work.OddRadon.radonInverse n (Work.OddCurve.LowSlope.GlueF n ρ) (4 / 5)
      = Work.OddRadon.radonInverse n (Work.OddCurve.LowSlope.radonPhi n ρ) (4 / 5) :=
    Work.OddCurve.LowSlope.radonInverse_congr_of_eqOn (n := n) (u := 4 / 5) (b := c')
      (by norm_num) hc'1 hGeq
  have hge : ¬ (Real.cos (Real.arccos (4 / 5)) < 4 / 5) := by rw [hcos]; norm_num
  rw [Work.OddCurve.LowSlope.glueA, if_neg hge, Work.OddCurve.LowSlope.GlueA,
    Work.OddCurve.LowSlope.GluePhi, hcos, hRloc,
    Work.OddRadon.radonInverse_radonPhi_local n hn (c₁ := c') hc'2 hρ (by norm_num) hc'1]
  field_simp

/-! ## The main estimate -/

theorem glueDataBounds (n : ℕ) (hn : 1 ≤ n) :
    ∃ K : ℝ, 0 < K ∧ ∀ {ε C₁ : ℝ} {h X Y ρ : ℝ → ℝ},
      0 < ε → C₁ * ε ≤ 1 →
      Work.OddVolterra.Free.IsSmallFlatBumpClass n (2 * n + 2) ε h →
      h ≠ 0 →
      Work.OddEnvelope.IsEnvelopeCurve h X Y →
      Work.OddCurve.LowSlope.CloseToProfileX X →
      Work.OddCurve.LowSlope.CloseToProfileX Y →
      (∀ s : ℝ, 1 - 3 * Work.OddVolterra.tau < s → s ≤ 1 →
        Work.OddCurve.momentA n h X Y (Work.OddEnvelope.envelopeProfile h X Y) s =
          Work.OddCurve.refConst n / Real.sqrt (1 + s ^ 2)) →
      (∀ s : ℝ, 1 - 3 * Work.OddVolterra.tau < s → s ≤ 1 →
        Work.OddCurve.momentB n h X Y (Work.OddEnvelope.envelopeProfile h X Y) s = 0) →
      Work.OddVolterra.Free.IsAnchorRadial h X Y ρ →
      (∀ u : ℝ, |u| < 4 / 5 →
        |ρ u - 1| ≤ C₁ * ε ∧ |deriv ρ u| ≤ C₁ * ε ∧ |deriv (deriv ρ) u| ≤ C₁ * ε) →
      ∀ α ∈ Set.Icc (0 : ℝ) (Real.pi / 2),
        |Work.OddCurve.LowSlope.glueA n ρ α| ≤ K * (C₁ + 1) * ε ∧
        |Work.OddCurve.LowSlope.glueB n ρ α| ≤ K * (C₁ + 1) * ε ∧
        |deriv (Work.OddCurve.LowSlope.glueA n ρ) α| ≤ K * (C₁ + 1) * ε ∧
        |deriv (deriv (Work.OddCurve.LowSlope.glueA n ρ)) α| ≤ K * (C₁ + 1) * ε ∧
        |deriv (Work.OddCurve.LowSlope.glueB n ρ) α| ≤ K * (C₁ + 1) * ε ∧
        |deriv (deriv (Work.OddCurve.LowSlope.glueB n ρ)) α| ≤ K * (C₁ + 1) * ε := by
  obtain ⟨KN, hKNpos, hKN⟩ := nearRegionGlueBounds n hn
  obtain ⟨KF, hKFpos, hKF⟩ := farRegionGlueBounds
  obtain ⟨CG, hCGpos, hCG⟩ := gap_inversion_bounds_free n hn
  set Cn : ℝ := ((2 * n + 2 : ℕ) : ℝ) * 2 ^ (2 * n + 2) with hCndef
  have hCn0 : (0 : ℝ) < Cn := by rw [hCndef]; positivity
  have hCn0' : (0 : ℝ) ≤ Cn := hCn0.le
  set K : ℝ := max KN (KF * CG * Cn) + 1 with hKdef
  have hKpos : 0 < K := by
    rw [hKdef]
    have h1 : (0 : ℝ) ≤ max KN (KF * CG * Cn) := le_trans hKNpos.le (le_max_left _ _)
    linarith
  refine ⟨K, hKpos, ?_⟩
  · intro ε C₁ h X Y ρ hε hCε hclass hne H hcX hcY hA hB hρ hρc α hα
    obtain ⟨hρpos, hρsm, hρmono, hgraph, hρ0⟩ := hρ
    obtain ⟨hbound, hwaist⟩ := anchorRadial_waist H ⟨hρpos, hρsm, hρmono, hgraph, hρ0⟩
    obtain ⟨c', hc'1, hc'2, hjuncW⟩ := anchorData_junction_wide n hn hclass H
      ⟨hρpos, hρsm, hρmono, hgraph, hρ0⟩ hA hB
    have hjuncA : ∀ c ∈ Set.Ioo Work.OddCurve.LowSlope.cStar (4 / 5),
        Work.OddCurve.LowSlope.radonPhi n ρ c = Work.OddCurve.LowSlope.ballPhiData n c :=
      fun c hc => (hjuncW c ⟨hc.1, lt_trans hc.2 hc'1⟩).1
    have hjuncB : ∀ c ∈ Set.Ioo Work.OddCurve.LowSlope.cStar (4 / 5),
        Work.OddCurve.LowSlope.radonPsi n ρ c = 0 :=
      fun c hc => (hjuncW c ⟨hc.1, lt_trans hc.2 hc'1⟩).2
    have hjuncW' : ∀ c ∈ Set.Ioo Work.OddCurve.LowSlope.cStar c',
        Work.OddCurve.LowSlope.radonPhi n ρ c = Work.OddCurve.LowSlope.ballPhiData n c :=
      fun c hc => (hjuncW c hc).1
    -- the deviations
    have hδAsm : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Work.OddCurve.LowSlope.deltaA n ρ)
        (Set.Ioo (0 : ℝ) 1) := contDiffOn_deltaA n hn hρsm hjuncA
    have hδAl : ∀ c ∈ Set.Ioo (0 : ℝ) 1, c < Work.OddEnvelope.tStar →
        Work.OddCurve.LowSlope.deltaA n ρ c = 0 := deltaA_zero_left n hwaist
    have hδAr : ∀ c : ℝ, Work.OddCurve.LowSlope.cStar < c →
        Work.OddCurve.LowSlope.deltaA n ρ c = 0 := deltaA_zero_right n hjuncA
    have hδBsm : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Work.OddCurve.LowSlope.deltaB n ρ)
        (Set.Ioo (0 : ℝ) 1) := contDiffOn_deltaB n hn hρsm hjuncB
    have hδBl : ∀ c ∈ Set.Ioo (0 : ℝ) 1, c < Work.OddEnvelope.tStar →
        Work.OddCurve.LowSlope.deltaB n ρ c = 0 := deltaB_zero_left n hwaist
    have hδBr : ∀ c : ℝ, Work.OddCurve.LowSlope.cStar < c →
        Work.OddCurve.LowSlope.deltaB n ρ c = 0 := deltaB_zero_right n hjuncB
    -- the size of the deviations
    have hδ0 : (0 : ℝ) ≤ C₁ * ε := by
      have h := (hρc 0 (by norm_num : |(0 : ℝ)| < 4 / 5)).1
      rw [hρ0] at h
      simpa using h
    set M : ℝ := Cn * (C₁ * ε) with hMdef
    have hM0 : (0 : ℝ) ≤ M := by rw [hMdef, hCndef]; positivity
    -- the profile deviation bounds
    have hγAeven : Function.Even (Work.OddCurve.LowSlope.gammaDev n ρ) :=
      Work.OddCurve.LowSlope.gammaDev_even n ρ
    have hγAsm : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Work.OddCurve.LowSlope.gammaDev n ρ)
        (Set.Ioo (0 : ℝ) 1) := by
      have h1 : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun u : ℝ => ρ u ^ (2 * n + 2))
          (Set.Ioo (0 : ℝ) 1) :=
        (hρsm.pow _).mono (fun x hx => ⟨by linarith [hx.1], hx.2⟩)
      have h2 : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun u : ℝ => ρ (-u) ^ (2 * n + 2))
          (Set.Ioo (0 : ℝ) 1) := by
        have hcomp : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun u : ℝ => ρ (-u))
            (Set.Ioo (0 : ℝ) 1) :=
          hρsm.comp (by fun_prop) (fun x hx => ⟨by linarith [hx.2], by linarith [hx.1]⟩)
        exact hcomp.pow _
      have h3 : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun u : ℝ => u ^ 2) (Set.Ioo (0 : ℝ) 1) :=
        (contDiffOn_id.pow 2)
      have h4 : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
          (fun u : ℝ => (ρ u ^ (2 * n + 2) + ρ (-u) ^ (2 * n + 2)) / 2 - 1) (Set.Ioo (0 : ℝ) 1) :=
        ((h1.add h2).div_const 2).sub contDiffOn_const
      exact h3.mul h4
    have hγAb : ∀ c ∈ Set.Ioo (0 : ℝ) Work.OddCurve.LowSlope.cStar,
        |Work.OddCurve.LowSlope.gammaDev n ρ c| ≤ M := by
      intro c hc
      have hcabs : |c| ≤ 1 := by
        rw [abs_of_pos hc.1]
        linarith [hc.2, Work.OddCurve.LowSlope.cStar_lt_four_fifths]
      have hclt : |c| < 4 / 5 := by
        rw [abs_of_pos hc.1]
        linarith [hc.2, Work.OddCurve.LowSlope.cStar_lt_four_fifths]
      have hc' : |(-c)| < 4 / 5 := by rw [abs_neg]; exact hclt
      have := gammaDev_abs_le n hcabs (hρc c hclt).1 (hρc (-c) hc').1 hCε
      rw [hMdef, hCndef]
      exact this
    have hγBeven : Function.Even (Work.OddCurve.LowSlope.gammaPsi n ρ) :=
      Work.OddCurve.LowSlope.gammaPsi_even n ρ
    have hγBsm : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Work.OddCurve.LowSlope.gammaPsi n ρ)
        (Set.Ioo (0 : ℝ) 1) := by
      have h1 : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun u : ℝ => u * ρ u ^ (2 * n + 1))
          (Set.Ioo (0 : ℝ) 1) :=
        (contDiffOn_id.mul (hρsm.pow _)).mono (fun x hx => ⟨by linarith [hx.1], hx.2⟩)
      have h2 : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun u : ℝ => (-u) * ρ (-u) ^ (2 * n + 1))
          (Set.Ioo (0 : ℝ) 1) := by
        have hcomp : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun u : ℝ => ρ (-u))
            (Set.Ioo (0 : ℝ) 1) :=
          hρsm.comp (by fun_prop) (fun x hx => ⟨by linarith [hx.2], by linarith [hx.1]⟩)
        have h3 : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun u : ℝ => (-u)) (Set.Ioo (0 : ℝ) 1) := by
          fun_prop
        exact h3.mul (hcomp.pow _)
      have h4 : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
          (fun u : ℝ => (u * ρ u ^ (2 * n + 1) + (-u) * ρ (-u) ^ (2 * n + 1)) / 2)
          (Set.Ioo (0 : ℝ) 1) :=
        ((h1.add h2).div_const 2)
      refine h4.congr ?_
      intro x hx
      simp only [Work.OddCurve.LowSlope.gammaPsi]
      ring
    have hγBb : ∀ c ∈ Set.Ioo (0 : ℝ) Work.OddCurve.LowSlope.cStar,
        |Work.OddCurve.LowSlope.gammaPsi n ρ c| ≤ M := by
      intro c hc
      have hcabs : |c| ≤ 1 := by
        rw [abs_of_pos hc.1]
        linarith [hc.2, Work.OddCurve.LowSlope.cStar_lt_four_fifths]
      have hclt : |c| < 4 / 5 := by
        rw [abs_of_pos hc.1]
        linarith [hc.2, Work.OddCurve.LowSlope.cStar_lt_four_fifths]
      have hc' : |(-c)| < 4 / 5 := by rw [abs_neg]; exact hclt
      have := gammaPsi_abs_le n hcabs (hρc c hclt).1 (hρc (-c) hc').1 hCε
      rw [hMdef, hCndef]
      exact this
    -- the cap identities
    have hδAid : ∀ c ∈ Set.Ioo (0 : ℝ) Work.OddCurve.LowSlope.cStar,
        Work.OddCurve.LowSlope.deltaA n ρ c
          = Work.OddRadon.radonProfile (2 * n + 1) (Work.OddCurve.LowSlope.gammaDev n ρ) c :=
      fun c hc => deltaA_eq_radonProfile_cap n hn hρsm c
        ⟨hc.1, lt_trans hc.2 Work.OddCurve.LowSlope.cStar_lt_four_fifths⟩
    have hδBid : ∀ c ∈ Set.Ioo (0 : ℝ) Work.OddCurve.LowSlope.cStar,
        Work.OddCurve.LowSlope.deltaB n ρ c
          = Work.OddRadon.radonProfile (2 * n + 1) (Work.OddCurve.LowSlope.gammaPsi n ρ) c :=
      fun c hc => deltaB_eq_radonProfile_cap n hn hρsm c
        ⟨hc.1, lt_trans hc.2 Work.OddCurve.LowSlope.cStar_lt_four_fifths⟩
    -- the gap bounds
    have hgapA := hCG (Work.OddCurve.LowSlope.gammaDev n ρ) (Work.OddCurve.LowSlope.deltaA n ρ)
      Work.OddCurve.LowSlope.cStar M Work.OddCurve.LowSlope.cStar_pos le_rfl hM0 hγAeven hγAsm
      hδAsm hγAb hδAl (fun c _ hc => hδAr c hc) hδAid
    have hgapB := hCG (Work.OddCurve.LowSlope.gammaPsi n ρ) (Work.OddCurve.LowSlope.deltaB n ρ)
      Work.OddCurve.LowSlope.cStar M Work.OddCurve.LowSlope.cStar_pos le_rfl hM0 hγBeven hγBsm
      hδBsm hγBb hδBl (fun c _ hc => hδBr c hc) hδBid
    -- differentiability of the two inverses
    have hdiffA := radonInverseGapDeriv n hn (δ := Work.OddCurve.LowSlope.deltaA n ρ)
      (m := Work.OddEnvelope.tStar) (M' := Work.OddCurve.LowSlope.cStar)
      Work.OddEnvelope.tStar_pos Work.OddCurve.LowSlope.tStar_lt_cStar.le
      Work.OddVolterra.Free.cStar_lt_79 hδAsm hδAl hδAr
    have hdiffB := radonInverseGapDeriv n hn (δ := Work.OddCurve.LowSlope.deltaB n ρ)
      (m := Work.OddEnvelope.tStar) (M' := Work.OddCurve.LowSlope.cStar)
      Work.OddEnvelope.tStar_pos Work.OddCurve.LowSlope.tStar_lt_cStar.le
      Work.OddVolterra.Free.cStar_lt_79 hδBsm hδBl hδBr
    -- constant bookkeeping
    have hKNleK : KN ≤ K := by rw [hKdef]; linarith [le_max_left KN (KF * CG * Cn)]
    have hKFKleK : KF * CG * Cn ≤ K := by rw [hKdef]; linarith [le_max_right KN (KF * CG * Cn)]
    have hC1nonneg : (0 : ℝ) ≤ C₁ := nonneg_of_mul_nonneg_left hδ0 hε
    have hCε1 : (0 : ℝ) ≤ (C₁ + 1) * ε := mul_nonneg (by linarith) hε.le
    -- the case split
    rcases le_or_gt α (Real.arccos (4 / 5)) with hfar | hnear
    · -- FAR: `4 / 5 ≤ cos α`
      have hα0 : 0 ≤ α := hα.1
      have hcosge : 4 / 5 ≤ Real.cos α := by
        have h := Real.cos_le_cos_of_nonneg_of_le_pi (x := α) (y := Real.arccos (4 / 5))
          hα0 (Real.arccos_le_pi _) hfar
        rwa [Real.cos_arccos (by norm_num) (by norm_num)] at h
      have harccos_lt : Real.arccos (4 / 5) < Real.pi / 2 := by
        have hmem1 : Real.pi / 2 ∈ Set.Icc (0 : ℝ) Real.pi :=
          ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
        have hmem2 : Real.arccos (4 / 5) ∈ Set.Icc (0 : ℝ) Real.pi :=
          ⟨Real.arccos_nonneg _, Real.arccos_le_pi _⟩
        exact (Real.strictAntiOn_cos.lt_iff_gt hmem1 hmem2).mp
          (by rw [Real.cos_pi_div_two, Real.cos_arccos (by norm_num) (by norm_num)]; norm_num)
      have hαlt : α < Real.pi / 2 := lt_of_le_of_lt hfar harccos_lt
      set RA : ℝ → ℝ :=
        fun u => Work.OddRadon.radonInverse n (Work.OddCurve.LowSlope.deltaA n ρ) u with hRA
      set RB : ℝ → ℝ :=
        fun u => Work.OddRadon.radonInverse n (Work.OddCurve.LowSlope.GlueG n ρ) u with hRB
      have hmemu : Real.cos α ∈ Set.Icc (4 / 5 : ℝ) 1 := ⟨hcosge, Real.cos_le_one α⟩
      have hRv : |RA (Real.cos α)| ≤ CG * M := (hgapA (Real.cos α) hmemu).1
      have hRv' : |deriv RA (Real.cos α)| ≤ CG * M := (hgapA (Real.cos α) hmemu).2.1
      have hRv'' : |deriv (deriv RA) (Real.cos α)| ≤ CG * M := (hgapA (Real.cos α) hmemu).2.2
      have hSv : |RB (Real.cos α)| ≤ CG * M := (hgapB (Real.cos α) hmemu).1
      have hSv' : |deriv RB (Real.cos α)| ≤ CG * M := (hgapB (Real.cos α) hmemu).2.1
      have hSv'' : |deriv (deriv RB) (Real.cos α)| ≤ CG * M := (hgapB (Real.cos α) hmemu).2.2
      have hRd : DifferentiableAt ℝ RA (Real.cos α) := (hdiffA (Real.cos α) hmemu).1
      have hRd' : DifferentiableAt ℝ (deriv RA) (Real.cos α) := (hdiffA (Real.cos α) hmemu).2
      have hSd : DifferentiableAt ℝ RB (Real.cos α) := (hdiffB (Real.cos α) hmemu).1
      have hSd' : DifferentiableAt ℝ (deriv RB) (Real.cos α) := (hdiffB (Real.cos α) hmemu).2
      have hga : (Work.OddCurve.LowSlope.glueA n ρ) =ᶠ[𝓝 α]
          (fun β : ℝ => 2 * RA (Real.cos β) / Real.cos β ^ 2) := by
        rcases lt_or_eq_of_le hfar with hlt | heq
        · have hcgt : 4 / 5 < Real.cos α := by
            have h := Real.cos_lt_cos_of_nonneg_of_le_pi (x := α) (y := Real.arccos (4 / 5))
              hα0 (Real.arccos_le_pi _) hlt
            rwa [Real.cos_arccos (by norm_num) (by norm_num)] at h
          filter_upwards [(isOpen_lt continuous_const Real.continuous_cos).mem_nhds hcgt]
            with β hβ
          exact Work.OddVolterra.Free.glueA_eq_inversion n hn hρsm β (by linarith)
            (by intro hcon; rw [hcon] at hβ; norm_num at hβ)
        · have hcosα : Real.cos α = 4 / 5 := by
            rw [heq, Real.cos_arccos (by norm_num) (by norm_num)]
          have hαpos : 0 < α := by rw [heq]; exact Real.arccos_pos.mpr (by norm_num)
          set δ : ℝ := min (α / 2) ((Real.pi / 2 - α) / 2) with hδdef
          have hδle1 : δ ≤ α / 2 := by rw [hδdef]; exact min_le_left _ _
          have hδle2 : δ ≤ (Real.pi / 2 - α) / 2 := by rw [hδdef]; exact min_le_right _ _
          have hδpos : 0 < δ := by rw [hδdef]; exact lt_min (by linarith) (by linarith)
          have hmemI : Set.Ioo (α - δ) (α + δ) ∈ 𝓝 α :=
            isOpen_Ioo.mem_nhds ⟨sub_lt_self α hδpos, lt_add_of_pos_right α hδpos⟩
          have hαmem : α ∈ Set.Icc (0 : ℝ) Real.pi :=
            ⟨hαpos.le, by linarith [hαlt, Real.pi_pos]⟩
          have hcont : ContinuousAt (fun c : ℝ => 2 * RA c / c ^ 2) (4 / 5) := by
            have h1 : ContinuousAt RA (4 / 5) :=
              ((hdiffA (4 / 5) ⟨le_rfl, by norm_num⟩).1).continuousAt
            exact (continuousAt_const.mul h1).div (continuousAt_id.pow 2) (by norm_num)
          filter_upwards [hmemI] with β hβ
          rw [Set.mem_Ioo] at hβ
          have hβ0 : 0 < β := by linarith [hβ.1, hδle1, hαpos]
          have hβlt : β < Real.pi / 2 := by linarith [hβ.2, hδle2, hαlt]
          have hβmem : β ∈ Set.Icc (0 : ℝ) Real.pi :=
            ⟨hβ0.le, by linarith [hβlt, Real.pi_pos]⟩
          by_cases hb : β = α
          · rw [hb]
            have h1 : Work.OddCurve.LowSlope.glueA n ρ α
                = ρ (4 / 5) ^ (2 * n + 2) + ρ (-(4 / 5)) ^ (2 * n + 2) - 2 := by
              rw [heq]
              exact glueA_at_arccos n hn hρsm hc'1 hc'2 hjuncW'
            have h2 : 2 * RA (Real.cos α) / Real.cos α ^ 2
                = ρ (4 / 5) ^ (2 * n + 2) + ρ (-(4 / 5)) ^ (2 * n + 2) - 2 := by
              rw [hcosα]
              exact two_mul_radonInverse_deltaA_at n hn hρsm hcont
            exact h1.trans h2.symm
          · have hcb : Real.cos β ≠ 4 / 5 := by
              intro hcon
              exact hb (Real.injOn_cos hβmem hαmem (by rw [hcon, hcosα]))
            have hβcos : 0 < Real.cos β := Real.cos_pos_of_mem_Ioo ⟨by linarith [hβ0], hβlt⟩
            rcases lt_or_gt_of_ne hcb with hlt' | hgt'
            · rw [Work.OddCurve.LowSlope.glueA_of_lt hlt',
                show RA (Real.cos β)
                  = Work.OddRadon.radonInverse n (Work.OddCurve.LowSlope.deltaA n ρ) (Real.cos β)
                  from rfl]
              exact (two_mul_radonInverse_deltaA_cap n hn hρsm (Real.cos β)
                ⟨hβcos, hlt'⟩).symm
            · exact Work.OddVolterra.Free.glueA_eq_inversion n hn hρsm β (by linarith)
                (ne_of_gt hgt')
      have hgb : (Work.OddCurve.LowSlope.glueB n ρ) =ᶠ[𝓝 α]
          (fun β : ℝ => 2 * RB (Real.cos β) / Real.cos β) := by
        rcases lt_or_eq_of_le hfar with hlt | heq
        · have hcgt : 4 / 5 < Real.cos α := by
            have h := Real.cos_lt_cos_of_nonneg_of_le_pi (x := α) (y := Real.arccos (4 / 5))
              hα0 (Real.arccos_le_pi _) hlt
            rwa [Real.cos_arccos (by norm_num) (by norm_num)] at h
          filter_upwards [(isOpen_lt continuous_const Real.continuous_cos).mem_nhds hcgt]
            with β hβ
          rw [Work.OddCurve.LowSlope.glueB_of_ge hβ.le]
          rfl
        · have hαpos : 0 < α := by rw [heq]; exact Real.arccos_pos.mpr (by norm_num)
          set δ : ℝ := min (α / 2) ((Real.pi / 2 - α) / 2) with hδdef
          have hδle1 : δ ≤ α / 2 := by rw [hδdef]; exact min_le_left _ _
          have hδle2 : δ ≤ (Real.pi / 2 - α) / 2 := by rw [hδdef]; exact min_le_right _ _
          have hδpos : 0 < δ := by rw [hδdef]; exact lt_min (by linarith) (by linarith)
          have hmemI : Set.Ioo (α - δ) (α + δ) ∈ 𝓝 α :=
            isOpen_Ioo.mem_nhds ⟨sub_lt_self α hδpos, lt_add_of_pos_right α hδpos⟩
          filter_upwards [hmemI] with β hβ
          rw [Set.mem_Ioo] at hβ
          have hβ0 : 0 < β := by linarith [hβ.1, hδle1, hαpos]
          have hβlt : β < Real.pi / 2 := by linarith [hβ.2, hδle2, hαlt]
          rcases lt_or_ge (Real.cos β) (4 / 5) with hb | hb
          · rw [Work.OddCurve.LowSlope.glueB_of_lt hb]
            have hbpos : 0 < Real.cos β := Real.cos_pos_of_mem_Ioo ⟨by linarith [hβ0], hβlt⟩
            rw [show RB (Real.cos β)
                = Work.OddRadon.radonInverse n (Work.OddCurve.LowSlope.GlueG n ρ) (Real.cos β)
                from rfl,
              Work.OddCurve.LowSlope.radonInverse_GlueG_eq (n := n) (ρ := ρ) hbpos hb,
              Work.OddRadon.radonInverse_radonPsi_local n hn (c₁ := 4 / 5) (by norm_num) hρsm
                hbpos hb]
            have hbne : Real.cos β ≠ 0 := ne_of_gt hbpos
            rw [eq_div_iff hbne]
            ring
          · rw [Work.OddCurve.LowSlope.glueB_of_ge hb]
            rfl
      have hM'0 : (0 : ℝ) ≤ CG * M := mul_nonneg hCGpos.le hM0
      have hkey := hKF (R := RA) (S := RB) (M := CG * M) (α := α) hM'0 hcosge hRd hRd' hSd hSd'
        hRv hRv' hRv'' hSv hSv' hSv''
      have hKle : KF * (CG * M) ≤ K * (C₁ + 1) * ε := by
        rw [hMdef]
        have hprod : (0 : ℝ) ≤ KF * CG * Cn := by positivity
        have h2 : C₁ * ε ≤ (C₁ + 1) * ε := by
          have hh : (C₁ + 1) * ε = C₁ * ε + ε := by ring
          rw [hh]; linarith [hε.le]
        have h4 : (0 : ℝ) ≤ (C₁ + 1) * ε := mul_nonneg (by linarith) hε.le
        calc KF * (CG * (Cn * (C₁ * ε))) = (KF * CG * Cn) * (C₁ * ε) := by ring
          _ ≤ (KF * CG * Cn) * ((C₁ + 1) * ε) := mul_le_mul_of_nonneg_left h2 hprod
          _ ≤ K * ((C₁ + 1) * ε) := mul_le_mul_of_nonneg_right hKFKleK h4
          _ = K * (C₁ + 1) * ε := by ring
      have hvalA : Work.OddCurve.LowSlope.glueA n ρ α = 2 * RA (Real.cos α) / Real.cos α ^ 2 :=
        hga.eq_of_nhds
      have hvalB : Work.OddCurve.LowSlope.glueB n ρ α = 2 * RB (Real.cos α) / Real.cos α :=
        hgb.eq_of_nhds
      have hderA : deriv (Work.OddCurve.LowSlope.glueA n ρ) α
          = deriv (fun β : ℝ => 2 * RA (Real.cos β) / Real.cos β ^ 2) α := hga.deriv_eq
      have hder2A : deriv (deriv (Work.OddCurve.LowSlope.glueA n ρ)) α
          = deriv (deriv (fun β : ℝ => 2 * RA (Real.cos β) / Real.cos β ^ 2)) α :=
        (hga.deriv).deriv_eq
      have hderB : deriv (Work.OddCurve.LowSlope.glueB n ρ) α
          = deriv (fun β : ℝ => 2 * RB (Real.cos β) / Real.cos β) α := hgb.deriv_eq
      have hder2B : deriv (deriv (Work.OddCurve.LowSlope.glueB n ρ)) α
          = deriv (deriv (fun β : ℝ => 2 * RB (Real.cos β) / Real.cos β)) α :=
        (hgb.deriv).deriv_eq
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [hvalA]; exact le_trans hkey.1 hKle
      · rw [hvalB]; exact le_trans hkey.2.2.2.1 hKle
      · rw [hderA]; exact le_trans hkey.2.1 hKle
      · rw [hder2A]; exact le_trans hkey.2.2.1 hKle
      · rw [hderB]; exact le_trans hkey.2.2.2.2.1 hKle
      · rw [hder2B]; exact le_trans hkey.2.2.2.2.2 hKle
    · -- NEAR: `cos α < 4 / 5`
      have hcoslt : Real.cos α < 4 / 5 := by
        have h := Real.cos_lt_cos_of_nonneg_of_le_pi (x := Real.arccos (4 / 5)) (y := α)
          (Real.arccos_nonneg _) (by linarith [hα.2, Real.pi_pos]) hnear
        rwa [Real.cos_arccos (by norm_num) (by norm_num)] at h
      have hcosnn : 0 ≤ Real.cos α :=
        Real.cos_nonneg_of_mem_Icc ⟨by linarith [hα.1, Real.pi_pos], hα.2⟩
      have hcosabs : |Real.cos α| < 4 / 5 := by
        rw [abs_of_nonneg hcosnn]; exact hcoslt
      have hkey := hKN hε hCε hρsm hρc hcosabs
      have hga : (Work.OddCurve.LowSlope.glueA n ρ) =ᶠ[𝓝 α]
          (fun β : ℝ => ρ (Real.cos β) ^ (2 * n + 2) + ρ (-Real.cos β) ^ (2 * n + 2) - 2) := by
        filter_upwards [(isOpen_lt Real.continuous_cos continuous_const).mem_nhds hcoslt]
          with β hβ
        exact Work.OddCurve.LowSlope.glueA_of_lt hβ
      have hgb : (Work.OddCurve.LowSlope.glueB n ρ) =ᶠ[𝓝 α]
          (fun β : ℝ => ρ (Real.cos β) ^ (2 * n + 1) - ρ (-Real.cos β) ^ (2 * n + 1)) := by
        filter_upwards [(isOpen_lt Real.continuous_cos continuous_const).mem_nhds hcoslt]
          with β hβ
        exact Work.OddCurve.LowSlope.glueB_of_lt hβ
      have hle : KN * (C₁ + 1) * ε ≤ K * (C₁ + 1) * ε := by
        calc KN * (C₁ + 1) * ε = KN * ((C₁ + 1) * ε) := by ring
          _ ≤ K * ((C₁ + 1) * ε) := mul_le_mul_of_nonneg_right hKNleK hCε1
          _ = K * (C₁ + 1) * ε := by ring
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [show Work.OddCurve.LowSlope.glueA n ρ α
            = ρ (Real.cos α) ^ (2 * n + 2) + ρ (-Real.cos α) ^ (2 * n + 2) - 2
            from hga.eq_of_nhds]
        exact le_trans hkey.1 hle
      · rw [show Work.OddCurve.LowSlope.glueB n ρ α
            = ρ (Real.cos α) ^ (2 * n + 1) - ρ (-Real.cos α) ^ (2 * n + 1)
            from hgb.eq_of_nhds]
        exact le_trans hkey.2.1 hle
      · rw [hga.deriv_eq]; exact le_trans hkey.2.2.1 hle
      · rw [(hga.deriv).deriv_eq]; exact le_trans hkey.2.2.2.1 hle
      · rw [hgb.deriv_eq]; exact le_trans hkey.2.2.2.2.1 hle
      · rw [(hgb.deriv).deriv_eq]; exact le_trans hkey.2.2.2.2.2 hle


end

end Work.OddVolterra.Free
