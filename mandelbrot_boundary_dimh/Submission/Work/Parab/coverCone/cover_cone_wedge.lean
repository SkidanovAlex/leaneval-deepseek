import Mathlib
import Submission.Work.Parab.LeftData
import Submission.Work.Parab.Setup
import Submission.Work.Parab.coverCone.log_le_mul
import Submission.Work.Parab.coverCone.inv_neg_norm_re
import Submission.Work.Parab.coverCone.inv_neg_wedge
import Submission.Work.Parab.coverCone.norm_log_le_abs_log_add_pi

/-!
# Covering the cone: the wedge version

Given a holomorphic coordinate `Φ` on a domain `L ⊆ ℂ` which

* contains the far left half plane `{Re ζ < -M₀}`,
* contains the far part of the wedge `{M₁ < |Im ζ|, Re ζ < 3 |Im ζ|}` (this is the form in which
  the maximal domain of the Fatou coordinate is available, cf. `Work.Parab.LeftCoordData`),
* is asymptotic to `ζ - a log(-ζ) - b` at infinity on `L`,

the inverse `τ₀ ζ = -1/ζ` of `Φ` covers a full sector of directions at `0`: there are `ξ₀, ρ > 0`
such that every `z` with `0 < ‖z‖ < ρ` and `|arg z| ≤ 2π/3 - π/12` is `τ₀ ζ` for some `ζ ∈ L`
whose image `Φ ζ` lies in the repelling sector `QLeft ξ₀`.
-/

namespace Work.Parab.coverCone

open Complex Set Metric Filter
open scoped Topology

theorem cover_cone_wedge {Φ : ℂ → ℂ} {L : Set ℂ} {M₀ M₁ : ℝ} {a b : ℂ}
    (hM₀ : 0 < M₀) (hM₁ : 0 < M₁)
    (hLleft : ∀ ζ : ℂ, ζ.re < -M₀ → ζ ∈ L)
    (hLim : ∀ ζ : ℂ, M₁ < |ζ.im| → ζ.re < 3 * |ζ.im| → ζ ∈ L)
    (hasym : ∀ ε > 0, ∃ R : ℝ, ∀ ζ ∈ L, R < ‖ζ‖ →
      ‖Φ ζ - (ζ - a * Complex.log (-ζ) - b)‖ < ε) :
    ∃ ξ₀ : ℝ, 0 < ξ₀ ∧ ∃ ρ : ℝ, 0 < ρ ∧
      ∀ z : ℂ, 0 < ‖z‖ → ‖z‖ < ρ → |z.arg| ≤ 2 * Real.pi / 3 - Real.pi / 12 →
        ∃ w ∈ MandelDim.QLeft ξ₀, ∃ ζ ∈ L, Φ ζ = w ∧ MandelDim.tau0 ζ = z := by
  obtain ⟨R, hR⟩ := hasym 1 one_pos
  obtain ⟨T₁, hT₁pos, hT₁⟩ := log_le_mul (1 / (200 * (‖a‖ + 1))) (by positivity)
  set Λ : ℝ := ‖a‖ * Real.pi + ‖b‖ + 1 with hΛ
  set T : ℝ := max (max (R + 1) 12) (max (200 * Λ) (max T₁ 1)) with hT
  have hT12 : 12 ≤ T := by
    rw [hT]; exact le_trans (le_max_right (R + 1) 12) (le_max_left _ _)
  have hTpos : 0 < T := by linarith
  have hTR : R + 1 ≤ T := by
    rw [hT]; exact le_trans (le_max_left (R + 1) 12) (le_max_left _ _)
  have hT200 : 200 * Λ ≤ T := by
    rw [hT]; exact le_trans (le_max_left (200 * Λ) (max T₁ 1)) (le_max_right _ _)
  have hTT₁ : T₁ ≤ T := by
    rw [hT]
    exact le_trans (le_trans (le_max_left T₁ 1) (le_max_right (200 * Λ) (max T₁ 1)))
      (le_max_right _ _)
  have hT1 : 1 ≤ T := le_trans (le_trans (le_max_right T₁ 1) (le_max_right (200 * Λ) (max T₁ 1)))
    (le_max_right _ _)
  refine ⟨1, one_pos,
    min (min (1 / T) (min (1 / (3 * M₀)) (1 / (2 * M₀)))) (3 / (4 * M₁)), ?_, ?_⟩
  · positivity
  · intro z hz0 hzρ hzarg
    have hz_ne : z ≠ 0 := by
      intro h; rw [h, norm_zero] at hz0; exact lt_irrefl 0 hz0
    have hz7 : |z.arg| ≤ 7 * Real.pi / 12 := by linarith
    have hρ1 : ‖z‖ < 1 / T := lt_of_lt_of_le hzρ (le_trans (min_le_left _ _) (min_le_left _ _))
    have hρ2 : ‖z‖ < 1 / (3 * M₀) :=
      lt_of_lt_of_le hzρ (le_trans (min_le_left _ _) (le_trans (min_le_right _ _) (min_le_left _ _)))
    have hρ3 : ‖z‖ < 1 / (2 * M₀) :=
      lt_of_lt_of_le hzρ (le_trans (min_le_left _ _) (le_trans (min_le_right _ _) (min_le_right _ _)))
    have hρ4 : ‖z‖ < 3 / (4 * M₁) := lt_of_lt_of_le hzρ (min_le_right _ _)
    have hζnorm : T < ‖-1 / z‖ := by
      rw [(inv_neg_norm_re hz_ne hz7).1]
      have h : 1 / (1 / T) < 1 / ‖z‖ := one_div_lt_one_div_of_lt hz0 hρ1
      rwa [one_div_one_div] at h
    have htT : T ≤ ‖-1 / z‖ := le_of_lt hζnorm
    have ht12 : 12 ≤ ‖-1 / z‖ := le_trans hT12 htT
    have ht1 : 1 ≤ ‖-1 / z‖ := le_trans hT1 htT
    have hRlt : R < ‖-1 / z‖ := by linarith
    have hLet : ‖a‖ * Real.pi + ‖b‖ + 1 ≤ ‖-1 / z‖ / 200 := by
      have := hT200; rw [hΛ] at this; linarith
    have hLmem : -1 / z ∈ L := by
      by_cases hcase : (-1 / z).re < -M₀
      · exact hLleft _ hcase
      · push_neg at hcase
        obtain ⟨him, hwedge⟩ :=
          inv_neg_wedge hM₀ hM₁ hz_ne hz7 (le_of_lt hρ2) (le_of_lt hρ4) hcase
        exact hLim _ him hwedge
    have hlog : ‖Complex.log (-(-1 / z))‖ ≤ Real.log ‖-1 / z‖ + Real.pi := by
      calc ‖Complex.log (-(-1 / z))‖ ≤ |Real.log ‖-(-1 / z)‖| + Real.pi := norm_log_le_abs_log_add_pi _
        _ = Real.log ‖-1 / z‖ + Real.pi := by
              rw [norm_neg, abs_of_nonneg (Real.log_nonneg ht1)]
    have he : ‖Φ (-1 / z) - (-1 / z)‖ ≤ ‖-1 / z‖ / 40 := by
      have hstep : ‖Φ (-1 / z) - (-1 / z)‖
          ≤ 1 + ‖a‖ * ‖Complex.log (-(-1 / z))‖ + ‖b‖ := by
        have hsplit : Φ (-1 / z) - (-1 / z)
            = (Φ (-1 / z) - (-1 / z - a * Complex.log (-(-1 / z)) - b))
              - (a * Complex.log (-(-1 / z)) + b) := by ring
        calc ‖Φ (-1 / z) - (-1 / z)‖
            = ‖(Φ (-1 / z) - (-1 / z - a * Complex.log (-(-1 / z)) - b))
                - (a * Complex.log (-(-1 / z)) + b)‖ := by rw [hsplit]
          _ ≤ ‖Φ (-1 / z) - (-1 / z - a * Complex.log (-(-1 / z)) - b)‖
                + ‖a * Complex.log (-(-1 / z)) + b‖ := norm_sub_le _ _
          _ ≤ 1 + (‖a‖ * ‖Complex.log (-(-1 / z))‖ + ‖b‖) := by
                refine add_le_add (le_of_lt (hR (-1 / z) hLmem hRlt)) ?_
                calc ‖a * Complex.log (-(-1 / z)) + b‖
                    ≤ ‖a * Complex.log (-(-1 / z))‖ + ‖b‖ := norm_add_le _ _
                  _ = ‖a‖ * ‖Complex.log (-(-1 / z))‖ + ‖b‖ := by rw [norm_mul]
          _ = 1 + ‖a‖ * ‖Complex.log (-(-1 / z))‖ + ‖b‖ := by ring
      have hlogmul : ‖a‖ * ‖Complex.log (-(-1 / z))‖
          ≤ ‖a‖ * Real.log ‖-1 / z‖ + ‖a‖ * Real.pi := by
        have h1 := mul_le_mul_of_nonneg_left hlog (norm_nonneg a)
        rw [mul_add] at h1
        exact h1
      have hA : ‖a‖ * Real.log ‖-1 / z‖ ≤ ‖-1 / z‖ / 200 := by
        have h1 : Real.log ‖-1 / z‖ ≤ (1 / (200 * (‖a‖ + 1))) * ‖-1 / z‖ :=
          hT₁ _ (le_trans hTT₁ htT)
        have h2 : ‖a‖ * Real.log ‖-1 / z‖
            ≤ ‖a‖ * ((1 / (200 * (‖a‖ + 1))) * ‖-1 / z‖) :=
          mul_le_mul_of_nonneg_left h1 (norm_nonneg a)
        have h3 : ‖a‖ * ((1 / (200 * (‖a‖ + 1))) * ‖-1 / z‖)
            = (‖a‖ / (200 * (‖a‖ + 1))) * ‖-1 / z‖ := by ring
        have h4 : ‖a‖ / (200 * (‖a‖ + 1)) ≤ 1 / 200 := by
          rw [div_le_div_iff₀ (by positivity) (by norm_num)]
          nlinarith [norm_nonneg a]
        have h5 : (‖a‖ / (200 * (‖a‖ + 1))) * ‖-1 / z‖ ≤ (1 / 200) * ‖-1 / z‖ :=
          mul_le_mul_of_nonneg_right h4 (norm_nonneg _)
        linarith [h2, h3, h5]
      have hC : ‖b‖ + 1 ≤ ‖-1 / z‖ / 200 := by
        have h1 : ‖b‖ + 1 ≤ ‖a‖ * Real.pi + ‖b‖ + 1 := by
          nlinarith [norm_nonneg a, Real.pi_pos.le]
        linarith [hLet, h1]
      have hB : ‖a‖ * Real.pi ≤ ‖-1 / z‖ / 200 := by
        have h1 : ‖a‖ * Real.pi ≤ ‖a‖ * Real.pi + ‖b‖ + 1 := by
          nlinarith [norm_nonneg b]
        linarith [hLet, h1]
      have hfin : 1 + ‖a‖ * ‖Complex.log (-(-1 / z))‖ + ‖b‖ ≤ ‖-1 / z‖ / 40 := by
        have ht : 0 ≤ ‖-1 / z‖ := norm_nonneg _
        linarith [hlogmul, hA, hB, hC, ht]
      linarith [hstep, hfin]
    refine ⟨Φ (-1 / z), ?_, -1 / z, hLmem, rfl, ?_⟩
    · rw [Work.Parab.QLeft_iff, Complex.ofReal_one]
      have hre : (-1 / z).re ≤ ‖-1 / z‖ / 3 := (inv_neg_norm_re hz_ne hz7).2
      have hb1 : (Φ (-1 / z) + 1).re ≤ ‖-1 / z‖ / 3 + ‖-1 / z‖ / 40 + 1 := by
        rw [Complex.add_re, Complex.one_re]
        have h2 : (Φ (-1 / z)).re ≤ (-1 / z).re + ‖Φ (-1 / z) - (-1 / z)‖ := by
          have h3 : (Φ (-1 / z)).re = (-1 / z).re + (Φ (-1 / z) - (-1 / z)).re := by
            rw [Complex.sub_re]; ring
          have h4 := Complex.re_le_norm (Φ (-1 / z) - (-1 / z))
          linarith
        linarith [h2, hre, he]
      have hb2 : ‖-1 / z‖ - ‖-1 / z‖ / 40 - 1 ≤ ‖Φ (-1 / z) + 1‖ := by
        have h2 : Φ (-1 / z) + 1 = (-1 / z) + ((Φ (-1 / z) - (-1 / z)) + 1) := by ring
        rw [h2]
        have hnorm : ‖((-1 / z) + ((Φ (-1 / z) - (-1 / z)) + 1))
            - ((Φ (-1 / z) - (-1 / z)) + 1)‖ = ‖-1 / z‖ := by
          congr 1; ring
        have h3 : ‖-1 / z‖ ≤ ‖(-1 / z) + ((Φ (-1 / z) - (-1 / z)) + 1)‖
            + ‖(Φ (-1 / z) - (-1 / z)) + 1‖ := by
          rw [← hnorm]; exact norm_sub_le _ _
        have h4 : ‖(Φ (-1 / z) - (-1 / z)) + 1‖ ≤ ‖Φ (-1 / z) - (-1 / z)‖ + 1 := by
          have := norm_add_le (Φ (-1 / z) - (-1 / z)) 1
          simpa using this
        linarith [h3, h4, he]
      have hb3 : 2 * (‖-1 / z‖ / 3 + ‖-1 / z‖ / 40 + 1) < ‖-1 / z‖ - ‖-1 / z‖ / 40 - 1 := by
        linarith [ht12]
      linarith [hb1, hb2, hb3]
    · simp only [MandelDim.tau0]
      field_simp

end Work.Parab.coverCone
