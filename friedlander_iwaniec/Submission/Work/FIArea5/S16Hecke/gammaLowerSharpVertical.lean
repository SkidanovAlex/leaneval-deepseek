import Mathlib
import Submission.Work.FIArea5.S16Hecke.gammaRatioSeqMono
import Submission.Work.FIArea5.S16Hecke.gammaRatioSeqLower
import Submission.Work.FIArea5.S16Hecke.gammaSeqRatioSeqTendsto
import Submission.Work.FIArea5.S16Hecke.normGammaHalfAddILower

open scoped BigOperators
open Filter

namespace Work.FIArea5.S16Hecke

noncomputable section

/-- The finite products `n ^ α * ∏_{j=0}^n sqrt ((T² + (j+1/2)²)/(T² + (j+α+1/2)²))`
whose monotone limit is `‖Γ(u+iT)‖ / ‖Γ(1/2+iT)‖` for `α = u - 1/2`. -/
private noncomputable def gammaRatioSeq (α T : ℝ) (n : ℕ) : ℝ :=
  (n : ℝ) ^ α * Finset.prod (Finset.range (n + 1))
    (fun j : ℕ => Real.sqrt ((T ^ 2 + ((j : ℝ) + 1 / 2) ^ 2) /
      (T ^ 2 + ((j : ℝ) + α + 1 / 2) ^ 2)))

private lemma gammaRatioSeq_mono (α T : ℝ) (hα : 1 / 2 ≤ α) (hT : 0 ≤ T) :
    Monotone (gammaRatioSeq α T) :=
  monotone_nat_of_le_succ (fun n => by
    simpa [gammaRatioSeq] using gammaRatioSeqMono α T hα hT n)

private lemma gammaRatioSeq_lower (α T : ℝ) (hα1 : 1 / 2 ≤ α) (hα2 : α ≤ 3 / 2)
    (hT : 0 ≤ T) :
    (1 / 1000) * (1 + T) ^ α ≤ gammaRatioSeq α T (max 3 (Nat.ceil T)) := by
  simpa [gammaRatioSeq] using gammaRatioSeqLower α T hα1 hα2 hT

private lemma gammaRatioSeq_tendsto (u T : ℝ) :
    Tendsto (gammaRatioSeq (u - 1 / 2) T) atTop
      (nhds (‖Complex.Gamma ((u : ℂ) + (T : ℂ) * Complex.I)‖ /
           ‖Complex.Gamma ((1 / 2 : ℂ) + (T : ℂ) * Complex.I)‖)) := by
  refine (gammaSeqRatioSeqTendsto u T).congr (fun n => ?_)
  simp only [gammaRatioSeq]
  congr 1
  apply Finset.prod_congr rfl
  intro j hj
  congr 1
  ring

private lemma gammaRatioSeq_le_limit (u T : ℝ) (hu : 1 ≤ u) (hT : 0 ≤ T) :
    gammaRatioSeq (u - 1 / 2) T (max 3 (Nat.ceil T)) ≤
      ‖Complex.Gamma ((u : ℂ) + (T : ℂ) * Complex.I)‖ /
        ‖Complex.Gamma ((1 / 2 : ℂ) + (T : ℂ) * Complex.I)‖ := by
  have hα : 1 / 2 ≤ u - 1 / 2 := by linarith
  exact (gammaRatioSeq_mono (u - 1 / 2) T hα hT).ge_of_tendsto
    (gammaRatioSeq_tendsto u T) (max 3 (Nat.ceil T))

end

theorem gammaLowerSharpVertical :
    ∃ c : ℝ, 0 < c ∧ ∀ (u t : ℝ), 1 ≤ u → u ≤ 2 →
      c * (1 + |t|) ^ (u - 1 / 2) * Real.exp (-(Real.pi / 2) * |t|) ≤
        ‖Complex.Gamma ((u : ℂ) + (t : ℂ) * Complex.I)‖ := by
  refine ⟨Real.sqrt Real.pi / 1000, by positivity, ?_⟩
  intro u t hu1 hu2
  have hα1 : 1 / 2 ≤ u - 1 / 2 := by linarith
  have hα2 : u - 1 / 2 ≤ 3 / 2 := by linarith
  have hT : 0 ≤ |t| := abs_nonneg t
  have hlow := gammaRatioSeq_lower (u - 1 / 2) |t| hα1 hα2 hT
  have hlim := gammaRatioSeq_le_limit u |t| hu1 hT
  have hcrit : Real.sqrt Real.pi * Real.exp (-(Real.pi / 2) * |t|) ≤
      ‖Complex.Gamma ((1 / 2 : ℂ) + (((|t| : ℝ)) : ℂ) * Complex.I)‖ := by
    simpa only [abs_abs] using normGammaHalfAddILower |t|
  have hpos : 0 < ‖Complex.Gamma ((1 / 2 : ℂ) + (((|t| : ℝ)) : ℂ) * Complex.I)‖ := by
    rw [norm_pos_iff]
    exact Complex.Gamma_ne_zero_of_re_pos (by simp)
  have hmain : (1 / 1000) * (1 + |t|) ^ (u - 1 / 2) *
        (Real.sqrt Real.pi * Real.exp (-(Real.pi / 2) * |t|)) ≤
      ‖Complex.Gamma ((u : ℂ) + (((|t| : ℝ)) : ℂ) * Complex.I)‖ := by
    have h1 : (1 / 1000) * (1 + |t|) ^ (u - 1 / 2) ≤
        ‖Complex.Gamma ((u : ℂ) + (((|t| : ℝ)) : ℂ) * Complex.I)‖ /
          ‖Complex.Gamma ((1 / 2 : ℂ) + (((|t| : ℝ)) : ℂ) * Complex.I)‖ :=
      hlow.trans hlim
    have h2 : (1 / 1000) * (1 + |t|) ^ (u - 1 / 2) *
          ‖Complex.Gamma ((1 / 2 : ℂ) + (((|t| : ℝ)) : ℂ) * Complex.I)‖ ≤
        ‖Complex.Gamma ((u : ℂ) + (((|t| : ℝ)) : ℂ) * Complex.I)‖ := by
      calc (1 / 1000) * (1 + |t|) ^ (u - 1 / 2) *
              ‖Complex.Gamma ((1 / 2 : ℂ) + (((|t| : ℝ)) : ℂ) * Complex.I)‖
          ≤ (‖Complex.Gamma ((u : ℂ) + (((|t| : ℝ)) : ℂ) * Complex.I)‖ /
                ‖Complex.Gamma ((1 / 2 : ℂ) + (((|t| : ℝ)) : ℂ) * Complex.I)‖) *
              ‖Complex.Gamma ((1 / 2 : ℂ) + (((|t| : ℝ)) : ℂ) * Complex.I)‖ :=
            mul_le_mul_of_nonneg_right h1 hpos.le
          _ = ‖Complex.Gamma ((u : ℂ) + (((|t| : ℝ)) : ℂ) * Complex.I)‖ := by
            rw [div_mul_cancel₀ _ hpos.ne']
    have h3 : (1 / 1000) * (1 + |t|) ^ (u - 1 / 2) *
          (Real.sqrt Real.pi * Real.exp (-(Real.pi / 2) * |t|)) ≤
        (1 / 1000) * (1 + |t|) ^ (u - 1 / 2) *
          ‖Complex.Gamma ((1 / 2 : ℂ) + (((|t| : ℝ)) : ℂ) * Complex.I)‖ :=
      mul_le_mul_of_nonneg_left hcrit
        (mul_nonneg (by norm_num) (Real.rpow_nonneg (by positivity) _))
    exact h3.trans h2
  have hnorm : ‖Complex.Gamma ((u : ℂ) + (((|t| : ℝ)) : ℂ) * Complex.I)‖ =
      ‖Complex.Gamma ((u : ℂ) + (t : ℂ) * Complex.I)‖ := by
    rcases le_or_gt 0 t with ht | ht
    · have h : (((|t| : ℝ)) : ℂ) = (t : ℂ) := by
        rw [abs_of_nonneg ht]
      rw [h]
    · have h : (((|t| : ℝ)) : ℂ) = ((-t : ℝ) : ℂ) := by
        rw [abs_of_nonpos ht.le]
      rw [h]
      have hconj : (u : ℂ) + ((-t : ℝ) : ℂ) * Complex.I =
          (starRingEnd ℂ) ((u : ℂ) + (t : ℂ) * Complex.I) := by
        apply Complex.ext <;> simp [Complex.conj_re, Complex.conj_im]
      rw [hconj, Complex.Gamma_conj, Complex.norm_conj]
  rw [hnorm] at hmain
  convert hmain using 1
  ring

end Work.FIArea5.S16Hecke
