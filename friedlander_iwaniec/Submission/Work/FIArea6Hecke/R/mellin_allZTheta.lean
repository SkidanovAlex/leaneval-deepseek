/-
# `Work.FIArea6Hecke.R.mellin_allZTheta`

The **Mellin step** for the all-`z` theta series:

  `∫_0^∞ allZTheta χ₀ m u · u^{s-1} du = Γ(s)·π^{-s}·fullHeckeLSeries χ₀ m (s - m/2)`

for `re s > 1 + m/2`, together with the exponential summability of the weighted all-`z` Hecke
eigenvalues.  The proof is the all-`z` counterpart of `mellin_thetaHol`: the generating function
identity `allZTheta_eq_tsum_allZLam` presents `allZTheta` as `Σ_n n^{m/2}·λ_n·e^{-πun}`, the
abstract Mellin transform `mellin_tsum_exp` converts this into `Γ(s)π^{-s}Σ_n n^{m/2}λ_n n^{-s}`,
and `fullHeckeLSeries_eq_tsum_allZLam` identifies the latter Dirichlet series with the all-`z`
Hecke `L`-series.
-/
import Mathlib
import Submission.Work.FIArea6Hecke.R.AllZThetaDefs
import Submission.Work.FIArea6Hecke.R.allZTheta_eq_tsum_allZLam
import Submission.Work.FIArea6Hecke.R.summable_allZLam_weight
import Submission.Work.FIArea6Hecke.R.fullHeckeLSeries_eq_tsum_allZLam
import Submission.Work.FIArea5.S16Hecke.mellin_tsum_exp
import Submission.Work.FIArea5.S16Hecke.rpow_mul_exp_neg_bounded

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Work.FIArea6Hecke.R

open MeasureTheory Set
open scoped BigOperators
open Work.FIPlan

noncomputable section

/-- `allZLam χ₀ k 0 = 0` when `χ₀ 0 = 0` (the fibre `|z|² = 0` is the single point `0`). -/
lemma allZLam_zero (chi₀ : GaussianInt → ℂ) (k : ℤ) (h0 : chi₀ 0 = 0) :
    allZLam chi₀ k 0 = 0 := by
  classical
  have hg0 : (gBox ((0 : ℕ) : ℤ)).filter (fun z => gnorm z = 0) = {0} := by
    ext z
    rw [Finset.mem_filter, Finset.mem_singleton]
    constructor
    · rintro ⟨_, hz⟩
      exact eq_zero_of_gnorm_eq_zero hz
    · rintro rfl
      refine ⟨?_, ?_⟩
      · rw [Work.FIArea5.S16Hecke.mem_gBox_iff]; simp
      · decide
  rw [allZLam, hg0, Finset.sum_singleton, Work.FIArea5.S16Hecke.psi, h0, zero_mul]

/-- **Exponential summability of the weighted all-`z` Hecke eigenvalues.** -/
theorem summable_allZLam_exp (chi₀ : GaussianInt → ℂ) (m : ℕ)
    (hchi : ∀ z : GaussianInt, ‖chi₀ z‖ ≤ 1) (hchi0 : chi₀ 0 = 0) {u : ℝ} (hu : 0 < u) :
    Summable (fun n : ℕ => ‖(n : ℂ) ^ ((m : ℂ) / 2) * allZLam chi₀ (m : ℤ) n‖ *
      Real.exp (-(Real.pi * u * (n : ℝ)))) := by
  set σ : ℝ := 1 + (m : ℝ) / 2 + 1 with hσdef
  have hσ : 1 + (m : ℝ) / 2 < σ := by rw [hσdef]; linarith
  have hweight := summable_allZLam_weight chi₀ m hchi hσ
  obtain ⟨C, _hC0, hC⟩ := Work.FIArea5.S16Hecke.rpow_mul_exp_neg_bounded (Real.pi * u)
    (by positivity) σ (by rw [hσdef]; positivity)
  refine Summable.of_nonneg_of_le
    (f := fun n : ℕ => C * (‖(n : ℂ) ^ ((m : ℂ) / 2) * allZLam chi₀ (m : ℤ) n‖ *
      (n : ℝ) ^ (-σ))) (fun n => by positivity) (fun n => ?_) (hweight.mul_left C)
  rcases eq_or_ne n 0 with hn | hn
  · subst hn
    rw [allZLam_zero chi₀ (m : ℤ) hchi0]
    simp
  · have hnR : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
    have hb : (n : ℝ) ^ σ * Real.exp (-(Real.pi * u * (n : ℝ))) ≤ C :=
      hC (n : ℝ) (le_of_lt hnR)
    have h1 : (n : ℝ) ^ (-σ) * (n : ℝ) ^ σ = 1 := by
      rw [← Real.rpow_add hnR, neg_add_cancel, Real.rpow_zero]
    calc ‖(n : ℂ) ^ ((m : ℂ) / 2) * allZLam chi₀ (m : ℤ) n‖ *
          Real.exp (-(Real.pi * u * (n : ℝ)))
        = (‖(n : ℂ) ^ ((m : ℂ) / 2) * allZLam chi₀ (m : ℤ) n‖ *
            ((n : ℝ) ^ (-σ) * (n : ℝ) ^ σ)) * Real.exp (-(Real.pi * u * (n : ℝ))) := by
          rw [h1, mul_one]
      _ = (‖(n : ℂ) ^ ((m : ℂ) / 2) * allZLam chi₀ (m : ℤ) n‖ * (n : ℝ) ^ (-σ)) *
            ((n : ℝ) ^ σ * Real.exp (-(Real.pi * u * (n : ℝ)))) := by ring
      _ ≤ (‖(n : ℂ) ^ ((m : ℂ) / 2) * allZLam chi₀ (m : ℤ) n‖ * (n : ℝ) ^ (-σ)) * C :=
          mul_le_mul_of_nonneg_left hb (by positivity)
      _ = C * (‖(n : ℂ) ^ ((m : ℂ) / 2) * allZLam chi₀ (m : ℤ) n‖ * (n : ℝ) ^ (-σ)) := by ring

/-- **The Mellin transform of the all-`z` theta series.** -/
theorem mellin_allZTheta (chi₀ : GaussianInt → ℂ) (m : ℕ)
    (hchi : ∀ z : GaussianInt, ‖chi₀ z‖ ≤ 1) (hchi0 : chi₀ 0 = 0) {s : ℂ}
    (hs : 1 + (m : ℝ) / 2 < s.re) :
    mellin (allZTheta chi₀ m) s = Complex.Gamma s * ((Real.pi : ℂ) ^ (-s)) *
      fullHeckeLSeries chi₀ (m : ℤ) (s - (m : ℂ) / 2) := by
  set w : ℕ → ℂ := fun n => (n : ℂ) ^ ((m : ℂ) / 2) * allZLam chi₀ (m : ℤ) n with hw
  have hwp : ∀ n : ℕ, w n = (n : ℂ) ^ ((m : ℂ) / 2) * allZLam chi₀ (m : ℤ) n :=
    fun n => by rw [hw]
  have hw0 : w 0 = 0 := by
    rw [hwp 0, allZLam_zero chi₀ (m : ℤ) hchi0, mul_zero]
  have hs0 : 0 < s.re := by
    have hm0 : (0 : ℝ) ≤ (m : ℝ) / 2 := by positivity
    linarith
  have hpoint : ∀ u : ℝ, 0 < u →
      Summable (fun n : ℕ => ‖w n‖ * Real.exp (-(Real.pi * u * (n : ℝ)))) := by
    intro u hu
    refine (summable_allZLam_exp chi₀ m hchi hchi0 hu).congr (fun n => ?_)
    rw [hwp n]
  have hsum : Summable (fun n : ℕ => ‖w n‖ * (n : ℝ) ^ (-s.re)) := by
    refine (summable_allZLam_weight chi₀ m hchi hs).congr (fun n => ?_)
    rw [hwp n]
  have hC := Work.FIArea5.S16Hecke.mellin_tsum_exp w Real.pi Real.pi_pos hw0 hs0 hpoint hsum
  have hL : ∀ u : ℝ, 0 < u → allZTheta chi₀ m u =
      ∑' n : ℕ, w n * Complex.exp (-((Real.pi : ℂ) * (u : ℂ) * ((n : ℝ) : ℂ))) := by
    intro u hu
    rw [allZTheta_eq_tsum_allZLam chi₀ m hchi hu]
  have hLHS : mellin (allZTheta chi₀ m) s =
      mellin (fun u : ℝ => ∑' n : ℕ,
        w n * Complex.exp (-((Real.pi : ℂ) * (u : ℂ) * ((n : ℝ) : ℂ)))) s := by
    rw [mellin, mellin]
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi (fun u hu => ?_)
    rw [hL u hu]
  have hR : (∑' n : ℕ, w n * (n : ℂ) ^ (-s)) =
      fullHeckeLSeries chi₀ (m : ℤ) (s - (m : ℂ) / 2) := by
    have h1 : (∑' n : ℕ, w n * (n : ℂ) ^ (-s)) =
        ∑' n : ℕ, (n : ℂ) ^ ((m : ℂ) / 2) * allZLam chi₀ (m : ℤ) n * (n : ℂ) ^ (-s) := by
      refine tsum_congr (fun n => ?_)
      rw [hwp n]
    rw [h1, ← fullHeckeLSeries_eq_tsum_allZLam chi₀ m hchi hs]
  rw [hLHS, hC, hR]

end

end Work.FIArea6Hecke.R
