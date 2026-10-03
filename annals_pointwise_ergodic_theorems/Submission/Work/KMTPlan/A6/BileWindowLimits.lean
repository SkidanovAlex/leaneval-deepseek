/-
# The window `ψ` of the bilinear lifting argument (Theorem `bile` at `r = 1`)

This module proves `Work.KMTPlan.A6.BileWindowLimits`, one of the five pieces of the lifting
proof of Theorem `bile` at `r = 1` (wired in `Submission/Work/KMTPlan/A6/BileAssembly.lean`).

The window is a Schwartz function `ψ : ℝ → ℂ` whose Fourier transform `𝓕ψ` is supported in
`[-1,1]` and whose `L²(ℝ)`-norm is `1`; its existence (the normalised inverse Fourier
transform of a smooth bump) is `BilePsiExists`.  The two estimates are the two window limits
consumed by the assembly:

* (`ℓ²` up) the lifted sequence `n ↦ R^{-1/2} ψ(n/R) u (n mod Q)` of `u : ℤ/Qℤ → ℂ` has
  `ℓ²(ℤ)`-norm at most `(1+ε)‖u‖_{L²(ℤ/Qℤ)}` for `R` large;
* (weighted `ℓ¹` down) `R⁻¹ ∑_x ‖ψ(x/R)‖² ‖u (x mod Q)‖ ≥ (1-ε)‖u‖_{L¹(ℤ/Qℤ)}` for `R`
  large.

Both are consequences of the single residue-class Riemann-sum limit
`BileWindowSumLimit`, `R⁻¹ ∑_n g(n/R) w (n mod Q) → (∫ g) · Q⁻¹ ∑_z w z` for a
differentiable integrable `g` with integrable derivative, `∫ g = 1` and `w ≥ 0`, applied to
`g = ‖ψ‖² ∈ 𝓢(ℝ)` (the analytic facts needed are `BileWeightFacts`) with `w = ‖u‖²`
respectively `w = ‖u‖`.  The passage from the `ℝ≥0∞`-valued `eLpNorm` with respect to the
counting measure on `ℤ` to the real `ℓ²`-sum is `BileELpNormCount`.
-/
import Mathlib
import Submission.Work.Analysis.Concentration.Basic
import Submission.Work.KMTContract.Defs
import Submission.Work.KMTPlan.A6.BilePsiExists
import Submission.Work.KMTPlan.A6.BileWindowSumLimit
import Submission.Work.KMTPlan.A6.BileELpNormCount
import Submission.Work.KMTPlan.A6.BileWeightFacts

-- v4.35 port: restore the v4.34 instance-unification behaviour (respectTransparency) in this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

set_option maxHeartbeats 1000000

namespace Work.KMTPlan.A6

open MeasureTheory Filter
open scoped ENNReal BigOperators FourierTransform

variable {Q : ℕ} [NeZero Q]

private lemma lpNormZMod_one (u : ZMod Q → ℂ) :
    Work.Analysis.Concentration.LpNormZMod Q 1 u = (Q : ℝ)⁻¹ * ∑ z : ZMod Q, ‖u z‖ := by
  unfold Work.Analysis.Concentration.LpNormZMod
  simp only [Real.rpow_one, div_one]

private lemma lpNormZMod_two_sq (u : ZMod Q → ℂ) :
    (Work.Analysis.Concentration.LpNormZMod Q 2 u) ^ 2
      = (Q : ℝ)⁻¹ * ∑ z : ZMod Q, ‖u z‖ ^ 2 := by
  have hnn : 0 ≤ (Q : ℝ)⁻¹ * ∑ z : ZMod Q, ‖u z‖ ^ (2 : ℝ) := by
    apply mul_nonneg (by positivity)
    exact Finset.sum_nonneg fun z _ => Real.rpow_nonneg (norm_nonneg _) 2
  unfold Work.Analysis.Concentration.LpNormZMod
  rw [← Real.sqrt_eq_rpow, Real.sq_sqrt hnn]
  congr 1
  exact Finset.sum_congr rfl fun z _ => Real.rpow_natCast _ 2

private lemma lpNormZMod_one_nonneg (u : ZMod Q → ℂ) :
    0 ≤ Work.Analysis.Concentration.LpNormZMod Q 1 u := by
  rw [lpNormZMod_one]
  exact mul_nonneg (by positivity) (Finset.sum_nonneg fun z _ => norm_nonneg _)

private lemma lpNormZMod_two_nonneg (u : ZMod Q → ℂ) :
    0 ≤ Work.Analysis.Concentration.LpNormZMod Q 2 u := by
  have hnn : 0 ≤ (Q : ℝ)⁻¹ * ∑ z : ZMod Q, ‖u z‖ ^ (2 : ℝ) := by
    apply mul_nonneg (by positivity)
    exact Finset.sum_nonneg fun z _ => Real.rpow_nonneg (norm_nonneg _) 2
  unfold Work.Analysis.Concentration.LpNormZMod
  exact Real.rpow_nonneg hnn (1 / 2)

private lemma eq_zero_of_lpNormZMod_one_eq_zero {u : ZMod Q → ℂ}
    (h : Work.Analysis.Concentration.LpNormZMod Q 1 u = 0) : u = 0 := by
  have hsum : ∑ z : ZMod Q, ‖u z‖ = 0 := by
    have h1 : (Q : ℝ)⁻¹ * ∑ z : ZMod Q, ‖u z‖ = 0 := by rw [← lpNormZMod_one]; exact h
    rcases mul_eq_zero.mp h1 with h2 | h2
    · exact absurd h2 (inv_ne_zero (Nat.cast_ne_zero.mpr (NeZero.ne Q)))
    · exact h2
  funext z
  have hz : ‖u z‖ = 0 := by
    have := (Finset.sum_eq_zero_iff_of_nonneg (fun z _ => norm_nonneg (u z))).mp hsum z (Finset.mem_univ z)
    simpa using this
  simpa using hz

private lemma eq_zero_of_lpNormZMod_two_eq_zero {u : ZMod Q → ℂ}
    (h : Work.Analysis.Concentration.LpNormZMod Q 2 u = 0) : u = 0 := by
  have hsq : (Q : ℝ)⁻¹ * ∑ z : ZMod Q, ‖u z‖ ^ 2 = 0 := by
    rw [← lpNormZMod_two_sq]
    rw [h]
    norm_num
  have hsum : ∑ z : ZMod Q, ‖u z‖ ^ 2 = 0 := by
    rcases mul_eq_zero.mp hsq with h2 | h2
    · exact absurd h2 (inv_ne_zero (Nat.cast_ne_zero.mpr (NeZero.ne Q)))
    · exact h2
  funext z
  have hz : ‖u z‖ ^ 2 = 0 := by
    have := (Finset.sum_eq_zero_iff_of_nonneg (fun z _ => by positivity)).mp hsum z (Finset.mem_univ z)
    simpa using this
  have hzero : ‖u z‖ = 0 := by
    have := sq_eq_zero_iff.mp hz
    simpa using this
  simpa using hzero

theorem BileWindowLimits :
    ∃ ψ : SchwartzMap ℝ ℂ,
      (∀ ξ : ℝ, 1 < |ξ| → Work.Analysis.InverseTheory.realFourier (ψ : ℝ → ℂ) ξ = 0) ∧
      MeasureTheory.eLpNorm (ψ : ℝ → ℂ) 2 MeasureTheory.volume = 1 ∧
      (∀ {Q : ℕ} [NeZero Q], 1 ≤ Q → ∀ u : ZMod Q → ℂ, ∀ ε : ℝ, 0 < ε →
        ∃ R₀ : ℕ, ∀ R : ℕ, R₀ ≤ R →
          MeasureTheory.eLpNorm (fun n : ℤ =>
              ((Real.sqrt (R : ℝ))⁻¹ : ℂ) * (ψ ((n : ℝ) / (R : ℝ))) * u (n : ZMod Q))
            2 MeasureTheory.Measure.count
            ≤ ENNReal.ofReal (1 + ε) *
                ENNReal.ofReal (Work.Analysis.Concentration.LpNormZMod Q 2 u)) ∧
      (∀ {Q : ℕ} [NeZero Q], 1 ≤ Q → ∀ u : ZMod Q → ℂ, ∀ ε : ℝ, 0 < ε →
        ∃ R₀ : ℕ, ∀ R : ℕ, R₀ ≤ R →
          ENNReal.ofReal ((1 - ε) * Work.Analysis.Concentration.LpNormZMod Q 1 u)
            ≤ ENNReal.ofReal ((R : ℝ)⁻¹ *
                ∑' x : ℤ, (‖ψ ((x : ℝ) / (R : ℝ))‖ ^ 2) *
                  ‖u (x : ZMod Q)‖)) := by
  obtain ⟨ψ, hψsupp, hψL2, hψint⟩ := BilePsiExists
  obtain ⟨hgd, hgint, hgint', hgsumm⟩ := BileWeightFacts ψ
  refine ⟨ψ, hψsupp, hψL2, ?_, ?_⟩
  · intro Q hNZ hQ u ε hε
    by_cases hu : u = 0
    · refine ⟨1, fun R hR => ?_⟩
      have hz : (fun n : ℤ =>
            ((Real.sqrt (R : ℝ))⁻¹ : ℂ) * (ψ ((n : ℝ) / (R : ℝ))) * u (n : ZMod Q)) = 0 := by
        funext n
        simp [hu]
      rw [hz, MeasureTheory.eLpNorm_zero]
      exact zero_le
    · obtain ⟨z, hzx⟩ := Function.ne_iff.mp hu
      have hApos : 0 < Work.Analysis.Concentration.LpNormZMod Q 2 u := by
        rcases lt_or_ge (0 : ℝ) (Work.Analysis.Concentration.LpNormZMod Q 2 u) with h | h
        · exact h
        · exact absurd (congrFun (eq_zero_of_lpNormZMod_two_eq_zero
            (le_antisymm h (lpNormZMod_two_nonneg u))) z) hzx
      set A := Work.Analysis.Concentration.LpNormZMod Q 2 u with hAdef
      have hAsq : A ^ 2 = (Q : ℝ)⁻¹ * ∑ z : ZMod Q, ‖u z‖ ^ 2 := lpNormZMod_two_sq u
      have hQ2pos : 0 < (Q : ℝ)⁻¹ * ∑ z : ZMod Q, ‖u z‖ ^ 2 := by
        rw [← hAsq]; positivity
      have hδpos : 0 < ((1 + ε) ^ 2 - 1) * ((Q : ℝ)⁻¹ * ∑ z : ZMod Q, ‖u z‖ ^ 2) :=
        mul_pos (by nlinarith) hQ2pos
      obtain ⟨R₀, hR₀⟩ := BileWindowSumLimit hgd hgint hgint' hψint hQ
        (fun z : ZMod Q => ‖u z‖ ^ 2) (fun z => by positivity)
        (((1 + ε) ^ 2 - 1) * ((Q : ℝ)⁻¹ * ∑ z : ZMod Q, ‖u z‖ ^ 2)) hδpos
      refine ⟨max R₀ 1, fun R hR => ?_⟩
      have hR₀' : R₀ ≤ R := le_trans (le_max_left _ _) hR
      have hR1 : 1 ≤ R := le_trans (le_max_right _ _) hR
      have hRpos : (0 : ℝ) < (R : ℝ) := by
        have h1 : (1 : ℝ) ≤ (R : ℝ) := by exact_mod_cast hR1
        linarith
      set f := (fun n : ℤ =>
          ((Real.sqrt (R : ℝ))⁻¹ : ℂ) * (ψ ((n : ℝ) / (R : ℝ))) * u (n : ZMod Q)) with hfdef
      set S := ∑' n : ℤ, ‖(ψ : ℝ → ℂ) ((n : ℝ) / (R : ℝ))‖ ^ 2 * ‖u (n : ZMod Q)‖ ^ 2 with hSdef
      have hb : |(R : ℝ)⁻¹ * S - (Q : ℝ)⁻¹ * (∑ z : ZMod Q, ‖u z‖ ^ 2)|
          ≤ ((1 + ε) ^ 2 - 1) * ((Q : ℝ)⁻¹ * ∑ z : ZMod Q, ‖u z‖ ^ 2) := by
        simpa [hSdef] using hR₀ R hR₀'
      have hle' : (R : ℝ)⁻¹ * S ≤ (1 + ε) ^ 2 * ((Q : ℝ)⁻¹ * ∑ z : ZMod Q, ‖u z‖ ^ 2) := by
        have h := (abs_le.mp hb).2
        nlinarith
      have hnorm : ∀ n : ℤ, ‖f n‖ ^ 2
          = (R : ℝ)⁻¹ * (‖(ψ : ℝ → ℂ) ((n : ℝ) / (R : ℝ))‖ ^ 2 * ‖u (n : ZMod Q)‖ ^ 2) := by
        have hsqrt : (Real.sqrt (R : ℝ))⁻¹ ^ 2 = (R : ℝ)⁻¹ := by
          rw [inv_pow, Real.sq_sqrt (by positivity : (0 : ℝ) ≤ (R : ℝ))]
        intro n
        simp only [hfdef]
        rw [norm_mul, norm_mul, norm_inv, Complex.norm_real,
          Real.norm_of_nonneg (by positivity : (0 : ℝ) ≤ Real.sqrt (R : ℝ)),
          mul_pow, mul_pow, hsqrt, mul_assoc]
      have h1 : (∑' n : ℤ, ‖f n‖ ^ 2) = (R : ℝ)⁻¹ * S := by
        rw [tsum_congr hnorm, ← tsum_mul_left]
      have hu_bound : ∀ n : ℤ, ‖u (n : ZMod Q)‖ ≤ ‖u‖ := fun n => norm_le_pi_norm u (n : ZMod Q)
      have hsummψ : Summable (fun n : ℤ => ‖(ψ : ℝ → ℂ) ((n : ℝ) / (R : ℝ))‖ ^ 2) :=
        hgsumm R (by omega)
      have hsumm2 : Summable (fun n : ℤ =>
          (R : ℝ)⁻¹ * (‖u‖ ^ 2 * ‖(ψ : ℝ → ℂ) ((n : ℝ) / (R : ℝ))‖ ^ 2)) :=
        (hsummψ.mul_left (‖u‖ ^ 2)).mul_left _
      have hsumm : Summable (fun n : ℤ => ‖f n‖ ^ 2) := by
        refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_) hsumm2
        rw [hnorm n]
        have h1' : ‖u (n : ZMod Q)‖ ^ 2 ≤ ‖u‖ ^ 2 := by
          nlinarith [hu_bound n, norm_nonneg (u (n : ZMod Q)), norm_nonneg u]
        have h2' : 0 ≤ (R : ℝ)⁻¹ := by positivity
        have h3' : 0 ≤ ‖(ψ : ℝ → ℂ) ((n : ℝ) / (R : ℝ))‖ ^ 2 := by positivity
        calc (R : ℝ)⁻¹ * (‖(ψ : ℝ → ℂ) ((n : ℝ) / (R : ℝ))‖ ^ 2 * ‖u (n : ZMod Q)‖ ^ 2)
            ≤ (R : ℝ)⁻¹ * (‖(ψ : ℝ → ℂ) ((n : ℝ) / (R : ℝ))‖ ^ 2 * ‖u‖ ^ 2) :=
              mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h1' h3') h2'
          _ = (R : ℝ)⁻¹ * (‖u‖ ^ 2 * ‖(ψ : ℝ → ℂ) ((n : ℝ) / (R : ℝ))‖ ^ 2) := by ring
      have hmain : (∑' n : ℤ, ‖f n‖ ^ 2) ≤ ((1 + ε) * A) ^ 2 := by
        rw [h1]
        calc (R : ℝ)⁻¹ * S ≤ (1 + ε) ^ 2 * ((Q : ℝ)⁻¹ * ∑ z : ZMod Q, ‖u z‖ ^ 2) := hle'
          _ = ((1 + ε) * A) ^ 2 := by rw [← hAsq]; ring
      rw [BileELpNormCount f hsumm]
      rw [← ENNReal.ofReal_mul (by linarith : (0 : ℝ) ≤ 1 + ε)]
      apply ENNReal.ofReal_le_ofReal
      have hsqrt : Real.sqrt (∑' n : ℤ, ‖f n‖ ^ 2) ≤ (1 + ε) * A := by
        calc Real.sqrt (∑' n : ℤ, ‖f n‖ ^ 2) ≤ Real.sqrt (((1 + ε) * A) ^ 2) :=
              Real.sqrt_le_sqrt hmain
          _ = (1 + ε) * A := Real.sqrt_sq (by positivity)
      simpa [hAdef] using hsqrt
  · intro Q hNZ hQ u ε hε
    by_cases hu : u = 0
    · refine ⟨1, fun R hR => ?_⟩
      have hL : Work.Analysis.Concentration.LpNormZMod Q 1 u = 0 := by
        rw [lpNormZMod_one]
        simp [hu]
      rw [hL, mul_zero, ENNReal.ofReal_zero]
      exact zero_le
    · obtain ⟨z, hzx⟩ := Function.ne_iff.mp hu
      have hLpos : 0 < Work.Analysis.Concentration.LpNormZMod Q 1 u := by
        rcases lt_or_ge (0 : ℝ) (Work.Analysis.Concentration.LpNormZMod Q 1 u) with h | h
        · exact h
        · exact absurd (congrFun (eq_zero_of_lpNormZMod_one_eq_zero
            (le_antisymm h (lpNormZMod_one_nonneg u))) z) hzx
      set L := Work.Analysis.Concentration.LpNormZMod Q 1 u with hLdef
      obtain ⟨R₀, hR₀⟩ := BileWindowSumLimit hgd hgint hgint' hψint hQ
        (fun z : ZMod Q => ‖u z‖) (fun z => norm_nonneg _) (ε * L) (by positivity)
      refine ⟨max R₀ 1, fun R hR => ?_⟩
      have hR₀' : R₀ ≤ R := le_trans (le_max_left _ _) hR
      have hL1 : L = (Q : ℝ)⁻¹ * ∑ z : ZMod Q, ‖u z‖ := lpNormZMod_one u
      have hb := hR₀ R hR₀'
      have hlow : (1 - ε) * L
          ≤ (R : ℝ)⁻¹ * (∑' x : ℤ, (‖(ψ : ℝ → ℂ) ((x : ℝ) / (R : ℝ))‖ ^ 2) * ‖u (x : ZMod Q)‖) := by
        have h2' : -(ε * L)
            ≤ (R : ℝ)⁻¹ * (∑' x : ℤ, (‖(ψ : ℝ → ℂ) ((x : ℝ) / (R : ℝ))‖ ^ 2) * ‖u (x : ZMod Q)‖)
              - (Q : ℝ)⁻¹ * ∑ z : ZMod Q, ‖u z‖ := (abs_le.mp hb).1
        rw [← hL1] at h2'
        linarith
      simpa [hLdef] using ENNReal.ofReal_le_ofReal hlow

end Work.KMTPlan.A6
