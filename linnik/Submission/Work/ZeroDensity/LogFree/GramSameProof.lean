import Mathlib
import Submission.Work.ZeroDensity.LogFree.GramResidueDefs
import Submission.Work.ZeroDensity.Jutila.mellinSmoothedDirichlet
import Submission.Work.LinnikAreas.Density4.mollSeries_eq
import Submission.Work.LinnikAreas.Density4.thetaS_Icc_eq
import Submission.Work.LinnikAreas.Density4.tsum_ite_dvd
import Submission.Commons.NumberTheory.DivisorBound.card_divisors_le_rpow

/-!
# `Work.ZeroDensity.LogFree.GramSameProof` — the residue decomposition of `gramEntrySame`

The `q`-free Gram entry `gramEntryFree W X U' ρ ρ'` is the smoothed sum
`Σ_n (Σ_{d|n}θ_d)² n^{s₀}(e^{-n/X} - e^{-n/U'})` with `s₀ = 1-ρ-conj ρ'`.  This module builds,
from the inverse-Mellin representation of an exponentially damped Dirichlet sum and the
contour shift across the single ζ-pole of the integrand, the identity

  `gramEntryFree W X U' ρ ρ' - (poleResidue W : ℂ) * poleK X U' ρ ρ'
      = (1/2π) ∫_ℝ gramPhi W X U' s₀ (δ + it) dt`,   `δ = s₀.re`,

together with the analytic bounds on that contour integral.
-/

open DirichletCharacter Complex Filter MeasureTheory
open scoped Classical BigOperators Topology
set_option maxHeartbeats 1000000
noncomputable section

namespace Work.ZeroDensity.LogFree

open Work.LinnikAreas.Density4

/-! ## 1. The Dirichlet series of the squared mollifier -/

open Work.LinnikAreas.Density4

/-- Summability of one summand of the `(d,e)` expansion of the squared mollifier. -/
lemma summable_gramInner {W : ℝ} {w : ℂ} (hw : 1 < w.re) (d e : ℕ) :
    Summable (fun n : ℕ => (if d ∣ n then ((thetaM W d : ℝ) : ℂ) else 0)
      * (if e ∣ n then ((thetaM W e : ℝ) : ℂ) else 0) * (n : ℂ) ^ (-w)) := by
  have hw0 : w ≠ 0 := by intro h; rw [h] at hw; simp at hw; linarith
  set C : ℝ := ‖((thetaM W d : ℝ) : ℂ)‖ * ‖((thetaM W e : ℝ) : ℂ)‖ with hC
  refine Summable.of_norm_bounded (g := fun n : ℕ => C * (n : ℝ) ^ (-w.re)) ?_ ?_
  · exact (Real.summable_nat_rpow.mpr (by linarith)).mul_left C
  · intro n
    have h1 : ‖(if d ∣ n then ((thetaM W d : ℝ) : ℂ) else 0)‖ ≤ ‖((thetaM W d : ℝ) : ℂ)‖ := by
      split_ifs <;> simp
    have h2 : ‖(if e ∣ n then ((thetaM W e : ℝ) : ℂ) else 0)‖ ≤ ‖((thetaM W e : ℝ) : ℂ)‖ := by
      split_ifs <;> simp
    have hP : (0:ℝ) ≤ (n : ℝ) ^ (-w.re) := Real.rpow_nonneg (Nat.cast_nonneg n) _
    have h4 : ‖(n : ℂ) ^ (-w)‖ ≤ (n : ℝ) ^ (-w.re) := by
      rcases Nat.eq_zero_or_pos n with hn | hn
      · subst hn
        rw [Nat.cast_zero, Complex.zero_cpow (neg_ne_zero.mpr hw0)]
        simp only [norm_zero]
        positivity
      · rw [Complex.norm_natCast_cpow_of_pos hn (-w), Complex.neg_re]
    calc ‖(if d ∣ n then ((thetaM W d : ℝ) : ℂ) else 0)
            * (if e ∣ n then ((thetaM W e : ℝ) : ℂ) else 0) * (n : ℂ) ^ (-w)‖
        = ‖(if d ∣ n then ((thetaM W d : ℝ) : ℂ) else 0)
            * (if e ∣ n then ((thetaM W e : ℝ) : ℂ) else 0)‖ * ‖(n : ℂ) ^ (-w)‖ := by
          rw [norm_mul]
      _ ≤ (‖((thetaM W d : ℝ) : ℂ)‖ * ‖((thetaM W e : ℝ) : ℂ)‖) * (n : ℝ) ^ (-w.re) := by
          refine mul_le_mul ?_ h4 (norm_nonneg _) (by positivity)
          rw [norm_mul]
          exact mul_le_mul h1 h2 (norm_nonneg _) (norm_nonneg _)
      _ = C * (n : ℝ) ^ (-w.re) := by rw [hC]

/-- The `(d,e)`-summand of the squared mollifier, re-indexed over the multiples of `[d,e]`. -/
lemma gramInner_tsum {W : ℝ} {w : ℂ} (hw : 1 < w.re) {d e : ℕ} (hd : 1 ≤ d) (he : 1 ≤ e) :
    (∑' n : ℕ, (if d ∣ n then ((thetaM W d : ℝ) : ℂ) else 0)
        * (if e ∣ n then ((thetaM W e : ℝ) : ℂ) else 0) * (n : ℂ) ^ (-w))
      = ((thetaM W d : ℝ) : ℂ) * ((thetaM W e : ℝ) : ℂ)
          * (((Nat.lcm d e : ℕ) : ℂ) ^ (-w)) * riemannZeta w := by
  set l : ℕ := Nat.lcm d e with hl
  have hlpos : 0 < l := by rw [hl]; exact Nat.lcm_pos (by omega) (by omega)
  have hkey : ∀ n : ℕ,
      (if d ∣ n then ((thetaM W d : ℝ) : ℂ) else 0)
        * (if e ∣ n then ((thetaM W e : ℝ) : ℂ) else 0) * (n : ℂ) ^ (-w)
      = (((thetaM W d : ℝ) : ℂ) * ((thetaM W e : ℝ) : ℂ))
          * ((if l ∣ n then (1 : ℂ) else 0) * ((n : ℂ) ^ (-w))) := by
    intro n
    by_cases hdl : d ∣ n <;> by_cases hel : e ∣ n
    · have hll : l ∣ n := by rw [hl]; exact Nat.lcm_dvd hdl hel
      rw [if_pos hdl, if_pos hel, if_pos hll]; ring
    · have hll : ¬ l ∣ n := by
        intro h; rw [hl] at h; exact hel (dvd_trans (Nat.dvd_lcm_right d e) h)
      rw [if_pos hdl, if_neg hel, if_neg hll]; ring
    · have hll : ¬ l ∣ n := by
        intro h; rw [hl] at h; exact hdl (dvd_trans (Nat.dvd_lcm_left d e) h)
      rw [if_neg hdl, if_neg hll]; ring
    · have hll : ¬ l ∣ n := by
        intro h; rw [hl] at h; exact hdl (dvd_trans (Nat.dvd_lcm_left d e) h)
      rw [if_neg hdl, if_neg hll]; ring
  have h1 : (∑' n : ℕ, (if d ∣ n then ((thetaM W d : ℝ) : ℂ) else 0)
        * (if e ∣ n then ((thetaM W e : ℝ) : ℂ) else 0) * (n : ℂ) ^ (-w))
      = (((thetaM W d : ℝ) : ℂ) * ((thetaM W e : ℝ) : ℂ)) * (∑' n : ℕ,
          (if l ∣ n then (1 : ℂ) else 0) * ((n : ℂ) ^ (-w))) := by
    rw [tsum_congr hkey, tsum_mul_left]
  have h2 : (∑' n : ℕ, (if l ∣ n then (1 : ℂ) else 0) * ((n : ℂ) ^ (-w)))
      = ∑' n : ℕ, (if l ∣ n then ((n : ℂ) ^ (-w)) else 0) := by
    refine tsum_congr fun n => ?_
    by_cases h : l ∣ n <;> simp [h]
  have h3 : (∑' n : ℕ, (if l ∣ n then ((n : ℂ) ^ (-w)) else 0))
      = ∑' m : ℕ, (((l * m : ℕ)) : ℂ) ^ (-w) :=
    tsum_ite_dvd hlpos _
  have h4 : (∑' m : ℕ, (((l * m : ℕ)) : ℂ) ^ (-w))
      = (((l : ℕ) : ℂ) ^ (-w)) * riemannZeta w := by
    have hpt : ∀ m : ℕ, (((l * m : ℕ)) : ℂ) ^ (-w)
        = (((l : ℕ) : ℂ) ^ (-w)) * (((m : ℕ) : ℂ) ^ (-w)) := by
      intro m
      rw [Nat.cast_mul]
      exact Complex.natCast_mul_natCast_cpow l m (-w)
    rw [tsum_congr hpt, tsum_mul_left]
    congr 1
    rw [zeta_eq_tsum_one_div_nat_cpow hw]
    refine tsum_congr fun m => ?_
    rw [Complex.cpow_neg, one_div]
  rw [h1, h2, h3, h4, hl]
  ring

/-- The Dirichlet series of the squared mollifier: `Σ_n (Σ_{d|n}θ_d)² n^{-w} = ζ(w)·A(w)`
for `Re w > 1`, where `A(w) = Σ_{d,e ≤ ⌈W⌉} θ_dθ_e [d,e]^{-w} = gramA W 0 w` is the finite
"lcm weight" of HB §11. -/
theorem gramDS_eq (W : ℝ) (w : ℂ) (hw : 1 < w.re) :
    (∑' n : ℕ, (((thetaS W n : ℝ)) : ℂ) ^ 2 * (n : ℂ) ^ (-w))
      = riemannZeta w * gramA W 0 w := by
  classical
  have hwne : w ≠ 0 := by intro h; rw [h] at hw; simp at hw; linarith
  have hzw : (0 : ℂ) ^ (-w) = 0 := Complex.zero_cpow (neg_ne_zero.mpr hwne)
  have hpt : ∀ n : ℕ,
      (((thetaS W n : ℝ)) : ℂ) ^ 2 * (n : ℂ) ^ (-w)
        = ∑ d ∈ Finset.Icc 1 (Nat.ceil W), ∑ e ∈ Finset.Icc 1 (Nat.ceil W),
            (if d ∣ n then ((thetaM W d : ℝ) : ℂ) else 0)
              * (if e ∣ n then ((thetaM W e : ℝ) : ℂ) else 0) * (n : ℂ) ^ (-w) := by
    intro n
    rcases eq_or_ne n 0 with h0 | h0
    · subst h0
      rw [Nat.cast_zero, hzw]
      simp
    · have hbs : ((Work.ZeroDensity.LogFree.thetaS W n : ℝ) : ℂ)
          = ∑ e ∈ Finset.Icc 1 (Nat.ceil W),
              (if e ∣ n then ((thetaM W e : ℝ) : ℂ) else 0) :=
        Work.LinnikAreas.Density4.thetaS_Icc_eq W n h0
      have hsq : (((thetaS W n : ℝ)) : ℂ) ^ 2
          = (∑ d ∈ Finset.Icc 1 (Nat.ceil W),
                (if d ∣ n then ((thetaM W d : ℝ) : ℂ) else 0))
              * (∑ e ∈ Finset.Icc 1 (Nat.ceil W),
                (if e ∣ n then ((thetaM W e : ℝ) : ℂ) else 0)) := by
        rw [sq, hbs]
      rw [hsq, Finset.sum_mul_sum, Finset.sum_mul]
      exact Finset.sum_congr rfl fun d _ => by rw [Finset.sum_mul]
  rw [tsum_congr hpt]
  rw [Summable.tsum_finsetSum (fun d _ => summable_sum (fun e _ => summable_gramInner hw d e))]
  have hper : ∀ d ∈ Finset.Icc 1 (Nat.ceil W),
      (∑' n : ℕ, ∑ e ∈ Finset.Icc 1 (Nat.ceil W),
          (if d ∣ n then ((thetaM W d : ℝ) : ℂ) else 0)
            * (if e ∣ n then ((thetaM W e : ℝ) : ℂ) else 0) * (n : ℂ) ^ (-w))
        = ∑ e ∈ Finset.Icc 1 (Nat.ceil W), ((thetaM W d : ℝ) : ℂ) * ((thetaM W e : ℝ) : ℂ)
            * (((Nat.lcm d e : ℕ) : ℂ) ^ (-w)) * riemannZeta w := by
    intro d hd
    refine (Summable.tsum_finsetSum (fun e _ => summable_gramInner hw d e)).trans ?_
    refine Finset.sum_congr rfl fun e he => ?_
    exact gramInner_tsum hw (Finset.mem_Icc.mp hd).1 (Finset.mem_Icc.mp he).1
  rw [Finset.sum_congr rfl hper]
  rw [gramA]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [show (0 : ℂ) - w = -w by ring]
  ring


/-! ## 2. Summability of the coefficient series -/

open Work.LinnikAreas.Density4

/-- `‖(Σ_{d|n}θ_d)²‖ ≤ C n^ε`. -/
lemma norm_thetaS_sq_le (W ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, ‖(((thetaS W n : ℝ)) : ℂ) ^ 2‖ ≤ C * (n : ℝ) ^ (2 * ε) := by
  obtain ⟨C, hCpos, hC⟩ := Commons.NumberTheory.DivisorBound.card_divisors_le_rpow ε hε
  refine ⟨C ^ 2, by positivity, fun n => ?_⟩
  have h1 : |thetaS W n| ≤ ((n.divisors.card : ℕ) : ℝ) := abs_thetaS_le_card_divisors W n
  have h2 : ‖(((thetaS W n : ℝ)) : ℂ) ^ 2‖ = |thetaS W n| ^ 2 := by
    rw [norm_pow, Complex.norm_real, Real.norm_eq_abs]
  have h3 : (0 : ℝ) ≤ ((n.divisors.card : ℕ) : ℝ) := Nat.cast_nonneg _
  have h4 : (0 : ℝ) ≤ (n : ℝ) ^ (2 * ε) := Real.rpow_nonneg (Nat.cast_nonneg n) _
  have h5 : |thetaS W n| ^ 2 ≤ (((n.divisors.card : ℕ) : ℝ) * 1) ^ 2 := by
    nlinarith [abs_nonneg (thetaS W n), h1]
  have h6 : (((n.divisors.card : ℕ) : ℝ)) ^ 2 ≤ (C * (n : ℝ) ^ ε) ^ 2 :=
    pow_le_pow_left₀ h3 (hC n) 2
  have h7 : (C * (n : ℝ) ^ ε) ^ 2 = C ^ 2 * (n : ℝ) ^ (2 * ε) := by
    rw [mul_pow, ← Real.rpow_natCast ((n:ℝ) ^ ε) 2, ← Real.rpow_mul (Nat.cast_nonneg n)]
    ring_nf
  rw [h2]
  calc |thetaS W n| ^ 2 ≤ (((n.divisors.card : ℕ) : ℝ)) ^ 2 := by
        rw [mul_one] at h5; exact h5
    _ ≤ (C * (n : ℝ) ^ ε) ^ 2 := h6
    _ = C ^ 2 * (n : ℝ) ^ (2 * ε) := h7

/-- Summability of the majorant for the Mellin representation. -/
lemma summable_thetaS_sq_majorant (W : ℝ) {s₀ : ℂ} (hs : s₀.re < 0) :
    Summable (fun n : ℕ => ‖(((thetaS W n : ℝ)) : ℂ) ^ 2‖ * (n : ℝ) ^ (s₀.re - 2)) := by
  obtain ⟨C, hCpos, hC⟩ := norm_thetaS_sq_le W ((1 - s₀.re) / 4) (by linarith)
  have hg : Summable (fun n : ℕ => (n : ℝ) ^ (-(3 / 2 : ℝ))) :=
    Real.summable_nat_rpow.mpr (by norm_num)
  refine Summable.of_nonneg_of_le
    (fun n => mul_nonneg (norm_nonneg _) (Real.rpow_nonneg (Nat.cast_nonneg n) _))
    (fun n => ?_) (hg.mul_left C)
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    rw [Nat.cast_zero, Real.zero_rpow (by linarith : s₀.re - 2 ≠ 0)]
    simp
  · have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    have h1 := hC n
    have h2 : (2:ℝ) * ((1 - s₀.re) / 4) = (1 - s₀.re) / 2 := by ring
    rw [h2] at h1
    calc ‖(((thetaS W n : ℝ)) : ℂ) ^ 2‖ * (n : ℝ) ^ (s₀.re - 2)
        ≤ (C * (n : ℝ) ^ ((1 - s₀.re) / 2)) * (n : ℝ) ^ (s₀.re - 2) :=
          mul_le_mul_of_nonneg_right h1 (Real.rpow_nonneg (Nat.cast_nonneg n) _)
      _ = C * ((n : ℝ) ^ ((1 - s₀.re) / 2) * (n : ℝ) ^ (s₀.re - 2)) := by ring
      _ = C * (n : ℝ) ^ ((1 - s₀.re) / 2 + (s₀.re - 2)) := by
          rw [← Real.rpow_add hnpos]
      _ ≤ C * (n : ℝ) ^ (-(3 / 2 : ℝ)) := by
          apply mul_le_mul_of_nonneg_left _ hCpos.le
          apply Real.rpow_le_rpow_of_exponent_le hn1
          nlinarith



/-! ## 3. The exponentially damped coefficient series -/
lemma summable_thetaS_sq_mul_exp (W X : ℝ) (hX : 0 < X) {s₀ : ℂ} (hs₀ : s₀.re ≤ 0) :
    Summable (fun n : ℕ => (((thetaS W n : ℝ)) : ℂ) ^ 2 * (n : ℂ) ^ (s₀)
      * ((Real.exp (-((n : ℝ) / X)) : ℝ) : ℂ)) := by
  obtain ⟨C, hCpos, hC⟩ := norm_thetaS_sq_le W (1 / 2) (by norm_num)
  have hC1 : ∀ n : ℕ, ‖(((thetaS W n : ℝ)) : ℂ) ^ 2‖ ≤ C * (n : ℝ) ^ (1 : ℝ) := by
    intro n
    have h := hC n
    rwa [show (2 : ℝ) * (1 / 2) = (1 : ℝ) by norm_num] at h
  have hg : Summable (fun n : ℕ => C * ((n : ℝ) ^ (1 : ℕ) * Real.exp ((-(1 / X)) * (n : ℝ)))) :=
    (Real.summable_pow_mul_exp_neg_nat_mul 1 (by positivity : (0 : ℝ) < 1 / X)).mul_left C
  refine Summable.of_norm_bounded (g := fun n : ℕ =>
    C * ((n : ℝ) ^ (1 : ℕ) * Real.exp ((-(1 / X)) * (n : ℝ)))) hg (fun n => ?_)
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    simp [thetaS, Nat.divisors_zero]
  · have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    have hnorm : ‖(((thetaS W n : ℝ)) : ℂ) ^ 2 * (n : ℂ) ^ (s₀)
        * ((Real.exp (-((n : ℝ) / X)) : ℝ) : ℂ)‖
        = ‖(((thetaS W n : ℝ)) : ℂ) ^ 2‖ * (n : ℝ) ^ (s₀.re) * Real.exp (-((n : ℝ) / X)) := by
      rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, Real.abs_exp,
        Complex.norm_natCast_cpow_of_pos hn]
    rw [hnorm]
    have hsp : (n : ℝ) ^ (s₀.re) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hn1 hs₀
    have hexp : Real.exp (-((n : ℝ) / X)) = Real.exp ((-(1 / X)) * (n : ℝ)) := by
      congr 1; ring
    rw [hexp]
    have h1 := hC1 n
    have h2 : ‖(((thetaS W n : ℝ)) : ℂ) ^ 2‖ * (n : ℝ) ^ (s₀.re) ≤ C * (n : ℝ) := by
      have h3 : (0 : ℝ) ≤ (n : ℝ) ^ (s₀.re) := Real.rpow_nonneg (Nat.cast_nonneg n) _
      rw [Real.rpow_one] at h1
      calc ‖(((thetaS W n : ℝ)) : ℂ) ^ 2‖ * (n : ℝ) ^ (s₀.re)
          ≤ (C * (n : ℝ)) * 1 := mul_le_mul h1 hsp h3 (by positivity)
        _ = C * (n : ℝ) := by ring
    calc ‖(((thetaS W n : ℝ)) : ℂ) ^ 2‖ * (n : ℝ) ^ (s₀.re) * Real.exp ((-(1 / X)) * (n : ℝ))
        ≤ (C * (n : ℝ)) * Real.exp ((-(1 / X)) * (n : ℝ)) :=
          mul_le_mul_of_nonneg_right h2 (Real.exp_nonneg _)
      _ = C * ((n : ℝ) ^ (1 : ℕ) * Real.exp ((-(1 / X)) * (n : ℝ))) := by
          rw [pow_one]; ring


/-! ## 4. The inverse-Mellin representation of `gramEntryFree` -/

open MeasureTheory in
lemma integrable_gamma_X (X : ℝ) (hX : 0 < X) :
    Integrable (fun t : ℝ => Complex.Gamma ((2 : ℂ) + (t : ℂ) * Complex.I)
      * (X : ℂ) ^ ((2 : ℂ) + (t : ℂ) * Complex.I)) := by
  have hΓ : Integrable (fun t : ℝ => ‖Complex.Gamma ((2 : ℂ) + (t : ℂ) * Complex.I)‖) :=
    Work.ZeroDensity.Jutila.integrable_norm_gamma_vertical 2 (by norm_num)
  have hcontΓ : Continuous (fun t : ℝ => Complex.Gamma ((2 : ℂ) + (t : ℂ) * Complex.I)) := by
    rw [continuous_iff_continuousAt]
    intro t
    exact ContinuousAt.comp (Complex.continuousAt_Gamma _ (fun m hm => by
      have hre : (2 : ℝ) = -(m : ℝ) := by simpa using congrArg Complex.re hm
      have : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
      linarith)) (by fun_prop)
  have h2 : Continuous (fun t : ℝ => (2 : ℂ) + (t : ℂ) * Complex.I) :=
    continuous_const.add (Complex.continuous_ofReal.mul continuous_const)
  have hcontX : Continuous (fun t : ℝ => (X : ℂ) ^ ((2 : ℂ) + (t : ℂ) * Complex.I)) :=
    h2.const_cpow (Or.inl (Complex.ofReal_ne_zero.mpr hX.ne'))
  refine (hΓ.const_mul (X ^ 2)).mono' (hcontΓ.mul hcontX).aestronglyMeasurable
    (Filter.Eventually.of_forall fun t => ?_)
  have hf' : ((2 : ℂ) + (t : ℂ) * Complex.I).re = (2 : ℝ) := by simp
  have hf : (X : ℝ) ^ (((2 : ℂ) + (t : ℂ) * Complex.I).re) = X ^ 2 := by
    rw [hf']; norm_num
  rw [Complex.norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hX, hf]
  exact le_of_eq (by ring)

open MeasureTheory in
lemma integrable_mellinGram (W X : ℝ) {s₀ : ℂ} (hX : 0 < X) (hs : s₀.re < 0) :
    Integrable (fun t : ℝ => Complex.Gamma ((2 : ℂ) + (t : ℂ) * Complex.I)
      * (X : ℂ) ^ ((2 : ℂ) + (t : ℂ) * Complex.I)
      * (∑' n : ℕ, (((thetaS W n : ℝ)) : ℂ) ^ 2
          * (n : ℂ) ^ (-(-s₀ + ((2 : ℂ) + (t : ℂ) * Complex.I))))) := by
  have hsumm := summable_thetaS_sq_majorant W hs
  have hexpre : ∀ t : ℝ, (-(-s₀ + ((2 : ℂ) + (t : ℂ) * Complex.I))).re = s₀.re - 2 := by
    intro t
    have h1 : (-s₀ + ((2 : ℂ) + (t : ℂ) * Complex.I)).re = -s₀.re + 2 := by simp
    rw [Complex.neg_re, h1]; ring
  have hnormterm : ∀ (t : ℝ) (n : ℕ), ‖(((thetaS W n : ℝ)) : ℂ) ^ 2
      * (n : ℂ) ^ (-(-s₀ + ((2 : ℂ) + (t : ℂ) * Complex.I)))‖
      = ‖(((thetaS W n : ℝ)) : ℂ) ^ 2‖ * (n : ℝ) ^ (s₀.re - 2) := by
    intro t n
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn
      rw [Nat.cast_zero]
      simp [thetaS, Nat.divisors_zero]
    · rw [norm_mul, Complex.norm_natCast_cpow_of_pos hn, hexpre t]
  have hsumm' : ∀ t : ℝ, Summable (fun n : ℕ => (((thetaS W n : ℝ)) : ℂ) ^ 2
      * (n : ℂ) ^ (-(-s₀ + ((2 : ℂ) + (t : ℂ) * Complex.I)))) := by
    intro t
    refine Summable.of_norm_bounded (g := fun n : ℕ =>
      ‖(((thetaS W n : ℝ)) : ℂ) ^ 2‖ * (n : ℝ) ^ (s₀.re - 2)) hsumm (fun n => ?_)
    rw [← hnormterm t n]
  have hnormsum : ∀ t : ℝ, ‖∑' n : ℕ, (((thetaS W n : ℝ)) : ℂ) ^ 2
      * (n : ℂ) ^ (-(-s₀ + ((2 : ℂ) + (t : ℂ) * Complex.I)))‖
      ≤ ∑' n : ℕ, ‖(((thetaS W n : ℝ)) : ℂ) ^ 2‖ * (n : ℝ) ^ (s₀.re - 2) := by
    intro t
    refine le_trans (norm_tsum_le_tsum_norm ?_) (le_of_eq (tsum_congr (hnormterm t)))
    have hfun : (fun n : ℕ => ‖(((thetaS W n : ℝ)) : ℂ) ^ 2
        * (n : ℂ) ^ (-(-s₀ + ((2 : ℂ) + (t : ℂ) * Complex.I)))‖) =
        (fun n : ℕ => ‖(((thetaS W n : ℝ)) : ℂ) ^ 2‖ * (n : ℝ) ^ (s₀.re - 2)) :=
      funext (hnormterm t)
    rw [hfun]
    exact hsumm
  have hcont : ∀ n : ℕ, AEMeasurable (fun t : ℝ => (((thetaS W n : ℝ)) : ℂ) ^ 2
      * (n : ℂ) ^ (-(-s₀ + ((2 : ℂ) + (t : ℂ) * Complex.I)))) volume := by
    intro n
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn
      have hne : ∀ t : ℝ, -(-s₀ + ((2 : ℂ) + (t : ℂ) * Complex.I)) ≠ 0 := by
        intro t h
        have h2 := congrArg Complex.re h
        simp only [Complex.zero_re] at h2
        rw [hexpre t] at h2
        linarith [hs]
      have hzero : (fun t : ℝ => (((thetaS W 0 : ℝ)) : ℂ) ^ 2
          * ((((0 : ℕ)) : ℂ) ^ (-(-s₀ + ((2 : ℂ) + (t : ℂ) * Complex.I))))) = fun _ => 0 := by
        funext t
        have h0 : ((((0 : ℕ)) : ℂ)) = (0 : ℂ) := by norm_num
        rw [h0, Complex.zero_cpow (hne t)]
        simp [thetaS, Nat.divisors_zero]
      rw [hzero]
      exact aemeasurable_const
    · have hc : ((n : ℕ) : ℂ) ≠ 0 := by
        rw [← Complex.ofReal_natCast]
        exact Complex.ofReal_ne_zero.mpr (by exact_mod_cast hn.ne')
      have h3 : Continuous (fun t : ℝ => -(-s₀ + ((2 : ℂ) + (t : ℂ) * Complex.I))) := by continuity
      exact (continuous_const.mul ((h3.const_cpow (Or.inl hc)).comp (by fun_prop))).aemeasurable
  have hmeasF : AEStronglyMeasurable (fun t : ℝ => ∑' n : ℕ, (((thetaS W n : ℝ)) : ℂ) ^ 2
      * (n : ℂ) ^ (-(-s₀ + ((2 : ℂ) + (t : ℂ) * Complex.I)))) volume :=
    (AEMeasurable.tsum hcont).aestronglyMeasurable
  exact (integrable_gamma_X X hX).mul_bdd hmeasF (Filter.Eventually.of_forall hnormsum)

open MeasureTheory in
/-- The two exponential normalisations agree. -/
lemma exp_div_form (θ : ℝ) (n : ℕ) :
    ((Real.exp (-(n : ℝ) / θ) : ℝ) : ℂ) = ((Real.exp (-((n : ℝ) / θ)) : ℝ) : ℂ) := by
  congr 1
  ring

open MeasureTheory in
/-- **The inverse-Mellin representation of the `q`-free Gram entry.** -/
theorem gramEntryFree_eq_line (W X U' : ℝ) (ρ ρ' : ℂ) (hX : 0 < X) (hU' : 0 < U')
    (hs : (1 - ρ - (starRingEnd ℂ) ρ').re < 0) :
    gramEntryFree W X U' ρ ρ'
      = (1 / (2 * Real.pi)) * ∫ t : ℝ,
          gramPhi W X U' (1 - ρ - (starRingEnd ℂ) ρ') ((2 : ℂ) + (t : ℂ) * Complex.I) := by
  set s₀ : ℂ := 1 - ρ - (starRingEnd ℂ) ρ' with hs₀def
  have hs₀ : s₀.re < 0 := hs
  set b : ℕ → ℂ := fun n => (((thetaS W n : ℝ)) : ℂ) ^ 2 with hbdef
  have hb0 : b 0 = 0 := by rw [hbdef]; simp [thetaS, Nat.divisors_zero]
  have hs₀' : s₀.re ≤ 0 := le_of_lt hs₀
  have hsumm : Summable (fun n : ℕ => ‖b n‖ * (n : ℝ) ^ (-(((-s₀ : ℂ)).re + 2))) := by
    have h := summable_thetaS_sq_majorant W hs₀
    convert h using 2 with n
    rw [hbdef, Complex.neg_re]
    ring_nf
  have hXeq := Work.ZeroDensity.Jutila.mellinSmoothedDirichlet (b := b) hX (s := -s₀) (c := 2)
    (by norm_num) hb0 hsumm
  have hU'eq := Work.ZeroDensity.Jutila.mellinSmoothedDirichlet (b := b) hU' (s := -s₀) (c := 2)
    (by norm_num) hb0 hsumm
  have hXeq' : (∑' n, b n * (n : ℂ) ^ (-(-s₀)) * ((Real.exp (-((n : ℝ) / X)) : ℝ) : ℂ))
      = (1 / (2 * Real.pi)) * ∫ t : ℝ, Complex.Gamma (((2 : ℝ) : ℂ) + (t : ℂ) * Complex.I)
          * (X : ℂ) ^ (((2 : ℝ) : ℂ) + (t : ℂ) * Complex.I)
          * (∑' n : ℕ, b n * (n : ℂ) ^ (-(-s₀ + (((2 : ℝ) : ℂ) + (t : ℂ) * Complex.I)))) := by
    have h1 : (∑' n, b n * (n : ℂ) ^ (-(-s₀)) * ((Real.exp (-((n : ℝ) / X)) : ℝ) : ℂ))
        = (∑' n, b n * (n : ℂ) ^ (-(-s₀)) * ((Real.exp (-(n : ℝ) / X) : ℝ) : ℂ)) :=
      tsum_congr fun n => by rw [← exp_div_form X n]
    rw [h1]
    exact hXeq
  have hU'eq' : (∑' n, b n * (n : ℂ) ^ (-(-s₀)) * ((Real.exp (-((n : ℝ) / U')) : ℝ) : ℂ))
      = (1 / (2 * Real.pi)) * ∫ t : ℝ, Complex.Gamma (((2 : ℝ) : ℂ) + (t : ℂ) * Complex.I)
          * (U' : ℂ) ^ (((2 : ℝ) : ℂ) + (t : ℂ) * Complex.I)
          * (∑' n : ℕ, b n * (n : ℂ) ^ (-(-s₀ + (((2 : ℝ) : ℂ) + (t : ℂ) * Complex.I)))) := by
    have h1 : (∑' n, b n * (n : ℂ) ^ (-(-s₀)) * ((Real.exp (-((n : ℝ) / U')) : ℝ) : ℂ))
        = (∑' n, b n * (n : ℂ) ^ (-(-s₀)) * ((Real.exp (-(n : ℝ) / U') : ℝ) : ℂ)) :=
      tsum_congr fun n => by rw [← exp_div_form U' n]
    rw [h1]
    exact hU'eq
  have hsumX : Summable (fun n : ℕ => b n * (n : ℂ) ^ (-(-s₀))
      * ((Real.exp (-((n : ℝ) / X)) : ℝ) : ℂ)) := by
    have h := summable_thetaS_sq_mul_exp W X hX (s₀ := s₀) hs₀'
    simpa only [hbdef, neg_neg] using h
  have hsumU : Summable (fun n : ℕ => b n * (n : ℂ) ^ (-(-s₀))
      * ((Real.exp (-((n : ℝ) / U')) : ℝ) : ℂ)) := by
    have h := summable_thetaS_sq_mul_exp W U' hU' (s₀ := s₀) hs₀'
    simpa only [hbdef, neg_neg] using h
  have hsplit : gramEntryFree W X U' ρ ρ'
      = (∑' n, b n * (n : ℂ) ^ (-(-s₀)) * ((Real.exp (-((n : ℝ) / X)) : ℝ) : ℂ))
        - (∑' n, b n * (n : ℂ) ^ (-(-s₀)) * ((Real.exp (-((n : ℝ) / U')) : ℝ) : ℂ)) := by
    rw [gramEntryFree, ← hsumX.tsum_sub hsumU]
    refine tsum_congr fun n => ?_
    rw [hbdef, hs₀def, gfun, Complex.ofReal_sub, neg_neg]
    ring
  rw [hsplit, hXeq', hU'eq']
  simp only [Complex.ofReal_ofNat]
  rw [← mul_sub, ← MeasureTheory.integral_sub
    (integrable_mellinGram W X hX hs₀) (integrable_mellinGram W U' hU' hs₀)]
  congr 1
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
  dsimp only
  have hw : 1 < ((((2 : ℂ) + (t : ℂ) * Complex.I) - s₀)).re := by
    have h1 : (((2 : ℂ) + (t : ℂ) * Complex.I) - s₀).re = 2 - s₀.re := by simp
    rw [h1]; linarith [hs₀]
  have hS : (∑' n : ℕ, ((thetaS W n : ℝ) : ℂ) ^ 2
      * (n : ℂ) ^ (-(-s₀ + ((2 : ℂ) + (t : ℂ) * Complex.I))))
      = riemannZeta (((2 : ℂ) + (t : ℂ) * Complex.I) - s₀)
        * gramA W s₀ ((2 : ℂ) + (t : ℂ) * Complex.I) := by
    rw [show (∑' n : ℕ, ((thetaS W n : ℝ) : ℂ) ^ 2
        * (n : ℂ) ^ (-(-s₀ + ((2 : ℂ) + (t : ℂ) * Complex.I))))
        = ∑' n : ℕ, ((thetaS W n : ℝ) : ℂ) ^ 2
          * (n : ℂ) ^ (-(((2 : ℂ) + (t : ℂ) * Complex.I) - s₀)) from
      tsum_congr fun n => by
        rw [show -(-s₀ + ((2 : ℂ) + (t : ℂ) * Complex.I))
          = -(((2 : ℂ) + (t : ℂ) * Complex.I) - s₀) by ring]]
    rw [gramDS_eq W (((2 : ℂ) + (t : ℂ) * Complex.I) - s₀) hw]
    congr 1
    rw [← gramA_shift W s₀ (((2 : ℂ) + (t : ℂ) * Complex.I) - s₀)]
    congr 1
    ring
  rw [hS]
  have hz : ((2 : ℂ) + (t : ℂ) * Complex.I) ≠ 0 := by
    intro h
    have h2 := congrArg Complex.re h
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im,
      mul_zero, mul_one, sub_zero, add_zero, Complex.zero_re] at h2
    norm_num at h2
  rw [gramPhi, gammaPow_of_ne X U' hz]
  ring


end Work.ZeroDensity.LogFree
