import Mathlib
import Submission.Work.KMTAreas.A7.M0Aux
import Submission.Work.KMTAreas.A7.M0WDerivBound
import Submission.Work.KMTAreas.A7.FiberFirstOrder

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Work.KMTAreas.A7

open MeasureTheory Polynomial Finset Filter Topology
open scoped ENNReal NNReal BigOperators
open PointwiseErgodicTheorems Submission.PointwiseErgodicTheorems
open Work.Analysis.IonescuWainger
open M0Aux

/-- The symbol-difference estimate at the heart of the §6 model approximation: the
`(ξ₁,ξ₂)`-derivative `M0deriv` of `M₀ = weylAvg − mZ·mTilde` is bounded by
`C·(X₁+X₂+1)^A·q·N^{j₁+dj₂}/N` when `q` is a period of `n ↦ e(α₁n+α₂P(n))` and the frequencies
obey `|ξ₁| ≤ X₁/N`, `|ξ₂| ≤ X₂/N^d`.  A complete proof (periodicity, residue splitting, the
FTC/mean-value argument, and the constants) is in `NOTES_A7_M0DerivBound.md` at the workspace root. -/
theorem M0DerivBound (P : ℤ[X]) (hdeg : 2 ≤ P.natDegree) :
    ∃ C A : ℝ, 0 < C ∧ 0 ≤ A ∧
      ∀ (N q : ℕ) (α₁ α₂ : Work.Analysis.IonescuWainger.Circle) (ξ₁ ξ₂ X₁ X₂ : ℝ)
        (j₁ j₂ : ℕ),
        1 ≤ N → 1 ≤ q → j₁ ≤ 2 → j₂ ≤ 2 → 1 ≤ X₁ → 1 ≤ X₂ →
        q • α₁ = 0 → q • α₂ = 0 →
        |ξ₁| ≤ X₁ / (N : ℝ) → |ξ₂| ≤ X₂ / ((N : ℝ) ^ P.natDegree) →
        ‖M0deriv P N q α₁ α₂ ξ₁ ξ₂ j₁ j₂‖
          ≤ C * (X₁ + X₂ + 1) ^ A * (q : ℝ) *
              ((N : ℝ) ^ j₁ * (N : ℝ) ^ (P.natDegree * j₂)) / (N : ℝ) := by
  obtain ⟨C₁, hC₁pos, hC₁⟩ := M0WDerivBound P
  refine ⟨5 * C₁, 1, by positivity, by norm_num, ?_⟩
  intro N q α₁ α₂ ξ₁ ξ₂ X₁ X₂ j₁ j₂ hN hq hj₁ hj₂ hX₁ hX₂ hα₁ hα₂ hξ₁ hξ₂
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hNne : (N : ℝ) ≠ 0 := ne_of_gt hNpos
  have hqpos : 0 < q := by omega
  have hqnn : (0 : ℝ) ≤ (q : ℝ) := Nat.cast_nonneg q
  have hXsum : (0 : ℝ) ≤ X₁ + X₂ := by linarith
  set M : ℝ := (N : ℝ) ^ (j₁ + P.natDegree * j₂) with hMdef
  have hMpos : 0 < M := by rw [hMdef]; positivity
  have hMnn : 0 ≤ M := le_of_lt hMpos
  have hVb : ∀ u ∈ Set.Icc (0 : ℝ) (N : ℝ), ‖Work.A7.m0w P ξ₁ ξ₂ j₁ j₂ u‖ ≤ C₁ * M := by
    intro u hu
    have h := (hC₁ N ξ₁ ξ₂ X₁ X₂ j₁ j₂ hN hj₁ hj₂ hX₁ hX₂ hξ₁ hξ₂ u hu).1
    rw [Real.rpow_natCast] at h
    rw [hMdef]
    exact h
  have hV'b : ∀ u ∈ Set.Icc (0 : ℝ) (N : ℝ),
      ‖deriv (Work.A7.m0w P ξ₁ ξ₂ j₁ j₂) u‖ ≤ C₁ * (X₁ + X₂ + 1) * (M / (N : ℝ)) := by
    intro u hu
    have h := (hC₁ N ξ₁ ξ₂ X₁ X₂ j₁ j₂ hN hj₁ hj₂ hX₁ hX₂ hξ₁ hξ₂ u hu).2
    rw [Real.rpow_sub hNpos, Real.rpow_one, Real.rpow_natCast] at h
    rw [hMdef]
    exact h
  have hmulB : (N : ℝ) * (C₁ * (X₁ + X₂ + 1) * (M / (N : ℝ))) = C₁ * (X₁ + X₂ + 1) * M := by
    field_simp
  have hfib_bound : ∀ a ∈ Finset.range q,
      ‖(∑ n ∈ (Finset.Ioc (N / 2) N).filter (fun n => n % q = a),
            Work.A7.m0w P ξ₁ ξ₂ j₁ j₂ (n : ℝ))
          - (q : ℝ)⁻¹ * ∫ u in ((N / 2 : ℕ) : ℝ)..(N : ℝ), Work.A7.m0w P ξ₁ ξ₂ j₁ j₂ u‖
        ≤ 3 * (C₁ * M) + C₁ * (X₁ + X₂ + 1) * M := by
    intro a ha
    have h := FiberFirstOrder (fun u : ℝ => Work.A7.m0w P ξ₁ ξ₂ j₁ j₂ u) (Nat.div_le_self N 2) hqpos
      (Finset.mem_range.mp ha) (by positivity) (by positivity)
      (fun u hu => hVb u ⟨le_trans (Nat.cast_nonneg _) hu.1, hu.2⟩)
      ((Work.A7.contDiff_two_m0w P ξ₁ ξ₂ j₁ j₂).of_le (by norm_num))
      (fun u hu => hV'b u ⟨le_trans (Nat.cast_nonneg _) hu.1, hu.2⟩)
    rw [hmulB] at h
    exact h
  have hqcast : (q : ℂ)⁻¹ = (((q : ℝ)⁻¹ : ℝ) : ℂ) := by
    rw [Complex.ofReal_inv, Complex.ofReal_natCast]
  have hsum_bound : ‖∑ a ∈ Finset.range q, Work.A7.arithW P α₁ α₂ (a : ℤ) *
        ((∑ n ∈ (Finset.Ioc (N / 2) N).filter (fun n => n % q = a),
            Work.A7.m0w P ξ₁ ξ₂ j₁ j₂ (n : ℝ))
          - (q : ℂ)⁻¹ * ∫ u in ((N / 2 : ℕ) : ℝ)..(N : ℝ), Work.A7.m0w P ξ₁ ξ₂ j₁ j₂ u)‖
      ≤ (q : ℝ) * (3 * (C₁ * M) + C₁ * (X₁ + X₂ + 1) * M) := by
    refine (norm_sum_le _ _).trans ?_
    calc ∑ a ∈ Finset.range q, ‖Work.A7.arithW P α₁ α₂ (a : ℤ) *
            ((∑ n ∈ (Finset.Ioc (N / 2) N).filter (fun n => n % q = a),
                Work.A7.m0w P ξ₁ ξ₂ j₁ j₂ (n : ℝ))
              - (q : ℂ)⁻¹ * ∫ u in ((N / 2 : ℕ) : ℝ)..(N : ℝ),
                  Work.A7.m0w P ξ₁ ξ₂ j₁ j₂ u)‖
        = ∑ a ∈ Finset.range q, ‖(∑ n ∈ (Finset.Ioc (N / 2) N).filter (fun n => n % q = a),
              Work.A7.m0w P ξ₁ ξ₂ j₁ j₂ (n : ℝ))
              - (q : ℂ)⁻¹ * ∫ u in ((N / 2 : ℕ) : ℝ)..(N : ℝ),
                  Work.A7.m0w P ξ₁ ξ₂ j₁ j₂ u‖ := by
          refine Finset.sum_congr rfl (fun a ha => ?_)
          rw [norm_mul, arithW_norm_eq_one, one_mul]
      _ ≤ ∑ a ∈ Finset.range q, (3 * (C₁ * M) + C₁ * (X₁ + X₂ + 1) * M) := by
          refine Finset.sum_le_sum (fun a ha => ?_)
          have h := hfib_bound a ha
          rw [hqcast]
          exact h
      _ = (q : ℝ) * (3 * (C₁ * M) + C₁ * (X₁ + X₂ + 1) * M) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have hZbound : ‖∫ u in ((N / 2 : ℕ) : ℝ)..((N : ℝ) / 2), Work.A7.m0w P ξ₁ ξ₂ j₁ j₂ u‖
      ≤ C₁ * M := by
    have h1 : ((N / 2 : ℕ) : ℝ) ≤ (N : ℝ) / 2 := Nat.cast_div_le
    have hlen : |(N : ℝ) / 2 - ((N / 2 : ℕ) : ℝ)| ≤ 1 := by
      have h2 : (N : ℝ) / 2 ≤ ((N / 2 : ℕ) : ℝ) + 1 := by
        have hmod : N % 2 ≤ 1 := by omega
        have hdec : N ≤ N / 2 * 2 + 1 := by omega
        have hdec' : (N : ℝ) ≤ ((N / 2 : ℕ) : ℝ) * 2 + 1 := by exact_mod_cast hdec
        linarith
      rw [abs_sub_le_iff]
      constructor <;> linarith
    have hb := intervalIntegral.norm_integral_le_of_norm_le_const
      (f := fun u : ℝ => Work.A7.m0w P ξ₁ ξ₂ j₁ j₂ u) (a := ((N / 2 : ℕ) : ℝ))
      (b := (N : ℝ) / 2) (C := C₁ * M)
      (fun x hx => by
        rw [Set.uIoc_of_le h1] at hx
        exact hVb x ⟨le_trans (Nat.cast_nonneg _) hx.1.le, le_trans hx.2 (by linarith)⟩)
    calc ‖∫ u in ((N / 2 : ℕ) : ℝ)..((N : ℝ) / 2), Work.A7.m0w P ξ₁ ξ₂ j₁ j₂ u‖
        ≤ (C₁ * M) * |(N : ℝ) / 2 - ((N / 2 : ℕ) : ℝ)| := hb
      _ ≤ (C₁ * M) * 1 :=
          mul_le_mul_of_nonneg_left hlen (mul_nonneg hC₁pos.le hMnn)
      _ = C₁ * M := by ring
  have hdecomp := m0deriv_decomp P (by omega : 0 < N) hqpos α₁ α₂ hα₁ hα₂ ξ₁ ξ₂ j₁ j₂
  have hmZ : ‖mZ P q α₁ α₂‖ ≤ 1 := mZ_norm_le_one P hq α₁ α₂
  have hmain : ‖M0deriv P N q α₁ α₂ ξ₁ ξ₂ j₁ j₂‖
      ≤ (N : ℝ)⁻¹ * ((q : ℝ) * (3 * (C₁ * M) + C₁ * (X₁ + X₂ + 1) * M))
        + (N : ℝ)⁻¹ * (C₁ * M) := by
    rw [hdecomp]
    refine (norm_add_le _ _).trans ?_
    refine add_le_add ?_ ?_
    · rw [norm_mul, norm_inv, Complex.norm_natCast]
      exact mul_le_mul_of_nonneg_left hsum_bound (inv_nonneg.mpr hNpos.le)
    · rw [norm_mul, norm_mul, norm_inv, Complex.norm_natCast]
      calc (N : ℝ)⁻¹ * ‖mZ P q α₁ α₂‖ * ‖∫ u in ((N / 2 : ℕ) : ℝ)..((N : ℝ) / 2),
              Work.A7.m0w P ξ₁ ξ₂ j₁ j₂ u‖
          ≤ (N : ℝ)⁻¹ * 1 * (C₁ * M) := by
            exact mul_le_mul (mul_le_mul_of_nonneg_left hmZ (inv_nonneg.mpr hNpos.le)) hZbound
              (norm_nonneg _) (by positivity)
        _ = (N : ℝ)⁻¹ * (C₁ * M) := by ring
  refine hmain.trans ?_
  have hpow : (N : ℝ) ^ j₁ * (N : ℝ) ^ (P.natDegree * j₂) = M := by
    rw [hMdef, ← pow_add]
  rw [hpow, Real.rpow_one]
  have hstep : (N : ℝ) * ((N : ℝ)⁻¹ * ((q : ℝ) * (3 * (C₁ * M) + C₁ * (X₁ + X₂ + 1) * M))
        + (N : ℝ)⁻¹ * (C₁ * M))
      = (q : ℝ) * M * (3 * C₁ + C₁ * (X₁ + X₂ + 1)) + C₁ * M := by
    field_simp
  have htarget : (N : ℝ) * (5 * C₁ * (X₁ + X₂ + 1) * (q : ℝ) * M / (N : ℝ))
      = 5 * C₁ * (X₁ + X₂ + 1) * (q : ℝ) * M := by
    field_simp
  have hq1 : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
  have hb1 : (q : ℝ) * M * (3 * C₁ + C₁ * (X₁ + X₂ + 1)) + C₁ * M
      ≤ (q : ℝ) * M * (3 * C₁ + C₁ * (X₁ + X₂ + 1) + C₁) := by
    have h : C₁ * M ≤ (q : ℝ) * (C₁ * M) := by nlinarith [hq1, mul_nonneg hC₁pos.le hMnn]
    nlinarith [h]
  have hb2 : (q : ℝ) * M * (3 * C₁ + C₁ * (X₁ + X₂ + 1) + C₁)
      ≤ 5 * C₁ * (X₁ + X₂ + 1) * (q : ℝ) * M := by
    have hfour : 3 * C₁ + C₁ * (X₁ + X₂ + 1) + C₁ ≤ 5 * C₁ * (X₁ + X₂ + 1) :=
      by nlinarith [hXsum, hC₁pos]
    calc (q : ℝ) * M * (3 * C₁ + C₁ * (X₁ + X₂ + 1) + C₁)
        ≤ (q : ℝ) * M * (5 * C₁ * (X₁ + X₂ + 1)) :=
          mul_le_mul_of_nonneg_left hfour (mul_nonneg hqnn hMnn)
      _ = 5 * C₁ * (X₁ + X₂ + 1) * (q : ℝ) * M := by ring
  refine le_of_mul_le_mul_left ?_ hNpos
  rw [hstep, htarget]
  nlinarith [hb1, hb2]


end Work.KMTAreas.A7
