import Mathlib
import Submission.Work.ZeroDensity.Jutila.BzCross.czReindexDefs
import Submission.Work.ZeroDensity.Jutila.Bz3ModelAux.DecaySum
import Submission.Work.ZeroDensity.Jutila.LzDiffAux.ExpSumNegSqrtSqBoundHere

namespace Work.ZeroDensity.Jutila.LzDiffAux

open Finset
open Work.ZeroDensity.Jutila

noncomputable section

/-- `t/2 ≤ ⌊t⌋₊` for `t ≥ 1`. -/
lemma half_le_floor {t : ℝ} (ht : 1 ≤ t) : t / 2 ≤ ((⌊t⌋₊ : ℕ) : ℝ) := by
  rcases le_or_gt t 2 with h | h
  · have h1 : (1 : ℝ) ≤ ((⌊t⌋₊ : ℕ) : ℝ) := by
      exact_mod_cast (Nat.one_le_floor_iff t).mpr ht
    linarith
  · have h1 : t - 1 < ((⌊t⌋₊ : ℕ) : ℝ) := Nat.sub_one_lt_floor t
    linarith

/-- Pointwise comparison of the envelope `Dc c x = exp(-(c√(log x)))` with the continuous
envelope `exp(-(c√(log(A/q))))`. -/
lemma Dc_le_exp_log_div (c : ℝ) (hc : 0 < c) {A : ℝ} (hA : 0 < A) {q : ℕ} (hq : 1 ≤ q)
    {x : ℕ} (hx : A / (q : ℝ) ≤ (x : ℝ)) :
    Dc c x ≤ Real.exp (-(c * Real.sqrt (Real.log (A / (q : ℝ))))) := by
  have hqpos : (0 : ℝ) < (q : ℝ) := by exact_mod_cast (by omega : 0 < q)
  have hAr : (0 : ℝ) < A / (q : ℝ) := div_pos hA hqpos
  rw [Dc]
  apply Real.exp_le_exp.mpr
  rcases le_or_gt (A / (q : ℝ)) 1 with h | h
  · rw [Real.sqrt_eq_zero_of_nonpos (Real.log_nonpos hAr.le h)]
    have hs := Real.sqrt_nonneg (Real.log (x : ℝ))
    nlinarith [hc]
  · have hlog : Real.log (A / (q : ℝ)) ≤ Real.log (x : ℝ) := Real.log_le_log hAr hx
    have hs : Real.sqrt (Real.log (A / (q : ℝ))) ≤ Real.sqrt (Real.log (x : ℝ)) :=
      Real.sqrt_le_sqrt hlog
    nlinarith [hs, hc]

/-- **Harmonic sums against the decaying envelope.**  For `c > 0` there is `C > 0` such that for
all `A > 0` and all `Q : ℕ` with `Q ≤ 2A`,
`Σ_{q ≤ Q} (1/q)·exp(−c√(log(A/q))) ≤ C`. -/
theorem CzHarmDecayAux (c : ℝ) (hc : 0 < c) :
    ∃ C : ℝ, 0 < C ∧ ∀ (A : ℝ) (Q : ℕ), 0 < A → (Q : ℝ) ≤ 2 * A →
      (∑ q ∈ Finset.Icc 1 Q,
        (1 / (q : ℝ)) * Real.exp (-(c * Real.sqrt (Real.log (A / (q : ℝ)))))) ≤ C := by
  have hlog2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hK2 : 0 < c ^ 2 * Real.log 2 := mul_pos (pow_pos hc 2) hlog2pos
  set α : ℝ := c * Real.sqrt (Real.log 2) with hαdef
  have hαpos : 0 < α := mul_pos hc (Real.sqrt_pos.mpr hlog2pos)
  have hαsq : α ^ 2 = c ^ 2 * Real.log 2 := by
    rw [hαdef, mul_pow, Real.sq_sqrt hlog2pos.le]
  refine ⟨31 + 30 / (c ^ 2 * Real.log 2), ?_, ?_⟩
  · have h : 0 < 30 / (c ^ 2 * Real.log 2) := div_pos (by norm_num) hK2
    linarith
  intro A Q hA hQ
  set A₀ : ℕ := ⌊A⌋₊ with hA₀def
  by_cases hA1 : A < 1
  · have hQ1 : Q ≤ 1 := by
      have h2 : (Q : ℝ) < 2 := lt_of_le_of_lt hQ (by linarith)
      have h3 : Q < 2 := by exact_mod_cast h2
      omega
    calc (∑ q ∈ Finset.Icc 1 Q,
            (1 / (q : ℝ)) * Real.exp (-(c * Real.sqrt (Real.log (A / (q : ℝ))))))
        ≤ ∑ q ∈ Finset.Icc 1 Q, (1 : ℝ) := by
          apply Finset.sum_le_sum
          intro q hq
          rw [Finset.mem_Icc] at hq
          have hq1 : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq.1
          have hexp : Real.exp (-(c * Real.sqrt (Real.log (A / (q : ℝ))))) ≤ 1 := by
            rw [Real.exp_le_one_iff]
            have hs := Real.sqrt_nonneg (Real.log (A / (q : ℝ)))
            nlinarith [hc]
          have h1q : (1 : ℝ) / (q : ℝ) ≤ 1 :=
            (div_le_one (by linarith : (0 : ℝ) < (q : ℝ))).mpr hq1
          calc (1 / (q : ℝ)) * Real.exp (-(c * Real.sqrt (Real.log (A / (q : ℝ)))))
              ≤ 1 * 1 := mul_le_mul h1q hexp (Real.exp_pos _).le (by norm_num)
            _ = 1 := by ring
      _ = (Q : ℝ) := by
          rw [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul]
          simp
      _ ≤ 1 := by exact_mod_cast hQ1
      _ ≤ 31 + 30 / (c ^ 2 * Real.log 2) := by
          have h : 0 < 30 / (c ^ 2 * Real.log 2) := div_pos (by norm_num) hK2
          linarith
  · push_neg at hA1
    have hA₀ge : 1 ≤ A₀ := by rw [hA₀def]; exact (Nat.one_le_floor_iff A).mpr hA1
    have hA₀le : ((A₀ : ℕ) : ℝ) ≤ A := by rw [hA₀def]; exact Nat.floor_le hA.le
    have hA₀lt : A < ((A₀ : ℕ) : ℝ) + 1 := by rw [hA₀def]; exact Nat.lt_floor_add_one A
    have hsplit : Finset.Icc 1 Q = Finset.Icc 1 (min Q A₀) ∪ Finset.Icc (A₀ + 1) Q := by
      rcases le_or_gt Q A₀ with hQA | hQA
      · rw [min_eq_left hQA]
        ext q; simp only [Finset.mem_Icc, Finset.mem_union]; omega
      · rw [min_eq_right hQA.le]
        ext q; simp only [Finset.mem_Icc, Finset.mem_union]; omega
    have hdisj : Disjoint (Finset.Icc 1 (min Q A₀)) (Finset.Icc (A₀ + 1) Q) := by
      rw [Finset.disjoint_left]
      intro q hq hq2
      simp only [Finset.mem_Icc] at hq hq2
      have hqA : q ≤ A₀ := le_trans hq.2 (min_le_right Q A₀)
      omega
    rw [hsplit, Finset.sum_union hdisj]
    have htail : (∑ q ∈ Finset.Icc (A₀ + 1) Q,
          (1 / (q : ℝ)) * Real.exp (-(c * Real.sqrt (Real.log (A / (q : ℝ)))))) ≤ 1 := by
      have hcard : (Finset.Icc (A₀ + 1) Q).card ≤ A₀ + 1 := by
        rw [Nat.card_Icc]
        have hQle : Q ≤ 2 * A₀ + 1 := by
          have h2 : (Q : ℝ) < 2 * (A₀ : ℝ) + 2 := by
            have h := hQ
            have h3 := hA₀lt
            linarith
          have h4 : Q < 2 * A₀ + 2 := by exact_mod_cast h2
          omega
        omega
      calc (∑ q ∈ Finset.Icc (A₀ + 1) Q,
              (1 / (q : ℝ)) * Real.exp (-(c * Real.sqrt (Real.log (A / (q : ℝ))))))
          ≤ ∑ q ∈ Finset.Icc (A₀ + 1) Q, (1 / ((A₀ : ℝ) + 1)) := by
            apply Finset.sum_le_sum
            intro q hq
            rw [Finset.mem_Icc] at hq
            have hq1 : ((A₀ : ℝ) + 1) ≤ (q : ℝ) := by
              have h : A₀ + 1 ≤ q := hq.1
              exact_mod_cast h
            have hexp : Real.exp (-(c * Real.sqrt (Real.log (A / (q : ℝ))))) ≤ 1 := by
              rw [Real.exp_le_one_iff]
              have hs := Real.sqrt_nonneg (Real.log (A / (q : ℝ)))
              nlinarith [hc]
            have h1q : (1 : ℝ) / (q : ℝ) ≤ 1 / ((A₀ : ℝ) + 1) :=
              one_div_le_one_div_of_le (by positivity) hq1
            calc (1 / (q : ℝ)) * Real.exp (-(c * Real.sqrt (Real.log (A / (q : ℝ)))))
                ≤ (1 / ((A₀ : ℝ) + 1)) * 1 :=
                  mul_le_mul h1q hexp (Real.exp_pos _).le (by positivity)
              _ = 1 / ((A₀ : ℝ) + 1) := by ring
        _ = ((Finset.Icc (A₀ + 1) Q).card : ℝ) * (1 / ((A₀ : ℝ) + 1)) := by
            rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ ((A₀ : ℝ) + 1) * (1 / ((A₀ : ℝ) + 1)) := by
            apply mul_le_mul_of_nonneg_right _ (by positivity)
            exact_mod_cast hcard
        _ = 1 := by
            have hne : ((A₀ : ℝ) + 1) ≠ 0 := by positivity
            rw [mul_one_div, div_self hne]

    have hhead : (∑ q ∈ Finset.Icc 1 (min Q A₀),
          (1 / (q : ℝ)) * Real.exp (-(c * Real.sqrt (Real.log (A / (q : ℝ))))))
        ≤ 30 + 30 / (c ^ 2 * Real.log 2) := by
      have hsub : Finset.Icc 1 (min Q A₀) ⊆ Finset.Icc 1 A₀ := by
        intro q hq
        simp only [Finset.mem_Icc] at hq ⊢
        exact ⟨hq.1, le_trans hq.2 (min_le_right Q A₀)⟩
      have hstep : (∑ q ∈ Finset.Icc 1 (min Q A₀),
            (1 / (q : ℝ)) * Real.exp (-(c * Real.sqrt (Real.log (A / (q : ℝ))))))
          ≤ ∑ q ∈ Finset.Icc 1 A₀,
            (1 / (q : ℝ)) * Real.exp (-(c * Real.sqrt (Real.log (A / (q : ℝ))))) :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub
          (fun q _ _ => mul_nonneg (by positivity) (Real.exp_pos _).le)
      have hmap : ∀ q ∈ Finset.Icc 1 A₀, Nat.log 2 (A₀ / q) ∈ Finset.range (Nat.log 2 A₀ + 1) := by
        intro q hq
        rw [Finset.mem_Icc] at hq
        rw [Finset.mem_range]
        have h1 : Nat.log 2 (A₀ / q) ≤ Nat.log 2 A₀ := Nat.log_mono_right (Nat.div_le_self A₀ q)
        omega
      have hfiber := Finset.sum_fiberwise_of_maps_to (s := Finset.Icc 1 A₀)
        (t := Finset.range (Nat.log 2 A₀ + 1)) (g := fun q => Nat.log 2 (A₀ / q)) hmap
        (fun q => (1 / (q : ℝ)) * Real.exp (-(c * Real.sqrt (Real.log (A / (q : ℝ))))))
      have hblock : ∀ k ∈ Finset.range (Nat.log 2 A₀ + 1),
          (∑ q ∈ (Finset.Icc 1 A₀).filter (fun q => Nat.log 2 (A₀ / q) = k),
            (1 / (q : ℝ)) * Real.exp (-(c * Real.sqrt (Real.log (A / (q : ℝ))))))
          ≤ 3 * Real.exp (-(α * Real.sqrt (k : ℝ))) := by
        intro k hk
        have hpow : Real.log ((2 : ℝ) ^ k) = (k : ℝ) * Real.log 2 := Real.log_pow 2 k
        have hs : Real.sqrt (Real.log ((2 : ℝ) ^ k))
            = Real.sqrt (k : ℝ) * Real.sqrt (Real.log 2) := by
          rw [hpow, Real.sqrt_mul (Nat.cast_nonneg k)]
        have hαk : α * Real.sqrt (k : ℝ) = c * Real.sqrt (Real.log ((2 : ℝ) ^ k)) := by
          rw [hαdef, hs]; ring
        have hterm : ∀ q ∈ (Finset.Icc 1 A₀).filter (fun q => Nat.log 2 (A₀ / q) = k),
            (1 / (q : ℝ)) * Real.exp (-(c * Real.sqrt (Real.log (A / (q : ℝ)))))
              ≤ Real.exp (-(α * Real.sqrt (k : ℝ))) * (1 / (q : ℝ)) := by
          intro q hq
          rw [Finset.mem_filter, Finset.mem_Icc] at hq
          obtain ⟨⟨hq1, hqA⟩, hlogq⟩ := hq
          have hqpos : 0 < q := hq1
          have hAqne : A₀ / q ≠ 0 := by
            have h : 1 ≤ A₀ / q := by rw [Nat.one_le_div_iff hqpos]; exact hqA
            omega
          have h2k : 2 ^ k ≤ A₀ / q := by
            have h := Nat.pow_log_le_self 2 hAqne
            rwa [hlogq] at h
          have h2kR : ((2 : ℝ) ^ k) ≤ ((A₀ / q : ℕ) : ℝ) := by
            have hk' : (((2 : ℕ) ^ k : ℕ) : ℝ) ≤ ((A₀ / q : ℕ) : ℝ) := by exact_mod_cast h2k
            simpa using hk'
          have hdivR : ((A₀ / q : ℕ) : ℝ) ≤ (A₀ : ℝ) / (q : ℝ) := Nat.cast_div_le
          have hAle : (A₀ : ℝ) / (q : ℝ) ≤ A / (q : ℝ) :=
            div_le_div_of_nonneg_right hA₀le (Nat.cast_nonneg q)
          have hlogge : Real.log ((2 : ℝ) ^ k) ≤ Real.log (A / (q : ℝ)) :=
            Real.log_le_log (by positivity) (h2kR.trans (hdivR.trans hAle))
          have hsq : Real.sqrt (Real.log ((2 : ℝ) ^ k)) ≤ Real.sqrt (Real.log (A / (q : ℝ))) :=
            Real.sqrt_le_sqrt hlogge
          have hexp : Real.exp (-(c * Real.sqrt (Real.log (A / (q : ℝ)))))
              ≤ Real.exp (-(α * Real.sqrt (k : ℝ))) := by
            rw [hαk]
            apply Real.exp_le_exp.mpr
            nlinarith [hsq, hc]
          calc (1 / (q : ℝ)) * Real.exp (-(c * Real.sqrt (Real.log (A / (q : ℝ)))))
              = Real.exp (-(c * Real.sqrt (Real.log (A / (q : ℝ))))) * (1 / (q : ℝ)) := by ring
            _ ≤ Real.exp (-(α * Real.sqrt (k : ℝ))) * (1 / (q : ℝ)) :=
                mul_le_mul_of_nonneg_right hexp (by positivity)
        calc (∑ q ∈ (Finset.Icc 1 A₀).filter (fun q => Nat.log 2 (A₀ / q) = k),
              (1 / (q : ℝ)) * Real.exp (-(c * Real.sqrt (Real.log (A / (q : ℝ))))))
            ≤ ∑ q ∈ (Finset.Icc 1 A₀).filter (fun q => Nat.log 2 (A₀ / q) = k),
                Real.exp (-(α * Real.sqrt (k : ℝ))) * (1 / (q : ℝ)) := Finset.sum_le_sum hterm
          _ = Real.exp (-(α * Real.sqrt (k : ℝ)))
                * ∑ q ∈ (Finset.Icc 1 A₀).filter (fun q => Nat.log 2 (A₀ / q) = k),
                    (1 / (q : ℝ)) := by rw [Finset.mul_sum]
          _ ≤ Real.exp (-(α * Real.sqrt (k : ℝ))) * 3 :=
              mul_le_mul_of_nonneg_left
                (Work.ZeroDensity.Jutila.Bz3ModelAux.fiber_sum_le A₀ k) (Real.exp_pos _).le
          _ = 3 * Real.exp (-(α * Real.sqrt (k : ℝ))) := by ring
      calc (∑ q ∈ Finset.Icc 1 (min Q A₀),
            (1 / (q : ℝ)) * Real.exp (-(c * Real.sqrt (Real.log (A / (q : ℝ))))))
          ≤ ∑ q ∈ Finset.Icc 1 A₀,
              (1 / (q : ℝ)) * Real.exp (-(c * Real.sqrt (Real.log (A / (q : ℝ))))) := hstep
        _ = ∑ k ∈ Finset.range (Nat.log 2 A₀ + 1),
              ∑ q ∈ (Finset.Icc 1 A₀).filter (fun q => Nat.log 2 (A₀ / q) = k),
                (1 / (q : ℝ)) * Real.exp (-(c * Real.sqrt (Real.log (A / (q : ℝ))))) :=
            hfiber.symm
        _ ≤ ∑ k ∈ Finset.range (Nat.log 2 A₀ + 1), 3 * Real.exp (-(α * Real.sqrt (k : ℝ))) :=
            Finset.sum_le_sum hblock
        _ = 3 * ∑ k ∈ Finset.range (Nat.log 2 A₀ + 1), Real.exp (-(α * Real.sqrt (k : ℝ))) := by
            rw [Finset.mul_sum]
        _ ≤ 3 * (10 + 10 / α ^ 2) := by
            apply mul_le_mul_of_nonneg_left _ (by norm_num)
            exact ExpSumNegSqrtSqBound hαpos (Nat.log 2 A₀)
        _ = 30 + 30 / (c ^ 2 * Real.log 2) := by rw [hαsq]; ring
    linarith [htail, hhead]

theorem CzRIIQSumBoundFinal (c : ℝ) (hc : 0 < c) :
  ∃ C : ℝ, 0 < C ∧
  (∀ (w y : ℝ) (N : ℕ), 1 ≤ w → w ≤ y → y ≤ (N:ℝ) → (N:ℝ) < w*y →
      (∑ q ∈ Finset.Icc 1 (Work.ZeroDensity.Jutila.czQ y N), (1:ℝ)/q
        * Work.ZeroDensity.Jutila.Dc c (Work.ZeroDensity.Jutila.czR w N q)) ≤ C)
  ∧ (∀ (w y : ℝ) (N : ℕ), 1 ≤ w → w ≤ y → y ≤ (N:ℝ) → (N:ℝ) < w*y →
      (∑ q ∈ Finset.Icc 1 (Work.ZeroDensity.Jutila.czQ y N), (1:ℝ)/q
        * Work.ZeroDensity.Jutila.Dc c (Work.ZeroDensity.Jutila.czT y N q)) ≤ C) := by
  obtain ⟨C, hCpos, hC⟩ := CzHarmDecayAux c hc
  refine ⟨C, hCpos, ?_, ?_⟩
  · intro w y N hw hwy hyN hNwy
    have hwpos : (0 : ℝ) < w := by linarith
    have hypos : (0 : ℝ) < y := by linarith
    have hNpos : (0 : ℝ) < (N : ℝ) := by linarith
    set A : ℝ := (N : ℝ) / (2 * w) with hAdef
    have hApos : 0 < A := by rw [hAdef]; exact div_pos hNpos (by linarith)
    have hczQle : ((czQ y N : ℕ) : ℝ) ≤ (N : ℝ) / y := by
      rw [czQ]; exact Nat.floor_le (div_nonneg (Nat.cast_nonneg N) hypos.le)
    have hQle : ((czQ y N : ℕ) : ℝ) ≤ 2 * A := by
      have h2 : (N : ℝ) / y ≤ (N : ℝ) / w := div_le_div_of_nonneg_left hNpos.le hwpos hwy
      have h3 : (N : ℝ) / w = 2 * A := by
        have hwne : w ≠ 0 := ne_of_gt hwpos
        rw [hAdef]
        field_simp
        try ring
      linarith [hczQle, h2, h3]
    refine le_trans ?_ (hC A (czQ y N) hApos hQle)
    apply Finset.sum_le_sum
    intro q hq
    rw [Finset.mem_Icc] at hq
    obtain ⟨hq1, hqQ⟩ := hq
    have hqposR : (0 : ℝ) < (q : ℝ) := by exact_mod_cast (by omega : 0 < q)
    have hqNy : (q : ℝ) * y ≤ (N : ℝ) := by
      have h1 : (q : ℝ) ≤ (N : ℝ) / y := le_trans (by exact_mod_cast hqQ) hczQle
      rw [le_div_iff₀ hypos] at h1
      linarith
    have hqw : (q : ℝ) * w ≤ (N : ℝ) := by nlinarith [hqNy, hwy, hqposR]
    have ht1 : 1 ≤ (N : ℝ) / ((q : ℝ) * w) := by
      rw [le_div_iff₀ (mul_pos hqposR hwpos)]
      linarith
    have hx : A / (q : ℝ) ≤ ((czR w N q : ℕ) : ℝ) := by
      have hte : A / (q : ℝ) = (N : ℝ) / ((q : ℝ) * w) / 2 := by
        rw [hAdef]
        field_simp
        try ring
      rw [hte]
      have hfl : (N : ℝ) / ((q : ℝ) * w) / 2 ≤ ((⌊(N : ℝ) / ((q : ℝ) * w)⌋₊ : ℕ) : ℝ) :=
        half_le_floor ht1
      have hczR : ((czR w N q : ℕ) : ℝ) = ((⌊(N : ℝ) / ((q : ℝ) * w)⌋₊ : ℕ) : ℝ) := by rw [czR]
      rw [hczR]; exact hfl
    calc (1 : ℝ) / q * Dc c (czR w N q)
        = (1 : ℝ) / (q : ℝ) * Dc c (czR w N q) := rfl
      _ ≤ (1 : ℝ) / (q : ℝ) * Real.exp (-(c * Real.sqrt (Real.log (A / (q : ℝ))))) :=
          mul_le_mul_of_nonneg_left
            (Dc_le_exp_log_div c hc hApos hq1 hx) (by positivity)
  · intro w y N hw hwy hyN hNwy
    have hwpos : (0 : ℝ) < w := by linarith
    have hypos : (0 : ℝ) < y := by linarith
    have hNpos : (0 : ℝ) < (N : ℝ) := by linarith
    set A : ℝ := (N : ℝ) / (2 * y) with hAdef
    have hApos : 0 < A := by rw [hAdef]; exact div_pos hNpos (by linarith)
    have hczQle : ((czQ y N : ℕ) : ℝ) ≤ (N : ℝ) / y := by
      rw [czQ]; exact Nat.floor_le (div_nonneg (Nat.cast_nonneg N) hypos.le)
    have hQle : ((czQ y N : ℕ) : ℝ) ≤ 2 * A := by
      have h3 : (N : ℝ) / y = 2 * A := by
        have hyne : y ≠ 0 := ne_of_gt hypos
        rw [hAdef]
        field_simp
        try ring
      linarith [hczQle, h3]
    refine le_trans ?_ (hC A (czQ y N) hApos hQle)
    apply Finset.sum_le_sum
    intro q hq
    rw [Finset.mem_Icc] at hq
    obtain ⟨hq1, hqQ⟩ := hq
    have hqposR : (0 : ℝ) < (q : ℝ) := by exact_mod_cast (by omega : 0 < q)
    have hqNy : (q : ℝ) * y ≤ (N : ℝ) := by
      have h1 : (q : ℝ) ≤ (N : ℝ) / y := le_trans (by exact_mod_cast hqQ) hczQle
      rw [le_div_iff₀ hypos] at h1
      linarith
    have ht1 : 1 ≤ (N : ℝ) / ((q : ℝ) * y) := by
      rw [le_div_iff₀ (mul_pos hqposR hypos)]
      linarith
    have hx : A / (q : ℝ) ≤ ((czT y N q : ℕ) : ℝ) := by
      have hte : A / (q : ℝ) = (N : ℝ) / ((q : ℝ) * y) / 2 := by
        rw [hAdef]
        field_simp
        try ring
      rw [hte]
      have hfl : (N : ℝ) / ((q : ℝ) * y) / 2 ≤ ((⌊(N : ℝ) / ((q : ℝ) * y)⌋₊ : ℕ) : ℝ) :=
        half_le_floor ht1
      have hczT : ((czT y N q : ℕ) : ℝ) = ((⌊(N : ℝ) / ((q : ℝ) * y)⌋₊ : ℕ) : ℝ) := by rw [czT]
      rw [hczT]; exact hfl
    calc (1 : ℝ) / q * Dc c (czT y N q)
        = (1 : ℝ) / (q : ℝ) * Dc c (czT y N q) := rfl
      _ ≤ (1 : ℝ) / (q : ℝ) * Real.exp (-(c * Real.sqrt (Real.log (A / (q : ℝ))))) :=
          mul_le_mul_of_nonneg_left
            (Dc_le_exp_log_div c hc hApos hq1 hx) (by positivity)

end

end Work.ZeroDensity.Jutila.LzDiffAux
