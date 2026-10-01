import Mathlib
import Submission.Work.ZeroDensity.Jutila.harmonicFiberMass
import Submission.Work.ZeroDensity.Jutila.LzDiffAux.ExpSumNegSqrtSqBoundHere

namespace Work.ZeroDensity.Jutila.LzDiffAux

open Finset

/-- Membership in a dyadic fiber `{q ∈ [1,Q] : Nat.log 2 ⌊A/q⌋ = j}` (`j ≥ 1`) pins `q`
into the ratio-`2` interval `(A/2^{j+1}, A/2^j]`. -/
lemma fiber_mem_Ioc {A : ℝ} (hA : 0 < A) {j : ℕ} (hj : 1 ≤ j) {Q q : ℕ}
    (hq : q ∈ (Finset.Icc 1 Q).filter (fun q : ℕ => Nat.log 2 (Nat.floor (A / (q : ℝ))) = j)) :
    A / (2 : ℝ) ^ (j + 1) < (q : ℝ) ∧ (q : ℝ) ≤ A / (2 : ℝ) ^ j := by
  rw [Finset.mem_filter, Finset.mem_Icc] at hq
  obtain ⟨⟨hq1, hqQ⟩, hlog⟩ := hq
  have hqpos : (0 : ℝ) < (q : ℝ) := by exact_mod_cast (by omega : 0 < q)
  have hAqpos : 0 < A / (q : ℝ) := div_pos hA hqpos
  have hne : Nat.floor (A / (q : ℝ)) ≠ 0 := by
    intro h0
    have hn2 : Nat.floor (A / (q : ℝ)) < 2 := by omega
    have hlog0 : Nat.log 2 (Nat.floor (A / (q : ℝ))) = 0 :=
      (Nat.log_eq_zero_iff).mpr (Or.inl hn2)
    omega
  have hpow : 2 ^ j ≤ Nat.floor (A / (q : ℝ)) := by
    have := Nat.pow_log_le_self 2 hne
    rwa [hlog] at this
  have h2j : (2 : ℝ) ^ j ≤ A / (q : ℝ) := by
    have h1 : (2 : ℝ) ^ j ≤ (Nat.floor (A / (q : ℝ)) : ℝ) := by
      have hh : (2 : ℝ) ^ j = ((2 ^ j : ℕ) : ℝ) := (Nat.cast_pow 2 j).symm
      rw [hh]
      exact_mod_cast hpow
    exact le_trans h1 (Nat.floor_le hAqpos.le)
  have hupper : (q : ℝ) ≤ A / (2 : ℝ) ^ j := by
    rw [le_div_iff₀ (by positivity : (0 : ℝ) < (2 : ℝ) ^ j)]
    have h := h2j
    rw [le_div_iff₀ hqpos] at h
    linarith
  have hlt : Nat.floor (A / (q : ℝ)) < 2 ^ (j + 1) := by
    have := Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) (Nat.floor (A / (q : ℝ)))
    rw [hlog] at this
    simpa [Nat.succ_eq_add_one] using this
  have hAqlt : A / (q : ℝ) < (2 : ℝ) ^ (j + 1) := by
    have h := (Nat.floor_lt hAqpos.le).mp hlt
    have hh : ((2 ^ (j + 1) : ℕ) : ℝ) = (2 : ℝ) ^ (j + 1) := Nat.cast_pow 2 (j + 1)
    rwa [hh] at h
  have hlower : A / (2 : ℝ) ^ (j + 1) < (q : ℝ) := by
    rw [div_lt_iff₀ (by positivity : (0 : ℝ) < (2 : ℝ) ^ (j + 1))]
    have h := hAqlt
    rw [div_lt_iff₀ hqpos] at h
    linarith
  exact ⟨hlower, hupper⟩

/-- Harmonic mass of a dyadic fiber is at most `1`. -/
lemma fiber_recip_le_one {A : ℝ} (hA : 0 < A) {j : ℕ} (hj : 1 ≤ j) (Q : ℕ) :
    (∑ q ∈ (Finset.Icc 1 Q).filter (fun q : ℕ => Nat.log 2 (Nat.floor (A / (q : ℝ))) = j),
        1 / (q : ℝ)) ≤ 1 := by
  set a : ℕ := Nat.floor (A / (2 : ℝ) ^ (j + 1)) with ha
  have hsub : (Finset.Icc 1 Q).filter (fun q : ℕ => Nat.log 2 (Nat.floor (A / (q : ℝ))) = j)
      ⊆ Finset.Icc (a + 1) (2 * a + 1) := by
    intro q hq
    obtain ⟨hlow, hup⟩ := fiber_mem_Ioc hA hj hq
    simp only [Finset.mem_Icc]
    constructor
    · have ha_le : (a : ℝ) ≤ A / (2 : ℝ) ^ (j + 1) := by
        rw [ha]; exact Nat.floor_le (by positivity)
      have : (a : ℝ) < (q : ℝ) := lt_of_le_of_lt ha_le hlow
      have : a < q := by exact_mod_cast this
      omega
    · have h2M : A / (2 : ℝ) ^ j = 2 * (A / (2 : ℝ) ^ (j + 1)) := by
        have hp : (2 : ℝ) ^ (j + 1) = (2 : ℝ) ^ j * 2 := by rw [pow_succ]
        rw [hp]
        field_simp
      have hqle : (q : ℝ) ≤ 2 * (A / (2 : ℝ) ^ (j + 1)) := by rw [← h2M]; exact hup
      have hlt : (A / (2 : ℝ) ^ (j + 1)) < (a : ℝ) + 1 := by
        rw [ha]; exact Nat.lt_floor_add_one _
      have hcast : (q : ℝ) < ((2 * a + 2 : ℕ) : ℝ) := by push_cast; linarith
      have : q < 2 * a + 2 := by exact_mod_cast hcast
      omega
  calc (∑ q ∈ (Finset.Icc 1 Q).filter (fun q : ℕ => Nat.log 2 (Nat.floor (A / (q : ℝ))) = j),
        1 / (q : ℝ))
      ≤ ∑ q ∈ Finset.Icc (a + 1) (2 * a + 1), 1 / (q : ℝ) :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (by intro i _ _; positivity)
    _ ≤ 1 := Work.ZeroDensity.Jutila.harmonicIntervalMass a

/-- The `j`-th dyadic fiber (`j ≥ 1`) carries the decay `exp(-(c√(j log 2)))`. -/
lemma FiberSumLe (A c : ℝ) (hA : 0 < A) (hc : 0 ≤ c) (j : ℕ) (hj : 1 ≤ j) (Q : ℕ) :
    (∑ q ∈ (Finset.Icc 1 Q).filter (fun q : ℕ => Nat.log 2 (Nat.floor (A / (q : ℝ))) = j),
        (1 / (q : ℝ)) * Real.exp (-(c * Real.sqrt (Real.log (A / (q : ℝ))))))
      ≤ Real.exp (-(c * Real.sqrt ((j : ℝ) * Real.log 2))) := by
  set E : ℝ := Real.exp (-(c * Real.sqrt ((j : ℝ) * Real.log 2))) with hE
  have hEpos : 0 ≤ E := hE ▸ Real.exp_nonneg _
  have hterm : ∀ q ∈ (Finset.Icc 1 Q).filter (fun q : ℕ => Nat.log 2 (Nat.floor (A / (q : ℝ))) = j),
      (1 / (q : ℝ)) * Real.exp (-(c * Real.sqrt (Real.log (A / (q : ℝ))))) ≤ (1 / (q : ℝ)) * E := by
    intro q hq
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    obtain ⟨hlow, hup⟩ := fiber_mem_Ioc hA hj hq
    rw [hE]
    apply Real.exp_le_exp.mpr
    apply neg_le_neg
    apply mul_le_mul_of_nonneg_left _ hc
    apply Real.sqrt_le_sqrt
    have hqpos : (0 : ℝ) < (q : ℝ) := by
      have := (Finset.mem_Icc.mp (Finset.mem_filter.mp hq).1).1
      exact_mod_cast (by omega : 0 < q)
    have h2j : (2 : ℝ) ^ j ≤ A / (q : ℝ) := by
      rw [le_div_iff₀ hqpos]
      rw [le_div_iff₀ (by positivity : (0 : ℝ) < (2 : ℝ) ^ j)] at hup
      linarith
    calc (j : ℝ) * Real.log 2 = Real.log ((2 : ℝ) ^ j) := (Real.log_pow 2 j).symm
      _ ≤ Real.log (A / (q : ℝ)) := Real.log_le_log (by positivity) h2j
  calc (∑ q ∈ (Finset.Icc 1 Q).filter (fun q : ℕ => Nat.log 2 (Nat.floor (A / (q : ℝ))) = j),
        (1 / (q : ℝ)) * Real.exp (-(c * Real.sqrt (Real.log (A / (q : ℝ))))))
      ≤ ∑ q ∈ (Finset.Icc 1 Q).filter (fun q : ℕ => Nat.log 2 (Nat.floor (A / (q : ℝ))) = j),
        (1 / (q : ℝ)) * E := Finset.sum_le_sum hterm
    _ = (∑ q ∈ (Finset.Icc 1 Q).filter (fun q : ℕ => Nat.log 2 (Nat.floor (A / (q : ℝ))) = j),
        1 / (q : ℝ)) * E := by rw [Finset.sum_mul]
    _ ≤ 1 * E := by
        apply mul_le_mul_of_nonneg_right _ hEpos
        exact fiber_recip_le_one hA hj Q
    _ = E := by rw [one_mul]

/-- The `j = 0` fiber (`q > A/2`) contributes at most `4`, using `Q ≤ 2A`. -/
lemma FiberZeroLe (A c : ℝ) (hA : 0 < A) (hc : 0 ≤ c) (Q : ℕ) (hQ : (Q : ℝ) ≤ 2 * A) :
    (∑ q ∈ (Finset.Icc 1 Q).filter (fun q : ℕ => Nat.log 2 (Nat.floor (A / (q : ℝ))) = 0),
        (1 / (q : ℝ)) * Real.exp (-(c * Real.sqrt (Real.log (A / (q : ℝ))))))
      ≤ 4 := by
  have hterm : ∀ q ∈ (Finset.Icc 1 Q).filter (fun q : ℕ => Nat.log 2 (Nat.floor (A / (q : ℝ))) = 0),
      (1 / (q : ℝ)) * Real.exp (-(c * Real.sqrt (Real.log (A / (q : ℝ))))) ≤ 2 / A := by
    intro q hq
    rw [Finset.mem_filter, Finset.mem_Icc] at hq
    obtain ⟨⟨hq1, hqQ⟩, hlog⟩ := hq
    have hqpos : (0 : ℝ) < (q : ℝ) := by exact_mod_cast (by omega : 0 < q)
    have hAqpos : 0 ≤ A / (q : ℝ) := div_nonneg hA.le hqpos.le
    have hlt : Nat.floor (A / (q : ℝ)) < 2 := by
      have := Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) (Nat.floor (A / (q : ℝ)))
      rw [hlog] at this
      simpa [Nat.succ_eq_add_one] using this
    have hAqlt : A / (q : ℝ) < 2 := by
      have := (Nat.floor_lt hAqpos).mp hlt
      push_cast at this
      simpa using this
    have hinv : 1 / (q : ℝ) < 2 / A := by
      rw [div_lt_div_iff₀ hqpos hA]
      have h := hAqlt
      rw [div_lt_iff₀ hqpos] at h
      linarith
    have hexp : Real.exp (-(c * Real.sqrt (Real.log (A / (q : ℝ))))) ≤ 1 := by
      rw [Real.exp_le_one_iff]
      have : 0 ≤ c * Real.sqrt (Real.log (A / (q : ℝ))) := mul_nonneg hc (Real.sqrt_nonneg _)
      linarith
    calc (1 / (q : ℝ)) * Real.exp (-(c * Real.sqrt (Real.log (A / (q : ℝ)))))
        ≤ (1 / (q : ℝ)) * 1 := mul_le_mul_of_nonneg_left hexp (by positivity)
      _ = 1 / (q : ℝ) := by ring
      _ ≤ 2 / A := le_of_lt hinv
  calc (∑ q ∈ (Finset.Icc 1 Q).filter (fun q : ℕ => Nat.log 2 (Nat.floor (A / (q : ℝ))) = 0),
        (1 / (q : ℝ)) * Real.exp (-(c * Real.sqrt (Real.log (A / (q : ℝ))))))
      ≤ ∑ q ∈ (Finset.Icc 1 Q).filter (fun q : ℕ => Nat.log 2 (Nat.floor (A / (q : ℝ))) = 0),
        (2 / A) := Finset.sum_le_sum hterm
    _ = (((Finset.Icc 1 Q).filter
        (fun q : ℕ => Nat.log 2 (Nat.floor (A / (q : ℝ))) = 0)).card : ℝ) * (2 / A) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (Q : ℝ) * (2 / A) := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        have hcard : ((Finset.Icc 1 Q).filter
            (fun q : ℕ => Nat.log 2 (Nat.floor (A / (q : ℝ))) = 0)).card ≤ Q := by
          calc ((Finset.Icc 1 Q).filter
              (fun q : ℕ => Nat.log 2 (Nat.floor (A / (q : ℝ))) = 0)).card
              ≤ (Finset.Icc 1 Q).card := Finset.card_filter_le _ _
            _ = Q := by rw [Nat.card_Icc]; omega
        exact_mod_cast hcard
    _ = 2 * Q / A := by ring
    _ ≤ 4 := by
        rw [div_le_iff₀ hA]
        linarith [hQ]

/-- The shifted series `Σ_{k<J} exp(-(c√((k+1)log 2)))` is uniformly bounded. -/
lemma SeriesBoundShift (c : ℝ) (hc : 0 < c) (J : ℕ) :
    (∑ k ∈ Finset.range J, Real.exp (-(c * Real.sqrt (((k + 1 : ℕ) : ℝ) * Real.log 2))))
      ≤ 10 + 10 / (c * Real.sqrt (Real.log 2)) ^ 2 := by
  set a : ℝ := c * Real.sqrt (Real.log 2) with ha
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hapos : 0 < a := by rw [ha]; exact mul_pos hc (Real.sqrt_pos.mpr hlog2)
  have hcongr : ∀ k : ℕ,
      Real.exp (-(c * Real.sqrt (((k + 1 : ℕ) : ℝ) * Real.log 2)))
        = Real.exp (-(a * Real.sqrt (((k + 1 : ℕ) : ℝ)))) := by
    intro k
    congr 1
    rw [ha, Real.sqrt_mul (by positivity) (Real.log 2)]
    ring
  rw [Finset.sum_congr rfl (fun k _ => hcongr k)]
  have h2 : (∑ k ∈ Finset.range J, Real.exp (-(a * Real.sqrt (((k + 1 : ℕ) : ℝ)))))
      ≤ (∑ j ∈ Finset.range (J + 1), Real.exp (-(a * Real.sqrt ((j : ℝ))))) := by
    rw [Finset.sum_range_succ']
    exact le_add_of_nonneg_right (Real.exp_nonneg _)
  calc (∑ k ∈ Finset.range J, Real.exp (-(a * Real.sqrt (((k + 1 : ℕ) : ℝ)))))
      ≤ (∑ j ∈ Finset.range (J + 1), Real.exp (-(a * Real.sqrt ((j : ℝ))))) := h2
    _ ≤ 10 + 10 / a ^ 2 := ExpSumNegSqrtSqBound hapos J

theorem CzHarmDecayHere (c : ℝ) (hc : 0 < c) :
    ∃ C : ℝ, 0 < C ∧ ∀ (A : ℝ) (Q : ℕ), 0 < A → (Q : ℝ) ≤ 2 * A →
      (∑ q ∈ Finset.Icc 1 Q,
        (1 / (q : ℝ)) * Real.exp (-(c * Real.sqrt (Real.log (A / (q : ℝ)))))) ≤ C := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  refine ⟨14 + 10 / (c * Real.sqrt (Real.log 2)) ^ 2, ?_, ?_⟩
  · have h : 0 < c * Real.sqrt (Real.log 2) := mul_pos hc (Real.sqrt_pos.mpr hlog2)
    positivity
  · intro A Q hA hQ
    set J : ℕ := Nat.log 2 (Nat.floor A) with hJ
    have hmap : ∀ q ∈ Finset.Icc 1 Q,
        Nat.log 2 (Nat.floor (A / (q : ℝ))) ∈ Finset.range (J + 1) := by
      intro q hq
      rw [Finset.mem_range]
      have hq1 : 1 ≤ q := (Finset.mem_Icc.mp hq).1
      have hqpos : (0 : ℝ) < (q : ℝ) := by exact_mod_cast (by omega : 0 < q)
      have hq1' : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq1
      have hAle : A / (q : ℝ) ≤ A := by
        rw [div_le_iff₀ hqpos]
        nlinarith [mul_nonneg hA.le (sub_nonneg.mpr hq1')]
      have hfloor : Nat.floor (A / (q : ℝ)) ≤ Nat.floor A := Nat.floor_mono hAle
      have hlogle : Nat.log 2 (Nat.floor (A / (q : ℝ))) ≤ Nat.log 2 (Nat.floor A) :=
        Nat.log_mono_right hfloor
      rw [hJ]
      omega
    have hfib := Finset.sum_fiberwise_of_maps_to hmap
      (fun q : ℕ => (1 / (q : ℝ)) * Real.exp (-(c * Real.sqrt (Real.log (A / (q : ℝ))))))
    rw [← hfib]
    rw [Finset.sum_range_succ']
    have h0 : (∑ q ∈ (Finset.Icc 1 Q).filter (fun q : ℕ => Nat.log 2 (Nat.floor (A / (q : ℝ))) = 0),
        (1 / (q : ℝ)) * Real.exp (-(c * Real.sqrt (Real.log (A / (q : ℝ)))))) ≤ 4 :=
      FiberZeroLe A c hA hc.le Q hQ
    have hk : (∑ k ∈ Finset.range J,
        (∑ q ∈ (Finset.Icc 1 Q).filter (fun q : ℕ => Nat.log 2 (Nat.floor (A / (q : ℝ))) = k + 1),
          (1 / (q : ℝ)) * Real.exp (-(c * Real.sqrt (Real.log (A / (q : ℝ)))))))
        ≤ ∑ k ∈ Finset.range J, Real.exp (-(c * Real.sqrt (((k + 1 : ℕ) : ℝ) * Real.log 2))) := by
      apply Finset.sum_le_sum
      intro k _
      exact FiberSumLe A c hA hc.le (k + 1) (by omega) Q
    have hser : (∑ k ∈ Finset.range J, Real.exp (-(c * Real.sqrt (((k + 1 : ℕ) : ℝ) * Real.log 2))))
        ≤ 10 + 10 / (c * Real.sqrt (Real.log 2)) ^ 2 := SeriesBoundShift c hc J
    linarith [hk, hser, h0]

end Work.ZeroDensity.Jutila.LzDiffAux
