import Mathlib

namespace Work.LinnikBurgess

/-- The segment bound `∑_{t = 1}^{N} √(gcd m t) ≤ N · τ(m)`, where `τ(m) = m.divisors.card`.

Split the sum according to the value `d = gcd m t` of the summand.  Each `d` ranges over a
divisor of `m`; the fibre of `d` is contained in the image of `{1, …, N/d}` under
`s ↦ d·s` (an injection since `d > 0`), hence has at most `N/d` elements, and
`(N/d)·√d ≤ N` because `√d ≤ d` for `d ≥ 1`.  Summing over the divisors of `m` gives
`N · τ(m)`. -/
theorem sumSqrtGcd_Icc_le_aux (m N : ℕ) (hm : 0 < m) :
    (∑ t ∈ Finset.Icc 1 N, Real.sqrt (((Nat.gcd m t : ℕ)) : ℝ)) ≤ (N : ℝ) * ((m.divisors.card : ℕ) : ℝ) := by
  have key : ∀ t : ℕ, Real.sqrt (((Nat.gcd m t : ℕ)) : ℝ)
      = ∑ d ∈ m.divisors, (if Nat.gcd m t = d then Real.sqrt (((d : ℕ)) : ℝ) else 0) := by
    intro t
    rw [Finset.sum_eq_single_of_mem (Nat.gcd m t)
      (Nat.mem_divisors.mpr ⟨Nat.gcd_dvd_left m t, hm.ne'⟩)]
    · simp
    · intro b _ hb
      rw [if_neg (Ne.symm hb)]
  have hcard : ∀ d ∈ m.divisors,
      ((((Finset.Icc 1 N).filter (fun t => Nat.gcd m t = d)).card : ℕ) : ℝ)
        * Real.sqrt (((d : ℕ)) : ℝ) ≤ (N : ℝ) := by
    intro d hd
    rw [Nat.mem_divisors] at hd
    obtain ⟨hdvd, -⟩ := hd
    have hdpos : 0 < d := Nat.pos_of_dvd_of_pos hdvd hm
    have hsub : (Finset.Icc 1 N).filter (fun t => Nat.gcd m t = d)
        ⊆ (Finset.Icc 1 (N / d)).image (fun s => d * s) := by
      intro t ht
      rw [Finset.mem_filter, Finset.mem_Icc] at ht
      obtain ⟨⟨ht1, ht2⟩, htgcd⟩ := ht
      have hdt : d ∣ t := htgcd ▸ Nat.gcd_dvd_right m t
      rw [Finset.mem_image]
      refine ⟨t / d, ?_, ?_⟩
      · rw [Finset.mem_Icc]
        exact ⟨(Nat.one_le_div_iff hdpos).mpr (Nat.le_of_dvd (by omega) hdt),
          Nat.div_le_div_right ht2⟩
      · exact Nat.mul_div_cancel' hdt
    have hcardle : ((Finset.Icc 1 N).filter (fun t => Nat.gcd m t = d)).card ≤ N / d := by
      refine (Finset.card_le_card hsub).trans ?_
      refine Finset.card_image_le.trans ?_
      simp
    have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg N
    have hd1 : (1 : ℝ) ≤ (d : ℝ) := by
      exact_mod_cast (Nat.one_le_iff_ne_zero.mpr (Nat.pos_iff_ne_zero.mp hdpos))
    have hs : Real.sqrt (((d : ℕ)) : ℝ) ≤ (d : ℝ) := by
      have hsq := Real.sq_sqrt (Nat.cast_nonneg d)
      have h1 : (1 : ℝ) ≤ Real.sqrt (((d : ℕ)) : ℝ) := Real.one_le_sqrt.mpr hd1
      nlinarith
    calc ((((Finset.Icc 1 N).filter (fun t => Nat.gcd m t = d)).card : ℕ) : ℝ)
          * Real.sqrt (((d : ℕ)) : ℝ)
        ≤ ((N : ℝ) / (d : ℝ)) * Real.sqrt (((d : ℕ)) : ℝ) := by
          apply mul_le_mul_of_nonneg_right _ (Real.sqrt_nonneg _)
          calc ((((Finset.Icc 1 N).filter (fun t => Nat.gcd m t = d)).card : ℕ) : ℝ)
              ≤ (((N / d : ℕ)) : ℝ) := by exact_mod_cast hcardle
            _ ≤ (N : ℝ) / (d : ℝ) := Nat.cast_div_le
      _ = (N : ℝ) * (Real.sqrt (((d : ℕ)) : ℝ) / (d : ℝ)) := by ring
      _ ≤ (N : ℝ) * 1 := by
          apply mul_le_mul_of_nonneg_left _ hN
          rw [div_le_one (by exact_mod_cast hdpos)]
          exact hs
      _ = (N : ℝ) := by ring
  calc (∑ t ∈ Finset.Icc 1 N, Real.sqrt (((Nat.gcd m t : ℕ)) : ℝ))
      = ∑ t ∈ Finset.Icc 1 N,
          ∑ d ∈ m.divisors, (if Nat.gcd m t = d then Real.sqrt (((d : ℕ)) : ℝ) else 0) :=
        Finset.sum_congr rfl (fun t _ => key t)
    _ = ∑ d ∈ m.divisors,
          ∑ t ∈ Finset.Icc 1 N, (if Nat.gcd m t = d then Real.sqrt (((d : ℕ)) : ℝ) else 0) :=
        Finset.sum_comm
    _ = ∑ d ∈ m.divisors,
          ((((Finset.Icc 1 N).filter (fun t => Nat.gcd m t = d)).card : ℕ) : ℝ)
            * Real.sqrt (((d : ℕ)) : ℝ) := by
        apply Finset.sum_congr rfl
        intro d _
        rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
    _ ≤ (N : ℝ) * ((m.divisors.card : ℕ) : ℝ) := by
        calc ∑ d ∈ m.divisors,
              ((((Finset.Icc 1 N).filter (fun t => Nat.gcd m t = d)).card : ℕ) : ℝ)
                * Real.sqrt (((d : ℕ)) : ℝ)
            ≤ ∑ _d ∈ m.divisors, (N : ℝ) := Finset.sum_le_sum (fun d hd => hcard d hd)
          _ = (N : ℝ) * ((m.divisors.card : ℕ) : ℝ) := by
              rw [Finset.sum_const, nsmul_eq_mul]
              ring


end Work.LinnikBurgess
