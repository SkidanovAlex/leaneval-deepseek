import Mathlib
import Submission.Work.LinnikAreas.Density4.SqfreeCoprimeDefs
import Submission.Work.LinnikAreas.Density4.moebU_abs_le
import Submission.Work.LinnikAreas.Density4.moebUtrunc_close

namespace Work.LinnikAreas.Density4

open Finset

/-- For naturals `N`, `D > 0`, the cast of the natural quotient `N / D` is within `1` of the
real quotient `N / D`. -/
private lemma floor_div_cast_close (N D : ℕ) (hD : 0 < D) :
    |((N / D : ℕ) : ℝ) - (N : ℝ) / (D : ℝ)| ≤ 1 := by
  have hle : ((N / D : ℕ) : ℝ) ≤ (N : ℝ) / (D : ℝ) := Nat.cast_div_le
  have hDpos : (0 : ℝ) < (D : ℝ) := by exact_mod_cast hD
  have hcast : ((N / D : ℕ) : ℝ) * (D : ℝ) + ((N % D : ℕ) : ℝ) = (N : ℝ) := by
    have h := Nat.div_add_mod N D
    have h2 : ((D * (N / D) + N % D : ℕ) : ℝ) = (N : ℝ) := by rw [h]
    push_cast at h2
    linarith
  have hr' : ((N % D : ℕ) : ℝ) < (D : ℝ) := by
    exact_mod_cast (Nat.mod_lt N hD)
  have hlt : (N : ℝ) / (D : ℝ) < ((N / D : ℕ) : ℝ) + 1 := by
    rw [div_lt_iff₀ hDpos]
    nlinarith [hcast, hr']
  rw [abs_le]
  exact ⟨by linarith, by linarith⟩

theorem inner_moebius_sum_close (X m₀ r : ℕ) (hX : 1 ≤ X) (hm₀ : 1 ≤ m₀) :
    |(∑ m₂ ∈ (Finset.Icc 1 X).filter (fun m₂ => Nat.Coprime m₂ r),
        (ArithmeticFunction.moebius m₂ : ℝ) * (((X / (m₀ * m₂ ^ 2)) : ℕ) : ℝ))
      - ((X : ℝ) / (m₀ : ℝ)) * moebU r| ≤ 3 * Real.sqrt ((X : ℝ) / (m₀ : ℝ)) := by
  have hXpos : (0 : ℝ) < (X : ℝ) := by exact_mod_cast (by omega : 0 < X)
  have hm0pos : (0 : ℝ) < (m₀ : ℝ) := by exact_mod_cast (by omega : 0 < m₀)
  have hXr1 : (1 : ℝ) ≤ (X : ℝ) := by exact_mod_cast hX
  have hm0r1 : (1 : ℝ) ≤ (m₀ : ℝ) := by exact_mod_cast hm₀
  set c : ℝ := Real.sqrt ((X : ℝ) / (m₀ : ℝ)) with hcdef
  have hcnn : 0 ≤ c := by rw [hcdef]; positivity
  have hcc : c ^ 2 = (X : ℝ) / (m₀ : ℝ) := by
    rw [hcdef]; exact Real.sq_sqrt (by positivity)
  set J : ℕ := ⌊c⌋₊ with hJdef
  have hJle : (J : ℝ) ≤ c := by rw [hJdef]; exact Nat.floor_le hcnn
  have hJlt : c < (J : ℝ) + 1 := by
    have h := Nat.lt_floor_add_one c; rw [← hJdef] at h; exact h
  rcases eq_or_ne J 0 with hJ0 | hJne
  · -- J = 0
    have hclt1 : c < 1 := by
      have h := Nat.lt_floor_add_one c
      rw [← hJdef, hJ0] at h
      simpa using h
    have hXm0 : (X : ℝ) < (m₀ : ℝ) := by
      have h1 : (X : ℝ) / (m₀ : ℝ) < 1 := by rw [← hcc]; nlinarith [hclt1, hcnn]
      rwa [div_lt_one hm0pos] at h1
    have hXlt : X < m₀ := by exact_mod_cast hXm0
    have hS0 : (∑ m₂ ∈ (Finset.Icc 1 X).filter (fun m₂ => Nat.Coprime m₂ r),
        (ArithmeticFunction.moebius m₂ : ℝ) * (((X / (m₀ * m₂ ^ 2)) : ℕ) : ℝ)) = 0 := by
      apply Finset.sum_eq_zero
      intro m₂ hm₂
      rw [Finset.mem_filter, Finset.mem_Icc] at hm₂
      obtain ⟨⟨hm1, _⟩, _⟩ := hm₂
      have hsq : 1 ≤ m₂ ^ 2 := by nlinarith [hm1]
      have hlt : X < m₀ * m₂ ^ 2 := by
        have : m₀ * 1 ≤ m₀ * m₂ ^ 2 := Nat.mul_le_mul_left m₀ hsq
        omega
      rw [Nat.div_eq_of_lt hlt, Nat.cast_zero, mul_zero]
    rw [hS0, zero_sub, abs_neg]
    calc |((X : ℝ) / (m₀ : ℝ)) * moebU r|
        = ((X : ℝ) / (m₀ : ℝ)) * |moebU r| := by
          rw [abs_mul, abs_of_pos (by positivity)]
      _ ≤ ((X : ℝ) / (m₀ : ℝ)) * 2 := by
          exact mul_le_mul_of_nonneg_left (moebU_abs_le r) (by positivity)
      _ = 2 * c ^ 2 := by rw [← hcc]; ring
      _ ≤ 2 * c := by nlinarith [hclt1, hcnn]
      _ ≤ 3 * c := by nlinarith [hcnn]
  · -- J ≥ 1
    have hJ1 : 1 ≤ J := Nat.one_le_iff_ne_zero.mpr hJne
    have hJpos : (0 : ℝ) < (J : ℝ) := by exact_mod_cast (by omega : 0 < J)
    have hc1 : 1 ≤ c := by
      have h : (1 : ℕ) ≤ ⌊c⌋₊ := by rw [← hJdef]; exact hJ1
      simpa using (Nat.le_floor_iff hcnn).mp h
    have hJX : J ≤ X := by
      have h2 : (J : ℝ) ^ 2 ≤ (X : ℝ) ^ 2 := by
        have h1 : (J : ℝ) ^ 2 ≤ c ^ 2 := by nlinarith [hJle, hcnn]
        rw [hcc] at h1
        have h3 : (X : ℝ) / (m₀ : ℝ) ≤ (X : ℝ) := by
          rw [div_le_iff₀ hm0pos]; nlinarith [hXpos, hm0r1]
        have h4 : (X : ℝ) ≤ (X : ℝ) ^ 2 := by nlinarith [hXpos, hXr1]
        linarith
      have hJnn : (0 : ℝ) ≤ (J : ℝ) := Nat.cast_nonneg J
      have hXnn : (0 : ℝ) ≤ (X : ℝ) := le_of_lt hXpos
      have habs := sq_le_sq.mp h2
      rw [abs_of_nonneg hJnn, abs_of_nonneg hXnn] at habs
      exact_mod_cast habs
    -- floor error bound
    have hfloor : ∀ n : ℕ, 1 ≤ n →
        |(((X / (m₀ * n ^ 2)) : ℕ) : ℝ) - (X : ℝ) / ((m₀ : ℝ) * (n : ℝ) ^ 2)| ≤ 1 := by
      intro n hn
      have hD : 0 < m₀ * n ^ 2 := by positivity
      have h := floor_div_cast_close X (m₀ * n ^ 2) hD
      push_cast at h
      exact h
    -- S = sum over Icc 1 J
    have hS : (∑ m₂ ∈ (Finset.Icc 1 X).filter (fun m₂ => Nat.Coprime m₂ r),
        (ArithmeticFunction.moebius m₂ : ℝ) * (((X / (m₀ * m₂ ^ 2)) : ℕ) : ℝ))
      = ∑ n ∈ Finset.Icc 1 J,
          (if Nat.Coprime n r then
            (ArithmeticFunction.moebius n : ℝ) * (((X / (m₀ * n ^ 2)) : ℕ) : ℝ) else 0) := by
      rw [Finset.sum_filter]
      refine (Finset.sum_subset (s₁ := Finset.Icc 1 J) (s₂ := Finset.Icc 1 X) ?_ ?_).symm
      · intro n hn
        rw [Finset.mem_Icc] at hn ⊢
        exact ⟨hn.1, le_trans hn.2 hJX⟩
      · intro n hn hnot
        rw [Finset.mem_Icc] at hn
        obtain ⟨hn1, _⟩ := hn
        have hnJ : J < n := by
          by_contra h
          exact hnot (by rw [Finset.mem_Icc]; omega)
        have hnR : c < (n : ℝ) := by
          have hle : (J : ℝ) + 1 ≤ (n : ℝ) := by exact_mod_cast (by omega : J + 1 ≤ n)
          linarith [hJlt]
        have hReal : (X : ℝ) < (m₀ : ℝ) * (n : ℝ) ^ 2 := by
          have hn2 : c ^ 2 < (n : ℝ) ^ 2 := by nlinarith [hnR, hcnn]
          rw [hcc] at hn2
          have hmul : (m₀ : ℝ) * ((X : ℝ) / (m₀ : ℝ)) = (X : ℝ) := by field_simp
          rw [← hmul]
          exact mul_lt_mul_of_pos_left hn2 hm0pos
        have hXn : X < m₀ * n ^ 2 := by exact_mod_cast hReal
        rw [Nat.div_eq_of_lt hXn, Nat.cast_zero, mul_zero]
        split_ifs <;> rfl
    -- the truncation sum equals (X/m₀) * moebUtrunc
    have hGtrunc : (∑ n ∈ Finset.Icc 1 J, ((X : ℝ) / (m₀ : ℝ)) *
        (if Nat.Coprime n r then (ArithmeticFunction.moebius n : ℝ) / (n : ℝ) ^ 2 else 0))
        = ((X : ℝ) / (m₀ : ℝ)) * moebUtrunc J r := by
      rw [moebUtrunc, Finset.mul_sum, Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro n _
      by_cases hP : Nat.Coprime n r <;> simp [hP]
    -- finite difference bound
    have hfin : |(∑ n ∈ Finset.Icc 1 J,
          (if Nat.Coprime n r then
            (ArithmeticFunction.moebius n : ℝ) * (((X / (m₀ * n ^ 2)) : ℕ) : ℝ) else 0))
        - ((X : ℝ) / (m₀ : ℝ)) * moebUtrunc J r| ≤ (J : ℝ) := by
      rw [← hGtrunc, ← Finset.sum_sub_distrib]
      refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
      have hterm : ∀ n ∈ Finset.Icc 1 J,
          |(if Nat.Coprime n r then
              (ArithmeticFunction.moebius n : ℝ) * (((X / (m₀ * n ^ 2)) : ℕ) : ℝ) else 0)
            - ((X : ℝ) / (m₀ : ℝ)) *
              (if Nat.Coprime n r then (ArithmeticFunction.moebius n : ℝ) / (n : ℝ) ^ 2 else 0)|
          ≤ 1 := by
        intro n hn
        rw [Finset.mem_Icc] at hn
        have hn1 : 1 ≤ n := hn.1
        have hfl := hfloor n hn1
        have hPsi : ((X : ℝ) / (m₀ : ℝ)) / (n : ℝ) ^ 2
            = (X : ℝ) / ((m₀ : ℝ) * (n : ℝ) ^ 2) := by
          field_simp
        by_cases hP : Nat.Coprime n r
        · rw [if_pos hP, if_pos hP]
          have hkey : |((X : ℝ) / (m₀ : ℝ)) / (n : ℝ) ^ 2
              - ((X / (m₀ * n ^ 2) : ℕ) : ℝ)| ≤ 1 := by
            rw [hPsi, abs_sub_comm]; exact hfl
          calc |(ArithmeticFunction.moebius n : ℝ) * (((X / (m₀ * n ^ 2)) : ℕ) : ℝ)
                - ((X : ℝ) / (m₀ : ℝ)) * ((ArithmeticFunction.moebius n : ℝ) / (n : ℝ) ^ 2)|
              = |(ArithmeticFunction.moebius n : ℝ)| *
                |((X / (m₀ * n ^ 2) : ℕ) : ℝ) - ((X : ℝ) / (m₀ : ℝ)) / (n : ℝ) ^ 2| := by
                rw [← abs_mul]; congr 1; ring
            _ ≤ 1 * 1 := by
                refine mul_le_mul (abs_moebius_cast_le_one n) ?_ (abs_nonneg _) (by norm_num)
                rw [abs_sub_comm]; exact hkey
            _ = 1 := by norm_num
        · rw [if_neg hP, if_neg hP]; simp
      refine le_trans (Finset.sum_le_sum hterm) ?_
      rw [Finset.sum_const, Nat.card_Icc]
      simp
    -- the truncation error
    have htrunc := moebUtrunc_close J r hJ1
    have herr : |((X : ℝ) / (m₀ : ℝ)) * moebUtrunc J r - ((X : ℝ) / (m₀ : ℝ)) * moebU r|
        ≤ ((X : ℝ) / (m₀ : ℝ)) / (J : ℝ) := by
      rw [← mul_sub, abs_mul, abs_of_pos (by positivity)]
      calc ((X : ℝ) / (m₀ : ℝ)) * |moebUtrunc J r - moebU r|
          ≤ ((X : ℝ) / (m₀ : ℝ)) * (1 / (J : ℝ)) :=
            mul_le_mul_of_nonneg_left htrunc (by positivity)
        _ = ((X : ℝ) / (m₀ : ℝ)) / (J : ℝ) := by ring
    rw [hS]
    calc |(∑ n ∈ Finset.Icc 1 J,
            (if Nat.Coprime n r then
              (ArithmeticFunction.moebius n : ℝ) * (((X / (m₀ * n ^ 2)) : ℕ) : ℝ) else 0))
          - ((X : ℝ) / (m₀ : ℝ)) * moebU r|
        = |((∑ n ∈ Finset.Icc 1 J,
              (if Nat.Coprime n r then
                (ArithmeticFunction.moebius n : ℝ) * (((X / (m₀ * n ^ 2)) : ℕ) : ℝ) else 0))
            - ((X : ℝ) / (m₀ : ℝ)) * moebUtrunc J r)
          + (((X : ℝ) / (m₀ : ℝ)) * moebUtrunc J r - ((X : ℝ) / (m₀ : ℝ)) * moebU r)| := by
          ring_nf
      _ ≤ |(∑ n ∈ Finset.Icc 1 J,
              (if Nat.Coprime n r then
                (ArithmeticFunction.moebius n : ℝ) * (((X / (m₀ * n ^ 2)) : ℕ) : ℝ) else 0))
            - ((X : ℝ) / (m₀ : ℝ)) * moebUtrunc J r|
          + |((X : ℝ) / (m₀ : ℝ)) * moebUtrunc J r - ((X : ℝ) / (m₀ : ℝ)) * moebU r| :=
          abs_add_le _ _
      _ ≤ (J : ℝ) + ((X : ℝ) / (m₀ : ℝ)) / (J : ℝ) := add_le_add hfin herr
      _ = (J : ℝ) + c ^ 2 / (J : ℝ) := by rw [hcc]
      _ ≤ 3 * c := by
          have heq : (J : ℝ) + c ^ 2 / (J : ℝ) = ((J : ℝ) ^ 2 + c ^ 2) / (J : ℝ) := by
            field_simp
          rw [heq, div_le_iff₀ hJpos]
          have hmul : c * c ≤ c * ((J : ℝ) + 1) :=
            mul_le_mul_of_nonneg_left (le_of_lt hJlt) hcnn
          have hJnn : (0 : ℝ) ≤ (J : ℝ) := Nat.cast_nonneg J
          have hJsq : (J : ℝ) ^ 2 ≤ c * (J : ℝ) := by nlinarith [hJle, hJnn]
          have hcJ : 0 ≤ c * ((J : ℝ) - 1) := by
            refine mul_nonneg hcnn ?_
            linarith [show (1 : ℝ) ≤ (J : ℝ) by exact_mod_cast hJ1]
          nlinarith [hJsq, hmul, hcJ]

end Work.LinnikAreas.Density4
