import Mathlib
import Submission.Work.BMF.Defs
import Submission.Work.BMF.n8_defs
import Submission.Work.N8.window_norm_intervalIntegrable

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.N8

/-- `‖e^{ia} - e^{ib}‖ ≤ |a - b|` for real `a`, `b`. -/
lemma norm_exp_I_mul_sub_le (a b : ℝ) :
    ‖Complex.exp (Complex.I * a) - Complex.exp (Complex.I * b)‖ ≤ |a - b| := by
  have h : Complex.exp (Complex.I * a)
      = Complex.exp (Complex.I * b) * Complex.exp (Complex.I * (a - b)) := by
    rw [← Complex.exp_add]; congr 1; ring
  have hmain_eq : Complex.exp (Complex.I * a) - Complex.exp (Complex.I * b)
      = Complex.exp (Complex.I * b) * (Complex.exp (Complex.I * (a - b)) - 1) := by
    rw [mul_sub, mul_one, ← h]
  rw [hmain_eq, norm_mul, Complex.norm_exp_I_mul_ofReal b, one_mul]
  simpa [Real.norm_eq_abs] using Real.norm_exp_I_mul_ofReal_sub_one_le (x := a - b)

/-- For `0 ≤ y`, `0 ≤ H'`, any `n ∈ natIcc y (y+H')` satisfies `y ≤ n ≤ y + H'`. -/
lemma natIcc_mem_sub {y H' : ℝ} (hy : 0 ≤ y) (hH' : 0 ≤ H') {n : ℕ}
    (hn : n ∈ Work.BMF.natIcc y (y + H')) : y ≤ (n : ℝ) ∧ (n : ℝ) ≤ y + H' := by
  rw [Work.BMF.natIcc, Finset.mem_Icc] at hn
  obtain ⟨h1, h2⟩ := hn
  refine ⟨le_trans (Nat.le_ceil y) (by exact_mod_cast h1), ?_⟩
  exact le_trans (by exact_mod_cast h2) (Nat.floor_le (by linarith))

/-- Sum of the distances `n - ⌈y⌉₊` over the integers `n` in the window `[y, y+H']`. -/
lemma window_sum_dist_ceil_le (y H' : ℝ) (hH' : 0 ≤ H') :
    ∑ n ∈ Work.BMF.natIcc y (y + H'), ((n : ℝ) - (⌈y⌉₊ : ℝ))
      ≤ (⌊H'⌋₊ : ℝ) * ((⌊H'⌋₊ : ℝ) + 1) := by
  set I := Work.BMF.natIcc y (y + H') with hI
  have hmem : ∀ n ∈ I, ⌈y⌉₊ ≤ n ∧ n ≤ ⌊y + H'⌋₊ := by
    intro n hn; rw [hI, Work.BMF.natIcc] at hn; exact Finset.mem_Icc.mp hn
  have hfloor : ⌊y + H'⌋₊ ≤ ⌈y⌉₊ + ⌊H'⌋₊ := by
    have h1 : y + H' ≤ (⌈y⌉₊ : ℝ) + H' := by have := Nat.le_ceil y; linarith
    calc ⌊y + H'⌋₊ ≤ ⌊(⌈y⌉₊ : ℝ) + H'⌋₊ := Nat.floor_mono h1
      _ = ⌊H' + (⌈y⌉₊ : ℝ)⌋₊ := by congr 1; ring
      _ = ⌊H'⌋₊ + ⌈y⌉₊ := Nat.floor_add_natCast hH' ⌈y⌉₊
      _ = ⌈y⌉₊ + ⌊H'⌋₊ := by omega
  have hterm : ∀ n ∈ I, (n : ℝ) - (⌈y⌉₊ : ℝ) ≤ (⌊H'⌋₊ : ℝ) := by
    intro n hn
    have h1 : (n : ℝ) ≤ (⌈y⌉₊ : ℝ) + (⌊H'⌋₊ : ℝ) := by
      have h2 : n ≤ ⌈y⌉₊ + ⌊H'⌋₊ := le_trans (hmem n hn).2 hfloor
      exact_mod_cast h2
    linarith
  have hcard : I.card ≤ ⌊H'⌋₊ + 1 := by
    have hsub : I ⊆ Finset.Icc ⌈y⌉₊ (⌈y⌉₊ + ⌊H'⌋₊) := by
      intro n hn; exact Finset.mem_Icc.mpr ⟨(hmem n hn).1, le_trans (hmem n hn).2 hfloor⟩
    calc I.card ≤ (Finset.Icc ⌈y⌉₊ (⌈y⌉₊ + ⌊H'⌋₊)).card := Finset.card_le_card hsub
      _ = ⌊H'⌋₊ + 1 := by rw [Nat.card_Icc]; omega
  calc ∑ n ∈ I, ((n : ℝ) - (⌈y⌉₊ : ℝ)) ≤ ∑ n ∈ I, (⌊H'⌋₊ : ℝ) := Finset.sum_le_sum hterm
    _ = (I.card : ℝ) * (⌊H'⌋₊ : ℝ) := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ((⌊H'⌋₊ : ℝ) + 1) * (⌊H'⌋₊ : ℝ) := by
        have hc : (I.card : ℝ) ≤ (⌊H'⌋₊ : ℝ) + 1 := by exact_mod_cast hcard
        have h0 : (0 : ℝ) ≤ ⌊H'⌋₊ := Nat.cast_nonneg _
        nlinarith
    _ = (⌊H'⌋₊ : ℝ) * ((⌊H'⌋₊ : ℝ) + 1) := by ring

theorem window_transfer_phase {g : ℕ → ℂ} {ψ : ℝ → ℝ} {K x L H' : ℝ} (hx : 1 ≤ x) (hH' : 0 < H') (hH'L : H' ≤ L)
    (hK : 0 ≤ K) (hg : ∀ n, ‖g n‖ ≤ 1)
    (hψ : ∀ a ∈ Set.Icc x (x + L), ∀ b ∈ Set.Icc x (x + L), |ψ a - ψ b| ≤ (K / L) * |a - b|) :
    (∫ y in x..(x + L - H'), ‖∑ n ∈ Work.BMF.natIcc y (y + H'), g n * Complex.exp (Complex.I * (ψ n))‖)
      ≤ (∫ y in x..(x + L - H'), ‖∑ n ∈ Work.BMF.natIcc y (y + H'), g n‖)
        + K * ((⌊H'⌋₊ : ℝ) * ((⌊H'⌋₊ : ℝ) + 1)) := by
  have hH'0 : 0 ≤ H' := le_of_lt hH'
  have hLpos : 0 < L := lt_of_lt_of_le hH' hH'L
  have hb : x ≤ x + L - H' := by linarith
  set N : ℝ := (⌊H'⌋₊ : ℝ) with hN
  set C : ℝ := (K / L) * ((⌊H'⌋₊ : ℝ) * ((⌊H'⌋₊ : ℝ) + 1)) with hC
  have hCnn : 0 ≤ C := by
    rw [hC]
    exact mul_nonneg (div_nonneg hK (le_of_lt hLpos)) (by positivity)
  -- integrability
  have hint_t : IntervalIntegrable
      (fun y : ℝ => ‖∑ n ∈ Work.BMF.natIcc y (y + H'), g n * Complex.exp (Complex.I * (ψ n))‖)
      MeasureTheory.volume x (x + L - H') :=
    window_norm_intervalIntegrable (g := fun n => g n * Complex.exp (Complex.I * (ψ n)))
      (x := x) (L := L) (H' := H') (a := x) (b := x + L - H') hx hH'0
      ⟨le_refl x, by linarith⟩ ⟨by linarith, by linarith⟩
  have hint_p : IntervalIntegrable
      (fun y : ℝ => ‖∑ n ∈ Work.BMF.natIcc y (y + H'), g n‖)
      MeasureTheory.volume x (x + L - H') :=
    window_norm_intervalIntegrable (g := g)
      (x := x) (L := L) (H' := H') (a := x) (b := x + L - H') hx hH'0
      ⟨le_refl x, by linarith⟩ ⟨by linarith, by linarith⟩
  have hint_pc : IntervalIntegrable
      (fun y : ℝ => ‖∑ n ∈ Work.BMF.natIcc y (y + H'), g n‖ + C)
      MeasureTheory.volume x (x + L - H') := by
    have h := hint_p.add (intervalIntegrable_const (c := C) (μ := MeasureTheory.volume) (a := x) (b := x + L - H'))
    simpa using h
  -- pointwise bound
  have hkey : ∀ y ∈ Set.Icc x (x + L - H'),
      ‖∑ n ∈ Work.BMF.natIcc y (y + H'), g n * Complex.exp (Complex.I * (ψ n))‖
        ≤ ‖∑ n ∈ Work.BMF.natIcc y (y + H'), g n‖ + C := by
    intro y hy
    obtain ⟨hyx, hyL⟩ := hy
    have hy0 : 0 ≤ y := le_trans (by linarith) hyx
    by_cases hI : (Work.BMF.natIcc y (y + H')).Nonempty
    · obtain ⟨n1, hn1⟩ := hI
      rw [Work.BMF.natIcc, Finset.mem_Icc] at hn1
      set I := Work.BMF.natIcc y (y + H') with hIdef
      have hceil_le_floor : ⌈y⌉₊ ≤ ⌊y + H'⌋₊ := le_trans hn1.1 hn1.2
      have hmem : ∀ n ∈ I, ⌈y⌉₊ ≤ n ∧ n ≤ ⌊y + H'⌋₊ := by
        intro n hn; rw [hIdef, Work.BMF.natIcc] at hn; exact Finset.mem_Icc.mp hn
      have hceilI : ⌈y⌉₊ ∈ I := by
        rw [hIdef, Work.BMF.natIcc]
        exact Finset.mem_Icc.mpr ⟨le_refl _, hceil_le_floor⟩
      have hceil_mem : (⌈y⌉₊ : ℝ) ∈ Set.Icc x (x + L) := by
        refine ⟨le_trans hyx (Nat.le_ceil y), ?_⟩
        have h3 : ((⌊y + H'⌋₊ : ℕ) : ℝ) ≤ y + H' := Nat.floor_le (by linarith)
        have h4 : (⌈y⌉₊ : ℝ) ≤ (⌊y + H'⌋₊ : ℝ) := by exact_mod_cast hceil_le_floor
        linarith
      have hmemI : ∀ n ∈ I, (n : ℝ) ∈ Set.Icc x (x + L) := by
        intro n hn
        obtain ⟨hn1', hn2'⟩ := hmem n hn
        have hsub : y ≤ (n : ℝ) ∧ (n : ℝ) ≤ y + H' :=
          natIcc_mem_sub hy0 hH'0 (by rw [← hIdef]; exact hn)
        refine ⟨le_trans hyx (le_trans (Nat.le_ceil y) (by exact_mod_cast hn1')), ?_⟩
        linarith [hsub.2]
      have hdecomp : ∑ n ∈ I, g n * Complex.exp (Complex.I * (ψ n))
          = Complex.exp (Complex.I * (ψ (⌈y⌉₊ : ℝ))) * (∑ n ∈ I, g n)
            + ∑ n ∈ I, g n * (Complex.exp (Complex.I * (ψ n))
                - Complex.exp (Complex.I * (ψ (⌈y⌉₊ : ℝ)))) := by
        rw [Finset.mul_sum, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro n hn; ring
      have herr : ‖∑ n ∈ I, g n * (Complex.exp (Complex.I * (ψ n))
            - Complex.exp (Complex.I * (ψ (⌈y⌉₊ : ℝ))))‖ ≤ C := by
        rw [hC]
        have hper : ∀ n ∈ I, ‖g n * (Complex.exp (Complex.I * (ψ n))
              - Complex.exp (Complex.I * (ψ (⌈y⌉₊ : ℝ))))‖
            ≤ (K / L) * ((n : ℝ) - (⌈y⌉₊ : ℝ)) := by
          intro n hn
          have hnmem := hmemI n hn
          have hnge : (⌈y⌉₊ : ℝ) ≤ (n : ℝ) := by exact_mod_cast (hmem n hn).1
          calc ‖g n * (Complex.exp (Complex.I * (ψ n))
                  - Complex.exp (Complex.I * (ψ (⌈y⌉₊ : ℝ))))‖
              = ‖g n‖ * ‖Complex.exp (Complex.I * (ψ n))
                  - Complex.exp (Complex.I * (ψ (⌈y⌉₊ : ℝ)))‖ := norm_mul _ _
            _ ≤ 1 * ‖Complex.exp (Complex.I * (ψ n))
                  - Complex.exp (Complex.I * (ψ (⌈y⌉₊ : ℝ)))‖ := by
                gcongr; exact hg n
            _ = ‖Complex.exp (Complex.I * (ψ n))
                  - Complex.exp (Complex.I * (ψ (⌈y⌉₊ : ℝ)))‖ := one_mul _
            _ ≤ |ψ n - ψ (⌈y⌉₊ : ℝ)| := norm_exp_I_mul_sub_le _ _
            _ ≤ (K / L) * |(n : ℝ) - (⌈y⌉₊ : ℝ)| := hψ _ hnmem _ hceil_mem
            _ = (K / L) * ((n : ℝ) - (⌈y⌉₊ : ℝ)) := by rw [abs_of_nonneg (by linarith)]
        calc ‖∑ n ∈ I, g n * (Complex.exp (Complex.I * (ψ n))
                - Complex.exp (Complex.I * (ψ (⌈y⌉₊ : ℝ))))‖
            ≤ ∑ n ∈ I, ‖g n * (Complex.exp (Complex.I * (ψ n))
                - Complex.exp (Complex.I * (ψ (⌈y⌉₊ : ℝ))))‖ := norm_sum_le _ _
          _ ≤ ∑ n ∈ I, (K / L) * ((n : ℝ) - (⌈y⌉₊ : ℝ)) := Finset.sum_le_sum hper
          _ = (K / L) * ∑ n ∈ I, ((n : ℝ) - (⌈y⌉₊ : ℝ)) := by rw [Finset.mul_sum]
          _ ≤ (K / L) * ((⌊H'⌋₊ : ℝ) * ((⌊H'⌋₊ : ℝ) + 1)) := by
              apply mul_le_mul_of_nonneg_left _ (div_nonneg hK (le_of_lt hLpos))
              rw [hIdef]
              exact window_sum_dist_ceil_le y H' hH'0
      calc ‖∑ n ∈ I, g n * Complex.exp (Complex.I * (ψ n))‖
          = ‖Complex.exp (Complex.I * (ψ (⌈y⌉₊ : ℝ))) * (∑ n ∈ I, g n)
              + ∑ n ∈ I, g n * (Complex.exp (Complex.I * (ψ n))
                  - Complex.exp (Complex.I * (ψ (⌈y⌉₊ : ℝ))))‖ := by rw [hdecomp]
        _ ≤ ‖Complex.exp (Complex.I * (ψ (⌈y⌉₊ : ℝ))) * (∑ n ∈ I, g n)‖
              + ‖∑ n ∈ I, g n * (Complex.exp (Complex.I * (ψ n))
                  - Complex.exp (Complex.I * (ψ (⌈y⌉₊ : ℝ))))‖ := norm_add_le _ _
        _ = ‖∑ n ∈ I, g n‖ + ‖∑ n ∈ I, g n * (Complex.exp (Complex.I * (ψ n))
                  - Complex.exp (Complex.I * (ψ (⌈y⌉₊ : ℝ))))‖ := by
              rw [norm_mul, Complex.norm_exp_I_mul_ofReal, one_mul]
        _ ≤ ‖∑ n ∈ I, g n‖ + C := by linarith [herr]
    · rw [Finset.not_nonempty_iff_eq_empty] at hI
      rw [hI]
      simp only [Finset.sum_empty, norm_zero, zero_add]
      exact hCnn
  -- arithmetic
  have harith : C * (L - H') ≤ K * ((⌊H'⌋₊ : ℝ) * ((⌊H'⌋₊ : ℝ) + 1)) := by
    rw [hC]
    have hN : 0 ≤ (⌊H'⌋₊ : ℝ) * ((⌊H'⌋₊ : ℝ) + 1) := by positivity
    have hKL : 0 ≤ K / L := div_nonneg hK (le_of_lt hLpos)
    have hstep : (K / L) * ((⌊H'⌋₊ : ℝ) * ((⌊H'⌋₊ : ℝ) + 1)) * (L - H')
        ≤ (K / L) * ((⌊H'⌋₊ : ℝ) * ((⌊H'⌋₊ : ℝ) + 1)) * L := by
      apply mul_le_mul_of_nonneg_left (by linarith) (mul_nonneg hKL hN)
    have hcancel : (K / L) * ((⌊H'⌋₊ : ℝ) * ((⌊H'⌋₊ : ℝ) + 1)) * L
        = K * ((⌊H'⌋₊ : ℝ) * ((⌊H'⌋₊ : ℝ) + 1)) := by
      have h1 : (K / L) * L = K := div_mul_cancel₀ K (ne_of_gt hLpos)
      calc (K / L) * ((⌊H'⌋₊ : ℝ) * ((⌊H'⌋₊ : ℝ) + 1)) * L
          = ((K / L) * L) * ((⌊H'⌋₊ : ℝ) * ((⌊H'⌋₊ : ℝ) + 1)) := by ring
        _ = K * ((⌊H'⌋₊ : ℝ) * ((⌊H'⌋₊ : ℝ) + 1)) := by rw [h1]
    linarith [hstep, hcancel.le, hcancel.ge]
  calc (∫ y in x..(x + L - H'), ‖∑ n ∈ Work.BMF.natIcc y (y + H'), g n * Complex.exp (Complex.I * (ψ n))‖)
      ≤ ∫ y in x..(x + L - H'), (‖∑ n ∈ Work.BMF.natIcc y (y + H'), g n‖ + C) :=
        intervalIntegral.integral_mono_on (μ := MeasureTheory.volume) (a := x) (b := x + L - H')
          hb hint_t hint_pc hkey
    _ = (∫ y in x..(x + L - H'), ‖∑ n ∈ Work.BMF.natIcc y (y + H'), g n‖)
          + C * (L - H') := by
        rw [intervalIntegral.integral_add (μ := MeasureTheory.volume) (a := x) (b := x + L - H')
              hint_p (intervalIntegrable_const (c := C) (μ := MeasureTheory.volume)
                (a := x) (b := x + L - H')), intervalIntegral.integral_const]
        simp only [smul_eq_mul]; ring
    _ ≤ (∫ y in x..(x + L - H'), ‖∑ n ∈ Work.BMF.natIcc y (y + H'), g n‖)
          + K * ((⌊H'⌋₊ : ℝ) * ((⌊H'⌋₊ : ℝ) + 1)) := by linarith [harith]

end Work.N8
