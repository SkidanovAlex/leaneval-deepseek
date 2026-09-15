import Mathlib
import Submission.Commons.Analysis.Measure.packing_separated_of_measure_gt

namespace Commons.Analysis.Complex.Cartan

open MeasureTheory
open scoped ENNReal BigOperators

/-! ### Auxiliary lemmas -/

lemma prod_range_sub_eq_factorial (i : ℕ) :
    ∏ k ∈ Finset.range i, (i - k) = Nat.factorial i := by
  have h := Finset.prod_range_reflect (fun k : ℕ => k + 1) i
  rw [Finset.prod_range_add_one_eq_factorial] at h
  rw [← h]
  apply Finset.prod_congr rfl
  intro k hk
  simp only [Finset.mem_range] at hk
  omega

lemma prod_range_real_sub_eq_factorial (i : ℕ) :
    ∏ k ∈ Finset.range i, ((i:ℝ) - (k:ℝ)) = ((Nat.factorial i : ℕ) : ℝ) := by
  have h : (∏ k ∈ Finset.range i, ((i - k : ℕ) : ℝ)) = ((Nat.factorial i : ℕ) : ℝ) := by
    rw [← Nat.cast_prod, prod_range_sub_eq_factorial]
  rw [← h]
  apply Finset.prod_congr rfl
  intro k hk
  simp only [Finset.mem_range] at hk
  rw [Nat.cast_sub (by omega)]

lemma prod_Ico_real_sub_eq_factorial (i N : ℕ) (hi : i ≤ N) :
    ∏ k ∈ Finset.Ico (i+1) (N+1), ((k:ℝ) - (i:ℝ)) = ((Nat.factorial (N-i) : ℕ) : ℝ) := by
  have h : (∏ m ∈ Finset.range (N-i), ((m+1 : ℕ) : ℝ)) = ((Nat.factorial (N-i) : ℕ) : ℝ) := by
    rw [← Nat.cast_prod, Finset.prod_range_add_one_eq_factorial]
  rw [Finset.prod_Ico_eq_prod_range (fun k => ((k:ℝ) - (i:ℝ))) (i+1) (N+1)]
  have h1 : N + 1 - (i+1) = N - i := by omega
  rw [h1, ← h]
  apply Finset.prod_congr rfl
  intro m _
  push_cast
  ring

lemma gap_accum (y : ℕ → ℝ) (Δ : ℝ) (n : ℕ) (hgap : ∀ k < n, y k + Δ ≤ y (k+1)) :
    ∀ (j k : ℕ), j + k ≤ n → y j + (k:ℝ) * Δ ≤ y (j+k) := by
  intro j k
  induction k with
  | zero => intro _; simp
  | succ k ih =>
      intro hk
      have hk' : j + k ≤ n := by omega
      have h1 := ih hk'
      have h2 := hgap (j+k) (by omega)
      have he : j + (k+1) = (j+k)+1 := by omega
      rw [he]
      push_cast
      linarith

lemma prod_range_erase_abs_sub_ge (N : ℕ) (y : ℕ → ℝ) (Δ : ℝ) (hΔ : 0 < Δ)
    (hgap : ∀ k < N, y k + Δ ≤ y (k+1))
    (i : ℕ) (hi : i ≤ N) :
    ∏ k ∈ (Finset.range (N+1)).erase i, |y i - y k| ≥
      Δ^N * ((Nat.factorial i : ℕ) : ℝ) * ((Nat.factorial (N-i) : ℕ) : ℝ) := by
  have hsplit : (Finset.range (N+1)).erase i
      = Finset.range i ∪ Finset.Ico (i+1) (N+1) := by
    ext k; simp only [Finset.mem_erase, Finset.mem_range, Finset.mem_union, Finset.mem_Ico]; omega
  have hdisj : Disjoint (Finset.range i) (Finset.Ico (i+1) (N+1)) := by
    rw [Finset.disjoint_left]
    intro k hk hk'
    simp only [Finset.mem_range] at hk
    simp only [Finset.mem_Ico] at hk'
    omega
  rw [hsplit, Finset.prod_union hdisj]
  have hleft : ∏ k ∈ Finset.range i, |y i - y k| ≥ Δ^i * ((Nat.factorial i : ℕ) : ℝ) := by
    have hprod1 : ∏ k ∈ Finset.range i, ((i:ℝ) - (k:ℝ)) * Δ ≤ ∏ k ∈ Finset.range i, |y i - y k| := by
      apply Finset.prod_le_prod
      · intro k hk
        simp only [Finset.mem_range] at hk
        have : (k:ℝ) < i := by exact_mod_cast hk
        exact mul_nonneg (by linarith) hΔ.le
      · intro k hk
        simp only [Finset.mem_range] at hk
        have hg := gap_accum y Δ N hgap k (i - k) (by omega)
        have hik : (k + (i - k) : ℕ) = i := by omega
        rw [hik] at hg
        have hcast : ((i - k : ℕ) : ℝ) = (i:ℝ) - (k:ℝ) := by rw [Nat.cast_sub (by omega)]
        rw [hcast] at hg
        have hmul : (0:ℝ) ≤ (i - k : ℕ) * Δ := by positivity
        rw [hcast] at hmul
        have hle : y k ≤ y i := le_trans (le_add_of_nonneg_right hmul) hg
        rw [abs_of_nonneg (by linarith)]
        linarith [hg]
    calc Δ^i * ((Nat.factorial i : ℕ) : ℝ)
        = ∏ k ∈ Finset.range i, ((i:ℝ) - (k:ℝ)) * Δ := by
          rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range,
            prod_range_real_sub_eq_factorial, mul_comm]
      _ ≤ ∏ k ∈ Finset.range i, |y i - y k| := hprod1
  have hright : ∏ k ∈ Finset.Ico (i+1) (N+1), |y i - y k| ≥
      Δ^(N-i) * ((Nat.factorial (N-i) : ℕ) : ℝ) := by
    have hprod1 : ∏ k ∈ Finset.Ico (i+1) (N+1), ((k:ℝ) - (i:ℝ)) * Δ ≤
        ∏ k ∈ Finset.Ico (i+1) (N+1), |y i - y k| := by
      apply Finset.prod_le_prod
      · intro k hk
        simp only [Finset.mem_Ico] at hk
        have : (i:ℝ) < k := by exact_mod_cast hk.1
        exact mul_nonneg (by linarith) hΔ.le
      · intro k hk
        simp only [Finset.mem_Ico] at hk
        have hki : i ≤ k := le_of_lt hk.1
        have hg := gap_accum y Δ N hgap i (k - i) (by omega)
        have hik : (i + (k - i) : ℕ) = k := by omega
        rw [hik] at hg
        have hcast : ((k - i : ℕ) : ℝ) = (k:ℝ) - (i:ℝ) := by rw [Nat.cast_sub hki]
        rw [hcast] at hg
        have hmul : (0:ℝ) ≤ (k - i : ℕ) * Δ := by positivity
        rw [hcast] at hmul
        have hle : y i ≤ y k := le_trans (le_add_of_nonneg_right hmul) hg
        rw [abs_of_nonpos (by linarith), neg_sub]
        linarith [hg]
    calc Δ^(N-i) * ((Nat.factorial (N-i) : ℕ) : ℝ)
        = ∏ k ∈ Finset.Ico (i+1) (N+1), ((k:ℝ) - (i:ℝ)) * Δ := by
          rw [Finset.prod_mul_distrib]
          have hcard : (Finset.Ico (i+1) (N+1)).card = N - i := by
            rw [Nat.card_Ico]; omega
          rw [Finset.prod_const, hcard, prod_Ico_real_sub_eq_factorial i N hi, mul_comm]
      _ ≤ ∏ k ∈ Finset.Ico (i+1) (N+1), |y i - y k| := hprod1
  have hpow : Δ^N = Δ^i * Δ^(N-i) := by rw [← pow_add]; congr 1; omega
  rw [hpow]
  have hfac : Δ^i * Δ^(N-i) * ((Nat.factorial i : ℕ) : ℝ) * ((Nat.factorial (N-i) : ℕ) : ℝ)
      = (Δ^i * ((Nat.factorial i : ℕ) : ℝ)) * (Δ^(N-i) * ((Nat.factorial (N-i) : ℕ) : ℝ)) := by
    ring
  rw [hfac]
  exact mul_le_mul hleft hright (by positivity) (by positivity)

lemma prod_fin_erase_abs_sub_ge (N : ℕ) (x : Fin (N+1) → ℝ) (Δ : ℝ) (hΔ : 0 < Δ)
    (hgap : ∀ i : Fin N, x (Fin.castSucc i) + Δ ≤ x i.succ) (i : Fin (N+1)) :
    ∏ j ∈ Finset.univ.erase i, |x i - x j| ≥
      Δ^N * ((Nat.factorial i.val : ℕ) : ℝ) * ((Nat.factorial (N - i.val) : ℕ) : ℝ) := by
  classical
  set y : ℕ → ℝ := fun k => if h : k < N+1 then x ⟨k, h⟩ else 0 with hy
  have hyi : y i.val = x i := by
    rw [hy]; simp only [dif_pos i.isLt]
  have hyj : ∀ j : Fin (N+1), y j.val = x j := by
    intro j; rw [hy]; simp only [dif_pos j.isLt]
  have hgapy : ∀ k < N, y k + Δ ≤ y (k+1) := by
    intro k hk
    have hk1 : k < N+1 := by omega
    have hk2 : k+1 < N+1 := by omega
    rw [hy]; simp only [dif_pos hk1, dif_pos hk2]
    have := hgap ⟨k, hk⟩
    simpa [Fin.castSucc, Fin.succ] using this
  have hrange := prod_range_erase_abs_sub_ge N y Δ hΔ hgapy i.val (Nat.le_of_lt_succ i.isLt)
  have hkey : ∏ j ∈ Finset.univ.erase i, |x i - x j|
      = ∏ k ∈ (Finset.range (N+1)).erase i.val, |y i.val - y k| := by
    have h1 : ∏ j ∈ Finset.univ.erase i, |x i - x j|
        = ∏ j ∈ Finset.univ.erase i, |y i.val - y j.val| := by
      apply Finset.prod_congr rfl
      intro j _
      rw [hyi, hyj j]
    rw [h1]
    refine Finset.prod_bij (fun (j : Fin (N+1)) _ => j.val) ?_ ?_ ?_ ?_
    · intro j hj
      rw [Finset.mem_erase] at hj ⊢
      exact ⟨fun h => hj.1 (Fin.ext h), Finset.mem_range.mpr j.isLt⟩
    · intro j1 _ j2 _ heq
      exact Fin.ext heq
    · intro k hk
      rw [Finset.mem_erase] at hk
      refine ⟨⟨k, Finset.mem_range.mp hk.2⟩, ?_, rfl⟩
      rw [Finset.mem_erase]
      exact ⟨fun h => hk.1 (by simpa using congrArg Fin.val h), Finset.mem_univ _⟩
    · intro j _
      rfl
  rw [← hkey] at hrange
  exact hrange

lemma sum_inv_factorial_eq_two_pow_div (N : ℕ) :
    ∑ i : Fin (N+1), (1:ℝ)/((Nat.factorial i.val : ℕ) * (Nat.factorial (N - i.val) : ℕ))
      = 2^N / ((Nat.factorial N : ℕ) : ℝ) := by
  have hN : ((Nat.factorial N : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero N
  rw [eq_div_iff hN, Finset.sum_mul]
  have key : ∀ i : Fin (N+1),
      (1:ℝ)/((Nat.factorial i.val : ℕ) * (Nat.factorial (N - i.val) : ℕ)) *
          ((Nat.factorial N : ℕ) : ℝ)
        = (Nat.choose N i.val : ℝ) := by
    intro i
    have hi : i.val ≤ N := Nat.le_of_lt_succ i.isLt
    have hmul : (Nat.choose N i.val : ℝ) * ((Nat.factorial i.val : ℕ) : ℝ) *
        ((Nat.factorial (N - i.val) : ℕ) : ℝ) = ((Nat.factorial N : ℕ) : ℝ) := by
      exact_mod_cast Nat.choose_mul_factorial_mul_factorial hi
    have ha : ((Nat.factorial i.val : ℕ) : ℝ) ≠ 0 := by positivity
    have hb : ((Nat.factorial (N - i.val) : ℕ) : ℝ) ≠ 0 := by positivity
    field_simp
    linarith [hmul]
  rw [Finset.sum_congr rfl (fun i _ => key i)]
  rw [show (∑ i : Fin (N+1), (Nat.choose N i.val : ℝ))
        = ((∑ m ∈ Finset.range (N+1), Nat.choose N m : ℕ) : ℝ) from ?_]
  · rw [Nat.sum_range_choose]; push_cast; ring
  · rw [Nat.cast_sum]
    exact Fin.sum_univ_eq_sum_range (fun m => (Nat.choose N m : ℝ)) (N+1)

lemma factorial_ge_div_pow (N : ℕ) : ((N:ℝ)/4)^N ≤ ((Nat.factorial N : ℕ) : ℝ) := by
  have hmain : (N:ℝ)^N ≤ 4^N * ((Nat.factorial N : ℕ) : ℝ) := by
    induction N with
    | zero => simp
    | succ n ih =>
      rcases Nat.eq_zero_or_pos n with hn0 | hn
      · subst hn0; norm_num
      · have hnpos : (0:ℝ) < n := by exact_mod_cast hn
        have hsplit : ((n:ℝ)+1)^n = (n:ℝ)^n * (1 + (n:ℝ)⁻¹)^n := by
          rw [← mul_pow]; congr 1; field_simp
        have hexp : (1 + (n:ℝ)⁻¹)^n ≤ Real.exp 1 := Real.one_add_inv_pow_le_exp
        have he3 : Real.exp 1 < 3 := Real.exp_one_lt_three
        have hnn : (0:ℝ) ≤ (n:ℝ)^n := by positivity
        have hstep : ((n:ℝ)+1)^(n+1) ≤ 4^(n+1) * ((Nat.factorial (n+1) : ℕ) : ℝ) := by
          have h1 : ((n:ℝ)+1)^(n+1) = ((n:ℝ)+1) * ((n:ℝ)+1)^n := by
            rw [pow_succ']
          rw [h1, hsplit]
          have h2 : (1 + (n:ℝ)⁻¹)^n ≤ 3 := le_trans hexp he3.le
          have h3 : ((n:ℝ)+1) * ((n:ℝ)^n * (1 + (n:ℝ)⁻¹)^n) ≤
              ((n:ℝ)+1) * ((n:ℝ)^n * 3) := by
            apply mul_le_mul_of_nonneg_left _ (by positivity)
            exact mul_le_mul_of_nonneg_left h2 hnn
          have h4 : ((n:ℝ)+1) * ((n:ℝ)^n * 3) ≤ 4^(n+1) * ((Nat.factorial (n+1) : ℕ) : ℝ) := by
            have hfac : ((Nat.factorial (n+1) : ℕ) : ℝ) =
                ((n:ℝ)+1) * ((Nat.factorial n : ℕ) : ℝ) := by
              rw [Nat.factorial_succ]; push_cast; ring
            rw [hfac]
            have hpow : (4:ℝ)^(n+1) = 4^n * 4 := by rw [pow_succ']; ring
            rw [hpow]
            nlinarith [ih, hnn, show (0:ℝ) ≤ 4^n * ((Nat.factorial n : ℕ) : ℝ) by positivity]
          linarith [h3, h4]
        simpa only [Nat.cast_add, Nat.cast_one] using hstep
  rw [div_pow, div_le_iff₀ (by positivity)]
  linarith [hmain]

/-! ### Main theorem -/

theorem monic_level_set_volume_le :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ), 1 ≤ N → ∀ (u : Fin N → ℂ) (δ : ℝ), 0 < δ →
      ∀ (E : Set ℝ), MeasurableSet E → E ⊆ Set.Icc (0 : ℝ) 1 →
        (∀ x ∈ E, ‖∏ j : Fin N, ((x : ℂ) - u j)‖ ≤ δ) →
        (volume E).toReal ≤ C * δ ^ ((1 : ℝ) / N) := by
  refine ⟨30, by norm_num, ?_⟩
  intro N hN u δ hδ E hEmeas hEsub hP
  classical
  set P : Polynomial ℂ := ∏ j : Fin N, (Polynomial.X - Polynomial.C (u j)) with hPdef
  have hPmonic : P.Monic := by
    rw [hPdef]
    exact Polynomial.monic_prod_of_monic _ _ (fun j _ => Polynomial.monic_X_sub_C (u j))
  have hPnatdeg : P.natDegree = N := by
    rw [hPdef, Polynomial.natDegree_prod_of_monic (s := Finset.univ)
      (f := fun j : Fin N => Polynomial.X - Polynomial.C (u j))
      (fun j _ => Polynomial.monic_X_sub_C (u j))]
    simp
  have hPne : P ≠ 0 := hPmonic.ne_zero
  have hPdeg : P.degree = (N : WithBot ℕ) := by
    rw [Polynomial.degree_eq_natDegree hPne, hPnatdeg]
  have hPcoeff : P.coeff N = 1 := by
    have := hPmonic.coeff_natDegree
    rwa [hPnatdeg] at this
  have hPeval : ∀ x : ℂ, P.eval x = ∏ j : Fin N, (x - u j) := by
    intro x
    rw [hPdef, Polynomial.eval_prod]
    apply Finset.prod_congr rfl
    intro j _
    simp [Polynomial.eval_sub]
  set Δ : ℝ := 15 * δ ^ ((1:ℝ)/N) / N with hΔdef
  have hNpos : (0:ℝ) < N := by exact_mod_cast hN
  have hΔpos : 0 < Δ := by
    rw [hΔdef]
    have : 0 < δ ^ ((1:ℝ)/N) := Real.rpow_pos_of_pos hδ _
    positivity
  have hDelta : 2 * (N:ℝ) * Δ = 30 * δ ^ ((1:ℝ)/N) := by
    rw [hΔdef]; field_simp; ring
  have hbound : (volume E).toReal ≤ 30 * δ ^ ((1:ℝ)/N) := by
    by_contra hcon
    rw [not_le] at hcon
    have hmeas : 2 * (N:ℝ) * Δ < (volume E).toReal := by rw [hDelta]; exact hcon
    obtain ⟨x, hxmono, hxmem, hxgap⟩ :=
      Commons.Analysis.Measure.packing_separated_of_measure_gt E hEmeas hEsub Δ hΔpos N hmeas
    have hv : Set.InjOn (fun i : Fin (N+1) => ((x i : ℝ) : ℂ)) ↑(Finset.univ : Finset (Fin (N+1))) := by
      intro i _ j _ hij
      have hxij : x i = x j := Complex.ofReal_injective hij
      exact hxmono.injective hxij
    have hdeg : P.degree < ((Finset.univ : Finset (Fin (N+1))).card : WithBot ℕ) := by
      rw [hPdeg, Finset.card_univ, Fintype.card_fin]
      exact_mod_cast Nat.lt_succ_self N
    have hLag := Lagrange.coeff_eq_sum (s := (Finset.univ : Finset (Fin (N+1))))
      (v := fun i => ((x i : ℝ) : ℂ)) hv hdeg
    have hcard : (Finset.univ : Finset (Fin (N+1))).card = N+1 := by
      rw [Finset.card_univ, Fintype.card_fin]
    rw [hcard, Nat.add_sub_cancel] at hLag
    -- Lagrange bound
    have hstep1 : (1:ℝ) ≤ ∑ i : Fin (N+1),
        ‖P.eval ((x i : ℝ) : ℂ) /
          ∏ j ∈ (Finset.univ.erase i), (((x i : ℝ) : ℂ) - ((x j : ℝ) : ℂ))‖ := by
      have hle := norm_sum_le (Finset.univ : Finset (Fin (N+1)))
        (fun i => P.eval ((x i : ℝ) : ℂ) /
          ∏ j ∈ (Finset.univ.erase i), (((x i : ℝ) : ℂ) - ((x j : ℝ) : ℂ)))
      rw [← hLag, hPcoeff, norm_one] at hle
      exact hle
    have hterm : ∀ i : Fin (N+1),
        ‖P.eval ((x i : ℝ) : ℂ) /
          ∏ j ∈ (Finset.univ.erase i), (((x i : ℝ) : ℂ) - ((x j : ℝ) : ℂ))‖ ≤
        δ / ∏ j ∈ (Finset.univ.erase i), |x i - x j| := by
      intro i
      rw [norm_div]
      have hnum : ‖P.eval ((x i : ℝ) : ℂ)‖ ≤ δ := by
        rw [hPeval]; exact hP (x i) (hxmem i)
      have hden : ‖∏ j ∈ (Finset.univ.erase i), (((x i : ℝ) : ℂ) - ((x j : ℝ) : ℂ))‖
          = ∏ j ∈ (Finset.univ.erase i), |x i - x j| := by
        rw [norm_prod]
        apply Finset.prod_congr rfl
        intro j _
        rw [show ((x i : ℝ) : ℂ) - ((x j : ℝ) : ℂ) = ((x i - x j : ℝ) : ℂ) by push_cast; ring,
          Complex.norm_real, Real.norm_eq_abs]
      rw [hden]
      have hdenpos : 0 < ∏ j ∈ (Finset.univ.erase i), |x i - x j| := by
        apply Finset.prod_pos
        intro j hj
        have hji : j ≠ i := (Finset.mem_erase.mp hj).1
        have hxne : x i ≠ x j := fun h => hji (hxmono.injective h.symm)
        rw [abs_pos]
        exact sub_ne_zero.mpr hxne
      exact div_le_div_of_nonneg_right hnum hdenpos.le
    have hstep2 : ∑ i : Fin (N+1),
        ‖P.eval ((x i : ℝ) : ℂ) /
          ∏ j ∈ (Finset.univ.erase i), (((x i : ℝ) : ℂ) - ((x j : ℝ) : ℂ))‖ ≤
        δ * ∑ i : Fin (N+1), (1 / ∏ j ∈ (Finset.univ.erase i), |x i - x j|) := by
      have hthis : ∀ i : Fin (N+1),
          ‖P.eval ((x i : ℝ) : ℂ) /
            ∏ j ∈ (Finset.univ.erase i), (((x i : ℝ) : ℂ) - ((x j : ℝ) : ℂ))‖ ≤
          δ * (1 / ∏ j ∈ (Finset.univ.erase i), |x i - x j|) := by
        intro i
        calc ‖P.eval ((x i : ℝ) : ℂ) /
                ∏ j ∈ (Finset.univ.erase i), (((x i : ℝ) : ℂ) - ((x j : ℝ) : ℂ))‖
            ≤ δ / ∏ j ∈ (Finset.univ.erase i), |x i - x j| := hterm i
          _ = δ * (1 / ∏ j ∈ (Finset.univ.erase i), |x i - x j|) := by rw [div_eq_mul_one_div]
      calc ∑ i : Fin (N+1), ‖P.eval ((x i : ℝ) : ℂ) /
              ∏ j ∈ (Finset.univ.erase i), (((x i : ℝ) : ℂ) - ((x j : ℝ) : ℂ))‖
          ≤ ∑ i : Fin (N+1), δ * (1 / ∏ j ∈ (Finset.univ.erase i), |x i - x j|) :=
            Finset.sum_le_sum (fun i _ => hthis i)
        _ = δ * ∑ i : Fin (N+1), (1 / ∏ j ∈ (Finset.univ.erase i), |x i - x j|) := by
            rw [Finset.mul_sum]
    have hprod := fun i => prod_fin_erase_abs_sub_ge N x Δ hΔpos hxgap i
    have hstep3 : ∑ i : Fin (N+1), (1 / ∏ j ∈ (Finset.univ.erase i), |x i - x j|) ≤
        (Δ^N)⁻¹ * (2^N / ((Nat.factorial N : ℕ) : ℝ)) := by
      have h1 : ∑ i : Fin (N+1), (1 / ∏ j ∈ (Finset.univ.erase i), |x i - x j|) ≤
          ∑ i : Fin (N+1), (1 / (Δ^N * ((Nat.factorial i.val : ℕ) : ℝ) *
            ((Nat.factorial (N - i.val) : ℕ) : ℝ))) := by
        apply Finset.sum_le_sum
        intro i _
        apply one_div_le_one_div_of_le
        · positivity
        · exact hprod i
      have h2 : ∑ i : Fin (N+1), (1 / (Δ^N * ((Nat.factorial i.val : ℕ) : ℝ) *
            ((Nat.factorial (N - i.val) : ℕ) : ℝ)))
          = (Δ^N)⁻¹ * ∑ i : Fin (N+1), (1 / (((Nat.factorial i.val : ℕ) : ℝ) *
            ((Nat.factorial (N - i.val) : ℕ) : ℝ))) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        field_simp
      rw [h2] at h1
      refine le_trans h1 (le_of_eq ?_)
      rw [sum_inv_factorial_eq_two_pow_div]
    have hmain : (1:ℝ) ≤ δ * ((Δ^N)⁻¹ * (2^N / ((Nat.factorial N : ℕ) : ℝ))) := by
      calc (1:ℝ) ≤ ∑ i : Fin (N+1), ‖P.eval ((x i : ℝ) : ℂ) /
              ∏ j ∈ (Finset.univ.erase i), (((x i : ℝ) : ℂ) - ((x j : ℝ) : ℂ))‖ := hstep1
        _ ≤ δ * ∑ i : Fin (N+1), (1 / ∏ j ∈ (Finset.univ.erase i), |x i - x j|) := hstep2
        _ ≤ δ * ((Δ^N)⁻¹ * (2^N / ((Nat.factorial N : ℕ) : ℝ))) :=
            mul_le_mul_of_nonneg_left hstep3 hδ.le
    -- contradiction
    have hDpow : Δ^N = 15^N * δ / (N:ℝ)^N := by
      rw [hΔdef, div_pow, mul_pow]
      have hrp : (δ ^ ((1:ℝ)/N))^N = δ := by
        rw [show (1:ℝ)/N = (N:ℝ)⁻¹ from by rw [one_div]]
        exact Real.rpow_inv_natCast_pow hδ.le (by omega)
      rw [hrp]
    have hval : δ * ((Δ^N)⁻¹ * (2^N / ((Nat.factorial N : ℕ) : ℝ)))
        = (2*(N:ℝ)/15)^N / ((Nat.factorial N : ℕ) : ℝ) := by
      rw [hDpow]
      have hNd : ((N:ℝ)) ≠ 0 := by positivity
      have hδne : δ ≠ 0 := hδ.ne'
      have hNfac : ((Nat.factorial N : ℕ) : ℝ) ≠ 0 := by positivity
      field_simp
      rw [div_pow, mul_pow]
      field_simp
    rw [hval] at hmain
    have hlt1 : (2*(N:ℝ)/15)^N / ((Nat.factorial N : ℕ) : ℝ) < 1 := by
      rw [div_lt_one (by positivity)]
      have hsplit2 : 2*(N:ℝ)/15 = ((N:ℝ)/4) * ((8:ℝ)/15) := by ring
      rw [hsplit2, mul_pow]
      have hN4pos : (0:ℝ) < ((N:ℝ)/4)^N := by
        apply pow_pos; positivity
      have h8lt : ((8:ℝ)/15)^N < 1 := by
        apply pow_lt_one₀ (by norm_num) (by norm_num)
        omega
      have hfac := factorial_ge_div_pow N
      nlinarith [hfac, h8lt, hN4pos,
        show (0:ℝ) ≤ ((Nat.factorial N : ℕ) : ℝ) by positivity]
    linarith [hmain, hlt1]
  exact hbound

end Commons.Analysis.Complex.Cartan
