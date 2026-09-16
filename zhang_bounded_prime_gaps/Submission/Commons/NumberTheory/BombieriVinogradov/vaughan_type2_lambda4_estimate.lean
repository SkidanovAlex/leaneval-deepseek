import Mathlib
import Submission.Commons.NumberTheory.BombieriVinogradov.maximal_bilinear_char_large_sieve_sSup
import Submission.Commons.NumberTheory.ArithmeticFunction.sum_vonMangoldt_sq_le
import Submission.Commons.NumberTheory.Moebius.sum_moebius_small_divisors_sq_le
import Submission.Commons.NumberTheory.BombieriVinogradov.lam4_block_real_bound
import Submission.Commons.NumberTheory.BombieriVinogradov.lam4_dyadic_sum_bound
import Submission.Commons.NumberTheory.BombieriVinogradov.lam4_block_bilinear
import Submission.Commons.NumberTheory.BombieriVinogradov.lam4_cover_dyadic

namespace Commons.NumberTheory.BombieriVinogradov

open scoped BigOperators

set_option autoImplicit false
set_option maxHeartbeats 1600000

noncomputable def lam4Prim (q : ℕ) : Finset (DirichletCharacter ℂ q) :=
  @Finset.filter (DirichletCharacter ℂ q) (fun χ => χ.IsPrimitive) (Classical.decPred _)
    Finset.univ

noncomputable def lam4C (T n : ℕ) : ℂ :=
  ∑ m ∈ n.divisors.filter (fun m => T < m ∧ T < n / m),
    ((ArithmeticFunction.vonMangoldt m : ℝ) : ℂ) *
      (∑ d ∈ (n / m).divisors.filter (fun d => d ≤ T),
        ((ArithmeticFunction.moebius d : ℤ) : ℂ))

noncomputable def lam4BlkT (T M n : ℕ) : ℂ :=
  ∑ m ∈ n.divisors.filter (fun m => M < m ∧ m ≤ 2 * M ∧ T < n / m),
    ((ArithmeticFunction.vonMangoldt m : ℝ) : ℂ) *
      (∑ d ∈ (n / m).divisors.filter (fun d => d ≤ T),
        ((ArithmeticFunction.moebius d : ℤ) : ℂ))

noncomputable def lam4A (T M m : ℕ) : ℂ :=
  if T < m ∧ M < m ∧ m ≤ 2 * M then ((ArithmeticFunction.vonMangoldt m : ℝ) : ℂ) else 0

noncomputable def lam4B (T k : ℕ) : ℂ :=
  if T < k then (∑ d ∈ k.divisors.filter (fun d => d ≤ T),
        ((ArithmeticFunction.moebius d : ℤ) : ℂ)) else 0

lemma lam4C_cover (T x n : ℕ) (hT : 1 ≤ T) (hn : n ≤ x) :
    lam4C T n = ∑ j ∈ Finset.range (Nat.log 2 (x / (T * T)) + 1),
        lam4BlkT T (T * 2 ^ j) n := by
  have h := lam4_cover_dyadic T x n hT hn
  unfold lam4C lam4BlkT
  exact h

lemma lam4BlkT_bilinear (T M x y q : ℕ) (hM : 1 ≤ M) (hMT : T ≤ M) (hMx : M ≤ x)
    (hy : y ≤ x) (χ : DirichletCharacter ℂ q) :
    (∑ n ∈ Finset.Icc 1 y, lam4BlkT T M n * χ (n : ZMod q))
      = ∑ m ∈ Finset.Icc 1 (2 * M), ∑ k ∈ Finset.Icc 1 (x / M),
          (if m * k ≤ y then (1 : ℂ) else 0) * lam4A T M m * lam4B T k
            * χ ((m * k : ℕ) : ZMod q) := by
  have h := lam4_block_bilinear T M x y q hM hMT hMx hy χ
  unfold lam4BlkT lam4A lam4B
  exact h

lemma lam4_sSup_image_Icc_le {f g : ℕ → ℝ} {a b : ℕ} (ha : 1 ≤ a) (hab : a ≤ b)
    (h : ∀ y ∈ Set.Icc 1 a, f y ≤ g y) :
    sSup (f '' Set.Icc 1 a) ≤ sSup (g '' Set.Icc 1 b) := by
  have hb : 1 ≤ b := le_trans ha hab
  have hne : (f '' Set.Icc 1 a).Nonempty := ⟨f 1, ⟨1, ⟨le_rfl, ha⟩, rfl⟩⟩
  refine csSup_le hne ?_
  rintro v ⟨y, hy, rfl⟩
  have hyb : y ∈ Set.Icc 1 b := ⟨hy.1, le_trans hy.2 hab⟩
  calc f y ≤ g y := h y hy
    _ ≤ sSup (g '' Set.Icc 1 b) :=
        le_csSup ((Set.finite_Icc 1 b).image g).bddAbove ⟨y, hyb, rfl⟩

lemma lam4_sSup_finset_sum_le {x : ℕ} (hx : 1 ≤ x) (s : Finset ℕ) (h : ℕ → ℕ → ℝ) :
    sSup ((fun y : ℕ => ∑ j ∈ s, h j y) '' Set.Icc 1 x)
      ≤ ∑ j ∈ s, sSup ((fun y : ℕ => h j y) '' Set.Icc 1 x) := by
  have hne : ((fun y : ℕ => ∑ j ∈ s, h j y) '' Set.Icc 1 x).Nonempty :=
    ⟨_, ⟨1, ⟨le_rfl, hx⟩, rfl⟩⟩
  refine csSup_le hne ?_
  rintro v ⟨y, hy, rfl⟩
  refine Finset.sum_le_sum (fun j _ => ?_)
  exact le_csSup ((Set.finite_Icc 1 x).image (fun y => h j y)).bddAbove ⟨y, hy, rfl⟩

lemma lam4_nat_log_two_cast_le (n : ℕ) (hn : 1 ≤ n) :
    (Nat.log 2 n : ℝ) ≤ Real.log (n : ℝ) / Real.log 2 := by
  have hpow : (2 : ℕ) ^ Nat.log 2 n ≤ n := Nat.pow_log_le_self 2 (by omega)
  have hcast : ((2 : ℝ) ^ Nat.log 2 n) ≤ (n : ℝ) := by exact_mod_cast hpow
  have hlogeq : Real.log ((2 : ℝ) ^ Nat.log 2 n) = (Nat.log 2 n : ℝ) * Real.log 2 :=
    Real.log_pow 2 _
  have hpos : 0 < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hle : Real.log ((2 : ℝ) ^ Nat.log 2 n) ≤ Real.log (n : ℝ) :=
    Real.log_le_log (by positivity) hcast
  rw [hlogeq] at hle
  rw [le_div_iff₀ hlog2]
  linarith

lemma lam4_two_mul_div_ge (M x : ℕ) (hM : 1 ≤ M) (hMx : M ≤ x) : x ≤ 2 * M * (x / M) := by
  have hdecomp : M * (x / M) + x % M = x := Nat.div_add_mod x M
  have hmod : x % M < M := Nat.mod_lt _ (by omega)
  have ha : 1 ≤ x / M := Nat.div_pos hMx (by omega)
  have h1 : x % M ≤ M * (x / M) := le_of_lt (by
    calc x % M < M := hmod
      _ = 1 * M := (one_mul M).symm
      _ ≤ (x / M) * M := Nat.mul_le_mul_right M ha
      _ = M * (x / M) := Nat.mul_comm _ _)
  calc x = M * (x / M) + x % M := hdecomp.symm
    _ ≤ M * (x / M) + M * (x / M) := Nat.add_le_add_left h1 _
    _ = 2 * M * (x / M) := by ring

/-- **Bilinear (Type II) estimate for the `λ₄` piece of Vaughan's decomposition** (piece `S₄`
of Vaughan's mean value theorem, Akbary--Hambrook (6.15)): with
`λ₄(n) = Σ_{m k = n, T<m, T<k} Λ m · Σ_{d | k, d ≤ T} μ d`, `2 ≤ Q`, `1 ≤ T ≤ x`, the
totient-weighted average over primitive characters of `sup_{y≤x} ‖Σ_{n≤y} λ₄(n) χ(n)‖` is
`≪ (x + Q x^{1/2} T + Q x T^{-1/2} + Q² x^{1/2}) log⁵(xQ)`. -/
theorem vaughan_type2_lambda4_estimate :
    ∃ C : ℝ, 0 < C ∧ ∀ x Q T : ℕ, 2 ≤ x → 2 ≤ Q → 1 ≤ T → T ≤ x →
      (∑ q ∈ Finset.Icc 1 Q, ((q : ℝ) / (q.totient : ℝ)) *
        ∑ χ ∈ (@Finset.filter (DirichletCharacter ℂ q) (fun χ => χ.IsPrimitive)
                (Classical.decPred _) Finset.univ),
          sSup ((fun y : ℕ => ‖∑ n ∈ Finset.Icc 1 y,
              (∑ m ∈ n.divisors.filter (fun m => T < m ∧ T < n / m),
                ((ArithmeticFunction.vonMangoldt m : ℝ) : ℂ) *
                  (∑ d ∈ (n / m).divisors.filter (fun d => d ≤ T),
                    ((ArithmeticFunction.moebius d : ℤ) : ℂ)))
              * χ (n : ZMod q)‖) '' Set.Icc 1 x))
      ≤ C * ((x : ℝ) + (Q : ℝ) * (x : ℝ) ^ (1 / 2 : ℝ) * (T : ℝ)
              + (Q : ℝ) * (x : ℝ) * ((T : ℝ) ^ (1 / 2 : ℝ))⁻¹
              + (Q : ℝ) ^ 2 * (x : ℝ) ^ (1 / 2 : ℝ))
          * (Real.log ((x : ℝ) * (Q : ℝ) + 2)) ^ 5 := by
  obtain ⟨cls, hclspos, hcls⟩ := maximal_bilinear_char_large_sieve_sSup
  obtain ⟨cVM, hVMpos, hVM⟩ := Commons.NumberTheory.ArithmeticFunction.sum_vonMangoldt_sq_le
  obtain ⟨cMoeb, hMoebpos, hMoeb⟩ := Commons.NumberTheory.Moebius.sum_moebius_small_divisors_sq_le
  refine ⟨4096 * (cls * Real.sqrt cVM * Real.sqrt cMoeb) + 1, by positivity, ?_⟩
  intro x Q T hx hQ hT hTx
  have hx1 : 1 ≤ x := by omega
  have hQ1 : 1 ≤ Q := by omega
  have hxR1 : (1 : ℝ) ≤ (x : ℝ) := by exact_mod_cast hx1
  have hxR2 : (2 : ℝ) ≤ (x : ℝ) := by exact_mod_cast hx
  have hQR2 : (2 : ℝ) ≤ (Q : ℝ) := by exact_mod_cast hQ
  have hQR1 : (1 : ℝ) ≤ (Q : ℝ) := by exact_mod_cast (by omega : 1 ≤ Q)
  have hxR0 : (0 : ℝ) ≤ (x : ℝ) := by positivity
  have hQR0 : (0 : ℝ) ≤ (Q : ℝ) := by positivity
  have hTR1 : (1 : ℝ) ≤ (T : ℝ) := by exact_mod_cast hT
  have hTR0 : (0 : ℝ) < (T : ℝ) := by exact_mod_cast (by omega : 0 < T)
  have hxTR : (T : ℝ) ≤ (x : ℝ) := by exact_mod_cast hTx
  set L : ℝ := Real.log ((x : ℝ) * (Q : ℝ) + 2) with hLdef
  have hL1 : 1 ≤ L := by
    rw [hLdef, Real.le_log_iff_exp_le (by positivity)]
    nlinarith [Real.exp_one_lt_d9, hxR2, hQR2]
  have hL0 : 0 ≤ L := le_trans (by norm_num) hL1
  have hlogxL : Real.log (x : ℝ) ≤ L := by
    rw [hLdef]
    apply Real.log_le_log (by positivity)
    nlinarith [hxR0, hQR1]
  have hlogTL : Real.log (T : ℝ) ≤ L := le_trans (Real.log_le_log hTR0 hxTR) hlogxL
  have hlog2L : Real.log 2 ≤ L := le_trans (by linarith only [Real.log_two_lt_d9]) hL1
  change (∑ q ∈ Finset.Icc 1 Q, ((q : ℝ) / (q.totient : ℝ)) *
        ∑ χ ∈ lam4Prim q, sSup ((fun y : ℕ =>
            ‖∑ n ∈ Finset.Icc 1 y, lam4C T n * χ (n : ZMod q)‖) '' Set.Icc 1 x))
      ≤ (4096 * (cls * Real.sqrt cVM * Real.sqrt cMoeb) + 1)
          * ((x : ℝ) + (Q : ℝ) * (x : ℝ) ^ (1 / 2 : ℝ) * (T : ℝ)
              + (Q : ℝ) * (x : ℝ) * ((T : ℝ) ^ (1 / 2 : ℝ))⁻¹
              + (Q : ℝ) ^ 2 * (x : ℝ) ^ (1 / 2 : ℝ)) * L ^ 5
  by_cases hcase : T * T ≤ x
  · -- main case
    have hq1 : 1 ≤ x / (T * T) :=
      (Nat.le_div_iff_mul_le (by positivity : 0 < T * T)).mpr (by simpa using hcase)
    have hqne : x / (T * T) ≠ 0 := by omega
    set J : ℕ := Nat.log 2 (x / (T * T)) + 1 with hJdef
    have hJv : J = Nat.log 2 (x / (T * T)) + 1 := hJdef
    have hJ_le : (J : ℝ) ≤ 3 * L := by
      have hmono : Nat.log 2 (x / (T * T)) ≤ Nat.log 2 x :=
        Nat.log_mono_right (Nat.div_le_self x (T * T))
      have h1 : (Nat.log 2 (x / (T * T)) : ℝ) ≤ Real.log (x : ℝ) / Real.log 2 :=
        le_trans (by exact_mod_cast hmono) (lam4_nat_log_two_cast_le x hx1)
      have hlog2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
      have h2 : Real.log (x : ℝ) / Real.log 2 ≤ L / Real.log 2 :=
        div_le_div_of_nonneg_right hlogxL (le_of_lt hlog2pos)
      have h3 : L / Real.log 2 ≤ 2 * L := by
        rw [div_le_iff₀ hlog2pos]
        nlinarith [hL0, Real.log_two_gt_d9]
      have hbig : (Nat.log 2 (x / (T * T)) : ℝ) ≤ 2 * L := le_trans h1 (le_trans h2 h3)
      rw [hJv]
      push_cast
      linarith
    have hTq : T * (x / (T * T)) ≤ x / T := by
      rw [Nat.le_div_iff_mul_le (by omega : 0 < T)]
      calc T * (x / (T * T)) * T = (T * T) * (x / (T * T)) := by ring
        _ ≤ x := Nat.mul_div_le x (T * T)
    have hTJ : (T : ℝ) * (2 : ℝ) ^ J ≤ 2 * (x : ℝ) / (T : ℝ) := by
      have hnat : T * 2 ^ J ≤ 2 * (x / T) := by
        rw [hJv, Nat.pow_succ]
        have h1 : 2 ^ Nat.log 2 (x / (T * T)) ≤ x / (T * T) :=
          Nat.pow_log_le_self 2 hqne
        calc T * (2 ^ Nat.log 2 (x / (T * T)) * 2)
              = T * 2 ^ Nat.log 2 (x / (T * T)) * 2 := by ring
          _ ≤ T * (x / (T * T)) * 2 := Nat.mul_le_mul_right 2 (Nat.mul_le_mul_left T h1)
          _ = 2 * (T * (x / (T * T))) := by ring
          _ ≤ 2 * (x / T) := Nat.mul_le_mul_left 2 hTq
      have hcast : ((T * 2 ^ J : ℕ) : ℝ) = (T : ℝ) * (2 : ℝ) ^ J := by push_cast; ring
      rw [← hcast]
      have h2 : ((T * 2 ^ J : ℕ) : ℝ) ≤ ((2 * (x / T) : ℕ) : ℝ) := by exact_mod_cast hnat
      refine le_trans h2 ?_
      have h3 : ((x / T : ℕ) : ℝ) ≤ (x : ℝ) / (T : ℝ) := Nat.cast_div_le
      rw [show ((2 * (x / T) : ℕ) : ℝ) = 2 * ((x / T : ℕ) : ℝ) by push_cast; ring, mul_div_assoc]
      exact mul_le_mul_of_nonneg_left h3 (by norm_num)
    have hcastM : ∀ j : ℕ, ((2 * (T * 2 ^ j) : ℕ) : ℝ) = 2 * ((T * 2 ^ j : ℕ) : ℝ) := by
      intro j; push_cast; ring
    have hMcase : ∀ j ∈ Finset.range J, T * 2 ^ j ≤ x := by
      intro j hj
      have hjQ : j ≤ Nat.log 2 (x / (T * T)) := by
        have : j < J := Finset.mem_range.mp hj
        rw [hJv] at this; omega
      have hpow : 2 ^ j ≤ x / (T * T) := by
        calc 2 ^ j ≤ 2 ^ Nat.log 2 (x / (T * T)) := pow_le_pow_right' (by norm_num) hjQ
          _ ≤ x / (T * T) := Nat.pow_log_le_self 2 hqne
      calc T * 2 ^ j ≤ T * (x / (T * T)) := Nat.mul_le_mul_left T hpow
        _ ≤ x / T := hTq
        _ ≤ x := Nat.div_le_self x T
    let saf : ℕ → ℝ := fun j => ∑ m ∈ Finset.Icc 1 (2 * (T * 2 ^ j)),
        ‖lam4A T (T * 2 ^ j) m‖ ^ 2
    let sbf : ℕ → ℝ := fun j => ∑ n ∈ Finset.Icc 1 (x / (T * 2 ^ j)),
        ‖lam4B T n‖ ^ 2
    let GS : ℕ → ℝ := fun j => Real.sqrt 2 * (x : ℝ)
        + Real.sqrt 2 * (Q : ℝ) * Real.sqrt ((x : ℝ) * ((T * 2 ^ j : ℕ) : ℝ))
        + (Q : ℝ) * (x : ℝ) / Real.sqrt ((T * 2 ^ j : ℕ) : ℝ)
        + (Q : ℝ) ^ 2 * Real.sqrt (x : ℝ)
    let bnd : ℕ → ℝ := fun j => cls
        * Real.sqrt ((((2 * (T * 2 ^ j) : ℕ) : ℝ) + (Q : ℝ) ^ 2) * saf j)
        * Real.sqrt ((((x / (T * 2 ^ j) : ℕ) : ℝ) + (Q : ℝ) ^ 2) * sbf j)
        * Real.log (2 * ((2 * (T * 2 ^ j) : ℕ) : ℝ) * ((x / (T * 2 ^ j) : ℕ) : ℝ) + 2)
    have hsaf_bd : ∀ j : ℕ, saf j ≤ cVM * (((2 * (T * 2 ^ j) : ℕ) : ℝ))
        * Real.log (2 * (((2 * (T * 2 ^ j)) : ℕ) : ℝ) + 2) := by
      intro j
      dsimp only [saf]
      refine le_trans (Finset.sum_le_sum (fun m _ => ?_)) (hVM (2 * (T * 2 ^ j)))
      show ‖lam4A T (T * 2 ^ j) m‖ ^ 2 ≤ (ArithmeticFunction.vonMangoldt m) ^ 2
      dsimp only [lam4A]
      split_ifs with hc
      · exact le_of_eq (by rw [← Complex.normSq_eq_norm_sq, Complex.normSq_ofReal]; ring)
      · rw [norm_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0)]; exact sq_nonneg _
    have hsbf_bd : ∀ j : ℕ, sbf j ≤ cMoeb * (((x / (T * 2 ^ j) : ℕ) : ℝ))
        * (Real.log (Real.exp 3 * (T : ℝ))) ^ 2 := by
      intro j
      dsimp only [sbf]
      refine le_trans (Finset.sum_le_sum (fun n _ => ?_)) (hMoeb (x / (T * 2 ^ j)) T hT)
      show ‖lam4B T n‖ ^ 2
        ≤ (∑ d ∈ n.divisors.filter (fun d => d ≤ T), (ArithmeticFunction.moebius d : ℝ)) ^ 2
      dsimp only [lam4B]
      split_ifs with hc
      · have hcast : (∑ d ∈ n.divisors.filter (fun d => d ≤ T),
              ((ArithmeticFunction.moebius d : ℤ) : ℂ))
            = (((∑ d ∈ n.divisors.filter (fun d => d ≤ T),
                (ArithmeticFunction.moebius d : ℝ)) : ℝ) : ℂ) := by
          rw [Complex.ofReal_sum]
          refine Finset.sum_congr rfl (fun d _ => ?_)
          push_cast; ring
        rw [hcast]
        exact le_of_eq (by rw [← Complex.normSq_eq_norm_sq, Complex.normSq_ofReal]; ring)
      · rw [norm_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0)]; exact sq_nonneg _
    have hsup : ∀ (q : ℕ) (χ : DirichletCharacter ℂ q),
        sSup ((fun y : ℕ => ‖∑ n ∈ Finset.Icc 1 y, lam4C T n * χ (n : ZMod q)‖)
            '' Set.Icc 1 x)
          ≤ ∑ j ∈ Finset.range J, sSup ((fun y : ℕ =>
              ‖∑ n ∈ Finset.Icc 1 y, lam4BlkT T (T * 2 ^ j) n * χ (n : ZMod q)‖)
                '' Set.Icc 1 x) := by
      intro q χ
      have hpt : ∀ y ∈ Set.Icc 1 x,
          ‖∑ n ∈ Finset.Icc 1 y, lam4C T n * χ (n : ZMod q)‖
            ≤ ∑ j ∈ Finset.range J,
                ‖∑ n ∈ Finset.Icc 1 y, lam4BlkT T (T * 2 ^ j) n * χ (n : ZMod q)‖ := by
        intro y hy
        have hcov : (∑ n ∈ Finset.Icc 1 y, lam4C T n * χ (n : ZMod q))
            = ∑ j ∈ Finset.range J, ∑ n ∈ Finset.Icc 1 y,
                lam4BlkT T (T * 2 ^ j) n * χ (n : ZMod q) := by
          have hC : ∀ n ∈ Finset.Icc 1 y, lam4C T n
              = ∑ j ∈ Finset.range J, lam4BlkT T (T * 2 ^ j) n := by
            intro n hn
            have hnx : n ≤ x := le_trans (Finset.mem_Icc.mp hn).2 hy.2
            rw [hJv]
            exact lam4C_cover T x n hT hnx
          calc (∑ n ∈ Finset.Icc 1 y, lam4C T n * χ (n : ZMod q))
              = ∑ n ∈ Finset.Icc 1 y,
                  (∑ j ∈ Finset.range J, lam4BlkT T (T * 2 ^ j) n) * χ (n : ZMod q) := by
                refine Finset.sum_congr rfl (fun n hn => ?_)
                rw [hC n hn]
            _ = ∑ n ∈ Finset.Icc 1 y, ∑ j ∈ Finset.range J,
                  lam4BlkT T (T * 2 ^ j) n * χ (n : ZMod q) := by
                refine Finset.sum_congr rfl (fun n _ => ?_)
                rw [Finset.sum_mul]
            _ = ∑ j ∈ Finset.range J, ∑ n ∈ Finset.Icc 1 y,
                  lam4BlkT T (T * 2 ^ j) n * χ (n : ZMod q) := Finset.sum_comm
        rw [hcov]
        exact norm_sum_le _ _
      calc sSup ((fun y : ℕ => ‖∑ n ∈ Finset.Icc 1 y, lam4C T n * χ (n : ZMod q)‖)
              '' Set.Icc 1 x)
          ≤ sSup ((fun y : ℕ => ∑ j ∈ Finset.range J,
                ‖∑ n ∈ Finset.Icc 1 y, lam4BlkT T (T * 2 ^ j) n * χ (n : ZMod q)‖)
                  '' Set.Icc 1 x) := lam4_sSup_image_Icc_le hx1 le_rfl hpt
        _ ≤ ∑ j ∈ Finset.range J, sSup ((fun y : ℕ =>
                ‖∑ n ∈ Finset.Icc 1 y, lam4BlkT T (T * 2 ^ j) n * χ (n : ZMod q)‖)
                  '' Set.Icc 1 x) := lam4_sSup_finset_sum_le hx1 _ _
    have hLS : ∀ j ∈ Finset.range J,
        (∑ q ∈ Finset.Icc 1 Q, ((q : ℝ) / (q.totient : ℝ)) *
          ∑ χ ∈ lam4Prim q, sSup ((fun y : ℕ =>
              ‖∑ n ∈ Finset.Icc 1 y, lam4BlkT T (T * 2 ^ j) n * χ (n : ZMod q)‖)
                '' Set.Icc 1 x))
          ≤ bnd j := by
      intro j hj
      have hM1 : 1 ≤ T * 2 ^ j := by
        have := Nat.mul_pos (by omega : 0 < T) (pow_pos (by norm_num : (0:ℕ) < 2) j)
        omega
      have hMT : T ≤ T * 2 ^ j := by
        have h2 : 1 ≤ 2 ^ j := Nat.one_le_two_pow
        calc T = T * 1 := by ring
          _ ≤ T * 2 ^ j := Nat.mul_le_mul_left T h2
      have hMx : T * 2 ^ j ≤ x := hMcase j hj
      have hN1 : 1 ≤ x / (T * 2 ^ j) := Nat.div_pos hMx (by positivity)
      have hMls : 1 ≤ 2 * (T * 2 ^ j) := by omega
      have h2Mx : x ≤ 2 * (T * 2 ^ j) * (x / (T * 2 ^ j)) :=
        lam4_two_mul_div_ge (T * 2 ^ j) x hM1 hMx
      have hstep : (∑ q ∈ Finset.Icc 1 Q, ((q : ℝ) / (q.totient : ℝ)) *
            ∑ χ ∈ lam4Prim q, sSup ((fun y : ℕ =>
                ‖∑ n ∈ Finset.Icc 1 y, lam4BlkT T (T * 2 ^ j) n * χ (n : ZMod q)‖)
                  '' Set.Icc 1 x))
          ≤ ∑ q ∈ Finset.Icc 1 Q, ((q : ℝ) / (q.totient : ℝ)) *
            ∑ χ ∈ lam4Prim q, sSup ((fun y : ℕ =>
                ‖∑ m ∈ Finset.Icc 1 (2 * (T * 2 ^ j)),
                    ∑ k ∈ Finset.Icc 1 (x / (T * 2 ^ j)),
                    (if m * k ≤ y then (1 : ℂ) else 0) * lam4A T (T * 2 ^ j) m
                      * lam4B T k * χ ((m * k : ℕ) : ZMod q)‖)
                  '' Set.Icc 1 (2 * (T * 2 ^ j) * (x / (T * 2 ^ j)))) := by
        refine Finset.sum_le_sum (fun q _ => mul_le_mul_of_nonneg_left ?_ (by positivity))
        refine Finset.sum_le_sum (fun χ _ => ?_)
        refine lam4_sSup_image_Icc_le hx1 h2Mx ?_
        intro y hy
        rw [lam4BlkT_bilinear T (T * 2 ^ j) x y q hM1 hMT hMx hy.2 χ]
      calc (∑ q ∈ Finset.Icc 1 Q, ((q : ℝ) / (q.totient : ℝ)) *
            ∑ χ ∈ lam4Prim q, sSup ((fun y : ℕ =>
                ‖∑ n ∈ Finset.Icc 1 y, lam4BlkT T (T * 2 ^ j) n * χ (n : ZMod q)‖)
                  '' Set.Icc 1 x))
          ≤ _ := hstep
        _ ≤ bnd j := hcls Q (2 * (T * 2 ^ j)) (x / (T * 2 ^ j)) hQ1 hMls hN1
              (lam4A T (T * 2 ^ j)) (lam4B T)
    have hB : ∀ j ∈ Finset.range J,
        bnd j ≤ 128 * (cls * Real.sqrt cVM * Real.sqrt cMoeb) * L ^ 4 * GS j := by
      intro j hj
      have hM1 : 1 ≤ T * 2 ^ j := by
        have := Nat.mul_pos (by omega : 0 < T) (pow_pos (by norm_num : (0:ℕ) < 2) j)
        omega
      have hMx : T * 2 ^ j ≤ x := hMcase j hj
      have hN1 : 1 ≤ x / (T * 2 ^ j) := Nat.div_pos hMx (by positivity)
      have hM1r : (1 : ℝ) ≤ ((T * 2 ^ j : ℕ) : ℝ) := by exact_mod_cast hM1
      have hMxr : ((T * 2 ^ j : ℕ) : ℝ) ≤ (x : ℝ) := by exact_mod_cast hMx
      have hN1r : (1 : ℝ) ≤ ((x / (T * 2 ^ j) : ℕ) : ℝ) := by exact_mod_cast hN1
      have hNle : ((x / (T * 2 ^ j) : ℕ) : ℝ) ≤ 2 * ((x : ℝ) / ((T * 2 ^ j : ℕ) : ℝ)) := by
        have h1 : ((x / (T * 2 ^ j) : ℕ) : ℝ) ≤ (x : ℝ) / ((T * 2 ^ j : ℕ) : ℝ) := Nat.cast_div_le
        have h2 : (0 : ℝ) ≤ (x : ℝ) / ((T * 2 ^ j : ℕ) : ℝ) := by positivity
        linarith
      have hlogM : Real.log (4 * ((T * 2 ^ j : ℕ) : ℝ) + 2) ≤ 2 * L := by
        have h4 : 4 * ((T * 2 ^ j : ℕ) : ℝ) + 2 ≤ 2 * ((x : ℝ) * (Q : ℝ) + 2) := by
          nlinarith [hMxr, hxR0, hQR2, hQR0]
        calc Real.log (4 * ((T * 2 ^ j : ℕ) : ℝ) + 2)
            ≤ Real.log (2 * ((x : ℝ) * (Q : ℝ) + 2)) := Real.log_le_log (by positivity) h4
          _ = Real.log 2 + L := by rw [Real.log_mul (by norm_num) (by positivity), hLdef]
          _ ≤ 2 * L := by linarith [hlog2L, hL1]
      have hlogT : Real.log (Real.exp 3 * (T : ℝ)) ≤ 4 * L := by
        rw [Real.log_mul (Real.exp_ne_zero 3) (ne_of_gt hTR0), Real.log_exp]
        linarith [hlogTL, hL1]
      have hlogN : Real.log (2 * (2 * ((T * 2 ^ j : ℕ) : ℝ)) * ((x / (T * 2 ^ j) : ℕ) : ℝ) + 2)
          ≤ 2 * L := by
        have hMN : ((T * 2 ^ j : ℕ) : ℝ) * ((x / (T * 2 ^ j) : ℕ) : ℝ) ≤ (x : ℝ) := by
          have h3 : ((T * 2 ^ j) * (x / (T * 2 ^ j)) : ℕ) ≤ x := Nat.mul_div_le x _
          calc ((T * 2 ^ j : ℕ) : ℝ) * ((x / (T * 2 ^ j) : ℕ) : ℝ)
              = (((T * 2 ^ j) * (x / (T * 2 ^ j)) : ℕ) : ℝ) := by push_cast; ring
            _ ≤ (x : ℝ) := by exact_mod_cast h3
        have h4 : 2 * (2 * ((T * 2 ^ j : ℕ) : ℝ)) * ((x / (T * 2 ^ j) : ℕ) : ℝ) + 2
            ≤ 2 * ((x : ℝ) * (Q : ℝ) + 2) := by
          nlinarith [hMN, hxR0, hQR2, hQR0]
        calc Real.log (2 * (2 * ((T * 2 ^ j : ℕ) : ℝ)) * ((x / (T * 2 ^ j) : ℕ) : ℝ) + 2)
            ≤ Real.log (2 * ((x : ℝ) * (Q : ℝ) + 2)) := Real.log_le_log (by positivity) h4
          _ = Real.log 2 + L := by rw [Real.log_mul (by norm_num) (by positivity), hLdef]
          _ ≤ 2 * L := by linarith [hlog2L, hL1]
      have hsaj : saf j ≤ cVM * (2 * ((T * 2 ^ j : ℕ) : ℝ)
          * Real.log (4 * ((T * 2 ^ j : ℕ) : ℝ) + 2)) := by
        have h := hsaf_bd j
        rw [hcastM j] at h
        have heq : cVM * (2 * ((T * 2 ^ j : ℕ) : ℝ)) * Real.log (2 * (2 * ((T * 2 ^ j : ℕ) : ℝ)) + 2)
            = cVM * (2 * ((T * 2 ^ j : ℕ) : ℝ) * Real.log (4 * ((T * 2 ^ j : ℕ) : ℝ) + 2)) := by
          have h2 : (2 * (2 * ((T * 2 ^ j : ℕ) : ℝ)) + 2) = (4 * ((T * 2 ^ j : ℕ) : ℝ) + 2) := by ring
          rw [h2]; ring
        rwa [heq] at h
      have hsbj : sbf j ≤ cMoeb * (((x / (T * 2 ^ j) : ℕ) : ℝ)
          * (Real.log (Real.exp 3 * (T : ℝ))) ^ 2) := by
        have h := hsbf_bd j
        rwa [mul_assoc] at h
      have hsq1 : Real.sqrt ((2 * ((T * 2 ^ j : ℕ) : ℝ) + (Q : ℝ) ^ 2) * saf j)
          ≤ Real.sqrt cVM * Real.sqrt ((2 * ((T * 2 ^ j : ℕ) : ℝ) + (Q : ℝ) ^ 2)
              * (2 * ((T * 2 ^ j : ℕ) : ℝ) * Real.log (4 * ((T * 2 ^ j : ℕ) : ℝ) + 2))) := by
        calc Real.sqrt ((2 * ((T * 2 ^ j : ℕ) : ℝ) + (Q : ℝ) ^ 2) * saf j)
            ≤ Real.sqrt (cVM * ((2 * ((T * 2 ^ j : ℕ) : ℝ) + (Q : ℝ) ^ 2)
                * (2 * ((T * 2 ^ j : ℕ) : ℝ) * Real.log (4 * ((T * 2 ^ j : ℕ) : ℝ) + 2)))) :=
              Real.sqrt_le_sqrt (by
                calc (2 * ((T * 2 ^ j : ℕ) : ℝ) + (Q : ℝ) ^ 2) * saf j
                    ≤ (2 * ((T * 2 ^ j : ℕ) : ℝ) + (Q : ℝ) ^ 2)
                      * (cVM * (2 * ((T * 2 ^ j : ℕ) : ℝ)
                        * Real.log (4 * ((T * 2 ^ j : ℕ) : ℝ) + 2))) :=
                      mul_le_mul_of_nonneg_left hsaj (by positivity)
                  _ = cVM * ((2 * ((T * 2 ^ j : ℕ) : ℝ) + (Q : ℝ) ^ 2)
                      * (2 * ((T * 2 ^ j : ℕ) : ℝ)
                        * Real.log (4 * ((T * 2 ^ j : ℕ) : ℝ) + 2))) := by ring)
          _ = Real.sqrt cVM * Real.sqrt ((2 * ((T * 2 ^ j : ℕ) : ℝ) + (Q : ℝ) ^ 2)
                * (2 * ((T * 2 ^ j : ℕ) : ℝ) * Real.log (4 * ((T * 2 ^ j : ℕ) : ℝ) + 2))) :=
              Real.sqrt_mul (le_of_lt hVMpos) _
      have hsq2 : Real.sqrt ((((x / (T * 2 ^ j) : ℕ) : ℝ) + (Q : ℝ) ^ 2) * sbf j)
          ≤ Real.sqrt cMoeb * Real.sqrt ((((x / (T * 2 ^ j) : ℕ) : ℝ) + (Q : ℝ) ^ 2)
              * (((x / (T * 2 ^ j) : ℕ) : ℝ) * (Real.log (Real.exp 3 * (T : ℝ))) ^ 2)) := by
        calc Real.sqrt ((((x / (T * 2 ^ j) : ℕ) : ℝ) + (Q : ℝ) ^ 2) * sbf j)
            ≤ Real.sqrt (cMoeb * ((((x / (T * 2 ^ j) : ℕ) : ℝ) + (Q : ℝ) ^ 2)
                * (((x / (T * 2 ^ j) : ℕ) : ℝ) * (Real.log (Real.exp 3 * (T : ℝ))) ^ 2))) :=
              Real.sqrt_le_sqrt (by
                calc (((x / (T * 2 ^ j) : ℕ) : ℝ) + (Q : ℝ) ^ 2) * sbf j
                    ≤ (((x / (T * 2 ^ j) : ℕ) : ℝ) + (Q : ℝ) ^ 2)
                      * (cMoeb * (((x / (T * 2 ^ j) : ℕ) : ℝ)
                        * (Real.log (Real.exp 3 * (T : ℝ))) ^ 2)) :=
                      mul_le_mul_of_nonneg_left hsbj (by positivity)
                  _ = cMoeb * ((((x / (T * 2 ^ j) : ℕ) : ℝ) + (Q : ℝ) ^ 2)
                      * (((x / (T * 2 ^ j) : ℕ) : ℝ)
                        * (Real.log (Real.exp 3 * (T : ℝ))) ^ 2)) := by ring)
          _ = Real.sqrt cMoeb * Real.sqrt ((((x / (T * 2 ^ j) : ℕ) : ℝ) + (Q : ℝ) ^ 2)
                * (((x / (T * 2 ^ j) : ℕ) : ℝ) * (Real.log (Real.exp 3 * (T : ℝ))) ^ 2)) :=
              Real.sqrt_mul (le_of_lt hMoebpos) _
      have hBapp := lam4_block_real_bound 1 ((T * 2 ^ j : ℕ) : ℝ) ((x / (T * 2 ^ j) : ℕ) : ℝ)
          (x : ℝ) (Q : ℝ) (T : ℝ) L (by norm_num) hM1r hxR1 hMxr hNle hN1r hQR1 hTR1 hL1
          hlogM hlogT hlogN
      dsimp only [bnd]
      rw [hcastM j]
      calc cls * Real.sqrt ((2 * ((T * 2 ^ j : ℕ) : ℝ) + (Q : ℝ) ^ 2) * saf j)
            * Real.sqrt ((((x / (T * 2 ^ j) : ℕ) : ℝ) + (Q : ℝ) ^ 2) * sbf j)
            * Real.log (2 * (2 * ((T * 2 ^ j : ℕ) : ℝ)) * ((x / (T * 2 ^ j) : ℕ) : ℝ) + 2)
          ≤ cls * (Real.sqrt cVM * Real.sqrt ((2 * ((T * 2 ^ j : ℕ) : ℝ) + (Q : ℝ) ^ 2)
                * (2 * ((T * 2 ^ j : ℕ) : ℝ) * Real.log (4 * ((T * 2 ^ j : ℕ) : ℝ) + 2))))
              * (Real.sqrt cMoeb * Real.sqrt ((((x / (T * 2 ^ j) : ℕ) : ℝ) + (Q : ℝ) ^ 2)
                * (((x / (T * 2 ^ j) : ℕ) : ℝ) * (Real.log (Real.exp 3 * (T : ℝ))) ^ 2)))
              * Real.log (2 * (2 * ((T * 2 ^ j : ℕ) : ℝ)) * ((x / (T * 2 ^ j) : ℕ) : ℝ) + 2) := by
            have hC1nn : 0 ≤ Real.log (2 * (2 * ((T * 2 ^ j : ℕ) : ℝ)) * ((x / (T * 2 ^ j) : ℕ) : ℝ) + 2) :=
              Real.log_nonneg (by nlinarith [hM1r, hN1r])
            refine mul_le_mul_of_nonneg_right ?_ hC1nn
            refine mul_le_mul ?_ hsq2 (Real.sqrt_nonneg _) (by positivity)
            exact mul_le_mul_of_nonneg_left hsq1 (le_of_lt hclspos)
        _ = cls * Real.sqrt cVM * Real.sqrt cMoeb
              * (Real.sqrt ((2 * ((T * 2 ^ j : ℕ) : ℝ) + (Q : ℝ) ^ 2)
                  * (2 * ((T * 2 ^ j : ℕ) : ℝ) * Real.log (4 * ((T * 2 ^ j : ℕ) : ℝ) + 2)))
                * Real.sqrt ((((x / (T * 2 ^ j) : ℕ) : ℝ) + (Q : ℝ) ^ 2)
                  * (((x / (T * 2 ^ j) : ℕ) : ℝ) * (Real.log (Real.exp 3 * (T : ℝ))) ^ 2))
                * Real.log (2 * (2 * ((T * 2 ^ j : ℕ) : ℝ)) * ((x / (T * 2 ^ j) : ℕ) : ℝ) + 2)) := by ring
        _ ≤ cls * Real.sqrt cVM * Real.sqrt cMoeb * (128 * L ^ 4 * GS j) := by
            apply mul_le_mul_of_nonneg_left _ (by positivity)
            dsimp only [GS]
            simpa only [one_mul, mul_one] using hBapp
        _ = 128 * (cls * Real.sqrt cVM * Real.sqrt cMoeb) * L ^ 4 * GS j := by ring
    have hfin : (∑ j ∈ Finset.range J, bnd j)
        ≤ 128 * (cls * Real.sqrt cVM * Real.sqrt cMoeb) * L ^ 4
            * (32 * L * ((x : ℝ) + (Q : ℝ) * Real.sqrt (x : ℝ) * (T : ℝ)
                + (Q : ℝ) * (x : ℝ) / Real.sqrt (T : ℝ) + (Q : ℝ) ^ 2 * Real.sqrt (x : ℝ))) := by
      calc (∑ j ∈ Finset.range J, bnd j)
          ≤ ∑ j ∈ Finset.range J, 128 * (cls * Real.sqrt cVM * Real.sqrt cMoeb) * L ^ 4 * GS j :=
            Finset.sum_le_sum hB
        _ = 128 * (cls * Real.sqrt cVM * Real.sqrt cMoeb) * L ^ 4 * (∑ j ∈ Finset.range J, GS j) := by
            rw [Finset.mul_sum]
        _ ≤ 128 * (cls * Real.sqrt cVM * Real.sqrt cMoeb) * L ^ 4
              * (32 * L * ((x : ℝ) + (Q : ℝ) * Real.sqrt (x : ℝ) * (T : ℝ)
                + (Q : ℝ) * (x : ℝ) / Real.sqrt (T : ℝ) + (Q : ℝ) ^ 2 * Real.sqrt (x : ℝ))) := by
            apply mul_le_mul_of_nonneg_left _ (by positivity)
            have hcongr : (∑ j ∈ Finset.range J, GS j)
                = ∑ j ∈ Finset.range J, (Real.sqrt 2 * (x : ℝ)
                    + Real.sqrt 2 * (Q : ℝ) * Real.sqrt ((x : ℝ) * ((T : ℝ) * (2 : ℝ) ^ j))
                    + (Q : ℝ) * (x : ℝ) / Real.sqrt ((T : ℝ) * (2 : ℝ) ^ j)
                    + (Q : ℝ) ^ 2 * Real.sqrt (x : ℝ)) := by
              refine Finset.sum_congr rfl (fun j _ => ?_)
              dsimp only [GS]
              rw [show ((T * 2 ^ j : ℕ) : ℝ) = (T : ℝ) * (2 : ℝ) ^ j by push_cast; ring]
            rw [hcongr]
            exact lam4_dyadic_sum_bound (x : ℝ) (Q : ℝ) (T : ℝ) L J hxR1 hQR0 hTR1 hL1 hJ_le hTJ
    have hcomb : (∑ q ∈ Finset.Icc 1 Q, ((q : ℝ) / (q.totient : ℝ)) *
          ∑ χ ∈ lam4Prim q, sSup ((fun y : ℕ =>
              ‖∑ n ∈ Finset.Icc 1 y, lam4C T n * χ (n : ZMod q)‖) '' Set.Icc 1 x))
        ≤ ∑ j ∈ Finset.range J, bnd j := by
      have hswap : (∑ q ∈ Finset.Icc 1 Q, ((q : ℝ) / (q.totient : ℝ)) *
            ∑ χ ∈ lam4Prim q, ∑ j ∈ Finset.range J, sSup ((fun y : ℕ =>
                ‖∑ n ∈ Finset.Icc 1 y, lam4BlkT T (T * 2 ^ j) n * χ (n : ZMod q)‖)
                  '' Set.Icc 1 x))
          = ∑ j ∈ Finset.range J, ∑ q ∈ Finset.Icc 1 Q, ((q : ℝ) / (q.totient : ℝ)) *
            ∑ χ ∈ lam4Prim q, sSup ((fun y : ℕ =>
                ‖∑ n ∈ Finset.Icc 1 y, lam4BlkT T (T * 2 ^ j) n * χ (n : ZMod q)‖)
                  '' Set.Icc 1 x) := by
        simp only [Finset.mul_sum]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl (fun j _ => ?_)
        rw [Finset.sum_comm]
      calc (∑ q ∈ Finset.Icc 1 Q, ((q : ℝ) / (q.totient : ℝ)) *
            ∑ χ ∈ lam4Prim q, sSup ((fun y : ℕ =>
                ‖∑ n ∈ Finset.Icc 1 y, lam4C T n * χ (n : ZMod q)‖) '' Set.Icc 1 x))
          ≤ ∑ q ∈ Finset.Icc 1 Q, ((q : ℝ) / (q.totient : ℝ)) *
            ∑ χ ∈ lam4Prim q, ∑ j ∈ Finset.range J, sSup ((fun y : ℕ =>
                ‖∑ n ∈ Finset.Icc 1 y, lam4BlkT T (T * 2 ^ j) n * χ (n : ZMod q)‖)
                  '' Set.Icc 1 x) := by
            refine Finset.sum_le_sum (fun q _ => mul_le_mul_of_nonneg_left ?_ (by positivity))
            exact Finset.sum_le_sum (fun χ _ => hsup q χ)
        _ = _ := hswap
        _ ≤ ∑ j ∈ Finset.range J, bnd j := Finset.sum_le_sum hLS
    have hSSe : ((x : ℝ) + (Q : ℝ) * Real.sqrt (x : ℝ) * (T : ℝ)
          + (Q : ℝ) * (x : ℝ) / Real.sqrt (T : ℝ) + (Q : ℝ) ^ 2 * Real.sqrt (x : ℝ))
        = ((x : ℝ) + (Q : ℝ) * (x : ℝ) ^ (1 / 2 : ℝ) * (T : ℝ)
            + (Q : ℝ) * (x : ℝ) * ((T : ℝ) ^ (1 / 2 : ℝ))⁻¹
            + (Q : ℝ) ^ 2 * (x : ℝ) ^ (1 / 2 : ℝ)) := by
      simp only [Real.sqrt_eq_rpow, div_eq_mul_inv]
    rw [← hSSe]
    have hSnn : 0 ≤ ((x : ℝ) + (Q : ℝ) * Real.sqrt (x : ℝ) * (T : ℝ)
        + (Q : ℝ) * (x : ℝ) / Real.sqrt (T : ℝ) + (Q : ℝ) ^ 2 * Real.sqrt (x : ℝ)) := by positivity
    have hL5 : 0 ≤ L ^ 5 := by positivity
    refine le_trans (le_trans hcomb hfin) ?_
    calc 128 * (cls * Real.sqrt cVM * Real.sqrt cMoeb) * L ^ 4
            * (32 * L * ((x : ℝ) + (Q : ℝ) * Real.sqrt (x : ℝ) * (T : ℝ)
              + (Q : ℝ) * (x : ℝ) / Real.sqrt (T : ℝ) + (Q : ℝ) ^ 2 * Real.sqrt (x : ℝ)))
        = 4096 * (cls * Real.sqrt cVM * Real.sqrt cMoeb) * L ^ 5
            * ((x : ℝ) + (Q : ℝ) * Real.sqrt (x : ℝ) * (T : ℝ)
              + (Q : ℝ) * (x : ℝ) / Real.sqrt (T : ℝ) + (Q : ℝ) ^ 2 * Real.sqrt (x : ℝ)) := by ring
      _ ≤ (4096 * (cls * Real.sqrt cVM * Real.sqrt cMoeb) + 1) * L ^ 5
            * ((x : ℝ) + (Q : ℝ) * Real.sqrt (x : ℝ) * (T : ℝ)
              + (Q : ℝ) * (x : ℝ) / Real.sqrt (T : ℝ) + (Q : ℝ) ^ 2 * Real.sqrt (x : ℝ)) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (by linarith) hL5) hSnn
      _ = (4096 * (cls * Real.sqrt cVM * Real.sqrt cMoeb) + 1)
            * ((x : ℝ) + (Q : ℝ) * Real.sqrt (x : ℝ) * (T : ℝ)
              + (Q : ℝ) * (x : ℝ) / Real.sqrt (T : ℝ) + (Q : ℝ) ^ 2 * Real.sqrt (x : ℝ)) * L ^ 5 := by ring
  · -- degenerate case: T * T > x
    push_neg at hcase
    have hcoeff : ∀ n, n ≤ x → lam4C T n = 0 := by
      intro n hn
      rw [lam4C]
      apply Finset.sum_eq_zero
      intro m hm
      obtain ⟨hmdiv, hTm, hTnm⟩ := Finset.mem_filter.mp hm
      exfalso
      have hmdvd : m ∣ n := (Nat.mem_divisors.mp hmdiv).1
      have hnm : m * (n / m) = n := Nat.mul_div_cancel' hmdvd
      have h1 : T + 1 ≤ m := hTm
      have h2 : T + 1 ≤ n / m := hTnm
      have h3 : (T + 1) * (T + 1) ≤ m * (n / m) := Nat.mul_le_mul h1 h2
      rw [hnm] at h3
      nlinarith [h3, hn, hcase]
    have hLHS0 : (∑ q ∈ Finset.Icc 1 Q, ((q : ℝ) / (q.totient : ℝ)) *
          ∑ χ ∈ lam4Prim q, sSup ((fun y : ℕ =>
              ‖∑ n ∈ Finset.Icc 1 y, lam4C T n * χ (n : ZMod q)‖) '' Set.Icc 1 x)) ≤ 0 := by
      apply Finset.sum_nonpos
      intro q hq
      apply mul_nonpos_of_nonneg_of_nonpos
      · positivity
      · apply Finset.sum_nonpos
        intro χ hχ
        apply csSup_le
        · exact ⟨_, ⟨1, ⟨le_rfl, hx1⟩, rfl⟩⟩
        · rintro v ⟨y, hy, rfl⟩
          have hz : (∑ n ∈ Finset.Icc 1 y, lam4C T n * χ (n : ZMod q)) = 0 := by
            apply Finset.sum_eq_zero
            intro n hn
            rw [hcoeff n (le_trans (Finset.mem_Icc.mp hn).2 hy.2), zero_mul]
          change ‖∑ n ∈ Finset.Icc 1 y, lam4C T n * χ (n : ZMod q)‖ ≤ 0
          rw [hz, norm_zero]
    refine le_trans hLHS0 ?_
    positivity

end Commons.NumberTheory.BombieriVinogradov
