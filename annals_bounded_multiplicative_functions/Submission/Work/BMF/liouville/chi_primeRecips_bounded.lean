import Mathlib
import Submission.Work.BMF.Defs
import Submission.Commons.NumberTheory.DirichletCharacter.psiChi_uniform_bound_primitive
import Submission.Work.BMF.liouville.abel_sum_bound
import Submission.Work.BMF.liouville.primeSum_sub_vonMangoldtSum

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BMF.liouville

/-- `G c L n = exp (-(c * √(log n / L)))` is antitone on `n ≥ 1`. -/
private lemma weight_antitone (c L : ℝ) (hc : 0 < c) (hL : 0 < L) {n m : ℕ} (hn : 1 ≤ n) (hnm : n ≤ m) :
    Real.exp (-(c * Real.sqrt (Real.log (m:ℝ) / L))) ≤
      Real.exp (-(c * Real.sqrt (Real.log (n:ℝ) / L))) := by
  apply Real.exp_le_exp.mpr
  have hnpos : (0:ℝ) < (n:ℝ) := by exact_mod_cast hn
  have hnm' : (n:ℝ) ≤ (m:ℝ) := by exact_mod_cast hnm
  have hlog : Real.log (n:ℝ) ≤ Real.log (m:ℝ) := Real.log_le_log hnpos hnm'
  have hsqrt : Real.sqrt (Real.log (n:ℝ) / L) ≤ Real.sqrt (Real.log (m:ℝ) / L) :=
    Real.sqrt_le_sqrt (div_le_div_of_nonneg_right hlog hL.le)
  nlinarith [hsqrt, hc]

/-- The doubling step: `T (2M) ≤ T M + G M` for `M ≥ 1`. -/
private lemma weight_T_double (c L : ℝ) (hc : 0 < c) (hL : 0 < L) {M : ℕ} (hM : 1 ≤ M) :
    (∑ n ∈ Finset.Icc 1 (2*M), Real.exp (-(c * Real.sqrt (Real.log (n:ℝ) / L))) / (n:ℝ))
      ≤ (∑ n ∈ Finset.Icc 1 M, Real.exp (-(c * Real.sqrt (Real.log (n:ℝ) / L))) / (n:ℝ))
        + Real.exp (-(c * Real.sqrt (Real.log (M:ℝ) / L))) := by
  have hsplit : Finset.Icc 1 (2*M) = Finset.Icc 1 M ∪ Finset.Icc (M+1) (2*M) := by
    ext x; simp only [Finset.mem_Icc, Finset.mem_union]; omega
  have hdisj : Disjoint (Finset.Icc 1 M) (Finset.Icc (M+1) (2*M)) := by
    rw [Finset.disjoint_left]
    intro x hx1 hx2
    rw [Finset.mem_Icc] at hx1 hx2
    omega
  rw [hsplit, Finset.sum_union hdisj]
  refine add_le_add le_rfl ?_
  have hcard : (Finset.Icc (M+1) (2*M)).card = M := by
    rw [Nat.card_Icc]; omega
  calc ∑ n ∈ Finset.Icc (M+1) (2*M), Real.exp (-(c * Real.sqrt (Real.log (n:ℝ) / L))) / (n:ℝ)
      ≤ ∑ n ∈ Finset.Icc (M+1) (2*M),
          Real.exp (-(c * Real.sqrt (Real.log (M:ℝ) / L))) / (M:ℝ) := by
        apply Finset.sum_le_sum
        intro n hn
        rw [Finset.mem_Icc] at hn
        have h1 : Real.exp (-(c * Real.sqrt (Real.log (n:ℝ) / L))) ≤
            Real.exp (-(c * Real.sqrt (Real.log (M:ℝ) / L))) :=
          weight_antitone c L hc hL hM (by omega)
        have hMpos : (0:ℝ) < (M:ℝ) := by exact_mod_cast (by omega : 0 < M)
        have h2 : ((n:ℝ))⁻¹ ≤ ((M:ℝ))⁻¹ := inv_anti₀ hMpos (by exact_mod_cast (by omega : M ≤ n))
        rw [div_eq_mul_inv, div_eq_mul_inv]
        exact mul_le_mul h1 h2 (by positivity) (Real.exp_pos _).le
    _ = (Finset.Icc (M+1) (2*M)).card *
          (Real.exp (-(c * Real.sqrt (Real.log (M:ℝ) / L))) / (M:ℝ)) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ = Real.exp (-(c * Real.sqrt (Real.log (M:ℝ) / L))) := by
        rw [hcard]
        have hMpos : (0:ℝ) < (M:ℝ) := by exact_mod_cast (by omega : 0 < M)
        field_simp

/-- `T (2^k) ≤ 1 + ∑_{i < k} G (2^i)`. -/
private lemma weight_T_pow (c L : ℝ) (hc : 0 < c) (hL : 0 < L) (k : ℕ) :
    (∑ n ∈ (Finset.Icc 1 (2^k) : Finset ℕ),
        Real.exp (-(c * Real.sqrt (Real.log (n:ℝ) / L))) / (n:ℝ))
      ≤ 1 + ∑ i ∈ Finset.range k,
          Real.exp (-(c * Real.sqrt (Real.log (((2:ℕ)^i:ℝ)) / L))) := by
  induction k with
  | zero => simp
  | succ k ih =>
      have h2 : (2:ℕ)^(k+1) = 2 * 2^k := by ring
      conv_lhs => rw [h2]
      have h1 : 1 ≤ (2:ℕ)^k := by
        have h : 0 < (2:ℕ)^k := pow_pos (by norm_num) k
        omega
      refine le_trans (weight_T_double c L hc hL h1) ?_
      rw [Finset.sum_range_succ]
      simp only [Nat.cast_pow]
      linarith

/-- The factorial trick: `G (2^i) ≤ 24/(α^4 i^2)` with `α = c √(log 2 / L)`, for `i ≥ 1`. -/
private lemma weight_pow_two_decay (c L : ℝ) (hc : 0 < c) (hL : 0 < L) (i : ℕ) (hi : 1 ≤ i) :
    Real.exp (-(c * Real.sqrt (Real.log (((2:ℕ)^i:ℝ)) / L)))
      ≤ 24 / ((c * Real.sqrt (Real.log 2 / L))^4 * (i:ℝ)^2) := by
  set α : ℝ := c * Real.sqrt (Real.log 2 / L) with hαdef
  have hαpos : 0 < α := by
    rw [hαdef]
    exact mul_pos hc (Real.sqrt_pos.mpr (div_pos (Real.log_pos (by norm_num)) hL))
  have h2i : (((2:ℕ)^i:ℝ)) = (2:ℝ)^i := by push_cast; ring
  have hlog : Real.log (((2:ℕ)^i:ℝ)) = (i:ℝ) * Real.log 2 := by
    rw [h2i, Real.log_pow]
  have hsqrt : Real.sqrt (Real.log (((2:ℕ)^i:ℝ)) / L) =
      Real.sqrt (i:ℝ) * Real.sqrt (Real.log 2 / L) := by
    rw [hlog, show (i:ℝ) * Real.log 2 / L = (i:ℝ) * (Real.log 2 / L) by ring,
      Real.sqrt_mul (by positivity)]
  rw [hsqrt]
  have harg : c * (Real.sqrt (i:ℝ) * Real.sqrt (Real.log 2 / L)) = α * Real.sqrt (i:ℝ) := by
    rw [hαdef]; ring
  rw [harg]
  have hipos : (0:ℝ) < (i:ℝ) := by exact_mod_cast (by omega : 0 < i)
  have hsipos : 0 < Real.sqrt (i:ℝ) := Real.sqrt_pos.mpr hipos
  have hkey := Real.pow_div_factorial_le_exp (α * Real.sqrt (i:ℝ)) (by positivity) 4
  have h4 : (4:ℕ).factorial = 24 := by norm_num
  rw [h4] at hkey
  have hpos4 : 0 < (α * Real.sqrt (i:ℝ))^4 / 24 := by positivity
  have hstep : Real.exp (-(α * Real.sqrt (i:ℝ))) ≤ ((α * Real.sqrt (i:ℝ))^4 / 24)⁻¹ := by
    rw [Real.exp_neg]
    exact (inv_le_inv₀ (Real.exp_pos _) hpos4).mpr hkey
  have hpow : (α * Real.sqrt (i:ℝ))^4 = α^4 * (i:ℝ)^2 := by
    rw [mul_pow]
    congr 1
    have h1 : (Real.sqrt (i:ℝ))^2 = (i:ℝ) := Real.sq_sqrt (le_of_lt hipos)
    have h2 : (Real.sqrt (i:ℝ))^4 = ((Real.sqrt (i:ℝ))^2)^2 := by ring
    rw [h2, h1]
  calc Real.exp (-(α * Real.sqrt (i:ℝ))) ≤ ((α * Real.sqrt (i:ℝ))^4 / 24)⁻¹ := hstep
    _ = 24 / (α * Real.sqrt (i:ℝ))^4 := by rw [inv_div]
    _ = 24 / (α^4 * (i:ℝ)^2) := by rw [hpow]

/-- `∑_{i ∈ Icc 1 K} 1/i^2 ≤ 2`. -/
private lemma inv_sq_sum_le_two (K : ℕ) :
    ∑ i ∈ Finset.Icc 1 K, ((i:ℝ))⁻¹ ^ 2 ≤ 2 := by
  rcases Nat.eq_zero_or_pos K with hK | hK
  · subst hK
    have hempty : Finset.Icc 1 0 = ∅ := by rw [Finset.Icc_eq_empty_iff]; omega
    rw [hempty, Finset.sum_empty]; norm_num
  · have htel : ∑ i ∈ Finset.Icc 1 K, (((i:ℝ))⁻¹ - (((i+1:ℕ):ℝ))⁻¹)
        = 1 - (((K+1:ℕ):ℝ))⁻¹ := by
      have h1 : ∑ i ∈ Finset.Icc 1 K, (((i:ℝ))⁻¹ - (((i+1:ℕ):ℝ))⁻¹)
          = -(((K+1:ℕ):ℝ))⁻¹ - (-(((1:ℕ):ℝ))⁻¹) := by
        have h := Finset.sum_Icc_sub (f := fun n : ℕ => -(((n:ℝ))⁻¹)) hK
        rw [← h]
        apply Finset.sum_congr rfl
        intro i hi
        ring
      rw [h1]
      ring_nf
    calc ∑ i ∈ Finset.Icc 1 K, ((i:ℝ))⁻¹ ^ 2
        ≤ ∑ i ∈ Finset.Icc 1 K, 2 * (((i:ℝ))⁻¹ - (((i+1:ℕ):ℝ))⁻¹) := by
          apply Finset.sum_le_sum
          intro i hi
          rw [Finset.mem_Icc] at hi
          have hi1 : (1:ℝ) ≤ (i:ℝ) := by exact_mod_cast hi.1
          have hipos : (0:ℝ) < (i:ℝ) := by linarith
          have hcast : (((i+1:ℕ):ℝ)) = (i:ℝ) + 1 := by push_cast; ring
          rw [hcast]
          have hkey : ((i:ℝ))⁻¹ ^ 2 ≤ 2 * ((i:ℝ)⁻¹ - ((i:ℝ)+1)⁻¹) := by
            rw [show 2 * ((i:ℝ)⁻¹ - ((i:ℝ)+1)⁻¹) = 2 * (1/(i:ℝ) - 1/((i:ℝ)+1)) by rw [one_div, one_div]]
            field_simp
            nlinarith [hi1]
          exact hkey
      _ = 2 * ∑ i ∈ Finset.Icc 1 K, (((i:ℝ))⁻¹ - (((i+1:ℕ):ℝ))⁻¹) := by
          rw [Finset.mul_sum]
      _ = 2 * (1 - (((K+1:ℕ):ℝ))⁻¹) := by rw [htel]
      _ ≤ 2 := by
          have : 0 ≤ (((K+1:ℕ):ℝ))⁻¹ := by positivity
          linarith

/-- `∑_{i < k} G (2^i) ≤ 2 + 48/α^4`. -/
private lemma weight_sum_range_bound (c L : ℝ) (hc : 0 < c) (hL : 0 < L) (k : ℕ) :
    ∑ i ∈ Finset.range k, Real.exp (-(c * Real.sqrt (Real.log (((2:ℕ)^i:ℝ)) / L)))
      ≤ 2 + 48 / (c * Real.sqrt (Real.log 2 / L))^4 := by
  set α : ℝ := c * Real.sqrt (Real.log 2 / L) with hαdef
  have hαpos : 0 < α := by
    rw [hαdef]
    exact mul_pos hc (Real.sqrt_pos.mpr (div_pos (Real.log_pos (by norm_num)) hL))
  rcases Nat.eq_zero_or_pos k with hk | hk
  · subst hk
    rw [Finset.range_zero, Finset.sum_empty]
    have : 0 < 48 / α^4 := by positivity
    linarith
  · have hsplit : Finset.range k = insert 0 (Finset.Icc 1 (k-1)) := by
      ext x; simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Icc]; omega
    rw [hsplit, Finset.sum_insert (by simp)]
    have h0 : Real.exp (-(c * Real.sqrt (Real.log (((2:ℕ)^0:ℝ)) / L))) = 1 := by
      norm_num
    rw [h0]
    have hrest : ∑ i ∈ Finset.Icc 1 (k-1),
          Real.exp (-(c * Real.sqrt (Real.log (((2:ℕ)^i:ℝ)) / L)))
        ≤ ∑ i ∈ Finset.Icc 1 (k-1), 24 / (α^4 * (i:ℝ)^2) := by
      apply Finset.sum_le_sum
      intro i hi
      rw [Finset.mem_Icc] at hi
      exact weight_pow_two_decay c L hc hL i hi.1
    refine le_trans (add_le_add le_rfl hrest) ?_
    have hrewrite : ∑ i ∈ Finset.Icc 1 (k-1), 24 / (α^4 * (i:ℝ)^2)
        = (24 / α^4) * ∑ i ∈ Finset.Icc 1 (k-1), ((i:ℝ))⁻¹ ^ 2 := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      field_simp
    rw [hrewrite]
    have hnn : 0 ≤ 24 / α^4 := by positivity
    calc 1 + (24 / α^4) * ∑ i ∈ Finset.Icc 1 (k-1), ((i:ℝ))⁻¹ ^ 2
        ≤ 1 + (24 / α^4) * 2 := by
          linarith [mul_le_mul_of_nonneg_left (inv_sq_sum_le_two (k-1)) hnn]
      _ = 1 + 48 / α^4 := by ring
      _ ≤ 2 + 48 / α^4 := by linarith

/-- For `c, L > 0`, the partial sums of `n ↦ exp (-(c * √(log n / L))) / n` are bounded. -/
theorem exp_weight_sum_bound_selfcontained (c L : ℝ) (hc : 0 < c) (hL : 0 < L) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ M : ℕ,
      ∑ n ∈ Finset.Icc 1 M, Real.exp (-(c * Real.sqrt (Real.log (n:ℝ) / L))) / (n:ℝ) ≤ K := by
  set α : ℝ := c * Real.sqrt (Real.log 2 / L) with hαdef
  have hαpos : 0 < α := by
    rw [hαdef]
    exact mul_pos hc (Real.sqrt_pos.mpr (div_pos (Real.log_pos (by norm_num)) hL))
  refine ⟨3 + 48 / α^4, by positivity, fun M => ?_⟩
  have hM2 : M ≤ 2^M := by
    induction M with
    | zero => simp
    | succ m ih =>
        rw [pow_succ]
        have h1 : 1 ≤ (2:ℕ)^m := by
          have h : 0 < (2:ℕ)^m := pow_pos (by norm_num) m
          omega
        nlinarith
  have hmono : (∑ n ∈ Finset.Icc 1 M, Real.exp (-(c * Real.sqrt (Real.log (n:ℝ) / L))) / (n:ℝ))
      ≤ ∑ n ∈ (Finset.Icc 1 (2^M) : Finset ℕ),
          Real.exp (-(c * Real.sqrt (Real.log (n:ℝ) / L))) / (n:ℝ) := by
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro x hx
      rw [Finset.mem_Icc] at hx ⊢
      exact ⟨hx.1, le_trans hx.2 hM2⟩
    · intro x hx _
      exact div_nonneg (Real.exp_pos _).le (by positivity)
  refine le_trans hmono ?_
  refine le_trans (weight_T_pow c L hc hL M) ?_
  have hb := weight_sum_range_bound c L hc hL M
  rw [← hαdef] at hb
  linarith

/-- The ground bound: for a primitive nonprincipal `ψ`, the prefix sums of `ψ · Λ` grow at most
like `B · n · exp (-(c √(log n / L)))`. -/
theorem vonMangoldt_chi_prefix_bound {d : ℕ} [NeZero d] {ψ : DirichletCharacter ℂ d}
    (hψ : ψ ≠ 1) (hprim : ψ.IsPrimitive) :
    ∃ (B c L : ℝ), 0 ≤ B ∧ 0 < c ∧ 0 < L ∧
      ∀ n : ℕ, 1 ≤ n →
        ‖∑ k ∈ Finset.Icc 1 n, ψ k * ((ArithmeticFunction.vonMangoldt k : ℝ) : ℂ)‖
          ≤ B * (n:ℝ) * Real.exp (-(c * Real.sqrt (Real.log (n:ℝ) / L))) := by
  obtain ⟨c, C, hc, hC, x₀, hbound⟩ :=
    Commons.NumberTheory.DirichletCharacter.psiChi_uniform_bound_primitive 2 (by norm_num)
  set L : ℝ := Real.log ((d:ℝ) + 2) with hLdef
  have hLpos : 0 < L := by
    rw [hLdef]
    apply Real.log_pos
    have : (0:ℝ) ≤ (d:ℝ) := Nat.cast_nonneg d
    linarith
  set Y : ℝ := max x₀ (Real.exp (max ((d:ℝ)) 1)) with hYdef
  set X : ℕ := ⌈Y⌉₊ + 3 with hXdef
  have hYX : Y ≤ (X:ℝ) := by
    have h1 : Y ≤ (⌈Y⌉₊ : ℝ) := Nat.le_ceil Y
    have h2 : ((⌈Y⌉₊ : ℕ) : ℝ) ≤ (X:ℝ) := by
      rw [hXdef]; push_cast; linarith
    linarith
  have hXpos : (0:ℝ) < (X:ℝ) := by
    have h3 : (3:ℝ) ≤ (X:ℝ) := by rw [hXdef]; push_cast; exact le_add_of_nonneg_left (Nat.cast_nonneg _)
    linarith
  have hx0X : x₀ ≤ (X:ℝ) := le_trans (le_max_left _ _) hYX
  have hdx : max ((d:ℝ)) 1 ≤ Real.log (X:ℝ) :=
    (Real.le_log_iff_exp_le hXpos).mpr (le_trans (le_max_right _ _) hYX)
  set B : ℝ := max C (Real.log (X:ℝ) * Real.exp (c * Real.sqrt (Real.log (X:ℝ) / L))) with hBdef
  have hBnn : 0 ≤ B := by rw [hBdef]; exact le_trans hC.le (le_max_left _ _)
  refine ⟨B, c, L, hBnn, hc, hLpos, ?_⟩
  intro n hn
  have hn1R : (1:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn
  have hnposR : (0:ℝ) < (n:ℝ) := by linarith
  rcases le_or_gt n X with hnX | hnX
  · have hlog_mono : Real.log (n:ℝ) ≤ Real.log (X:ℝ) :=
      Real.log_le_log hnposR (by exact_mod_cast hnX)
    have hG_le : Real.exp (-(c * Real.sqrt (Real.log (X:ℝ) / L))) ≤
        Real.exp (-(c * Real.sqrt (Real.log (n:ℝ) / L))) := by
      apply Real.exp_le_exp.mpr
      have h4 : Real.sqrt (Real.log (n:ℝ) / L) ≤ Real.sqrt (Real.log (X:ℝ) / L) :=
        Real.sqrt_le_sqrt (div_le_div_of_nonneg_right hlog_mono hLpos.le)
      nlinarith [h4, hc]
    have hBX : Real.log (X:ℝ) ≤ B * Real.exp (-(c * Real.sqrt (Real.log (n:ℝ) / L))) := by
      have h1 : Real.log (X:ℝ) * Real.exp (c * Real.sqrt (Real.log (X:ℝ) / L)) ≤ B := by
        rw [hBdef]; exact le_max_right _ _
      calc Real.log (X:ℝ)
          = Real.log (X:ℝ) * Real.exp (c * Real.sqrt (Real.log (X:ℝ) / L)) *
              Real.exp (-(c * Real.sqrt (Real.log (X:ℝ) / L))) := by
              rw [mul_assoc, ← Real.exp_add, add_neg_cancel, Real.exp_zero, mul_one]
        _ ≤ B * Real.exp (-(c * Real.sqrt (Real.log (X:ℝ) / L))) :=
              mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le
        _ ≤ B * Real.exp (-(c * Real.sqrt (Real.log (n:ℝ) / L))) :=
              mul_le_mul_of_nonneg_left hG_le hBnn
    have hsum : ‖∑ k ∈ Finset.Icc 1 n, ψ k * ((ArithmeticFunction.vonMangoldt k : ℝ) : ℂ)‖
        ≤ (n:ℝ) * Real.log (n:ℝ) := by
      calc ‖∑ k ∈ Finset.Icc 1 n, ψ k * ((ArithmeticFunction.vonMangoldt k : ℝ) : ℂ)‖
          ≤ ∑ k ∈ Finset.Icc 1 n, (ArithmeticFunction.vonMangoldt k : ℝ) := by
            refine le_trans (norm_sum_le _ _) (Finset.sum_le_sum ?_)
            intro k hk
            rw [norm_mul]
            have h1 : ‖ψ k‖ ≤ 1 := DirichletCharacter.norm_le_one ψ _
            have h2 : ‖((ArithmeticFunction.vonMangoldt k : ℝ) : ℂ)‖ =
                (ArithmeticFunction.vonMangoldt k : ℝ) := by
              rw [Complex.norm_real, Real.norm_eq_abs,
                abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
            rw [h2]
            exact mul_le_of_le_one_left ArithmeticFunction.vonMangoldt_nonneg h1
        _ ≤ ∑ k ∈ Finset.Icc 1 n, Real.log (n:ℝ) := by
              apply Finset.sum_le_sum
              intro k hk
              rw [Finset.mem_Icc] at hk
              exact le_trans ArithmeticFunction.vonMangoldt_le_log
                (Real.log_le_log (by exact_mod_cast hk.1) (by exact_mod_cast hk.2))
        _ = ((Finset.Icc 1 n).card : ℝ) * Real.log (n:ℝ) := by rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ (n:ℝ) * Real.log (n:ℝ) := by
              apply mul_le_mul_of_nonneg_right _ (Real.log_nonneg hn1R)
              have hcard : ((Finset.Icc 1 n).card : ℝ) ≤ (n:ℝ) := by
                have h2 : (Finset.Icc 1 n).card = n := by
                  rw [Nat.card_Icc]; omega
                rw [h2]
              exact hcard
    calc ‖∑ k ∈ Finset.Icc 1 n, ψ k * ((ArithmeticFunction.vonMangoldt k : ℝ) : ℂ)‖
        ≤ (n:ℝ) * Real.log (n:ℝ) := hsum
      _ ≤ (n:ℝ) * Real.log (X:ℝ) := mul_le_mul_of_nonneg_left hlog_mono hnposR.le
      _ ≤ (n:ℝ) * (B * Real.exp (-(c * Real.sqrt (Real.log (n:ℝ) / L)))) :=
            mul_le_mul_of_nonneg_left hBX hnposR.le
      _ = B * (n:ℝ) * Real.exp (-(c * Real.sqrt (Real.log (n:ℝ) / L))) := by ring
  · have hx₀ : x₀ ≤ (n:ℝ) := le_trans hx0X (by exact_mod_cast le_of_lt hnX)
    have hlogXn : max ((d:ℝ)) 1 ≤ Real.log (n:ℝ) :=
      le_trans hdx (Real.log_le_log (by linarith) (by exact_mod_cast le_of_lt hnX))
    have hdn : (d:ℝ) ≤ (Real.log (n:ℝ)) ^ (2:ℝ) := by
      have h1 : (1:ℝ) ≤ Real.log (n:ℝ) := le_trans (le_max_right _ _) hlogXn
      rw [show (2:ℝ) = ((2:ℕ):ℝ) by norm_num, Real.rpow_natCast]
      calc (d:ℝ) ≤ Real.log (n:ℝ) := le_trans (le_max_left _ _) hlogXn
        _ = (Real.log (n:ℝ))^1 := (pow_one _).symm
        _ ≤ (Real.log (n:ℝ))^2 := pow_le_pow_right₀ h1 (by norm_num)
    have hb := hbound (n:ℝ) hx₀ d ψ hψ hprim hdn
    rw [Nat.floor_natCast] at hb
    have hb2 : ‖∑ k ∈ Finset.Icc 1 n, ψ k * ((ArithmeticFunction.vonMangoldt k : ℝ) : ℂ)‖ ≤
        C * (n:ℝ) * Real.exp (-(c * Real.sqrt (Real.log (n:ℝ) / L))) := by
      simpa only [hLdef] using hb
    calc ‖∑ k ∈ Finset.Icc 1 n, ψ k * ((ArithmeticFunction.vonMangoldt k : ℝ) : ℂ)‖
        ≤ C * (n:ℝ) * Real.exp (-(c * Real.sqrt (Real.log (n:ℝ) / L))) := hb2
      _ ≤ B * (n:ℝ) * Real.exp (-(c * Real.sqrt (Real.log (n:ℝ) / L))) := by
            have hCB : C ≤ B := by rw [hBdef]; exact le_max_left _ _
            have hpos : (0:ℝ) ≤ Real.exp (-(c * Real.sqrt (Real.log (n:ℝ) / L))) :=
              (Real.exp_pos _).le
            calc C * (n:ℝ) * Real.exp (-(c * Real.sqrt (Real.log (n:ℝ) / L)))
                = ((n:ℝ) * Real.exp (-(c * Real.sqrt (Real.log (n:ℝ) / L)))) * C := by ring
              _ ≤ ((n:ℝ) * Real.exp (-(c * Real.sqrt (Real.log (n:ℝ) / L)))) * B :=
                    mul_le_mul_of_nonneg_left hCB (mul_nonneg hnposR.le hpos)
              _ = B * (n:ℝ) * Real.exp (-(c * Real.sqrt (Real.log (n:ℝ) / L))) := by ring


/-- Abel summation + the weight estimate: if the prefix sums of `a` grow like `B · n · G n`,
then `∑ a n / n` has bounded partial sums. -/
theorem abel_recip_bound {a : ℕ → ℂ} {B c L : ℝ} (hB : 0 ≤ B) (hc : 0 < c) (hL : 0 < L)
    (h : ∀ n : ℕ, 1 ≤ n → ‖∑ k ∈ Finset.Icc 1 n, a k‖ ≤
      B * (n:ℝ) * Real.exp (-(c * Real.sqrt (Real.log (n:ℝ) / L)))) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ M : ℕ, ‖∑ n ∈ Finset.Icc 1 M, a n / (n:ℂ)‖ ≤ K := by
  obtain ⟨K₀, hK₀nn, hK₀⟩ := exp_weight_sum_bound_selfcontained c L hc hL
  refine ⟨B * (1 + K₀), mul_nonneg hB (by linarith), fun M => ?_⟩
  rcases Nat.eq_zero_or_pos M with hM0 | hMpos
  · subst hM0
    have hempty : Finset.Icc 1 0 = ∅ := by rw [Finset.Icc_eq_empty_iff]; omega
    rw [hempty, Finset.sum_empty, norm_zero]
    exact mul_nonneg hB (by linarith)
  · have hgoal : (∑ n ∈ Finset.Icc 1 M, a n / (n:ℂ)) = ∑ n ∈ Finset.Icc 1 M, a n * ((n:ℂ))⁻¹ := by
      apply Finset.sum_congr rfl
      intro n hn
      rw [div_eq_mul_inv]
    rw [hgoal]
    have hb : ‖∑ n ∈ Finset.Icc 1 M, a n * ((n:ℂ))⁻¹‖ ≤
        B * (M:ℝ) * Real.exp (-(c * Real.sqrt (Real.log (M:ℝ) / L))) * ‖((M:ℂ))⁻¹‖ +
        ∑ n ∈ Finset.Icc 1 (M - 1), B * (n:ℝ) * Real.exp (-(c * Real.sqrt (Real.log (n:ℝ) / L))) *
          ‖((n:ℂ))⁻¹ - (((n+1:ℕ):ℂ))⁻¹‖ :=
      abel_sum_bound a (fun n => ((n:ℂ))⁻¹)
        (fun n => B * (n:ℝ) * Real.exp (-(c * Real.sqrt (Real.log (n:ℝ) / L))))
        (le_refl 1) hMpos (fun n hn _ => h n hn)
    have hterm1 : B * (M:ℝ) * Real.exp (-(c * Real.sqrt (Real.log (M:ℝ) / L))) *
        ‖((M:ℂ))⁻¹‖ ≤ B := by
      have hMr : (0:ℝ) < (M:ℝ) := by exact_mod_cast hMpos
      have hnorm : ‖((M:ℂ))⁻¹‖ = ((M:ℝ))⁻¹ := by
        rw [norm_inv, Complex.norm_natCast]
      rw [hnorm]
      have hexp : Real.exp (-(c * Real.sqrt (Real.log (M:ℝ) / L))) ≤ 1 := by
        rw [Real.exp_le_one_iff]
        have : 0 ≤ c * Real.sqrt (Real.log (M:ℝ) / L) :=
          mul_nonneg hc.le (Real.sqrt_nonneg _)
        linarith
      calc B * (M:ℝ) * Real.exp (-(c * Real.sqrt (Real.log (M:ℝ) / L))) * (M:ℝ)⁻¹
          = B * Real.exp (-(c * Real.sqrt (Real.log (M:ℝ) / L))) := by field_simp
        _ ≤ B * 1 := mul_le_mul_of_nonneg_left hexp hB
        _ = B := mul_one B
    have hstep : ∀ n ∈ Finset.Icc 1 (M - 1), B * (n:ℝ) *
        Real.exp (-(c * Real.sqrt (Real.log (n:ℝ) / L))) * ‖((n:ℂ))⁻¹ - (((n+1:ℕ):ℂ))⁻¹‖
          ≤ B * (Real.exp (-(c * Real.sqrt (Real.log (n:ℝ) / L))) / (n:ℝ)) := by
      intro n hn
      rw [Finset.mem_Icc] at hn
      have hn1 : 1 ≤ n := hn.1
      have hnpos : (0:ℝ) < (n:ℝ) := by exact_mod_cast hn1
      have hreal : (((n:ℝ)⁻¹ - ((n:ℝ)+1)⁻¹ : ℝ) : ℂ) = ((n:ℂ))⁻¹ - (((n+1:ℕ):ℂ))⁻¹ := by
        rw [Complex.ofReal_sub, Complex.ofReal_inv, Complex.ofReal_inv, Complex.ofReal_add,
          Complex.ofReal_one, Complex.ofReal_natCast, Nat.cast_add, Nat.cast_one]
      have hnorm : ‖((n:ℂ))⁻¹ - (((n+1:ℕ):ℂ))⁻¹‖ = ((n:ℝ)⁻¹ - ((n:ℝ)+1)⁻¹) := by
        rw [← hreal, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg]
        have h1 : ((n:ℝ)+1)⁻¹ ≤ (n:ℝ)⁻¹ := by
          have h2 : (1:ℝ) / ((n:ℝ)+1) ≤ 1 / (n:ℝ) :=
            one_div_le_one_div_of_le hnpos (by linarith)
          simpa [one_div] using h2
        linarith
      rw [hnorm]
      have hkey : (n:ℝ) * ((n:ℝ)⁻¹ - ((n:ℝ)+1)⁻¹) = ((n:ℝ)+1)⁻¹ := by
        field_simp
        push_cast
        ring
      have h1 : ((n:ℝ)+1)⁻¹ ≤ (n:ℝ)⁻¹ := by
        have h2 : (1:ℝ) / ((n:ℝ)+1) ≤ 1 / (n:ℝ) :=
          one_div_le_one_div_of_le hnpos (by linarith)
        simpa [one_div] using h2
      have h2 : 0 ≤ B * Real.exp (-(c * Real.sqrt (Real.log (n:ℝ) / L))) :=
        mul_nonneg hB (Real.exp_pos _).le
      calc B * (n:ℝ) * Real.exp (-(c * Real.sqrt (Real.log (n:ℝ) / L))) *
              ((n:ℝ)⁻¹ - ((n:ℝ)+1)⁻¹)
          = (B * Real.exp (-(c * Real.sqrt (Real.log (n:ℝ) / L)))) *
              ((n:ℝ) * ((n:ℝ)⁻¹ - ((n:ℝ)+1)⁻¹)) := by ring
        _ = (B * Real.exp (-(c * Real.sqrt (Real.log (n:ℝ) / L)))) * ((n:ℝ)+1)⁻¹ := by rw [hkey]
        _ ≤ (B * Real.exp (-(c * Real.sqrt (Real.log (n:ℝ) / L)))) * (n:ℝ)⁻¹ :=
              mul_le_mul_of_nonneg_left h1 h2
        _ = B * (Real.exp (-(c * Real.sqrt (Real.log (n:ℝ) / L))) / (n:ℝ)) := by ring
    have hterm2 : (∑ n ∈ Finset.Icc 1 (M - 1), B * (n:ℝ) *
        Real.exp (-(c * Real.sqrt (Real.log (n:ℝ) / L))) * ‖((n:ℂ))⁻¹ - (((n+1:ℕ):ℂ))⁻¹‖)
          ≤ B * K₀ := by
      calc (∑ n ∈ Finset.Icc 1 (M - 1), B * (n:ℝ) *
            Real.exp (-(c * Real.sqrt (Real.log (n:ℝ) / L))) * ‖((n:ℂ))⁻¹ - (((n+1:ℕ):ℂ))⁻¹‖)
          ≤ ∑ n ∈ Finset.Icc 1 (M - 1),
              B * (Real.exp (-(c * Real.sqrt (Real.log (n:ℝ) / L))) / (n:ℝ)) :=
            Finset.sum_le_sum hstep
        _ = B * ∑ n ∈ Finset.Icc 1 (M - 1),
              Real.exp (-(c * Real.sqrt (Real.log (n:ℝ) / L))) / (n:ℝ) := by
            rw [Finset.mul_sum]
        _ ≤ B * ∑ n ∈ Finset.Icc 1 M,
              Real.exp (-(c * Real.sqrt (Real.log (n:ℝ) / L))) / (n:ℝ) := by
            apply mul_le_mul_of_nonneg_left _ hB
            apply Finset.sum_le_sum_of_subset_of_nonneg
            · intro x hx; rw [Finset.mem_Icc] at hx ⊢; omega
            · intro x hx _; positivity
        _ ≤ B * K₀ := mul_le_mul_of_nonneg_left (hK₀ M) hB
    calc ‖∑ n ∈ Finset.Icc 1 M, a n * ((n:ℂ))⁻¹‖
        ≤ B * (M:ℝ) * Real.exp (-(c * Real.sqrt (Real.log (M:ℝ) / L))) * ‖((M:ℂ))⁻¹‖
          + ∑ n ∈ Finset.Icc 1 (M - 1), B * (n:ℝ) *
              Real.exp (-(c * Real.sqrt (Real.log (n:ℝ) / L))) *
              ‖((n:ℂ))⁻¹ - (((n+1:ℕ):ℂ))⁻¹‖ := hb
      _ ≤ B + B * K₀ := add_le_add hterm1 hterm2
      _ = B * (1 + K₀) := by ring

/-- Telescoping bound for the logarithmic weight differences. -/
private lemma log_inv_telescope (K : ℕ) :
    ∑ n ∈ Finset.Icc 2 (K - 1), ((Real.log (n:ℝ))⁻¹ - (Real.log ((n:ℝ)+1))⁻¹)
      ≤ (Real.log 2)⁻¹ := by
  rcases le_or_gt K 2 with hK | hK
  · have hempty : Finset.Icc 2 (K - 1) = ∅ := by
      rw [Finset.Icc_eq_empty_iff]; omega
    rw [hempty, Finset.sum_empty]
    exact le_of_lt (inv_pos.mpr (Real.log_pos (by norm_num)))
  · have h2K : 2 ≤ K - 1 := by omega
    have h1 : ∑ n ∈ Finset.Icc 2 (K - 1), ((Real.log (n:ℝ))⁻¹ - (Real.log ((n:ℝ)+1))⁻¹)
        = (Real.log 2)⁻¹ - (Real.log (K:ℝ))⁻¹ := by
      have htel := Finset.sum_Icc_sub (f := fun n : ℕ => (Real.log (n:ℝ))⁻¹) h2K
      rw [show (K - 1) + 1 = K from by omega] at htel
      simp only [Nat.cast_add, Nat.cast_one] at htel
      have h2 : ∑ n ∈ Finset.Icc 2 (K - 1), ((Real.log (n:ℝ))⁻¹ - (Real.log ((n:ℝ)+1))⁻¹)
          = -∑ n ∈ Finset.Icc 2 (K - 1),
              ((Real.log ((n:ℝ)+1))⁻¹ - (Real.log (n:ℝ))⁻¹) := by
        rw [← Finset.sum_neg_distrib]
        apply Finset.sum_congr rfl
        intro n hn
        ring
      rw [h2, htel]
      ring
    rw [h1]
    have hKn : 0 ≤ (Real.log (K:ℝ))⁻¹ :=
      inv_nonneg.mpr (Real.log_natCast_nonneg K)
    linarith

/-- Second summation by parts: the weight `1/log p` on the primes converts the bounded prime sum
`∑_{p ≤ M} ψ(p) log p / p` into the bounded prime sum `∑_{p ≤ M} ψ(p)/p`. -/
theorem prime_recip_of_prime_log_sum {d : ℕ} [NeZero d] (ψ : DirichletCharacter ℂ d) {B : ℝ}
    (hB : 0 ≤ B)
    (h : ∀ n : ℕ, 1 ≤ n →
      ‖∑ p ∈ n.primesLE, ψ p * ((Real.log (p:ℝ) : ℂ) / (p:ℂ))‖ ≤ B) :
    ∀ M : ℕ, ‖∑ p ∈ M.primesLE, ψ p / (p:ℂ)‖ ≤ B * (3 / Real.log 2) := by
  have hlog2 : (0:ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have htarget : (0:ℝ) ≤ B * (3 / Real.log 2) :=
    mul_nonneg hB (div_nonneg (by norm_num) hlog2.le)
  intro M
  rcases le_or_gt M 1 with hM1 | hM1
  · have hsum0 : (∑ p ∈ M.primesLE, ψ p / (p:ℂ)) = 0 := by
      apply Finset.sum_eq_zero
      intro p hp
      rw [Nat.mem_primesLE] at hp
      have := hp.2.two_le
      omega
    rw [hsum0, norm_zero]
    exact htarget
  · set a : ℕ → ℂ := fun n => if n.Prime then ψ n * ((Real.log (n:ℝ) : ℂ) / (n:ℂ)) else 0 with hadef
    set b : ℕ → ℂ := fun n => ((Real.log (n:ℝ) : ℂ))⁻¹ with hbdef
    have ha : ∀ n : ℕ, 1 ≤ n → ‖∑ k ∈ Finset.Icc 1 n, a k‖ ≤ B := by
      intro n hn
      have h1 : ∑ k ∈ Finset.Icc 1 n, a k
          = ∑ p ∈ n.primesLE, ψ p * ((Real.log (p:ℝ) : ℂ) / (p:ℂ)) := by
        rw [Nat.primesLE_eq_filter_Icc_one, Finset.sum_filter]
      rw [h1]; exact h n hn
    have hunf : ∀ n : ℕ, a n * b n = (if n.Prime then ψ n / (n:ℂ) else 0) := by
      intro n
      by_cases hn' : n.Prime
      · have hlog : (Real.log (n:ℝ) : ℂ) ≠ 0 := by
          have hlt : (0:ℝ) < Real.log (n:ℝ) := Real.log_pos (by exact_mod_cast hn'.one_lt)
          exact_mod_cast ne_of_gt hlt
        have hn0 : (n:ℂ) ≠ 0 := by
          have hlt : (0:ℝ) < (n:ℝ) := by exact_mod_cast hn'.pos
          exact_mod_cast ne_of_gt hlt
        simp only [hadef, hbdef, hn', if_true]
        field_simp
      · simp only [hadef, hbdef, hn', if_false, zero_mul]
    have hgoal : (∑ p ∈ M.primesLE, ψ p / (p:ℂ)) = ∑ n ∈ Finset.Icc 1 M, a n * b n := by
      rw [Nat.primesLE_eq_filter_Icc_one, Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro n hn
      rw [hunf n]
    have hbM : ‖b M‖ ≤ (Real.log 2)⁻¹ := by
      have hnorm : ‖b M‖ = ((Real.log (M:ℝ))⁻¹) := by
        simp only [hbdef]
        rw [norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.log_natCast_nonneg M)]
      rw [hnorm]
      have h2M : (2:ℝ) ≤ (M:ℝ) := by exact_mod_cast hM1
      have hle : (1:ℝ) / Real.log (M:ℝ) ≤ 1 / Real.log 2 :=
        one_div_le_one_div_of_le hlog2 (Real.log_le_log (by norm_num) h2M)
      simpa [one_div] using hle
    have hsplit : Finset.Icc 1 (M - 1) = insert 1 (Finset.Icc 2 (M - 1)) := by
      ext x; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
    have hb1 : b 1 = 0 := by simp [hbdef]
    have hb2 : b (1 + 1) = ((Real.log (2:ℝ) : ℂ))⁻¹ := by
      simp only [hbdef]
      norm_num
    have h1term : B * ‖b 1 - b (1 + 1)‖ = B * ((Real.log 2)⁻¹) := by
      have hbn : ‖b 1 - b (1 + 1)‖ = (Real.log 2)⁻¹ := by
        rw [hb1, hb2, zero_sub, norm_neg, norm_inv, Complex.norm_real, Real.norm_eq_abs,
          abs_of_pos hlog2]
      rw [hbn]
    have hstep : ∀ n ∈ Finset.Icc 2 (M - 1),
        ‖b n - b (n + 1)‖ ≤ ((Real.log (n:ℝ))⁻¹ - (Real.log ((n:ℝ)+1))⁻¹) := by
      intro n hn
      rw [Finset.mem_Icc] at hn
      have hn2 : 2 ≤ n := hn.1
      have hreal : (((Real.log (n:ℝ))⁻¹ - (Real.log ((n:ℝ)+1))⁻¹ : ℝ) : ℂ)
          = ((Real.log (n:ℝ) : ℂ))⁻¹ - ((Real.log (((n+1:ℕ):ℝ)) : ℂ))⁻¹ := by
        rw [Complex.ofReal_sub, Complex.ofReal_inv, Complex.ofReal_inv]
        congr 2
        push_cast
        ring
      have hunfb : b n - b (n + 1) = ((Real.log (n:ℝ) : ℂ))⁻¹ - ((Real.log (((n+1:ℕ):ℝ)) : ℂ))⁻¹ := by
        simp only [hbdef]
      have hnonneg : 0 ≤ ((Real.log (n:ℝ))⁻¹ - (Real.log ((n:ℝ)+1))⁻¹) := by
        have hnpos : (0:ℝ) < (n:ℝ) := by exact_mod_cast (by omega : 0 < n)
        have hlt : 0 < Real.log (n:ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < n))
        have h1 : ((Real.log ((n:ℝ)+1))⁻¹) ≤ ((Real.log (n:ℝ))⁻¹) := by
          have h2 : (1:ℝ) / Real.log ((n:ℝ)+1) ≤ 1 / Real.log (n:ℝ) :=
            one_div_le_one_div_of_le hlt (Real.log_le_log hnpos (by linarith))
          simpa [one_div] using h2
        exact sub_nonneg.mpr h1
      rw [hunfb, ← hreal, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hnonneg]
    have h2term : ∑ n ∈ Finset.Icc 2 (M - 1), B * ‖b n - b (n + 1)‖ ≤ B * ((Real.log 2)⁻¹) := by
      rw [← Finset.mul_sum]
      apply mul_le_mul_of_nonneg_left _ hB
      calc ∑ n ∈ Finset.Icc 2 (M - 1), ‖b n - b (n + 1)‖
          ≤ ∑ n ∈ Finset.Icc 2 (M - 1),
              ((Real.log (n:ℝ))⁻¹ - (Real.log ((n:ℝ)+1))⁻¹) := Finset.sum_le_sum hstep
        _ ≤ (Real.log 2)⁻¹ := log_inv_telescope M
    have hmain : ‖∑ n ∈ Finset.Icc 1 M, a n * b n‖ ≤ B * (3 / Real.log 2) := by
      have hb := abel_sum_bound (a := a) (b := b) (K := fun _ => B) (N := 1) (M := M)
        (le_refl 1) (by omega) (fun n hn _ => ha n hn)
      refine le_trans hb ?_
      rw [hsplit, Finset.sum_insert (by simp), h1term]
      calc B * ‖b M‖ + (B * ((Real.log 2)⁻¹) + ∑ n ∈ Finset.Icc 2 (M - 1), B * ‖b n - b (n + 1)‖)
          ≤ B * ((Real.log 2)⁻¹) + (B * ((Real.log 2)⁻¹) + B * ((Real.log 2)⁻¹)) :=
            add_le_add (mul_le_mul_of_nonneg_left hbM hB) (add_le_add le_rfl h2term)
        _ = B * (3 / Real.log 2) := by rw [div_eq_mul_inv]; ring
    rw [hgoal]
    exact hmain

/-- Reduction of an imprimitive character to its primitive counterpart, at the cost of an
additive constant depending on the level. -/
theorem imprimitive_reduction {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (M : ℕ) :
    ‖∑ p ∈ M.primesLE, (χ p : ℂ) / (p:ℂ)‖
      ≤ ‖∑ p ∈ M.primesLE, ((χ.primitiveCharacter) p : ℂ) / (p:ℂ)‖
        + ∑ p ∈ q.primesLE, 1 / (p:ℝ) := by
  have hpt : ∀ p ∈ M.primesLE,
      ‖(χ p : ℂ) / (p:ℂ) - ((χ.primitiveCharacter) p : ℂ) / (p:ℂ)‖
        ≤ (if p ∣ q then 1 / (p:ℝ) else 0) := by
    intro p hp
    rw [Nat.mem_primesLE] at hp
    obtain ⟨hpq, hpprime⟩ := hp
    by_cases hdiv : p ∣ q
    · rw [if_pos hdiv]
      have hzero : (χ (p : ZMod q)) = 0 := by
        have hcop : ¬ IsCoprime (p:ℤ) (q:ℤ) := by
          rw [Nat.isCoprime_iff_coprime]
          exact fun hc => (Nat.Prime.coprime_iff_not_dvd hpprime).mp hc hdiv
        simpa using (DirichletCharacter.apply_eq_zero_iff χ (p:ℤ)).mpr hcop
      rw [← sub_div, hzero, zero_sub, norm_div, norm_neg, Complex.norm_natCast]
      have h1 : ‖χ.primitiveCharacter (p : ZMod χ.conductor)‖ ≤ 1 :=
        DirichletCharacter.norm_le_one _ _
      exact (div_le_div_iff_of_pos_right (by exact_mod_cast hpprime.pos)).mpr h1
    · rw [if_neg hdiv]
      have hcop : IsCoprime (p:ℤ) (q:ℤ) := by
        rw [Nat.isCoprime_iff_coprime]
        exact (Nat.Prime.coprime_iff_not_dvd hpprime).mpr hdiv
      have heq : χ (p : ZMod q) = χ.primitiveCharacter (p : ZMod χ.conductor) := by
        have h2 := DirichletCharacter.primitiveCharacter_apply_of_isCoprime χ hcop
        simpa using h2.symm
      rw [heq, sub_self, norm_zero]
  have hsub : ‖(∑ p ∈ M.primesLE, (χ p : ℂ)/(p:ℂ)) - (∑ p ∈ M.primesLE, ((χ.primitiveCharacter) p : ℂ)/(p:ℂ))‖
      ≤ ∑ p ∈ q.primesLE, 1/(p:ℝ) := by
    rw [← Finset.sum_sub_distrib]
    calc ‖∑ p ∈ M.primesLE, ((χ p : ℂ)/(p:ℂ) - ((χ.primitiveCharacter) p : ℂ)/(p:ℂ))‖
        ≤ ∑ p ∈ M.primesLE, ‖(χ p : ℂ)/(p:ℂ) - ((χ.primitiveCharacter) p : ℂ)/(p:ℂ)‖ :=
          norm_sum_le _ _
      _ ≤ ∑ p ∈ M.primesLE, (if p ∣ q then 1/(p:ℝ) else 0) := Finset.sum_le_sum hpt
      _ = ∑ p ∈ M.primesLE.filter (fun p => p ∣ q), 1/(p:ℝ) := by
            rw [Finset.sum_filter]
      _ ≤ ∑ p ∈ q.primesLE, 1/(p:ℝ) := by
            apply Finset.sum_le_sum_of_subset_of_nonneg
            · intro x hx
              rw [Finset.mem_filter, Nat.mem_primesLE] at hx
              obtain ⟨⟨hxM, hxprime⟩, hxdvd⟩ := hx
              rw [Nat.mem_primesLE]
              exact ⟨Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne q)) hxdvd, hxprime⟩
            · intro x hx hxnot
              rw [Nat.mem_primesLE] at hx
              positivity
  calc ‖∑ p ∈ M.primesLE, (χ p : ℂ)/(p:ℂ)‖
      = ‖(∑ p ∈ M.primesLE, ((χ.primitiveCharacter) p : ℂ)/(p:ℂ)) +
          ((∑ p ∈ M.primesLE, (χ p : ℂ)/(p:ℂ)) - (∑ p ∈ M.primesLE, ((χ.primitiveCharacter) p : ℂ)/(p:ℂ)))‖ := by
        rw [add_sub_cancel]
    _ ≤ ‖∑ p ∈ M.primesLE, ((χ.primitiveCharacter) p : ℂ)/(p:ℂ)‖
        + ‖(∑ p ∈ M.primesLE, (χ p : ℂ)/(p:ℂ)) - (∑ p ∈ M.primesLE, ((χ.primitiveCharacter) p : ℂ)/(p:ℂ))‖ :=
        norm_add_le _ _
    _ ≤ ‖∑ p ∈ M.primesLE, ((χ.primitiveCharacter) p : ℂ)/(p:ℂ)‖ + ∑ p ∈ q.primesLE, 1/(p:ℝ) :=
        add_le_add le_rfl hsub


/-- For every nonprincipal Dirichlet character `χ` modulo `q`, the reciprocal prime sum
`∑_{p ≤ x} χ(p)/p` is bounded uniformly in `x`; the bound may depend on `q`.-/
theorem chi_primeRecips_bounded {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, 2 ≤ x →
      ‖∑ p ∈ (⌊x⌋₊).primesLE, (χ p : ℂ) / (p : ℂ)‖ ≤ C := by
  haveI hcond : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
  have hψne : χ.primitiveCharacter ≠ 1 := by
    intro h
    apply hχ
    rw [← DirichletCharacter.changeLevel_primitiveCharacter χ, h]
    exact map_one _
  obtain ⟨B, c, L, hB, hc, hL, hground⟩ :=
    vonMangoldt_chi_prefix_bound hψne χ.primitiveCharacter_isPrimitive
  obtain ⟨K₁, hK₁nn, hK₁⟩ := abel_recip_bound
    (a := fun n => χ.primitiveCharacter n * ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ))
    hB hc hL (fun n hn => hground n hn)
  set C₂ : ℝ := K₁ + B * (1 + K₁) + 2 with hC₂def
  have hBnn' : 0 ≤ B * (1 + K₁) := mul_nonneg hB (by linarith)
  have hC₂nn : 0 ≤ C₂ := by rw [hC₂def]; linarith
  have hK₁2 : K₁ + 2 ≤ C₂ := by rw [hC₂def]; linarith
  have hlogsum : ∀ M : ℕ, ‖∑ p ∈ M.primesLE, (χ.primitiveCharacter p : ℂ) *
      ((Real.log (p:ℝ) : ℂ) / (p:ℂ))‖ ≤ C₂ := by
    intro M
    have h1 := hK₁ M
    have h2 := primeSum_sub_vonMangoldtSum χ.conductor χ.primitiveCharacter M
    have hsplit : (∑ p ∈ M.primesLE, (χ.primitiveCharacter p : ℂ) * ((Real.log (p:ℝ) : ℂ) / (p:ℂ)))
        = (∑ n ∈ Finset.Icc 1 M, (χ.primitiveCharacter n : ℂ) *
              ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) / (n:ℂ))
          + ((∑ p ∈ M.primesLE, (χ.primitiveCharacter p : ℂ) * ((Real.log (p:ℝ) : ℂ) / (p:ℂ)))
              - (∑ n ∈ Finset.Icc 1 M, (χ.primitiveCharacter n : ℂ) *
                  ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) / (n:ℂ))) := by ring
    rw [hsplit]
    have h2' : ‖(∑ p ∈ M.primesLE, (χ.primitiveCharacter p : ℂ) * ((Real.log (p:ℝ) : ℂ) / (p:ℂ)))
        - (∑ n ∈ Finset.Icc 1 M, (χ.primitiveCharacter n : ℂ) *
            ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) / (n:ℂ))‖ ≤ 2 := h2
    calc ‖(∑ n ∈ Finset.Icc 1 M, (χ.primitiveCharacter n : ℂ) *
              ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) / (n:ℂ))
          + ((∑ p ∈ M.primesLE, (χ.primitiveCharacter p : ℂ) * ((Real.log (p:ℝ) : ℂ) / (p:ℂ)))
              - (∑ n ∈ Finset.Icc 1 M, (χ.primitiveCharacter n : ℂ) *
                  ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) / (n:ℂ)))‖
        ≤ ‖∑ n ∈ Finset.Icc 1 M, (χ.primitiveCharacter n : ℂ) *
              ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) / (n:ℂ)‖
          + ‖(∑ p ∈ M.primesLE, (χ.primitiveCharacter p : ℂ) * ((Real.log (p:ℝ) : ℂ) / (p:ℂ)))
              - (∑ n ∈ Finset.Icc 1 M, (χ.primitiveCharacter n : ℂ) *
                  ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) / (n:ℂ))‖ := norm_add_le _ _
      _ ≤ K₁ + 2 := add_le_add h1 h2'
      _ ≤ C₂ := hK₁2
  have hfin : ∀ M : ℕ, ‖∑ p ∈ M.primesLE, (χ.primitiveCharacter p : ℂ) / (p:ℂ)‖ ≤ C₂ * (3 / Real.log 2) :=
    prime_recip_of_prime_log_sum χ.primitiveCharacter hC₂nn (fun n _ => hlogsum n)
  refine ⟨C₂ * (3 / Real.log 2) + ∑ p ∈ q.primesLE, 1/(p:ℝ), ?_, fun x hx => ?_⟩
  · refine add_nonneg (mul_nonneg hC₂nn ?_) (Finset.sum_nonneg (fun p _ => by positivity))
    exact div_nonneg (by norm_num) (Real.log_pos (by norm_num)).le
  · have hr := imprimitive_reduction χ hχ (⌊x⌋₊)
    exact le_trans hr (add_le_add (hfin ⌊x⌋₊) le_rfl)

end Work.BMF.liouville
