import Mathlib
import Submission.SieveExpansion
import Submission.Lemma41K

open scoped BigOperators

set_option maxHeartbeats 1000000

/-!
# Theorem 3.6(i) (Polymath8a), the `O(1)`-error half

The window expansion of `Submission/SieveExpansion.lean` writes the sieve sum
(29) as `goodMainSum + goodErrSum`, where `goodErrSum` collects the `O(1)`
errors `#S − N/(W·∏[dᵢ,d′ᵢ])` of the `S`-counting.  This module bounds that
error from above using only the support of the smooth cutoffs `Fᵢ, Gᵢ`:

    |goodErrSum| ≤ 2·Σ_{d,e} |coefProd| = 2·∏ᵢ (Σ_d |λ_{Fᵢ,R}(d)|)·(Σ_e |λ_{Gᵢ,R}(e)|)
                ≤ C·x^{Σᵢ (S(Fᵢ) + S(Gᵢ))} .

Since the hypothesis of Theorem 3.6(i) is `Σᵢ (S(Fᵢ) + S(Gᵢ)) < 1`, this is
`O(x^{1−ε})`, negligible against the main term `≍ x·B^{−k}`.

The key inputs are elementary: `|μ| ≤ 1`, the support bound
`F t = 0` for `|t| > M` (from `HasCompactSupport`), and the resulting
`log_R d ≤ M ⟹ d ≤ R^M`.

All kernel-verified, zero `sorry`.
-/

namespace Commons.NumberTheory.MaynardSieve

/-! ## Support bounds -/

/-- A compactly supported real function vanishes outside a ball: there is
`M > 0` with `F t = 0` whenever `M < |t|`. -/
theorem exists_abs_support_bound (F : ℝ → ℝ) (hcs : HasCompactSupport F) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ t : ℝ, M < |t| → F t = 0 := by
  have hb : Bornology.IsBounded (tsupport F) := hcs.isBounded
  obtain ⟨r, hrpos, hr⟩ := hb.subset_closedBall_lt (0 : ℝ) (0 : ℝ)
  refine ⟨r, hrpos.le, fun t ht => ?_⟩
  have hmem : t ∉ tsupport F := by
    intro h
    have := hr h
    simp only [Metric.mem_closedBall, Real.dist_eq, sub_zero] at this
    linarith [abs_nonneg t]
  exact image_eq_zero_of_notMem_tsupport hmem

/-- `log_R d ≤ M` forces `d ≤ R^M` (for `1 < R`, `d ≠ 0`). -/
lemma le_rpow_of_logR_le {R d : ℕ} {M : ℝ} (hR : 1 < R) (hd : d ≠ 0)
    (h : logR d R ≤ M) : (d : ℝ) ≤ (R : ℝ) ^ M := by
  have hRr : (1 : ℝ) < (R : ℝ) := by exact_mod_cast hR
  have hlogR : 0 < Real.log (R : ℝ) := Real.log_pos hRr
  have hdpos : (0 : ℝ) < (d : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hd
  have hlogd : Real.log (d : ℝ) ≤ M * Real.log (R : ℝ) := by
    have hmul := mul_le_mul_of_nonneg_right h hlogR.le
    rw [logR] at hmul
    rwa [div_mul_cancel₀ (Real.log (d : ℝ)) hlogR.ne'] at hmul
  calc (d : ℝ) = Real.exp (Real.log (d : ℝ)) := (Real.exp_log hdpos).symm
    _ ≤ Real.exp (M * Real.log (R : ℝ)) := Real.exp_le_exp.mpr hlogd
    _ = (R : ℝ) ^ M := by rw [Real.rpow_def_of_pos (by positivity)]; ring_nf

/-! ## Bounding the one-dimensional Möbius weight sum -/

/-- `|μ(d)| ≤ 1` as a real number. -/
lemma abs_moebiusReal_le_one (d : ℕ) : |moebiusReal d| ≤ 1 := by
  rw [moebiusReal, ← Int.cast_abs]
  have h := ArithmeticFunction.abs_moebius_le_one (n := d)
  have h' : ((|ArithmeticFunction.moebius d| : ℤ) : ℝ) ≤ ((1 : ℤ) : ℝ) := by exact_mod_cast h
  simpa using h'

/-- **Support bound for the Möbius weight sum.**  If `F t = 0` for `M < |t|`
and `|F| ≤ B`, then `Σ_{d ≤ D} |μ(d)·F(log_R d)| ≤ 2·(R^M+1)·B`: all
contributing `d` satisfy `d < R^M+1`, and each term is at most `B`. -/
theorem sum_abs_lamDivWeight_le {F : ℝ → ℝ} {R D : ℕ} {M B : ℝ}
    (hR : 1 < R) (hB : 0 ≤ B) (hF : ∀ t : ℝ, |F t| ≤ B)
    (hsupp : ∀ t : ℝ, M < |t| → F t = 0) :
    (∑ d ∈ Finset.range (D + 1), |lamDivWeight F R d|) ≤
      2 * ((R : ℝ) ^ M + 1) * B := by
  classical
  set T : Finset ℕ := (Finset.range (D + 1)).filter (fun d => F (logR d R) ≠ 0) with hT
  have hterm : ∀ d : ℕ, |moebiusReal d| * |F (logR d R)| ≤
      (if F (logR d R) ≠ 0 then (1 : ℝ) else 0) * B := by
    intro d
    by_cases hd : F (logR d R) = 0
    · rw [if_neg (by simp [hd]), zero_mul]
      rw [hd, abs_zero, mul_zero]
    · rw [if_pos hd]
      calc |moebiusReal d| * |F (logR d R)| ≤ 1 * B :=
            mul_le_mul (abs_moebiusReal_le_one d) (hF _) (abs_nonneg _) (by norm_num)
        _ = 1 * B := rfl
  have h1 : (∑ d ∈ Finset.range (D + 1), |lamDivWeight F R d|)
      = ∑ d ∈ Finset.range (D + 1), |moebiusReal d| * |F (logR d R)| := by
    refine Finset.sum_congr rfl (fun d _ => ?_)
    simp only [lamDivWeight, abs_mul, logR]
  have h2 : (∑ d ∈ Finset.range (D + 1), (if F (logR d R) ≠ 0 then (1 : ℝ) else 0) * B)
      = (T.card : ℝ) * B := by
    rw [← Finset.sum_mul]
    congr 1
    rw [hT, ← Finset.sum_filter]
    rw [Finset.sum_const, nsmul_eq_mul, mul_one]
  have hdmem : ∀ d ∈ T, (d : ℝ) < (R : ℝ) ^ M + 1 := by
    intro d hd
    rw [hT, Finset.mem_filter] at hd
    rcases hd with ⟨_, hne⟩
    by_cases hd0 : d = 0
    · subst hd0
      have : (0 : ℝ) ≤ (R : ℝ) ^ M := Real.rpow_nonneg (by positivity) _
      push_cast
      linarith
    · have hlogR : logR d R ≤ M := by
        by_contra hc
        push_neg at hc
        exact hne (hsupp _ (lt_of_lt_of_le hc (le_abs_self _)))
      have hle := le_rpow_of_logR_le (d := d) hR hd0 hlogR
      linarith
  have hcard : (T.card : ℝ) ≤ 2 * ((R : ℝ) ^ M + 1) := by
    have hsub : T ⊆ Finset.range (Nat.ceil ((R : ℝ) ^ M + 1)) := by
      intro d hd
      rw [Finset.mem_range]
      exact Nat.lt_ceil.mpr (hdmem d hd)
    have h1' : T.card ≤ Nat.ceil ((R : ℝ) ^ M + 1) := by
      calc T.card ≤ (Finset.range (Nat.ceil ((R : ℝ) ^ M + 1))).card := Finset.card_le_card hsub
        _ = Nat.ceil ((R : ℝ) ^ M + 1) := Finset.card_range _
    have h2' : ((Nat.ceil ((R : ℝ) ^ M + 1) : ℕ) : ℝ) ≤ 2 * ((R : ℝ) ^ M + 1) := by
      have hnn : (0 : ℝ) ≤ (R : ℝ) ^ M := Real.rpow_nonneg (by positivity) _
      have hlt := Nat.ceil_lt_add_one (by linarith : (0:ℝ) ≤ (R : ℝ) ^ M + 1)
      push_cast
      push_cast at hlt
      linarith
    calc (T.card : ℝ) ≤ ((Nat.ceil ((R : ℝ) ^ M + 1) : ℕ) : ℝ) := by exact_mod_cast h1'
      _ ≤ 2 * ((R : ℝ) ^ M + 1) := h2'
  calc (∑ d ∈ Finset.range (D + 1), |lamDivWeight F R d|)
      = ∑ d ∈ Finset.range (D + 1), |moebiusReal d| * |F (logR d R)| := h1
    _ ≤ ∑ d ∈ Finset.range (D + 1),
          (if F (logR d R) ≠ 0 then (1 : ℝ) else 0) * B := Finset.sum_le_sum (fun d _ => hterm d)
    _ = (T.card : ℝ) * B := h2
    _ ≤ (2 * ((R : ℝ) ^ M + 1)) * B := mul_le_mul_of_nonneg_right hcard hB
    _ = 2 * ((R : ℝ) ^ M + 1) * B := by ring

end Commons.NumberTheory.MaynardSieve

/-! ## The total absolute coefficient sum and the `goodErrSum` bound -/

namespace Commons.NumberTheory.MaynardSieve

/-- **Total absolute coefficient bound.**  For the Maynard weights
`αᵢ = μ·Fᵢ(log_R ·)`, `βᵢ = μ·Gᵢ(log_R ·)`, the sum of the absolute values of
the pair coefficients is bounded by the product of the one-dimensional support
bounds: each factor `Σ_d |μ(d)Fᵢ(log_R d)|` is `≤ 2 (R^{M(Fᵢ)}+1)‖Fᵢ‖`. -/
theorem abs_coefProd_sum_le {k D R : ℕ} {F G : Fin k → ℝ → ℝ}
    {MF MG BF BG : Fin k → ℝ}
    (hR : 1 < R) (hBF : ∀ i, 0 ≤ BF i) (hBG : ∀ i, 0 ≤ BG i)
    (hF : ∀ i t, |F i t| ≤ BF i) (hG : ∀ i t, |G i t| ≤ BG i)
    (hsuppF : ∀ i t, MF i < |t| → F i t = 0)
    (hsuppG : ∀ i t, MG i < |t| → G i t = 0) :
    (∑ d : Fin k → Fin (D + 1), ∑ e : Fin k → Fin (D + 1),
        |coefProd (fun i d => lamDivWeight (F i) R d) (fun i d => lamDivWeight (G i) R d)
          (fun i => (d i : ℕ)) (fun i => (e i : ℕ))|)
      ≤ (∏ i, 2 * ((R : ℝ) ^ MF i + 1) * BF i) *
        (∏ i, 2 * ((R : ℝ) ^ MG i + 1) * BG i) := by
  classical
  have hfac : (∑ d : Fin k → Fin (D + 1), ∑ e : Fin k → Fin (D + 1),
        |coefProd (fun i d => lamDivWeight (F i) R d) (fun i d => lamDivWeight (G i) R d)
          (fun i => (d i : ℕ)) (fun i => (e i : ℕ))|)
      = (∏ i : Fin k, ∑ y : Fin (D + 1), |lamDivWeight (F i) R (y : ℕ)|) *
        (∏ i : Fin k, ∑ y : Fin (D + 1), |lamDivWeight (G i) R (y : ℕ)|) :=
    abs_coefProd_sum_factor (k := k) (D := D)
      (α := fun i d => lamDivWeight (F i) R d) (β := fun i d => lamDivWeight (G i) R d)
  have hA : (∏ i : Fin k, ∑ y : Fin (D + 1), |lamDivWeight (F i) R (y : ℕ)|)
      ≤ (∏ i : Fin k, 2 * ((R : ℝ) ^ MF i + 1) * BF i) := by
    refine Finset.prod_le_prod₀ (fun i _ => ?_) (fun i _ => ?_)
    · exact Finset.sum_nonneg (fun y _ => abs_nonneg _)
    · rw [Fin.sum_univ_eq_sum_range (α := ℝ) (fun d : ℕ => |lamDivWeight (F i) R d|) (D + 1)]
      exact sum_abs_lamDivWeight_le (D := D) hR (hBF i) (hF i) (hsuppF i)
  have hB : (∏ i : Fin k, ∑ y : Fin (D + 1), |lamDivWeight (G i) R (y : ℕ)|)
      ≤ (∏ i : Fin k, 2 * ((R : ℝ) ^ MG i + 1) * BG i) := by
    refine Finset.prod_le_prod₀ (fun i _ => ?_) (fun i _ => ?_)
    · exact Finset.sum_nonneg (fun y _ => abs_nonneg _)
    · rw [Fin.sum_univ_eq_sum_range (α := ℝ) (fun d : ℕ => |lamDivWeight (G i) R d|) (D + 1)]
      exact sum_abs_lamDivWeight_le (D := D) hR (hBG i) (hG i) (hsuppG i)
  have hGnn : (0 : ℝ) ≤ ∏ i : Fin k, ∑ y : Fin (D + 1), |lamDivWeight (G i) R (y : ℕ)| :=
    Finset.prod_nonneg (fun i _ => Finset.sum_nonneg (fun y _ => abs_nonneg _))
  have hFnn : (0 : ℝ) ≤ ∏ i : Fin k, 2 * ((R : ℝ) ^ MF i + 1) * BF i :=
    Finset.prod_nonneg (fun i _ => by
      have h1 : (0:ℝ) ≤ (R : ℝ) ^ MF i := Real.rpow_nonneg (by positivity) _
      have h2 : (0:ℝ) ≤ 2 * ((R : ℝ) ^ MF i + 1) := by positivity
      exact mul_nonneg h2 (hBF i))
  exact le_trans (le_of_eq hfac) (mul_le_mul hA hB hGnn hFnn)

/-- **`O(1)`-error bound of the window expansion** (Theorem 3.6(i), error half).
The collected `S`-count errors are bounded by twice the total absolute
coefficient sum, hence by the product of the support bounds. -/
theorem goodErrSum_support_bound {k D N W b : ℕ} {H : Fin k → ℕ} {R : ℕ}
    {F G : Fin k → ℝ → ℝ} {MF MG BF BG : Fin k → ℝ}
    (hW2 : 2 ≤ W) (hR : 1 < R)
    (hBF : ∀ i, 0 ≤ BF i) (hBG : ∀ i, 0 ≤ BG i)
    (hF : ∀ i t, |F i t| ≤ BF i) (hG : ∀ i t, |G i t| ≤ BG i)
    (hsuppF : ∀ i t, MF i < |t| → F i t = 0)
    (hsuppG : ∀ i t, MG i < |t| → G i t = 0) :
    |goodErrSum (k := k) (D := D) (N := N) (W := W) (b := b) (H := H)
        (fun i d => lamDivWeight (F i) R d) (fun i d => lamDivWeight (G i) R d)| ≤
      2 * ((∏ i, 2 * ((R : ℝ) ^ MF i + 1) * BF i) *
        (∏ i, 2 * ((R : ℝ) ^ MG i + 1) * BG i)) := by
  refine (goodErrSum_bound (k := k) (D := D) (N := N) (W := W) (b := b) (H := H)
    (α := fun i d => lamDivWeight (F i) R d) (β := fun i d => lamDivWeight (G i) R d)
    hW2).trans ?_
  refine mul_le_mul_of_nonneg_left ?_ (by norm_num : (0:ℝ) ≤ 2)
  exact abs_coefProd_sum_le (k := k) (D := D) (R := R) hR hBF hBG hF hG hsuppF hsuppG

end Commons.NumberTheory.MaynardSieve

namespace Commons.NumberTheory.MaynardSieve

/-- **The `O(x^{σ})` form of the error bound**, `σ := Σᵢ (M(Fᵢ) + M(Gᵢ))`: with
`R ≥ 1` and `M ≥ 0`, the factor `2(R^{M}+1)` is at most `4 R^{M}`, so the whole
error is `≤ 2·4^{2k}·(∏‖Fᵢ‖)(∏‖Gᵢ‖)·R^{σ}`.  With the sieve level `R = x` and
the hypothesis `σ < 1` of Theorem 3.6(i), this is `O(x^{1−ε})`. -/
theorem goodErrSum_le_rpow {k D N W b R : ℕ} {H : Fin k → ℕ} {F G : Fin k → ℝ → ℝ}
    {MF MG BF BG : Fin k → ℝ}
    (hW2 : 2 ≤ W) (hR : 1 < R)
    (hMF : ∀ i, 0 ≤ MF i) (hMG : ∀ i, 0 ≤ MG i)
    (hBF : ∀ i, 0 ≤ BF i) (hBG : ∀ i, 0 ≤ BG i)
    (hF : ∀ i t, |F i t| ≤ BF i) (hG : ∀ i t, |G i t| ≤ BG i)
    (hsuppF : ∀ i t, MF i < |t| → F i t = 0)
    (hsuppG : ∀ i t, MG i < |t| → G i t = 0) :
    |goodErrSum (k := k) (D := D) (N := N) (W := W) (b := b) (H := H)
        (fun i d => lamDivWeight (F i) R d) (fun i d => lamDivWeight (G i) R d)| ≤
      (2 * 4 ^ (2 * k) * (∏ i, BF i) * (∏ i, BG i)) *
        (R : ℝ) ^ (∑ i, (MF i + MG i)) := by
  classical
  have hbase := goodErrSum_support_bound (k := k) (D := D) (N := N) (W := W) (b := b)
    (H := H) (R := R) (F := F) (G := G) (MF := MF) (MG := MG) (BF := BF) (BG := BG)
    hW2 hR hBF hBG hF hG hsuppF hsuppG
  refine hbase.trans ?_
  have hRnn : (0 : ℝ) ≤ (R : ℝ) := by positivity
  -- factor-wise bound
  have hfacF : (∏ i, 2 * ((R : ℝ) ^ MF i + 1) * BF i)
      ≤ (∏ i, 4 * (R : ℝ) ^ MF i * BF i) := by
    refine Finset.prod_le_prod₀ (fun i _ => ?_) (fun i _ => ?_)
    · have : (0:ℝ) ≤ (R : ℝ) ^ MF i := Real.rpow_nonneg hRnn _
      have : (0:ℝ) ≤ 2 * ((R : ℝ) ^ MF i + 1) := by positivity
      exact mul_nonneg this (hBF i)
    · have h1 : (1 : ℝ) ≤ (R : ℝ) ^ MF i := Real.one_le_rpow (by exact_mod_cast hR.le) (hMF i)
      have h2 : (0:ℝ) ≤ (R : ℝ) ^ MF i := Real.rpow_nonneg hRnn _
      nlinarith [h1, h2, hBF i, hMF i]
  have hfacG : (∏ i, 2 * ((R : ℝ) ^ MG i + 1) * BG i)
      ≤ (∏ i, 4 * (R : ℝ) ^ MG i * BG i) := by
    refine Finset.prod_le_prod₀ (fun i _ => ?_) (fun i _ => ?_)
    · have : (0:ℝ) ≤ (R : ℝ) ^ MG i := Real.rpow_nonneg hRnn _
      have : (0:ℝ) ≤ 2 * ((R : ℝ) ^ MG i + 1) := by positivity
      exact mul_nonneg this (hBG i)
    · have h1 : (1 : ℝ) ≤ (R : ℝ) ^ MG i := Real.one_le_rpow (by exact_mod_cast hR.le) (hMG i)
      have h2 : (0:ℝ) ≤ (R : ℝ) ^ MG i := Real.rpow_nonneg hRnn _
      nlinarith [h1, h2, hBG i, hMG i]
  have hnn1 : (0:ℝ) ≤ (∏ i, 2 * ((R : ℝ) ^ MG i + 1) * BG i) :=
    Finset.prod_nonneg (fun i _ => mul_nonneg (by have := Real.rpow_nonneg hRnn (MF i); positivity) (hBG i))
  have hnn1' : (0:ℝ) ≤ (∏ i, 2 * ((R : ℝ) ^ MF i + 1) * BF i) :=
    Finset.prod_nonneg (fun i _ => mul_nonneg (by have := Real.rpow_nonneg hRnn (MF i); positivity) (hBF i))
  have hstep : 2 * ((∏ i, 2 * ((R : ℝ) ^ MF i + 1) * BF i) *
        (∏ i, 2 * ((R : ℝ) ^ MG i + 1) * BG i))
      ≤ 2 * ((∏ i, 4 * (R : ℝ) ^ MF i * BF i) * (∏ i, 4 * (R : ℝ) ^ MG i * BG i)) := by
    refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
    exact mul_le_mul hfacF hfacG hnn1 (Finset.prod_nonneg (fun i _ => by
      have : (0:ℝ) ≤ (R : ℝ) ^ MF i := Real.rpow_nonneg hRnn _
      exact mul_nonneg (mul_nonneg (by norm_num) this) (hBF i)))
  refine hstep.trans (le_of_eq ?_)
  have hpow : (R : ℝ) ^ (∑ i, (MF i + MG i))
      = (∏ i, (R : ℝ) ^ MF i) * (∏ i, (R : ℝ) ^ MG i) := by
    rw [Real.rpow_sum_of_nonneg (s := Finset.univ) hRnn
      (fun i _ => add_nonneg (hMF i) (hMG i))]
    rw [Finset.prod_congr rfl (fun i _ => Real.rpow_add (by positivity) (MF i) (MG i))]
    rw [Finset.prod_mul_distrib]
  have hprodF : (∏ i, 4 * (R : ℝ) ^ MF i * BF i)
      = 4 ^ k * ((∏ i, (R : ℝ) ^ MF i) * (∏ i, BF i)) := by
    rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib, Finset.prod_const]
    rw [Finset.card_univ, Fintype.card_fin]
    ring
  have hprodG : (∏ i, 4 * (R : ℝ) ^ MG i * BG i)
      = 4 ^ k * ((∏ i, (R : ℝ) ^ MG i) * (∏ i, BG i)) := by
    rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib, Finset.prod_const]
    rw [Finset.card_univ, Fintype.card_fin]
    ring
  rw [hpow, hprodF, hprodG]
  ring

end Commons.NumberTheory.MaynardSieve
