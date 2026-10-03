/-
# The uniform sup bound for signed sums of the modified KMT bumps `varphiNtj`

The target of this file is `Work.KMTPlan.A6.MdlLinVarphiNtjSupBound`: for a lacunary sequence
`a` (`Λ`-lacunary, `Λ > 1`, with `a n ≥ 1`) there is a constant `C` such that for *every* finite
set of indices `U`, *every* choice of signs `ω : ℕ → Bool` and every frequency `ξ`

  `‖∑_{n ∈ U} (±1) φ_{⌊a n⌋,k₁,j₁}(t,ξ)‖ ≤ C`

uniformly in the height `k₁ ≥ 1` and the twist `j₁ ∈ {-1,0,1}`, and likewise for the bottom height
`(k₁,j₁) = (0,1)`.

Math.  The summands are the modified bumps
`φ_{N,k,j}(t,ξ) = (2^{-k}Nξ)^j φ_{N,k}(ξ) e(Ntξ)` of the integration-by-parts identity.

* At the heights `k₁ ≥ 1` the bump `φ_{N,k₁}` is supported in the *annulus*
  `1/4 < |2^{Log N-k₁}ξ| ≤ 1`, so a nonzero value of the `n`-th summand forces the scale
  `N = ⌊a n⌋` into the multiplicative window `(A,16A)`, `A = 2^{k₁}/(8|ξ|)`.  Summands are
  bounded by `8` (`norm_varphiNtj_le_eight`) and by lacunarity only a bounded number of scales
  (at most twice `log 9 / log Λ + 1`) fall into such a window (`lacWindow_card`).  No
  cancellation is used: the signs `ω` are absorbed by the triangle inequality.
* At the bottom height `(k₁,j₁) = (0,1)` the bump `φ_{N,0} = η(2^{Log N}·)` is *not* an annulus
  and there may be unboundedly many active scales; but the summand is
  `(Nξ)η(2^{Log N}ξ)e(Ntξ)`, i.e. a fixed profile evaluated at the geometrically growing variable
  `2^{Log N}ξ`, so the active scales (those with `⌊a n⌋|ξ| < 2`) form a geometric progression and
  the sum of `⌊a n⌋|ξ|` over them is bounded by `4Λ/(Λ-1)`.

Both bounds are insensitive to the signs `ω`, which is why arbitrary signs cost nothing.
-/
import Mathlib
import Submission.Work.KMTPlan.A6.lowModSymbFAux
import Submission.Work.KMTPlan.A6.lacWindowCard16
import Submission.Work.KMTPlan.A6.lacGeomSumBound

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.unusedVariables false

namespace Work.KMTPlan.A6

open Finset
open Work.KMTAreas.A7
open Work.Analysis.EndVar

noncomputable section

/-! ## Pointwise facts about the modified bumps -/

/-- At the frequencies `ξ ≠ 0` the bump `φ_{N,k}` with `k ≥ 1` is supported in the annulus
`1/4 < |2^{Log N-k}ξ| ≤ 1`; in *cleared* form (multiplying by `8|ξ| > 0`) this says that the scale
`N` lies in the multiplicative window `(2^k/(8|ξ|), 16·2^k/(8|ξ|))`. -/
private lemma window_cleared {N k : ℕ} (hN : 1 ≤ N) (hk : 1 ≤ k) {ξ : ℝ} (hξ : ξ ≠ 0)
    (h : varphiN N k ξ ≠ 0) :
    (2 : ℝ) ^ k < 8 * |ξ| * (N : ℝ) ∧ (8 : ℝ) * |ξ| * (N : ℝ) < 16 * (2 : ℝ) ^ k := by
  set p : ℝ := (2 : ℝ) ^ ((logN N : ℝ) - (k : ℝ)) with hp
  set q : ℝ := (2 : ℝ) ^ (logN N : ℝ) with hq
  set Q : ℝ := (2 : ℝ) ^ (k : ℝ) with hQ
  have hp0 : 0 < p := by rw [hp]; exact Real.rpow_pos_of_pos (by norm_num) _
  have hQ0 : 0 < Q := by rw [hQ]; exact Real.rpow_pos_of_pos (by norm_num) _
  have hpq : q = p * Q := by
    rw [hp, hq, hQ, ← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
    congr 1
    ring
  have hlow : (1 : ℝ) / 4 < p * |ξ| := by
    have h1 := one_four_lt_of_varphiN_ne_zero N k hk ξ h
    rwa [← hp, abs_mul, abs_of_pos hp0] at h1
  have hup : p * |ξ| ≤ 1 := by
    have h1 := varphiN_ne_zero_le N k ξ h
    rwa [← hp, abs_mul, abs_of_pos hp0] at h1
  have hQeq : (2 : ℝ) ^ k = Q := by rw [hQ, Real.rpow_natCast]
  have hNge : q / 2 ≤ (N : ℝ) := by
    have h1 := two_pow_logN_le_two_mul_N hN
    rw [← hq] at h1
    linarith
  have hNlt : (N : ℝ) < 2 * q := by
    have h1 := nat_lt_two_mul_two_pow_logN N
    rw [← hq] at h1
    linarith
  constructor
  · rw [hQeq]
    have hkey : Q < 4 * (|ξ| * p) * Q := by
      have h1 := mul_lt_mul_of_pos_right hlow hQ0
      linarith
    have h2 : Q < 8 * |ξ| * (q / 2) := by
      have h3 : 8 * |ξ| * (q / 2) = 4 * (|ξ| * p) * Q := by rw [hpq]; ring
      rw [h3]; exact hkey
    have h4 : 8 * |ξ| * (q / 2) ≤ 8 * |ξ| * (N : ℝ) :=
      mul_le_mul_of_nonneg_left hNge (by positivity)
    linarith
  · rw [hQeq]
    have hkey : 16 * ((p * |ξ|) * Q) ≤ 16 * Q := by
      have h1 := mul_le_mul_of_nonneg_right hup hQ0.le
      linarith
    have h2 : 8 * |ξ| * (2 * q) ≤ 16 * Q := by
      have h3 : 8 * |ξ| * (2 * q) = 16 * ((p * |ξ|) * Q) := by rw [hpq]; ring
      rw [h3]; exact hkey
    have h4 : 8 * |ξ| * (N : ℝ) < 8 * |ξ| * (2 * q) :=
      mul_lt_mul_of_pos_left hNlt (by positivity)
    linarith

/-- The window form of `window_cleared`: a nonzero value of `φ_{N,k}` (`k ≥ 1`) at `ξ ≠ 0`
forces `A < N < 16A` for `A = 2^k/(8|ξ|)`. -/
private lemma window_of_varphiN_ne_zero {N k : ℕ} (hN : 1 ≤ N) (hk : 1 ≤ k) {ξ : ℝ}
    (hξ : ξ ≠ 0) (h : varphiN N k ξ ≠ 0) :
    (2 : ℝ) ^ k / (8 * |ξ|) < (N : ℝ) ∧
      (N : ℝ) < 16 * ((2 : ℝ) ^ k / (8 * |ξ|)) := by
  obtain ⟨h1, h2⟩ := window_cleared hN hk hξ h
  have hpos : 0 < (8 : ℝ) * |ξ| := by
    have : 0 < |ξ| := abs_pos.mpr hξ
    linarith
  constructor
  · rw [div_lt_iff₀ hpos]
    linarith
  · have h3 : (N : ℝ) < 16 * (2 : ℝ) ^ k / ((8 : ℝ) * |ξ|) := by
      rw [lt_div_iff₀ hpos]
      linarith
    calc (N : ℝ) < 16 * (2 : ℝ) ^ k / ((8 : ℝ) * |ξ|) := h3
      _ = 16 * ((2 : ℝ) ^ k / ((8 : ℝ) * |ξ|)) := mul_div_assoc _ _ _

/-- At the frequencies `ξ = 0` the modified bump at a height `k ≥ 1` vanishes, for every twist
`j`. -/
private lemma varphiNtj_apply_zero {N k : ℕ} (hk : 1 ≤ k) (j : ℤ) (t : ℝ) :
    varphiNtj N k j t 0 = 0 := by
  have hφ : varphiN N k (0 : ℝ) = 0 := by
    rw [varphiN_apply_form]
    have hk0 : k ≠ 0 := by omega
    simp [hk0]
  rw [varphiNtj, varphiNt, hφ, zero_mul, mul_zero]

/-- The `(k,j) = (0,1)` bump is bounded by `N|ξ|`. -/
private lemma norm_varphiNtj_k0j1_le (N : ℕ) (t ξ : ℝ) :
    ‖varphiNtj N 0 1 t ξ‖ ≤ (N : ℝ) * |ξ| := by
  have h1 : varphiNtj N 0 1 t ξ = ((((N : ℝ) * ξ : ℝ)) : ℂ) * varphiNt N 0 t ξ := by
    rw [varphiNtj]
    simp only [Nat.cast_zero, neg_zero, Real.rpow_zero, one_mul, zpow_one]
  rw [h1, norm_mul, Complex.norm_real, Real.norm_eq_abs]
  calc |(N : ℝ) * ξ| * ‖varphiNt N 0 t ξ‖ ≤ |(N : ℝ) * ξ| * 1 :=
        mul_le_mul_of_nonneg_left (varphiNt_norm_le_one N 0 t ξ) (abs_nonneg _)
    _ = (N : ℝ) * |ξ| := by
        rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg N), mul_one]

/-- A nonzero value of the `(k,j) = (0,1)` bump forces `N|ξ| < 2`. -/
private lemma k0j1_support {N : ℕ} (t ξ : ℝ) (h : varphiNtj N 0 1 t ξ ≠ 0) :
    (N : ℝ) * |ξ| < 2 := by
  have hφ : varphiN N 0 ξ ≠ 0 := varphiN_ne_zero_of_varphiNtj_ne_zero N 0 1 t ξ h
  have hφ' : Work.KMTContract.kmtEta ((2 : ℝ) ^ (logN N : ℝ) * ξ) ≠ 0 := by
    simpa only [varphiN, if_true] using hφ
  have h3 : ¬ (1 ≤ |(2 : ℝ) ^ (logN N : ℝ) * ξ|) :=
    fun hc => hφ' (Work.KMTContract.kmtEta_zero hc)
  have h4 : |(2 : ℝ) ^ (logN N : ℝ) * ξ| < 1 := lt_of_not_ge h3
  have hp : 0 < (2 : ℝ) ^ (logN N : ℝ) := Real.rpow_pos_of_pos (by norm_num) _
  rw [abs_mul, abs_of_pos hp] at h4
  by_cases hξ : ξ = 0
  · rw [hξ, abs_zero, mul_zero]; norm_num
  · have h5 : (N : ℝ) < 2 * (2 : ℝ) ^ (logN N : ℝ) := nat_lt_two_mul_two_pow_logN N
    have h6 := mul_lt_mul_of_pos_right h5 (abs_pos.mpr hξ)
    linarith

/-! ## The two clauses -/

/-- The heights `k₁ ≥ 1`, twists `j₁ ∈ {-1,0,1}`: the signed sums of the bumps are bounded, by the
annulus structure of `φ_{N,k₁}` and the lacunary window count. -/
private theorem sup_bound_kpos (Λ : NNReal) (hΛ : 1 < Λ) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (k₁ : ℕ) (hk₁ : 1 ≤ k₁) (j₁ : ℤ) (hj₁ : j₁ ∈ ({-1, 0, 1} : Finset ℤ))
        (t : ℝ) (ht : t ∈ Set.Icc (1 / 2 : ℝ) 1) (a : ℕ → NNReal)
        (ha : PointwiseErgodicTheorems.Lacunary Λ a) (ha1 : ∀ n, 1 ≤ a n)
        (U : Finset ℕ) (ω : ℕ → Bool) (ξ : ℝ),
        ‖∑ n ∈ U, (if ω n then (1 : ℂ) else -1) *
            varphiNtj (Nat.floor (a n)) k₁ j₁ t ξ‖ ≤ C := by
  obtain ⟨C₀, hC₀0, hC₀⟩ := lacWindowCard16 Λ hΛ
  refine ⟨8 * C₀ + 1, by linarith, ?_⟩
  intro k₁ hk₁ j₁ hj₁ t ht a ha ha1 U ω ξ
  classical
  have hUU : U ⊆ Finset.range (U.sup id + 1) := by
    intro n hn
    simp only [Finset.mem_range]
    have h1 : n ≤ U.sup id := Finset.le_sup (f := id) hn
    omega
  by_cases hξ : ξ = 0
  · have hzero : ∀ n, varphiNtj (Nat.floor (a n)) k₁ j₁ t ξ = 0 := by
      intro n; rw [hξ]; exact varphiNtj_apply_zero hk₁ j₁ t
    have hsum : ∑ n ∈ U, (if ω n then (1 : ℂ) else -1) *
        varphiNtj (Nat.floor (a n)) k₁ j₁ t ξ = 0 := by
      refine Finset.sum_eq_zero fun n _ => ?_
      rw [hzero n, mul_zero]
    rw [hsum, norm_zero]
    linarith
  · set A : ℝ := (2 : ℝ) ^ k₁ / (8 * |ξ|) with hA
    have hApos : 0 < A := by
      have hξpos : 0 < |ξ| := abs_pos.mpr hξ
      rw [hA]; positivity
    set d : ℕ → ℂ := fun n => varphiNtj (Nat.floor (a n)) k₁ j₁ t ξ with hd
    have hd8 : ∀ n, ‖d n‖ ≤ 8 := fun n =>
      norm_varphiNtj_le_eight (Nat.floor (a n)) k₁ j₁ hj₁ (Or.inl (by omega))
        ((Nat.one_le_floor_iff (a n)).mpr (ha1 n)) t ξ
    have hdwin : ∀ n, d n ≠ 0 →
        A < (Nat.floor (a n) : ℝ) ∧ (Nat.floor (a n) : ℝ) < 16 * A := by
      intro n hn
      have h := window_of_varphiN_ne_zero ((Nat.one_le_floor_iff (a n)).mpr (ha1 n)) hk₁ hξ
        (varphiN_ne_zero_of_varphiNtj_ne_zero _ _ _ _ _ hn)
      rwa [← hA] at h
    have hcard : ((U.filter fun n => d n ≠ 0).card : ℝ) ≤ C₀ := by
      have hsub : U.filter (fun n => d n ≠ 0) ⊆ (Finset.range (U.sup id + 1)).filter
          (fun n => A < (Nat.floor (a n) : ℝ) ∧ (Nat.floor (a n) : ℝ) < 16 * A) := by
        intro n hn
        rw [Finset.mem_filter] at hn ⊢
        exact ⟨hUU hn.1, hdwin n hn.2⟩
      have h1 : ((U.filter fun n => d n ≠ 0).card : ℝ)
          ≤ (((Finset.range (U.sup id + 1)).filter
              (fun n => A < (Nat.floor (a n) : ℝ) ∧ (Nat.floor (a n) : ℝ) < 16 * A)).card : ℝ) :=
        by exact_mod_cast Finset.card_le_card hsub
      exact le_trans h1 (hC₀ a ha ha1 (U.sup id + 1) A hApos)
    calc ‖∑ n ∈ U, (if ω n then (1 : ℂ) else -1) * d n‖
        ≤ ∑ n ∈ U, ‖(if ω n then (1 : ℂ) else -1) * d n‖ := norm_sum_le _ _
      _ = ∑ n ∈ U, ‖d n‖ := by
          refine Finset.sum_congr rfl fun n _ => ?_
          rw [norm_mul]
          by_cases h : ω n <;> simp [h]
      _ = ∑ n ∈ U.filter (fun n => d n ≠ 0), ‖d n‖ :=
          (Finset.sum_filter_of_ne fun n _ hn => norm_ne_zero_iff.mp hn).symm
      _ ≤ ∑ n ∈ U.filter (fun n => d n ≠ 0), (8 : ℝ) :=
          Finset.sum_le_sum fun n _ => hd8 n
      _ = 8 * ((U.filter fun n => d n ≠ 0).card : ℝ) := by
          rw [Finset.sum_const, nsmul_eq_mul]
          ring
      _ ≤ 8 * C₀ := by linarith
      _ ≤ 8 * C₀ + 1 := by linarith

/-- The bottom height `(k₁,j₁) = (0,1)`: the signed sums of the bumps are bounded by the geometric
sum of the active scales. -/
private theorem sup_bound_k0j1 (Λ : NNReal) (hΛ : 1 < Λ) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (t : ℝ) (ht : t ∈ Set.Icc (1 / 2 : ℝ) 1) (a : ℕ → NNReal)
        (ha : PointwiseErgodicTheorems.Lacunary Λ a) (ha1 : ∀ n, 1 ≤ a n)
        (U : Finset ℕ) (ω : ℕ → Bool) (ξ : ℝ),
        ‖∑ n ∈ U, (if ω n then (1 : ℂ) else -1) *
            varphiNtj (Nat.floor (a n)) 0 1 t ξ‖ ≤ C := by
  obtain ⟨C₀, hC₀0, hC₀⟩ := lacGeomSumBound Λ hΛ
  refine ⟨C₀ + 1, by linarith, ?_⟩
  intro t ht a ha ha1 U ω ξ
  classical
  set d : ℕ → ℂ := fun n => varphiNtj (Nat.floor (a n)) 0 1 t ξ with hd
  have hS : ∀ n ∈ U.filter (fun n => d n ≠ 0), (Nat.floor (a n) : ℝ) * |ξ| < 2 :=
    fun n hn => k0j1_support t ξ (Finset.mem_filter.mp hn).2
  calc ‖∑ n ∈ U, (if ω n then (1 : ℂ) else -1) * d n‖
      ≤ ∑ n ∈ U, ‖(if ω n then (1 : ℂ) else -1) * d n‖ := norm_sum_le _ _
    _ = ∑ n ∈ U, ‖d n‖ := by
        refine Finset.sum_congr rfl fun n _ => ?_
        rw [norm_mul]
        by_cases h : ω n <;> simp [h]
    _ = ∑ n ∈ U.filter (fun n => d n ≠ 0), ‖d n‖ :=
        (Finset.sum_filter_of_ne fun n _ hn => norm_ne_zero_iff.mp hn).symm
    _ ≤ ∑ n ∈ U.filter (fun n => d n ≠ 0), (Nat.floor (a n) : ℝ) * |ξ| :=
        Finset.sum_le_sum fun n _ => norm_varphiNtj_k0j1_le _ t ξ
    _ ≤ C₀ := hC₀ a ha ha1 |ξ| _ hS
    _ ≤ C₀ + 1 := by linarith

/-- **The uniform sup bound for signed sums of the modified bumps.**

For a `Λ`-lacunary sequence `a` with `Λ > 1` and `a n ≥ 1` the signed sums
`∑_{n ∈ U} (±1) φ_{⌊a n⌋,k₁,j₁}(t,ξ)` over an *arbitrary* finite set of indices and *arbitrary*
signs are bounded by a constant depending only on `Λ`: at the heights `k₁ ≥ 1` and twists
`j₁ ∈ {-1,0,1}` by the lacunary window count (`sup_bound_kpos`), and at the bottom height
`(k₁,j₁) = (0,1)` by the geometric bound on the active scales (`sup_bound_k0j1`). -/
theorem MdlLinVarphiNtjSupBound (Λ : NNReal) (hΛ : 1 < Λ) :
    ∃ C : ℝ, 0 < C ∧
      (∀ (k₁ : ℕ) (hk₁ : 1 ≤ k₁) (j₁ : ℤ) (hj₁ : j₁ ∈ ({-1, 0, 1} : Finset ℤ))
        (t : ℝ) (ht : t ∈ Set.Icc (1 / 2 : ℝ) 1) (a : ℕ → NNReal)
        (ha : PointwiseErgodicTheorems.Lacunary Λ a) (ha1 : ∀ n, 1 ≤ a n)
        (U : Finset ℕ) (ω : ℕ → Bool) (ξ : ℝ),
        ‖∑ n ∈ U, (if ω n then (1 : ℂ) else -1) *
            Work.KMTPlan.A6.varphiNtj (Nat.floor (a n)) k₁ j₁ t ξ‖ ≤ C) ∧
      (∀ (t : ℝ) (ht : t ∈ Set.Icc (1 / 2 : ℝ) 1) (a : ℕ → NNReal)
        (ha : PointwiseErgodicTheorems.Lacunary Λ a) (ha1 : ∀ n, 1 ≤ a n)
        (U : Finset ℕ) (ω : ℕ → Bool) (ξ : ℝ),
        ‖∑ n ∈ U, (if ω n then (1 : ℂ) else -1) *
            Work.KMTPlan.A6.varphiNtj (Nat.floor (a n)) 0 1 t ξ‖ ≤ C) := by
  obtain ⟨C₁, hC₁0, hC₁⟩ := sup_bound_kpos Λ hΛ
  obtain ⟨C₂, hC₂0, hC₂⟩ := sup_bound_k0j1 Λ hΛ
  refine ⟨max C₁ C₂, lt_of_lt_of_le hC₁0 (le_max_left _ _), ?_, ?_⟩
  · intro k₁ hk₁ j₁ hj₁ t ht a ha ha1 U ω ξ
    exact le_trans (hC₁ k₁ hk₁ j₁ hj₁ t ht a ha ha1 U ω ξ) (le_max_left _ _)
  · intro t ht a ha ha1 U ω ξ
    exact le_trans (hC₂ t ht a ha ha1 U ω ξ) (le_max_right _ _)

end

end Work.KMTPlan.A6
