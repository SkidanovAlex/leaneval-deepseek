import Submission.ZagierHoffmanProof.EndgameLast1

/-!
# SESSION 362 — the last case `w = 2q-2`: the `θ`-coefficient extraction `tp`

`PLAN.md` §«SESSION 362».  `tp p j` is the `X`-polynomial of the `θ^j`-coefficients of `p`:
`(tp F p j).coeff n = coeffNu F 0 j (p.coeff n)`.  Its multiplicativity against `θ`-constant factors
(`tp_mul_const`) and against `θ`-powers (`tp_theta_pow_mul`) is what turns the identity `num = L^w·V`
into the two *polynomial* relations `D_1 = w·X·D_2` and `D_0 = w·X·D_1 - C(w,2)·X²·D_2` that give
`V = D_2·L²` (Dac §6, the `k = q-1` computation).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 4000000
open Polynomial
open scoped WithZero Classical

namespace ZagierHoffmanPositiveChar

variable (F : Type*) [Field F] [Finite F] [DecidableEq (RatFunc F)]

/-! ## §3. The `θ`-coefficient extraction -/

/-- The `X`-polynomial of the `θ^j`-coefficients of `p`. -/
noncomputable def tp (p : Polynomial (Ambient F)) (j : ℕ) : Polynomial (Ambient F) :=
  p.sum (fun n _ => Polynomial.C (coeffNu F 0 j (p.coeff n)) * Polynomial.X ^ n)

lemma tp_coeff (p : Polynomial (Ambient F)) (j n : ℕ) :
    (tp F p j).coeff n = coeffNu F 0 j (p.coeff n) := by
  classical
  rw [tp, Polynomial.coeff_sum, Polynomial.sum_def]
  have h1 : ∀ m ∈ p.support,
      ((Polynomial.C (coeffNu F 0 j (p.coeff m)) * Polynomial.X ^ m :
        Polynomial (Ambient F)).coeff n) = if n = m then coeffNu F 0 j (p.coeff m) else 0 := by
    intro m _
    rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
    by_cases hmn : n = m
    · rw [if_pos hmn, if_pos hmn, mul_one]
    · rw [if_neg hmn, if_neg hmn, mul_zero]
  rw [Finset.sum_congr rfl h1, Finset.sum_ite_eq]
  by_cases hn : n ∈ p.support
  · rw [if_pos hn]
  · rw [if_neg hn]
    have h0 : p.coeff n = 0 := by
      by_contra hne
      exact hn (Polynomial.mem_support_iff.mpr hne)
    rw [h0, coeffNu_zero]

/-- ★ **`tp` against a `θ`-constant factor.** -/
lemma tp_mul_const {p q : Polynomial (Ambient F)} (hp : ∀ n, p.coeff n ∈ ambF F)
    (hq : ∀ n, q.coeff n ∈ ambA F 0) (j : ℕ) :
    tp F (p * q) j = p * tp F q j := by
  ext n
  rw [tp_coeff, Polynomial.coeff_mul, Polynomial.coeff_mul]
  rw [coeffNu_sum F _ (fun b _ =>
    ambA_mul_mem F (mem_ambA_zero_of_mem_ambF (hp b.1)) (hq b.2)) j]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [coeffNu_mul_of_constant F (mem_ambA_zero_of_mem_ambF (hp b.1)) (hq b.2)
    (fun i hi => coeffNu_eq_zero_of_mem_ambF F (hp b.1) hi) j,
    coeffNu_zero_of_mem_ambF F (hp b.1), tp_coeff]

/-- The `θ`-coefficient of a `θ`-power times an element of `A_0`. -/
lemma coeffNu_theta_pow_mul {N j : ℕ} {x : Ambient F} (hx : x ∈ ambA F 0) :
    coeffNu F 0 j ((ambTheta F) ^ N * x) = if N ≤ j then coeffNu F 0 (j - N) x else 0 := by
  obtain ⟨p, hp⟩ := (mem_ambA_iff F 0 x).mp hx
  rw [ambThetaNu_zero F] at hp
  have h1 : (ambTheta F) ^ N * p.eval₂ (algebraMap F (Ambient F)) (ambTheta F)
      = (Polynomial.X ^ N * p).eval₂ (algebraMap F (Ambient F)) (ambTheta F) := by
    rw [Polynomial.eval₂_mul, Polynomial.eval₂_pow, Polynomial.eval₂_X]
  have hmem : p.eval₂ (algebraMap F (Ambient F)) (ambTheta F) ∈ ambA F 0 :=
    (mem_ambA_iff F 0 _).mpr ⟨p, by rw [ambThetaNu_zero F]⟩
  have hmem2 : (Polynomial.X ^ N * p).eval₂ (algebraMap F (Ambient F)) (ambTheta F) ∈ ambA F 0 :=
    (mem_ambA_iff F 0 _).mpr ⟨Polynomial.X ^ N * p, by rw [ambThetaNu_zero F]⟩
  rw [← hp]
  rw [h1, coeffNu_eq_of_eval F hmem2 (p := Polynomial.X ^ N * p)
      (by rw [ambThetaNu_zero F]) j,
    coeffNu_eq_of_eval F hmem (p := p) (by rw [ambThetaNu_zero F]) (j - N),
    Polynomial.coeff_X_pow_mul']
  by_cases h : N ≤ j
  · rw [if_pos h, if_pos h]
  · rw [if_neg h, if_neg h, map_zero]

/-- ★ **`tp` against a `θ`-power factor.** -/
lemma tp_theta_pow_mul {N : ℕ} {y : Polynomial (Ambient F)} (hy : ∀ n, y.coeff n ∈ ambA F 0)
    (j : ℕ) :
    tp F (Polynomial.C ((ambTheta F) ^ N) * y) j
      = if N ≤ j then tp F y (j - N) else 0 := by
  ext n
  rw [tp_coeff, Polynomial.coeff_C_mul, coeffNu_theta_pow_mul F (hy n)]
  by_cases h : N ≤ j
  · rw [if_pos h, if_pos h, tp_coeff]
  · rw [if_neg h, if_neg h]
    simp


/-- ★ **`tp` is additive** (on `A_0`-valued polynomials). -/
lemma tp_add {p q : Polynomial (Ambient F)} (hp : ∀ n, p.coeff n ∈ ambA F 0)
    (hq : ∀ n, q.coeff n ∈ ambA F 0) (j : ℕ) :
    tp F (p + q) j = tp F p j + tp F q j := by
  ext n
  have h1 : (tp F (p + q) j).coeff n = coeffNu F 0 j (p.coeff n) + coeffNu F 0 j (q.coeff n) := by
    rw [tp_coeff, Polynomial.coeff_add, coeffNu_add F (hp n) (hq n)]
  rw [h1, Polynomial.coeff_add, tp_coeff, tp_coeff]

/-- The coefficients of `tp F p i` are `θ`-constants. -/
lemma tp_coeff_mem_ambF {p : Polynomial (Ambient F)} (hp : ∀ n, p.coeff n ∈ ambA F 0)
    (i n : ℕ) : (tp F p i).coeff n ∈ ambF F := by
  rw [tp_coeff]
  exact coeffNu_mem_ambF F (hp n)

/-- ★★★★★ **The `θ`-decomposition**: an `A_0[X]`-polynomial with all `θ`-degrees `≤ 2` is a
quadratic in `θ` with coefficients in `F_q[X]`. -/
theorem tp_decomp {p : Polynomial (Ambient F)} (hp : ∀ n, p.coeff n ∈ ambA F 0)
    (hd : ∀ n, degNu F 0 (p.coeff n) ≤ 2) :
    p = tp F p 0 + tp F p 1 * Polynomial.C (ambTheta F)
      + tp F p 2 * Polynomial.C ((ambTheta F) ^ 2) := by
  ext n
  rw [Polynomial.coeff_add, Polynomial.coeff_add, Polynomial.coeff_mul_C, Polynomial.coeff_mul_C,
    tp_coeff, tp_coeff, tp_coeff]
  have hsum := sum_coeffNu_mul_ambThetaNu F 0 (hp n)
  rw [ambThetaNu_zero F] at hsum
  have hsub : (∑ j ∈ Finset.range (degNu F 0 (p.coeff n) + 1),
      coeffNu F 0 j (p.coeff n) * (ambTheta F) ^ j)
      = (∑ j ∈ Finset.range 3, coeffNu F 0 j (p.coeff n) * (ambTheta F) ^ j) := by
    refine Finset.sum_subset ?_ ?_
    · intro j hj
      rw [Finset.mem_range] at hj ⊢
      have := hd n
      omega
    · intro j hj3 hjnot
      rw [Finset.mem_range] at hj3 hjnot
      rw [coeffNu_degNu_lt F (hp n) (by omega), zero_mul]
  have hfinal : (∑ j ∈ Finset.range 3, coeffNu F 0 j (p.coeff n) * (ambTheta F) ^ j)
      = p.coeff n := hsub.symm.trans hsum
  conv_lhs => rw [← hfinal]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  ring


/-! ## §4. `tp` of `(X - C θ)^k` -/

/-- ★★ **The `θ^j`-coefficient of the `X^n`-coefficient of `(X - Cθ)^k`.** -/
lemma coeffNu_X_sub_C_theta_pow_coeff (k n j : ℕ) :
    coeffNu F 0 j (((Polynomial.X - Polynomial.C (ambTheta F)) ^ k :
        Polynomial (Ambient F)).coeff n)
      = if k - n = j then ambCoeff F (((-1 : F) ^ (k - n)) * (k.choose n : F)) else 0 := by
  have hx : ambCoeff F (((-1 : F) ^ (k - n)) * (k.choose n : F)) ∈ ambA F 0 :=
    ambF_subset_ambA_zero (F := F) (ambCoeff_mem_ambF F _)
  rw [coeff_X_sub_C_theta_pow F k n, mul_comm, coeffNu_theta_pow_mul F hx]
  by_cases h : k - n = j
  · rw [if_pos (le_of_eq h), show j - (k - n) = 0 from by omega, if_pos h,
      coeffNu_zero_of_mem_ambF F (ambCoeff_mem_ambF F _)]
  · rw [if_neg h]
    rcases lt_or_gt_of_ne (Ne.symm h) with hlt | hgt
    · rw [if_neg (by omega : ¬ (k - n ≤ j))]
    · rw [if_pos (by omega : k - n ≤ j),
        coeffNu_eq_zero_of_mem_ambF F (ambCoeff_mem_ambF F _) (by omega)]

/-- `tp` of `(X - Cθ)^k` above the `θ`-degree `k`. -/
lemma tp_X_sub_C_theta_pow_gt {k j : ℕ} (h : k < j) :
    tp F ((Polynomial.X - Polynomial.C (ambTheta F)) ^ k) j = 0 := by
  ext n
  rw [tp_coeff, coeffNu_X_sub_C_theta_pow_coeff F k n j,
    if_neg (by omega : ¬ k - n = j)]
  simp

/-- ★★★ `tp` of `(X - Cθ)^k` at the top `θ`-degree `k`. -/
lemma tp_X_sub_C_theta_pow_self {k : ℕ} (hk0 : k ≠ 0) (h : (-1 : F) ^ k = 1) :
    tp F ((Polynomial.X - Polynomial.C (ambTheta F)) ^ k) k = 1 := by
  ext n
  rw [tp_coeff, coeffNu_X_sub_C_theta_pow_coeff F k n k, Polynomial.coeff_one]
  by_cases hn : n = 0
  · subst hn
    rw [show k - 0 = k from by omega, if_pos rfl, Nat.choose_zero_right, Nat.cast_one, mul_one, h,
      map_one, if_pos rfl]
  · rw [if_neg hn, if_neg (by omega : ¬ (k - n = k))]

/-- ★★★ `tp` of `(X - Cθ)^k` at `θ`-degree `k-1`. -/
lemma tp_X_sub_C_theta_pow_sub_one {k : ℕ} (hk : 1 ≤ k) (h : (-1 : F) ^ (k - 1) = -1) :
    tp F ((Polynomial.X - Polynomial.C (ambTheta F)) ^ k) (k - 1)
      = Polynomial.C (ambCoeff F (-(k : F))) * Polynomial.X := by
  ext n
  rw [tp_coeff, coeffNu_X_sub_C_theta_pow_coeff F k n (k - 1), Polynomial.coeff_C_mul,
    Polynomial.coeff_X]
  by_cases hn : n = 1
  · subst hn
    rw [if_pos rfl, if_pos rfl, mul_one, h, Nat.choose_one_right, neg_one_mul]
  · rw [if_neg (fun h1 : (1 : ℕ) = n => hn h1.symm), mul_zero]
    by_cases hnk : n ≤ k
    · rw [if_neg (by omega : ¬ (k - n = k - 1))]
    · by_cases hc : k - n = k - 1
      · rw [if_pos hc, Nat.choose_eq_zero_of_lt (by omega), Nat.cast_zero, mul_zero, map_zero]
      · rw [if_neg hc]

/-- ★★★ `tp` of `(X - Cθ)^k` at `θ`-degree `k-2`. -/
lemma tp_X_sub_C_theta_pow_sub_two {k : ℕ} (hk : 2 ≤ k) (h : (-1 : F) ^ (k - 2) = 1) :
    tp F ((Polynomial.X - Polynomial.C (ambTheta F)) ^ k) (k - 2)
      = Polynomial.C (ambCoeff F ((k.choose 2 : ℕ) : F)) * Polynomial.X ^ 2 := by
  ext n
  rw [tp_coeff, coeffNu_X_sub_C_theta_pow_coeff F k n (k - 2), Polynomial.coeff_C_mul,
    Polynomial.coeff_X_pow]
  by_cases hn : n = 2
  · subst hn
    rw [if_pos rfl, h, one_mul, if_pos rfl, mul_one]
  · rw [if_neg hn, mul_zero]
    by_cases hnk : n ≤ k
    · rw [if_neg (by omega : ¬ (k - n = k - 2))]
    · by_cases hc : k - n = k - 2
      · rw [if_pos hc, Nat.choose_eq_zero_of_lt (by omega), Nat.cast_zero, mul_zero, map_zero]
      · rw [if_neg hc]


/-- The coefficients of `C a` lie in `A_ν` for `a ∈ A_ν`. -/
lemma coeff_C_mem_ambA {ν : ℕ} {a : Ambient F} (ha : a ∈ ambA F ν) (n : ℕ) :
    (Polynomial.C a : Polynomial (Ambient F)).coeff n ∈ ambA F ν := by
  rw [Polynomial.coeff_C]
  split_ifs with h
  · exact ha
  · exact ambA_zero_mem ν

/-! ## §5. The `tp` of `L^w · V` in terms of the `D_i` -/

/-- ★★★★★ **The `θ`-coefficient of `L^w·V` when `V` is a quadratic in `θ`.**  With
`V = D_0 + D_1·θ + D_2·θ²` (`tp_decomp`), `tp (L^w·V) j` is the three-term combination
`D_0·tp(L^w)j + D_1·tp(L^w)(j-1) + D_2·tp(L^w)(j-2)` (the shifts being the `θ`-powers). -/
lemma tp_L_pow_mul {w j : ℕ} {V : Polynomial (Ambient F)}
    (hV : ∀ n, V.coeff n ∈ ambA F 0) (hd : ∀ n, degNu F 0 (V.coeff n) ≤ 2) :
    tp F ((Polynomial.X - Polynomial.C (ambTheta F)) ^ w * V) j
      = tp F V 0 * tp F ((Polynomial.X - Polynomial.C (ambTheta F)) ^ w) j
        + tp F V 1 * (if 1 ≤ j then
            tp F ((Polynomial.X - Polynomial.C (ambTheta F)) ^ w) (j - 1) else 0)
        + tp F V 2 * (if 2 ≤ j then
            tp F ((Polynomial.X - Polynomial.C (ambTheta F)) ^ w) (j - 2) else 0) := by
  set L : Polynomial (Ambient F) := Polynomial.X - Polynomial.C (ambTheta F) with hL
  have hL0 : ∀ n, (L ^ w).coeff n ∈ ambA F 0 := fun n => by
    rw [hL]
    exact coeff_pow_mem_ambA (fun i => coeff_X_sub_C_mem_ambA_zero ambTheta_mem_ambA_zero i) w n
  have hD : ∀ i n, (tp F V i).coeff n ∈ ambA F 0 := fun i n =>
    ambF_subset_ambA_zero (F := F) (tp_coeff_mem_ambF F hV i n)
  have hDf : ∀ i n, (tp F V i).coeff n ∈ ambF F := fun i n => tp_coeff_mem_ambF F hV i n
  have hCθ : ∀ n, (Polynomial.C (ambTheta F) * L ^ w : Polynomial (Ambient F)).coeff n
      ∈ ambA F 0 := fun n =>
    coeff_mul_mem_ambA (coeff_C_mem_ambA F (ambTheta_mem_ambA F 0)) hL0 n
  have hCθ2 : ∀ n, (Polynomial.C ((ambTheta F) ^ 2) * L ^ w : Polynomial (Ambient F)).coeff n
      ∈ ambA F 0 := fun n =>
    coeff_mul_mem_ambA (coeff_C_mem_ambA F (ambA_pow_mem F 0 (ambTheta_mem_ambA F 0) 2)) hL0 n
  have hA : ∀ n, (tp F V 0 * L ^ w : Polynomial (Ambient F)).coeff n ∈ ambA F 0 :=
    fun n => coeff_mul_mem_ambA (hD 0) hL0 n
  have hB : ∀ n, (tp F V 1 * (Polynomial.C (ambTheta F) * L ^ w) :
      Polynomial (Ambient F)).coeff n ∈ ambA F 0 := fun n => coeff_mul_mem_ambA (hD 1) hCθ n
  have hCc : ∀ n, (tp F V 2 * (Polynomial.C ((ambTheta F) ^ 2) * L ^ w) :
      Polynomial (Ambient F)).coeff n ∈ ambA F 0 := fun n => coeff_mul_mem_ambA (hD 2) hCθ2 n
  have hExp : L ^ w * V = tp F V 0 * L ^ w + tp F V 1 * (Polynomial.C (ambTheta F) * L ^ w)
      + tp F V 2 * (Polynomial.C ((ambTheta F) ^ 2) * L ^ w) := by
    conv_lhs => rw [tp_decomp F hV hd]
    ring
  have hAB : ∀ n, (tp F V 0 * L ^ w + tp F V 1 * (Polynomial.C (ambTheta F) * L ^ w) :
      Polynomial (Ambient F)).coeff n ∈ ambA F 0 := fun n => by
    rw [Polynomial.coeff_add]
    exact ambA_add_mem F (hA n) (hB n)
  have hstep1 : tp F (tp F V 0 * L ^ w + tp F V 1 * (Polynomial.C (ambTheta F) * L ^ w)
      + tp F V 2 * (Polynomial.C ((ambTheta F) ^ 2) * L ^ w)) j
      = tp F (tp F V 0 * L ^ w + tp F V 1 * (Polynomial.C (ambTheta F) * L ^ w)) j
        + tp F (tp F V 2 * (Polynomial.C ((ambTheta F) ^ 2) * L ^ w)) j :=
    tp_add F hAB hCc j
  have hstep2 : tp F (tp F V 0 * L ^ w + tp F V 1 * (Polynomial.C (ambTheta F) * L ^ w)) j
      = tp F (tp F V 0 * L ^ w) j
        + tp F (tp F V 1 * (Polynomial.C (ambTheta F) * L ^ w)) j :=
    tp_add F hA hB j
  rw [hExp, hstep1, hstep2,
    tp_mul_const F (hDf 0) hL0 j, tp_mul_const F (hDf 1) hCθ j, tp_mul_const F (hDf 2) hCθ2 j]
  rw [show (Polynomial.C (ambTheta F) : Polynomial (Ambient F))
      = Polynomial.C ((ambTheta F) ^ 1) by rw [pow_one]]
  rw [tp_theta_pow_mul (N := 1) (y := L ^ w) F hL0 j,
    tp_theta_pow_mul (N := 2) (y := L ^ w) F hL0 j]


/-- ★★★★ **The specialization of `tp_L_pow_mul` at `j = w+1`** (the `θ`-read that gives
`D_1 = w·X·D_2`). -/
lemma tp_L_pow_mul_add_one {w : ℕ} {V : Polynomial (Ambient F)}
    (hV : ∀ n, V.coeff n ∈ ambA F 0) (hd : ∀ n, degNu F 0 (V.coeff n) ≤ 2)
    (hwe : (-1 : F) ^ w = 1) (hwo : (-1 : F) ^ (w - 1) = -1) (hw1 : 1 ≤ w) :
    tp F ((Polynomial.X - Polynomial.C (ambTheta F)) ^ w * V) (w + 1)
      = tp F V 1
        + tp F V 2 * (Polynomial.C (ambCoeff F (-(((w : ℕ)) : F))) * Polynomial.X) := by
  set L : Polynomial (Ambient F) := Polynomial.X - Polynomial.C (ambTheta F) with hL
  have hL0 : ∀ n, (L ^ w).coeff n ∈ ambA F 0 := fun n => by
    rw [hL]
    exact coeff_pow_mem_ambA (fun i => coeff_X_sub_C_mem_ambA_zero ambTheta_mem_ambA_zero i) w n
  have hD : ∀ i n, (tp F V i).coeff n ∈ ambA F 0 := fun i n =>
    ambF_subset_ambA_zero (F := F) (tp_coeff_mem_ambF F hV i n)
  have hDf : ∀ i n, (tp F V i).coeff n ∈ ambF F := fun i n => tp_coeff_mem_ambF F hV i n
  have hCθ : ∀ n, (Polynomial.C (ambTheta F) * L ^ w : Polynomial (Ambient F)).coeff n
      ∈ ambA F 0 := fun n =>
    coeff_mul_mem_ambA (coeff_C_mem_ambA F (ambTheta_mem_ambA F 0)) hL0 n
  have hCθ2 : ∀ n, (Polynomial.C ((ambTheta F) ^ 2) * L ^ w : Polynomial (Ambient F)).coeff n
      ∈ ambA F 0 := fun n =>
    coeff_mul_mem_ambA (coeff_C_mem_ambA F (ambA_pow_mem F 0 (ambTheta_mem_ambA F 0) 2)) hL0 n
  have hA : ∀ n, (tp F V 0 * L ^ w : Polynomial (Ambient F)).coeff n ∈ ambA F 0 :=
    fun n => coeff_mul_mem_ambA (hD 0) hL0 n
  have hB : ∀ n, (tp F V 1 * (Polynomial.C (ambTheta F) * L ^ w) :
      Polynomial (Ambient F)).coeff n ∈ ambA F 0 := fun n => coeff_mul_mem_ambA (hD 1) hCθ n
  have hCc : ∀ n, (tp F V 2 * (Polynomial.C ((ambTheta F) ^ 2) * L ^ w) :
      Polynomial (Ambient F)).coeff n ∈ ambA F 0 := fun n => coeff_mul_mem_ambA (hD 2) hCθ2 n
  have hAB : ∀ n, (tp F V 0 * L ^ w + tp F V 1 * (Polynomial.C (ambTheta F) * L ^ w) :
      Polynomial (Ambient F)).coeff n ∈ ambA F 0 := fun n => by
    rw [Polynomial.coeff_add]
    exact ambA_add_mem F (hA n) (hB n)
  have hExp : L ^ w * V = tp F V 0 * L ^ w + tp F V 1 * (Polynomial.C (ambTheta F) * L ^ w)
      + tp F V 2 * (Polynomial.C ((ambTheta F) ^ 2) * L ^ w) := by
    conv_lhs => rw [tp_decomp F hV hd]
    ring
  have hstep1 : tp F (tp F V 0 * L ^ w + tp F V 1 * (Polynomial.C (ambTheta F) * L ^ w)
      + tp F V 2 * (Polynomial.C ((ambTheta F) ^ 2) * L ^ w)) (w + 1)
      = tp F (tp F V 0 * L ^ w + tp F V 1 * (Polynomial.C (ambTheta F) * L ^ w)) (w + 1)
        + tp F (tp F V 2 * (Polynomial.C ((ambTheta F) ^ 2) * L ^ w)) (w + 1) :=
    tp_add F hAB hCc (w + 1)
  have hstep2 : tp F (tp F V 0 * L ^ w + tp F V 1 * (Polynomial.C (ambTheta F) * L ^ w)) (w + 1)
      = tp F (tp F V 0 * L ^ w) (w + 1)
        + tp F (tp F V 1 * (Polynomial.C (ambTheta F) * L ^ w)) (w + 1) :=
    tp_add F hA hB (w + 1)
  rw [hExp, hstep1, hstep2,
    tp_mul_const F (hDf 0) hL0 (w + 1), tp_mul_const F (hDf 1) hCθ (w + 1),
    tp_mul_const F (hDf 2) hCθ2 (w + 1),
    show (Polynomial.C (ambTheta F) : Polynomial (Ambient F))
      = Polynomial.C ((ambTheta F) ^ 1) by rw [pow_one],
    tp_theta_pow_mul (N := 1) (y := L ^ w) F hL0 (w + 1),
    tp_theta_pow_mul (N := 2) (y := L ^ w) F hL0 (w + 1),
    if_pos (by omega : 1 ≤ w + 1), if_pos (by omega : 2 ≤ w + 1),
    show w + 1 - 1 = w from by omega, show w + 1 - 2 = w - 1 from by omega,
    tp_X_sub_C_theta_pow_gt F (by omega : w < w + 1),
    tp_X_sub_C_theta_pow_self F (by omega : w ≠ 0) hwe,
    tp_X_sub_C_theta_pow_sub_one F hw1 hwo]
  ring

/-- ★★★★ **The specialization of `tp_L_pow_mul` at `j = w`** (the `θ`-read that gives
`D_0 = w·X·D_1 - C(w,2)·X²·D_2`). -/
lemma tp_L_pow_mul_self {w : ℕ} {V : Polynomial (Ambient F)}
    (hV : ∀ n, V.coeff n ∈ ambA F 0) (hd : ∀ n, degNu F 0 (V.coeff n) ≤ 2)
    (hwe : (-1 : F) ^ w = 1) (hwo : (-1 : F) ^ (w - 1) = -1) (hw2 : 2 ≤ w)
    (hw2' : (-1 : F) ^ (w - 2) = 1) :
    tp F ((Polynomial.X - Polynomial.C (ambTheta F)) ^ w * V) w
      = tp F V 0
        + tp F V 1 * (Polynomial.C (ambCoeff F (-(((w : ℕ)) : F))) * Polynomial.X)
        + tp F V 2 * (Polynomial.C (ambCoeff F ((((w.choose 2 : ℕ)) : F)))
            * Polynomial.X ^ 2) := by
  set L : Polynomial (Ambient F) := Polynomial.X - Polynomial.C (ambTheta F) with hL
  have hL0 : ∀ n, (L ^ w).coeff n ∈ ambA F 0 := fun n => by
    rw [hL]
    exact coeff_pow_mem_ambA (fun i => coeff_X_sub_C_mem_ambA_zero ambTheta_mem_ambA_zero i) w n
  have hD : ∀ i n, (tp F V i).coeff n ∈ ambA F 0 := fun i n =>
    ambF_subset_ambA_zero (F := F) (tp_coeff_mem_ambF F hV i n)
  have hDf : ∀ i n, (tp F V i).coeff n ∈ ambF F := fun i n => tp_coeff_mem_ambF F hV i n
  have hCθ : ∀ n, (Polynomial.C (ambTheta F) * L ^ w : Polynomial (Ambient F)).coeff n
      ∈ ambA F 0 := fun n =>
    coeff_mul_mem_ambA (coeff_C_mem_ambA F (ambTheta_mem_ambA F 0)) hL0 n
  have hCθ2 : ∀ n, (Polynomial.C ((ambTheta F) ^ 2) * L ^ w : Polynomial (Ambient F)).coeff n
      ∈ ambA F 0 := fun n =>
    coeff_mul_mem_ambA (coeff_C_mem_ambA F (ambA_pow_mem F 0 (ambTheta_mem_ambA F 0) 2)) hL0 n
  have hA : ∀ n, (tp F V 0 * L ^ w : Polynomial (Ambient F)).coeff n ∈ ambA F 0 :=
    fun n => coeff_mul_mem_ambA (hD 0) hL0 n
  have hB : ∀ n, (tp F V 1 * (Polynomial.C (ambTheta F) * L ^ w) :
      Polynomial (Ambient F)).coeff n ∈ ambA F 0 := fun n => coeff_mul_mem_ambA (hD 1) hCθ n
  have hCc : ∀ n, (tp F V 2 * (Polynomial.C ((ambTheta F) ^ 2) * L ^ w) :
      Polynomial (Ambient F)).coeff n ∈ ambA F 0 := fun n => coeff_mul_mem_ambA (hD 2) hCθ2 n
  have hAB : ∀ n, (tp F V 0 * L ^ w + tp F V 1 * (Polynomial.C (ambTheta F) * L ^ w) :
      Polynomial (Ambient F)).coeff n ∈ ambA F 0 := fun n => by
    rw [Polynomial.coeff_add]
    exact ambA_add_mem F (hA n) (hB n)
  have hExp : L ^ w * V = tp F V 0 * L ^ w + tp F V 1 * (Polynomial.C (ambTheta F) * L ^ w)
      + tp F V 2 * (Polynomial.C ((ambTheta F) ^ 2) * L ^ w) := by
    conv_lhs => rw [tp_decomp F hV hd]
    ring
  have hstep1 : tp F (tp F V 0 * L ^ w + tp F V 1 * (Polynomial.C (ambTheta F) * L ^ w)
      + tp F V 2 * (Polynomial.C ((ambTheta F) ^ 2) * L ^ w)) w
      = tp F (tp F V 0 * L ^ w + tp F V 1 * (Polynomial.C (ambTheta F) * L ^ w)) w
        + tp F (tp F V 2 * (Polynomial.C ((ambTheta F) ^ 2) * L ^ w)) w :=
    tp_add F hAB hCc w
  have hstep2 : tp F (tp F V 0 * L ^ w + tp F V 1 * (Polynomial.C (ambTheta F) * L ^ w)) w
      = tp F (tp F V 0 * L ^ w) w
        + tp F (tp F V 1 * (Polynomial.C (ambTheta F) * L ^ w)) w :=
    tp_add F hA hB w
  rw [hExp, hstep1, hstep2,
    tp_mul_const F (hDf 0) hL0 w, tp_mul_const F (hDf 1) hCθ w, tp_mul_const F (hDf 2) hCθ2 w,
    show (Polynomial.C (ambTheta F) : Polynomial (Ambient F))
      = Polynomial.C ((ambTheta F) ^ 1) by rw [pow_one],
    tp_theta_pow_mul (N := 1) (y := L ^ w) F hL0 w,
    tp_theta_pow_mul (N := 2) (y := L ^ w) F hL0 w,
    if_pos (by omega : 1 ≤ w), if_pos (by omega : 2 ≤ w),
    tp_X_sub_C_theta_pow_self F (by omega : w ≠ 0) hwe,
    tp_X_sub_C_theta_pow_sub_one F (by omega : 1 ≤ w) hwo,
    tp_X_sub_C_theta_pow_sub_two F hw2 hw2']
  ring

end ZagierHoffmanPositiveChar
