import Mathlib

namespace Work.Crux

open Filter Metric
open scoped Topology ContDiff

noncomputable section

/-- Mathlib's smooth bump centred at `0`: it is `1` on `[-1,1]` and `0` off `(-2,2)`. -/
noncomputable def Vb : ContDiffBump (0 : ℝ) := ⟨1, 2, by norm_num, by norm_num⟩

/-- The bump as a plain function. -/
noncomputable def w : ℝ → ℝ := Vb

lemma w_contDiff : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) w := by
  simpa only [w] using (Vb.contDiff (n := ⊤))

lemma w_zero {t : ℝ} (h : 2 ≤ |t|) : w t = 0 := by
  refine Vb.zero_of_le_dist ?_
  rw [Real.dist_eq, sub_zero]; exact h

lemma w_one {t : ℝ} (h : |t| ≤ 1) : w t = 1 := by
  refine Vb.one_of_mem_closedBall ?_
  rwa [Metric.mem_closedBall, Real.dist_eq, sub_zero]

/-- A sum of binomial coefficients weighted by the derivative bounds `M`. -/
noncomputable def Cb (M : ℕ → ℝ) (k : ℕ) : ℝ :=
  ∑ j ∈ Finset.range (k + 1), (k.choose j : ℝ) * M (k - j)

lemma descFactorial_le_factorial (n k : ℕ) : n.descFactorial k ≤ n.factorial := by
  rcases le_or_gt k n with h | h
  · rw [Nat.descFactorial_eq_div h]; exact Nat.div_le_self _ _
  · rw [Nat.descFactorial_eq_zero_iff_lt.mpr h]; exact Nat.zero_le _

lemma Cb_nonneg {M : ℕ → ℝ} (hM : ∀ l, 0 ≤ M l) (k : ℕ) : 0 ≤ Cb M k := by
  rw [Cb]; exact Finset.sum_nonneg (fun j _ => mul_nonneg (by positivity) (hM _))

/-- The scalar function `y ↦ y ^ i / i ! * w y`. -/
noncomputable def hp (i : ℕ) : ℝ → ℝ := fun y => (y ^ i / (i.factorial : ℝ)) * w y

lemma hp_contDiff (i : ℕ) : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (hp i) := by
  unfold hp
  exact (contDiff_id.pow i).div_const _ |>.mul w_contDiff

/-- The scaling factor `4 ^ k * (1 + ‖a k‖)`. -/
noncomputable def L {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (a : ℕ → E) (k : ℕ) : ℝ := (4 : ℝ) ^ k * (1 + ‖a k‖)

lemma L_pos {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (a : ℕ → E) (k : ℕ) : 0 < L a k := by
  rw [L]; exact mul_pos (pow_pos (by norm_num) k) (by positivity)

lemma one_le_L {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (a : ℕ → E) (k : ℕ) : 1 ≤ L a k := by
  rw [L]
  have h1 : (1 : ℝ) ≤ (4 : ℝ) ^ k := one_le_pow₀ (by norm_num)
  have h2 : (1 : ℝ) ≤ 1 + ‖a k‖ := le_add_of_nonneg_right (norm_nonneg _)
  calc (1 : ℝ) = 1 * 1 := by ring
    _ ≤ (4 : ℝ) ^ k * (1 + ‖a k‖) := mul_le_mul h1 h2 zero_le_one (by positivity)

lemma norm_a_mul_four_pow_le_L {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (a : ℕ → E) (k : ℕ) : ‖a k‖ * (4 : ℝ) ^ k ≤ L a k := by
  rw [L]
  calc ‖a k‖ * (4 : ℝ) ^ k ≤ (1 + ‖a k‖) * (4 : ℝ) ^ k :=
        mul_le_mul_of_nonneg_right (le_add_of_nonneg_left zero_le_one) (by positivity)
    _ = (4 : ℝ) ^ k * (1 + ‖a k‖) := by ring

lemma contDiff_of_le_top {f : ℝ → ℝ} (h : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f) (k : ℕ) :
    ContDiff ℝ (↑k) f := h.of_le (by exact_mod_cast (le_top : (k : ℕ∞) ≤ ⊤))

/-- The `k`-th term of the series defining `H`. -/
noncomputable def T {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (a : ℕ → E) (k : ℕ) : ℝ → E :=
  fun x => (((L a k) ^ k)⁻¹ * hp k (L a k * x)) • a k

lemma T_contDiff {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (a : ℕ → E) (k : ℕ) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (T a k) := by
  unfold T
  exact ContDiff.smul_const
    (contDiff_const.mul ((hp_contDiff k).comp (contDiff_const.mul contDiff_id))) (a k)

lemma norm_iteratedDeriv_pow_div_le (i j : ℕ) (y : ℝ) :
    ‖iteratedDeriv j (fun z : ℝ => z ^ i / (i.factorial : ℝ)) y‖ ≤ |y| ^ (i - j) := by
  rw [iteratedDeriv_div_const (f := fun z : ℝ => z ^ i) (c := (i.factorial : ℝ)), iteratedDeriv_pow]
  simp only [Real.norm_eq_abs, abs_mul, abs_div, abs_pow,
    abs_of_nonneg (by positivity : (0 : ℝ) ≤ (i.factorial : ℝ)),
    abs_of_nonneg (by positivity : (0 : ℝ) ≤ ((i.descFactorial j : ℕ) : ℝ))]
  have hle : (i.descFactorial j : ℝ) / (i.factorial : ℝ) ≤ 1 := by
    rw [div_le_one (by positivity)]; exact_mod_cast descFactorial_le_factorial i j
  calc (i.descFactorial j : ℝ) * |y| ^ (i - j) / (i.factorial : ℝ)
      = ((i.descFactorial j : ℝ) / (i.factorial : ℝ)) * |y| ^ (i - j) := by ring
    _ ≤ 1 * |y| ^ (i - j) := mul_le_mul_of_nonneg_right hle (by positivity)
    _ = |y| ^ (i - j) := one_mul _

lemma hpow_deriv_bound {M : ℕ → ℝ} (hM : ∀ l t, ‖iteratedDeriv l w t‖ ≤ M l)
    (i k : ℕ) (y : ℝ) : ‖iteratedDeriv k (hp i) y‖ ≤ (2 : ℝ) ^ i * Cb M k := by
  have hMn : ∀ l, 0 ≤ M l := fun l => le_trans (norm_nonneg _) (hM l 0)
  unfold hp
  rcases le_or_gt |y| 2 with hy | hy
  · have hgm : ContDiffAt ℝ (↑k) (fun z : ℝ => z ^ i / (i.factorial : ℝ)) y := by fun_prop
    have hwm : ContDiffAt ℝ (↑k) w y := (contDiff_of_le_top w_contDiff k).contDiffAt
    rw [show (fun z : ℝ => (z ^ i / (i.factorial : ℝ)) * w z)
          = (fun z : ℝ => z ^ i / (i.factorial : ℝ)) * w from rfl,
        iteratedDeriv_mul hgm hwm]
    calc ‖∑ j ∈ Finset.range (k + 1),
            (k.choose j : ℝ) * iteratedDeriv j (fun z : ℝ => z ^ i / (i.factorial : ℝ)) y
              * iteratedDeriv (k - j) w y‖
        ≤ ∑ j ∈ Finset.range (k + 1),
            ‖(k.choose j : ℝ) * iteratedDeriv j (fun z : ℝ => z ^ i / (i.factorial : ℝ)) y
              * iteratedDeriv (k - j) w y‖ := norm_sum_le _ _
      _ ≤ ∑ j ∈ Finset.range (k + 1), (k.choose j : ℝ) * ((2 : ℝ) ^ i) * M (k - j) := by
          apply Finset.sum_le_sum; intro j hj
          have hA : ‖iteratedDeriv j (fun z : ℝ => z ^ i / (i.factorial : ℝ)) y‖ ≤ (2 : ℝ) ^ i := by
            refine le_trans (norm_iteratedDeriv_pow_div_le i j y) ?_
            calc |y| ^ (i - j) ≤ 2 ^ (i - j) := pow_le_pow_left₀ (abs_nonneg y) hy _
              _ ≤ 2 ^ i := pow_le_pow_right₀ (by norm_num) (Nat.sub_le i j)
          have hB : ‖iteratedDeriv (k - j) w y‖ ≤ M (k - j) := hM _ _
          rw [show (k.choose j : ℝ)
                * iteratedDeriv j (fun z : ℝ => z ^ i / (i.factorial : ℝ)) y
                * iteratedDeriv (k - j) w y
              = (k.choose j : ℝ)
                * (iteratedDeriv j (fun z : ℝ => z ^ i / (i.factorial : ℝ)) y
                  * iteratedDeriv (k - j) w y) by ring,
              norm_mul, norm_mul, Real.norm_of_nonneg (by positivity : (0 : ℝ) ≤ (k.choose j : ℝ))]
          rw [show (k.choose j : ℝ) * 2 ^ i * M (k - j)
                = (k.choose j : ℝ) * (2 ^ i * M (k - j)) by ring]
          exact mul_le_mul_of_nonneg_left (mul_le_mul hA hB (norm_nonneg _) (by positivity)) (by positivity)
      _ = (2 : ℝ) ^ i * Cb M k := by
          rw [Cb, Finset.mul_sum]; apply Finset.sum_congr rfl; intro j hj; ring
  · have hzero : (fun z : ℝ => (z ^ i / (i.factorial : ℝ)) * w z) =ᶠ[𝓝 y] (fun _ => 0) := by
      have hopen : IsOpen {z : ℝ | 2 < |z|} := isOpen_lt continuous_const continuous_abs
      filter_upwards [hopen.mem_nhds hy] with z hz
      rw [w_zero (le_of_lt hz), mul_zero]
    have h0 : iteratedDeriv k (fun z : ℝ => (z ^ i / (i.factorial : ℝ)) * w z) y = 0 := by
      have hthis : iteratedDeriv k (fun z : ℝ => (z ^ i / (i.factorial : ℝ)) * w z) y
          = iteratedDeriv k (fun _ : ℝ => (0 : ℝ)) y :=
        (Filter.EventuallyEq.iteratedDeriv hzero k).eq_of_nhds
      rw [hthis, iteratedDeriv_const]; simp
    rw [h0, norm_zero]
    exact mul_nonneg (by positivity) (Cb_nonneg hMn k)

lemma T_deriv_bound {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {M : ℕ → ℝ} (hM : ∀ l t, ‖iteratedDeriv l w t‖ ≤ M l) (a : ℕ → E) (k i : ℕ) (x : ℝ) :
    ‖iteratedDeriv k (T a i) x‖ ≤ ‖a i‖ * ((L a i) ^ k / (L a i) ^ i) * ((2 : ℝ) ^ i * Cb M k) := by
  have hkey : iteratedDeriv k (T a i) x
      = (((L a i) ^ i)⁻¹ * ((L a i) ^ k * iteratedDeriv k (hp i) (L a i * x))) • a i := by
    unfold T
    have hcont : ContDiffAt ℝ (↑k)
        (fun x : ℝ => ((L a i) ^ i)⁻¹ * hp i (L a i * x)) x :=
      (contDiff_of_le_top
        (contDiff_const.mul ((hp_contDiff i).comp (contDiff_const.mul contDiff_id))) k).contDiffAt
    rw [iteratedDeriv_smul_const hcont (a i)]
    rw [iteratedDeriv_const_mul_field ((L a i) ^ i)⁻¹ (fun x : ℝ => hp i (L a i * x))]
    rw [iteratedDeriv_comp_const_smul (contDiff_of_le_top (hp_contDiff i) k) (L a i)]
    simp only [smul_eq_mul]
  rw [hkey, norm_smul]
  have hLp : 0 < L a i := L_pos a i
  have hA : 0 ≤ (L a i) ^ k / (L a i) ^ i :=
    div_nonneg (pow_nonneg (le_of_lt hLp) k) (pow_nonneg (le_of_lt hLp) i)
  have hmn : 0 ≤ ‖a i‖ := norm_nonneg _
  have hd : ‖iteratedDeriv k (hp i) (L a i * x)‖ ≤ (2 : ℝ) ^ i * Cb M k := hpow_deriv_bound hM i k _
  have hnorms : ‖(((L a i) ^ i)⁻¹ * ((L a i) ^ k * iteratedDeriv k (hp i) (L a i * x)))‖
      = ((L a i) ^ k / (L a i) ^ i) * ‖iteratedDeriv k (hp i) (L a i * x)‖ := by
    rw [Real.norm_eq_abs, abs_mul, abs_mul,
        abs_of_nonneg (inv_nonneg.mpr (pow_nonneg (le_of_lt hLp) i)),
        abs_of_nonneg (pow_nonneg (le_of_lt hLp) k), Real.norm_eq_abs]
    rw [show ((L a i) ^ i)⁻¹ * ((L a i) ^ k * |iteratedDeriv k (hp i) (L a i * x)|)
          = ((L a i) ^ k / (L a i) ^ i) * |iteratedDeriv k (hp i) (L a i * x)| by
        rw [div_eq_mul_inv]; ring]
  rw [hnorms, show ‖a i‖ * ((L a i) ^ k / (L a i) ^ i) * ((2 : ℝ) ^ i * Cb M k)
        = ((L a i) ^ k / (L a i) ^ i) * ((2 : ℝ) ^ i * Cb M k) * ‖a i‖ by ring]
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hd hA) hmn

/-- The bound on `‖a i‖` for `i ≤ k`. -/
noncomputable def cA {E : Type*} [NormedAddCommGroup E] (a : ℕ → E) (k : ℕ) : ℝ :=
  1 + ∑ i ∈ Finset.range (k + 1), ‖a i‖

/-- The bound on `L a i` for `i ≤ k`. -/
noncomputable def cL {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (a : ℕ → E) (k : ℕ) : ℝ :=
  1 + ∑ i ∈ Finset.range (k + 1), L a i

/-- The summable dominating sequence. -/
noncomputable def bnd {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (M : ℕ → ℝ) (a : ℕ → E) (k i : ℕ) : ℝ :=
  (1 / 2 : ℝ) ^ i * Cb M k + if i ≤ k then cA a k * 2 ^ k * (cL a k) ^ k * Cb M k else 0

lemma cA_nonneg {E : Type*} [NormedAddCommGroup E] (a : ℕ → E) (k : ℕ) : 0 ≤ cA a k := by
  rw [cA]; exact add_nonneg zero_le_one (Finset.sum_nonneg (fun _ _ => norm_nonneg _))

lemma cL_nonneg {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (a : ℕ → E) (k : ℕ) :
    0 ≤ cL a k := by
  rw [cL]; exact add_nonneg zero_le_one (Finset.sum_nonneg (fun j _ => le_of_lt (L_pos a j)))

lemma norm_a_le_cA {E : Type*} [NormedAddCommGroup E] (a : ℕ → E) {i k : ℕ} (h : i ≤ k) :
    ‖a i‖ ≤ cA a k := by
  rw [cA]
  calc ‖a i‖ ≤ ∑ j ∈ Finset.range (k + 1), ‖a j‖ :=
        Finset.single_le_sum (fun j _ => norm_nonneg _) (Finset.mem_range.mpr (Nat.lt_succ_of_le h))
    _ ≤ 1 + ∑ j ∈ Finset.range (k + 1), ‖a j‖ := le_add_of_nonneg_left zero_le_one

lemma L_le_cL {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (a : ℕ → E) {i k : ℕ}
    (h : i ≤ k) : L a i ≤ cL a k := by
  rw [cL]
  calc L a i ≤ ∑ j ∈ Finset.range (k + 1), L a j :=
        Finset.single_le_sum (fun j _ => le_of_lt (L_pos a j)) (Finset.mem_range.mpr (Nat.lt_succ_of_le h))
    _ ≤ 1 + ∑ j ∈ Finset.range (k + 1), L a j := le_add_of_nonneg_left zero_le_one

lemma norm_iteratedFDeriv_T_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {M : ℕ → ℝ} (hM : ∀ l t, ‖iteratedDeriv l w t‖ ≤ M l) (a : ℕ → E) (k i : ℕ) (x : ℝ) :
    ‖iteratedFDeriv ℝ k (T a i) x‖ ≤ bnd M a k i := by
  have hMn : ∀ l, 0 ≤ M l := fun l => le_trans (norm_nonneg _) (hM l 0)
  have hCb : 0 ≤ Cb M k := Cb_nonneg hMn k
  have hLp : 0 < L a i := L_pos a i
  have hL1 : 1 ≤ L a i := one_le_L a i
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv]
  rcases le_or_gt i k with hik | hik
  · refine le_trans (T_deriv_bound hM a k i x) ?_
    rw [bnd, if_pos hik]
    refine le_trans ?_ (le_add_of_nonneg_left (mul_nonneg (by positivity : (0 : ℝ) ≤ (1 / 2) ^ i) hCb))
    have hpow : (L a i) ^ k / (L a i) ^ i = (L a i) ^ (k - i) := by
      rw [div_eq_mul_inv, ← pow_sub₀ (L a i) (ne_of_gt hLp) hik]
    have hle1 : (L a i) ^ (k - i) ≤ (cL a k) ^ k := by
      calc (L a i) ^ (k - i) ≤ (L a i) ^ k := pow_le_pow_right₀ hL1 (Nat.sub_le k i)
        _ ≤ (cL a k) ^ k := pow_le_pow_left₀ (le_of_lt hLp) (L_le_cL a hik) k
    have hle2 : (2 : ℝ) ^ i ≤ 2 ^ k := pow_le_pow_right₀ (by norm_num) hik
    calc ‖a i‖ * ((L a i) ^ k / (L a i) ^ i) * ((2 : ℝ) ^ i * Cb M k)
        = (‖a i‖ * (L a i) ^ (k - i)) * ((2 : ℝ) ^ i * Cb M k) := by rw [hpow]
      _ ≤ (cA a k * (cL a k) ^ k) * ((2 : ℝ) ^ k * Cb M k) := by
          apply mul_le_mul
          · exact mul_le_mul (norm_a_le_cA a hik) hle1 (by positivity) (cA_nonneg a k)
          · exact mul_le_mul_of_nonneg_right hle2 hCb
          · positivity
          · exact mul_nonneg (cA_nonneg a k) (pow_nonneg (cL_nonneg a k) k)
      _ = cA a k * 2 ^ k * (cL a k) ^ k * Cb M k := by ring
  · refine le_trans (T_deriv_bound hM a k i x) ?_
    rw [bnd, if_neg (not_le.mpr hik), add_zero]
    have hpow : (L a i) ^ k / (L a i) ^ i = ((L a i) ^ (i - k))⁻¹ := by
      rw [div_eq_mul_inv]
      rw [show (L a i) ^ i = (L a i) ^ k * (L a i) ^ (i - k) by
            rw [← pow_add, Nat.add_sub_of_le (le_of_lt hik)]]
      field_simp
    have hle : ‖a i‖ * (4 : ℝ) ^ i ≤ (L a i) ^ (i - k) := by
      refine le_trans (norm_a_mul_four_pow_le_L a i) ?_
      calc L a i = (L a i) ^ 1 := (pow_one _).symm
        _ ≤ (L a i) ^ (i - k) := pow_le_pow_right₀ hL1 (Nat.succ_le_iff.mpr (Nat.sub_pos_iff_lt.mpr hik))
    have hmain : ‖a i‖ * ((L a i) ^ (i - k))⁻¹ * (2 : ℝ) ^ i ≤ (1 / 2 : ℝ) ^ i := by
      have hB : 0 < (L a i) ^ (i - k) := pow_pos hLp _
      rw [show ‖a i‖ * ((L a i) ^ (i - k))⁻¹ * (2 : ℝ) ^ i
            = ‖a i‖ * (2 : ℝ) ^ i / (L a i) ^ (i - k) by ring]
      rw [div_le_iff₀ hB]
      have hkey : (1 / 2 : ℝ) ^ i * (4 : ℝ) ^ i = (2 : ℝ) ^ i := by rw [← mul_pow]; norm_num
      calc ‖a i‖ * (2 : ℝ) ^ i = (1 / 2 : ℝ) ^ i * (‖a i‖ * (4 : ℝ) ^ i) := by
            rw [show (1 / 2 : ℝ) ^ i * (‖a i‖ * (4 : ℝ) ^ i)
                  = ‖a i‖ * ((1 / 2 : ℝ) ^ i * (4 : ℝ) ^ i) by ring, hkey]
        _ ≤ (1 / 2 : ℝ) ^ i * (L a i) ^ (i - k) := mul_le_mul_of_nonneg_left hle (by positivity)
    calc ‖a i‖ * ((L a i) ^ k / (L a i) ^ i) * ((2 : ℝ) ^ i * Cb M k)
        = (‖a i‖ * ((L a i) ^ (i - k))⁻¹ * (2 : ℝ) ^ i) * Cb M k := by rw [hpow]; ring
      _ ≤ (1 / 2 : ℝ) ^ i * Cb M k := mul_le_mul_of_nonneg_right hmain hCb

/-- Summability of the dominating sequence. -/
lemma summable_bnd {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (M : ℕ → ℝ) (a : ℕ → E) (k : ℕ) : Summable (bnd M a k) := by
  have h1 : Summable (fun i : ℕ => (1 / 2 : ℝ) ^ i * Cb M k) :=
    (summable_geometric_of_norm_lt_one (x := (1 / 2 : ℝ)) (by norm_num)).mul_right (Cb M k)
  have h2 : Summable (fun i : ℕ =>
      if i ≤ k then cA a k * 2 ^ k * (cL a k) ^ k * Cb M k else 0) := by
    refine summable_of_ne_finset_zero (s := Finset.range (k + 1)) (fun b hb => ?_)
    rw [if_neg]
    simp only [Finset.mem_range, not_lt] at hb
    omega
  exact h1.add h2

/-- Near `0`, the `i`-th term is the monomial `x ^ i / i ! • a i`. -/
lemma T_eventuallyEq {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (a : ℕ → E) (i : ℕ) :
    T a i =ᶠ[𝓝 (0 : ℝ)] (fun x => (x ^ i / (i.factorial : ℝ)) • a i) := by
  have hmem : {x : ℝ | |L a i * x| ≤ 1} ∈ 𝓝 (0 : ℝ) := by
    have hopen : IsOpen {x : ℝ | |L a i * x| < 1} := by
      rw [show {x : ℝ | |L a i * x| < 1} = (fun x : ℝ => L a i * x) ⁻¹' (Set.Ioo (-1) 1) by
            ext x; rw [Set.mem_ofPred_eq, Set.mem_preimage, Set.mem_Ioo, abs_lt]]
      exact isOpen_Ioo.preimage (continuous_const.mul continuous_id)
    exact Filter.mem_of_superset (hopen.mem_nhds (by simp)) (by
      intro x hx
      simp only [Set.mem_ofPred_eq] at hx ⊢
      exact le_of_lt hx)
  filter_upwards [hmem] with x hx
  unfold T hp
  rw [w_one hx, mul_one]
  congr 1
  rw [mul_pow]
  rw [show ((L a i) ^ i)⁻¹ * ((L a i) ^ i * x ^ i / (i.factorial : ℝ))
        = (((L a i) ^ i)⁻¹ * (L a i) ^ i) * (x ^ i / (i.factorial : ℝ)) by ring,
      inv_mul_cancel₀ (pow_ne_zero i (ne_of_gt (L_pos a i))), one_mul]

/-- The `k`-th derivative at `0` of `x ↦ x ^ i / i !`. -/
lemma iteratedDeriv_pow_div_zero (i k : ℕ) :
    iteratedDeriv k (fun x : ℝ => x ^ i / (i.factorial : ℝ)) 0 = if i = k then 1 else 0 := by
  rw [iteratedDeriv_div_const (f := fun x : ℝ => x ^ i) (c := (i.factorial : ℝ)),
      iteratedDeriv_fun_pow_zero]
  by_cases h : i = k
  · subst h; simp [Nat.factorial_ne_zero]
  · rw [if_neg (Ne.symm h), if_neg h]; simp

/-- The `k`-th derivative at `0` of the `i`-th term. -/
lemma iteratedDeriv_T_zero {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (a : ℕ → E) (k i : ℕ) :
    iteratedDeriv k (T a i) 0 = if i = k then a i else 0 := by
  have hEq : iteratedDeriv k (T a i)
      =ᶠ[𝓝 (0 : ℝ)] iteratedDeriv k (fun x => (x ^ i / (i.factorial : ℝ)) • a i) :=
    (T_eventuallyEq a i).iteratedDeriv k
  rw [hEq.eq_of_nhds]
  rw [iteratedDeriv_smul_const (f := fun x : ℝ => x ^ i / (i.factorial : ℝ)) (v := a i)
        (by fun_prop)]
  rw [iteratedDeriv_pow_div_zero]
  by_cases h : i = k
  · subst h; simp
  · simp [h]

theorem exists_contDiff_iteratedDeriv {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] (a : ℕ → E) :
    ∃ H : ℝ → E, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) H ∧
      ∀ k : ℕ, iteratedDeriv k H 0 = a k := by
  -- Choose a global bound for the derivatives of the bump.
  have hMex : ∀ l : ℕ, ∃ M : ℝ, 0 ≤ M ∧ ∀ t : ℝ, ‖iteratedDeriv l w t‖ ≤ M := fun l => by
    have hwcs : HasCompactSupport w := by simpa only [w] using Vb.hasCompactSupport
    have hcs : HasCompactSupport (iteratedFDeriv ℝ l w) := hwcs.iteratedFDeriv (𝕜 := ℝ) l
    have hcont : Continuous (iteratedFDeriv ℝ l w) :=
      w_contDiff.continuous_iteratedFDeriv (m := l)
        (by exact_mod_cast (le_top : (l : ℕ∞) ≤ ⊤))
    have hc : IsCompact (Set.range (iteratedFDeriv ℝ l w)) := hcs.isCompact_range hcont
    obtain ⟨r, hr⟩ := hc.isBounded.subset_closedBall (0 : ℝ [×l]→L[ℝ] ℝ)
    refine ⟨max r 0, le_max_right _ _, fun t => ?_⟩
    have hmem : iteratedFDeriv ℝ l w t ∈ Metric.closedBall (0 : ℝ [×l]→L[ℝ] ℝ) r :=
      hr (Set.mem_range_self t)
    rw [Metric.mem_closedBall, dist_zero_right] at hmem
    rw [← norm_iteratedFDeriv_eq_norm_iteratedDeriv]
    exact le_trans hmem (le_max_left _ _)
  choose M hMnn hMbd using hMex
  refine ⟨fun x => ∑' i, T a i x, ?_, ?_⟩
  · refine contDiff_tsum (𝕜 := ℝ) (N := (⊤ : ℕ∞)) (f := T a) (v := bnd M a)
      (fun i => T_contDiff a i) (fun k _ => summable_bnd M a k) ?_
    intro k i x _
    exact norm_iteratedFDeriv_T_le hMbd a k i x
  · intro k
    have htsum : iteratedFDeriv ℝ k (fun x => ∑' i, T a i x) 0
        = ∑' i, iteratedFDeriv ℝ k (T a i) 0 :=
      iteratedFDeriv_tsum_apply (𝕜 := ℝ) (N := (⊤ : ℕ∞)) (f := T a) (v := bnd M a)
        (fun i => T_contDiff a i) (fun k _ => summable_bnd M a k)
        (fun k i x _ => norm_iteratedFDeriv_T_le hMbd a k i x) (k := k) le_top 0
    have h1 : iteratedDeriv k (fun x => ∑' i, T a i x) 0
        = (ContinuousMultilinearMap.piFieldEquiv ℝ (Fin k) E).symm
            (iteratedFDeriv ℝ k (fun x => ∑' i, T a i x) 0) := by
      rw [iteratedDeriv_eq_equiv_comp]; rfl
    calc iteratedDeriv k (fun x => ∑' i, T a i x) 0
        = (ContinuousMultilinearMap.piFieldEquiv ℝ (Fin k) E).symm
            (iteratedFDeriv ℝ k (fun x => ∑' i, T a i x) 0) := h1
      _ = (ContinuousMultilinearMap.piFieldEquiv ℝ (Fin k) E).symm
            (∑' i, iteratedFDeriv ℝ k (T a i) 0) := by rw [htsum]
      _ = ∑' i, (ContinuousMultilinearMap.piFieldEquiv ℝ (Fin k) E).symm
            (iteratedFDeriv ℝ k (T a i) 0) :=
          ContinuousLinearEquiv.map_tsum
            ((ContinuousMultilinearMap.piFieldEquiv ℝ (Fin k) E).symm.toContinuousLinearEquiv)
      _ = ∑' i, iteratedDeriv k (T a i) 0 := by
          apply tsum_congr; intro i; rw [iteratedDeriv_eq_equiv_comp]; rfl
      _ = ∑' i, (if i = k then a i else 0) := by
          apply tsum_congr; intro i; exact iteratedDeriv_T_zero a k i
      _ = a k := by
          rw [tsum_eq_single k (fun b hb => if_neg hb)]; simp

end

end Work.Crux
