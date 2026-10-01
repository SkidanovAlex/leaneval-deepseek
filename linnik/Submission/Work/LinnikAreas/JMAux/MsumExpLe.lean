import Mathlib

namespace Work.LinnikAreas.JMAux

/-- Bound on a finite geometric sum over `ℕ`: for `0 ≤ r < 1`, the sum of `r^i`
over any finset of natural numbers is at most the full infinite geometric series. -/
lemma geom_finset_le {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (s : Finset ℕ) :
    ∑ i ∈ s, r^i ≤ (1 - r)⁻¹ := by
  have hsum : Summable (fun i : ℕ => r^i) := summable_geometric_of_lt_one hr0 hr1
  have h := Summable.sum_le_tsum s (fun i _ => pow_nonneg hr0 i) hsum
  rwa [tsum_geometric_of_lt_one hr0 hr1] at h

/-- Geometric bound with a lower bound `t` on the index set: if every `m ∈ s`
satisfies `t ≤ m` then `∑_{m∈s} r^m ≤ r^t / (1 - r)` for `0 ≤ r < 1`. -/
lemma geom_finset_shift_le {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) {s : Finset ℕ} {t : ℕ}
    (ht : ∀ m ∈ s, t ≤ m) :
    ∑ m ∈ s, r^m ≤ r^t * (1 - r)⁻¹ := by
  have hdecomp : ∑ m ∈ s, r^m = r^t * ∑ m ∈ s, r^(m-t) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro m hm
    rw [← pow_add]
    congr 1
    have := ht m hm; omega
  rw [hdecomp]
  apply mul_le_mul_of_nonneg_left _ (pow_nonneg hr0 t)
  have hinj : ∀ a ∈ s, ∀ b ∈ s, a - t = b - t → a = b := by
    intro a ha b hb hab
    have ha' := ht a ha; have hb' := ht b hb; omega
  have himg : ∑ j ∈ s.image (fun m => m - t), r^j = ∑ m ∈ s, r^(m-t) := Finset.sum_image hinj
  rw [← himg]
  exact geom_finset_le hr0 hr1 _

lemma MsumExpLe (q : ℕ) (hq : 2 ≤ q) {L : ℝ} (hLp : 0 < L) (hLdef : L = Real.log (q:ℝ))
    {s : Finset ℕ} (hs1 : ∀ m ∈ s, L/5 < (m:ℝ)+1) :
    (∑ m ∈ s, Real.exp (-(49/10) * (m:ℝ)) * (q:ℝ) ^ ((2451/1000) * (((m:ℝ)+1)/L)))
      ≤ 400 * (q:ℝ)^(-(19/40:ℝ)) := by
  have hqpos : (0:ℝ) < (q:ℝ) := by
    have : 0 < q := by omega
    exact_mod_cast this
  have hterm : ∀ m : ℕ, Real.exp (-(49/10) * (m:ℝ)) * (q:ℝ) ^ ((2451/1000) * (((m:ℝ)+1)/L))
      = Real.exp (2451/1000) * (Real.exp (-(2449/1000)))^m := by
    intro m
    have key : (q:ℝ) ^ ((2451/1000) * (((m:ℝ)+1)/L)) = Real.exp ((2451/1000)*((m:ℝ)+1)) := by
      rw [Real.rpow_def_of_pos hqpos]
      congr 1
      rw [← hLdef]
      field_simp
    rw [key, ← Real.exp_add]
    rw [show -(49/10) * (m:ℝ) + (2451/1000)*((m:ℝ)+1) = (2451/1000) + (m:ℝ)*(-(2449/1000)) by ring]
    rw [Real.exp_add, Real.exp_nat_mul]
  have h49 : Real.exp (49/10) ≤ 243 := by
    have h1 : Real.exp (49/10) ≤ Real.exp 5 := Real.exp_le_exp.mpr (by norm_num)
    have h2 : Real.exp 5 = Real.exp 1 ^ 5 := by rw [← Real.exp_nat_mul]; norm_num
    rw [h2] at h1
    have h3 : Real.exp 1 ^ 5 < 3 ^ 5 :=
      pow_lt_pow_left₀ Real.exp_one_lt_three (le_of_lt (Real.exp_pos 1)) (by norm_num)
    norm_num at h3
    linarith
  have h_rle : Real.exp (-(2449/1000)) ≤ 1/4 := by
    have hexp2 : (4:ℝ) < Real.exp 2 := by
      have h : Real.exp 2 = Real.exp 1 ^ 2 := by rw [← Real.exp_nat_mul]; norm_num
      rw [h]; nlinarith [Real.exp_one_gt_two, Real.exp_pos 1]
    have h1 : Real.exp (-(2449/1000)) < Real.exp (-2) := Real.exp_lt_exp.mpr (by norm_num)
    have h2 : Real.exp (-2) = (Real.exp 2)⁻¹ := by rw [Real.exp_neg]
    have h3 : (Real.exp 2)⁻¹ < (4:ℝ)⁻¹ := (inv_lt_inv₀ (Real.exp_pos 2) (by norm_num)).mpr hexp2
    rw [h2] at h1
    have : (4:ℝ)⁻¹ = 1/4 := by norm_num
    linarith [h3, this]
  have hr0 : 0 ≤ Real.exp (-(2449/1000)) := le_of_lt (Real.exp_pos _)
  have hr1 : Real.exp (-(2449/1000)) < 1 := by
    rw [← Real.exp_zero]
    exact Real.exp_lt_exp.mpr (by norm_num)
  have hrpos : (0:ℝ) < 1 - Real.exp (-(2449/1000)) := by linarith
  have hr_inv_le : (1 - Real.exp (-(2449/1000)))⁻¹ ≤ 4/3 := by
    have h34 : (3/4:ℝ) ≤ 1 - Real.exp (-(2449/1000)) := by linarith
    have h := (inv_le_inv₀ hrpos (by norm_num : (0:ℝ) < 3/4)).mpr h34
    have : ((3/4:ℝ))⁻¹ = 4/3 := by norm_num
    linarith [h, this]
  have htle : ∀ m ∈ s, Nat.ceil (L/5 - 1) ≤ m := by
    intro m hm
    apply Nat.ceil_le.mpr
    have h := hs1 m hm
    linarith
  have htce : (L/5 - 1 : ℝ) ≤ (Nat.ceil (L/5 - 1) : ℝ) := Nat.le_ceil _
  have hbound1 : Real.exp (2451/1000) * (Real.exp (-(2449/1000)))^(Nat.ceil (L/5-1))
      ≤ Real.exp (49/10 - 2449*L/5000) := by
    rw [← Real.exp_nat_mul, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    nlinarith [htce, hLp]
  have hbound2 : Real.exp (49/10 - 2449*L/5000) ≤ 243 * Real.exp (-(19/40)*L) := by
    calc Real.exp (49/10 - 2449*L/5000)
        = Real.exp (49/10) * Real.exp (-(2449*L/5000)) := by
            rw [show 49/10 - 2449*L/5000 = 49/10 + (-(2449*L/5000)) by ring, Real.exp_add]
      _ ≤ 243 * Real.exp (-(2449*L/5000)) := mul_le_mul_of_nonneg_right h49 (le_of_lt (Real.exp_pos _))
      _ ≤ 243 * Real.exp (-(19/40)*L) := by
            apply mul_le_mul_of_nonneg_left _ (by norm_num)
            apply Real.exp_le_exp.mpr
            nlinarith [hLp]
  have hmain : Real.exp (2451/1000) * (∑ m ∈ s, (Real.exp (-(2449/1000)))^m)
      ≤ 400 * Real.exp (-(19/40)*L) := by
    have hsumb : ∑ m ∈ s, (Real.exp (-(2449/1000)))^m
        ≤ (Real.exp (-(2449/1000)))^(Nat.ceil (L/5-1)) * (1 - Real.exp (-(2449/1000)))⁻¹ :=
      geom_finset_shift_le hr0 hr1 htle
    have hA0 : (0:ℝ) ≤ Real.exp (2451/1000) := le_of_lt (Real.exp_pos _)
    have hinv0 : (0:ℝ) ≤ (1 - Real.exp (-(2449/1000)))⁻¹ := le_of_lt (inv_pos.mpr hrpos)
    have he0 : (0:ℝ) ≤ Real.exp (-(19/40)*L) := le_of_lt (Real.exp_pos _)
    calc Real.exp (2451/1000) * (∑ m ∈ s, (Real.exp (-(2449/1000)))^m)
        ≤ Real.exp (2451/1000) * ((Real.exp (-(2449/1000)))^(Nat.ceil (L/5-1))
            * (1 - Real.exp (-(2449/1000)))⁻¹) :=
            mul_le_mul_of_nonneg_left hsumb hA0
      _ = (Real.exp (2451/1000) * (Real.exp (-(2449/1000)))^(Nat.ceil (L/5-1)))
            * (1 - Real.exp (-(2449/1000)))⁻¹ := by ring
      _ ≤ Real.exp (49/10 - 2449*L/5000) * (1 - Real.exp (-(2449/1000)))⁻¹ :=
            mul_le_mul_of_nonneg_right hbound1 hinv0
      _ ≤ Real.exp (49/10 - 2449*L/5000) * (4/3) :=
            mul_le_mul_of_nonneg_left hr_inv_le (le_of_lt (Real.exp_pos _))
      _ = (4/3) * Real.exp (49/10 - 2449*L/5000) := by ring
      _ ≤ (4/3) * (243 * Real.exp (-(19/40)*L)) :=
            mul_le_mul_of_nonneg_left hbound2 (by norm_num)
      _ = ((4/3) * 243) * Real.exp (-(19/40)*L) := by ring
      _ ≤ 400 * Real.exp (-(19/40)*L) :=
            mul_le_mul_of_nonneg_right (by norm_num) he0
  have hsum_eq : (∑ m ∈ s, Real.exp (-(49/10) * (m:ℝ)) * (q:ℝ) ^ ((2451/1000) * (((m:ℝ)+1)/L)))
      = Real.exp (2451/1000) * (∑ m ∈ s, (Real.exp (-(2449/1000)))^m) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro m hm
    exact hterm m
  rw [hsum_eq]
  rw [show (q:ℝ)^(-(19/40:ℝ)) = Real.exp (-(19/40) * L) by
    rw [Real.rpow_def_of_pos hqpos, ← hLdef]; congr 1; ring]
  exact hmain

end Work.LinnikAreas.JMAux
