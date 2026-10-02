import Mathlib
import Submission.Work.PARIMPL2.Direct.oidDefs

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


set_option maxHeartbeats 2000000

namespace Work.PARIMPL2.Direct

noncomputable section

/-! ## Elementary trigonometric/cotangent facts on `(0, π/2]` -/

/-- For `0 < a ≤ π/2`, `a * cos a ≤ sin a`. -/
private lemma mul_cos_le_sin (a : ℝ) (ha0 : 0 < a) (ha : a ≤ Real.pi / 2) :
    a * Real.cos a ≤ Real.sin a := by
  rcases lt_or_eq_of_le ha with hlt | heq
  · have htan : a ≤ Real.tan a := Real.le_tan ha0.le hlt
    rw [Real.tan_eq_sin_div_cos] at htan
    rw [le_div_iff₀ (Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hlt⟩)] at htan
    linarith
  · rw [heq, Real.cos_pi_div_two, mul_zero, Real.sin_pi_div_two]; norm_num

/-- For `0 < a ≤ π/2`, `1/sin²a ≤ 1 + 1/a²`. -/
private lemma inv_sin_sq_le_one_add (u : ℝ) (hu0 : 0 < u) (hu : u ≤ Real.pi / 2) :
    1 / (Real.sin u) ^ 2 ≤ 1 + 1 / u ^ 2 := by
  have hsin_pos : 0 < Real.sin u := Real.sin_pos_of_pos_of_lt_pi hu0 (by linarith [hu, Real.pi_pos])
  have hcos_nn : 0 ≤ Real.cos u := Real.cos_nonneg_of_mem_Icc ⟨by linarith [Real.pi_pos], hu⟩
  have hkey : u * Real.cos u ≤ Real.sin u := mul_cos_le_sin u hu0 hu
  have hsquare : (u * Real.cos u) ^ 2 ≤ (Real.sin u) ^ 2 := by
    have h1 : 0 ≤ u * Real.cos u := mul_nonneg hu0.le hcos_nn
    have h2 := mul_self_le_mul_self h1 hkey
    simpa [sq] using h2
  have hcs := Real.sin_sq_add_cos_sq u
  have hsq : u ^ 2 ≤ (Real.sin u) ^ 2 * (u ^ 2 + 1) := by nlinarith [hsquare, hcs]
  rw [div_le_iff₀ (pow_pos hsin_pos 2)]
  have h1 : (1 + 1 / u ^ 2) * (Real.sin u) ^ 2 = ((u ^ 2 + 1) * (Real.sin u) ^ 2) / u ^ 2 := by
    field_simp
  rw [h1, le_div_iff₀ (by positivity : (0:ℝ) < u ^ 2)]
  linarith [hsq]

/-- For `0 < a ≤ π/2`, `a * (cos a / sin a) ≤ 1`. -/
private lemma mul_cot_le_one (a : ℝ) (ha0 : 0 < a) (ha : a ≤ Real.pi / 2) :
    a * (Real.cos a / Real.sin a) ≤ 1 := by
  have hsin : 0 < Real.sin a := Real.sin_pos_of_pos_of_lt_pi ha0 (by linarith [ha, Real.pi_pos])
  have h := mul_cos_le_sin a ha0 ha
  rw [← mul_div_assoc, div_le_one hsin]; exact h

/-! ## A one-step logarithmic comparison -/

/-- For `0 < b ≤ a` with `1/3 ≤ a - b`, `1/a ≤ 3*(log a - log b)`. -/
private lemma inv_le_log_step (a b : ℝ) (hb : 0 < b) (hba : b ≤ a) (hgap : 1/3 ≤ a - b) :
    1/a ≤ 3*(Real.log a - Real.log b) := by
  have ha : 0 < a := lt_of_lt_of_le hb hba
  have h : (a-b)/a ≤ Real.log a - Real.log b := by
    have h0 := Real.one_sub_inv_le_log_of_pos (show 0 < a/b by positivity)
    rw [inv_div, Real.log_div (ne_of_gt ha) (ne_of_gt hb)] at h0
    have h1 : (a-b)/a = 1 - b/a := by field_simp
    linarith [h0, h1.le, h1.ge]
  have h2 : 1/a ≤ 3*((a-b)/a) := by
    rw [div_le_iff₀ ha, show 3*((a-b)/a)*a = 3*(a-b) by field_simp]
    nlinarith [hgap]
  linarith [h, h2]

/-! ## Sums of `1/x²` along a decreasing, `1/3`-separated sequence -/

private lemma sum_inv_sq_le_decr (x : ℕ → ℝ) (p q : ℕ)
    (hdec : ∀ k, k < q → x (k+1) ≤ x k - 1/3)
    (hxpos : ∀ k, k ≤ q → 0 < x k) :
    ∑ i ∈ Finset.Ico p q, 1/(x i)^2 ≤ 3/x q := by
  have hq : 0 < x q := hxpos q le_rfl
  by_cases hpq : p ≤ q
  · have hstep : ∀ i ∈ Finset.Ico p q, 1/(x i)^2 ≤ 3*(1/(x (i+1)) - 1/(x i)) := by
      intro i hi
      have hi' := Finset.mem_Ico.mp hi
      have hxi : 0 < x i := hxpos i (le_of_lt hi'.2)
      have hxi1 : 0 < x (i+1) := hxpos (i+1) hi'.2
      have hd := hdec i (Finset.mem_Ico.mp hi).2
      have hsub : 1/(x (i+1)) - 1/(x i) = (x i - x (i+1))/(x i * x (i+1)) := by
        field_simp
      rw [hsub]
      rw [show 3 * ((x i - x (i+1))/(x i * x (i+1)))
          = 3*(x i - x (i+1))/(x i * x (i+1)) by ring]
      rw [le_div_iff₀ (by positivity : 0 < x i * x (i+1))]
      rw [show (1/(x i)^2) * (x i * x (i+1)) = x (i+1)/x i by field_simp]
      rw [div_le_iff₀ hxi]
      have h1 : 1/3 ≤ x i - x (i+1) := by linarith
      have h2 : x (i+1) ≤ x i := by linarith
      nlinarith [hxi, hxi1, h1, h2]
    calc ∑ i ∈ Finset.Ico p q, 1/(x i)^2
        ≤ ∑ i ∈ Finset.Ico p q, 3*(1/(x (i+1)) - 1/(x i)) := Finset.sum_le_sum hstep
      _ = 3 * ∑ i ∈ Finset.Ico p q, (1/(x (i+1)) - 1/(x i)) := by rw [Finset.mul_sum]
      _ = 3 * (1/(x q) - 1/(x p)) := by
            rw [Finset.sum_Ico_sub (fun i => 1/(x i)) hpq]
      _ ≤ 3/x q := by
            have h1 : (0:ℝ) ≤ 1/(x p) := by
              have : 0 < x p := hxpos p hpq
              positivity
            have h2 : 1/(x q) - 1/(x p) ≤ 1/(x q) := by linarith
            have h3 : 3 * (1/(x q) - 1/(x p)) ≤ 3 * (1/(x q)) :=
              mul_le_mul_of_nonneg_left h2 (by norm_num)
            rw [show 3*(1/(x q)) = 3/x q by ring] at h3
            exact h3
  · have hempty : Finset.Ico p q = ∅ := Finset.Ico_eq_empty (by omega)
    rw [hempty, Finset.sum_empty]
    positivity

/-! ## The chord bound for the exponential -/

private lemma exp_chord (B g : ℝ) (hB : 0 < B) (hg0 : 0 ≤ g) (hgB : g ≤ B) :
    Real.exp g - 1 ≤ ((Real.exp B - 1)/B) * g := by
  rcases eq_or_lt_of_le hg0 with h | h
  · subst h; simp
  · have hsec := ConvexOn.secant_mono convexOn_exp
      (Set.mem_univ (0:ℝ)) (Set.mem_univ g) (Set.mem_univ B) h.ne' (ne_of_gt hB) hgB
    rw [Real.exp_zero, sub_zero, sub_zero] at hsec
    rw [div_le_iff₀ h] at hsec
    linarith

/-! ## Logarithmic bounds for `R` and the `λ·log` term -/

private lemma log_le_div (R : ℝ) (hR : 128 ≤ R) : Real.log R ≤ R / 128 + 4 := by
  have h1 : 0 < R / 128 := by positivity
  have h2 : Real.log (R/128) ≤ R/128 - 1 := Real.log_le_sub_one_of_pos h1
  have h3 : Real.log R = Real.log 128 + Real.log (R/128) := by
    rw [← Real.log_mul (by norm_num : (128:ℝ) ≠ 0) (by positivity : R/128 ≠ 0)]
    congr 1; ring
  have h4 : Real.log 128 = 7 * Real.log 2 := by
    rw [show (128:ℝ) = 2^7 by norm_num, Real.log_pow]; norm_num
  have h5 : Real.log 2 ≤ 0.7 := by linarith [Real.log_two_lt_d9]
  rw [h3, h4]; linarith

private lemma log_2piR_le (R : ℝ) (hR : 128 ≤ R) :
    Real.log (2*Real.pi*R) ≤ R/128 + 7 := by
  have h2pi : Real.log (2*Real.pi) ≤ 3 := by
    have h1 : Real.log (2*Real.pi) ≤ Real.log 8 := by
      apply Real.log_le_log (by positivity)
      nlinarith [Real.pi_lt_four]
    have h2 : Real.log 8 = 3*Real.log 2 := by
      rw [show (8:ℝ) = 2^3 by norm_num, Real.log_pow]; norm_num
    have h3 : Real.log 2 ≤ 0.7 := by linarith [Real.log_two_lt_d9]
    linarith [h1, h2.le, h2.ge, h3]
  have hmul : Real.log (2*Real.pi) + Real.log R = Real.log (2*Real.pi*R) := by
    rw [Real.log_mul (by positivity : (2*Real.pi) ≠ 0) (ne_of_gt (by linarith : (0:ℝ) < R))]
  have := log_le_div R hR
  linarith [h2pi, hmul.le, hmul.ge, this]

private lemma lam_log_bound (lam R : ℝ) (hlam : 0 < lam) (hR : 128 ≤ R)
    (hlamR : lam * R^2 ≤ 1) :
    lam * Real.log (2 * Real.pi / (lam * (R + 8))) ≤ Real.log (2*Real.pi*R) / R^2 := by
  have hRpos : 0 < R := by linarith
  have hR2pos : (0:ℝ) < R^2 := by positivity
  have hR8pos : (0:ℝ) < R + 8 := by linarith
  set m : ℝ := lam * R^2 with hmdef
  have hm0 : 0 < m := by rw [hmdef]; positivity
  have hm1 : m ≤ 1 := by rw [hmdef]; exact hlamR
  have hlam_eq : lam = m / R^2 := by rw [hmdef]; field_simp
  have hmlog : -(m * Real.log m) ≤ 1 - m := by
    have h := Real.log_le_sub_one_of_pos (show 0 < 1/m by positivity)
    rw [Real.log_div one_ne_zero (ne_of_gt hm0), Real.log_one, zero_sub] at h
    have := mul_le_mul_of_nonneg_left h hm0.le
    have he : m * (1/m - 1) = 1 - m := by field_simp
    linarith [this, he.le, he.ge]
  have hlog2piR_ge1 : 1 ≤ Real.log (2*Real.pi*R) := by
    rw [Real.le_log_iff_exp_le (by positivity)]
    nlinarith [Real.exp_one_lt_three, Real.pi_gt_three, Real.pi_pos]
  have hRle : Real.log (R/(R+8)) ≤ 0 :=
    Real.log_nonpos (by positivity) ((div_le_one hR8pos).mpr (by linarith))
  have hpos1 : (0:ℝ) < 2*Real.pi*R := by positivity
  have hpos2 : (0:ℝ) < R/(R+8) := by positivity
  have hlog_eq : Real.log (2*Real.pi/(lam*(R+8)))
      = Real.log (2*Real.pi*R/m) + Real.log (R/(R+8)) := by
    rw [hlam_eq]
    have heq : 2 * Real.pi / (m / R^2 * (R+8)) = (2*Real.pi*R/m) * (R/(R+8)) := by
      field_simp
      try ring
    rw [heq, Real.log_mul (ne_of_gt (by positivity : (0:ℝ) < 2*Real.pi*R/m)) (ne_of_gt hpos2)]
  have hlogRm : Real.log (2*Real.pi*R/m) = Real.log (2*Real.pi*R) - Real.log m :=
    Real.log_div (ne_of_gt hpos1) (ne_of_gt hm0)
  rw [hlog_eq, hlam_eq]
  have hstep : (m/R^2) * (Real.log (2*Real.pi*R/m) + Real.log (R/(R+8)))
      ≤ (m/R^2) * Real.log (2*Real.pi*R/m) := by
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    linarith
  refine le_trans hstep ?_
  rw [hlogRm]
  rw [show (m/R^2)*(Real.log (2*Real.pi*R) - Real.log m)
      = (m*(Real.log (2*Real.pi*R) - Real.log m))/R^2 by ring]
  rw [div_le_div_iff₀ hR2pos hR2pos]
  have h2 : (1-m)*1 ≤ (1-m)*Real.log (2*Real.pi*R) :=
    mul_le_mul_of_nonneg_left hlog2piR_ge1 (by linarith)
  nlinarith [hmlog, h2, hm1]

/-! ## The final numeric inequality -/

private lemma arith_final (R : ℝ) (hR : 128 ≤ R) :
    18 * Real.pi * Real.log (2*Real.pi*R) / R^2 + 36/(R+8) + 48/(R+8)^2 ≤ 72/R := by
  have hRpos : 0 < R := by linarith
  have hR8 : (0:ℝ) < R + 8 := by linarith
  have hR2 : (0:ℝ) < R^2 := by positivity
  have hlog := log_2piR_le R hR
  have e1 : 18 * Real.pi * Real.log (2*Real.pi*R) / R^2
      ≤ 18*Real.pi*(R/128+7)/R^2 :=
    div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hlog (by positivity)) hR2.le
  have e2 : 36/(R+8) ≤ 36/R := div_le_div_of_nonneg_left (by norm_num) hRpos (by linarith)
  have e3 : 48/(R+8)^2 ≤ 48/R^2 :=
    div_le_div_of_nonneg_left (by norm_num) hR2 (by nlinarith [hR8])
  have hgoal2 : 18 * Real.pi * Real.log (2*Real.pi*R) / R^2 + 36/(R+8) + 48/(R+8)^2
      ≤ 18*Real.pi*(R/128+7)/R^2 + 36/R + 48/R^2 := by linarith [e1, e2, e3]
  have hgoal3 : 18*Real.pi*(R/128+7)/R^2 + 36/R + 48/R^2 ≤ 72/R := by
    have H : (18*Real.pi*(R/128+7)/R^2 + 36/R + 48/R^2) * R^2 ≤ (72/R)*R^2 := by
      rw [show (18*Real.pi*(R/128+7)/R^2 + 36/R + 48/R^2) * R^2
          = 18*Real.pi*(R/128+7) + 36*R + 48 by field_simp; try ring]
      rw [show (72/R)*R^2 = 72*R by field_simp]
      nlinarith [Real.pi_lt_four, Real.pi_pos, hR]
    exact le_of_mul_le_mul_right H hR2
  linarith [hgoal2, hgoal3]

/-- `1 ≤ exp x ↔ 0 ≤ x` -/
private lemma one_le_exp_iff' (x : ℝ) : 1 ≤ Real.exp x ↔ 0 ≤ x := by
  rw [← Real.exp_zero, Real.exp_le_exp]

/-! ## Main theorem -/

theorem oidArcPos (lam R cp : ℝ) (hlam : 0 < lam) (hR : 128 ≤ R) (hlamR : lam * R ^ 2 ≤ 1)
    (hcp : 0 ≤ cp)
    (n j0 : ℕ) (x y : ℕ → ℝ) (hj0 : j0 ≤ n)
    (hpos : ∀ j, j0 ≤ j → j < n → lam * x j ≤ Real.pi / 2)
    (hx1 : ∀ j ≤ n, R / 4 + 2 ≤ x j) (hx2 : ∀ j ≤ n, x j ≤ Real.pi / lam - R / 4)
    (hdec : ∀ j < n, x (j + 1) ≤ x j - 1 / 3)
    (hDpos : ∀ j ≤ n, 0 < Work.PARIMPL2.Direct.ocDen lam x y j)
    (hSn : |∑ j ∈ Finset.range n, Work.PARIMPL2.Direct.ocA lam x y j| ≤ 8 * (1 + Real.log R)) :
    ∑ j ∈ Finset.Ico j0 n, Work.PARIMPL2.Direct.ocA lam x y j *
      (Real.exp (∑ i ∈ Finset.Ico (j0 + 1) (j + 1), Work.PARIMPL2.Direct.oidCg lam cp x y i) - 1)
      ≤ 6 * (Real.exp (12 * cp / R) - 1) := by
  have hRpos : 0 < R := by linarith
  rcases Nat.eq_or_lt_of_le hj0 with hjn | hjn
  · subst hjn
    rw [Finset.Ico_self, Finset.sum_empty]
    have h1 : (0:ℝ) ≤ 12*cp/R := by positivity
    have h2 : 1 ≤ Real.exp (12*cp/R) := (one_le_exp_iff' _).mpr h1
    nlinarith
  rcases eq_or_lt_of_le hcp with hcp0 | hcp0
  · subst hcp0
    have hzero : ∀ j, (∑ i ∈ Finset.Ico (j0 + 1) (j + 1), oidCg lam 0 x y i) = 0 := by
      intro j; apply Finset.sum_eq_zero; intro i hi; rw [oidCg]; ring
    rw [Finset.sum_eq_zero (fun j hj => by rw [hzero j, Real.exp_zero, sub_self, mul_zero])]
    rw [show (12:ℝ)*0/R = 0 by ring, Real.exp_zero]
    norm_num
  -- ============ MAIN CASE ============
  have hxpos : ∀ j ≤ n, 0 < x j := fun j hj => by linarith [hx1 j hj, hRpos]
  have harcpos : ∀ j, j0 ≤ j → j < n → 0 < lam * x j := by
    intro j hj hjlt; have h := hxpos j (le_of_lt hjlt); positivity
  have hsinpos : ∀ j, j0 ≤ j → j < n → 0 < Real.sin (lam * x j) := by
    intro j hj hjlt
    have h1 := harcpos j hj hjlt
    have h2 := hpos j hj hjlt
    exact Real.sin_pos_of_pos_of_lt_pi h1 (by linarith [h2, Real.pi_pos])
  have hcosnn : ∀ j, j0 ≤ j → j < n → 0 ≤ Real.cos (lam * x j) := by
    intro j hj hjlt
    have h2 := hpos j hj hjlt
    have h1 := harcpos j hj hjlt
    exact Real.cos_nonneg_of_mem_Icc ⟨by linarith [h1, Real.pi_pos], h2⟩
  have hxn : R/4 + 2 ≤ x n := hx1 n le_rfl
  have hxnpos : 0 < x n := by linarith
  have hxj0pos : 0 < x j0 := by linarith [hx1 j0 hj0]
  -- x is antitone on [0,n]
  have hxanti : ∀ b, b ≤ n → ∀ a, a ≤ b → x b ≤ x a := by
    intro b
    induction b with
    | zero => intro _ a ha; simp only [Nat.le_zero] at ha; subst ha; exact le_rfl
    | succ b ih =>
      intro hb a ha
      rcases Nat.eq_or_lt_of_le ha with h | h
      · subst h; exact le_rfl
      · have hab : a ≤ b := by omega
        have hbn : b ≤ n := by omega
        have ih' := ih hbn a hab
        have hd : x (b+1) ≤ x b := by
          have := hdec b (Nat.lt_of_lt_of_le (Nat.lt_succ_self b) hb); linarith
        linarith
  -- n ≤ 3π/λ
  have htel : ∀ k ≤ n, x k + (k:ℝ)*(1/3) ≤ x 0 := by
    intro k hk
    induction k with
    | zero => simp
    | succ m ih =>
      have hmn : m ≤ n := le_trans (Nat.le_succ m) hk
      have ih' := ih hmn
      have hmlt : m < n := lt_of_lt_of_le (Nat.lt_succ_self m) hk
      have hd := hdec m hmlt
      have : ((m:ℝ)+1)*(1/3) = (m:ℝ)*(1/3) + 1/3 := by ring
      push_cast
      rw [this]; linarith
  have hn3 : (n:ℝ) ≤ 3*(Real.pi/lam) := by
    have h1 := htel n le_rfl
    have h2 := hx2 0 (Nat.zero_le n)
    have h3 := hx1 n le_rfl
    linarith
  have hnlam : (n:ℝ) * lam^2 ≤ 3*Real.pi*lam := by
    have h := mul_le_mul_of_nonneg_right hn3 (sq_nonneg lam)
    calc (n:ℝ)*lam^2 ≤ (3*(Real.pi/lam))*lam^2 := h
      _ = 3*Real.pi*lam := by field_simp
  -- L
  set L : ℝ := Real.log (x j0) - Real.log (x n) with hLdef
  have hLnn : 0 ≤ L := by
    rw [hLdef, ← Real.log_div (ne_of_gt hxj0pos) (ne_of_gt hxnpos)]
    apply Real.log_nonneg
    rw [le_div_iff₀ hxnpos]
    simpa using hxanti n le_rfl j0 hj0
  have hxj0top : x j0 ≤ Real.pi/(2*lam) := by
    have h := hpos j0 le_rfl hjn
    rw [le_div_iff₀ (by positivity : (0:ℝ) < 2*lam)]
    linarith
  have hLbound : L ≤ Real.log (2*Real.pi/(lam*(R+8))) := by
    rw [hLdef, ← Real.log_div (ne_of_gt hxj0pos) (ne_of_gt hxnpos)]
    apply Real.log_le_log (by positivity)
    have hratio : x j0 / x n ≤ 2*Real.pi/(lam*(R+8)) := by
      rw [div_le_iff₀ hxnpos]
      rw [show (2*Real.pi/(lam*(R+8)))*x n = 2*Real.pi*x n/(lam*(R+8)) by ring]
      rw [le_div_iff₀ (by positivity : (0:ℝ) < lam*(R+8))]
      have h1 : 2*lam*x j0 ≤ Real.pi := by
        have := mul_le_mul_of_nonneg_left hxj0top (by positivity : (0:ℝ) ≤ 2*lam)
        rw [show 2*lam*(Real.pi/(2*lam)) = Real.pi by field_simp] at this
        exact this
      have h2 : R+8 ≤ 4*x n := by linarith [hxn]
      nlinarith [h1, h2, Real.pi_pos, hlam, hxn]
    exact hratio
  have hlamL : lam * L ≤ Real.log (2*Real.pi*R) / R^2 := by
    have h1 : lam * L ≤ lam * Real.log (2*Real.pi/(lam*(R+8))) :=
      mul_le_mul_of_nonneg_left hLbound hlam.le
    exact le_trans h1 (lam_log_bound lam R hlam hR hlamR)
  -- named sequences
  set A : ℕ → ℝ := ocA lam x y with hAdef
  set Cg : ℕ → ℝ := oidCg lam cp x y with hCgdef
  set B : ℝ := 12*cp/R with hBdef
  have hBpos : 0 < B := by rw [hBdef]; positivity
  have hAnn : ∀ j, j0 ≤ j → j < n → 0 ≤ A j := by
    intro j hj hjlt
    have hs := hsinpos j hj hjlt
    have hc := hcosnn j hj hjlt
    have hD : 0 < ocDen lam x y j := hDpos j (le_of_lt hjlt)
    rw [hAdef, ocA]
    exact div_nonneg (mul_nonneg (mul_nonneg hlam.le hs.le) hc) hD.le
  have hAle : ∀ j, j0 ≤ j → j < n → A j ≤ 1/x j := by
    intro j hj hjlt
    have hs := hsinpos j hj hjlt
    have hc := hcosnn j hj hjlt
    have hD : 0 < ocDen lam x y j := hDpos j (le_of_lt hjlt)
    have hsj : 0 < x j := hxpos j (le_of_lt hjlt)
    have harccot : lam * x j * (Real.cos (lam*x j)/Real.sin (lam*x j)) ≤ 1 :=
      mul_cot_le_one (lam*x j) (harcpos j hj hjlt) (hpos j hj hjlt)
    have hDge : (Real.sin (lam*x j))^2 ≤ ocDen lam x y j := by
      rw [ocDen]; nlinarith [sq_nonneg (Real.sinh (lam*y j))]
    have hstep : A j ≤ lam * (Real.cos (lam*x j)/Real.sin (lam*x j)) := by
      rw [hAdef, ocA, div_le_iff₀ hD]
      have hquot : Real.sin (lam*x j) ≤ ocDen lam x y j / Real.sin (lam*x j) := by
        rw [le_div_iff₀ hs]
        simpa [pow_two] using hDge
      have hlamnn : 0 ≤ lam * Real.cos (lam*x j) := mul_nonneg hlam.le hc
      calc lam * Real.sin (lam*x j) * Real.cos (lam*x j)
          = (lam * Real.cos (lam*x j)) * Real.sin (lam*x j) := by ring
        _ ≤ (lam * Real.cos (lam*x j)) * (ocDen lam x y j / Real.sin (lam*x j)) :=
            mul_le_mul_of_nonneg_left hquot hlamnn
        _ = lam * (Real.cos (lam*x j)/Real.sin (lam*x j)) * ocDen lam x y j := by ring
    calc A j ≤ lam * (Real.cos (lam*x j)/Real.sin (lam*x j)) := hstep
      _ = (1/x j) * (lam * x j * (Real.cos (lam*x j)/Real.sin (lam*x j))) := by
            field_simp; try ring
      _ ≤ (1/x j) * 1 := mul_le_mul_of_nonneg_left harccot (by positivity)
      _ = 1/x j := by ring
  have hCgnn : ∀ i, i ≤ n → 0 ≤ Cg i := by
    intro i hin
    rw [hCgdef, oidCg]
    exact mul_nonneg hcp (add_nonneg (sq_nonneg lam)
      (div_nonneg (sq_nonneg lam) (hDpos i hin).le))
  have hCgle : ∀ i, j0 ≤ i → i < n → Cg i ≤ cp*(2*lam^2 + 1/(x i)^2) := by
    intro i hi hilt
    have hs := hsinpos i hi hilt
    have hD : 0 < ocDen lam x y i := hDpos i (le_of_lt hilt)
    have hDge : (Real.sin (lam*x i))^2 ≤ ocDen lam x y i := by
      rw [ocDen]; nlinarith [sq_nonneg (Real.sinh (lam*y i))]
    have his : 0 < lam * x i := harcpos i hi hilt
    have hbound : lam^2/ocDen lam x y i ≤ lam^2 + 1/(x i)^2 := by
      have h1 : lam^2/ocDen lam x y i ≤ lam^2/(Real.sin (lam*x i))^2 := by
        rw [div_le_div_iff₀ hD (pow_pos hs 2)]
        nlinarith [hDge, sq_nonneg lam]
      have h2 : lam^2/(Real.sin (lam*x i))^2 ≤ lam^2 + 1/(x i)^2 := by
        have h3 := inv_sin_sq_le_one_add (lam*x i) his (hpos i hi hilt)
        have h4 := mul_le_mul_of_nonneg_left h3 (sq_nonneg lam)
        rw [mul_add, mul_one] at h4
        rw [show lam^2 * (1/(lam*x i)^2) = 1/(x i)^2 by field_simp] at h4
        have e : lam^2/(Real.sin (lam*x i))^2 = lam^2 * (1/(Real.sin (lam*x i))^2) := by ring
        rw [e]; linarith [h4]
      linarith [h1, h2]
    rw [hCgdef, oidCg]
    exact mul_le_mul_of_nonneg_left (by linarith [hbound, sq_nonneg lam]) hcp
  -- pointwise G bound
  have hGbound : ∀ j, j0 ≤ j → j < n →
      (∑ i ∈ Finset.Ico (j0+1) (j+1), Cg i) ≤ cp*(2*lam^2*((j:ℝ) - j0) + 3/x (j+1)) := by
    intro j hj hjlt
    have hjn' : j + 1 ≤ n := by omega
    have hsum : (∑ i ∈ Finset.Ico (j0+1) (j+1), Cg i)
        ≤ ∑ i ∈ Finset.Ico (j0+1) (j+1), cp*(2*lam^2 + 1/(x i)^2) := by
      apply Finset.sum_le_sum
      intro i hi
      have hi' := Finset.mem_Ico.mp hi
      exact hCgle i (by omega) (by omega)
    refine le_trans hsum ?_
    rw [← Finset.mul_sum]
    rw [Finset.sum_add_distrib]
    have hconst : (∑ i ∈ Finset.Ico (j0+1) (j+1), 2*lam^2) = 2*lam^2*((j:ℝ) - j0) := by
      rw [Finset.sum_const, Nat.card_Ico, nsmul_eq_mul]
      have hcard : ((j+1 - (j0+1) : ℕ):ℝ) = (j:ℝ) - j0 := by
        rw [Nat.cast_sub (by omega)]; push_cast [Nat.cast_add, Nat.cast_one]; ring
      rw [hcard]; ring
    have hsum2 : (∑ i ∈ Finset.Ico (j0+1) (j+1), 1/(x i)^2) ≤ 3/x (j+1) :=
      sum_inv_sq_le_decr x (j0+1) (j+1) (fun k hk => hdec k (by omega))
        (fun k hk => hxpos k (le_trans hk hjn'))
    rw [hconst]
    exact mul_le_mul_of_nonneg_left (by linarith [hsum2]) hcp
  -- G ≤ B
  have hGleB : ∀ j, j0 ≤ j → j < n → (∑ i ∈ Finset.Ico (j0+1) (j+1), Cg i) ≤ B := by
    intro j hj hjlt
    have h := hGbound j hj hjlt
    have hjn' : j + 1 ≤ n := by omega
    have hjle : (j:ℝ) - j0 ≤ n := by
      have h1 : (j:ℝ) ≤ n := by exact_mod_cast le_of_lt hjlt
      have h2 : (0:ℝ) ≤ j0 := Nat.cast_nonneg j0
      linarith
    have hkey : 2*lam^2*((j:ℝ) - j0) + 3/x (j+1) ≤ 12/R := by
      have h2 : 2*lam^2*((j:ℝ) - j0) ≤ 2*lam^2*n := by
        have h4 : (0:ℝ) ≤ 2*lam^2 := by positivity
        nlinarith [hjle, h4]
      have h5 : 2*lam^2*n ≤ 6*Real.pi*lam := by nlinarith [hnlam]
      have h6 : 6*Real.pi*lam ≤ 6*Real.pi/R^2 := by
        have h7 : lam ≤ 1/R^2 := by rw [le_div_iff₀ (by positivity : (0:ℝ) < R^2)]; linarith
        have := mul_le_mul_of_nonneg_left h7 (by positivity : (0:ℝ) ≤ 6*Real.pi)
        rwa [mul_one_div] at this
      have h8 : 3/x (j+1) ≤ 12/(R+8) := by
        have h9 : 3/x (j+1) ≤ 3/(R/4+2) :=
          div_le_div_of_nonneg_left (by norm_num) (by linarith) (hx1 (j+1) hjn')
        have h10 : 3/(R/4+2) = 12/(R+8) := by field_simp; try ring
        linarith [h9, h10.le, h10.ge]
      have h11 : 6*Real.pi/R^2 + 12/(R+8) ≤ 12/R := by
        have H : (6*Real.pi/R^2 + 12/(R+8)) * (R^2*(R+8)) ≤ (12/R) * (R^2*(R+8)) := by
          have e : (6*Real.pi/R^2 + 12/(R+8)) * (R^2*(R+8)) = 6*Real.pi*(R+8) + 12*R^2 := by
            field_simp; try ring
          rw [e]
          have e2 : (12/R) * (R^2*(R+8)) = 12*R*(R+8) := by field_simp; try ring
          rw [e2]
          nlinarith [Real.pi_lt_four, hR]
        exact le_of_mul_le_mul_right H (by positivity)
      linarith [h2, h5, h6, h8, h11]
    rw [hBdef]
    refine le_trans h ?_
    refine (mul_le_mul_of_nonneg_left hkey hcp).trans (le_of_eq ?_)
    ring
  -- ∑ A_j ≤ 3 L
  have hsumAx : (∑ j ∈ Finset.Ico j0 n, A j) ≤ 3*L := by
    have hlogtel : (∑ j ∈ Finset.Ico j0 n, (Real.log (x j) - Real.log (x (j+1)))) = L := by
      have h := Finset.sum_Ico_sub (fun j => Real.log (x j)) hj0
      have h3 : (∑ j ∈ Finset.Ico j0 n, (Real.log (x j) - Real.log (x (j+1))))
          = - ∑ j ∈ Finset.Ico j0 n, (Real.log (x (j+1)) - Real.log (x j)) := by
        rw [← Finset.sum_neg_distrib]
        apply Finset.sum_congr rfl; intro j hj; ring
      rw [h3, h, hLdef]; ring
    calc (∑ j ∈ Finset.Ico j0 n, A j)
        ≤ ∑ j ∈ Finset.Ico j0 n, 3 * (Real.log (x j) - Real.log (x (j+1))) := by
          apply Finset.sum_le_sum
          intro j hj
          have hj' := Finset.mem_Ico.mp hj
          have h1 := hAle j hj'.1 hj'.2
          have hgap : 1/3 ≤ x j - x (j+1) := by have := hdec j hj'.2; linarith
          have h2 := inv_le_log_step (x j) (x (j+1)) (hxpos (j+1) (by omega))
            (by linarith [hdec j hj'.2]) hgap
          linarith [h1, h2]
      _ = 3 * L := by rw [← hlogtel, Finset.mul_sum]
  -- ∑ 1/x_{j+1}² ≤ 3/x_n + 1/x_n²
  have hsum_re : (∑ j ∈ Finset.Ico j0 n, 1/(x (j+1))^2) ≤ 3/x n + 1/(x n)^2 := by
    have hreindex : (∑ j ∈ Finset.Ico j0 n, 1/(x (j+1))^2)
        = ∑ k ∈ Finset.Ico (j0+1) (n+1), 1/(x k)^2 := by
      rw [Finset.sum_Ico_eq_sum_range, Finset.sum_Ico_eq_sum_range]
      apply Finset.sum_congr
      · rw [show n + 1 - (j0 + 1) = n - j0 by omega]
      · intro k hk
        rw [Nat.add_right_comm]
    rw [hreindex, Finset.sum_Ico_succ_top (by omega : j0 + 1 ≤ n)]
    have := sum_inv_sq_le_decr x (j0+1) n (fun k hk => hdec k hk) (fun k hk => hxpos k hk)
    linarith [this]
  -- split the main inner sum
  have hinner : (∑ j ∈ Finset.Ico j0 n, A j * (2*lam^2*((j:ℝ) - j0) + 3/x (j+1)))
      ≤ 18*Real.pi*Real.log (2*Real.pi*R)/R^2 + 36/(R+8) + 48/(R+8)^2 := by
    have hsplit : (∑ j ∈ Finset.Ico j0 n, A j * (2*lam^2*((j:ℝ) - j0) + 3/x (j+1)))
        = 2*lam^2*(∑ j ∈ Finset.Ico j0 n, A j * ((j:ℝ) - j0))
          + 3*(∑ j ∈ Finset.Ico j0 n, A j / x (j+1)) := by
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro j hj; ring
    rw [hsplit]
    have hterm1 : 2*lam^2*(∑ j ∈ Finset.Ico j0 n, A j * ((j:ℝ) - j0))
        ≤ 18*Real.pi*Real.log (2*Real.pi*R)/R^2 := by
      have h1 : (∑ j ∈ Finset.Ico j0 n, A j * ((j:ℝ) - j0)) ≤ n * (∑ j ∈ Finset.Ico j0 n, A j) := by
        rw [Finset.mul_sum]
        apply Finset.sum_le_sum
        intro j hj
        have hj' := Finset.mem_Ico.mp hj
        have ha := hAnn j hj'.1 hj'.2
        have hle : ((j:ℝ) - j0) ≤ n := by
          have h1 : (j:ℝ) ≤ n := by exact_mod_cast le_of_lt hj'.2
          have h2 : (0:ℝ) ≤ j0 := Nat.cast_nonneg j0
          linarith
        nlinarith [ha, hle]
      have h2 : (n:ℝ) * (∑ j ∈ Finset.Ico j0 n, A j) ≤ (n:ℝ) * (3*L) :=
        mul_le_mul_of_nonneg_left hsumAx (Nat.cast_nonneg n)
      calc 2*lam^2*(∑ j ∈ Finset.Ico j0 n, A j * ((j:ℝ) - j0))
          ≤ 2*lam^2*((n:ℝ) * (∑ j ∈ Finset.Ico j0 n, A j)) :=
            mul_le_mul_of_nonneg_left h1 (by positivity)
        _ ≤ 2*lam^2*((n:ℝ)*(3*L)) := mul_le_mul_of_nonneg_left h2 (by positivity)
        _ = 6*((n:ℝ)*lam^2)*L := by ring
        _ ≤ 6*(3*Real.pi*lam)*L :=
            mul_le_mul_of_nonneg_right (by linarith [hnlam]) (by linarith [hLnn])
        _ = 18*Real.pi*(lam*L) := by ring
        _ ≤ 18*Real.pi*(Real.log (2*Real.pi*R)/R^2) :=
            mul_le_mul_of_nonneg_left hlamL (by positivity)
        _ = 18*Real.pi*Real.log (2*Real.pi*R)/R^2 := by ring
    have hterm2 : 3*(∑ j ∈ Finset.Ico j0 n, A j / x (j+1)) ≤ 9/x n + 3/(x n)^2 := by
      have h1 : (∑ j ∈ Finset.Ico j0 n, A j / x (j+1))
          ≤ ∑ j ∈ Finset.Ico j0 n, 1/(x (j+1))^2 := by
        apply Finset.sum_le_sum
        intro j hj
        have hj' := Finset.mem_Ico.mp hj
        have hxj' : 0 < x j := hxpos j (le_of_lt hj'.2)
        have hxn' : 0 < x (j+1) := hxpos (j+1) (by omega)
        have hle1 : A j ≤ 1/x j := hAle j hj'.1 hj'.2
        have hle2 : 1/x j ≤ 1/x (j+1) :=
          one_div_le_one_div_of_le hxn' (by linarith [hdec j hj'.2])
        have h3 : A j / x (j+1) ≤ (1/x (j+1))/x (j+1) :=
          div_le_div_of_nonneg_right (by linarith [hle1, hle2]) hxn'.le
        calc A j / x (j+1) ≤ (1/x (j+1))/x (j+1) := h3
          _ = 1/(x (j+1))^2 := by field_simp
      have h2 : 3*(∑ j ∈ Finset.Ico j0 n, 1/(x (j+1))^2) ≤ 3*(3/x n + 1/(x n)^2) :=
        mul_le_mul_of_nonneg_left hsum_re (by norm_num)
      have h3 : 3*(3/x n + 1/(x n)^2) = 9/x n + 3/(x n)^2 := by ring
      linarith [h1, h2, h3.le, h3.ge, mul_le_mul_of_nonneg_left h1 (by norm_num : (0:ℝ) ≤ 3)]
    have hx8 : 9/x n ≤ 36/(R+8) := by
      have h1 : 9/x n ≤ 9/(R/4+2) := div_le_div_of_nonneg_left (by norm_num) (by linarith) hxn
      have h2 : 9/(R/4+2) = 36/(R+8) := by field_simp; try ring
      linarith [h1, h2.le, h2.ge]
    have hx8' : 3/(x n)^2 ≤ 48/(R+8)^2 := by
      have h1 : 3/(x n)^2 ≤ 3/(R/4+2)^2 :=
        div_le_div_of_nonneg_left (by norm_num) (by positivity) (pow_le_pow_left₀ (by linarith) hxn 2)
      have h2 : 3/(R/4+2)^2 = 48/(R+8)^2 := by field_simp; try ring
      linarith [h1, h2.le, h2.ge]
    linarith [hterm1, hterm2, hx8, hx8']
  -- main sum bound
  have hGsum : (∑ j ∈ Finset.Ico j0 n, A j * (∑ i ∈ Finset.Ico (j0+1) (j+1), Cg i)) ≤ cp*(72/R) := by
    calc (∑ j ∈ Finset.Ico j0 n, A j * (∑ i ∈ Finset.Ico (j0+1) (j+1), Cg i))
        ≤ ∑ j ∈ Finset.Ico j0 n, A j * (cp*(2*lam^2*((j:ℝ) - j0) + 3/x (j+1))) := by
          apply Finset.sum_le_sum
          intro j hj
          have hj' := Finset.mem_Ico.mp hj
          exact mul_le_mul_of_nonneg_left (hGbound j hj'.1 hj'.2) (hAnn j hj'.1 hj'.2)
      _ = cp * (∑ j ∈ Finset.Ico j0 n, A j * (2*lam^2*((j:ℝ) - j0) + 3/x (j+1))) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl; intro j hj; ring
      _ ≤ cp * (72/R) := by
          apply mul_le_mul_of_nonneg_left _ hcp
          linarith [hinner, arith_final R hR]
  -- pointwise exponential bound
  have hpoint : (∑ j ∈ Finset.Ico j0 n, A j * (Real.exp (∑ i ∈ Finset.Ico (j0+1) (j+1), Cg i) - 1))
      ≤ ((Real.exp B - 1)/B) * (∑ j ∈ Finset.Ico j0 n, A j * (∑ i ∈ Finset.Ico (j0+1) (j+1), Cg i)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro j hj
    have hj' := Finset.mem_Ico.mp hj
    have hAnn' := hAnn j hj'.1 hj'.2
    have hGnn : 0 ≤ ∑ i ∈ Finset.Ico (j0+1) (j+1), Cg i :=
      Finset.sum_nonneg (fun i hi => hCgnn i (by have hh := (Finset.mem_Ico.mp hi).2; omega))
    have hGle := hGleB j hj'.1 hj'.2
    have hc := exp_chord B (∑ i ∈ Finset.Ico (j0+1) (j+1), Cg i) hBpos hGnn hGle
    calc A j * (Real.exp (∑ i ∈ Finset.Ico (j0+1) (j+1), Cg i) - 1)
        ≤ A j * (((Real.exp B - 1)/B) * (∑ i ∈ Finset.Ico (j0+1) (j+1), Cg i)) :=
          mul_le_mul_of_nonneg_left hc hAnn'
      _ = ((Real.exp B - 1)/B) * (A j * (∑ i ∈ Finset.Ico (j0+1) (j+1), Cg i)) := by ring
  have hfinal : ((Real.exp B - 1)/B) * (cp*(72/R)) = 6*(Real.exp (12*cp/R) - 1) := by
    rw [hBdef]
    field_simp
    ring
  calc ∑ j ∈ Finset.Ico j0 n, A j * (Real.exp (∑ i ∈ Finset.Ico (j0+1) (j+1), Cg i) - 1)
      ≤ ((Real.exp B - 1)/B) * (∑ j ∈ Finset.Ico j0 n, A j * (∑ i ∈ Finset.Ico (j0+1) (j+1), Cg i)) := hpoint
    _ ≤ ((Real.exp B - 1)/B) * (cp*(72/R)) := by
          apply mul_le_mul_of_nonneg_left hGsum
          exact div_nonneg (sub_nonneg.mpr ((one_le_exp_iff' B).mpr hBpos.le)) hBpos.le
    _ = 6*(Real.exp (12*cp/R) - 1) := hfinal

end

end Work.PARIMPL2.Direct
