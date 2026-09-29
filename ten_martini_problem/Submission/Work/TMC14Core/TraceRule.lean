import Mathlib
import Submission.Work.TMC14Core.Weyl

open Matrix
open Work.TMC14Core

noncomputable section

namespace Work.TMC14Core

namespace TraceRuleAux

/-! ### Arithmetic of `Nat` division and remainder -/

theorem traceModSucc (q A : ℕ) (_hq : 0 < q) : (A % q + 1) % q = (A + 1) % q := by
  have hA : q * (A / q) + A % q = A := Nat.div_add_mod A q
  have hA1 : A + 1 = (A % q + 1) + q * (A / q) := by
    conv_lhs => rw [← hA]
    ring
  rw [hA1]
  exact (Nat.add_mul_mod_self_left (A % q + 1) q (A / q)).symm

theorem traceDivSucc (q A : ℕ) (hq : 0 < q) :
    (A + 1) / q = A / q + (if A % q + 1 < q then 0 else 1) := by
  have hA : q * (A / q) + A % q = A := Nat.div_add_mod A q
  have hA1 : A + 1 = (A % q + 1) + q * (A / q) := by
    conv_lhs => rw [← hA]
    ring
  have hx : (A % q + 1) / q = if A % q + 1 < q then 0 else 1 := by
    rcases Nat.lt_or_ge (A % q + 1) q with h | h
    · rw [if_pos h, Nat.div_eq_of_lt h]
    · have h' : A % q + 1 = q := by
        have hm := Nat.mod_lt A hq
        omega
      rw [if_neg (by omega), h', Nat.div_self hq]
  rw [hA1, Nat.add_mul_div_left (A % q + 1) (A / q) hq, hx, add_comm]

theorem traceDvdOfModEq (q m i : ℕ) (h : (i + m) % q = i) : q ∣ m := by
  have h1 := Nat.div_add_mod (i + m) q
  rw [h] at h1
  rw [Nat.add_comm (q * ((i + m) / q)) i] at h1
  exact ⟨(i + m) / q, (Nat.add_left_cancel h1).symm⟩

/-! ### Powers of the cyclic shift `U = wU q k` -/

theorem wU_pow_entry (q : ℕ) (k : ℝ) (hq : 0 < q) :
    ∀ (n : ℕ) (i j : Fin q),
      (wU q k ^ n) i j
        = if (i.val + n) % q = j.val then wShiftBeta k ^ ((i.val + n) / q) else 0 := by
  intro n
  induction n with
  | zero =>
    intro i j
    rw [pow_zero, Matrix.one_apply]
    have hmod : (i.val + 0) % q = i.val := by
      rw [Nat.add_zero, Nat.mod_eq_of_lt i.isLt]
    by_cases hij : i = j
    · rw [if_pos hij, if_pos (by rw [← hij]; exact hmod), Nat.add_zero,
        Nat.div_eq_of_lt i.isLt, pow_zero]
    · rw [if_neg hij, if_neg]
      intro hh
      rw [Nat.add_zero, Nat.mod_eq_of_lt i.isLt] at hh
      exact hij (Fin.ext hh)
  | succ n ih =>
    intro i j
    rw [pow_succ, Matrix.mul_apply]
    set l0 : Fin q := ⟨(i.val + n) % q, Nat.mod_lt _ hq⟩ with hl0
    have hl0v : l0.val = (i.val + n) % q := by rw [hl0]
    have hsingle : (∑ l : Fin q, (wU q k ^ n) i l * wU q k l j)
        = (wU q k ^ n) i l0 * wU q k l0 j := by
      apply Finset.sum_eq_single l0
      · intro l _ hl
        rw [ih i l, if_neg]
        · ring
        · intro hh
          exact hl (Fin.ext (by rw [hl0v, ← hh]))
      · intro h
        exact absurd (Finset.mem_univ l0) h
    rw [hsingle, ih i l0, if_pos hl0v.symm, wU_apply, hl0v]
    have hcond : (((i.val + n) % q + 1) % q = j.val) ↔ ((i.val + (n + 1)) % q = j.val) := by
      rw [traceModSucc q (i.val + n) hq, Nat.add_assoc]
    have hdiv : (i.val + (n + 1)) / q
        = (i.val + n) / q + (if (i.val + n) % q + 1 < q then 0 else 1) := by
      rw [← Nat.add_assoc, traceDivSucc q (i.val + n) hq]
    by_cases hc : (i.val + (n + 1)) % q = j.val
    · rw [if_pos (hcond.mpr hc), if_pos hc]
      by_cases hlt : (i.val + n) % q + 1 < q
      · rw [if_pos hlt, hdiv, if_pos hlt, add_zero, mul_one]
      · rw [if_neg hlt, hdiv, if_neg hlt, ← pow_succ]
    · rw [if_neg (fun hh => hc (hcond.mp hh)), if_neg hc, mul_zero]

theorem wU_pow_scalar (q : ℕ) (k : ℝ) (hq : 0 < q) {m : ℕ} (hm : q ∣ m) :
    wU q k ^ m = (wShiftBeta k ^ (m / q)) • 1 := by
  obtain ⟨t, rfl⟩ := hm
  ext i j
  rw [wU_pow_entry q k hq (q * t) i j, Matrix.smul_apply, smul_eq_mul, Matrix.one_apply]
  have hmul : (q * t) / q = t := Nat.mul_div_right t hq
  have hmod : (i.val + q * t) % q = i.val := by
    rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt i.isLt]
  have hdiv : (i.val + q * t) / q = t := by
    rw [Nat.add_mul_div_left _ _ hq, Nat.div_eq_of_lt i.isLt, zero_add]
  rw [hmod, hdiv, hmul]
  by_cases hij : i = j
  · rw [if_pos (by rw [hij]), if_pos hij, mul_one]
  · rw [if_neg (fun hh => hij (Fin.ext hh)), if_neg hij, mul_zero]

theorem wU_pow_scalar_mul (q : ℕ) (k : ℝ) (hq : 0 < q) (t : ℕ) :
    wU q k ^ (q * t) = (wShiftBeta k ^ t) • 1 := by
  rw [wU_pow_scalar q k hq ⟨t, rfl⟩, Nat.mul_div_right t hq]

theorem wU_pow_diag_zero (q : ℕ) (k : ℝ) (hq : 0 < q) {m : ℕ} (hm : ¬ q ∣ m) (i : Fin q) :
    (wU q k ^ m) i i = 0 := by
  rw [wU_pow_entry q k hq m i i, if_neg]
  exact fun hh => hm (traceDvdOfModEq q m i.val hh)

/-! ### Divisibility conversions -/

theorem traceIntDvdSubNat (q c n : ℕ) (hnc : n ≤ c) :
    ((q : ℤ) ∣ ((c : ℤ) - (n : ℤ))) ↔ q ∣ (c - n) := by
  constructor
  · intro hd
    have hcast : ((c - n : ℕ) : ℤ) = (c : ℤ) - (n : ℤ) := Nat.cast_sub hnc
    have h' : (q : ℤ) ∣ ((c - n : ℕ) : ℤ) := by rw [hcast]; exact hd
    exact_mod_cast h'
  · intro hd
    obtain ⟨t, ht⟩ := hd
    exact ⟨t, by rw [← Nat.cast_sub hnc, ht]; push_cast; ring⟩

theorem traceIntDvdSubNat' (q c n : ℕ) (hnc : c ≤ n) :
    ((q : ℤ) ∣ ((c : ℤ) - (n : ℤ))) ↔ q ∣ (n - c) := by
  have h1 : ((q : ℤ) ∣ ((n : ℤ) - (c : ℤ))) ↔ q ∣ (n - c) := traceIntDvdSubNat q n c hnc
  rw [← h1]
  constructor
  · intro hd; simpa using dvd_neg.mpr hd
  · intro hd; simpa using dvd_neg.mpr hd

/-! ### The matrix `U^c (Uᴴ)^n` -/

theorem wU_commute_star (q : ℕ) (k : ℝ) (hq : 0 < q) :
    Commute (wU q k) (star (wU q k)) := by
  rw [commute_iff_eq, Matrix.mem_unitaryGroup_iff.mp (wU_mem_unitaryGroup q k hq),
    Matrix.mem_unitaryGroup_iff'.mp (wU_mem_unitaryGroup q k hq)]

theorem wU_pow_mul_star_pow (q : ℕ) (k : ℝ) (hq : 0 < q) (n : ℕ) :
    wU q k ^ n * star (wU q k) ^ n = 1 := by
  rw [← (wU_commute_star q k hq).mul_pow,
    Matrix.mem_unitaryGroup_iff.mp (wU_mem_unitaryGroup q k hq), one_pow]

theorem traceUStarReduce (q : ℕ) (k : ℝ) (hq : 0 < q) {c n : ℕ} (hnc : n ≤ c) :
    wU q k ^ c * star (wU q k) ^ n = wU q k ^ (c - n) := by
  conv_lhs => rw [show c = (c - n) + n from (Nat.sub_add_cancel hnc).symm, pow_add]
  rw [mul_assoc, wU_pow_mul_star_pow q k hq n, mul_one]

theorem traceUStarReduce' (q : ℕ) (k : ℝ) (hq : 0 < q) {c n : ℕ} (hcn : c ≤ n) :
    wU q k ^ c * star (wU q k) ^ n = (wU q k ^ (n - c))ᴴ := by
  have hstar : star (wU q k) = (wU q k)ᴴ := Matrix.star_eq_conjTranspose _
  conv_lhs => rw [show n = c + (n - c) from (Nat.add_sub_cancel' hcn).symm, pow_add]
  rw [← mul_assoc, wU_pow_mul_star_pow q k hq c, one_mul, hstar, ← Matrix.conjTranspose_pow]

theorem traceXScalar (q : ℕ) (k : ℝ) (hq : 0 < q) (c n : ℕ)
    (h : (q : ℤ) ∣ ((c : ℤ) - (n : ℤ))) :
    ∃ mu : ℂ, wU q k ^ c * star (wU q k) ^ n = mu • 1 := by
  rcases Nat.lt_or_ge c n with hcn | hnc
  · obtain ⟨t, ht⟩ := (traceIntDvdSubNat' q c n hcn.le).mp h
    refine ⟨star (wShiftBeta k ^ t), ?_⟩
    rw [traceUStarReduce' q k hq hcn.le, ht, wU_pow_scalar_mul q k hq t,
      Matrix.conjTranspose_smul, Matrix.conjTranspose_one]
  · obtain ⟨t, ht⟩ := (traceIntDvdSubNat q c n hnc).mp h
    refine ⟨wShiftBeta k ^ t, ?_⟩
    rw [traceUStarReduce q k hq hnc, ht, wU_pow_scalar_mul q k hq t]

theorem traceXDiagZero (q : ℕ) (k : ℝ) (hq : 0 < q) (c n : ℕ)
    (h : ¬ (q : ℤ) ∣ ((c : ℤ) - (n : ℤ))) (i : Fin q) :
    (wU q k ^ c * star (wU q k) ^ n) i i = 0 := by
  rcases Nat.lt_or_ge c n with hcn | hnc
  · have hnd : ¬ q ∣ (n - c) := fun hd => h ((traceIntDvdSubNat' q c n hcn.le).mpr hd)
    rw [traceUStarReduce' q k hq hcn.le, Matrix.conjTranspose_apply,
      wU_pow_diag_zero q k hq hnd i, star_zero]
  · have hnd : ¬ q ∣ (c - n) := fun hd => h ((traceIntDvdSubNat q c n hnc).mpr hd)
    rw [traceUStarReduce q k hq hnc]
    exact wU_pow_diag_zero q k hq hnd i

/-! ### Roots of unity sums -/

theorem wPh_pow (n : ℕ) (x : ℝ) : wPh x ^ n = wPh ((n : ℝ) * x) := by
  induction n with
  | zero => rw [Nat.cast_zero, zero_mul, pow_zero, wPh_zero]
  | succ n ih =>
    rw [pow_succ, ih, Nat.cast_succ, add_mul, one_mul, ← wPh_add]

theorem traceIntDvdOfCoprime (q : ℕ) (p d : ℤ) (hpq : Nat.Coprime p.natAbs q)
    (h : (q : ℤ) ∣ d * p) : (q : ℤ) ∣ d := by
  have h1 : (q : ℤ) ∣ ((d * p).natAbs : ℤ) := Int.dvd_natAbs.mpr h
  rw [Int.natAbs_mul] at h1
  have h2 : q ∣ d.natAbs * p.natAbs := by exact_mod_cast h1
  have h3 : q ∣ d.natAbs := Nat.Coprime.dvd_of_dvd_mul_right hpq.symm h2
  have h4 : (q : ℤ) ∣ ((d.natAbs : ℕ) : ℤ) := by exact_mod_cast h3
  exact Int.dvd_natAbs.mp h4

theorem traceSumVdPowZero (p : ℤ) (q : ℕ) (θ : ℝ) (hq : 0 < q) (hpq : Nat.Coprime p.natAbs q)
    (A B : ℕ) (h : ¬ (q : ℤ) ∣ ((A : ℤ) - (B : ℤ))) :
    ∑ i : Fin q, (wVd p q θ i) ^ A * (star (wVd p q θ i)) ^ B = 0 := by
  set d : ℤ := (A : ℤ) - (B : ℤ) with hd
  set x : ℂ := wPh ((d : ℝ) * (p : ℝ) / (q : ℝ)) with hx
  set cc : ℂ := wPh ((d : ℝ) * θ) with hcc
  have hqR : (q : ℝ) ≠ 0 := by
    have h1 : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
    exact ne_of_gt h1
  have hterm : ∀ i : Fin q,
      (wVd p q θ i) ^ A * (star (wVd p q θ i)) ^ B = cc * x ^ i.val := by
    intro i
    have harith : (A : ℝ) * (θ + (i.val : ℝ) * (p : ℝ) / (q : ℝ))
        + (B : ℝ) * (-(θ + (i.val : ℝ) * (p : ℝ) / (q : ℝ)))
        = (d : ℝ) * θ + (i.val : ℝ) * ((d : ℝ) * (p : ℝ) / (q : ℝ)) := by
      rw [hd]; push_cast; ring
    rw [wVd, wPh_conj, wPh_pow, wPh_pow, ← wPh_add, hcc, hx, wPh_pow, ← wPh_add, harith]
  have hxq : x ^ q = 1 := by
    rw [hx, wPh_pow]
    have harg : (q : ℝ) * ((d : ℝ) * (p : ℝ) / (q : ℝ)) = ((d * p : ℤ) : ℝ) := by
      push_cast
      field_simp
    rw [harg, wPh_int]
  have hx1 : x ≠ 1 := by
    intro hh
    rw [hx, wPh] at hh
    obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.mp hh
    have hne : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 := by
      simp [Complex.I_ne_zero, Real.pi_ne_zero]
    have h2 : (2 * (Real.pi : ℂ) * Complex.I) * (((d : ℝ) * (p : ℝ) / (q : ℝ) : ℝ) : ℂ)
        = (2 * (Real.pi : ℂ) * Complex.I) * (n : ℂ) := by
      rw [mul_comm (2 * (Real.pi : ℂ) * Complex.I) ((n : ℤ) : ℂ)]
      exact hn
    have hcancel : (((d : ℝ) * (p : ℝ) / (q : ℝ) : ℝ) : ℂ) = (n : ℂ) :=
      mul_left_cancel₀ hne h2
    have hreal : (d : ℝ) * (p : ℝ) / (q : ℝ) = (n : ℝ) := Complex.ofReal_injective hcancel
    have hmul : (d : ℝ) * (p : ℝ) = (n : ℝ) * (q : ℝ) := by
      field_simp at hreal
      linarith [hreal]
    have hint : d * p = n * (q : ℤ) := by
      have h5 := hmul
      exact_mod_cast h5
    have hdvd : (q : ℤ) ∣ d := traceIntDvdOfCoprime q p d hpq ⟨n, by rw [hint, mul_comm]⟩
    exact h (by rwa [hd] at hdvd)
  rw [Finset.sum_congr rfl (fun i _ => hterm i), ← Finset.mul_sum, Fin.sum_univ_eq_sum_range,
    geom_sum_eq hx1 q, hxq, sub_self, zero_div, mul_zero]

/-! ### Diagonal sandwich -/

theorem traceDiagSandwich (q : ℕ) (u w : Fin q → ℂ) (X : Matrix (Fin q) (Fin q) ℂ) :
    (Matrix.diagonal u * X * Matrix.diagonal w).trace = ∑ i, u i * X i i * w i := by
  rw [Matrix.trace]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Matrix.diag_apply, Matrix.mul_apply]
  rw [Finset.sum_eq_single i]
  · rw [Matrix.diagonal_apply, if_pos rfl, Matrix.diagonal_mul]
  · intro j _ hj
    rw [Matrix.diagonal_apply, if_neg hj, mul_zero]
  · intro hh
    exact absurd (Finset.mem_univ i) hh

theorem traceDvdCem (q c e m : ℕ) :
    ((q : ℤ) ∣ ((c : ℤ) - (e : ℤ) - (m : ℤ))) ↔
      ((q : ℤ) ∣ ((c : ℤ) - (((e + m : ℕ) : ℤ)))) := by
  constructor
  · intro hd
    obtain ⟨t, ht⟩ := hd
    exact ⟨t, by push_cast at ht ⊢; linarith⟩
  · intro hd
    obtain ⟨t, ht⟩ := hd
    exact ⟨t, by push_cast at ht ⊢; linarith⟩

theorem traceDvdAbm (q a b m : ℕ) :
    ((q : ℤ) ∣ ((a : ℤ) - (b : ℤ) - (m : ℤ))) ↔
      ((q : ℤ) ∣ ((a : ℤ) - (((b + m : ℕ) : ℤ)))) := by
  constructor
  · intro hd
    obtain ⟨t, ht⟩ := hd
    exact ⟨t, by push_cast at ht ⊢; linarith⟩
  · intro hd
    obtain ⟨t, ht⟩ := hd
    exact ⟨t, by push_cast at ht ⊢; linarith⟩

end TraceRuleAux

open TraceRuleAux

/-! ### The trace rule -/

theorem TraceRule (p : ℤ) (q : ℕ) (θ k : ℝ) (hq : 0 < q) (hpq : Nat.Coprime p.natAbs q)
    (a b c e m : ℕ)
    (h : ¬ ((q : ℤ) ∣ ((a : ℤ) - (b : ℤ) - (m : ℤ))) ∨
      ¬ ((q : ℤ) ∣ ((c : ℤ) - (e : ℤ) - (m : ℤ)))) :
    ((wV p q θ ^ a) * (star (wV p q θ) ^ b) * (wU q k ^ c) * (star (wU q k) ^ e) *
      (star (wU q k) ^ m) * (star (wV p q θ) ^ m)).trace = 0 := by
  have hVa : wV p q θ ^ a = Matrix.diagonal (fun i => wVd p q θ i ^ a) := by
    rw [wV, Matrix.diagonal_pow]
    congr 1
  have hVb : star (wV p q θ) ^ b = Matrix.diagonal (fun i => star (wVd p q θ i) ^ b) := by
    rw [Matrix.star_eq_conjTranspose, wV, Matrix.diagonal_conjTranspose, Matrix.diagonal_pow]
    congr 1
  have hVm : star (wV p q θ) ^ m = Matrix.diagonal (fun i => star (wVd p q θ i) ^ m) := by
    rw [Matrix.star_eq_conjTranspose, wV, Matrix.diagonal_conjTranspose, Matrix.diagonal_pow]
    congr 1
  have hUmerge : star (wU q k) ^ e * star (wU q k) ^ m = star (wU q k) ^ (e + m) := by
    rw [← pow_add]
  have e1 : (wV p q θ ^ a) * (star (wV p q θ) ^ b) * (wU q k ^ c) * (star (wU q k) ^ e) *
        (star (wU q k) ^ m) * (star (wV p q θ) ^ m)
      = Matrix.diagonal (fun i => wVd p q θ i ^ a) *
        Matrix.diagonal (fun i => star (wVd p q θ i) ^ b) *
        (wU q k ^ c * (star (wU q k) ^ e * star (wU q k) ^ m)) *
        Matrix.diagonal (fun i => star (wVd p q θ i) ^ m) := by
    rw [hVa, hVb, hVm]
    noncomm_ring
  have e3 : Matrix.diagonal (fun i => wVd p q θ i ^ a) *
        Matrix.diagonal (fun i => star (wVd p q θ i) ^ b)
      = Matrix.diagonal (fun i => wVd p q θ i ^ a * star (wVd p q θ i) ^ b) := by
    rw [Matrix.diagonal_mul_diagonal]
  rw [e1, hUmerge, e3, traceDiagSandwich]
  by_cases hγ : (q : ℤ) ∣ ((c : ℤ) - (e : ℤ) - (m : ℤ))
  · have hδ : ¬ (q : ℤ) ∣ ((a : ℤ) - (b : ℤ) - (m : ℤ)) := by
      rcases h with hh | hh
      · exact hh
      · exact absurd hγ hh
    obtain ⟨mu, hmu⟩ := traceXScalar q k hq c (e + m) ((traceDvdCem q c e m).mp hγ)
    rw [hmu]
    simp only [Matrix.smul_apply, smul_eq_mul, Matrix.one_apply, if_true, mul_one]
    have hsum : ∑ i : Fin q,
        (wVd p q θ i ^ a * star (wVd p q θ i) ^ b) * star (wVd p q θ i) ^ m = 0 := by
      have hpt : ∀ i : Fin q,
          (wVd p q θ i ^ a * star (wVd p q θ i) ^ b) * star (wVd p q θ i) ^ m
            = (wVd p q θ i) ^ a * star (wVd p q θ i) ^ (b + m) := by
        intro i
        rw [mul_assoc, ← pow_add]
      rw [Finset.sum_congr rfl (fun i _ => hpt i)]
      exact traceSumVdPowZero p q θ hq hpq a (b + m) ((traceDvdAbm q a b m).not.mp hδ)
    rw [show (∑ i : Fin q,
        (wVd p q θ i ^ a * star (wVd p q θ i) ^ b) * mu * star (wVd p q θ i) ^ m)
        = (∑ i : Fin q,
        (wVd p q θ i ^ a * star (wVd p q θ i) ^ b) * star (wVd p q θ i) ^ m) * mu from by
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl (fun i _ => by ring)]
    rw [hsum, zero_mul]
  · have hX0 : ∀ i : Fin q, (wU q k ^ c * star (wU q k) ^ (e + m)) i i = 0 :=
      fun i => traceXDiagZero q k hq c (e + m) ((traceDvdCem q c e m).not.mp hγ) i
    refine Finset.sum_eq_zero (fun i _ => ?_)
    rw [hX0 i, mul_zero, zero_mul]

end Work.TMC14Core
