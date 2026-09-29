import Mathlib
import Submission.Work.Resample.auDefs
import Submission.Work.Resample.auMLe
import Submission.Work.Resample.auKArith

set_option autoImplicit false

namespace Work.Resample

/-! ## Size of a natural number value -/

/-- `isz` of a natural number cast to `ℤ`. -/
lemma isz_natCast (n : ℕ) : HvdH.isz ((n : ℤ)) = n.size + 2 := by
  simp [HvdH.isz]

/-- A size bound: `n < 2^q` implies `isz n ≤ q + 2`. -/
lemma isz_natCast_le {n q : ℕ} (h : n < 2 ^ q) : HvdH.isz ((n : ℤ)) ≤ q + 2 := by
  rw [isz_natCast]
  have : n.size ≤ q := Nat.size_le.mpr h
  omega

/-- The crude exponential bound `4p + 5 ≤ 2^p`, valid for `p ≥ 6`. -/
lemma four_p_add_five_le_two_pow (p : ℕ) (hp : 6 ≤ p) : 4 * p + 5 ≤ 2 ^ p := by
  induction p, hp using Nat.le_induction with
  | base => norm_num
  | succ n hn ih =>
      have h1 : 4 * (n + 1) + 5 ≤ 2 * (4 * n + 5) := by omega
      have h2 : 2 * (4 * n + 5) ≤ 2 * 2 ^ n := by omega
      calc 4 * (n + 1) + 5 ≤ 2 * (4 * n + 5) := h1
        _ ≤ 2 * 2 ^ n := h2
        _ = 2 ^ (n + 1) := by rw [pow_succ]; ring

/-! ## Arithmetic of the window centre -/

/-- For `k ≤ t` the window centre never passes `s`: `⌊(2ks+t)/(2t)⌋ ≤ s`. -/
lemma auK_le_s {s t k : ℕ} (hs : 1 ≤ s) (ht : 0 < t) (hk : k ≤ t) : auK s t k ≤ s := by
  have ht2 : 0 < 2 * t := by omega
  rw [auK, Nat.div_le_iff_le_mul ht2]
  have hmul : 2 * k * s ≤ 2 * t * s := Nat.mul_le_mul_right s (Nat.mul_le_mul_left 2 hk)
  have hcomm : s * (2 * t) = 2 * t * s := by ring
  omega

/-- The window centre of the zeroth output is `0`. -/
lemma auK_zero {s t : ℕ} (ht : 0 < t) : auK s t 0 = 0 := by
  simp only [auK, Nat.mul_zero, Nat.zero_mul, Nat.zero_add]
  exact Nat.div_eq_of_lt (by omega)

/-- Consecutive window centres differ by at most one: `K(k+1) - K k ≤ 1`. -/
lemma auK_step_sub {s t k : ℕ} (hst : s < t) (ht : 0 < t) :
    auK s t (k + 1) - auK s t k ≤ 1 := by
  have h1 : auK s t k ≤ auK s t (k + 1) := auKArith_mono s t (Nat.le_succ k)
  have h2 : auK s t (k + 1) ≤ auK s t k + 1 := auKArith_step s t k hst ht
  omega

/-- The slide of the window centre is a `0`/`1`-valued integer, so its size is at most `3`. -/
lemma isz_auK_diff {s t k : ℕ} (hst : s < t) (ht : 0 < t) :
    HvdH.isz (((auK s t (k + 1) : ℕ) : ℤ) - ((auK s t k : ℕ) : ℤ)) ≤ 3 := by
  have h1 : auK s t k ≤ auK s t (k + 1) := auKArith_mono s t (Nat.le_succ k)
  have h2 : auK s t (k + 1) ≤ auK s t k + 1 := auKArith_step s t k hst ht
  have hd : ((auK s t (k + 1) : ℕ) : ℤ) - ((auK s t k : ℕ) : ℤ)
      = ((auK s t (k + 1) - auK s t k : ℕ) : ℤ) := (Nat.cast_sub (R := ℤ) h1).symm
  rw [hd, isz_natCast]
  have hle : auK s t (k + 1) - auK s t k ≤ 1 := by omega
  have hsize : (auK s t (k + 1) - auK s t k).size ≤ 1 := by
    rw [Nat.size_le]
    simp only [pow_one]
    omega
  omega

/-! ## The size statement -/

theorem auSizes (p α s t : ℕ) (hs : 2 ≤ s) (hst : s < t) (hα : 2 ≤ α) (hp : 100 ≤ p) (hαp : α ^ 2 < p)
    (htp : t < 2 ^ p) :
    HvdH.isz ((Work.Resample.auOff p α s : ℕ) : ℤ) ≤ p + 3 ∧
    HvdH.isz ((Work.Resample.auCop p α s : ℕ) : ℤ) ≤ p + 3 ∧
    HvdH.isz ((Work.Resample.auM p α : ℕ) : ℤ) ≤ p + 3 ∧
    HvdH.isz ((Work.Resample.auL p α : ℕ) : ℤ) ≤ p + 3 ∧
    (∀ k ≤ t, Work.Resample.auK s t k ≤ s) ∧
    Monotone (Work.Resample.auK s t) ∧
    Work.Resample.auK s t 0 = 0 ∧
    (∀ k, k < t → Work.Resample.auK s t (k + 1) - Work.Resample.auK s t k ≤ 1) ∧
    (∀ k, k < t → HvdH.isz (((Work.Resample.auK s t (k + 1) : ℕ) : ℤ) - ((Work.Resample.auK s t k : ℕ) : ℤ)) ≤ 3) ∧
    (Work.Resample.auCop p α s * s ≤ Work.Resample.auOff p α s + 2 * s + 2 * Work.Resample.auM p α + s) := by
  have ht : 0 < t := by omega
  have hs1 : 1 ≤ s := by omega
  obtain ⟨hM, hL⟩ := auMLe p α hα hαp
  -- the three exponential bounds
  have h2p : 2 * p < 2 ^ (p + 1) := by
    have h := Nat.lt_two_pow_self (n := p)
    calc 2 * p < 2 * 2 ^ p := by linarith
      _ = 2 ^ (p + 1) := by rw [pow_succ]; ring
  have hfp : 4 * p + 1 < 2 ^ (p + 1) := by
    have h5 : 4 * p + 5 ≤ 2 ^ p := four_p_add_five_le_two_pow p (by omega)
    have hle : 2 ^ p ≤ 2 ^ (p + 1) := Nat.pow_le_pow_right (by norm_num) (Nat.le_succ p)
    omega
  have hMpow : auM p α < 2 ^ (p + 1) := lt_of_le_of_lt hM h2p
  have hLpow : auL p α < 2 ^ (p + 1) := lt_of_le_of_lt hL hfp
  -- the offset `auOff ≤ s - 1 < 2^p`
  have hOff : auOff p α s ≤ s - 1 := by
    have hc : s * ((auM p α + s - 1) / s) ≤ auM p α + s - 1 := Nat.mul_div_le _ _
    have hsub : s * ((auM p α + s - 1) / s) - auM p α ≤ (auM p α + s - 1) - auM p α :=
      Nat.sub_le_sub_right hc (auM p α)
    simp only [auOff]
    omega
  have hOfflt : s - 1 < 2 ^ (p + 1) := by
    have hlt : 2 ^ p < 2 ^ (p + 1) := Nat.pow_lt_pow_succ (by norm_num)
    omega
  have hOffpow : auOff p α s < 2 ^ (p + 1) := by omega
  -- the number of copies `auCop ≤ 4p + 4 < 2^(p+1)`
  have hCoplt : auCop p α s < 4 * p + 5 := by
    rw [auCop, Nat.div_lt_iff_lt_mul (by omega : 0 < s)]
    have hOff' : auOff p α s + 1 ≤ s := by omega
    nlinarith [hOff', hM, hs, hp]
  have hCoppow : auCop p α s < 2 ^ (p + 1) := by
    have h5 : 4 * p + 5 ≤ 2 ^ p := four_p_add_five_le_two_pow p (by omega)
    have hle : 2 ^ p ≤ 2 ^ (p + 1) := Nat.pow_le_pow_right (by norm_num) (Nat.le_succ p)
    omega
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have := isz_natCast_le hOffpow (q := p + 1); omega
  · have := isz_natCast_le hCoppow (q := p + 1); omega
  · have := isz_natCast_le hMpow (q := p + 1); omega
  · have := isz_natCast_le hLpow (q := p + 1); omega
  · intro k hk
    exact auK_le_s hs1 ht hk
  · exact auKArith_mono s t
  · exact auK_zero ht
  · intro k _
    exact auK_step_sub hst ht
  · intro k _
    exact isz_auK_diff hst ht
  · have : auCop p α s * s ≤ auOff p α s + 2 * s + 2 * auM p α := by
      simp only [auCop]
      exact Nat.div_mul_le_self _ _
    omega

end Work.Resample
