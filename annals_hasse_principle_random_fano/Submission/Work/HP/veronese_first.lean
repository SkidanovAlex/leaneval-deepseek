import Mathlib
import Submission.Work.HP.evaldefs

/-!
# `Work.HP.veronese_first`

Elementary analytic bounds for the Veronese monomials `veronese d n` and for the partial
derivatives `dm` (see `Submission/Work/HP/evaldefs.lean`), on the Euclidean ball of radius `2`:

* `|veronese d n x m| ≤ 2^d`;
* `|dm d n m x j| ≤ d · 2^{d-1}`;
* `veronese d n · m` is `2^{3d}`-Lipschitz on the ball;
* `dm d n m · j` is `2^{3d}`-Lipschitz on the ball.

The proof rests on the telescoping product bound `prod_pow_diff_le` and the exponent bound
`abs_prod_pow_le` from `evaldefs`.  The key rewriting is that `dm d n m x j` is `m_j` times the
monomial whose exponent vector is `m - e_j` (truncated at `0`), so the same product tools apply.
-/

set_option autoImplicit false

open Finset

namespace Work.HP

/-! ## Arithmetic on the reduced exponent vector -/

/-- `dm d n m x j` factors as `m_j` times the monomial with exponent vector
`i ↦ m_i - [i = j]`. -/
lemma vf_dm_eq (d n : ℕ) (m : Mon d n) (x : Fin (n + 1) → ℝ) (j : Fin (n + 1)) :
    dm d n m x j
      = ((m.1 j : ℕ) : ℝ) * ∏ i, x i ^ ((m.1 i : ℕ) - (if i = j then 1 else 0)) := by
  rw [dm]
  have hprod : ∏ i, x i ^ ((m.1 i : ℕ) - (if i = j then 1 else 0))
      = x j ^ ((m.1 j : ℕ) - (if j = j then 1 else 0))
        * ∏ l ∈ Finset.univ.erase j, x l ^ ((m.1 l : ℕ) - (if l = j then 1 else 0)) :=
    (Finset.mul_prod_erase Finset.univ
      (fun i => x i ^ ((m.1 i : ℕ) - (if i = j then 1 else 0))) (Finset.mem_univ j)).symm
  rw [hprod]
  simp only [if_true]
  have hcongr : ∏ l ∈ Finset.univ.erase j, x l ^ ((m.1 l : ℕ) - (if l = j then 1 else 0))
      = ∏ l ∈ Finset.univ.erase j, x l ^ ((m.1 l : ℕ)) := by
    apply Finset.prod_congr rfl
    intro l hl
    rw [if_neg (Finset.mem_erase.mp hl).1]
    simp
  rw [hcongr]
  ring

/-- Sum of the reduced exponent vector when `m_j ≥ 1`. -/
lemma vf_dm_sum_pos (d n : ℕ) (m : Mon d n) (j : Fin (n + 1)) (h1 : 1 ≤ (m.1 j : ℕ)) :
    ∑ i, ((m.1 i : ℕ) - (if i = j then 1 else 0)) = d - 1 := by
  have hsplit : ∑ i, ((m.1 i : ℕ) - (if i = j then 1 else 0))
      = ((m.1 j : ℕ) - (if j = j then 1 else 0))
        + ∑ i ∈ Finset.univ.erase j, ((m.1 i : ℕ) - (if i = j then 1 else 0)) :=
    (Finset.add_sum_erase Finset.univ _ (Finset.mem_univ j)).symm
  rw [hsplit]
  simp only [if_true]
  have hcongr : ∑ i ∈ Finset.univ.erase j, ((m.1 i : ℕ) - (if i = j then 1 else 0))
      = ∑ i ∈ Finset.univ.erase j, ((m.1 i : ℕ)) := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [if_neg (Finset.mem_erase.mp hi).1]
    simp
  rw [hcongr]
  have herase : ∑ i ∈ Finset.univ.erase j, ((m.1 i : ℕ)) = d - (m.1 j : ℕ) := by
    have h2 := Finset.sum_erase_add Finset.univ (fun i => (m.1 i : ℕ)) (Finset.mem_univ j)
    rw [m.2] at h2
    exact Nat.eq_sub_of_add_eq h2
  rw [herase]
  have hjle : (m.1 j : ℕ) ≤ d := by
    have h := Finset.single_le_sum (s := Finset.univ) (f := fun i => (m.1 i : ℕ))
      (fun i _ => Nat.zero_le _) (Finset.mem_univ j)
    rw [m.2] at h
    exact h
  omega

/-- Sum of the reduced exponent vector is at most `d`. -/
lemma vf_dm_sum_le (d n : ℕ) (m : Mon d n) (j : Fin (n + 1)) :
    ∑ i, ((m.1 i : ℕ) - (if i = j then 1 else 0)) ≤ d := by
  calc ∑ i, ((m.1 i : ℕ) - (if i = j then 1 else 0)) ≤ ∑ i, (m.1 i : ℕ) :=
        Finset.sum_le_sum (fun i _ => Nat.sub_le _ _)
    _ = d := m.2

/-- The single coefficient `m_j` is at most `d`. -/
lemma vf_coeff_le (d n : ℕ) (m : Mon d n) (j : Fin (n + 1)) : (m.1 j : ℕ) ≤ d := by
  have h := Finset.single_le_sum (s := Finset.univ) (f := fun i => (m.1 i : ℕ))
    (fun i _ => Nat.zero_le _) (Finset.mem_univ j)
  rw [m.2] at h
  exact h

/-! ## Power inequalities -/

lemma vf_pow_lin (d : ℕ) : (d : ℝ) * 2 ^ d ≤ 2 ^ (3 * d) := by
  have hd : (d : ℝ) ≤ 2 ^ d := by
    have h : (d : ℝ) < (2 : ℝ) ^ d := by exact_mod_cast Nat.lt_two_pow_self (n := d)
    linarith
  calc (d : ℝ) * 2 ^ d ≤ 2 ^ d * 2 ^ d := mul_le_mul_of_nonneg_right hd (by positivity)
    _ = 2 ^ (2 * d) := by rw [← pow_add]; congr 1; omega
    _ ≤ 2 ^ (3 * d) := by apply pow_le_pow_right₀ (by norm_num); omega

lemma vf_pow_sq (d : ℕ) : (d : ℝ) ^ 2 * 2 ^ d ≤ 2 ^ (3 * d) := by
  have hd1 : (d : ℝ) ≤ 2 ^ d := by
    have h : (d : ℝ) < (2 : ℝ) ^ d := by exact_mod_cast Nat.lt_two_pow_self (n := d)
    linarith
  have hd : (d : ℝ) ^ 2 ≤ 2 ^ (2 * d) := by
    calc (d : ℝ) ^ 2 ≤ (2 ^ d) ^ 2 := pow_le_pow_left₀ (by positivity) hd1 2
      _ = 2 ^ (2 * d) := by rw [← pow_mul]; congr 1; omega
  calc (d : ℝ) ^ 2 * 2 ^ d ≤ 2 ^ (2 * d) * 2 ^ d :=
        mul_le_mul_of_nonneg_right hd (by positivity)
    _ = 2 ^ (3 * d) := by rw [← pow_add]; congr 1; omega

/-! ## The four bounds -/

/-- `|veronese d n x m| ≤ 2^d` on the ball of radius `2`. -/
lemma vf_veronese_bound (d n : ℕ) (m : Mon d n) (x : Fin (n + 1) → ℝ) (hx : rNorm x ≤ 2) :
    |veronese d n x m| ≤ 2 ^ d := by
  have hcoord : ∀ i, |x i| ≤ (2 : ℝ) := fun i => le_trans (abs_coord_le_rNorm x i) hx
  have h := abs_prod_pow_le (fun i => (m.1 i : ℕ)) x (M := 2) hcoord
  rw [m.2] at h
  simpa only [veronese] using h

/-- `|dm d n m x j| ≤ d · 2^{d-1}` on the ball of radius `2`. -/
lemma vf_dm_bound (d n : ℕ) (m : Mon d n) (x : Fin (n + 1) → ℝ) (j : Fin (n + 1))
    (hx : rNorm x ≤ 2) : |dm d n m x j| ≤ (d : ℝ) * 2 ^ (d - 1) := by
  rw [vf_dm_eq d n m x j, abs_mul, abs_of_nonneg (Nat.cast_nonneg (m.1 j : ℕ))]
  have hcoord : ∀ i, |x i| ≤ (2 : ℝ) := fun i => le_trans (abs_coord_le_rNorm x i) hx
  have hP : |∏ i, x i ^ ((m.1 i : ℕ) - (if i = j then 1 else 0))|
      ≤ 2 ^ (∑ i, ((m.1 i : ℕ) - (if i = j then 1 else 0))) :=
    abs_prod_pow_le (fun i => (m.1 i : ℕ) - (if i = j then 1 else 0)) x (M := 2) hcoord
  have hAle : ((m.1 j : ℕ) : ℝ) ≤ (d : ℝ) := by exact_mod_cast vf_coeff_le d n m j
  rcases Nat.eq_zero_or_pos (m.1 j : ℕ) with h0 | h1
  · rw [h0]; simp only [Nat.cast_zero, zero_mul]; positivity
  · rw [vf_dm_sum_pos d n m j h1] at hP
    calc ((m.1 j : ℕ) : ℝ) * |∏ i, x i ^ ((m.1 i : ℕ) - (if i = j then 1 else 0))|
        ≤ ((m.1 j : ℕ) : ℝ) * 2 ^ (d - 1) := mul_le_mul_of_nonneg_left hP (Nat.cast_nonneg _)
      _ ≤ (d : ℝ) * 2 ^ (d - 1) := mul_le_mul_of_nonneg_right hAle (by positivity)

/-- `veronese d n · m` is `2^{3d}`-Lipschitz on the ball of radius `2`. -/
lemma vf_veronese_lip (d n : ℕ) (m : Mon d n) (x y : Fin (n + 1) → ℝ)
    (hx : rNorm x ≤ 2) (hy : rNorm y ≤ 2) :
    |veronese d n y m - veronese d n x m| ≤ 2 ^ (3 * d) * rNorm (y - x) := by
  have hcoordx : ∀ i, |x i| ≤ (2 : ℝ) := fun i => le_trans (abs_coord_le_rNorm x i) hx
  have hcoordy : ∀ i, |y i| ≤ (2 : ℝ) := fun i => le_trans (abs_coord_le_rNorm y i) hy
  have hxyi : ∀ i, |y i - x i| ≤ rNorm (y - x) := fun i => abs_coord_le_rNorm (y - x) i
  have hε : 0 ≤ rNorm (y - x) := rNorm_nonneg _
  have h := prod_pow_diff_le Finset.univ (fun i => (m.1 i : ℕ)) x y (2 : ℝ) (rNorm (y - x))
      (by norm_num) hε (fun i _ => hcoordx i) (fun i _ => hcoordy i) (fun i _ => hxyi i)
  have hmain : |veronese d n y m - veronese d n x m| ≤ (d : ℝ) * 2 ^ d * rNorm (y - x) := by
    simp only [veronese]
    rw [m.2] at h
    simpa using h
  calc |veronese d n y m - veronese d n x m| ≤ (d : ℝ) * 2 ^ d * rNorm (y - x) := hmain
    _ ≤ 2 ^ (3 * d) * rNorm (y - x) := by
        apply mul_le_mul_of_nonneg_right _ hε
        exact vf_pow_lin d

/-- `dm d n m · j` is `2^{3d}`-Lipschitz on the ball of radius `2`. -/
lemma vf_dm_lip (d n : ℕ) (m : Mon d n) (x y : Fin (n + 1) → ℝ) (j : Fin (n + 1))
    (hx : rNorm x ≤ 2) (hy : rNorm y ≤ 2) :
    |dm d n m y j - dm d n m x j| ≤ 2 ^ (3 * d) * rNorm (y - x) := by
  have hcoordx : ∀ i, |x i| ≤ (2 : ℝ) := fun i => le_trans (abs_coord_le_rNorm x i) hx
  have hcoordy : ∀ i, |y i| ≤ (2 : ℝ) := fun i => le_trans (abs_coord_le_rNorm y i) hy
  have hxyi : ∀ i, |y i - x i| ≤ rNorm (y - x) := fun i => abs_coord_le_rNorm (y - x) i
  have hε : 0 ≤ rNorm (y - x) := rNorm_nonneg _
  rw [vf_dm_eq d n m y j, vf_dm_eq d n m x j]
  have hfact : ((m.1 j : ℕ) : ℝ) * ∏ i, y i ^ ((m.1 i : ℕ) - (if i = j then 1 else 0))
      - ((m.1 j : ℕ) : ℝ) * ∏ i, x i ^ ((m.1 i : ℕ) - (if i = j then 1 else 0))
      = ((m.1 j : ℕ) : ℝ) * (∏ i, y i ^ ((m.1 i : ℕ) - (if i = j then 1 else 0))
          - ∏ i, x i ^ ((m.1 i : ℕ) - (if i = j then 1 else 0))) := by ring
  rw [hfact, abs_mul, abs_of_nonneg (Nat.cast_nonneg (m.1 j : ℕ))]
  have hdiff := prod_pow_diff_le Finset.univ
      (fun i => (m.1 i : ℕ) - (if i = j then 1 else 0)) x y (2 : ℝ) (rNorm (y - x))
      (by norm_num) hε (fun i _ => hcoordx i) (fun i _ => hcoordy i) (fun i _ => hxyi i)
  have hsumle : ((∑ i, ((m.1 i : ℕ) - (if i = j then 1 else 0)) : ℕ) : ℝ) ≤ (d : ℝ) := by
    exact_mod_cast vf_dm_sum_le d n m j
  have hpow : (2 : ℝ) ^ (∑ i, ((m.1 i : ℕ) - (if i = j then 1 else 0))) ≤ (2 : ℝ) ^ d :=
    pow_le_pow_right₀ (by norm_num) (vf_dm_sum_le d n m j)
  have hbase : ((∑ i, ((m.1 i : ℕ) - (if i = j then 1 else 0)) : ℕ) : ℝ)
        * (2 : ℝ) ^ (∑ i, ((m.1 i : ℕ) - (if i = j then 1 else 0)))
      ≤ (d : ℝ) * 2 ^ d := mul_le_mul hsumle hpow (by positivity) (by positivity)
  have hAle : ((m.1 j : ℕ) : ℝ) ≤ (d : ℝ) := by exact_mod_cast vf_coeff_le d n m j
  have hdiff' : |∏ i, y i ^ ((m.1 i : ℕ) - (if i = j then 1 else 0))
      - ∏ i, x i ^ ((m.1 i : ℕ) - (if i = j then 1 else 0))|
      ≤ (d : ℝ) * 2 ^ d * rNorm (y - x) :=
    le_trans (by simpa using hdiff) (mul_le_mul_of_nonneg_right hbase hε)
  calc ((m.1 j : ℕ) : ℝ) * |∏ i, y i ^ ((m.1 i : ℕ) - (if i = j then 1 else 0))
          - ∏ i, x i ^ ((m.1 i : ℕ) - (if i = j then 1 else 0))|
      ≤ (d : ℝ) * ((d : ℝ) * 2 ^ d * rNorm (y - x)) :=
        mul_le_mul hAle hdiff' (abs_nonneg _) (by positivity)
    _ = (d : ℝ) ^ 2 * 2 ^ d * rNorm (y - x) := by ring
    _ ≤ 2 ^ (3 * d) * rNorm (y - x) := by
        apply mul_le_mul_of_nonneg_right _ hε
        exact vf_pow_sq d

/-! ## The target -/

theorem veronese_first (d n : ℕ) :
    (∀ (m : Mon d n) (x : Fin (n + 1) → ℝ), rNorm x ≤ 2 → |veronese d n x m| ≤ 2 ^ d) ∧
    (∀ (m : Mon d n) (x : Fin (n + 1) → ℝ) (j : Fin (n + 1)), rNorm x ≤ 2 →
        |dm d n m x j| ≤ (d : ℝ) * 2 ^ (d - 1)) ∧
    (∀ (m : Mon d n) (x y : Fin (n + 1) → ℝ), rNorm x ≤ 2 → rNorm y ≤ 2 →
        |veronese d n y m - veronese d n x m| ≤ 2 ^ (3 * d) * rNorm (y - x)) ∧
    (∀ (m : Mon d n) (x y : Fin (n + 1) → ℝ) (j : Fin (n + 1)), rNorm x ≤ 2 → rNorm y ≤ 2 →
        |dm d n m y j - dm d n m x j| ≤ 2 ^ (3 * d) * rNorm (y - x)) :=
  ⟨fun m x hx => vf_veronese_bound d n m x hx,
   fun m x j hx => vf_dm_bound d n m x j hx,
   fun m x y hx hy => vf_veronese_lip d n m x y hx hy,
   fun m x y j hx hy => vf_dm_lip d n m x y j hx hy⟩

end Work.HP
