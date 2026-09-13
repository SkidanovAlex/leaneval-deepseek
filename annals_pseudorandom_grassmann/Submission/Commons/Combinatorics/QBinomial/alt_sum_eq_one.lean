import Mathlib
import Submission.Commons.LinearAlgebra.Submodule.card_submodule_pascal_zmod_two

namespace Commons.Combinatorics.QBinomial

open Module

noncomputable section

/-- `gb n i` is the number of `i`-dimensional subspaces of `𝔽₂ⁿ`. -/
def gb (n i : ℕ) : ℕ :=
  Nat.card {W : Submodule (ZMod 2) (Fin n → ZMod 2) // Module.finrank (ZMod 2) W = i}

lemma gb_zero (n : ℕ) : gb n 0 = 1 := by
  unfold gb
  rw [Nat.card_eq_one_iff_exists]
  refine ⟨⟨⊥, ?_⟩, ?_⟩
  · simp
  · rintro ⟨W, hW⟩
    exact Subtype.ext ((Submodule.finrank_eq_zero (R := ZMod 2)).mp hW)

lemma gb_eq_zero_of_lt (n i : ℕ) (h : n < i) : gb n i = 0 := by
  unfold gb
  exact Commons.LinearAlgebra.Submodule.natCard_submodule_finrank_eq_zero_of_lt
    (K := ZMod 2) (V := Fin n → ZMod 2) (r := i)
    (by rw [Module.finrank_pi, Fintype.card_fin]; exact h)

lemma gb_pascal (n i : ℕ) :
    gb (n + 1) (i + 1) = gb n (i + 1) + 2 ^ (n - i) * gb n i := by
  unfold gb
  exact Commons.LinearAlgebra.Submodule.card_submodule_pascal_zmod_two n i

/-- The alternating weight `(-1)^i · 2^{C(i,2)}`. -/
def altWeight (i : ℕ) : ℤ := (-1 : ℤ) ^ i * (2 : ℤ) ^ (i.choose 2)

lemma altWeight_zero : altWeight 0 = 1 := by
  simp [altWeight]

lemma choose_two_succ (i : ℕ) : (i + 1).choose 2 = i.choose 2 + i := by
  have h := Nat.choose_succ_succ' i 1
  rw [Nat.choose_one_right] at h
  norm_num at h
  omega

lemma altWeight_succ (i : ℕ) : altWeight (i + 1) = -altWeight i * (2 : ℤ) ^ i := by
  unfold altWeight
  have h1 : (i + 1).choose 2 = i.choose 2 + i := choose_two_succ i
  have h2 : (-1 : ℤ) ^ (i + 1) = -(-1 : ℤ) ^ i := by rw [pow_succ]; ring
  rw [h1, h2, pow_add]
  ring

lemma altWeight_eq_neg (i : ℕ) (hi : 1 ≤ i) :
    altWeight i = -((-1 : ℤ) ^ (i - 1) * (2 : ℤ) ^ (i.choose 2)) := by
  unfold altWeight
  have hsign : (-1 : ℤ) ^ i = -(-1) ^ (i - 1) := by
    conv_lhs => rw [show i = (i - 1) + 1 from (Nat.sub_add_cancel hi).symm]
    rw [pow_succ]
    ring
  rw [hsign]
  ring

/-- `F n = ∑_{i=0}^{n} (-1)^i 2^{i(i-1)/2} · [n choose i]_2`. -/
def F (n : ℕ) : ℤ :=
  ∑ i ∈ Finset.range (n + 1), altWeight i * (gb n i : ℤ)

/-- `T n` is the target alternating sum with `i.choose 2` in the exponent. -/
def T (n : ℕ) : ℤ :=
  ∑ i ∈ Finset.Icc 1 n, (-1 : ℤ) ^ (i - 1) * (2 : ℤ) ^ (i.choose 2) * (gb n i : ℤ)

lemma sumA (n : ℕ) :
    (∑ i ∈ Finset.range (n + 1), altWeight (i + 1) * (gb n (i + 1) : ℤ)) = F n - 1 := by
  let h : ℕ → ℤ := fun j => altWeight j * (gb n j : ℤ)
  have hA : (∑ i ∈ Finset.range (n + 1), altWeight (i + 1) * (gb n (i + 1) : ℤ))
      = ∑ i ∈ Finset.range (n + 1), h (i + 1) := by
    apply Finset.sum_congr rfl
    intro i _
    simp only [h]
  have hFn : (∑ i ∈ Finset.range (n + 1), h i) = F n := by
    simp only [F, h]
  have h0 : h 0 = 1 := by
    simp only [h, altWeight_zero, gb_zero, Nat.cast_one, one_mul]
  have htop : h (n + 1) = 0 := by
    simp only [h, gb_eq_zero_of_lt n (n + 1) (by omega), Nat.cast_zero, mul_zero]
  have key : (∑ k ∈ Finset.range (n + 1 + 1), h k)
      = (∑ k ∈ Finset.range (n + 1), h (k + 1)) + h 0 :=
    Finset.sum_range_succ' h (n + 1)
  have key2 : (∑ k ∈ Finset.range (n + 1 + 1), h k)
      = (∑ k ∈ Finset.range (n + 1), h k) + h (n + 1) :=
    Finset.sum_range_succ h (n + 1)
  rw [hA]
  linarith

lemma sumB (n : ℕ) :
    (∑ i ∈ Finset.range (n + 1), altWeight (i + 1) * (2 : ℤ) ^ (n - i) * (gb n i : ℤ))
      = -(2 : ℤ) ^ n * F n := by
  have hpoint : ∀ i ∈ Finset.range (n + 1),
      altWeight (i + 1) * (2 : ℤ) ^ (n - i) * (gb n i : ℤ)
        = -(2 : ℤ) ^ n * (altWeight i * (gb n i : ℤ)) := by
    intro i hi
    have hin : i ≤ n := by
      simp only [Finset.mem_range] at hi; omega
    rw [altWeight_succ]
    have hpow : (2 : ℤ) ^ i * (2 : ℤ) ^ (n - i) = (2 : ℤ) ^ n := by
      rw [← pow_add, Nat.add_sub_cancel' hin]
    calc (-altWeight i * (2 : ℤ) ^ i) * (2 : ℤ) ^ (n - i) * (gb n i : ℤ)
        = -altWeight i * ((2 : ℤ) ^ i * (2 : ℤ) ^ (n - i)) * (gb n i : ℤ) := by ring
      _ = -altWeight i * (2 : ℤ) ^ n * (gb n i : ℤ) := by rw [hpow]
      _ = -(2 : ℤ) ^ n * (altWeight i * (gb n i : ℤ)) := by ring
  rw [Finset.sum_congr rfl hpoint, ← Finset.mul_sum]
  rfl
  -- (the goal is exactly `F n` after unfolding)

lemma F_step (n : ℕ) : F (n + 1) = (1 - (2 : ℤ) ^ n) * F n := by
  have hf0 : altWeight 0 * (gb (n + 1) 0 : ℤ) = 1 := by
    simp only [altWeight_zero, gb_zero, Nat.cast_one, one_mul]
  have hterm : ∀ i,
      (fun i => altWeight i * (gb (n + 1) i : ℤ)) (i + 1)
        = altWeight (i + 1) * (gb n (i + 1) : ℤ)
          + altWeight (i + 1) * (2 : ℤ) ^ (n - i) * (gb n i : ℤ) := by
    intro i
    simp only []
    rw [gb_pascal n i]
    push_cast
    ring
  have hF : F (n + 1) = ∑ i ∈ Finset.range (n + 1 + 1), altWeight i * (gb (n + 1) i : ℤ) := by
    simp only [F]
  rw [hF, Finset.sum_range_succ' (fun i => altWeight i * (gb (n + 1) i : ℤ)) (n + 1), hf0]
  rw [Finset.sum_congr rfl (fun i _ => hterm i)]
  rw [Finset.sum_add_distrib, sumA n, sumB n]
  ring

lemma F_eq_zero : ∀ n : ℕ, 1 ≤ n → F n = 0 := by
  intro n
  induction n with
  | zero => intro h; omega
  | succ k ih =>
    intro hk1
    rcases Nat.eq_zero_or_pos k with hk | hk
    · subst hk
      rw [F_step 0]
      simp
    · rw [F_step k, ih hk, mul_zero]

lemma F_eq_one_sub_T (n : ℕ) : F n = 1 - T n := by
  have hrange : Finset.range (n + 1) = insert 0 (Finset.Icc 1 n) := by
    ext m
    simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Icc]
    omega
  have h0 : altWeight 0 * (gb n 0 : ℤ) = 1 := by
    rw [altWeight_zero, gb_zero, Nat.cast_one, one_mul]
  have hsum : (∑ i ∈ Finset.Icc 1 n, altWeight i * (gb n i : ℤ))
      = -(∑ i ∈ Finset.Icc 1 n, (-1 : ℤ) ^ (i - 1) * (2 : ℤ) ^ (i.choose 2) * (gb n i : ℤ)) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    rw [altWeight_eq_neg i (Finset.mem_Icc.mp hi).1]
    ring
  simp only [F, T]
  rw [hrange, Finset.sum_insert (by simp [Finset.mem_Icc]), h0, hsum]
  ring

lemma T_eq_one (n : ℕ) (hn : 1 ≤ n) : T n = 1 := by
  have h1 := F_eq_one_sub_T n
  have h2 := F_eq_zero n hn
  linarith

/-- The "`q`-Möbius" sequence of arXiv:2209.04243 (proof of `lem:F2 helper`): for `n ≥ 1` and
`q = 2`, `∑_{i=1}^{n} (-1)^{i-1} q^{i(i-1)/2} [n choose i]_q = 1`, where `[n choose i]_q` is
the number of `i`-dimensional subspaces of `𝔽₂ⁿ`. -/
theorem alt_sum_eq_one {n : ℕ} (hn : 1 ≤ n) :
    ∑ i ∈ Finset.Icc 1 n, (-1 : ℤ) ^ (i - 1) * 2 ^ (i * (i - 1) / 2) *
      (Nat.card {W : Submodule (ZMod 2) (Fin n → ZMod 2) //
        Module.finrank (ZMod 2) W = i} : ℤ) = 1 := by
  have h : (∑ i ∈ Finset.Icc 1 n, (-1 : ℤ) ^ (i - 1) * 2 ^ (i * (i - 1) / 2) *
      (Nat.card {W : Submodule (ZMod 2) (Fin n → ZMod 2) //
        Module.finrank (ZMod 2) W = i} : ℤ)) = T n := by
    simp only [T, gb]
    apply Finset.sum_congr rfl
    intro i _
    rw [Nat.choose_two_right]
  rw [h, T_eq_one n hn]

end

end Commons.Combinatorics.QBinomial
