import Mathlib.Algebra.CharP.Defs
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseRowsL.LatticeCoulomb

/-- `∑_{M=1}^{N} 1/M² ≤ 2 - 1/N` for `N ≥ 1` (the elementary telescoping bound). -/
private lemma sum_Icc_inv_sq_le (N : ℕ) (hN : 1 ≤ N) :
    (∑ M ∈ Finset.Icc 1 N, (1 : ℝ) / (M : ℝ) ^ 2) ≤ 2 - 1 / (N : ℝ) := by
  induction N, hN using Nat.le_induction with
  | base => norm_num [Finset.Icc_self]
  | succ n hn ih =>
      rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ n + 1)]
      have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
      have hA : (1 : ℝ) / ((n : ℝ) + 1) ^ 2 ≤ 1 / ((n : ℝ) * ((n : ℝ) + 1)) := by
        refine one_div_le_one_div_of_le (by positivity) (by nlinarith)
      have hB : (1 : ℝ) / ((n : ℝ) * ((n : ℝ) + 1)) = 1 / (n : ℝ) - 1 / ((n : ℝ) + 1) := by
        field_simp
        ring
      have hcast : ((n + 1 : ℕ) : ℝ) = (n : ℝ) + 1 := by push_cast; ring
      rw [hcast]
      linarith [ih, hA, hB]

/-- `∑_{M=1}^{K} M = K(K+1)/2`. -/
private lemma sum_Icc_cast_id (K : ℕ) :
    (∑ M ∈ Finset.Icc 1 K, ((M : ℕ) : ℝ)) = (K : ℝ) * ((K : ℝ) + 1) / 2 := by
  induction K with
  | zero =>
      rw [Finset.Icc_eq_empty (by omega : ¬ 1 ≤ 0)]
      simp
  | succ k ih =>
      rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ k + 1), ih]
      push_cast
      ring

theorem telQSum (R : ℝ) (hR : 1 ≤ R) (N : ℕ) (hN : (N : ℝ) ≤ R) :
    (∑ M ∈ Finset.Icc 1 N,
        (8 * (M : ℝ)) * (27 / (10 * (M : ℝ) ^ 3) + min (10 / R ^ 2) (4 / (M : ℝ) ^ 2)))
      ≤ 92 := by
  rcases Nat.eq_zero_or_pos N with h0 | hpos
  · subst h0
    simp
  have hRpos : (0 : ℝ) < R := by linarith
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hpos
  set K : ℕ := N / 2 with hKdef
  -- termwise splitting of the summand
  have hterm : ∀ M ∈ Finset.Icc 1 N,
      (8 * (M : ℝ)) * (27 / (10 * (M : ℝ) ^ 3) + min (10 / R ^ 2) (4 / (M : ℝ) ^ 2))
      = (108 / 5) * (1 / (M : ℝ) ^ 2)
        + (8 * (M : ℝ)) * min (10 / R ^ 2) (4 / (M : ℝ) ^ 2) := by
    intro M hM
    rw [Finset.mem_Icc] at hM
    have hMpos : (M : ℝ) ≠ 0 := by
      have h1 : (1 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM.1
      linarith
    have h27 : (8 * (M : ℝ)) * (27 / (10 * (M : ℝ) ^ 3)) = (108 / 5) * (1 / (M : ℝ) ^ 2) := by
      field_simp
      ring
    rw [mul_add, h27]
  have hsum_split :
      (∑ M ∈ Finset.Icc 1 N,
          (8 * (M : ℝ)) * (27 / (10 * (M : ℝ) ^ 3) + min (10 / R ^ 2) (4 / (M : ℝ) ^ 2)))
      = (∑ M ∈ Finset.Icc 1 N, (108 / 5) * (1 / (M : ℝ) ^ 2))
        + (∑ M ∈ Finset.Icc 1 N, (8 * (M : ℝ)) * min (10 / R ^ 2) (4 / (M : ℝ) ^ 2)) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl hterm
  -- split the `min` sum at `K = N/2`
  have hset : Finset.Icc 1 N = Finset.Icc 1 K ∪ Finset.Icc (K + 1) N := by
    ext x
    simp only [Finset.mem_Icc, Finset.mem_union]
    omega
  have hdisj : Disjoint (Finset.Icc 1 K) (Finset.Icc (K + 1) N) := by
    rw [Finset.disjoint_left]
    intro x hx hx'
    simp only [Finset.mem_Icc] at hx hx'
    omega
  have hsum_min_split :
      (∑ M ∈ Finset.Icc 1 N, (8 * (M : ℝ)) * min (10 / R ^ 2) (4 / (M : ℝ) ^ 2))
      = (∑ M ∈ Finset.Icc 1 K, (8 * (M : ℝ)) * min (10 / R ^ 2) (4 / (M : ℝ) ^ 2))
        + (∑ M ∈ Finset.Icc (K + 1) N,
            (8 * (M : ℝ)) * min (10 / R ^ 2) (4 / (M : ℝ) ^ 2)) := by
    rw [hset, Finset.sum_union hdisj]
  -- bound the reciprocal-square part
  have hA : (∑ M ∈ Finset.Icc 1 N, (108 / 5) * (1 / (M : ℝ) ^ 2))
      ≤ (108 / 5) * (2 - 1 / (N : ℝ)) := by
    rw [← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left (sum_Icc_inv_sq_le N hpos) (by norm_num)
  -- bound the head (`M ≤ K = N/2`)
  have hH : (∑ M ∈ Finset.Icc 1 K, (8 * (M : ℝ)) * min (10 / R ^ 2) (4 / (M : ℝ) ^ 2))
      ≤ 10 + 20 / R := by
    have hstep : (∑ M ∈ Finset.Icc 1 K, (8 * (M : ℝ)) * min (10 / R ^ 2) (4 / (M : ℝ) ^ 2))
        ≤ ∑ M ∈ Finset.Icc 1 K, 80 * (M : ℝ) / R ^ 2 := by
      apply Finset.sum_le_sum
      intro M _
      have hle : min (10 / R ^ 2) (4 / (M : ℝ) ^ 2) ≤ 10 / R ^ 2 := min_le_left _ _
      calc (8 * (M : ℝ)) * min (10 / R ^ 2) (4 / (M : ℝ) ^ 2)
          ≤ (8 * (M : ℝ)) * (10 / R ^ 2) := mul_le_mul_of_nonneg_left hle (by positivity)
        _ = 80 * (M : ℝ) / R ^ 2 := by ring
    have hsum : (∑ M ∈ Finset.Icc 1 K, 80 * (M : ℝ) / R ^ 2)
        = (80 / R ^ 2) * (((K : ℝ) * ((K : ℝ) + 1)) / 2) := by
      have h1 : (∑ M ∈ Finset.Icc 1 K, 80 * (M : ℝ) / R ^ 2)
          = ∑ M ∈ Finset.Icc 1 K, (80 / R ^ 2) * (M : ℝ) := by
        apply Finset.sum_congr rfl
        intro M _
        ring
      rw [h1, ← Finset.mul_sum, sum_Icc_cast_id]
    have hKl : (K : ℝ) ≤ (N : ℝ) / 2 := by
      rw [hKdef]
      have h : ((N / 2 : ℕ) : ℝ) * 2 ≤ (N : ℝ) := by
        exact_mod_cast Nat.div_mul_le_self N 2
      linarith
    have h2 : (K : ℝ) * ((K : ℝ) + 1) ≤ ((N : ℝ) / 2) * ((N : ℝ) / 2 + 1) :=
      mul_le_mul hKl (by linarith) (by positivity) (by positivity)
    have hNsq : (N : ℝ) ^ 2 ≤ R ^ 2 := by
      have hNn : (0 : ℝ) ≤ (N : ℝ) := by positivity
      nlinarith [hN, hNn, hR]
    have hmain : (80 / R ^ 2) * (((K : ℝ) * ((K : ℝ) + 1)) / 2) ≤ 10 + 20 / R := by
      have hmono : (80 / R ^ 2) * (((K : ℝ) * ((K : ℝ) + 1)) / 2)
          ≤ (80 / R ^ 2) * ((((N : ℝ) / 2) * ((N : ℝ) / 2 + 1)) / 2) :=
        mul_le_mul_of_nonneg_left (by linarith [h2]) (by positivity)
      refine le_trans hmono ?_
      have heq : (80 / R ^ 2) * ((((N : ℝ) / 2) * ((N : ℝ) / 2 + 1)) / 2)
          = (10 * (N : ℝ) ^ 2 + 20 * (N : ℝ)) / R ^ 2 := by
        field_simp
        ring
      rw [heq]
      have hnum : 10 * (N : ℝ) ^ 2 + 20 * (N : ℝ) ≤ (10 + 20 / R) * R ^ 2 := by
        have hRne : R ≠ 0 := ne_of_gt hRpos
        field_simp
        nlinarith [hNsq, hN, hR]
      exact (div_le_iff₀ (by positivity : (0 : ℝ) < R ^ 2)).mpr hnum
    exact le_trans hstep (le_trans (by rw [hsum]) hmain)
  -- bound the tail (`M ≥ K+1 > N/2`)
  have hT : (∑ M ∈ Finset.Icc (K + 1) N,
        (8 * (M : ℝ)) * min (10 / R ^ 2) (4 / (M : ℝ) ^ 2)) ≤ 32 := by
    have hstep : (∑ M ∈ Finset.Icc (K + 1) N,
          (8 * (M : ℝ)) * min (10 / R ^ 2) (4 / (M : ℝ) ^ 2))
        ≤ ∑ M ∈ Finset.Icc (K + 1) N, 32 / (M : ℝ) := by
      apply Finset.sum_le_sum
      intro M hM
      rw [Finset.mem_Icc] at hM
      have hMpos : (0 : ℝ) < (M : ℝ) := by
        have h1 : 1 ≤ M := by omega
        have h2 : (1 : ℝ) ≤ (M : ℝ) := by exact_mod_cast h1
        linarith
      have hle : min (10 / R ^ 2) (4 / (M : ℝ) ^ 2) ≤ 4 / (M : ℝ) ^ 2 := min_le_right _ _
      have h32 : (8 * (M : ℝ)) * (4 / (M : ℝ) ^ 2) = 32 / (M : ℝ) := by
        field_simp
        ring
      calc (8 * (M : ℝ)) * min (10 / R ^ 2) (4 / (M : ℝ) ^ 2)
          ≤ (8 * (M : ℝ)) * (4 / (M : ℝ) ^ 2) :=
            mul_le_mul_of_nonneg_left hle (by positivity)
        _ = 32 / (M : ℝ) := h32
    have hstep2 : (∑ M ∈ Finset.Icc (K + 1) N, 32 / (M : ℝ))
        ≤ ∑ _M ∈ Finset.Icc (K + 1) N, 32 / ((K : ℝ) + 1) := by
      apply Finset.sum_le_sum
      intro M hM
      rw [Finset.mem_Icc] at hM
      have h1 : ((K : ℝ) + 1) ≤ (M : ℝ) := by exact_mod_cast hM.1
      have h2 : (0 : ℝ) < (K : ℝ) + 1 := by
        have : (0 : ℝ) ≤ (K : ℝ) := by positivity
        linarith
      exact div_le_div_of_nonneg_left (by norm_num) h2 h1
    have hNK : N + 1 - (K + 1) ≤ K + 1 := by
      have h : N ≤ 2 * K + 1 := by
        rw [hKdef]
        omega
      omega
    have hreal : ((N + 1 - (K + 1) : ℕ) : ℝ) ≤ (K : ℝ) + 1 := by
      have h := hNK
      exact_mod_cast h
    have hlast : (∑ _M ∈ Finset.Icc (K + 1) N, 32 / ((K : ℝ) + 1)) ≤ 32 := by
      rw [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul]
      have hpos : (0 : ℝ) < (K : ℝ) + 1 := by
        have : (0 : ℝ) ≤ (K : ℝ) := by positivity
        linarith
      calc ((N + 1 - (K + 1) : ℕ) : ℝ) * (32 / ((K : ℝ) + 1))
          ≤ ((K : ℝ) + 1) * (32 / ((K : ℝ) + 1)) :=
            mul_le_mul_of_nonneg_right hreal (by positivity)
        _ = 32 := by field_simp
    exact le_trans hstep (le_trans hstep2 hlast)
  have hfinal : (108 / 5) * (2 - 1 / (N : ℝ)) + ((10 + 20 / R) + 32) ≤ 92 := by
    have hN1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hpos
    have hinv : 1 / (N : ℝ) ≤ 1 := by
      simpa using one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1) hN1
    have hinvnn : (0 : ℝ) ≤ 1 / (N : ℝ) := by positivity
    have hdiv : 1 / R ≤ 1 / (N : ℝ) := one_div_le_one_div_of_le hNpos hN
    have h1 : (108 / 5) * (2 - 1 / (N : ℝ)) = 216 / 5 - (108 / 5) * (1 / (N : ℝ)) := by ring
    have h2 : ((10 + 20 / R) + 32) = 42 + 20 * (1 / R) := by ring
    rw [h1, h2]
    have h3 : 20 * (1 / R) ≤ 20 * (1 / (N : ℝ)) := by linarith [hdiv]
    linarith
  calc (∑ M ∈ Finset.Icc 1 N,
        (8 * (M : ℝ)) * (27 / (10 * (M : ℝ) ^ 3) + min (10 / R ^ 2) (4 / (M : ℝ) ^ 2)))
      = (∑ M ∈ Finset.Icc 1 N, (108 / 5) * (1 / (M : ℝ) ^ 2))
        + ((∑ M ∈ Finset.Icc 1 K, (8 * (M : ℝ)) * min (10 / R ^ 2) (4 / (M : ℝ) ^ 2))
          + (∑ M ∈ Finset.Icc (K + 1) N,
              (8 * (M : ℝ)) * min (10 / R ^ 2) (4 / (M : ℝ) ^ 2))) := by
        rw [hsum_split, hsum_min_split]
    _ ≤ (108 / 5) * (2 - 1 / (N : ℝ)) + ((10 + 20 / R) + 32) := add_le_add hA (add_le_add hH hT)
    _ ≤ 92 := hfinal

end Work.BoseRowsL.LatticeCoulomb
