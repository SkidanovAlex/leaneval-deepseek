import Mathlib
import Submission.Commons.NumberTheory.Totient.sum_inv_not_dvd_le_sum_mu_sq_div_totient
import Submission.Commons.NumberTheory.Harmonic.harm_ge_log_add_half

/-!
# `∑_{r ≤ z} μ(r)²/φ(r) − H_z ≥ 9/20` for `z ≥ 1001`

Lower bound for the squarefree-restricted totient sum `∑_{r ≤ z} μ(r)²/φ(r)`
(in the sense that it exceeds the harmonic number `H_z` by at least `9/20`),
for all `z ≥ 1001`.  Used in the Duffin–Schaeffer project.

**Math.**  Split `r` by its coprime-to-6 part (the recursion
`S(z) = S₆(z) + S₆(z/2) + S₆(z/3)/2 + S₆(z/6)/2`) and dominate the coprime sums
`S₆(y)` by the plain reciprocal sums `A₆(y)` over integers coprime to `6`
(via the radical bijection).  Expanding `A₆` against `A₂` and `A₂` against the
harmonic numbers turns the excess `S(z) − H_z` into a sum of explicit harmonic
differences, which are then bounded below using `log`.
-/

open scoped BigOperators
open Finset

namespace Commons.NumberTheory.Totient

open Commons.NumberTheory.Nat

private noncomputable def F (r : ℕ) : ℝ :=
  ((ArithmeticFunction.moebius r : ℤ) : ℝ) ^ 2 / (Nat.totient r : ℝ)

private lemma F_nonneg (r : ℕ) : 0 ≤ F r := by unfold F; positivity
private lemma F_two : F 2 = 1 := by
  unfold F
  rw [ArithmeticFunction.moebius_apply_prime (by norm_num : Nat.Prime 2),
      Nat.totient_prime (by norm_num : Nat.Prime 2)]; norm_num
private lemma F_three : F 3 = 1/2 := by
  unfold F
  rw [ArithmeticFunction.moebius_apply_prime (by norm_num : Nat.Prime 3),
      Nat.totient_prime (by norm_num : Nat.Prime 3)]; norm_num
private lemma F_six : F 6 = 1/2 := by
  unfold F
  rw [show (6:ℕ) = 2*3 by norm_num,
      ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime (by norm_num : (2:ℕ).Coprime 3),
      Nat.totient_mul (by norm_num : (2:ℕ).Coprime 3),
      ArithmeticFunction.moebius_apply_prime (by norm_num : Nat.Prime 2),
      ArithmeticFunction.moebius_apply_prime (by norm_num : Nat.Prime 3),
      Nat.totient_prime (by norm_num : Nat.Prime 2), Nat.totient_prime (by norm_num : Nat.Prime 3)]
  norm_num
private lemma F_mul {c m : ℕ} (hc : 1 ≤ c) (hm : 1 ≤ m) (h : c.Coprime m) :
    F (c*m) = F c * F m := by
  have hcφ : (Nat.totient c : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.totient_pos.mpr (by omega)).ne'
  have hmφ : (Nat.totient m : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.totient_pos.mpr (by omega)).ne'
  unfold F
  rw [ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime h, Nat.totient_mul h]
  push_cast
  field_simp
private lemma F_two_mul (m : ℕ) : F (2*m) = if 2 ∣ m then 0 else F m := by
  by_cases h : 2 ∣ m
  · obtain ⟨k, rfl⟩ := h
    have hnsf : ¬ Squarefree (2*(2*k)) := by
      intro hsf
      have h4 : (2:ℕ)*(2:ℕ) ∣ 2*(2*k) := ⟨k, by ring⟩
      exact (Nat.squarefree_iff_prime_squarefree.mp hsf 2 Nat.prime_two) h4
    rw [if_pos ⟨k, rfl⟩]
    unfold F
    rw [ArithmeticFunction.moebius_eq_zero_of_not_squarefree hnsf]; norm_num
  · rw [if_neg h]
    have hcop : (2:ℕ).Coprime m := (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).2 h
    rw [F_mul (by omega) (by omega) hcop, F_two, one_mul]
private lemma F_three_mul (m : ℕ) : F (3*m) = if 3 ∣ m then 0 else F m / 2 := by
  by_cases h : 3 ∣ m
  · obtain ⟨k, rfl⟩ := h
    have hnsf : ¬ Squarefree (3*(3*k)) := by
      intro hsf
      have h9 : (3:ℕ)*(3:ℕ) ∣ 3*(3*k) := ⟨k, by ring⟩
      exact (Nat.squarefree_iff_prime_squarefree.mp hsf 3 (by norm_num)) h9
    rw [if_pos ⟨k, rfl⟩]
    unfold F
    rw [ArithmeticFunction.moebius_eq_zero_of_not_squarefree hnsf]; norm_num
  · rw [if_neg h]
    have hcop : (3:ℕ).Coprime m := (Nat.Prime.coprime_iff_not_dvd (by norm_num : Nat.Prime 3)).2 h
    rw [F_mul (by omega) (by omega) hcop, F_three]; ring
private lemma F_six_mul (m : ℕ) : F (6*m) = if 2 ∣ m ∨ 3 ∣ m then 0 else F m / 2 := by
  by_cases h : 2 ∣ m ∨ 3 ∣ m
  · rw [if_pos h]
    have hnsf : ¬ Squarefree (6*m) := by
      intro hsf
      rcases h with h2 | h3
      · obtain ⟨k, rfl⟩ := h2
        have h4 : (2:ℕ)*(2:ℕ) ∣ 6*(2*k) := ⟨3*k, by ring⟩
        exact (Nat.squarefree_iff_prime_squarefree.mp hsf 2 Nat.prime_two) h4
      · obtain ⟨k, rfl⟩ := h3
        have h9 : (3:ℕ)*(3:ℕ) ∣ 6*(3*k) := ⟨2*k, by ring⟩
        exact (Nat.squarefree_iff_prime_squarefree.mp hsf 3 (by norm_num)) h9
    unfold F
    rw [ArithmeticFunction.moebius_eq_zero_of_not_squarefree hnsf]; norm_num
  · rw [if_neg h]
    push_neg at h
    obtain ⟨h2, h3⟩ := h
    have hcop : (6:ℕ).Coprime m := by
      rw [show (6:ℕ) = 2*3 by norm_num, Nat.coprime_mul_iff_left]
      exact ⟨(Nat.Prime.coprime_iff_not_dvd Nat.prime_two).2 h2,
        (Nat.Prime.coprime_iff_not_dvd (by norm_num : Nat.Prime 3)).2 h3⟩
    rw [F_mul (by omega) (by omega) hcop, F_six]; ring

private noncomputable def Sall (R : ℕ) : ℝ := ∑ r ∈ Finset.Icc 1 R, F r
private noncomputable def Scop (Y : ℕ) : ℝ := ∑ r ∈ (Finset.Icc 1 Y).filter (fun r => ¬ 2 ∣ r ∧ ¬ 3 ∣ r), F r

private lemma sum_reindex_two (R : ℕ) (p : ℕ → Prop) [DecidablePred p] (G : ℕ → ℝ) :
    (∑ r ∈ (Finset.Icc 1 R).filter (fun r => 2 ∣ r ∧ p r), G r)
      = ∑ m ∈ (Finset.Icc 1 (R/2)).filter (fun m => p (2*m)), G (2*m) := by
  have hset : (Finset.Icc 1 R).filter (fun r => 2 ∣ r ∧ p r)
      = ((Finset.Icc 1 (R/2)).filter (fun m => p (2*m))).image (fun m => 2*m) := by
    ext r
    simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_image]
    constructor
    · rintro ⟨⟨hr1, hrR⟩, h2, hp⟩
      obtain ⟨m, rfl⟩ := h2
      exact ⟨m, ⟨⟨by omega, by omega⟩, hp⟩, rfl⟩
    · rintro ⟨m, ⟨⟨hm1, hmR⟩, hp⟩, rfl⟩
      exact ⟨⟨by omega, by omega⟩, ⟨m, rfl⟩, hp⟩
  rw [hset, Finset.sum_image]
  intro a _ b _ hab
  simp only at hab
  omega
private lemma sum_reindex_three (R : ℕ) (p : ℕ → Prop) [DecidablePred p] (G : ℕ → ℝ) :
    (∑ r ∈ (Finset.Icc 1 R).filter (fun r => 3 ∣ r ∧ p r), G r)
      = ∑ m ∈ (Finset.Icc 1 (R/3)).filter (fun m => p (3*m)), G (3*m) := by
  have hset : (Finset.Icc 1 R).filter (fun r => 3 ∣ r ∧ p r)
      = ((Finset.Icc 1 (R/3)).filter (fun m => p (3*m))).image (fun m => 3*m) := by
    ext r
    simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_image]
    constructor
    · rintro ⟨⟨hr1, hrR⟩, h3, hp⟩
      obtain ⟨m, rfl⟩ := h3
      exact ⟨m, ⟨⟨by omega, by omega⟩, hp⟩, rfl⟩
    · rintro ⟨m, ⟨⟨hm1, hmR⟩, hp⟩, rfl⟩
      exact ⟨⟨by omega, by omega⟩, ⟨m, rfl⟩, hp⟩
  rw [hset, Finset.sum_image]
  intro a _ b _ hab
  simp only at hab
  omega
private lemma sum_reindex_six (R : ℕ) (G : ℕ → ℝ) :
    (∑ r ∈ (Finset.Icc 1 R).filter (fun r => 6 ∣ r), G r)
      = ∑ m ∈ (Finset.Icc 1 (R/6)), G (6*m) := by
  have hset : (Finset.Icc 1 R).filter (fun r => 6 ∣ r)
      = (Finset.Icc 1 (R/6)).image (fun m => 6*m) := by
    ext r
    simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_image]
    constructor
    · rintro ⟨⟨hr1, hrR⟩, h6⟩
      obtain ⟨m, rfl⟩ := h6
      exact ⟨m, ⟨by omega, by omega⟩, rfl⟩
    · rintro ⟨m, ⟨hm1, hmR⟩, rfl⟩
      exact ⟨⟨by omega, by omega⟩, ⟨m, rfl⟩⟩
  rw [hset, Finset.sum_image]
  intro a _ b _ hab
  simp only at hab
  omega

private lemma not_three_dvd_two_mul (m : ℕ) : ¬ 3 ∣ 2*m ↔ ¬ 3 ∣ m := by
  have h3 : Nat.Prime 3 := by norm_num
  constructor
  · intro h h3m; exact h (dvd_mul_of_dvd_right h3m 2)
  · intro h h32m
    rcases (h3.dvd_mul.mp h32m) with h32 | h3m
    · exact absurd h32 (by norm_num)
    · exact h h3m

private lemma not_two_dvd_three_mul (m : ℕ) : ¬ 2 ∣ 3*m ↔ ¬ 2 ∣ m := by
  constructor
  · intro h h2m; exact h (dvd_mul_of_dvd_right h2m 3)
  · intro h h23m
    rcases (Nat.prime_two.dvd_mul.mp h23m) with h23 | h2m
    · exact absurd h23 (by norm_num)
    · exact h h2m

private lemma six_iff (r : ℕ) : (2 ∣ r ∧ 3 ∣ r) ↔ 6 ∣ r := by
  constructor
  · rintro ⟨h2, h3⟩
    have := Nat.lcm_dvd h2 h3
    rwa [show Nat.lcm 2 3 = 6 by norm_num] at this
  · intro h; exact ⟨dvd_trans (by norm_num : (2:ℕ) ∣ 6) h, dvd_trans (by norm_num : (3:ℕ) ∣ 6) h⟩

private lemma Sall_eq (R : ℕ) :
    Sall R = Scop R + Scop (R/2) + (1/2)*Scop (R/3) + (1/2)*Scop (R/6) := by
  have hsplit : Sall R
      = (∑ r ∈ (Finset.Icc 1 R).filter (fun r => ¬2∣r ∧ ¬3∣r), F r)
      + (∑ r ∈ (Finset.Icc 1 R).filter (fun r => 2∣r ∧ ¬3∣r), F r)
      + (∑ r ∈ (Finset.Icc 1 R).filter (fun r => ¬2∣r ∧ 3∣r), F r)
      + (∑ r ∈ (Finset.Icc 1 R).filter (fun r => 2∣r ∧ 3∣r), F r) := by
    have h2 := Finset.sum_filter_add_sum_filter_not (Finset.Icc 1 R) (fun r => 2∣r) F
    have h3a := Finset.sum_filter_add_sum_filter_not ((Finset.Icc 1 R).filter (fun r => 2∣r)) (fun r => 3∣r) F
    have h3b := Finset.sum_filter_add_sum_filter_not ((Finset.Icc 1 R).filter (fun r => ¬2∣r)) (fun r => 3∣r) F
    rw [Finset.filter_filter, Finset.filter_filter] at h3a
    rw [Finset.filter_filter, Finset.filter_filter] at h3b
    unfold Sall
    linarith [h2, h3a, h3b]
  have e1 : (∑ r ∈ (Finset.Icc 1 R).filter (fun r => ¬2∣r ∧ ¬3∣r), F r) = Scop R := rfl
  have e2 : (∑ r ∈ (Finset.Icc 1 R).filter (fun r => 2∣r ∧ ¬3∣r), F r) = Scop (R/2) := by
    rw [sum_reindex_two R (fun r => ¬ 3 ∣ r) F]
    rw [show (Finset.Icc 1 (R/2)).filter (fun m => ¬ 3 ∣ 2*m)
          = (Finset.Icc 1 (R/2)).filter (fun m => ¬ 3 ∣ m) from by
        apply Finset.filter_congr; intro m _; exact not_three_dvd_two_mul m]
    unfold Scop
    calc (∑ m ∈ (Finset.Icc 1 (R/2)).filter (fun m => ¬ 3 ∣ m), F (2*m))
        = ∑ m ∈ (Finset.Icc 1 (R/2)).filter (fun m => ¬ 3 ∣ m), (if 2 ∣ m then (0:ℝ) else F m) :=
          Finset.sum_congr rfl (fun m _ => F_two_mul m)
      _ = ∑ m ∈ (Finset.Icc 1 (R/2)), if (¬ 3 ∣ m) then (if 2 ∣ m then 0 else F m) else 0 :=
          Finset.sum_filter _ _
      _ = ∑ m ∈ (Finset.Icc 1 (R/2)), if (¬ 2 ∣ m ∧ ¬ 3 ∣ m) then F m else 0 := by
          apply Finset.sum_congr rfl; intro m _
          by_cases h2 : 2 ∣ m <;> by_cases h3 : 3 ∣ m <;> simp [h2, h3]
      _ = ∑ m ∈ (Finset.Icc 1 (R/2)).filter (fun m => ¬ 2 ∣ m ∧ ¬ 3 ∣ m), F m :=
          (Finset.sum_filter _ _).symm
  have e3 : (∑ r ∈ (Finset.Icc 1 R).filter (fun r => ¬2∣r ∧ 3∣r), F r) = (1/2)*Scop (R/3) := by
    rw [show (Finset.Icc 1 R).filter (fun r => ¬2∣r ∧ 3∣r)
          = (Finset.Icc 1 R).filter (fun r => 3∣r ∧ ¬2∣r) from by
        apply Finset.filter_congr; intro r _; tauto]
    rw [sum_reindex_three R (fun r => ¬ 2 ∣ r) F]
    rw [show (Finset.Icc 1 (R/3)).filter (fun m => ¬ 2 ∣ 3*m)
          = (Finset.Icc 1 (R/3)).filter (fun m => ¬ 2 ∣ m) from by
        apply Finset.filter_congr; intro m _; exact not_two_dvd_three_mul m]
    unfold Scop
    calc (∑ m ∈ (Finset.Icc 1 (R/3)).filter (fun m => ¬ 2 ∣ m), F (3*m))
        = ∑ m ∈ (Finset.Icc 1 (R/3)).filter (fun m => ¬ 2 ∣ m), (if 3 ∣ m then (0:ℝ) else F m / 2) :=
          Finset.sum_congr rfl (fun m _ => F_three_mul m)
      _ = ∑ m ∈ (Finset.Icc 1 (R/3)), if (¬ 2 ∣ m) then (if 3 ∣ m then 0 else F m / 2) else 0 :=
          Finset.sum_filter _ _
      _ = (1/2) * ∑ m ∈ (Finset.Icc 1 (R/3)).filter (fun m => ¬ 2 ∣ m ∧ ¬ 3 ∣ m), F m := by
          rw [Finset.mul_sum, Finset.sum_filter]
          apply Finset.sum_congr rfl; intro m _
          by_cases h2 : 2 ∣ m <;> by_cases h3 : 3 ∣ m <;> simp [h2, h3] <;> ring
  have e4 : (∑ r ∈ (Finset.Icc 1 R).filter (fun r => 2∣r ∧ 3∣r), F r) = (1/2)*Scop (R/6) := by
    rw [show (Finset.Icc 1 R).filter (fun r => 2∣r ∧ 3∣r)
          = (Finset.Icc 1 R).filter (fun r => 6∣r) from by
        apply Finset.filter_congr; intro r _; exact six_iff r]
    rw [sum_reindex_six R F]
    unfold Scop
    calc (∑ m ∈ Finset.Icc 1 (R/6), F (6*m))
        = ∑ m ∈ Finset.Icc 1 (R/6), (if 2 ∣ m ∨ 3 ∣ m then (0:ℝ) else F m / 2) :=
          Finset.sum_congr rfl (fun m _ => F_six_mul m)
      _ = ∑ m ∈ Finset.Icc 1 (R/6), if (¬ 2 ∣ m ∧ ¬ 3 ∣ m) then (F m / 2) else 0 := by
          apply Finset.sum_congr rfl; intro m _
          by_cases h2 : 2 ∣ m <;> by_cases h3 : 3 ∣ m <;> simp [h2, h3]
      _ = (1/2) * ∑ m ∈ (Finset.Icc 1 (R/6)).filter (fun m => ¬ 2 ∣ m ∧ ¬ 3 ∣ m), F m := by
          rw [Finset.mul_sum, Finset.sum_filter]
          apply Finset.sum_congr rfl; intro m _
          by_cases h2 : 2 ∣ m <;> by_cases h3 : 3 ∣ m <;> simp [h2, h3] <;> ring
  rw [hsplit, e1, e2, e3, e4]

private noncomputable def A2 (Y : ℕ) : ℝ := ∑ n ∈ (Finset.Icc 1 Y).filter (fun n => ¬ 2 ∣ n), (1:ℝ)/n
private noncomputable def A6 (Y : ℕ) : ℝ := ∑ n ∈ (Finset.Icc 1 Y).filter (fun n => ¬ 2 ∣ n ∧ ¬ 3 ∣ n), (1:ℝ)/n


private lemma A6_le_Scop (Y : ℕ) : A6 Y ≤ Scop Y := by
  unfold A6 Scop F
  have h := Commons.NumberTheory.Totient.sum_inv_not_dvd_le_sum_mu_sq_div_totient Y ({2,3} : Finset ℕ) (by
    intro p hp
    rw [Finset.mem_insert, Finset.mem_singleton] at hp
    rcases hp with rfl | rfl <;> norm_num)
  simpa using h

private lemma harmonic_cast_Icc (Y : ℕ) : (harmonic Y : ℝ) = ∑ n ∈ Finset.Icc 1 Y, (1:ℝ)/n := by
  rw [harmonic_eq_sum_Icc]
  push_cast
  apply Finset.sum_congr rfl
  intro i _
  rw [one_div]

private lemma sum_reindex_two' (R : ℕ) (G : ℕ → ℝ) :
    (∑ r ∈ (Finset.Icc 1 R).filter (fun r => 2 ∣ r), G r)
      = ∑ m ∈ Finset.Icc 1 (R/2), G (2*m) := by
  have hset : (Finset.Icc 1 R).filter (fun r => 2 ∣ r)
      = (Finset.Icc 1 (R/2)).image (fun m => 2*m) := by
    ext r
    simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_image]
    constructor
    · rintro ⟨⟨hr1, hrR⟩, h2⟩
      obtain ⟨m, rfl⟩ := h2
      exact ⟨m, ⟨by omega, by omega⟩, rfl⟩
    · rintro ⟨m, ⟨hm1, hmR⟩, rfl⟩
      exact ⟨⟨by omega, by omega⟩, ⟨m, rfl⟩⟩
  rw [hset, Finset.sum_image]
  intro a _ b _ hab
  simp only at hab
  omega

private lemma sum_reindex_three' (R : ℕ) (G : ℕ → ℝ) :
    (∑ r ∈ (Finset.Icc 1 R).filter (fun r => 3 ∣ r), G r)
      = ∑ m ∈ Finset.Icc 1 (R/3), G (3*m) := by
  have hset : (Finset.Icc 1 R).filter (fun r => 3 ∣ r)
      = (Finset.Icc 1 (R/3)).image (fun m => 3*m) := by
    ext r
    simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_image]
    constructor
    · rintro ⟨⟨hr1, hrR⟩, h3⟩
      obtain ⟨m, rfl⟩ := h3
      exact ⟨m, ⟨by omega, by omega⟩, rfl⟩
    · rintro ⟨m, ⟨hm1, hmR⟩, rfl⟩
      exact ⟨⟨by omega, by omega⟩, ⟨m, rfl⟩⟩
  rw [hset, Finset.sum_image]
  intro a _ b _ hab
  simp only at hab
  omega

private lemma A2_eq (Y : ℕ) :
    A2 Y = (harmonic Y : ℝ) - (1/2)*(harmonic (Y/2) : ℝ) := by
  have hsplit := Finset.sum_filter_add_sum_filter_not (Finset.Icc 1 Y) (fun n => 2∣n) (fun n => (1:ℝ)/n)
  have heven : (∑ n ∈ (Finset.Icc 1 Y).filter (fun n => 2∣n), (1:ℝ)/n)
      = (1/2)*(harmonic (Y/2) : ℝ) := by
    rw [sum_reindex_two' Y (fun n => (1:ℝ)/n), harmonic_cast_Icc (Y/2), Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro m _
    rw [Nat.cast_mul]
    ring_nf
  unfold A2
  rw [harmonic_cast_Icc Y]
  linarith [hsplit, heven]

private lemma A6_eq (Y : ℕ) : A6 Y = A2 Y - (1/3)*A2 (Y/3) := by
  have hsplit : A2 Y = A6 Y + (∑ n ∈ (Finset.Icc 1 Y).filter (fun n => ¬2∣n ∧ 3∣n), (1:ℝ)/n) := by
    unfold A2 A6
    have h := Finset.sum_filter_add_sum_filter_not ((Finset.Icc 1 Y).filter (fun n => ¬2∣n)) (fun n => 3∣n) (fun n => (1:ℝ)/n)
    rw [Finset.filter_filter, Finset.filter_filter] at h
    linarith [h]
  have hthree : (∑ n ∈ (Finset.Icc 1 Y).filter (fun n => ¬2∣n ∧ 3∣n), (1:ℝ)/n)
      = (1/3)*A2 (Y/3) := by
    rw [show (Finset.Icc 1 Y).filter (fun n => ¬2∣n ∧ 3∣n)
          = (Finset.Icc 1 Y).filter (fun n => 3∣n ∧ ¬2∣n) from by
        apply Finset.filter_congr; intro n _; tauto]
    rw [sum_reindex_three Y (fun r => ¬ 2 ∣ r) (fun r => (1:ℝ)/r)]
    rw [show (Finset.Icc 1 (Y/3)).filter (fun m => ¬ 2 ∣ 3*m)
          = (Finset.Icc 1 (Y/3)).filter (fun m => ¬ 2 ∣ m) from by
        apply Finset.filter_congr; intro m _; exact not_two_dvd_three_mul m]
    unfold A2
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro m _
    rw [Nat.cast_mul]
    ring_nf
  linarith [hsplit, hthree]

private lemma harmonic_sub_eq_sum (a b : ℕ) (hab : a ≤ b) :
    (harmonic b : ℝ) - (harmonic a : ℝ) = ∑ n ∈ Finset.Icc (a+1) b, (1:ℝ)/n := by
  rw [Commons.NumberTheory.Harmonic.harmonic_cast_eq_sum,
      Commons.NumberTheory.Harmonic.harmonic_cast_eq_sum,
      ← Finset.sum_Ico_eq_sub (fun i => ((i:ℝ)+1)⁻¹) hab]
  have hstep : (∑ i ∈ Finset.Ico a b, ((i:ℝ)+1)⁻¹)
      = ∑ n ∈ Finset.Icc (a+1) b, ((n:ℝ))⁻¹ := by
    rw [show (∑ i ∈ Finset.Ico a b, ((i:ℝ)+1)⁻¹)
          = ∑ i ∈ Finset.Ico a b, (((i+1:ℕ):ℝ))⁻¹ from
        Finset.sum_congr rfl (fun x hx => by push_cast; ring)]
    rw [Finset.sum_Ico_add' (fun n : ℕ => ((n:ℝ))⁻¹) a b 1]
    rw [show Finset.Ico (a+1) (b+1) = Finset.Icc (a+1) b from Finset.Ico_succ_right_eq_Icc (a+1) b]
  rw [hstep]
  apply Finset.sum_congr rfl
  intro x hx
  simp [one_div]

private lemma harmonic_sub_ge_log (a b : ℕ) (hab : a ≤ b) :
    Real.log ((b:ℝ)+1) - Real.log ((a:ℝ)+1) ≤ (harmonic b : ℝ) - (harmonic a : ℝ) := by
  rw [harmonic_sub_eq_sum a b hab]
  have htel : (∑ n ∈ Finset.Icc (a+1) b, (Real.log ((n:ℝ)+1) - Real.log (n:ℝ)))
      = Real.log ((b:ℝ)+1) - Real.log ((a:ℝ)+1) := by
    rw [show Finset.Icc (a+1) b = Finset.Ico (a+1) (b+1) from
        (Finset.Ico_succ_right_eq_Icc (a+1) b).symm]
    rw [show (∑ n ∈ Finset.Ico (a+1) (b+1), (Real.log ((n:ℝ)+1) - Real.log (n:ℝ)))
          = ∑ n ∈ Finset.Ico (a+1) (b+1), (Real.log ((n+1:ℕ):ℝ) - Real.log ((n:ℕ):ℝ)) from
        Finset.sum_congr rfl (fun n _ => by push_cast; ring)]
    rw [Finset.sum_Ico_sub (fun n : ℕ => Real.log ((n:ℕ):ℝ)) (by omega : a+1 ≤ b+1)]
    push_cast
    ring
  rw [← htel]
  apply Finset.sum_le_sum
  intro n hn
  rw [Finset.mem_Icc] at hn
  have hn1 : (1:ℕ) ≤ n := by omega
  have hpos : (0:ℝ) < (n:ℝ) := by exact_mod_cast hn1
  have hlog : Real.log ((n:ℝ)+1) - Real.log (n:ℝ) = Real.log (((n:ℝ)+1)/(n:ℝ)) := by
    rw [Real.log_div (by positivity) (by positivity)]
  rw [hlog]
  have hx : (0:ℝ) < ((n:ℝ)+1)/(n:ℝ) := by positivity
  calc Real.log (((n:ℝ)+1)/(n:ℝ)) ≤ ((n:ℝ)+1)/(n:ℝ) - 1 := Real.log_le_sub_one_of_pos hx
    _ = 1/(n:ℝ) := by field_simp; ring

private lemma harmonic_sub_le_log (a b : ℕ) (h1 : 1 ≤ a) (hab : a ≤ b) :
    (harmonic b : ℝ) - (harmonic a : ℝ) ≤ Real.log (b:ℝ) - Real.log (a:ℝ) := by
  rw [harmonic_sub_eq_sum a b hab]
  have htel : (∑ n ∈ Finset.Icc (a+1) b, (Real.log (n:ℝ) - Real.log ((n:ℝ)-1)))
      = Real.log (b:ℝ) - Real.log (a:ℝ) := by
    rw [show Finset.Icc (a+1) b = Finset.Ico (a+1) (b+1) from
        (Finset.Ico_succ_right_eq_Icc (a+1) b).symm]
    rw [show (∑ n ∈ Finset.Ico (a+1) (b+1), (Real.log (n:ℝ) - Real.log ((n:ℝ)-1)))
          = ∑ n ∈ Finset.Ico (a+1) (b+1),
              (Real.log (((n+1:ℕ):ℝ)-1) - Real.log (((n:ℕ):ℝ)-1)) from
        Finset.sum_congr rfl (fun n _ => by push_cast; ring)]
    rw [Finset.sum_Ico_sub (fun n : ℕ => Real.log (((n:ℕ):ℝ)-1)) (by omega : a+1 ≤ b+1)]
    rw [show ((b+1:ℕ):ℝ)-1 = (b:ℝ) by push_cast; ring]
    rw [show ((a+1:ℕ):ℝ)-1 = (a:ℝ) by push_cast; ring]
  rw [← htel]
  apply Finset.sum_le_sum
  intro n hn
  rw [Finset.mem_Icc] at hn
  have hn2 : 2 ≤ n := by omega
  have hnR : (1:ℝ) < (n:ℝ) := by exact_mod_cast (by omega : 1 < n)
  have hpos : (0:ℝ) < (n:ℝ)/((n:ℝ)-1) := by
    apply div_pos <;> linarith
  have hlog : Real.log (n:ℝ) - Real.log ((n:ℝ)-1) = Real.log ((n:ℝ)/((n:ℝ)-1)) := by
    rw [Real.log_div (by linarith) (by linarith)]
  rw [hlog]
  have hone := Real.one_sub_inv_le_log_of_pos hpos
  have hinv : ((n:ℝ)/((n:ℝ)-1))⁻¹ = ((n:ℝ)-1)/(n:ℝ) := by rw [inv_div]
  rw [hinv] at hone
  have h1n : 1 - ((n:ℝ)-1)/(n:ℝ) = 1/(n:ℝ) := by field_simp; ring
  linarith [hone, h1n.le, h1n.ge]

private lemma log_one_sub_ge (y : ℝ) (hy0 : 0 ≤ y) (hy : y ≤ 1/2) :
    -(2*y) ≤ Real.log (1-y) := by
  have hy1 : (0:ℝ) < 1-y := by linarith
  have h := Real.log_le_sub_one_of_pos (show (0:ℝ) < 1/(1-y) by positivity)
  have hlog : Real.log (1/(1-y)) = - Real.log (1-y) := by
    rw [one_div, Real.log_inv]
  rw [hlog] at h
  have heq : 1/(1-y) - 1 = y/(1-y) := by field_simp; ring
  rw [heq] at h
  have hle : y/(1-y) ≤ 2*y := by
    rw [div_le_iff₀ hy1]; nlinarith
  linarith

private lemma ratio1 (z : ℕ) (hz : 1001 ≤ z) :
    (2002:ℝ)/1005 ≤ (((z/2:ℕ):ℝ)+1)/(((z/4:ℕ):ℝ)+1) := by
  have hzr : (1001:ℝ) ≤ (z:ℝ) := by exact_mod_cast hz
  have hnum : (z:ℝ)/2 ≤ ((z/2:ℕ):ℝ)+1 := by
    have h2 : z ≤ 2*(z/2)+1 := by omega
    have h2r : (z:ℝ) ≤ 2*((z/2:ℕ):ℝ)+1 := by exact_mod_cast h2
    linarith
  have hden : ((z/4:ℕ):ℝ)+1 ≤ (z:ℝ)/4 + 1 := by
    have h4 : ((z/4:ℕ):ℝ) ≤ (z:ℝ)/4 := by
      have h := Nat.div_mul_le_self z 4
      have h' : ((z/4:ℕ):ℝ)*4 ≤ (z:ℝ) := by exact_mod_cast (by simpa using h)
      linarith
    linarith
  have hdenpos : (0:ℝ) < ((z/4:ℕ):ℝ)+1 := by positivity
  rw [le_div_iff₀ hdenpos]
  have h1 : (2002:ℝ)/1005 * (((z/4:ℕ):ℝ)+1) ≤ (2002:ℝ)/1005 * ((z:ℝ)/4+1) :=
    mul_le_mul_of_nonneg_left hden (by norm_num)
  have h2 : (2002:ℝ)/1005 * ((z:ℝ)/4+1) ≤ (z:ℝ)/2 := by nlinarith [hzr]
  linarith [h1, h2, hnum]

private lemma ratio2 (z : ℕ) (hz : 1001 ≤ z) :
    (3003:ℝ)/1010 ≤ (((z/3:ℕ):ℝ)+1)/(((z/9:ℕ):ℝ)+1) := by
  have hzr : (1001:ℝ) ≤ (z:ℝ) := by exact_mod_cast hz
  have hnum : (z:ℝ)/3 ≤ ((z/3:ℕ):ℝ)+1 := by
    have h2 : z ≤ 3*(z/3)+2 := by omega
    have h2r : (z:ℝ) ≤ 3*((z/3:ℕ):ℝ)+2 := by exact_mod_cast h2
    linarith
  have hden : ((z/9:ℕ):ℝ)+1 ≤ (z:ℝ)/9 + 1 := by
    have h4 : ((z/9:ℕ):ℝ) ≤ (z:ℝ)/9 := by
      have h := Nat.div_mul_le_self z 9
      have h' : ((z/9:ℕ):ℝ)*9 ≤ (z:ℝ) := by exact_mod_cast (by simpa using h)
      linarith
    linarith
  have hdenpos : (0:ℝ) < ((z/9:ℕ):ℝ)+1 := by positivity
  rw [le_div_iff₀ hdenpos]
  have h1 : (3003:ℝ)/1010 * (((z/9:ℕ):ℝ)+1) ≤ (3003:ℝ)/1010 * ((z:ℝ)/9+1) :=
    mul_le_mul_of_nonneg_left hden (by norm_num)
  have h2 : (3003:ℝ)/1010 * ((z:ℝ)/9+1) ≤ (z:ℝ)/3 := by nlinarith [hzr]
  linarith [h1, h2, hnum]

private lemma ratio3 (z : ℕ) (hz : 1001 ≤ z) :
    (3003:ℝ)/1019 ≤ (((z/6:ℕ):ℝ)+1)/(((z/18:ℕ):ℝ)+1) := by
  have hzr : (1001:ℝ) ≤ (z:ℝ) := by exact_mod_cast hz
  have hnum : (z:ℝ)/6 ≤ ((z/6:ℕ):ℝ)+1 := by
    have h2 : z ≤ 6*(z/6)+5 := by omega
    have h2r : (z:ℝ) ≤ 6*((z/6:ℕ):ℝ)+5 := by exact_mod_cast h2
    linarith
  have hden : ((z/18:ℕ):ℝ)+1 ≤ (z:ℝ)/18 + 1 := by
    have h4 : ((z/18:ℕ):ℝ) ≤ (z:ℝ)/18 := by
      have h := Nat.div_mul_le_self z 18
      have h' : ((z/18:ℕ):ℝ)*18 ≤ (z:ℝ) := by exact_mod_cast (by simpa using h)
      linarith
    linarith
  have hdenpos : (0:ℝ) < ((z/18:ℕ):ℝ)+1 := by positivity
  rw [le_div_iff₀ hdenpos]
  have h1 : (3003:ℝ)/1019 * (((z/18:ℕ):ℝ)+1) ≤ (3003:ℝ)/1019 * ((z:ℝ)/18+1) :=
    mul_le_mul_of_nonneg_left hden (by norm_num)
  have h2 : (3003:ℝ)/1019 * ((z:ℝ)/18+1) ≤ (z:ℝ)/6 := by nlinarith [hzr]
  linarith [h1, h2, hnum]

private lemma log2002 : Real.log 2 - 8/1005 ≤ Real.log ((2002:ℝ)/1005) := by
  have h : (2002:ℝ)/1005 = 2*(1 - 4/1005) := by norm_num
  rw [h, Real.log_mul (by norm_num) (by norm_num)]
  have := log_one_sub_ge (4/1005) (by norm_num) (by norm_num)
  linarith

private lemma log3003_1010 : Real.log 3 - 18/1010 ≤ Real.log ((3003:ℝ)/1010) := by
  have h : (3003:ℝ)/1010 = 3*(1 - 9/1010) := by norm_num
  rw [h, Real.log_mul (by norm_num) (by norm_num)]
  have := log_one_sub_ge (9/1010) (by norm_num) (by norm_num)
  linarith

private lemma log3003_1019 : Real.log 3 - 36/1019 ≤ Real.log ((3003:ℝ)/1019) := by
  have h : (3003:ℝ)/1019 = 3*(1 - 18/1019) := by norm_num
  rw [h, Real.log_mul (by norm_num) (by norm_num)]
  have := log_one_sub_ge (18/1019) (by norm_num) (by norm_num)
  linarith

private lemma log3_ge : (1.0264805:ℝ) ≤ Real.log 3 := by
  have h2 := Real.log_two_gt_d9
  have h32 : (1/3:ℝ) ≤ Real.log (3/2) := by
    have := Real.one_sub_inv_le_log_of_pos (show (0:ℝ) < 3/2 by norm_num)
    norm_num at this
    linarith
  have hmul : Real.log 3 = Real.log 2 + Real.log (3/2) := by
    rw [← Real.log_mul (by norm_num : (2:ℝ) ≠ 0) (by norm_num : (3/2:ℝ) ≠ 0)]
    norm_num
  linarith [h2, h32, hmul]

private lemma upper2 (z : ℕ) (hz : 1001 ≤ z) :
    (harmonic (z/6) : ℝ) - (harmonic (z/18) : ℝ) ≤ Real.log 3 + 18/983 := by
  have h18 : (1:ℕ) ≤ z/18 := by omega
  have hle : z/18 ≤ z/6 := by omega
  have hl := harmonic_sub_le_log (z/18) (z/6) h18 hle
  have hzr : (1001:ℝ) ≤ (z:ℝ) := by exact_mod_cast hz
  have hB : (0:ℝ) < ((z/18:ℕ):ℝ) := by
    have : (0:ℕ) < z/18 := by omega
    exact_mod_cast this
  have hA : (0:ℝ) < ((z/6:ℕ):ℝ) := by
    have : (0:ℕ) < z/6 := by omega
    exact_mod_cast this
  have hz18 : (0:ℝ) < (z:ℝ)-18 := by linarith
  have hratio : (((z/6:ℕ):ℝ))/(((z/18:ℕ):ℝ)) ≤ 3*(z:ℝ)/((z:ℝ)-18) := by
    rw [div_le_iff₀ hB, div_mul_eq_mul_div, le_div_iff₀ hz18]
    have hnum : ((z/6:ℕ):ℝ) ≤ (z:ℝ)/6 := by
      have h := Nat.div_mul_le_self z 6
      have h' : ((z/6:ℕ):ℝ)*6 ≤ (z:ℝ) := by exact_mod_cast (by simpa using h)
      linarith
    have hden : (z:ℝ)-18 ≤ 18*((z/18:ℕ):ℝ) := by
      have h : z ≤ 18*(z/18)+17 := by omega
      have h' : (z:ℝ) ≤ 18*((z/18:ℕ):ℝ)+17 := by exact_mod_cast h
      linarith
    nlinarith [hnum, hden]
  have hlogeq : Real.log ((z/6:ℕ):ℝ) - Real.log ((z/18:ℕ):ℝ)
      = Real.log (((z/6:ℕ):ℝ)/((z/18:ℕ):ℝ)) := (Real.log_div (ne_of_gt hA) (ne_of_gt hB)).symm
  have hmb : Real.log (((z/6:ℕ):ℝ)/((z/18:ℕ):ℝ)) ≤ Real.log 3 + 18/983 := by
    have hmono : Real.log (((z/6:ℕ):ℝ)/((z/18:ℕ):ℝ)) ≤ Real.log (3*(z:ℝ)/((z:ℝ)-18)) :=
      Real.log_le_log (by positivity) hratio
    have hsplit : Real.log (3*(z:ℝ)/((z:ℝ)-18)) = Real.log 3 + Real.log ((z:ℝ)/((z:ℝ)-18)) := by
      rw [show 3*(z:ℝ)/((z:ℝ)-18) = 3*((z:ℝ)/((z:ℝ)-18)) by ring,
          Real.log_mul (by norm_num : (3:ℝ)≠0) (by positivity)]
    have htail : Real.log ((z:ℝ)/((z:ℝ)-18)) ≤ 18/983 := by
      have h1 : (z:ℝ)/((z:ℝ)-18) = 1 + 18/((z:ℝ)-18) := by field_simp; ring
      rw [h1]
      have hlog := Real.log_le_sub_one_of_pos (show (0:ℝ) < 1 + 18/((z:ℝ)-18) by positivity)
      have hle18 : 18/((z:ℝ)-18) ≤ 18/983 := by
        rw [div_le_iff₀ hz18, div_mul_eq_mul_div, le_div_iff₀ (by norm_num : (0:ℝ) < 983)]
        nlinarith [hzr]
      linarith
    linarith [hmono, hsplit, htail]
  linarith [hl, hlogeq, hmb]

private lemma upper3 (z : ℕ) (hz : 1001 ≤ z) :
    (harmonic (z/12) : ℝ) - (harmonic (z/36) : ℝ) ≤ Real.log 3 + 36/965 := by
  have h36 : (1:ℕ) ≤ z/36 := by omega
  have hle : z/36 ≤ z/12 := by omega
  have hl := harmonic_sub_le_log (z/36) (z/12) h36 hle
  have hzr : (1001:ℝ) ≤ (z:ℝ) := by exact_mod_cast hz
  have hB : (0:ℝ) < ((z/36:ℕ):ℝ) := by
    have : (0:ℕ) < z/36 := by omega
    exact_mod_cast this
  have hA : (0:ℝ) < ((z/12:ℕ):ℝ) := by
    have : (0:ℕ) < z/12 := by omega
    exact_mod_cast this
  have hz36 : (0:ℝ) < (z:ℝ)-36 := by linarith
  have hratio : (((z/12:ℕ):ℝ))/(((z/36:ℕ):ℝ)) ≤ 3*(z:ℝ)/((z:ℝ)-36) := by
    rw [div_le_iff₀ hB, div_mul_eq_mul_div, le_div_iff₀ hz36]
    have hnum : ((z/12:ℕ):ℝ) ≤ (z:ℝ)/12 := by
      have h := Nat.div_mul_le_self z 12
      have h' : ((z/12:ℕ):ℝ)*12 ≤ (z:ℝ) := by exact_mod_cast (by simpa using h)
      linarith
    have hden : (z:ℝ)-36 ≤ 36*((z/36:ℕ):ℝ) := by
      have h : z ≤ 36*(z/36)+35 := by omega
      have h' : (z:ℝ) ≤ 36*((z/36:ℕ):ℝ)+35 := by exact_mod_cast h
      linarith
    nlinarith [hnum, hden]
  have hlogeq : Real.log ((z/12:ℕ):ℝ) - Real.log ((z/36:ℕ):ℝ)
      = Real.log (((z/12:ℕ):ℝ)/((z/36:ℕ):ℝ)) := (Real.log_div (ne_of_gt hA) (ne_of_gt hB)).symm
  have hmb : Real.log (((z/12:ℕ):ℝ)/((z/36:ℕ):ℝ)) ≤ Real.log 3 + 36/965 := by
    have hmono : Real.log (((z/12:ℕ):ℝ)/((z/36:ℕ):ℝ)) ≤ Real.log (3*(z:ℝ)/((z:ℝ)-36)) :=
      Real.log_le_log (by positivity) hratio
    have hsplit : Real.log (3*(z:ℝ)/((z:ℝ)-36)) = Real.log 3 + Real.log ((z:ℝ)/((z:ℝ)-36)) := by
      rw [show 3*(z:ℝ)/((z:ℝ)-36) = 3*((z:ℝ)/((z:ℝ)-36)) by ring,
          Real.log_mul (by norm_num : (3:ℝ)≠0) (by positivity)]
    have htail : Real.log ((z:ℝ)/((z:ℝ)-36)) ≤ 36/965 := by
      have h1 : (z:ℝ)/((z:ℝ)-36) = 1 + 36/((z:ℝ)-36) := by field_simp; ring
      rw [h1]
      have hlog := Real.log_le_sub_one_of_pos (show (0:ℝ) < 1 + 36/((z:ℝ)-36) by positivity)
      have hle36 : 36/((z:ℝ)-36) ≤ 36/965 := by
        rw [div_le_iff₀ hz36, div_mul_eq_mul_div, le_div_iff₀ (by norm_num : (0:ℝ) < 965)]
        nlinarith [hzr]
      linarith
    linarith [hmono, hsplit, htail]
  linarith [hl, hlogeq, hmb]

theorem totient_sum_sub_harmonic_ge_of_large (z : ℕ) (hz : 1001 ≤ z) :
    (9/20 : ℝ) ≤ (∑ r ∈ Finset.Icc 1 z,
      ((ArithmeticFunction.moebius r : ℤ) : ℝ) ^ 2 / (Nat.totient r : ℝ))
      - (harmonic z : ℝ) := by
  change (9/20 : ℝ) ≤ Sall z - (harmonic z : ℝ)
  have hd1 : (z/2)/3 = z/6 := by omega
  have hd2 : (z/3)/3 = z/9 := by omega
  have hd3 : (z/6)/3 = z/18 := by omega
  have hd4 : (z/2)/2 = z/4 := by omega
  have hstep : (1/2)*((harmonic (z/2) : ℝ) - (harmonic (z/4) : ℝ))
      + (1/6)*(A2 (z/3) - A2 (z/9)) + (1/6)*(A2 (z/6) - A2 (z/18))
      ≤ Sall z - (harmonic z : ℝ) := by
    have hS := Sall_eq z
    have hA1 := A6_le_Scop z
    have hA2 := A6_le_Scop (z/2)
    have hA3 := A6_le_Scop (z/3)
    have hA4 := A6_le_Scop (z/6)
    have e1 := A6_eq z
    have e2 := A6_eq (z/2)
    have e3 := A6_eq (z/3)
    have e4 := A6_eq (z/6)
    rw [hd1] at e2
    rw [hd2] at e3
    rw [hd3] at e4
    have f1 := A2_eq z
    have f2 := A2_eq (z/2)
    rw [hd4] at f2
    linarith [hS, hA1, hA2, hA3, hA4, e1, e2, e3, e4, f1, f2]
  have b1 : Real.log 2 - 8/1005 ≤ (harmonic (z/2) : ℝ) - (harmonic (z/4) : ℝ) := by
    have hg := harmonic_sub_ge_log (z/4) (z/2) (by omega)
    have h4 : (((z/4:ℕ):ℝ)+1) ≠ 0 := by positivity
    have h2 : (((z/2:ℕ):ℝ)+1) ≠ 0 := by positivity
    have hld : Real.log (((z/2:ℕ):ℝ)+1) - Real.log (((z/4:ℕ):ℝ)+1)
        = Real.log ((((z/2:ℕ):ℝ)+1)/(((z/4:ℕ):ℝ)+1)) := (Real.log_div h2 h4).symm
    rw [hld] at hg
    have hmono := Real.log_le_log (by norm_num : (0:ℝ) < 2002/1005) (ratio1 z hz)
    linarith [hg, hmono, log2002]
  have b2 : (1/2)*Real.log 3 - 18/1010 - 9/983 ≤ A2 (z/3) - A2 (z/9) := by
    have ha := A2_eq (z/3)
    have hb := A2_eq (z/9)
    rw [show (z/3)/2 = z/6 by omega] at ha
    rw [show (z/9)/2 = z/18 by omega] at hb
    have hg := harmonic_sub_ge_log (z/9) (z/3) (by omega)
    have h3 : (((z/3:ℕ):ℝ)+1) ≠ 0 := by positivity
    have h9 : (((z/9:ℕ):ℝ)+1) ≠ 0 := by positivity
    have hld : Real.log (((z/3:ℕ):ℝ)+1) - Real.log (((z/9:ℕ):ℝ)+1)
        = Real.log ((((z/3:ℕ):ℝ)+1)/(((z/9:ℕ):ℝ)+1)) := (Real.log_div h3 h9).symm
    rw [hld] at hg
    have hmono := Real.log_le_log (by norm_num : (0:ℝ) < 3003/1010) (ratio2 z hz)
    have hu := upper2 z hz
    linarith [ha, hb, hg, hmono, hu, log3003_1010]
  have b3 : (1/2)*Real.log 3 - 36/1019 - 18/965 ≤ A2 (z/6) - A2 (z/18) := by
    have ha := A2_eq (z/6)
    have hb := A2_eq (z/18)
    rw [show (z/6)/2 = z/12 by omega] at ha
    rw [show (z/18)/2 = z/36 by omega] at hb
    have hg := harmonic_sub_ge_log (z/18) (z/6) (by omega)
    have h6 : (((z/6:ℕ):ℝ)+1) ≠ 0 := by positivity
    have h18 : (((z/18:ℕ):ℝ)+1) ≠ 0 := by positivity
    have hld : Real.log (((z/6:ℕ):ℝ)+1) - Real.log (((z/18:ℕ):ℝ)+1)
        = Real.log ((((z/6:ℕ):ℝ)+1)/(((z/18:ℕ):ℝ)+1)) := (Real.log_div h6 h18).symm
    rw [hld] at hg
    have hmono := Real.log_le_log (by norm_num : (0:ℝ) < 3003/1019) (ratio3 z hz)
    have hu := upper3 z hz
    linarith [ha, hb, hg, hmono, hu, log3003_1019]
  have h2 := Real.log_two_gt_d9
  have h3 := log3_ge
  linarith [hstep, b1, b2, b3, h2, h3]

end Commons.NumberTheory.Totient

