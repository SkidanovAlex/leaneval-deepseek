import Mathlib
import Submission.Commons.Analysis.ExponentialSums.large_sieve
import Submission.Commons.NumberTheory.FriedlanderIwaniec.large_sieve_sq_neg_one

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Commons.Analysis.ExponentialSums

open Finset

/-- The summand of the large sieve over the roots of `ν ^ 2 ≡ -1 (mod d)`. -/
private noncomputable def nuSum (N : ℕ) (a : ℕ → ℂ) (d : ℕ) : ℝ :=
  ∑ ν ∈ (Finset.range d).filter (fun ν : ℕ => ((ν : ZMod d))^2 = -1),
    ‖∑ n ∈ Finset.Icc 1 N, a n * ch ((n:ℝ) * ((ν:ℕ):ℝ)/((d:ℝ)))‖^2

private lemma nuSum_nonneg (N : ℕ) (a : ℕ → ℂ) (d : ℕ) : 0 ≤ nuSum N a d :=
  Finset.sum_nonneg (fun _ _ => sq_nonneg _)

private lemma sum_union_le (A B : Finset ℕ) (f : ℕ → ℝ) (hf : ∀ x, 0 ≤ f x) :
    (∑ x ∈ A ∪ B, f x) ≤ (∑ x ∈ A, f x) + (∑ x ∈ B, f x) := by
  classical
  have h : A ∪ B = A ∪ (B \ A) := by
    ext x; simp only [Finset.mem_union, Finset.mem_sdiff]; tauto
  rw [h, Finset.sum_union Finset.disjoint_sdiff]
  have hb : (∑ x ∈ B \ A, f x) ≤ ∑ x ∈ B, f x :=
    Finset.sum_le_sum_of_subset_of_nonneg Finset.sdiff_subset (fun x _ _ => hf x)
  linarith

private lemma sum_biUnion_le {ι : Type*} [DecidableEq ι] (s : Finset ι) (t : ι → Finset ℕ)
    (f : ℕ → ℝ) (hf : ∀ x, 0 ≤ f x) :
    (∑ x ∈ s.biUnion t, f x) ≤ ∑ i ∈ s, ∑ x ∈ t i, f x := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
      rw [Finset.biUnion_insert, Finset.sum_insert ha]
      have h1 := sum_union_le (t a) (s.biUnion t) f hf
      linarith

private lemma sum_range_two_pow_nat (m : ℕ) :
    (∑ j ∈ Finset.range m, ((2^j : ℕ) : ℝ)) = ((2^m : ℕ) : ℝ) - 1 := by
  induction m with
  | zero => simp
  | succ m ih => rw [Finset.sum_range_succ, ih, pow_succ]; push_cast; ring

/-- The final numerical comparison `2 ^ (log₂ D + 1) - 1 ≤ (log₂ D + 1) · D`. -/
private lemma two_pow_log_sub_one_le (D : ℕ) (hD : 1 ≤ D) :
    (((2 ^ (Nat.log 2 D + 1) : ℕ)) : ℝ) - 1
      ≤ ((Nat.log 2 D + 1 : ℕ) : ℝ) * (D : ℝ) := by
  have hDne : D ≠ 0 := by omega
  have hpow : 2 ^ (Nat.log 2 D) ≤ D := Nat.pow_log_le_self 2 hDne
  have h2m : ((2 ^ (Nat.log 2 D + 1) : ℕ) : ℝ) ≤ 2 * (D : ℝ) := by
    have hpowR : ((2 ^ Nat.log 2 D : ℕ) : ℝ) ≤ (D : ℝ) := by exact_mod_cast hpow
    calc ((2 ^ (Nat.log 2 D + 1) : ℕ) : ℝ)
        = 2 * ((2 ^ Nat.log 2 D : ℕ) : ℝ) := by rw [pow_succ]; push_cast; ring
      _ ≤ 2 * (D : ℝ) := mul_le_mul_of_nonneg_left hpowR (by norm_num)
  by_cases hD1 : D = 1
  · subst hD1
    have hlog : Nat.log 2 1 = 0 := by simp
    rw [hlog]; norm_num
  · have hD2 : 2 ≤ D := by omega
    have hlog : 1 ≤ Nat.log 2 D := by
      rw [Nat.le_log_iff_pow_le (by norm_num : 1 < 2) hDne]
      have : (2 : ℕ) ^ 1 = 2 := by norm_num
      rw [this]; omega
    have hm2 : (2 : ℝ) ≤ ((Nat.log 2 D + 1 : ℕ) : ℝ) := by
      have : (2 : ℕ) ≤ Nat.log 2 D + 1 := by omega
      exact_mod_cast this
    have h2D : 2 * (D : ℝ) ≤ ((Nat.log 2 D + 1 : ℕ) : ℝ) * (D : ℝ) :=
      mul_le_mul_of_nonneg_right hm2 (by positivity)
    linarith

theorem large_sieve_sq_neg_one_Icc (D N : ℕ) (a : ℕ → ℂ) :
    (∑ d ∈ Finset.Icc 1 D, ∑ ν ∈ (Finset.range d).filter (fun ν : ℕ => ((ν : ZMod d))^2 = -1),
        ‖∑ n ∈ Finset.Icc 1 N, a n * Commons.Analysis.ExponentialSums.ch ((n:ℝ) * ((ν:ℕ):ℝ)/((d:ℝ)))‖^2)
      ≤ 8 * ((Nat.log 2 D : ℝ) + 1) * ((N:ℝ) + (D:ℝ)) * (∑ n ∈ Finset.Icc 1 N, ‖a n‖^2) := by
  classical
  rcases Nat.eq_zero_or_pos D with hD0 | hDpos
  · subst hD0
    rw [show (Finset.Icc 1 0 : Finset ℕ) = ∅ by
          rw [Finset.Icc_eq_empty_iff]; omega, Finset.sum_empty]
    have hlog : Nat.log 2 0 = 0 := by simp
    rw [hlog]
    positivity
  · set S0 : ℝ := ∑ n ∈ Finset.Icc 1 N, ‖a n‖^2 with hS0def
    have hS0 : 0 ≤ S0 := by rw [hS0def]; exact Finset.sum_nonneg (fun n _ => sq_nonneg _)
    change (∑ d ∈ Finset.Icc 1 D, nuSum N a d)
        ≤ 8 * ((Nat.log 2 D : ℝ) + 1) * ((N:ℝ) + (D:ℝ)) * S0
    -- single term bound
    have hterm : ∀ (d ν : ℕ),
        ‖∑ n ∈ Finset.Icc 1 N, a n * ch ((n:ℝ) * ((ν:ℕ):ℝ)/((d:ℝ)))‖^2
          ≤ (N:ℝ) * S0 := by
      intro d ν
      have h1 : ‖∑ n ∈ Finset.Icc 1 N, a n * ch ((n:ℝ) * ((ν:ℕ):ℝ)/((d:ℝ)))‖
          ≤ ∑ n ∈ Finset.Icc 1 N, ‖a n‖ := by
        refine le_trans (norm_sum_le _ _) ?_
        exact Finset.sum_le_sum (fun n _ => by rw [norm_mul, norm_ch_eq_one, mul_one])
      have h2 : (∑ n ∈ Finset.Icc 1 N, ‖a n‖)^2 ≤ (N:ℝ) * S0 := by
        rw [hS0def]
        have hcs := Finset.sum_mul_sq_le_sq_mul_sq (Finset.Icc 1 N)
          (fun n => ‖a n‖) (fun _ => (1:ℝ))
        have hcard : (∑ _n ∈ Finset.Icc 1 N, ((1:ℝ))^2) = (N:ℝ) := by
          rw [Finset.sum_const, Nat.card_Icc]; simp
        rw [hcard] at hcs
        rw [mul_comm ((∑ n ∈ Finset.Icc 1 N, ‖a n‖^2)) (N:ℝ)] at hcs
        simpa only [mul_one] using hcs
      exact pow_le_pow_left₀ (norm_nonneg _) h1 2 |>.trans h2
    -- pointwise bound of `nuSum`
    have hgd : ∀ d, nuSum N a d ≤ (d:ℝ) * ((N:ℝ) * S0) := by
      intro d
      simp only [nuSum]
      calc (∑ ν ∈ (Finset.range d).filter (fun ν : ℕ => ((ν : ZMod d))^2 = -1),
              ‖∑ n ∈ Finset.Icc 1 N, a n * ch ((n:ℝ) * ((ν:ℕ):ℝ)/((d:ℝ)))‖^2)
          ≤ ∑ ν ∈ Finset.range d,
              ‖∑ n ∈ Finset.Icc 1 N, a n * ch ((n:ℝ) * ((ν:ℕ):ℝ)/((d:ℝ)))‖^2 :=
            Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
              (fun ν _ _ => sq_nonneg _)
        _ ≤ ∑ ν ∈ Finset.range d, (N:ℝ) * S0 := Finset.sum_le_sum (fun ν _ => hterm d ν)
        _ = (d:ℝ) * ((N:ℝ) * S0) := by
            rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    -- main block decomposition
    set m : ℕ := Nat.log 2 D + 1 with hm
    have hm_pos : 0 < m := by rw [hm]; omega
    have hDpow : D < 2^m := by
      rw [hm]; exact Nat.lt_pow_succ_log_self (by norm_num) D
    have hmR : (m:ℝ) = (Nat.log 2 D : ℝ) + 1 := by rw [hm]; push_cast; ring
    let blk : ℕ → Finset ℕ := fun j =>
      if j = 0 then Finset.Icc 1 2 else Finset.Icc (2^j+1) (2^(j+1))
    have hblk0 : blk 0 = Finset.Icc 1 2 := by simp [blk]
    have hblkj : ∀ j, j ≠ 0 → blk j = Finset.Icc (2^j+1) (2^(j+1)) := by
      intro j hj; simp [blk, if_neg hj]
    have hcover : ∀ d ∈ Finset.Icc 1 D, ∃ j ∈ Finset.range m, d ∈ blk j := by
      intro d hd
      obtain ⟨hd1, hdD⟩ := Finset.mem_Icc.mp hd
      by_cases hle2 : d ≤ 2
      · refine ⟨0, Finset.mem_range.mpr hm_pos, ?_⟩
        rw [hblk0, Finset.mem_Icc]
        exact ⟨hd1, hle2⟩
      · push Not at hle2
        have hd3 : 3 ≤ d := by omega
        refine ⟨Nat.log 2 (d-1), ?_, ?_⟩
        · rw [Finset.mem_range]
          exact Nat.log_lt_of_lt_pow (by omega : d - 1 ≠ 0) (by omega)
        · have hj0 : Nat.log 2 (d-1) ≠ 0 := by
            have h1 : 1 ≤ Nat.log 2 (d-1) := by
              rw [Nat.le_log_iff_pow_le (by norm_num : 1 < 2) (by omega : d - 1 ≠ 0)]
              have : (2:ℕ)^1 = 2 := by norm_num
              rw [this]; omega
            omega
          rw [hblkj _ hj0, Finset.mem_Icc]
          refine ⟨?_, ?_⟩
          · have := Nat.pow_log_le_self 2 (by omega : d - 1 ≠ 0); omega
          · have := Nat.lt_pow_succ_log_self (b:=2) (by norm_num) (d-1); omega
    have hsum_le : (∑ d ∈ Finset.Icc 1 D, nuSum N a d)
        ≤ ∑ j ∈ Finset.range m, ∑ d ∈ blk j, nuSum N a d := by
      have hsub : Finset.Icc 1 D ⊆ (Finset.range m).biUnion blk := by
        intro d hd
        obtain ⟨j, hj, hdj⟩ := hcover d hd
        exact Finset.mem_biUnion.mpr ⟨j, hj, hdj⟩
      calc (∑ d ∈ Finset.Icc 1 D, nuSum N a d)
          ≤ ∑ d ∈ (Finset.range m).biUnion blk, nuSum N a d :=
            Finset.sum_le_sum_of_subset_of_nonneg hsub (fun i _ _ => nuSum_nonneg N a i)
        _ ≤ ∑ j ∈ Finset.range m, ∑ d ∈ blk j, nuSum N a d :=
            sum_biUnion_le _ _ _ (nuSum_nonneg N a)
    have hsplit : (∑ j ∈ Finset.range m, ∑ d ∈ blk j, nuSum N a d)
        = (∑ d ∈ blk 0, nuSum N a d)
          + ∑ j ∈ (Finset.range m).erase 0, ∑ d ∈ blk j, nuSum N a d := by
      have h := Finset.sum_erase_add (Finset.range m)
        (fun j => ∑ d ∈ blk j, nuSum N a d) (Finset.mem_range.mpr hm_pos)
      rw [← h]; ring
    -- block 0
    have hb0 : (∑ d ∈ blk 0, nuSum N a d) ≤ 8 * ((N:ℝ) + 1) * S0 := by
      rw [hblk0]
      have hpt : ∀ d ∈ Finset.Icc 1 2, nuSum N a d ≤ 2 * ((N:ℝ) * S0) := by
        intro d hd
        refine le_trans (hgd d) ?_
        have hdle : (d:ℝ) ≤ 2 := by
          have : d ≤ 2 := (Finset.mem_Icc.mp hd).2
          exact_mod_cast this
        have hNN : 0 ≤ (N:ℝ) * S0 := mul_nonneg (Nat.cast_nonneg N) hS0
        exact mul_le_mul_of_nonneg_right hdle hNN
      calc (∑ d ∈ Finset.Icc 1 2, nuSum N a d)
          ≤ (Finset.Icc 1 2).card • (2 * ((N:ℝ) * S0)) :=
            Finset.sum_le_card_nsmul _ _ _ hpt
        _ = 4 * ((N:ℝ) * S0) := by
            rw [Nat.card_Icc, nsmul_eq_mul]; norm_num; ring
        _ ≤ 8 * ((N:ℝ) + 1) * S0 := by
            have hNN : 0 ≤ (N:ℝ) * S0 := mul_nonneg (Nat.cast_nonneg N) hS0
            nlinarith [hNN, hS0]
    -- nonzero blocks
    have hbj : ∀ j ∈ (Finset.range m).erase 0,
        (∑ d ∈ blk j, nuSum N a d) ≤ 8 * ((N:ℝ) + ((2^j:ℕ):ℝ)) * S0 := by
      intro j hj
      rw [Finset.mem_erase] at hj
      obtain ⟨hj0, hjm⟩ := hj
      rw [hblkj j hj0]
      have h := Commons.NumberTheory.FriedlanderIwaniec.large_sieve_sq_neg_one (2^j) N a
      rw [show (2 * 2^j : ℕ) = 2^(j+1) by rw [pow_succ]; ring] at h
      simpa only [nuSum, hS0def] using h
    -- assemble
    have hsum2 : (∑ j ∈ Finset.range m, ∑ d ∈ blk j, nuSum N a d)
        ≤ 8 * ((N:ℝ) + 1) * S0
          + ∑ j ∈ (Finset.range m).erase 0, 8 * ((N:ℝ) + ((2^j:ℕ):ℝ)) * S0 := by
      rw [hsplit]
      refine add_le_add hb0 ?_
      exact Finset.sum_le_sum hbj
    -- evaluate the geometric sum
    have hgeom : (∑ j ∈ (Finset.range m).erase 0, ((N:ℝ) + ((2^j:ℕ):ℝ)))
        = ((m:ℝ) - 1) * (N:ℝ) + (((2^m:ℕ):ℝ) - 2) := by
      have h1 : (∑ j ∈ (Finset.range m).erase 0, ((2^j:ℕ):ℝ)) = ((2^m:ℕ):ℝ) - 2 := by
        have hex := Finset.sum_erase_add (Finset.range m) (fun j => ((2^j:ℕ):ℝ))
          (Finset.mem_range.mpr hm_pos)
        rw [sum_range_two_pow_nat] at hex
        simp only [pow_zero, Nat.cast_one] at hex
        linarith
      have hcard : (((Finset.range m).erase 0).card : ℝ) = (m:ℝ) - 1 := by
        rw [Finset.card_erase_of_mem (Finset.mem_range.mpr hm_pos), Finset.card_range,
            Nat.cast_sub (by omega : 1 ≤ m)]
        norm_num
      rw [Finset.sum_add_distrib, Finset.sum_const, h1, nsmul_eq_mul, hcard]
    have hbnd : (∑ j ∈ (Finset.range m).erase 0, 8 * ((N:ℝ) + ((2^j:ℕ):ℝ)) * S0)
        = 8 * S0 * (((m:ℝ) - 1) * (N:ℝ) + (((2^m:ℕ):ℝ) - 2)) := by
      rw [← hgeom, Finset.mul_sum]
      refine Finset.sum_congr rfl (fun j _ => by ring)
    have hfin : ((2^m : ℕ) : ℝ) - 1 ≤ (m:ℝ) * (D:ℝ) := by
      rw [hm]; exact two_pow_log_sub_one_le D hDpos
    calc (∑ d ∈ Finset.Icc 1 D, nuSum N a d)
        ≤ ∑ j ∈ Finset.range m, ∑ d ∈ blk j, nuSum N a d := hsum_le
      _ ≤ 8 * ((N:ℝ) + 1) * S0
          + ∑ j ∈ (Finset.range m).erase 0, 8 * ((N:ℝ) + ((2^j:ℕ):ℝ)) * S0 := hsum2
      _ = 8 * S0 * ((m:ℝ) * (N:ℝ) + (((2^m:ℕ):ℝ) - 1)) := by
            rw [hbnd]; ring
      _ ≤ 8 * S0 * ((m:ℝ) * ((N:ℝ) + (D:ℝ))) := by
            apply mul_le_mul_of_nonneg_left _ (by positivity)
            rw [mul_add]
            nlinarith [hfin]
      _ = 8 * ((Nat.log 2 D : ℝ) + 1) * ((N:ℝ) + (D:ℝ)) * S0 := by
            rw [← hmR]; ring

end Commons.Analysis.ExponentialSums
