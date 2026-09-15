import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Data.Int.Star

open Classical
open Finset

namespace Commons.Combinatorics.Transference

/-- If `0 ≤ r < N`, then the number of `k ∈ range N` with `N ≤ r + k` equals `⌊r⌋`. -/
private lemma gridKey_iff (N : ℕ) (r : ℝ) (hr0 : 0 ≤ r) (hfN : Nat.floor r ≤ N) (k : ℕ) :
    ((N:ℝ) ≤ r + (k:ℝ)) ↔ (N - Nat.floor r ≤ k) := by
  have hfl : (Nat.floor r : ℝ) ≤ r := Nat.floor_le hr0
  constructor
  · intro h
    have hm1 : ((N - Nat.floor r : ℕ) : ℝ) - 1 < (k:ℝ) := by
      rw [Nat.cast_sub hfN]
      have hh : (N:ℝ) - r ≤ (k:ℝ) := by linarith
      have hfu : r < (Nat.floor r : ℝ) + 1 := Nat.lt_floor_add_one r
      linarith
    by_contra hc
    push Not at hc
    have h2 : k + 1 ≤ N - Nat.floor r := hc
    have h3 : ((k:ℝ) + 1) ≤ ((N - Nat.floor r : ℕ):ℝ) := by exact_mod_cast h2
    linarith
  · intro h
    have hkk : ((N - Nat.floor r : ℕ):ℝ) ≤ (k:ℝ) := by exact_mod_cast h
    have hsub : ((N - Nat.floor r : ℕ):ℝ) = (N:ℝ) - (Nat.floor r : ℝ) := Nat.cast_sub hfN
    rw [hsub] at hkk
    linarith

/-- Hermite's identity in the form `∑_{k<N} ⌊(r+k)/N⌋ = ⌊r⌋` for `0 ≤ r < N`. -/
private lemma floor_div_grid_aux (N : ℕ) (hN : 1 ≤ N) (r : ℝ) (hr0 : 0 ≤ r) (hrN : r < N) :
    (∑ k ∈ Finset.range N, ⌊(r + (k : ℝ)) / (N : ℝ)⌋) = ⌊r⌋ := by
  have hNpos : (0:ℝ) < N := by exact_mod_cast hN
  have hfl : (Nat.floor r : ℝ) ≤ r := Nat.floor_le hr0
  have hfu : r < (Nat.floor r : ℝ) + 1 := Nat.lt_floor_add_one r
  have hfN : Nat.floor r ≤ N := by
    have h2 : (Nat.floor r : ℝ) < N := by linarith
    exact (by exact_mod_cast h2 : Nat.floor r < N).le
  have hterm : ∀ k : ℕ, k < N →
      ⌊(r + (k:ℝ)) / (N:ℝ)⌋ = if (N:ℝ) ≤ r + (k:ℝ) then (1:ℤ) else 0 := by
    intro k hk
    have hk' : (k:ℝ) < N := by exact_mod_cast hk
    have h2 : r + (k:ℝ) < 2 * N := by linarith
    have h0 : 0 ≤ r + (k:ℝ) := by positivity
    split_ifs with h
    · rw [Int.floor_eq_iff]
      refine ⟨?_, ?_⟩
      · simp only [Int.cast_one]
        rw [one_le_div hNpos]; exact h
      · simp only [Int.cast_one]
        rw [div_lt_iff₀ hNpos]; linarith
    · push Not at h
      rw [Int.floor_eq_iff]
      refine ⟨?_, ?_⟩
      · simp only [Int.cast_zero]
        rw [le_div_iff₀ hNpos]; linarith
      · simp only [Int.cast_zero, zero_add]
        rw [div_lt_iff₀ hNpos]; linarith
  have hsum : (∑ k ∈ Finset.range N, ⌊(r + (k:ℝ)) / (N:ℝ)⌋)
      = ∑ k ∈ Finset.range N, (if (N:ℝ) ≤ r + (k:ℝ) then (1:ℤ) else 0) := by
    apply Finset.sum_congr rfl
    intro k hk
    exact hterm k (Finset.mem_range.mp hk)
  rw [hsum, Finset.sum_boole]
  have hset : (Finset.range N).filter (fun k : ℕ => (N:ℝ) ≤ r + (k:ℝ))
      = Finset.Ico (N - Nat.floor r) N := by
    apply Finset.ext
    intro k
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
    rw [gridKey_iff N r hr0 hfN k]
    exact ⟨fun h => ⟨h.2, h.1⟩, fun h => ⟨h.2, h.1⟩⟩
  rw [hset, Nat.card_Ico, Nat.sub_sub_self hfN]
  exact ((Int.floor_eq_iff (a := r) (z := (Nat.floor r : ℤ))).mpr ⟨hfl, hfu⟩).symm

/-- Hermite's identity: `∑_{k<N} ⌊x + k/N⌋ = ⌊N x⌋`. -/
private lemma sum_floor_div_add_grid (N : ℕ) (hN : 1 ≤ N) (y : ℝ) :
    (∑ k ∈ Finset.range N, ⌊(y + (k : ℝ)) / (N : ℝ)⌋) = ⌊y⌋ := by
  have hNpos : (0:ℝ) < N := by exact_mod_cast hN
  have hNne : (N:ℝ) ≠ 0 := ne_of_gt hNpos
  set Q : ℤ := ⌊y / N⌋ with hQ
  set f : ℝ := Int.fract (y / N) with hf
  have hQf : (Q:ℝ) + f = y / N := by
    rw [hQ, hf]; exact Int.floor_add_fract _
  have hf0 : 0 ≤ f := by rw [hf]; exact Int.fract_nonneg _
  have hf1 : f < 1 := by rw [hf]; exact Int.fract_lt_one _
  have hr0 : 0 ≤ (N:ℝ) * f := mul_nonneg hNpos.le hf0
  have hrN : (N:ℝ) * f < N := by
    have : (N:ℝ) * f < (N:ℝ) * 1 := mul_lt_mul_of_pos_left hf1 hNpos
    simpa using this
  have haux := floor_div_grid_aux N hN ((N:ℝ) * f) hr0 hrN
  have hcongr : (∑ k ∈ Finset.range N, ⌊((N:ℝ) * f + (k:ℝ)) / (N:ℝ)⌋)
      = ∑ k ∈ Finset.range N, ⌊f + (k:ℝ) / (N:ℝ)⌋ := by
    apply Finset.sum_congr rfl; intro k hk
    congr 1
    field_simp
  rw [hcongr] at haux
  have hmain : (∑ k ∈ Finset.range N, ⌊(y + (k:ℝ)) / (N:ℝ)⌋)
      = ∑ k ∈ Finset.range N, ((Q:ℤ) + ⌊f + (k:ℝ) / (N:ℝ)⌋) := by
    apply Finset.sum_congr rfl; intro k hk
    have h1 : (y + (k:ℝ)) / (N:ℝ) = (Q:ℝ) + (f + (k:ℝ) / (N:ℝ)) := by
      rw [add_div, ← hQf]; ring
    rw [h1, Int.floor_intCast_add]
  rw [hmain, Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, haux, nsmul_eq_mul]
  have hy : (N:ℝ) * ((Q:ℝ) + f) = ((N:ℤ) * Q : ℤ) + (N:ℝ) * f := by
    push_cast; ring
  have hy2 : y = (N:ℝ) * ((Q:ℝ) + f) := by
    rw [hQf, mul_div_cancel₀ y hNne]
  rw [hy2, hy, Int.floor_intCast_add]

/-- The `-` variant: `∑_{k<N} ⌊x - k/N⌋ = ⌊N x⌋ - (N-1)`. -/
private lemma sum_floor_div_sub_grid (N : ℕ) (hN : 1 ≤ N) (x : ℝ) :
    (∑ k ∈ Finset.range N, ⌊x - (k:ℝ)/(N:ℝ)⌋) = ⌊(N:ℝ) * x⌋ - ((N:ℤ) - 1) := by
  have hNpos : (0:ℝ) < N := by exact_mod_cast hN
  have hNne : (N:ℝ) ≠ 0 := ne_of_gt hNpos
  rw [← Finset.sum_range_reflect (fun k => ⌊x - (k:ℝ)/(N:ℝ)⌋) N]
  have hcongr : (∑ k ∈ Finset.range N, ⌊x - ((N-1-k:ℕ):ℝ)/(N:ℝ)⌋)
      = ∑ k ∈ Finset.range N, ⌊(x - ((N-1:ℕ):ℝ)/(N:ℝ)) + (k:ℝ)/(N:ℝ)⌋ := by
    apply Finset.sum_congr rfl; intro k hk
    have hk' : k ≤ N - 1 := by have := Finset.mem_range.mp hk; omega
    congr 1
    rw [Nat.cast_sub hk']
    ring
  rw [hcongr]
  have hcongr2 : (∑ k ∈ Finset.range N, ⌊x - ((N-1:ℕ):ℝ)/(N:ℝ) + (k:ℝ)/(N:ℝ)⌋)
      = ∑ k ∈ Finset.range N, ⌊((N:ℝ) * (x - ((N-1:ℕ):ℝ)/(N:ℝ)) + (k:ℝ))/(N:ℝ)⌋ := by
    apply Finset.sum_congr rfl; intro k hk
    congr 1
    field_simp
  rw [hcongr2, sum_floor_div_add_grid N hN]
  have hsub : (N:ℝ) * (x - ((N-1:ℕ):ℝ)/(N:ℝ)) = (N:ℝ) * x - (((N:ℤ) - 1 : ℤ) : ℝ) := by
    have h1 : ((N-1:ℕ):ℝ) = (((N:ℤ) - 1 : ℤ) : ℝ) := by
      rw [Nat.cast_sub hN, Nat.cast_one]; push_cast; ring
    rw [mul_sub, mul_div_cancel₀ ((N-1:ℕ):ℝ) hNne, h1]
  rw [hsub, Int.floor_sub_intCast]

/-- Counting lemma: among the `N` grid points `k/N` (`k < N`), at most `2 η N + 2` of them lie
within distance `η` of an integer. -/
private lemma card_filter_dist_grid_le (N : ℕ) (hN : 1 ≤ N) (β η : ℝ) (hη : 0 ≤ η) :
    (((Finset.range N).filter (fun k : ℕ => ∃ n : ℤ, |β - (k:ℝ)/(N:ℝ) - (n:ℝ)| ≤ η)).card : ℝ)
      ≤ 2 * η * (N:ℝ) + 2 := by
  have hNpos : (0:ℝ) < N := by exact_mod_cast hN
  have hNne : (N:ℝ) ≠ 0 := ne_of_gt hNpos
  set ε : ℝ := 1/(2*N) with hεdef
  have hε : 0 < ε := by rw [hεdef]; positivity
  have hNε : (N:ℝ) * ε = 1/2 := by rw [hεdef]; field_simp
  have hpt : ∀ k : ℕ, (if (∃ n : ℤ, |β - (k:ℝ)/(N:ℝ) - (n:ℝ)| ≤ η) then (1:ℤ) else 0)
      ≤ ⌊(β + η + ε) - (k:ℝ)/(N:ℝ)⌋ - ⌊(β - η - ε) - (k:ℝ)/(N:ℝ)⌋ := by
    intro k
    by_cases h : ∃ n : ℤ, |β - (k:ℝ)/(N:ℝ) - (n:ℝ)| ≤ η
    · rw [if_pos h]
      obtain ⟨n, hn⟩ := h
      have hn' := abs_le.mp hn
      have h1 : n ≤ ⌊(β + η + ε) - (k:ℝ)/(N:ℝ)⌋ := by
        rw [Int.le_floor]; linarith [hn'.1]
      have h2 : ⌊(β - η - ε) - (k:ℝ)/(N:ℝ)⌋ ≤ n - 1 := by
        have hlt : ⌊(β - η - ε) - (k:ℝ)/(N:ℝ)⌋ < n := by
          rw [Int.floor_lt]; linarith [hn'.2]
        omega
      linarith
    · rw [if_neg h]
      have : ⌊(β - η - ε) - (k:ℝ)/(N:ℝ)⌋ ≤ ⌊(β + η + ε) - (k:ℝ)/(N:ℝ)⌋ := by
        apply Int.floor_mono; linarith
      linarith
  have hcardZ : (((Finset.range N).filter (fun k : ℕ => ∃ n : ℤ, |β - (k:ℝ)/(N:ℝ) - (n:ℝ)| ≤ η)).card : ℤ)
      = ∑ k ∈ Finset.range N, (if (∃ n : ℤ, |β - (k:ℝ)/(N:ℝ) - (n:ℝ)| ≤ η) then (1:ℤ) else 0) :=
    (Finset.sum_boole (fun k : ℕ => ∃ n : ℤ, |β - (k:ℝ)/(N:ℝ) - (n:ℝ)| ≤ η) (Finset.range N)).symm
  have hle : (∑ k ∈ Finset.range N, (if (∃ n : ℤ, |β - (k:ℝ)/(N:ℝ) - (n:ℝ)| ≤ η) then (1:ℤ) else 0))
      ≤ ⌊(N:ℝ) * (β + η + ε)⌋ - ⌊(N:ℝ) * (β - η - ε)⌋ := by
    calc (∑ k ∈ Finset.range N, (if (∃ n : ℤ, |β - (k:ℝ)/(N:ℝ) - (n:ℝ)| ≤ η) then (1:ℤ) else 0))
        ≤ ∑ k ∈ Finset.range N, (⌊(β + η + ε) - (k:ℝ)/(N:ℝ)⌋ - ⌊(β - η - ε) - (k:ℝ)/(N:ℝ)⌋) :=
          Finset.sum_le_sum (fun k _ => hpt k)
      _ = (∑ k ∈ Finset.range N, ⌊(β + η + ε) - (k:ℝ)/(N:ℝ)⌋)
            - ∑ k ∈ Finset.range N, ⌊(β - η - ε) - (k:ℝ)/(N:ℝ)⌋ := by rw [Finset.sum_sub_distrib]
      _ = (⌊(N:ℝ) * (β + η + ε)⌋ - ((N:ℤ) - 1)) - (⌊(N:ℝ) * (β - η - ε)⌋ - ((N:ℤ) - 1)) := by
          rw [sum_floor_div_sub_grid N hN, sum_floor_div_sub_grid N hN]
      _ = ⌊(N:ℝ) * (β + η + ε)⌋ - ⌊(N:ℝ) * (β - η - ε)⌋ := by ring
  have h1 : (((Finset.range N).filter (fun k : ℕ => ∃ n : ℤ, |β - (k:ℝ)/(N:ℝ) - (n:ℝ)| ≤ η)).card : ℤ)
      ≤ ⌊(N:ℝ) * (β + η + ε)⌋ - ⌊(N:ℝ) * (β - η - ε)⌋ := by rw [hcardZ]; exact hle
  have h2 : ((⌊(N:ℝ) * (β + η + ε)⌋ - ⌊(N:ℝ) * (β - η - ε)⌋ : ℤ) : ℝ) ≤ 2 * η * (N:ℝ) + 2 := by
    have hf1 : (⌊(N:ℝ) * (β + η + ε)⌋ : ℝ) ≤ (N:ℝ) * (β + η + ε) := Int.floor_le _
    have hf2 : (N:ℝ) * (β - η - ε) - 1 < (⌊(N:ℝ) * (β - η - ε)⌋ : ℝ) := by
      have := Int.lt_floor_add_one ((N:ℝ) * (β - η - ε)); linarith
    push_cast
    linarith [hNε]
  calc (((Finset.range N).filter (fun k : ℕ => ∃ n : ℤ, |β - (k:ℝ)/(N:ℝ) - (n:ℝ)| ≤ η)).card : ℝ)
      = ((((Finset.range N).filter (fun k : ℕ => ∃ n : ℤ, |β - (k:ℝ)/(N:ℝ) - (n:ℝ)| ≤ η)).card : ℤ) : ℝ) := by simp
    _ ≤ ((⌊(N:ℝ) * (β + η + ε)⌋ - ⌊(N:ℝ) * (β - η - ε)⌋ : ℤ) : ℝ) := by exact_mod_cast h1
    _ ≤ 2 * η * (N:ℝ) + 2 := h2

theorem exists_shift_boundary_cover {X : Type*} [Fintype X] (G ν : X → ℝ) {ε η : ℝ}
    (hε : 0 < ε) (hη : 0 < η) (hη1 : η ≤ 1) (hν : ∀ x, 0 ≤ ν x + 1) :
    ∃ α : ℝ, 0 ≤ α ∧ α < ε ∧ ∃ T : Finset X,
      (∀ x, (∃ n : ℤ, |(G x - α) / ε - n| ≤ η) → x ∈ T) ∧
      ∑ x ∈ T, (ν x + 1) ≤ 3 * η * ∑ x, (ν x + 1) := by
  classical
  obtain ⟨N, hNgt⟩ := exists_nat_gt (2 / η)
  have hNposR : (0:ℝ) < N := by
    have : (0:ℝ) < 2 / η := by positivity
    linarith
  have hNnat : 0 < N := by exact_mod_cast hNposR
  have hN1 : 1 ≤ N := hNnat
  have hηN : 2 ≤ η * (N:ℝ) := by
    have h1 : η * (2/η) < η * (N:ℝ) := mul_lt_mul_of_pos_left hNgt hη
    have h2 : η * (2/η) = 2 := by field_simp
    linarith
  set W : ℝ := ∑ x : X, (ν x + 1) with hWdef
  have hWnn : 0 ≤ W := by rw [hWdef]; exact Finset.sum_nonneg (fun x _ => hν x)
  let F : ℕ → ℝ := fun k => ∑ x : X,
    (if (∃ n : ℤ, |(G x - (k:ℝ)*ε/(N:ℝ))/ε - (n:ℝ)| ≤ η) then (ν x + 1) else 0)
  let c : X → ℕ := fun x =>
    ((Finset.range N).filter (fun k : ℕ => ∃ n : ℤ, |(G x - (k:ℝ)*ε/(N:ℝ))/ε - (n:ℝ)| ≤ η)).card
  have key_id : ∀ (k : ℕ) (x : X),
      (G x - (k:ℝ) * ε / (N:ℝ)) / ε = G x / ε - (k:ℝ) / (N:ℝ) := by
    intro k x
    have hNne : (N:ℝ) ≠ 0 := ne_of_gt hNposR
    field_simp
  have hc_bound : ∀ x : X, (c x : ℝ) ≤ 2 * η * (N:ℝ) + 2 := by
    intro x
    have hbadeq : ∀ k : ℕ, ((∃ n : ℤ, |(G x - (k:ℝ)*ε/(N:ℝ))/ε - (n:ℝ)| ≤ η)
        ↔ (∃ n : ℤ, |G x / ε - (k:ℝ)/(N:ℝ) - (n:ℝ)| ≤ η)) := by
      intro k
      constructor
      · rintro ⟨n, hn⟩; exact ⟨n, by rwa [key_id k x] at hn⟩
      · rintro ⟨n, hn⟩; exact ⟨n, by rwa [key_id k x]⟩
    have hcongr : (Finset.range N).filter (fun k : ℕ => ∃ n : ℤ, |(G x - (k:ℝ)*ε/(N:ℝ))/ε - (n:ℝ)| ≤ η)
        = (Finset.range N).filter (fun k : ℕ => ∃ n : ℤ, |G x / ε - (k:ℝ)/(N:ℝ) - (n:ℝ)| ≤ η) :=
      Finset.filter_congr (fun k _ => hbadeq k)
    dsimp only [c]
    rw [hcongr]
    exact card_filter_dist_grid_le N hN1 (G x / ε) η (le_of_lt hη)
  have hF_eq : ∀ k : ℕ, F k = ∑ x : X,
      (ν x + 1) * (if (∃ n : ℤ, |(G x - (k:ℝ)*ε/(N:ℝ))/ε - (n:ℝ)| ≤ η) then (1:ℝ) else 0) := by
    intro k
    dsimp only [F]
    apply Finset.sum_congr rfl; intro x _
    by_cases h : (∃ n : ℤ, |(G x - (k:ℝ)*ε/(N:ℝ))/ε - (n:ℝ)| ≤ η)
    · simp [h]
    · simp [h]
  have hswap : ∑ k ∈ Finset.range N, F k = ∑ x : X, (ν x + 1) * (c x : ℝ) := by
    rw [show (∑ k ∈ Finset.range N, F k) = ∑ k ∈ Finset.range N, ∑ x : X,
          (ν x + 1) * (if (∃ n : ℤ, |(G x - (k:ℝ)*ε/(N:ℝ))/ε - (n:ℝ)| ≤ η) then (1:ℝ) else 0)
        from Finset.sum_congr rfl (fun k _ => hF_eq k)]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro x _
    rw [← Finset.mul_sum]
    congr 1
    dsimp only [c]
    exact Finset.sum_boole (fun k : ℕ => ∃ n : ℤ, |(G x - (k:ℝ)*ε/(N:ℝ))/ε - (n:ℝ)| ≤ η) (Finset.range N)
  have hsum_bound : ∑ k ∈ Finset.range N, F k ≤ (2 * η * (N:ℝ) + 2) * W := by
    rw [hswap]
    calc ∑ x : X, (ν x + 1) * (c x : ℝ) ≤ ∑ x : X, (ν x + 1) * (2 * η * (N:ℝ) + 2) := by
          apply Finset.sum_le_sum; intro x _
          exact mul_le_mul_of_nonneg_left (hc_bound x) (hν x)
      _ = (2 * η * (N:ℝ) + 2) * W := by
          rw [← Finset.sum_mul, hWdef]; ring
  have h3 : ∃ k ∈ Finset.range N, F k ≤ 3 * η * W := by
    by_contra hcon
    push Not at hcon
    have hne : (Finset.range N).Nonempty := ⟨0, Finset.mem_range.mpr hNnat⟩
    have h4 : ∑ k ∈ Finset.range N, (3 * η * W) < ∑ k ∈ Finset.range N, F k :=
      Finset.sum_lt_sum_of_nonempty hne (fun k hk => hcon k hk)
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at h4
    have hub : ∑ k ∈ Finset.range N, F k ≤ (N:ℝ) * (3 * η * W) := by
      calc ∑ k ∈ Finset.range N, F k ≤ (2 * η * (N:ℝ) + 2) * W := hsum_bound
        _ ≤ (N:ℝ) * (3 * η * W) := by nlinarith [hηN, hWnn]
    linarith
  obtain ⟨k, hkN, hkF⟩ := h3
  have hkNlt : k < N := Finset.mem_range.mp hkN
  refine ⟨(k:ℝ) * ε / (N:ℝ), ?_, ?_, ?_⟩
  · positivity
  · have hkR : (k:ℝ) < N := by exact_mod_cast hkNlt
    have hNpos : (0:ℝ) < N := hNposR
    rw [div_lt_iff₀ hNpos]
    nlinarith [hε, hkR]
  · refine ⟨Finset.univ.filter (fun x => ∃ n : ℤ, |(G x - (k:ℝ)*ε/(N:ℝ))/ε - (n:ℝ)| ≤ η), ?_, ?_⟩
    · intro x hx
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ x, hx⟩
    · rw [Finset.sum_filter]
      have hFk : (∑ x : X, (if (∃ n : ℤ, |(G x - (k:ℝ)*ε/(N:ℝ))/ε - (n:ℝ)| ≤ η) then (ν x + 1) else 0)) = F k := by
        dsimp only [F]
      rw [hFk]
      rw [hWdef] at hkF
      exact hkF

end Commons.Combinatorics.Transference