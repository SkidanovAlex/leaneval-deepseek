import Mathlib
import Submission.Work.BMF.TentDefs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Counting `n` with `nint (g n) ≤ θ` when `g` grows at a uniform rate

This file proves `Work.BMF.space_count`: if `g : ℝ → ℝ` has increments
`g (n+1) - g (n) ∈ [μ, A₀ μ]` for `1 ≤ n < N`, then the number of `n ∈ {1,…,N}`
for which `g n` is within `θ ∈ [0,1]` of an integer is at most
`100 (1 + A₀ μ N)(1 + θ/μ)`.

The heart of the argument is the combinatorial estimate
`card_le_mul_of_fiber_range`: a finite set `s ⊆ ℕ` mapped by `φ : ℕ → ℤ` is
controlled by the sizes of the fibres of `φ` (bounded via the fact that
`nint (g n) ≤ θ` forces `|n - m| ≤ 2θ/μ` whenever `round (g n) = round (g m)`)
and by the range of `φ` (bounded via the growth of `g`).
-/

namespace Work.BMF

open Finset

/-- Combinatorial counting lemma: if the fibres of `φ` on `s` are contained in
intervals of length `c` and the whole image of `φ` on `s` lies in an interval of
`L + 1` consecutive integers, then `s` has at most `(c+1)(L+1)` elements. -/
lemma card_le_mul_of_fiber_range {s : Finset ℕ} {phi : ℕ → ℤ} {c L : ℕ} {y : ℤ}
    (hfib : ∀ n ∈ s, ∀ m ∈ s, phi n = phi m → n ≤ m + c)
    (hrange : ∀ n ∈ s, y ≤ phi n ∧ phi n ≤ y + L) :
    s.card ≤ (c + 1) * (L + 1) := by
  classical
  rw [Finset.card_eq_sum_card_fiberwise
      (f := phi) (t := s.image phi) (by intro x hx; exact Finset.mem_image.mpr ⟨x, hx, rfl⟩)]
  calc ∑ b ∈ s.image phi, (s.filter fun a => phi a = b).card
      ≤ ∑ _b ∈ s.image phi, (c + 1) := by
        apply Finset.sum_le_sum
        intro b hb
        rcases Finset.eq_empty_or_nonempty (s.filter (fun a => phi a = b)) with he | hne
        · rw [he]; simp
        · have hmin_mem : (s.filter fun a => phi a = b).min' hne ∈ (s.filter fun a => phi a = b) := Finset.min'_mem _ hne
          have hsub : (s.filter fun a => phi a = b) ⊆
              Finset.Icc ((s.filter fun a => phi a = b).min' hne) ((s.filter fun a => phi a = b).min' hne + c) := by
            intro x hx
            rw [Finset.mem_Icc]
            refine ⟨Finset.min'_le _ x hx, ?_⟩
            have hx' : x ∈ s := (Finset.mem_filter.mp hx).1
            have hp' : (s.filter fun a => phi a = b).min' hne ∈ s := (Finset.mem_filter.mp hmin_mem).1
            have heq : phi x = phi ((s.filter fun a => phi a = b).min' hne) := by
              rw [(Finset.mem_filter.mp hx).2, (Finset.mem_filter.mp hmin_mem).2]
            exact hfib x hx' _ hp' heq
          calc (s.filter fun a => phi a = b).card
              ≤ (Finset.Icc ((s.filter fun a => phi a = b).min' hne) ((s.filter fun a => phi a = b).min' hne + c)).card :=
                Finset.card_le_card hsub
            _ = c + 1 := by rw [Nat.card_Icc]; omega
    _ = (s.image phi).card * (c + 1) := by rw [Finset.sum_const, smul_eq_mul]
    _ ≤ (L + 1) * (c + 1) := by
        apply Nat.mul_le_mul_right
        calc (s.image phi).card ≤ (Finset.Icc y (y + L)).card := by
              apply Finset.card_le_card
              intro z hz
              rcases Finset.mem_image.mp hz with ⟨x, hx, rfl⟩
              exact Finset.mem_Icc.mpr (hrange x hx)
          _ = L + 1 := by rw [Int.card_Icc]; rw [show y + (L:ℤ) + 1 - y = (L:ℤ)+1 by ring]; simp
    _ = (c + 1) * (L + 1) := by ring

/-- If an integer `z` is at most a real number `x`, then `z ≤ round x`. -/
lemma le_round_of_le {x : ℝ} {z : ℤ} (h : (z : ℝ) ≤ x) : z ≤ round x := by
  by_contra hc
  rw [not_le] at hc
  have h1 : (z : ℝ) - 1 < (round x : ℝ) := by
    have := sub_half_lt_round x
    linarith
  have h2 : z - 1 < round x := by exact_mod_cast h1
  omega

/-- If a real number `x` is at most an integer `z`, then `round x ≤ z`. -/
lemma round_le_of_le {x : ℝ} {z : ℤ} (h : x ≤ (z : ℝ)) : round x ≤ z := by
  by_contra hc
  rw [not_le] at hc
  have hz1 : z + 1 ≤ round x := by omega
  have h1 : (z : ℝ) + 1 ≤ (round x : ℝ) := by exact_mod_cast hz1
  have h2 : (round x : ℝ) ≤ x + 1 / 2 := round_le_add_half x
  linarith

/-- Telescoping bound for a function with increments in `[μ, A₀ μ]` on `{1,…,N}`. -/
lemma g_diff_bounds {N : ℕ} {g : ℝ → ℝ} {mu A0 : ℝ}
    (hinc : ∀ n : ℕ, 1 ≤ n → n < N → mu ≤ g ((n : ℝ) + 1) - g (n:ℝ))
    (hinc2 : ∀ n : ℕ, 1 ≤ n → n < N → g ((n : ℝ) + 1) - g (n:ℝ) ≤ A0 * mu)
    {n m : ℕ} (hn : 1 ≤ n) (hmN : m ≤ N) (hnm : n ≤ m) :
    mu * ((m : ℝ) - n) ≤ g (m:ℝ) - g (n:ℝ) ∧
      g (m:ℝ) - g (n:ℝ) ≤ A0 * mu * ((m : ℝ) - n) := by
  have hsum : ∑ i ∈ Finset.Ico n m, (g ((i : ℝ) + 1) - g (i:ℝ)) = g (m:ℝ) - g (n:ℝ) := by
    have h := Finset.sum_Ico_sub (fun i : ℕ => g (i:ℝ)) hnm
    simpa [Nat.cast_add, Nat.cast_one] using h
  constructor
  · have hle : ∑ i ∈ Finset.Ico n m, mu ≤ ∑ i ∈ Finset.Ico n m, (g ((i:ℝ)+1) - g (i:ℝ)) := by
      apply Finset.sum_le_sum
      intro i hi
      rw [Finset.mem_Ico] at hi
      exact hinc i (le_trans hn hi.1) (lt_of_lt_of_le hi.2 hmN)
    rw [hsum] at hle
    rw [Finset.sum_const, nsmul_eq_mul] at hle
    have hcard : ((Finset.Ico n m).card : ℝ) = (m:ℝ) - (n:ℝ) := by
      rw [Nat.card_Ico, Nat.cast_sub hnm]
    rw [hcard] at hle
    linarith
  · have hle : ∑ i ∈ Finset.Ico n m, (g ((i:ℝ)+1) - g (i:ℝ)) ≤ ∑ i ∈ Finset.Ico n m, (A0*mu) := by
      apply Finset.sum_le_sum
      intro i hi
      rw [Finset.mem_Ico] at hi
      exact hinc2 i (le_trans hn hi.1) (lt_of_lt_of_le hi.2 hmN)
    rw [hsum] at hle
    rw [Finset.sum_const, nsmul_eq_mul] at hle
    have hcard : ((Finset.Ico n m).card : ℝ) = (m:ℝ) - (n:ℝ) := by
      rw [Nat.card_Ico, Nat.cast_sub hnm]
    rw [hcard] at hle
    linarith

theorem space_count (N : ℕ) (g : ℝ → ℝ) (mu A0 theta : ℝ)
    (hmu : 0 < mu) (hA0 : 1 ≤ A0) (htheta0 : 0 ≤ theta) (htheta1 : theta ≤ 1)
    (hinc : ∀ n : ℕ, 1 ≤ n → n < N → mu ≤ g ((n : ℝ) + 1) - g n)
    (hinc2 : ∀ n : ℕ, 1 ≤ n → n < N → g ((n : ℝ) + 1) - g n ≤ A0 * mu) :
    (((Finset.Icc 1 N).filter (fun n : ℕ => nint (g (n : ℝ)) ≤ theta)).card : ℝ)
      ≤ 100 * (1 + A0 * mu * N) * (1 + theta / mu) := by
  classical
  set S : Finset ℕ := (Finset.Icc 1 N).filter (fun n : ℕ => nint (g (n : ℝ)) ≤ theta) with hS
  rcases Finset.eq_empty_or_nonempty S with hSe | hSne
  · rw [hSe]
    simp only [Finset.card_empty, Nat.cast_zero]
    have h1 : (0:ℝ) ≤ 1 + A0 * mu * N := by
      have h0 : (0:ℝ) ≤ A0 * mu * N := mul_nonneg (mul_nonneg (by linarith) hmu.le) (by positivity)
      linarith
    have h2 : (0:ℝ) ≤ 1 + theta / mu := by
      have h0 : (0:ℝ) ≤ theta / mu := div_nonneg htheta0 hmu.le
      linarith
    exact mul_nonneg (mul_nonneg (by norm_num) h1) h2
  · set n0 := S.min' hSne with hn0def
    have hn0mem : n0 ∈ S := Finset.min'_mem S hSne
    have hn0le : ∀ n ∈ S, n0 ≤ n := fun n hn => Finset.min'_le S n hn
    have hn0_1 : 1 ≤ n0 := (Finset.mem_Icc.mp (Finset.mem_filter.mp hn0mem).1).1
    have hn0_N : n0 ≤ N := (Finset.mem_Icc.mp (Finset.mem_filter.mp hn0mem).1).2
    have hn0_nint : |g (n0:ℝ) - ((round (g (n0:ℝ))) : ℝ)| ≤ theta := by
      have := (Finset.mem_filter.mp hn0mem).2
      simpa [nint] using this
    have hA0pos : (0:ℝ) < A0 := lt_of_lt_of_le zero_lt_one hA0
    have hA0muNnn : (0:ℝ) ≤ A0 * mu * N := mul_nonneg (mul_nonneg hA0pos.le hmu.le) (by positivity)
    have hthmu : (0:ℝ) ≤ theta / mu := div_nonneg htheta0 hmu.le
    set c : ℕ := Nat.ceil (2 * theta / mu) with hcdef
    set L : ℕ := Nat.ceil (A0 * mu * N) + 3 with hLdef
    set y : ℤ := round (g (n0:ℝ)) - 1 with hydef
    have hyR : (y:ℝ) = (round (g (n0:ℝ)) : ℝ) - 1 := by rw [hydef]; push_cast; ring
    have hmain : S.card ≤ (c + 1) * (L + 1) := by
      apply card_le_mul_of_fiber_range (phi := fun n : ℕ => round (g (n:ℝ))) (y := y)
      · intro n hn m hm heq
        have hnf := Finset.mem_filter.mp hn
        have hmf := Finset.mem_filter.mp hm
        have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hnf.1).1
        have hnN : n ≤ N := (Finset.mem_Icc.mp hnf.1).2
        have hm1 : 1 ≤ m := (Finset.mem_Icc.mp hmf.1).1
        have hmN : m ≤ N := (Finset.mem_Icc.mp hmf.1).2
        have hnint : |g (n:ℝ) - ((round (g (n:ℝ))) : ℝ)| ≤ theta := by simpa [nint] using hnf.2
        have hmint : |g (m:ℝ) - ((round (g (m:ℝ))) : ℝ)| ≤ theta := by simpa [nint] using hmf.2
        have heqR : ((round (g (n:ℝ))) : ℝ) = ((round (g (m:ℝ))) : ℝ) := by exact_mod_cast heq
        have habs : |g (n:ℝ) - g (m:ℝ)| ≤ 2 * theta := by
          have hmid : |((round (g (n:ℝ))) : ℝ) - ((round (g (m:ℝ))) : ℝ)| = 0 := by
            rw [heqR, sub_self, abs_zero]
          have hmint' : |((round (g (m:ℝ))) : ℝ) - g (m:ℝ)| ≤ theta := by
            rw [abs_sub_comm]; exact hmint
          have key := abs_add_three (g (n:ℝ) - ((round (g (n:ℝ))) : ℝ))
              (((round (g (n:ℝ))) : ℝ) - ((round (g (m:ℝ))) : ℝ))
              (((round (g (m:ℝ))) : ℝ) - g (m:ℝ))
          have hsum' : (g (n:ℝ) - ((round (g (n:ℝ))) : ℝ)) +
              (((round (g (n:ℝ))) : ℝ) - ((round (g (m:ℝ))) : ℝ)) +
              (((round (g (m:ℝ))) : ℝ) - g (m:ℝ)) = g (n:ℝ) - g (m:ℝ) := by ring
          rw [hsum'] at key
          rw [hmid] at key
          linarith [hnint, hmint']
        have hlow : mu * |(n:ℝ) - (m:ℝ)| ≤ |g (n:ℝ) - g (m:ℝ)| := by
          rcases le_total n m with hnm | hmn
          · have hb := (g_diff_bounds (N:=N) (g:=g) (mu:=mu) (A0:=A0) hinc hinc2 hn1 hmN hnm).1
            have hnm' : (n:ℝ) ≤ (m:ℝ) := by exact_mod_cast hnm
            have hgnm : g (n:ℝ) - g (m:ℝ) ≤ 0 := by
              have : (0:ℝ) ≤ mu * ((m:ℝ) - n) := mul_nonneg hmu.le (sub_nonneg.mpr hnm')
              linarith
            have h1 : |(n:ℝ) - (m:ℝ)| = (m:ℝ) - (n:ℝ) := by rw [abs_of_nonpos (by linarith)]; ring
            have h2 : |g (n:ℝ) - g (m:ℝ)| = g (m:ℝ) - g (n:ℝ) := by rw [abs_of_nonpos hgnm]; ring
            rw [h1, h2]; linarith
          · have hb := (g_diff_bounds (N:=N) (g:=g) (mu:=mu) (A0:=A0) hinc hinc2 hm1 hnN hmn).1
            have hmn' : (m:ℝ) ≤ (n:ℝ) := by exact_mod_cast hmn
            have hgnm : (0:ℝ) ≤ g (n:ℝ) - g (m:ℝ) := by
              have : (0:ℝ) ≤ mu * ((n:ℝ) - m) := mul_nonneg hmu.le (sub_nonneg.mpr hmn')
              linarith
            have h1 : |(n:ℝ) - (m:ℝ)| = (n:ℝ) - (m:ℝ) := abs_of_nonneg (by linarith)
            have h2 : |g (n:ℝ) - g (m:ℝ)| = g (n:ℝ) - g (m:ℝ) := abs_of_nonneg hgnm
            rw [h1, h2]; linarith
        have h2t : mu * |(n:ℝ) - (m:ℝ)| ≤ 2 * theta := le_trans hlow habs
        have hdiv : |(n:ℝ) - (m:ℝ)| ≤ 2 * theta / mu := by
          rw [le_div_iff₀ hmu]; linarith
        have hle2 : (n:ℝ) - (m:ℝ) ≤ 2 * theta / mu := le_trans (le_abs_self _) hdiv
        have hcge : 2 * theta / mu ≤ (c : ℝ) := by rw [hcdef]; exact Nat.le_ceil _
        have hfin : (n:ℝ) ≤ ((m + c : ℕ) : ℝ) := by push_cast; linarith
        exact_mod_cast hfin
      · intro n hn
        have hnf := Finset.mem_filter.mp hn
        have hnN : n ≤ N := (Finset.mem_Icc.mp hnf.1).2
        have hnle : n0 ≤ n := hn0le n hn
        have hge : g (n0:ℝ) ≤ g (n:ℝ) := by
          have hb := (g_diff_bounds (N:=N) (g:=g) (mu:=mu) (A0:=A0) hinc hinc2 hn0_1 hnN hnle).1
          have hnn : (0:ℝ) ≤ mu * ((n:ℝ) - n0) :=
            mul_nonneg hmu.le (sub_nonneg.mpr (by exact_mod_cast hnle))
          linarith
        constructor
        · have hyn : (y:ℝ) ≤ g (n:ℝ) := by
            have hlow := (abs_le.mp hn0_nint).1
            rw [hyR]; linarith
          exact le_round_of_le hyn
        · have hgn_le : g (n:ℝ) ≤ (round (g (n0:ℝ)) : ℝ) + theta + A0 * mu * N := by
            have hb := (g_diff_bounds (N:=N) (g:=g) (mu:=mu) (A0:=A0) hinc hinc2 hn0_1 hnN hnle).2
            have hup := (abs_le.mp hn0_nint).2
            have hsub : (n:ℝ) - n0 ≤ (N:ℝ) := by
              have h1 : (n:ℝ) ≤ (N:ℝ) := by exact_mod_cast hnN
              have h2 : (0:ℝ) ≤ (n0:ℝ) := by positivity
              linarith
            have hb2 : A0 * mu * ((n:ℝ) - n0) ≤ A0 * mu * N :=
              mul_le_mul_of_nonneg_left hsub (mul_nonneg hA0pos.le hmu.le)
            linarith
          have hround_le : (round (g (n:ℝ)) : ℝ) ≤ (y:ℝ) + (L:ℝ) := by
            have h1 : (round (g (n:ℝ)) : ℝ) ≤ g (n:ℝ) + 1/2 := round_le_add_half _
            have hLge : A0 * mu * N + 3 ≤ (L:ℝ) := by
              have := Nat.le_ceil (A0 * mu * N)
              rw [hLdef]; push_cast; linarith
            rw [hyR]; linarith
          exact_mod_cast hround_le
    calc (S.card : ℝ) ≤ ((c + 1) * (L + 1) : ℕ) := by exact_mod_cast hmain
      _ = ((c:ℝ) + 1) * ((L:ℝ) + 1) := by push_cast; ring
      _ ≤ (2 * theta / mu + 2) * (A0 * mu * N + 5) := by
          apply mul_le_mul
          · have hceil : ((Nat.ceil (2 * theta / mu) : ℕ) : ℝ) < 2 * theta / mu + 1 :=
              Nat.ceil_lt_add_one (div_nonneg (by linarith) hmu.le)
            rw [hcdef]; linarith
          · have hceil : ((Nat.ceil (A0 * mu * N) : ℕ) : ℝ) < A0 * mu * N + 1 :=
              Nat.ceil_lt_add_one hA0muNnn
            rw [hLdef]; push_cast; linarith
          · positivity
          · positivity
      _ ≤ 100 * (1 + A0 * mu * N) * (1 + theta / mu) := by
          have hkey : 100 * (1 + A0 * mu * N) * (1 + theta / mu) - (2 * theta / mu + 2) * (A0 * mu * N + 5)
              = 90 + 98 * (A0 * mu * N) + 90 * (theta / mu) + 98 * ((A0 * mu * N) * (theta / mu)) := by
            ring
          have huv : (0:ℝ) ≤ (A0 * mu * N) * (theta / mu) := mul_nonneg hA0muNnn hthmu
          linarith [hkey, hA0muNnn, hthmu, huv]

end Work.BMF
