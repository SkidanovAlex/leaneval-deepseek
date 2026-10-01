import Mathlib

/-!
# The repaired `a1`-sum bound

`Work.LinnikBurgess.a1_sum_bound` (file `a1_sum_bound.lean`) is **false** as stated: with
`H = 1, d = 1` and `|a0 - a1| = m` the single summand equals `2√m`, which exceeds the
right-hand side `4·(τ(d)/d + 1)·τ(m) = 8τ(m)` for every prime `m ≥ 67`.

This file states and proves the repair.  The failure is caused by

* the term `a1 = a0` (i.e. `k = 0`), whose contribution is `(H·d/d + 1)·√m = (H+1)√m`: the
  right-hand side's `4H²τ(d)/d·τ(m)` piece cannot absorb it when `τ(d)/d` is small
  (e.g. `d` a large prime), so that term has to be excluded; and
* the anchoring of the window: if `a0 ∉ [1,H]` then the `H`-window of differences `a0 - a1` is
  not rooted at `0`, and a single term with `dm ∣ k` again contributes `(H+1)√m`
  (see `a1_sum_bound_mleH_false`, which shows that adding `m ≤ H` does **not** repair the
  statement).

So the correct hypotheses are `1 ≤ a0 ≤ H` together with the guard `a1 ≠ a0`.  Under them the
elementary divisor-counting argument goes through with no hypothesis relating `m`, `d`, `H`:
for each `n ≥ 1` the set `{a1 ∈ [1,H] : a1 ≠ a0, n ∣ |a0-a1|}` has at most `H/n` elements
(`a1Idx_residue_card`), whence

* `∑_{a1 ≠ a0} √gcd(m, |a0-a1|) ≤ H·τ(m)`, and
* `(H/d)·∑_{a1 ≠ a0} gcd(d, |a0-a1|)·√gcd(m, |a0-a1|) ≤ (H²/d)·τ(d)·τ(m)`,

using `gcd(N,k) = ∑_{n ∣ N, n ∣ k} φ(n)` and `φ(n)/n ≤ 1`.

## Scorecard of the proposed repairs (all machine-checked in this file or in `a1_sum_bound.lean`)

| repair | verdict |
|---|---|
| restrict to `a1 ≠ a0` **and** `1 ≤ a0 ≤ H` | **true** — `a1_sum_bound_guarded` |
| the requested statement unchanged | **false** — `a1_sum_bound_statement_false` (`a1_sum_bound.lean`) |
| add the hypothesis `m ≤ H` | **false** — `a1_sum_bound_mleH_false` |
| restrict to `a1 ≠ a0` only (no anchoring) | **false** — `a1_sum_bound_guardOnly_false` |
| add `2√m` to the right-hand side | **false** — `a1_sum_bound_shift2sqrt_false` |

There is also a *conservative* form needing no change of range: `a1_sum_bound_guarded_full` bounds
the sum over the whole `[1,H]` by the same right-hand side plus the explicit extra term `(H+1)√m`
(the `a1 = a0` summand), for use when the range cannot be filtered.

The three failures have the same cause: a single difference `k = |a0-a1|` with `dm ∣ k` (or `k=0`)
contributes `(H+1)·√m`, and `4H²τ(d)/d·τ(m)` is of size `8Hτ(m)` when `d ≫ H`, which cannot reach
`H√m` once `m` is a prime `≥ 67`.
-/

open Finset

namespace Work.LinnikBurgess

/-- `|a0 - a1|` as a natural number. -/
def a1Shift (a0 a1 : ℕ) : ℕ := ((a0 : ℤ) - (a1 : ℤ)).natAbs

/-- The repaired summation range: `a1 ∈ [1,H]` with `a1 ≠ a0`. -/
def a1Idx (a0 H : ℕ) : Finset ℕ := (Finset.Icc 1 H).filter (fun a1 => a1 ≠ a0)

/-! ### Elementary helpers -/

/-- For `a1 ≤ a0` the shift is the natural difference. -/
private lemma a1Shift_of_le {a0 a1 : ℕ} (h : a1 ≤ a0) : a1Shift a0 a1 = a0 - a1 := by
  rw [a1Shift, ← Int.ofNat_sub h, Int.natAbs_natCast]

/-- For `a0 ≤ a1` the shift is the natural difference. -/
private lemma a1Shift_of_ge {a0 a1 : ℕ} (h : a0 ≤ a1) : a1Shift a0 a1 = a1 - a0 := by
  rw [a1Shift, show ((a0 : ℤ) - (a1 : ℤ)) = -((a1 : ℤ) - (a0 : ℤ)) by ring, Int.natAbs_neg,
    ← Int.ofNat_sub h, Int.natAbs_natCast]

/-- `√x ≤ x` for a natural number `x ≥ 1`. -/
private lemma sqrt_natCast_le_self {x : ℕ} (hx : 1 ≤ x) : Real.sqrt ((x : ℕ) : ℝ) ≤ (x : ℝ) := by
  have h1 : (1 : ℝ) ≤ (x : ℝ) := by exact_mod_cast hx
  rw [Real.sqrt_le_iff]
  refine ⟨by positivity, ?_⟩
  nlinarith [mul_nonneg (by positivity : (0 : ℝ) ≤ (x : ℝ)) (sub_nonneg.mpr h1)]

/-- At most `K / n` multiples of `n` lie in `[1,K]`. -/
private lemma card_multiples_Icc_le (K n : ℕ) (hn : 1 ≤ n) :
    ((Finset.Icc 1 K).filter (fun p => n ∣ p)).card ≤ K / n := by
  have hn0 : 0 < n := hn
  set S := (Finset.Icc 1 K).filter (fun p => n ∣ p) with hS
  have hsub : S.image (fun p => p / n) ⊆ Finset.Icc 1 (K / n) := by
    intro x hx
    rcases Finset.mem_image.mp hx with ⟨p, hp, rfl⟩
    have hpI : p ∈ Finset.Icc 1 K := (Finset.mem_filter.mp hp).1
    have hpn : n ∣ p := (Finset.mem_filter.mp hp).2
    have hp1 : 0 < p := (Finset.mem_Icc.mp hpI).1
    have hpK : p ≤ K := (Finset.mem_Icc.mp hpI).2
    rw [Finset.mem_Icc]
    exact ⟨(Nat.one_le_div_iff hn0).mpr (Nat.le_of_dvd hp1 hpn), Nat.div_le_div_right hpK⟩
  have hinj : Set.InjOn (fun p : ℕ => p / n) ↑S := by
    intro p hp q hq hpq
    have hpn : n ∣ p := (Finset.mem_filter.mp hp).2
    have hqn : n ∣ q := (Finset.mem_filter.mp hq).2
    have h2 : p / n = q / n := by simpa using hpq
    have h1 : p = q := by
      rw [← Nat.mul_div_cancel' hpn, ← Nat.mul_div_cancel' hqn, h2]
    exact h1
  calc S.card = (S.image (fun p => p / n)).card := (Finset.card_image_of_injOn hinj).symm
    _ ≤ (Finset.Icc 1 (K / n)).card := Finset.card_le_card hsub
    _ = K / n := by simp

/-- From `card·n ≤ H` (with `n ≥ 1`) get the real bound `card ≤ H/n`. -/
private lemma card_cast_le_div {s : Finset ℕ} {H n : ℕ} (hn : 1 ≤ n) (h : s.card * n ≤ H) :
    ((s.card : ℕ) : ℝ) ≤ (H : ℝ) / (n : ℝ) := by
  have hn' : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  rw [le_div_iff₀ hn']
  have h' : ((s.card * n : ℕ) : ℝ) ≤ (H : ℝ) := by exact_mod_cast h
  push_cast at h'
  linarith

/-- Sums of `c` over the divisors of `k a1` inside a fixed divisor set `D`, swapped. -/
private lemma swap_sum_filter (S D : Finset ℕ) (k : ℕ → ℕ) (c : ℕ → ℝ) :
    (∑ a1 ∈ S, ∑ n ∈ D.filter (fun n => n ∣ k a1), c n)
      = ∑ n ∈ D, c n * (((S.filter (fun a1 => n ∣ k a1)).card : ℕ) : ℝ) := by
  calc (∑ a1 ∈ S, ∑ n ∈ D.filter (fun n => n ∣ k a1), c n)
      = ∑ a1 ∈ S, ∑ n ∈ D, (if n ∣ k a1 then c n else 0) := by
        refine Finset.sum_congr rfl (fun a1 _ => ?_)
        rw [Finset.sum_filter]
    _ = ∑ n ∈ D, ∑ a1 ∈ S, (if n ∣ k a1 then c n else 0) := Finset.sum_comm
    _ = ∑ n ∈ D, c n * (((S.filter (fun a1 => n ∣ k a1)).card : ℕ) : ℝ) := by
        refine Finset.sum_congr rfl (fun n _ => ?_)
        rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
        ring

/-- `φ(n)/n ≤ 1`, so `∑_{n ∣ M} φ(n)/n ≤ τ(M)`. -/
private lemma sum_totient_div_le_card (M : ℕ) :
    (∑ n ∈ M.divisors, (Nat.totient n : ℝ) / (n : ℝ)) ≤ ((M.divisors.card : ℕ) : ℝ) := by
  have h : ∀ n ∈ M.divisors, (Nat.totient n : ℝ) / (n : ℝ) ≤ 1 := by
    intro n hn
    have hn0 : (0 : ℝ) < (n : ℝ) := by
      have := Nat.pos_of_mem_divisors hn
      exact_mod_cast this
    rw [div_le_one hn0]
    exact_mod_cast Nat.totient_le n
  calc (∑ n ∈ M.divisors, (Nat.totient n : ℝ) / (n : ℝ)) ≤ ∑ n ∈ M.divisors, (1 : ℝ) :=
        Finset.sum_le_sum h
    _ = ((M.divisors.card : ℕ) : ℝ) := by simp

/-- For coprime positive `d, m`, the product of the two gcds divides `gcd (d·m) k`. -/
private lemma gcd_mul_gcd_dvd {d m k : ℕ} (_hm : 0 < m) (_hd : 0 < d) (hmd : Nat.Coprime d m) :
    Nat.gcd d k * Nat.gcd m k ∣ Nat.gcd (d * m) k := by
  have hc : Nat.Coprime (Nat.gcd d k) (Nat.gcd m k) :=
    (hmd.coprime_dvd_left (Nat.gcd_dvd_left d k)).coprime_dvd_right (Nat.gcd_dvd_left m k)
  exact Nat.dvd_gcd
    (hc.mul_dvd_of_dvd_of_dvd (Nat.dvd_trans (Nat.gcd_dvd_left d k) (Nat.dvd_mul_right d m))
      (Nat.dvd_trans (Nat.gcd_dvd_left m k) (Nat.dvd_mul_left m d)))
    (hc.mul_dvd_of_dvd_of_dvd (Nat.gcd_dvd_right d k) (Nat.gcd_dvd_right m k))

/-- `τ(d·m) ≤ τ(d)·τ(m)`. -/
private lemma card_divisors_mul_le (d m : ℕ) :
    (d * m).divisors.card ≤ d.divisors.card * m.divisors.card := by
  rw [Nat.divisors_mul]
  exact Finset.card_mul_le

/-! ### The library lemmas -/

/-- **Counting a residue class rooted at `a0`.**  For `1 ≤ a0 ≤ H` and `1 ≤ n`, the number of
`a1 ∈ [1,H]`, `a1 ≠ a0` with `n ∣ |a0 - a1|` is at most `H/n`, in the strong form
`card * n ≤ H`.  (`a0` itself is the unique term with `k = 0` in the window, and removing it is
what makes the estimate independent of the position of the window.) -/
theorem a1Idx_residue_card {a0 H n : ℕ} (ha0 : 1 ≤ a0) (ha0H : a0 ≤ H) (hn : 1 ≤ n) :
    ((a1Idx a0 H).filter (fun a1 : ℕ => n ∣ a1Shift a0 a1)).card * n ≤ H := by
  set T := (a1Idx a0 H).filter (fun a1 : ℕ => n ∣ a1Shift a0 a1) with hT
  have hlo : (T.filter (fun a1 => a1 < a0)).card ≤ (a0 - 1) / n := by
    have hsub : (T.filter (fun a1 => a1 < a0)).image (fun a1 => a0 - a1)
        ⊆ (Finset.Icc 1 (a0 - 1)).filter (fun p => n ∣ p) := by
      intro x hx
      rcases Finset.mem_image.mp hx with ⟨a1, ha1, rfl⟩
      have ha1T : a1 ∈ T := (Finset.mem_filter.mp ha1).1
      have hlt : a1 < a0 := (Finset.mem_filter.mp ha1).2
      have ha1I : a1 ∈ Finset.Icc 1 H := (Finset.mem_filter.mp (Finset.mem_filter.mp ha1T).1).1
      have ha11 : 1 ≤ a1 := (Finset.mem_Icc.mp ha1I).1
      have hdiv : n ∣ a1Shift a0 a1 := (Finset.mem_filter.mp ha1T).2
      rw [a1Shift_of_le (le_of_lt hlt)] at hdiv
      rw [Finset.mem_filter, Finset.mem_Icc]
      exact ⟨⟨by omega, by omega⟩, hdiv⟩
    have hinj : Set.InjOn (fun a1 : ℕ => a0 - a1) ↑(T.filter (fun a1 => a1 < a0)) := by
      intro p hp q hq hpq
      have hpq' : a0 - p = a0 - q := by simpa using hpq
      have hp' : p < a0 := (Finset.mem_filter.mp hp).2
      have hq' : q < a0 := (Finset.mem_filter.mp hq).2
      omega
    calc (T.filter (fun a1 => a1 < a0)).card
        = ((T.filter (fun a1 => a1 < a0)).image (fun a1 => a0 - a1)).card :=
          (Finset.card_image_of_injOn hinj).symm
      _ ≤ ((Finset.Icc 1 (a0 - 1)).filter (fun p => n ∣ p)).card := Finset.card_le_card hsub
      _ ≤ (a0 - 1) / n := card_multiples_Icc_le _ _ hn
  have hhi : (T.filter (fun a1 => a0 < a1)).card ≤ (H - a0) / n := by
    have hsub : (T.filter (fun a1 => a0 < a1)).image (fun a1 => a1 - a0)
        ⊆ (Finset.Icc 1 (H - a0)).filter (fun p => n ∣ p) := by
      intro x hx
      rcases Finset.mem_image.mp hx with ⟨a1, ha1, rfl⟩
      have ha1T : a1 ∈ T := (Finset.mem_filter.mp ha1).1
      have hgt : a0 < a1 := (Finset.mem_filter.mp ha1).2
      have ha1I : a1 ∈ Finset.Icc 1 H := (Finset.mem_filter.mp (Finset.mem_filter.mp ha1T).1).1
      have ha1H : a1 ≤ H := (Finset.mem_Icc.mp ha1I).2
      have hdiv : n ∣ a1Shift a0 a1 := (Finset.mem_filter.mp ha1T).2
      rw [a1Shift_of_ge (le_of_lt hgt)] at hdiv
      rw [Finset.mem_filter, Finset.mem_Icc]
      exact ⟨⟨by omega, by omega⟩, hdiv⟩
    have hinj : Set.InjOn (fun a1 : ℕ => a1 - a0) ↑(T.filter (fun a1 => a0 < a1)) := by
      intro p hp q hq hpq
      have hpq' : p - a0 = q - a0 := by simpa using hpq
      have hp' : a0 < p := (Finset.mem_filter.mp hp).2
      have hq' : a0 < q := (Finset.mem_filter.mp hq).2
      omega
    calc (T.filter (fun a1 => a0 < a1)).card
        = ((T.filter (fun a1 => a0 < a1)).image (fun a1 => a1 - a0)).card :=
          (Finset.card_image_of_injOn hinj).symm
      _ ≤ ((Finset.Icc 1 (H - a0)).filter (fun p => n ∣ p)).card := Finset.card_le_card hsub
      _ ≤ (H - a0) / n := card_multiples_Icc_le _ _ hn
  have hcover : T ⊆ T.filter (fun a1 => a1 < a0) ∪ T.filter (fun a1 => a0 < a1) := by
    intro a1 ha1
    have hne : a1 ≠ a0 := (Finset.mem_filter.mp (Finset.mem_filter.mp ha1).1).2
    rcases lt_trichotomy a1 a0 with h | h | h
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨ha1, h⟩)
    · exact absurd h hne
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨ha1, h⟩)
  have hcard : T.card ≤ (a0 - 1) / n + (H - a0) / n := by
    calc T.card ≤ (T.filter (fun a1 => a1 < a0) ∪ T.filter (fun a1 => a0 < a1)).card :=
          Finset.card_le_card hcover
      _ ≤ (T.filter (fun a1 => a1 < a0)).card + (T.filter (fun a1 => a0 < a1)).card :=
          Finset.card_union_le _ _
      _ ≤ (a0 - 1) / n + (H - a0) / n := add_le_add hlo hhi
  calc T.card * n ≤ ((a0 - 1) / n + (H - a0) / n) * n := Nat.mul_le_mul_right _ hcard
    _ = (a0 - 1) / n * n + (H - a0) / n * n := by ring
    _ ≤ (a0 - 1) + (H - a0) := add_le_add (Nat.div_mul_le_self _ _) (Nat.div_mul_le_self _ _)
    _ = H - 1 := by omega
    _ ≤ H := by omega

/-- **Totient identity for `gcd`.**  `gcd M k = ∑_{n ∣ M, n ∣ k} φ(n)` for `M > 0`. -/
theorem gcd_eq_sum_totient_filter {M : ℕ} (hM : 0 < M) (k : ℕ) :
    Nat.gcd M k = ∑ n ∈ M.divisors.filter (fun n => n ∣ k), Nat.totient n := by
  have hpos : 0 < Nat.gcd M k := Nat.gcd_pos_of_pos_left k hM
  rw [← Nat.sum_totient (Nat.gcd M k)]
  refine Finset.sum_congr ?_ (fun n _ => rfl)
  ext n
  rw [Nat.mem_divisors, Finset.mem_filter, Nat.mem_divisors]
  constructor
  · rintro ⟨hnd, -⟩
    exact ⟨⟨Nat.dvd_trans hnd (Nat.gcd_dvd_left M k), ne_of_gt hM⟩,
      Nat.dvd_trans hnd (Nat.gcd_dvd_right M k)⟩
  · rintro ⟨⟨hnM, _⟩, hnk⟩
    exact ⟨Nat.dvd_gcd hnM hnk, ne_of_gt hpos⟩

/-- **The core divisor-sum bound.**  For `M > 0` and `1 ≤ a0 ≤ H`,
`∑_{a1 ∈ [1,H], a1 ≠ a0} gcd(M, |a0-a1|) ≤ H·τ(M)`. -/
private lemma sum_gcd_core (M a0 H : ℕ) (hM : 0 < M) (ha0 : 1 ≤ a0) (ha0H : a0 ≤ H) :
    (∑ a1 ∈ a1Idx a0 H, ((Nat.gcd M (a1Shift a0 a1) : ℕ) : ℝ))
      ≤ (H : ℝ) * ((M.divisors.card : ℝ)) := by
  have hcast : ∀ a1 : ℕ, ((Nat.gcd M (a1Shift a0 a1) : ℕ) : ℝ)
      = ∑ n ∈ M.divisors.filter (fun n => n ∣ a1Shift a0 a1), (Nat.totient n : ℝ) := by
    intro a1
    rw [gcd_eq_sum_totient_filter hM]
    push_cast
    ring
  calc (∑ a1 ∈ a1Idx a0 H, ((Nat.gcd M (a1Shift a0 a1) : ℕ) : ℝ))
      = ∑ a1 ∈ a1Idx a0 H, ∑ n ∈ M.divisors.filter (fun n => n ∣ a1Shift a0 a1),
          (Nat.totient n : ℝ) := Finset.sum_congr rfl (fun a1 _ => hcast a1)
    _ = ∑ n ∈ M.divisors, (Nat.totient n : ℝ)
          * (((a1Idx a0 H).filter (fun a1 => n ∣ a1Shift a0 a1)).card : ℝ) :=
        swap_sum_filter _ _ _ _
    _ ≤ ∑ n ∈ M.divisors, (Nat.totient n : ℝ) * ((H : ℝ) / (n : ℝ)) := by
        refine Finset.sum_le_sum (fun n hn => ?_)
        have hn1 : 1 ≤ n := Nat.pos_of_mem_divisors hn
        have hcard := a1Idx_residue_card ha0 ha0H hn1
        have hle := card_cast_le_div hn1 hcard
        have hφ : (0 : ℝ) ≤ (Nat.totient n : ℝ) := by positivity
        nlinarith
    _ = (H : ℝ) * ∑ n ∈ M.divisors, (Nat.totient n : ℝ) / (n : ℝ) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun n hn => ?_)
        have hn0 : (0 : ℝ) < (n : ℝ) := by
          have := Nat.pos_of_mem_divisors hn
          exact_mod_cast this
        field_simp
    _ ≤ (H : ℝ) * ((M.divisors.card : ℝ)) := by
        have hsum := sum_totient_div_le_card M
        have hH : (0 : ℝ) ≤ (H : ℝ) := by positivity
        nlinarith

/-! ### The two halves of the repaired sum -/

/-- **The `+ 1` part.**  `∑_{a1 ∈ [1,H], a1 ≠ a0} √gcd(m, |a0-a1|) ≤ H·τ(m)`. -/
theorem sum_sqrtGcd_guarded_le {m a0 H : ℕ} (hm : 0 < m) (ha0 : 1 ≤ a0) (ha0H : a0 ≤ H) :
    (∑ a1 ∈ a1Idx a0 H, Real.sqrt (((Nat.gcd m (a1Shift a0 a1)) : ℕ) : ℝ))
      ≤ (H : ℝ) * ((m.divisors.card : ℝ)) := by
  refine le_trans (Finset.sum_le_sum (fun a1 _ => ?_)) (sum_gcd_core m a0 H hm ha0 ha0H)
  exact sqrt_natCast_le_self (by
    have := Nat.gcd_pos_of_pos_left (a1Shift a0 a1) hm
    omega)

/-- **The weighted part.**  `(H/d)·∑_{a1 ≠ a0} gcd(d,|a0-a1|)·√gcd(m,|a0-a1|) ≤ (H²/d)·τ(d)·τ(m)`
for positive coprime `d, m` and `1 ≤ a0 ≤ H`. -/
theorem sum_gcdMulSqrtGcd_guarded_le {m d a0 H : ℕ} (hm : 0 < m) (hd : 0 < d)
    (hmd : Nat.Coprime m d) (ha0 : 1 ≤ a0) (ha0H : a0 ≤ H) :
    (H : ℝ) / (d : ℝ) * (∑ a1 ∈ a1Idx a0 H, ((Nat.gcd d (a1Shift a0 a1) : ℕ) : ℝ)
        * Real.sqrt (((Nat.gcd m (a1Shift a0 a1)) : ℕ) : ℝ))
      ≤ ((H : ℝ) ^ 2 * ((d.divisors.card : ℝ)) / (d : ℝ)) * ((m.divisors.card : ℝ)) := by
  have hdR : (0 : ℝ) ≤ (H : ℝ) / (d : ℝ) := by positivity
  have hpt : ∀ a1 ∈ a1Idx a0 H, ((Nat.gcd d (a1Shift a0 a1) : ℕ) : ℝ)
      * Real.sqrt (((Nat.gcd m (a1Shift a0 a1)) : ℕ) : ℝ)
        ≤ ((Nat.gcd (d * m) (a1Shift a0 a1) : ℕ) : ℝ) := by
    intro a1 _
    have h1 : ((Nat.gcd d (a1Shift a0 a1) : ℕ) : ℝ) * ((Nat.gcd m (a1Shift a0 a1) : ℕ) : ℝ)
        ≤ ((Nat.gcd (d * m) (a1Shift a0 a1) : ℕ) : ℝ) := by
      have hdvd := gcd_mul_gcd_dvd (k := a1Shift a0 a1) hm hd hmd.symm
      exact_mod_cast Nat.le_of_dvd (Nat.gcd_pos_of_pos_left _ (Nat.mul_pos hd hm)) hdvd
    have h2 := sqrt_natCast_le_self (show 1 ≤ Nat.gcd m (a1Shift a0 a1) by
      have := Nat.gcd_pos_of_pos_left (a1Shift a0 a1) hm
      omega)
    have h3 : (0 : ℝ) ≤ ((Nat.gcd d (a1Shift a0 a1) : ℕ) : ℝ) := by positivity
    nlinarith
  have hτ : (((d * m).divisors.card : ℕ) : ℝ)
      ≤ ((d.divisors.card : ℕ) : ℝ) * ((m.divisors.card : ℕ) : ℝ) := by
    have := card_divisors_mul_le d m
    exact_mod_cast this
  calc (H : ℝ) / (d : ℝ) * (∑ a1 ∈ a1Idx a0 H, ((Nat.gcd d (a1Shift a0 a1) : ℕ) : ℝ)
        * Real.sqrt (((Nat.gcd m (a1Shift a0 a1)) : ℕ) : ℝ))
      ≤ (H : ℝ) / (d : ℝ) * (∑ a1 ∈ a1Idx a0 H,
          ((Nat.gcd (d * m) (a1Shift a0 a1) : ℕ) : ℝ)) :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum hpt) hdR
    _ ≤ (H : ℝ) / (d : ℝ) * ((H : ℝ) * (((d * m).divisors.card : ℕ) : ℝ)) :=
        mul_le_mul_of_nonneg_left (sum_gcd_core (d * m) a0 H (Nat.mul_pos hd hm) ha0 ha0H) hdR
    _ = ((H : ℝ) ^ 2 / (d : ℝ)) * (((d * m).divisors.card : ℕ) : ℝ) := by
        rw [div_mul_eq_mul_div]; ring
    _ ≤ ((H : ℝ) ^ 2 / (d : ℝ))
          * (((d.divisors.card : ℕ) : ℝ) * ((m.divisors.card : ℕ) : ℝ)) :=
        mul_le_mul_of_nonneg_left hτ (by positivity)
    _ = ((H : ℝ) ^ 2 * ((d.divisors.card : ℝ)) / (d : ℝ)) * ((m.divisors.card : ℝ)) := by ring

/-! ### The repaired statement -/

/-- **The repaired `a1`-sum bound.**  For `0 < m`, `0 < d`, `Nat.Coprime m d` and `1 ≤ a0 ≤ H`,
`∑_{a1 ∈ [1,H], a1 ≠ a0} (H/d·gcd(d,|a0-a1|) + 1)·√gcd(m,|a0-a1|) ≤ 4·(H²·τ(d)/d + H)·τ(m)`.

(No hypothesis relating `m`, `d` and `H` is needed; the requested statement is the special case
in which the guard `a1 ≠ a0` is dropped, and that is exactly what makes it false — see
`a1_sum_bound_statement_false` in `a1_sum_bound.lean` and `a1_sum_bound_mleH_false` below.) -/
theorem a1_sum_bound_guarded {m d H a0 : ℕ} (hm : 0 < m) (hmd : Nat.Coprime m d) (hd : 0 < d)
    (ha0 : 1 ≤ a0) (ha0H : a0 ≤ H) :
    (∑ a1 ∈ (Finset.Icc 1 H).filter (fun a1 => a1 ≠ a0),
        (((H : ℝ) * (Nat.gcd d (((a0 : ℤ) - (a1 : ℤ)).natAbs) : ℝ) / (d : ℝ) + 1)
          * Real.sqrt (((Nat.gcd m (((a0 : ℤ) - (a1 : ℤ)).natAbs)) : ℕ) : ℝ)))
      ≤ 4 * (((H : ℝ) ^ 2 * ((d.divisors.card : ℝ)) / (d : ℝ)) + (H : ℝ))
          * ((m.divisors.card : ℝ)) := by
  have hD := sum_sqrtGcd_guarded_le (m := m) (a0 := a0) (H := H) hm ha0 ha0H
  have hE := sum_gcdMulSqrtGcd_guarded_le (m := m) (d := d) (a0 := a0) (H := H) hm hd hmd ha0 ha0H
  have hsplit : (∑ a1 ∈ a1Idx a0 H,
        (((H : ℝ) * (Nat.gcd d (a1Shift a0 a1) : ℝ) / (d : ℝ) + 1)
          * Real.sqrt (((Nat.gcd m (a1Shift a0 a1)) : ℕ) : ℝ)))
      = (H : ℝ) / (d : ℝ) * (∑ a1 ∈ a1Idx a0 H, ((Nat.gcd d (a1Shift a0 a1) : ℕ) : ℝ)
            * Real.sqrt (((Nat.gcd m (a1Shift a0 a1)) : ℕ) : ℝ))
        + ∑ a1 ∈ a1Idx a0 H, Real.sqrt (((Nat.gcd m (a1Shift a0 a1)) : ℕ) : ℝ) := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun a1 _ => ?_)
    ring
  change (∑ a1 ∈ a1Idx a0 H, (((H : ℝ) * (Nat.gcd d (a1Shift a0 a1) : ℝ) / (d : ℝ) + 1)
        * Real.sqrt (((Nat.gcd m (a1Shift a0 a1)) : ℕ) : ℝ)))
      ≤ 4 * (((H : ℝ) ^ 2 * ((d.divisors.card : ℝ)) / (d : ℝ)) + (H : ℝ))
          * ((m.divisors.card : ℝ))
  rw [hsplit]
  refine le_trans (add_le_add hE hD) ?_
  have hX : (0 : ℝ) ≤ ((H : ℝ) ^ 2 * ((d.divisors.card : ℝ)) / (d : ℝ) + (H : ℝ))
      * ((m.divisors.card : ℝ)) := by positivity
  calc ((H : ℝ) ^ 2 * ((d.divisors.card : ℝ)) / (d : ℝ)) * ((m.divisors.card : ℝ))
        + (H : ℝ) * ((m.divisors.card : ℝ))
      = ((H : ℝ) ^ 2 * ((d.divisors.card : ℝ)) / (d : ℝ) + (H : ℝ))
          * ((m.divisors.card : ℝ)) := by ring
    _ ≤ 4 * (((H : ℝ) ^ 2 * ((d.divisors.card : ℝ)) / (d : ℝ) + (H : ℝ))
          * ((m.divisors.card : ℝ))) := by linarith
    _ = 4 * (((H : ℝ) ^ 2 * ((d.divisors.card : ℝ)) / (d : ℝ)) + (H : ℝ))
          * ((m.divisors.card : ℝ)) := by ring

/-! ### The `m ≤ H` repair fails -/

/-- **The `m ≤ H` repair fails.**  `m = 101 ≤ H = 101`, `d = 1000003` (prime, coprime to `101`)
and `a0 = 1`: the term `a1 = a0` alone contributes `(H·d/d + 1)·√m = 102√101 ≈ 1025`, while the
entire right-hand side is `4·(101²·τ(d)/d + 101)·τ(101) ≈ 808`. -/
theorem a1_sum_bound_mleH_false :
    ¬ ((∑ a1 ∈ Finset.Icc (1 : ℕ) 101,
        (((101 : ℝ) * (Nat.gcd 1000003 (((1 : ℤ) - (a1 : ℤ)).natAbs) : ℝ) / (1000003 : ℝ) + 1)
          * Real.sqrt (((Nat.gcd 101 (((1 : ℤ) - (a1 : ℤ)).natAbs)) : ℕ) : ℝ)))
      ≤ 4 * (((101 : ℝ) ^ 2 * (((1000003 : ℕ).divisors.card : ℝ)) / (1000003 : ℝ)) + (101 : ℝ))
          * (((101 : ℕ).divisors.card : ℝ))) := by
  intro h
  have hnn : ∀ a1 ∈ Finset.Icc (1 : ℕ) 101,
      (0 : ℝ) ≤ (((101 : ℝ) * (Nat.gcd 1000003 (((1 : ℤ) - (a1 : ℤ)).natAbs) : ℝ)
            / (1000003 : ℝ) + 1)
          * Real.sqrt (((Nat.gcd 101 (((1 : ℤ) - (a1 : ℤ)).natAbs)) : ℕ) : ℝ)) := by
    intro a1 _
    positivity
  have hterm : (102 : ℝ) * Real.sqrt 101
      ≤ (∑ a1 ∈ Finset.Icc (1 : ℕ) 101,
        (((101 : ℝ) * (Nat.gcd 1000003 (((1 : ℤ) - (a1 : ℤ)).natAbs) : ℝ) / (1000003 : ℝ) + 1)
          * Real.sqrt (((Nat.gcd 101 (((1 : ℤ) - (a1 : ℤ)).natAbs)) : ℕ) : ℝ))) := by
    have h1 : (1 : ℕ) ∈ Finset.Icc (1 : ℕ) 101 := by simp
    have hs := Finset.single_le_sum hnn h1
    have heq : (((101 : ℝ) * (Nat.gcd 1000003 (((1 : ℤ) - ((1 : ℕ) : ℤ)).natAbs) : ℝ)
            / (1000003 : ℝ) + 1)
          * Real.sqrt (((Nat.gcd 101 (((1 : ℤ) - ((1 : ℕ) : ℤ)).natAbs)) : ℕ) : ℝ))
        = 102 * Real.sqrt 101 := by
      norm_num
    rwa [heq] at hs
  have hR : 4 * (((101 : ℝ) ^ 2 * (((1000003 : ℕ).divisors.card : ℝ)) / (1000003 : ℝ))
        + (101 : ℝ)) * (((101 : ℕ).divisors.card : ℝ)) < 816 := by
    rw [(by norm_num : Nat.Prime 1000003).divisors, (by norm_num : Nat.Prime 101).divisors]
    norm_num
  have hsqrt : (10 : ℝ) ≤ Real.sqrt 101 := by
    rw [Real.le_sqrt (by norm_num) (by norm_num)]
    norm_num
  have h1020 : (1020 : ℝ) ≤ (102 : ℝ) * Real.sqrt 101 := by nlinarith
  linarith

end Work.LinnikBurgess

namespace Work.LinnikBurgess

/-- The parameters of `a1_sum_bound_mleH_false` satisfy every hypothesis of the *requested*
statement, together with the proposed extra hypothesis `m ≤ H`. -/
theorem a1_sum_bound_mleH_false_hypotheses :
    (0 < 101 ∧ 101 ≤ (101 : ℕ) ∧ Nat.Coprime 101 1000003 ∧ 0 < 1000003) :=
  ⟨by norm_num, le_rfl, by decide, by norm_num⟩

private lemma sum_Icc_one_two' (f : ℕ → ℝ) :
    (∑ a1 ∈ Finset.Icc (1 : ℕ) 2, f a1) = f 1 + f 2 := by
  have h := Finset.sum_Icc_succ_top (a := 1) (b := 1) (f := f) (by norm_num : (1 : ℕ) ≤ 1 + 1)
  simpa [Finset.Icc_self] using h

/-- **The guard `a1 ≠ a0` alone does not repair the statement.**  `m = 37`, `H = 2`,
`d = 1009` (prime, coprime to `37`) and `a0 = 37335 ∉ [1,2]`: the guard is vacuous, the term
`a1 = 2` has `|a0 - a1| = 37333 = 37·1009` and contributes `(2·1009/1009 + 1)·√37 = 3√37`, so the
left-hand side is `3√37 + 1 + 2/1009 ≈ 19.25`, while the right-hand side is
`4·(4·τ(1009)/1009 + 2)·τ(37) = 16 + 64/1009 ≈ 16.06`.  So the guard must be combined with the
anchoring `a0 ∈ [1,H]` (or with an `m`-`H`-`d` hypothesis), not used alone. -/
theorem a1_sum_bound_guardOnly_false :
    ¬ ((∑ a1 ∈ (Finset.Icc (1 : ℕ) 2).filter (fun a1 => a1 ≠ 37335),
        (((2 : ℝ) * (Nat.gcd 1009 (((37335 : ℤ) - (a1 : ℤ)).natAbs) : ℝ) / (1009 : ℝ) + 1)
          * Real.sqrt (((Nat.gcd 37 (((37335 : ℤ) - (a1 : ℤ)).natAbs)) : ℕ) : ℝ)))
      ≤ 4 * (((2 : ℝ) ^ 2 * (((1009 : ℕ).divisors.card : ℝ)) / (1009 : ℝ)) + (2 : ℝ))
          * (((37 : ℕ).divisors.card : ℝ))) := by
  intro h
  have hfilter : (Finset.Icc (1 : ℕ) 2).filter (fun a1 => a1 ≠ 37335) = Finset.Icc (1 : ℕ) 2 := by
    refine Finset.filter_true_of_mem ?_
    intro a1 ha1
    simp only [Finset.mem_Icc] at ha1
    omega
  rw [hfilter, sum_Icc_one_two'] at h
  have ht1 : (((2 : ℝ) * (Nat.gcd 1009 (((37335 : ℤ) - ((1 : ℕ) : ℤ)).natAbs) : ℝ)
        / (1009 : ℝ) + 1)
      * Real.sqrt (((Nat.gcd 37 (((37335 : ℤ) - ((1 : ℕ) : ℤ)).natAbs)) : ℕ) : ℝ))
      = 1 + 2 / 1009 := by norm_num
  have ht2 : (((2 : ℝ) * (Nat.gcd 1009 (((37335 : ℤ) - ((2 : ℕ) : ℤ)).natAbs) : ℝ)
        / (1009 : ℝ) + 1)
      * Real.sqrt (((Nat.gcd 37 (((37335 : ℤ) - ((2 : ℕ) : ℤ)).natAbs)) : ℕ) : ℝ))
      = 3 * Real.sqrt 37 := by norm_num
  have hR : 4 * (((2 : ℝ) ^ 2 * (((1009 : ℕ).divisors.card : ℝ)) / (1009 : ℝ)) + (2 : ℝ))
      * (((37 : ℕ).divisors.card : ℝ)) = 16 + 64 / 1009 := by
    rw [(by norm_num : Nat.Prime 1009).divisors, (by norm_num : Nat.Prime 37).divisors]
    norm_num
  rw [ht1, ht2, hR] at h
  have h1 : 3 * Real.sqrt 37 ≤ 15 + 62 / 1009 := by linarith
  have h3 : (3 * Real.sqrt 37) ^ 2 ≤ (15 + 62 / 1009) ^ 2 := by
    nlinarith [Real.sqrt_nonneg 37]
  rw [mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 37)] at h3
  norm_num at h3

end Work.LinnikBurgess

namespace Work.LinnikBurgess

/-- **Adding `2√m` to the right-hand side does not repair the statement either.**  With
`m = 401 ≤ H = 401`, `d = 1000003` (prime, coprime to `401`) and `a0 = 1`, the term `a1 = a0`
contributes `402·√401 ≈ 8050`, while `4·(401²·τ(d)/d + 401)·τ(401) + 2√401 ≈ 3251`. -/
theorem a1_sum_bound_shift2sqrt_false :
    ¬ ((∑ a1 ∈ Finset.Icc (1 : ℕ) 401,
        (((401 : ℝ) * (Nat.gcd 1000003 (((1 : ℤ) - (a1 : ℤ)).natAbs) : ℝ) / (1000003 : ℝ) + 1)
          * Real.sqrt (((Nat.gcd 401 (((1 : ℤ) - (a1 : ℤ)).natAbs)) : ℕ) : ℝ)))
      ≤ 4 * (((401 : ℝ) ^ 2 * (((1000003 : ℕ).divisors.card : ℝ)) / (1000003 : ℝ)) + (401 : ℝ))
          * (((401 : ℕ).divisors.card : ℝ)) + 2 * Real.sqrt 401) := by
  intro h
  have hnn : ∀ a1 ∈ Finset.Icc (1 : ℕ) 401,
      (0 : ℝ) ≤ (((401 : ℝ) * (Nat.gcd 1000003 (((1 : ℤ) - (a1 : ℤ)).natAbs) : ℝ)
            / (1000003 : ℝ) + 1)
          * Real.sqrt (((Nat.gcd 401 (((1 : ℤ) - (a1 : ℤ)).natAbs)) : ℕ) : ℝ)) := by
    intro a1 _
    positivity
  have hterm : (402 : ℝ) * Real.sqrt 401
      ≤ (∑ a1 ∈ Finset.Icc (1 : ℕ) 401,
        (((401 : ℝ) * (Nat.gcd 1000003 (((1 : ℤ) - (a1 : ℤ)).natAbs) : ℝ) / (1000003 : ℝ) + 1)
          * Real.sqrt (((Nat.gcd 401 (((1 : ℤ) - (a1 : ℤ)).natAbs)) : ℕ) : ℝ))) := by
    have h1 : (1 : ℕ) ∈ Finset.Icc (1 : ℕ) 401 := by simp
    have hs := Finset.single_le_sum hnn h1
    have heq : (((401 : ℝ) * (Nat.gcd 1000003 (((1 : ℤ) - ((1 : ℕ) : ℤ)).natAbs) : ℝ)
            / (1000003 : ℝ) + 1)
          * Real.sqrt (((Nat.gcd 401 (((1 : ℤ) - ((1 : ℕ) : ℤ)).natAbs)) : ℕ) : ℝ))
        = 402 * Real.sqrt 401 := by
      norm_num
    rwa [heq] at hs
  have h20 : (20 : ℝ) ≤ Real.sqrt 401 := by
    rw [Real.le_sqrt (by norm_num) (by norm_num)]
    norm_num
  have h21 : Real.sqrt 401 ≤ 21 := by
    rw [Real.sqrt_le_iff]
    exact ⟨by norm_num, by norm_num⟩
  have hcd : (((1000003 : ℕ).divisors.card : ℝ)) = 2 := by
    rw [(by norm_num : Nat.Prime 1000003).divisors]
    norm_num
  have hcm : (((401 : ℕ).divisors.card : ℝ)) = 2 := by
    rw [(by norm_num : Nat.Prime 401).divisors]
    norm_num
  rw [hcd, hcm] at h
  have hfrac : (401 : ℝ) ^ 2 * 2 / 1000003 < 1 := by norm_num
  have hR : 4 * ((401 : ℝ) ^ 2 * 2 / 1000003 + 401) * 2 + 2 * Real.sqrt 401 < 3258 := by
    nlinarith [h21, Real.sqrt_nonneg 401]
  have h8040 : (8040 : ℝ) ≤ (402 : ℝ) * Real.sqrt 401 := by nlinarith
  linarith

end Work.LinnikBurgess

namespace Work.LinnikBurgess

/-- **Conservative form: no change of range, one explicit extra term.**  For `0 < m`,
`Nat.Coprime m d`, `0 < d` and `1 ≤ a0 ≤ H`, the sum over the *whole* range `[1,H]` is bounded by
the right-hand side of `a1_sum_bound_guarded` plus the single term at `a1 = a0`, which equals
`(H·gcd(d,0)/d + 1)·√gcd(m,0) = (H+1)·√m`.  Use this when the range cannot be filtered. -/
theorem a1_sum_bound_guarded_full {m d H a0 : ℕ} (hm : 0 < m) (hmd : Nat.Coprime m d) (hd : 0 < d)
    (ha0 : 1 ≤ a0) (ha0H : a0 ≤ H) :
    (∑ a1 ∈ Finset.Icc 1 H,
        (((H : ℝ) * (Nat.gcd d (((a0 : ℤ) - (a1 : ℤ)).natAbs) : ℝ) / (d : ℝ) + 1)
          * Real.sqrt (((Nat.gcd m (((a0 : ℤ) - (a1 : ℤ)).natAbs)) : ℕ) : ℝ)))
      ≤ 4 * (((H : ℝ) ^ 2 * ((d.divisors.card : ℝ)) / (d : ℝ)) + (H : ℝ))
          * ((m.divisors.card : ℝ)) + ((H : ℝ) + 1) * Real.sqrt m := by
  have hmain := a1_sum_bound_guarded (m := m) (d := d) (H := H) (a0 := a0) hm hmd hd ha0 ha0H
  have hlast : (((H : ℝ) * (Nat.gcd d (a1Shift a0 a0) : ℝ) / (d : ℝ) + 1)
        * Real.sqrt (((Nat.gcd m (a1Shift a0 a0)) : ℕ) : ℝ)) = ((H : ℝ) + 1) * Real.sqrt m := by
    have hd0 : Nat.gcd d (a1Shift a0 a0) = d := by simp [a1Shift]
    have hm0 : Nat.gcd m (a1Shift a0 a0) = m := by simp [a1Shift]
    rw [hd0, hm0]
    have hdR : (d : ℝ) ≠ 0 := by positivity
    have hdiv : (H : ℝ) * (d : ℝ) / (d : ℝ) = (H : ℝ) := by
      field_simp
    rw [hdiv]
  have hsplit : (∑ a1 ∈ Finset.Icc 1 H,
        (((H : ℝ) * (Nat.gcd d (((a0 : ℤ) - (a1 : ℤ)).natAbs) : ℝ) / (d : ℝ) + 1)
          * Real.sqrt (((Nat.gcd m (((a0 : ℤ) - (a1 : ℤ)).natAbs)) : ℕ) : ℝ)))
      = (∑ a1 ∈ a1Idx a0 H,
          (((H : ℝ) * (Nat.gcd d (a1Shift a0 a1) : ℝ) / (d : ℝ) + 1)
            * Real.sqrt (((Nat.gcd m (a1Shift a0 a1)) : ℕ) : ℝ)))
        + (((H : ℝ) * (Nat.gcd d (a1Shift a0 a0) : ℝ) / (d : ℝ) + 1)
            * Real.sqrt (((Nat.gcd m (a1Shift a0 a0)) : ℕ) : ℝ)) := by
    have h := Finset.sum_filter_add_sum_filter_not (Finset.Icc 1 H) (fun a1 => a1 ≠ a0)
      (fun a1 => (((H : ℝ) * (Nat.gcd d (a1Shift a0 a1) : ℝ) / (d : ℝ) + 1)
            * Real.sqrt (((Nat.gcd m (a1Shift a0 a1)) : ℕ) : ℝ)))
    have hfilter : (Finset.Icc 1 H).filter (fun a1 => ¬ a1 ≠ a0) = {a0} := by
      have h1 : (Finset.Icc 1 H).filter (fun a1 => ¬ a1 ≠ a0)
          = (Finset.Icc 1 H).filter (fun a1 => a1 = a0) := by
        refine Finset.filter_congr ?_
        intro x _
        simp
      rw [h1, Finset.filter_eq']
      rw [if_pos]
      exact Finset.mem_Icc.mpr ⟨ha0, ha0H⟩
    rw [hfilter, Finset.sum_singleton] at h
    exact h.symm
  rw [hsplit, hlast]
  exact add_le_add hmain le_rfl

end Work.LinnikBurgess

namespace Work.LinnikBurgess

/-! ### The weight form of the `a1`-sum (companion of `a2_sum_bound`) -/

/-- **The `a1`-sum, weight form.**  For `0 < m`, `Nat.Coprime m d`, `0 < d` and a pivot
`a0 ∈ [1,H]`, the sum over `a1 ∈ [1,H]`, `a1 ≠ a0`, of
`gcd(m,|a0-a1|)·(H/d·gcd(d,|a0-a1|) + 1)` is at most `2·(H²·τ(d)/d + H)·τ(m)`.

This is the exact `a1`-companion of `a2_sum_bound` for the same family of sums: same weight
(the `√`-free form `gcd(m,·)`), same hypotheses (anchoring `a0 ∈ [1,H]` plus the guard
`a1 ≠ a0`) and the same constant `2`.  The `√`-weighted form `a1_sum_bound_guarded` follows from
it pointwise (`√x ≤ x` for `x ≥ 1`), with constant `4`.

Proof: `gcd(m,c)·(H·gcd(d,c)/d + 1) = H/d·gcd(m,c)·gcd(d,c) + gcd(m,c)`; each half is a
divisor-counting estimate (`gcd(m,c)·gcd(d,c) ≤ gcd(d·m, c)` since `Nat.Coprime m d`), namely
`∑_{a1 ≠ a0} gcd(N,c) ≤ H·τ(N)` (`sum_gcd_core`) with `N = d·m` and `N = m`, together with
`τ(d·m) ≤ τ(d)·τ(m)`. -/
theorem a1_sum_bound_weight {m d H : ℕ} (hm : 0 < m) (hmd : Nat.Coprime m d) (hd : 0 < d)
    (a0 : ℕ) (ha0 : a0 ∈ Finset.Icc 1 H) :
    (∑ a1 ∈ (Finset.Icc 1 H).filter (fun a1 => a1 ≠ a0),
        ((Nat.gcd m (((a0 : ℤ) - (a1 : ℤ)).natAbs) : ℝ)
          * ((H : ℝ) * (Nat.gcd d (((a0 : ℤ) - (a1 : ℤ)).natAbs) : ℝ) / (d : ℝ) + 1)))
      ≤ 2 * (((H : ℝ) ^ 2 * ((d.divisors.card : ℝ)) / (d : ℝ)) + (H : ℝ))
          * ((m.divisors.card : ℝ)) := by
  obtain ⟨ha01, ha0H⟩ := Finset.mem_Icc.mp ha0
  have hdm : 0 < d * m := Nat.mul_pos hd hm
  have hsplit : (∑ a1 ∈ a1Idx a0 H,
        ((Nat.gcd m (a1Shift a0 a1) : ℝ)
          * ((H : ℝ) * (Nat.gcd d (a1Shift a0 a1) : ℝ) / (d : ℝ) + 1)))
      = (H : ℝ) / (d : ℝ) * (∑ a1 ∈ a1Idx a0 H,
            ((Nat.gcd m (a1Shift a0 a1) : ℝ) * (Nat.gcd d (a1Shift a0 a1) : ℝ)))
        + ∑ a1 ∈ a1Idx a0 H, ((Nat.gcd m (a1Shift a0 a1) : ℝ)) := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun a1 _ => ?_)
    ring
  have hA : (∑ a1 ∈ a1Idx a0 H,
        ((Nat.gcd m (a1Shift a0 a1) : ℝ) * (Nat.gcd d (a1Shift a0 a1) : ℝ)))
      ≤ (H : ℝ) * (((d * m).divisors.card : ℝ)) := by
    refine le_trans (Finset.sum_le_sum (fun a1 _ => ?_))
      (sum_gcd_core (d * m) a0 H hdm ha01 ha0H)
    have hle : Nat.gcd m (a1Shift a0 a1) * Nat.gcd d (a1Shift a0 a1)
        ≤ Nat.gcd (d * m) (a1Shift a0 a1) := by
      rw [Nat.mul_comm]
      exact Nat.le_of_dvd (Nat.gcd_pos_of_pos_left _ hdm)
        (gcd_mul_gcd_dvd (k := a1Shift a0 a1) hm hd hmd.symm)
    exact_mod_cast hle
  have hB := sum_gcd_core m a0 H hm ha01 ha0H
  have hτdm : (((d * m).divisors.card : ℕ) : ℝ)
      ≤ ((d.divisors.card : ℕ) : ℝ) * ((m.divisors.card : ℕ) : ℝ) := by
    have := card_divisors_mul_le d m
    exact_mod_cast this
  have hH : (0 : ℝ) ≤ (H : ℝ) := by positivity
  have hτm : (0 : ℝ) ≤ ((m.divisors.card : ℝ)) := by positivity
  have hτd : (0 : ℝ) ≤ ((d.divisors.card : ℝ)) := by positivity
  calc (∑ a1 ∈ (Finset.Icc 1 H).filter (fun a1 => a1 ≠ a0),
        ((Nat.gcd m (((a0 : ℤ) - (a1 : ℤ)).natAbs) : ℝ)
          * ((H : ℝ) * (Nat.gcd d (((a0 : ℤ) - (a1 : ℤ)).natAbs) : ℝ) / (d : ℝ) + 1)))
      = (H : ℝ) / (d : ℝ) * (∑ a1 ∈ a1Idx a0 H,
            ((Nat.gcd m (a1Shift a0 a1) : ℝ) * (Nat.gcd d (a1Shift a0 a1) : ℝ)))
        + ∑ a1 ∈ a1Idx a0 H, ((Nat.gcd m (a1Shift a0 a1) : ℝ)) := hsplit
    _ ≤ (H : ℝ) / (d : ℝ) * ((H : ℝ) * (((d * m).divisors.card : ℝ))) + (H : ℝ) * ((m.divisors.card : ℝ)) := by
        refine add_le_add (mul_le_mul_of_nonneg_left hA (by positivity)) hB
    _ ≤ (H : ℝ) / (d : ℝ) * ((H : ℝ) * (((d.divisors.card : ℝ)) * ((m.divisors.card : ℝ))))
          + (H : ℝ) * ((m.divisors.card : ℝ)) := by
        have h1 : (H : ℝ) * (((d * m).divisors.card : ℕ) : ℝ)
            ≤ (H : ℝ) * (((d.divisors.card : ℕ) : ℝ) * ((m.divisors.card : ℕ) : ℝ)) :=
          mul_le_mul_of_nonneg_left hτdm hH
        have h2 := mul_le_mul_of_nonneg_left h1 (by positivity : (0 : ℝ) ≤ (H : ℝ) / (d : ℝ))
        linarith
    _ = (((H : ℝ) ^ 2 * ((d.divisors.card : ℝ)) / (d : ℝ)) + (H : ℝ)) * ((m.divisors.card : ℝ)) := by
        ring
    _ ≤ 2 * (((H : ℝ) ^ 2 * ((d.divisors.card : ℝ)) / (d : ℝ)) + (H : ℝ))
          * ((m.divisors.card : ℝ)) := by
        have hX : (0 : ℝ) ≤ (((H : ℝ) ^ 2 * ((d.divisors.card : ℝ)) / (d : ℝ)) + (H : ℝ))
            * ((m.divisors.card : ℝ)) := by positivity
        linarith

end Work.LinnikBurgess
