import Mathlib
import Submission.Commons.NumberTheory.FriedlanderIwaniec.sq_sum_sq_root_count_prime_pow
import Submission.Commons.NumberTheory.FriedlanderIwaniec.two_pow_card_primeFactors_le_card_divisors
import Submission.Commons.NumberTheory.FriedlanderIwaniec.tau_le_nine_sum_divisors_cube
import Submission.Commons.NumberTheory.DivisorBound.card_divisors_le_rpow
import Submission.Commons.NumberTheory.Diophantine.ncard_primitive_sq_add_mul_sq_le

namespace Commons.NumberTheory.Int

open Finset
open Commons.NumberTheory.FriedlanderIwaniec (pow_dvd_sq_iff card_filter_range_dvd card_filter_range_mod)

/-!
## Counting representations by `a * x ^ 2 + b * y ^ 2`

For fixed positive integers `a`, `b`, the number of integer solutions of
`a * x ^ 2 + b * y ^ 2 = n` is `O_ε (n ^ ε)` for every `ε > 0`.

The strategy is:

* the map `(x, y) ↦ (a * x, y)` is an injection from the solutions of
  `a * x ^ 2 + b * y ^ 2 = n` into the solutions of `X ^ 2 + D * Y ^ 2 = a * n`
  with `D = a * b`;
* decompose the solutions of `X ^ 2 + D * Y ^ 2 = M` according to `g = gcd (X, Y)`:
  the reduced pair `(X / g, Y / g)` is a *primitive* solution of
  `X ^ 2 + D * Y ^ 2 = M / g ^ 2`, and `g ^ 2 ∣ M`;
* a primitive solution of `X ^ 2 + D * Y ^ 2 = M'` has `Y` invertible modulo `M'`
  and produces the square root `X * Y⁻¹` of `-D` modulo `M'`; at most `4` primitive
  solutions yield the same root (this is the shared lemma
  `Commons.NumberTheory.Diophantine.ncard_primitive_sq_add_mul_sq_le`);
* the number of square roots of `-D` modulo `M'` is at most `D * d (M') ^ 3`, proved
  below by a Chinese-remainder reduction to prime powers and Hensel-type estimates;
* finally `d (a * n) ≤ d a * d n` and `d n ^ 4 ≪_ε n ^ ε`.

`PpR p α N` denotes the number of roots of `X ^ 2 + N` modulo `p ^ α`, i.e. the
number of `r < p ^ α` with `p ^ α ∣ r ^ 2 + N`.
-/

open Finset

private lemma zmod_sq_eq_neg_natCast_iff {n D r : ℕ} [NeZero n] :
    ((r : ZMod n) ^ 2 = -((D : ℕ) : ZMod n)) ↔ n ∣ r ^ 2 + D := by
  rw [eq_neg_iff_add_eq_zero, ← Nat.cast_pow, ← Nat.cast_add, ZMod.natCast_eq_zero_iff]

private lemma ncard_zmod_sq_eq_neg_range {n D : ℕ} [NeZero n] :
    ({α : ZMod n | α ^ 2 = -((D : ℕ) : ZMod n)}).ncard
      = ((Finset.range n).filter (fun r => n ∣ r ^ 2 + D)).card := by
  rw [Commons.NumberTheory.FriedlanderIwaniec.ncard_zmod_eq_range (n := n)
    (ψ := fun α : ZMod n => α ^ 2 = -((D : ℕ) : ZMod n))]
  exact congrArg Finset.card (Finset.filter_congr
    (fun r _ => zmod_sq_eq_neg_natCast_iff (n := n) (D := D) (r := r)))

private lemma dvd_or_dvd_of_not_dvd_gcd {p α a b : ℕ} (hp : p.Prime)
    (hab : p ^ α ∣ a * b) (hg : ¬ p ∣ a.gcd b) : p ^ α ∣ a ∨ p ^ α ∣ b := by
  by_cases hpa : p ∣ a
  · left
    have hpb : ¬ p ∣ b := fun hpb => hg (Nat.dvd_gcd hpa hpb)
    exact (Nat.Coprime.pow_left α (hp.coprime_iff_not_dvd.mpr hpb)).dvd_of_dvd_mul_right hab
  · right
    exact (Nat.Coprime.pow_left α (hp.coprime_iff_not_dvd.mpr hpa)).dvd_of_dvd_mul_left hab

private lemma PpR_le_two_of_not_dvd {p α D : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hpd : ¬ p ∣ D) (hα : 1 ≤ α) :
    ((Finset.range (p ^ α)).filter (fun r => p ^ α ∣ r ^ 2 + D)).card ≤ 2 := by
  classical
  have hp0 : 0 < p := hp.pos
  have hpodd : ¬ ((p:ℤ) ∣ 2) := by
    intro h
    have h1 : p ∣ 2 := by
      have := Int.natAbs_dvd_natAbs.mpr h
      simpa using this
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h1)
  set S := (Finset.range (p ^ α)).filter (fun r => p ^ α ∣ r ^ 2 + D) with hS
  rcases S.eq_empty_or_nonempty with hemp | ⟨r₀, hr₀⟩
  · rw [hemp]; simp
  · have hr₀mem := hr₀
    rw [hS, Finset.mem_filter, Finset.mem_range] at hr₀mem
    obtain ⟨hr₀lt, hr₀d⟩ := hr₀mem
    have hsub : S ⊆ ({r₀, p ^ α - r₀} : Finset ℕ) := by
      intro r hr
      rw [hS, Finset.mem_filter, Finset.mem_range] at hr
      obtain ⟨hrlt, hrd⟩ := hr
      have hrdZ : (p:ℤ)^α ∣ (r:ℤ)^2 + (D:ℤ) := by
        have h : ((p ^ α : ℕ) : ℤ) ∣ ((r ^ 2 + D : ℕ) : ℤ) := by exact_mod_cast hrd
        push_cast at h ⊢
        exact h
      have hr₀dZ : (p:ℤ)^α ∣ (r₀:ℤ)^2 + (D:ℤ) := by
        have h : ((p ^ α : ℕ) : ℤ) ∣ ((r₀ ^ 2 + D : ℕ) : ℤ) := by exact_mod_cast hr₀d
        push_cast at h ⊢
        exact h
      have hprodZ : (p:ℤ)^α ∣ ((r:ℤ) - r₀) * ((r:ℤ) + r₀) := by
        have h1 : ((r:ℤ)^2 + (D:ℤ)) - ((r₀:ℤ)^2 + (D:ℤ))
            = ((r:ℤ) - r₀) * ((r:ℤ) + r₀) := by ring
        rw [← h1]
        exact Int.dvd_sub hrdZ hr₀dZ
      have hprodN : p^α ∣ (((r:ℤ) - r₀).natAbs) * (r + r₀) := by
        have h2 : ((p:ℤ)^α).natAbs ∣ ((((r:ℤ) - r₀) * ((r:ℤ) + r₀)).natAbs) :=
          Int.natAbs_dvd_natAbs.mpr hprodZ
        rw [Int.natAbs_pow, Int.natAbs_natCast, Int.natAbs_mul] at h2
        have hb : ((r:ℤ) + r₀).natAbs = r + r₀ := by
          have h : ((r:ℤ) + r₀) = ((r + r₀ : ℕ) : ℤ) := by push_cast; ring
          rw [h, Int.natAbs_natCast]
        rw [hb] at h2
        exact h2
      have hgcdnot : ¬ p ∣ (((r:ℤ) - r₀).natAbs).gcd (r + r₀) := by
        intro hg
        have h1 : p ∣ (((r:ℤ) - r₀).natAbs) := Nat.dvd_trans hg (Nat.gcd_dvd_left _ _)
        have h2 : p ∣ r + r₀ := Nat.dvd_trans hg (Nat.gcd_dvd_right _ _)
        have h1Z : (p:ℤ) ∣ ((r:ℤ) - r₀) := by
          have h := Int.ofNat_dvd.mpr h1
          rwa [Int.dvd_natAbs] at h
        have h2Z : (p:ℤ) ∣ ((r:ℤ) + r₀) := by
          have h := Int.ofNat_dvd.mpr h2
          push_cast at h
          exact h
        have h3 : (p:ℤ) ∣ 2 * (r:ℤ) := by
          have h := Int.dvd_add h1Z h2Z
          convert h using 1
          ring
        have hpz : Prime (p:ℤ) := by rw [Int.prime_iff_natAbs_prime]; simpa using hp
        rcases hpz.dvd_mul.mp h3 with h4 | h4
        · exact hpodd h4
        · have h5 : p ∣ r := Int.ofNat_dvd.mp (by simpa using h4)
          have h6 : p ∣ r ^ 2 := by
            obtain ⟨t, ht⟩ := h5
            exact ⟨t * r, by rw [ht]; ring⟩
          have h7 : p ∣ r ^ 2 + D :=
            dvd_trans (by simpa using (pow_dvd_pow p hα : p^1 ∣ p^α)) hrd
          have h8 : p ∣ D := by
            have := Nat.dvd_sub h7 h6
            rwa [Nat.add_sub_cancel_left] at this
          exact hpd h8
      rcases dvd_or_dvd_of_not_dvd_gcd hp hprodN hgcdnot with h | h
      · have hlt : ((r:ℤ) - r₀).natAbs < p^α := by
          rcases le_total r₀ r with hle | hle
          · have he : ((r:ℤ) - r₀).natAbs = r - r₀ := by
              have h1 : (r:ℤ) - r₀ = ((r - r₀ : ℕ) : ℤ) := by omega
              rw [h1, Int.natAbs_natCast]
            omega
          · have he : ((r:ℤ) - r₀).natAbs = r₀ - r := by
              have h1 : (r:ℤ) - r₀ = -((r₀ - r : ℕ) : ℤ) := by omega
              rw [h1, Int.natAbs_neg, Int.natAbs_natCast]
            omega
        have hzero := Nat.eq_zero_of_dvd_of_lt h hlt
        have hz : (r:ℤ) - r₀ = 0 := Int.natAbs_eq_zero.mp hzero
        have : r = r₀ := by omega
        exact Finset.mem_insert.mpr (Or.inl this)
      · have hlt : r + r₀ < 2 * p^α := by omega
        obtain ⟨k, hk⟩ := h
        have hk2 : k < 2 := by
          by_contra hk2
          push Not at hk2
          have hk2' : 2 * p^α ≤ r + r₀ := by
            calc 2 * p^α ≤ k * p^α := Nat.mul_le_mul_right _ hk2
              _ = p^α * k := Nat.mul_comm _ _
              _ = r + r₀ := hk.symm
          omega
        interval_cases k
        · have : r = r₀ := by omega
          exact Finset.mem_insert.mpr (Or.inl this)
        · have : r = p^α - r₀ := by omega
          exact Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton.mpr this))
    calc S.card ≤ ({r₀, p ^ α - r₀} : Finset ℕ).card := Finset.card_le_card hsub
      _ ≤ 2 := Finset.card_le_two


open Finset

private lemma mod_two_eq_zero_or_one' (n : ℕ) : n % 2 = 0 ∨ n % 2 = 1 := by omega

/-- If `2^α ∣ u * w`, `4 ∣ u`, `2 ∣ w` and `4 ∤ w`, then `2^(α-1) ∣ u`. -/
private lemma two_pow_dvd_left_of {α u w : ℕ} (hα : 3 ≤ α) (h : 2^α ∣ u * w)
    (hu : 4 ∣ u) (hw2 : 2 ∣ w) (hw4 : ¬ 4 ∣ w) : 2^(α-1) ∣ u := by
  obtain ⟨d, hd⟩ := hu
  obtain ⟨c, hc⟩ := hw2
  have hcodd : ¬ 2 ∣ c := by
    intro hc2
    apply hw4
    obtain ⟨e, he⟩ := hc2
    exact ⟨e, by rw [hc, he]; ring⟩
  have h2 : 2^α ∣ 2^3 * (d * c) := by
    rw [hd, hc] at h
    convert h using 1
    ring
  have h3 : 2^(α-1) ∣ 4 * d := by
    have hp : 2^α = 2^3 * 2^(α-3) := by rw [← pow_add]; congr 1; omega
    rw [hp] at h2
    have h4 : 2^(α-3) ∣ d * c := (Nat.mul_dvd_mul_iff_left (by norm_num : 0 < 2^3)).mp h2
    have h5 : 2^(α-3) ∣ d :=
      (Nat.Coprime.pow_left _ (Nat.prime_two.coprime_iff_not_dvd.mpr hcodd)).dvd_of_dvd_mul_right h4
    have hp2 : 2^(α-1) = 4 * 2^(α-3) := by
      rw [show (4:ℕ) = 2^2 by norm_num, ← pow_add]; congr 1; omega
    rw [hp2]
    exact mul_dvd_mul_left 4 h5
  rwa [hd]

private lemma card_three_le (a b c : ℕ) : ({a, b, c} : Finset ℕ).card ≤ 3 := by
  have h1 := Finset.card_insert_le a ({b, c} : Finset ℕ)
  have h2 := Finset.card_insert_le b ({c} : Finset ℕ)
  have h3 : ({c} : Finset ℕ).card = 1 := Finset.card_singleton c
  omega

private lemma two_dvd_two_pow' {α : ℕ} (hα : 1 ≤ α) : (2:ℕ) ∣ 2^α := by
  simpa using (pow_dvd_pow 2 hα : (2:ℕ)^1 ∣ 2^α)

private lemma four_dvd_two_pow' {α : ℕ} (hα : 2 ≤ α) : (4:ℕ) ∣ 2^α := by
  have := pow_dvd_pow 2 hα
  simpa using (this : (2:ℕ)^2 ∣ 2^α)

private lemma two_odd_odd' {r r' : ℕ} (hr : r % 2 = 1) (hr' : r' % 2 = 1) : (r + r') % 2 = 0 := by omega
private lemma mod_four_of_mod_four' {r r' : ℕ} (h : r % 4 = r' % 4) (hr : r % 2 = 1) :
    (r + r') % 4 = 2 := by omega

private lemma odd_of_root {D r : ℕ} (hDodd : D % 2 = 1) (hr : 2 ∣ r^2 + D) : r % 2 = 1 := by
  rcases mod_two_eq_zero_or_one' r with h | h
  · exfalso
    have h3 : (r^2 + D) % 2 = 0 := Nat.dvd_iff_mod_eq_zero.mp hr
    have hr2dvd : 2 ∣ r^2 := by
      obtain ⟨k, hk⟩ := Nat.dvd_of_mod_eq_zero h
      exact ⟨2*k*k, by rw [hk]; ring⟩
    have h4 : r^2 % 2 = 0 := Nat.dvd_iff_mod_eq_zero.mp hr2dvd
    have h5 : (r^2 + D) % 2 = (r^2 % 2 + D % 2) % 2 := Nat.add_mod _ _ _
    rw [h4, hDodd] at h5
    norm_num at h5
    rw [h5] at h3
    norm_num at h3
  · exact h

/-- For two roots `r > r'` of `X^2 + D` modulo `2^α` (with `D` odd, `α ≥ 3`) that
are congruent modulo `4`, one has `r - r' = 2 ^ (α - 1)`. -/
private lemma sub_eq_two_pow_of {α D r r' : ℕ} (hα : 3 ≤ α) (hDodd : D % 2 = 1)
    (hr : 2^α ∣ r^2 + D) (hr' : 2^α ∣ r'^2 + D) (hmod : r % 4 = r' % 4)
    (hgt : r' < r) (hrlt : r < 2^α) : r - r' = 2^(α-1) := by
  have hrodd : r % 2 = 1 := odd_of_root hDodd (dvd_trans (two_dvd_two_pow' (by omega)) hr)
  have hr'odd : r' % 2 = 1 := odd_of_root hDodd (dvd_trans (two_dvd_two_pow' (by omega)) hr')
  have hle : r'^2 ≤ r^2 := Nat.pow_le_pow_left (le_of_lt hgt) 2
  have hdiff : 2^α ∣ (r - r') * (r + r') := by
    have h := Nat.dvd_sub hr hr'
    have heq : (r^2 + D) - (r'^2 + D) = (r - r') * (r + r') := by
      have h1 : (r^2 + D) - (r'^2 + D) = r^2 - r'^2 := by omega
      rw [h1, Nat.sq_sub_sq, mul_comm]
    rwa [heq] at h
  have h4 : 4 ∣ r - r' := Nat.dvd_of_mod_eq_zero (Nat.sub_mod_eq_zero_of_mod_eq hmod)
  have h2w : 2 ∣ r + r' := Nat.dvd_of_mod_eq_zero (two_odd_odd' hrodd hr'odd)
  have h4w : ¬ 4 ∣ r + r' := by
    intro h
    have hmm : (r + r') % 4 = 2 := mod_four_of_mod_four' hmod hrodd
    rw [Nat.dvd_iff_mod_eq_zero] at h
    omega
  have hdvd : 2^(α-1) ∣ r - r' := two_pow_dvd_left_of hα hdiff h4 h2w h4w
  have hlt : r - r' < 2^α := by omega
  have hpos : 0 < r - r' := by omega
  have h2α : 2^(α-1) * 2 = 2^α := by
    rw [← pow_succ]
    congr 1
    omega
  obtain ⟨m, hm⟩ := hdvd
  have h1 : 0 < 2^(α-1) := pow_pos (by norm_num) _
  have hmlt : m < 2 := by
    have : 2^(α-1) * m < 2^(α-1) * 2 := by rw [← hm, h2α]; exact hlt
    exact (Nat.mul_lt_mul_left h1).mp this
  have hmpos : 0 < m := by
    have : 0 < 2^(α-1) * m := by rw [← hm]; exact hpos
    rcases Nat.eq_zero_or_pos m with h0 | h0
    · rw [h0, mul_zero] at this; omega
    · exact h0
  have hm1 : m = 1 := by omega
  rw [hm, hm1, mul_one]

private lemma PpR_two_le_eight {α D : ℕ} (hD : ¬ 2 ∣ D) (hα : 1 ≤ α) :
    ((Finset.range (2^α)).filter (fun r => 2^α ∣ r^2 + D)).card ≤ 8 := by
  classical
  have hDodd : D % 2 = 1 := by
    rcases mod_two_eq_zero_or_one' D with h | h
    · exact absurd (Nat.dvd_of_mod_eq_zero h) hD
    · exact h
  by_cases hα2 : α ≤ 2
  · have h1 : ((Finset.range (2^α)).filter (fun r => 2^α ∣ r^2 + D)).card ≤ 2^α := by
      calc _ ≤ (Finset.range (2^α)).card := Finset.card_filter_le _ _
        _ = 2^α := Finset.card_range _
    have h2 : 2^α ≤ 4 := by
      calc 2^α ≤ 2^2 := Nat.pow_le_pow_right (by norm_num) hα2
        _ = 4 := by norm_num
    omega
  · push Not at hα2
    set S := (Finset.range (2^α)).filter (fun r => 2^α ∣ r^2 + D) with hS
    have hroot : ∀ r ∈ S, 2^α ∣ r^2 + D := by
      intro r hr; rw [hS, Finset.mem_filter] at hr; exact hr.2
    have hrlt : ∀ r ∈ S, r < 2^α := by
      intro r hr; rw [hS, Finset.mem_filter] at hr; exact Finset.mem_range.mp hr.1
    set T := (Finset.range 4).filter (fun c => 4 ∣ c^2 + D) with hT
    have hTsub : T ⊆ ({1, 3} : Finset ℕ) := by
      intro c hc
      rw [hT, Finset.mem_filter, Finset.mem_range] at hc
      obtain ⟨hc4, hcd⟩ := hc
      have hcodd : c % 2 = 1 := odd_of_root hDodd (dvd_trans (by norm_num : (2:ℕ) ∣ 4) hcd)
      have : c = 1 ∨ c = 3 := by omega
      rcases this with h | h <;> rw [h] <;> simp
    have hTcard : T.card ≤ 2 := by
      calc T.card ≤ ({1,3} : Finset ℕ).card := Finset.card_le_card hTsub
        _ ≤ 2 := Finset.card_le_two
    have hmaps : ∀ r ∈ S, r % 4 ∈ T := by
      intro r hr
      have h2 : 2^α ∣ r^2 + D := hroot r hr
      have h4 : 4 ∣ r^2 + D := dvd_trans (four_dvd_two_pow' (by omega)) h2
      rw [hT, Finset.mem_filter, Finset.mem_range]
      refine ⟨by omega, ?_⟩
      have hcong : r^2 ≡ (r % 4)^2 [MOD 4] := Nat.ModEq.pow 2 (Nat.mod_modEq r 4).symm
      have h0 : (r^2 + D) % 4 = 0 := Nat.dvd_iff_mod_eq_zero.mp h4
      have hh : (r^2 + D) % 4 = ((r%4)^2 + D) % 4 := hcong.add (Nat.ModEq.refl D)
      rw [hh] at h0
      rwa [Nat.dvd_iff_mod_eq_zero]
    have hfiber : ∀ c ∈ T, (S.filter (fun r => r % 4 = c)).card ≤ 3 := by
      intro c hc
      rcases (S.filter (fun r => r % 4 = c)).eq_empty_or_nonempty with hemp | ⟨r₁, hr₁⟩
      · rw [hemp]; simp
      · have hr₁m := hr₁
        rw [Finset.mem_filter] at hr₁m
        obtain ⟨hr₁S, hr₁c⟩ := hr₁m
        have hsub : (S.filter (fun r => r % 4 = c))
            ⊆ ({r₁ - 2^(α-1), r₁, r₁ + 2^(α-1)} : Finset ℕ) := by
          intro r hr
          rw [Finset.mem_filter] at hr
          obtain ⟨hrS, hrc⟩ := hr
          have hmod : r % 4 = r₁ % 4 := by rw [hrc, hr₁c]
          rcases eq_or_ne r r₁ with h | h
          · exact Finset.mem_insert.mpr (Or.inr (Finset.mem_insert.mpr (Or.inl h)))
          · rcases lt_or_gt_of_ne h with hlt | hgt
            · have h2 : r₁ - r = 2^(α-1) := sub_eq_two_pow_of hα2 hDodd (hroot r₁ hr₁S)
                (hroot r hrS) hmod.symm hlt (hrlt r₁ hr₁S)
              have : r = r₁ - 2^(α-1) := by omega
              rw [this]
              exact Finset.mem_insert.mpr (Or.inl rfl)
            · have h2 : r - r₁ = 2^(α-1) := sub_eq_two_pow_of hα2 hDodd (hroot r hrS)
                (hroot r₁ hr₁S) hmod hgt (hrlt r hrS)
              have : r = r₁ + 2^(α-1) := by omega
              rw [this]
              exact Finset.mem_insert.mpr
                (Or.inr (Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton.mpr rfl))))
        calc (S.filter (fun r => r % 4 = c)).card
            ≤ ({r₁ - 2^(α-1), r₁, r₁ + 2^(α-1)} : Finset ℕ).card := Finset.card_le_card hsub
          _ ≤ 3 := card_three_le _ _ _
    have hmain := Finset.card_le_mul_card_image_of_maps_to (s := S) (t := T)
      (f := fun r => r % 4) hmaps 3 hfiber
    calc S.card ≤ 3 * T.card := hmain
      _ ≤ 3 * 2 := Nat.mul_le_mul_left 3 hTcard
      _ ≤ 8 := by norm_num


open Finset
open Commons.NumberTheory.FriedlanderIwaniec (pow_dvd_sq_iff card_filter_range_dvd card_filter_range_mod)

/-- Roots of `X^2 + p^β * D₀` modulo `p^α` (with `p ∤ D₀`) number at most `8 * p^β`. -/
private lemma PpR_dvd_le {p α β D₀ : ℕ} (hp : p.Prime) (hD₀ : ¬ p ∣ D₀) (hβ : 1 ≤ β)
    (hα : 1 ≤ α) :
    ((Finset.range (p^α)).filter (fun r => p^α ∣ r^2 + p^β * D₀)).card ≤ 8 * p^β := by
  classical
  have hp0 : 0 < p := hp.pos
  by_cases hcase : α ≤ β
  · have hdvd : p^α ∣ p^β * D₀ := dvd_mul_of_dvd_left (Nat.pow_dvd_pow p hcase) D₀
    have hsub : ((Finset.range (p^α)).filter (fun r => p^α ∣ r^2 + p^β * D₀))
        ⊆ (Finset.range (p^α)).filter (fun r => p^α ∣ r^2) := by
      intro r hr
      rw [Finset.mem_filter] at hr ⊢
      exact ⟨hr.1, by
        have h := Nat.dvd_sub hr.2 hdvd
        convert h using 1
        omega⟩
    have hcard : ((Finset.range (p^α)).filter (fun r => p^α ∣ r^2)).card ≤ p^β := by
      have heq : ((Finset.range (p^α)).filter (fun r => p^α ∣ r^2))
          = ((Finset.range (p^α)).filter (fun r => p^((α+1)/2) ∣ r)) := by
        apply Finset.filter_congr
        intro r _
        exact pow_dvd_sq_iff p α r hp
      rw [heq, card_filter_range_dvd (p^α) (p^((α+1)/2)) (pow_pos hp0 _)
        (Nat.pow_dvd_pow p (by omega))]
      rw [Nat.pow_div (by omega : (α+1)/2 ≤ α) hp0]
      have : α - (α+1)/2 = α/2 := by omega
      rw [this]
      exact le_trans (Nat.pow_le_pow_right hp0 (by omega)) (Nat.pow_le_pow_right hp0 hcase)
    calc _ ≤ ((Finset.range (p^α)).filter (fun r => p^α ∣ r^2)).card := Finset.card_le_card hsub
      _ ≤ p^β := hcard
      _ ≤ 8 * p^β := by
          have : 1 ≤ p^β := Nat.one_le_pow _ _ hp0
          nlinarith
  · push Not at hcase
    have hβ1 : β + 1 ≤ α := hcase
    set S := (Finset.range (p^α)).filter (fun r => p^α ∣ r^2 + p^β * D₀) with hS
    rcases S.eq_empty_or_nonempty with hemp | ⟨r₀, hr₀⟩
    · rw [hemp]; simp
    · have hkey : ∀ r ∈ S, p^β ∣ r^2 ∧ ¬ p^(β+1) ∣ r^2 := by
        intro r hr
        rw [hS, Finset.mem_filter] at hr
        obtain ⟨-, hrd⟩ := hr
        have hd1 : p^(β+1) ∣ r^2 + p^β * D₀ := dvd_trans (Nat.pow_dvd_pow p hβ1) hrd
        have h1 : p^β ∣ r^2 := by
          have hd0 : p^β ∣ r^2 + p^β * D₀ :=
            dvd_trans (Nat.pow_dvd_pow p (by omega : β ≤ β + 1)) hd1
          have h := Nat.dvd_sub hd0 (dvd_mul_right (p^β) D₀)
          convert h using 1
          omega
        refine ⟨h1, ?_⟩
        intro h2
        have h3 : p^(β+1) ∣ p^β * D₀ := by
          have h := Nat.dvd_sub hd1 h2
          convert h using 1
          omega
        have h4 : p ∣ D₀ := by
          have h := h3
          rw [pow_succ] at h
          exact (Nat.mul_dvd_mul_iff_left (pow_pos hp0 β)).mp h
        exact hD₀ h4
      have hkey2 : ∀ r ∈ S, p^((β+1)/2) ∣ r ∧ ¬ p^((β+2)/2) ∣ r := by
        intro r hr
        obtain ⟨h1, h2⟩ := hkey r hr
        exact ⟨(pow_dvd_sq_iff p β r hp).mp h1,
          fun h => h2 ((pow_dvd_sq_iff p (β+1) r hp).mpr h)⟩
      have hβeven : (β+2)/2 = (β+1)/2 + 1 := by
        rcases Nat.lt_or_ge ((β+2)/2) ((β+1)/2 + 1) with h | h
        · have hh : (β+2)/2 = (β+1)/2 := by omega
          obtain ⟨hd1, hd2⟩ := hkey2 r₀ hr₀
          rw [hh] at hd2
          exact absurd hd1 hd2
        · omega
      have hdiv : (β+1)/2 = β/2 := by omega
      have hβdvd : ∀ r ∈ S, p^(β/2) ∣ r := by
        intro r hr
        have h := (hkey2 r hr).1
        rwa [hdiv] at h
      set W := (Finset.range (p^(α - β/2))).filter (fun w => p^(α-β) ∣ w^2 + D₀) with hW
      have hmaps : Set.MapsTo (fun r => r / p^(β/2)) ↑S ↑W := by
        intro r hr
        have hbd := hβdvd r hr
        have hrmem : r ∈ S := hr
        rw [hS, Finset.mem_filter] at hrmem
        obtain ⟨hrlt, hrd⟩ := hrmem
        have hrlt' : r < p^α := Finset.mem_range.mp hrlt
        rw [Finset.mem_coe, hW, Finset.mem_filter, Finset.mem_range]
        have hsplit : r = p^(β/2) * (r / p^(β/2)) := (Nat.mul_div_cancel' hbd).symm
        refine ⟨?_, ?_⟩
        · have hp2 : 0 < p^(β/2) := pow_pos hp0 _
          have hlt : p^(β/2) * (r / p^(β/2)) < p^(β/2) * p^(α - β/2) := by
            have h1 : β/2 + (α - β/2) = α := by omega
            rw [← hsplit, ← pow_add, h1]
            exact hrlt'
          exact (Nat.mul_lt_mul_left hp2).mp hlt
        · have hr2 : r^2 = p^β * (r / p^(β/2))^2 := by
            conv_lhs => rw [hsplit]
            rw [mul_pow, ← pow_mul]
            have h1 : β/2 * 2 = β := by omega
            rw [h1]
          have h2 : p^α ∣ p^β * ((r / p^(β/2))^2 + D₀) := by
            rw [hr2, ← mul_add] at hrd
            exact hrd
          have hpab : p^β * p^(α-β) = p^α := by rw [← pow_add]; congr 1; omega
          rw [← hpab] at h2
          exact (Nat.mul_dvd_mul_iff_left (pow_pos hp0 β)).mp h2
      have hinj : Set.InjOn (fun r => r / p^(β/2)) ↑S := by
        intro r hr r' hr' heq
        change r / p^(β/2) = r' / p^(β/2) at heq
        have h1 := hβdvd r hr
        have h2 := hβdvd r' hr'
        have e1 : p^(β/2) * (r / p^(β/2)) = r := Nat.mul_div_cancel' h1
        have e2 : p^(β/2) * (r' / p^(β/2)) = r' := Nat.mul_div_cancel' h2
        rw [← e1, ← e2, heq]
      have hcardW : W.card = p^(β/2) * ((Finset.range (p^(α-β))).filter
          (fun c => p^(α-β) ∣ c^2 + D₀)).card := by
        rw [hW]
        have heq : ((Finset.range (p^(α - β/2))).filter (fun w => p^(α-β) ∣ w^2 + D₀))
            = ((Finset.range (p^(α - β/2))).filter
                (fun w => p^(α-β) ∣ (w % p^(α-β))^2 + D₀)) := by
          apply Finset.filter_congr
          intro w _
          rw [Nat.dvd_iff_mod_eq_zero, Nat.dvd_iff_mod_eq_zero]
          have h1 : w ≡ w % p^(α-β) [MOD p^(α-β)] := (Nat.mod_modEq w _).symm
          have h2 : w^2 ≡ (w % p^(α-β))^2 [MOD p^(α-β)] := Nat.ModEq.pow 2 h1
          have h3 : w^2 + D₀ ≡ (w % p^(α-β))^2 + D₀ [MOD p^(α-β)] :=
            h2.add (Nat.ModEq.refl D₀)
          constructor
          · intro h; rwa [h3] at h
          · intro h; rwa [h3]
        rw [heq]
        rw [card_filter_range_mod (p^(α-β)) (p^(α - β/2)) (pow_pos hp0 _)
          (Nat.pow_dvd_pow p (by omega)) (fun c => p^(α-β) ∣ c^2 + D₀)]
        rw [Nat.pow_div (by omega : α - β ≤ α - β/2) hp0]
        have h1 : α - β/2 - (α - β) = β/2 := by omega
        rw [h1]
      have hbound : ((Finset.range (p^(α-β))).filter (fun c => p^(α-β) ∣ c^2 + D₀)).card ≤ 8 := by
        rcases hp.eq_two_or_odd with h2 | hodd
        · rw [h2] at hD₀ ⊢
          exact PpR_two_le_eight (α := α-β) (D := D₀) hD₀ (by omega)
        · have hp2 : p ≠ 2 := by rintro rfl; omega
          have h2' : ((Finset.range (p^(α-β))).filter (fun r => p^(α-β) ∣ r^2 + D₀)).card ≤ 2 :=
            PpR_le_two_of_not_dvd (α := α-β) (D := D₀) hp hp2 hD₀ (by omega)
          omega
      calc S.card ≤ W.card := Finset.card_le_card_of_injOn _ hmaps hinj
        _ = p^(β/2) * _ := hcardW
        _ ≤ p^(β/2) * 8 := Nat.mul_le_mul_left _ hbound
        _ ≤ 8 * p^β := by
            have h1 : p^(β/2) ≤ p^β := Nat.pow_le_pow_right hp0 (by omega)
            have h2 : 1 ≤ p^(β/2) := Nat.one_le_pow _ _ hp0
            nlinarith


open Finset

private lemma ncard_pi_of_finite {ι : Type*} [Fintype ι] {α : ι → Type*} {s : ∀ i, Set (α i)}
    (h : ∀ i, (s i).Finite) : (Set.pi Set.univ s).ncard = ∏ i, (s i).ncard := by
  have h1 : (∏ i, (s i).encard) = ∏ i, ((s i).ncard : ℕ∞) :=
    Finset.prod_congr rfl (fun i _ => ((h i).cast_ncard_eq).symm)
  rw [Set.ncard_def, Set.encard_pi_eq_prod_encard, h1, ← Nat.cast_prod, ENat.toNat_natCast]

private lemma ringEquiv_image_sq_eq_neg {R S : Type*} [Ring R] [Ring S] (e : R ≃+* S) (c : R) :
    e '' ({r : R | r ^ 2 = -c} : Set R) = {s : S | s ^ 2 = -e c} := by
  ext s
  constructor
  · rintro ⟨r, hr, rfl⟩
    change (e r) ^ 2 = -e c
    rw [← map_pow e r 2, hr, map_neg]
  · intro hs
    change s ^ 2 = -e c at hs
    refine ⟨e.symm s, ?_, e.apply_symm_apply s⟩
    change (e.symm s) ^ 2 = -c
    have h := congrArg e.symm hs
    simp only [map_pow, map_neg, RingEquiv.symm_apply_apply] at h
    exact h

private lemma sq_eq_neg_pi_eq {ι : Type*} [Fintype ι] (a : ι → ℕ) (c : Π i, ZMod (a i)) :
    ({f : Π i, ZMod (a i) | f ^ 2 = -c} : Set (Π i, ZMod (a i)))
      = Set.pi Set.univ (fun i => {α : ZMod (a i) | α ^ 2 = -c i}) := by
  ext f
  constructor
  · intro hf i
    have h := congrFun hf i
    simpa using h
  · intro hf
    funext i
    simpa using hf i

private lemma ncard_sq_eq_neg_pi {ι : Type*} [Fintype ι] (a : ι → ℕ) (c : Π i, ZMod (a i))
    (ha : ∀ i, a i ≠ 0) :
    ({f : Π i, ZMod (a i) | f ^ 2 = -c}.ncard)
      = ∏ i, ({α : ZMod (a i) | α ^ 2 = -c i}.ncard) := by
  rw [sq_eq_neg_pi_eq]
  exact ncard_pi_of_finite (fun i => by
    have : NeZero (a i) := ⟨ha i⟩
    exact Set.toFinite _)

private lemma ncard_sq_eq_neg_prod_factorization {D d : ℕ} (hd : 0 < d) :
    ({α : ZMod d | α ^ 2 = -((D : ℕ) : ZMod d)}).ncard =
      (Nat.primeFactors d).prod (fun p =>
        ({α : ZMod (p ^ d.factorization p) |
            α ^ 2 = -((D : ℕ) : ZMod (p ^ d.factorization p))}).ncard) := by
  classical
  have hd0 : d ≠ 0 := hd.ne'
  let e : ZMod d ≃+* Π p : d.primeFactors, ZMod ((p : ℕ) ^ d.factorization p) :=
    ZMod.equivPi d hd0
  let F : ℕ → ℕ := fun p => ({α : ZMod (p ^ d.factorization p) |
      α ^ 2 = -((D : ℕ) : ZMod (p ^ d.factorization p))}).ncard
  have hc : e (((D : ℕ)) : ZMod d) =
      (fun p : d.primeFactors => ((D : ℕ) : ZMod ((p : ℕ) ^ d.factorization p))) := by
    rw [map_natCast]
    rfl
  calc ({α : ZMod d | α ^ 2 = -((D : ℕ) : ZMod d)}).ncard
      = (e '' ({α : ZMod d | α ^ 2 = -((D : ℕ) : ZMod d)} : Set (ZMod d))).ncard :=
          (Set.ncard_image_of_injective _ e.injective).symm
    _ = ({f : Π p : d.primeFactors, ZMod ((p : ℕ) ^ d.factorization p) |
            f ^ 2 = -(fun p : d.primeFactors =>
              ((D : ℕ) : ZMod ((p : ℕ) ^ d.factorization p)))}.ncard) := by
          rw [ringEquiv_image_sq_eq_neg e (((D : ℕ)) : ZMod d), hc]
    _ = ∏ p : d.primeFactors, F (p : ℕ) :=
          ncard_sq_eq_neg_pi (fun p : d.primeFactors => (p : ℕ) ^ d.factorization p)
            (fun p : d.primeFactors => ((D : ℕ) : ZMod ((p : ℕ) ^ d.factorization p)))
            (fun p => pow_ne_zero _ (Nat.prime_of_mem_primeFactors p.2).ne_zero)
    _ = (Nat.primeFactors d).prod F :=
          Finset.prod_coe_sort (s := d.primeFactors) (f := F)

theorem ncard_sq_eq_neg_le (D M : ℕ) (hD : 1 ≤ D) (hM : 1 ≤ M) :
    ({α : ZMod M | α ^ 2 = -((D : ℕ) : ZMod M)}).ncard ≤ D * (Nat.divisors M).card ^ 3 := by
  classical
  have hM0 : M ≠ 0 := by omega
  have hD0 : D ≠ 0 := by omega
  rw [ncard_sq_eq_neg_prod_factorization (D := D) (d := M) (by omega)]
  have hfac : ∀ p ∈ M.primeFactors,
      ({α : ZMod (p ^ M.factorization p) |
          α ^ 2 = -((D : ℕ) : ZMod (p ^ M.factorization p))}).ncard
        ≤ (if p ∣ D then 8 * p ^ (D.factorization p) else 8) := by
    intro p hp
    have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
    have hα : 1 ≤ M.factorization p :=
      (hpp.dvd_iff_one_le_factorization hM0).mp (Nat.mem_primeFactors.mp hp).2.1
    haveI : NeZero (p ^ M.factorization p) := ⟨pow_ne_zero _ hpp.ne_zero⟩
    have hrange := ncard_zmod_sq_eq_neg_range (n := p ^ M.factorization p) (D := D)
    rw [hrange]
    by_cases hpd : p ∣ D
    · rw [if_pos hpd]
      have hβ : 1 ≤ D.factorization p := (hpp.dvd_iff_one_le_factorization hD0).mp hpd
      have hdvd : p ^ D.factorization p ∣ D :=
        (hpp.pow_dvd_iff_le_factorization hD0).mpr (le_refl _)
      have hsplit : p ^ (D.factorization p) * (D / p ^ (D.factorization p)) = D :=
        Nat.mul_div_cancel' hdvd
      have hnotdvd : ¬ p ∣ D / p ^ (D.factorization p) := by
        intro h2
        have h3 : p ^ (D.factorization p + 1) ∣ D := by
          conv_rhs => rw [← hsplit]
          rw [pow_succ]
          exact mul_dvd_mul_left (p ^ (D.factorization p)) h2
        have h4 := (hpp.pow_dvd_iff_le_factorization hD0).mp h3
        omega
      have hres := PpR_dvd_le (p := p) (α := M.factorization p)
        (β := D.factorization p) (D₀ := D / p ^ (D.factorization p)) hpp hnotdvd hβ hα
      rwa [hsplit] at hres
    · rw [if_neg hpd]
      rcases hpp.eq_two_or_odd with h2 | hodd
      · subst h2
        exact PpR_two_le_eight hpd (by omega)
      · have hp2 : p ≠ 2 := by rintro rfl; omega
        have hres := PpR_le_two_of_not_dvd (p := p) (α := M.factorization p)
          (D := D) hpp hp2 hpd hα
        omega
  have hstep1 : (Nat.primeFactors M).prod (fun p =>
        ({α : ZMod (p ^ M.factorization p) |
            α ^ 2 = -((D : ℕ) : ZMod (p ^ M.factorization p))}).ncard)
      ≤ (Nat.primeFactors M).prod (fun p =>
          (if p ∣ D then 8 * p ^ (D.factorization p) else 8)) :=
    Finset.prod_le_prod (fun p _ => Nat.zero_le _) hfac
  have hstep2 : (Nat.primeFactors M).prod (fun p =>
        (if p ∣ D then 8 * p ^ (D.factorization p) else 8))
      = 8 ^ ((Nat.primeFactors M).filter (fun p => p ∣ D)).card
        * (((Nat.primeFactors M).filter (fun p => p ∣ D)).prod
            (fun p => p ^ (D.factorization p))
          * 8 ^ ((Nat.primeFactors M).filter (fun p => ¬ p ∣ D)).card) := by
    rw [Finset.prod_ite (fun p => 8 * p ^ (D.factorization p)) (fun _ => 8)]
    rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.prod_const]
    ring
  have hX : ((Nat.primeFactors M).filter (fun p => p ∣ D)).prod
      (fun p => p ^ (D.factorization p)) ≤ D := by
    have hDprod : D = ∏ p ∈ D.primeFactors, p ^ D.factorization p :=
      Nat.prod_primeFactors_pow_factorization hD0
    have hsub : (Nat.primeFactors M).filter (fun p => p ∣ D) ⊆ D.primeFactors := by
      intro p hp
      rw [Finset.mem_filter] at hp
      exact Nat.mem_primeFactors.mpr ⟨Nat.prime_of_mem_primeFactors hp.1, hp.2, hD0⟩
    calc ((Nat.primeFactors M).filter (fun p => p ∣ D)).prod (fun p => p ^ (D.factorization p))
        ≤ D.primeFactors.prod (fun p => p ^ (D.factorization p)) := by
          refine Finset.prod_le_prod_of_subset_of_one_le hsub (fun i _ => Nat.zero_le _) ?_
          intro i hi _
          exact Nat.one_le_pow _ _ (Nat.pos_of_ne_zero (Nat.prime_of_mem_primeFactors hi).ne_zero)
      _ = D := hDprod.symm
  have hcard : ((Nat.primeFactors M).filter (fun p => p ∣ D)).card
      + ((Nat.primeFactors M).filter (fun p => ¬ p ∣ D)).card = (Nat.primeFactors M).card :=
    Finset.card_filter_add_card_filter_not (fun p => p ∣ D)
  have h8 : 8 ^ ((Nat.primeFactors M).filter (fun p => p ∣ D)).card
      * 8 ^ ((Nat.primeFactors M).filter (fun p => ¬ p ∣ D)).card
      = 8 ^ (Nat.primeFactors M).card := by
    rw [← pow_add, hcard]
  have hfin : (Nat.primeFactors M).prod (fun p =>
        (if p ∣ D then 8 * p ^ (D.factorization p) else 8))
      ≤ 8 ^ (Nat.primeFactors M).card * D := by
    rw [hstep2]
    have h9 : 8 ^ ((Nat.primeFactors M).filter (fun p => p ∣ D)).card
        * (((Nat.primeFactors M).filter (fun p => p ∣ D)).prod
            (fun p => p ^ (D.factorization p))
          * 8 ^ ((Nat.primeFactors M).filter (fun p => ¬ p ∣ D)).card)
        = 8 ^ (Nat.primeFactors M).card
          * ((Nat.primeFactors M).filter (fun p => p ∣ D)).prod
              (fun p => p ^ (D.factorization p)) := by
      rw [← h8]; ring
    rw [h9]
    exact Nat.mul_le_mul_left _ hX
  have h8d : 8 ^ (Nat.primeFactors M).card ≤ (Nat.divisors M).card ^ 3 := by
    have h := Commons.NumberTheory.FriedlanderIwaniec.two_pow_card_primeFactors_le_card_divisors
      (by omega : 0 < M)
    calc 8 ^ (Nat.primeFactors M).card = (2 ^ 3) ^ (Nat.primeFactors M).card := by norm_num
      _ = (2 ^ (Nat.primeFactors M).card) ^ 3 := by
            rw [← pow_mul, ← pow_mul]; congr 1; ring
      _ ≤ (Nat.divisors M).card ^ 3 := Nat.pow_le_pow_left h 3
  calc (Nat.primeFactors M).prod (fun p =>
        ({α : ZMod (p ^ M.factorization p) |
            α ^ 2 = -((D : ℕ) : ZMod (p ^ M.factorization p))}).ncard)
      ≤ (Nat.primeFactors M).prod (fun p =>
          (if p ∣ D then 8 * p ^ (D.factorization p) else 8)) := hstep1
    _ ≤ 8 ^ (Nat.primeFactors M).card * D := hfin
    _ ≤ (Nat.divisors M).card ^ 3 * D := Nat.mul_le_mul_right _ h8d
    _ = D * (Nat.divisors M).card ^ 3 := by ring


/-! ## Decomposition by the content `gcd (X, Y)` -/

/-- For `D ≥ 1` and `M ≥ 1`, an integer solution of `a ^ 2 + D * b ^ 2 = M` has
`|a| ≤ M` and `|b| ≤ M`. -/
private lemma natAbs_le_of_sq_add_mul_sq_eq {D M : ℕ} (hD : 1 ≤ D) {a b : ℤ}
    (h : a ^ 2 + (D : ℤ) * b ^ 2 = (M : ℤ)) : a.natAbs ≤ M ∧ b.natAbs ≤ M := by
  have hD1 : (1 : ℤ) ≤ (D : ℤ) := by exact_mod_cast hD
  have ha2 : a ^ 2 ≤ (M : ℤ) := by
    have : (0 : ℤ) ≤ (D : ℤ) * b ^ 2 := by positivity
    linarith
  have hb2 : b ^ 2 ≤ (M : ℤ) := by
    have hle : b ^ 2 ≤ (D : ℤ) * b ^ 2 := by
      calc b ^ 2 = 1 * b ^ 2 := by ring
        _ ≤ (D : ℤ) * b ^ 2 := mul_le_mul_of_nonneg_right hD1 (sq_nonneg b)
    linarith [sq_nonneg a, h, hle]
  constructor
  · have h2 : (a.natAbs : ℤ) ^ 2 ≤ (M : ℤ) := by rw [Int.natAbs_sq]; exact ha2
    have h3 : a.natAbs ^ 2 ≤ M := by exact_mod_cast h2
    exact le_trans (Nat.le_self_pow (by norm_num) a.natAbs) h3
  · have h2 : (b.natAbs : ℤ) ^ 2 ≤ (M : ℤ) := by rw [Int.natAbs_sq]; exact hb2
    have h3 : b.natAbs ^ 2 ≤ M := by exact_mod_cast h2
    exact le_trans (Nat.le_self_pow (by norm_num) b.natAbs) h3

/-- The number of integer solutions of `X ^ 2 + D * Y ^ 2 = M` is at most
`4 * D * d (M) ^ 4`. -/
theorem ncard_sq_add_mul_sq_le (D M : ℕ) (hD : 1 ≤ D) (hM : 1 ≤ M) :
    ({p : ℤ × ℤ | p.1 ^ 2 + (D : ℤ) * p.2 ^ 2 = (M : ℤ)}).ncard
      ≤ 4 * D * (Nat.divisors M).card ^ 4 := by
  classical
  have hM0 : M ≠ 0 := by omega
  set s : Finset (ℤ × ℤ) :=
    ((Finset.Icc (-(M : ℤ)) (M : ℤ)) ×ˢ (Finset.Icc (-(M : ℤ)) (M : ℤ))).filter
      (fun p => p.1 ^ 2 + (D : ℤ) * p.2 ^ 2 = (M : ℤ)) with hs
  have hs_eq : ∀ p, p ∈ s → p.1 ^ 2 + (D : ℤ) * p.2 ^ 2 = (M : ℤ) := by
    intro p hp; rw [hs, Finset.mem_filter] at hp; exact hp.2
  have hset : ({p : ℤ × ℤ | p.1 ^ 2 + (D : ℤ) * p.2 ^ 2 = (M : ℤ)} : Set (ℤ × ℤ)) = ↑s := by
    ext p
    rw [Set.mem_ofPred_eq, Finset.mem_coe, hs, Finset.mem_filter, Finset.mem_product]
    constructor
    · intro hp
      obtain ⟨h1, h2⟩ := natAbs_le_of_sq_add_mul_sq_eq hD hp
      have ha : |p.1| ≤ (M : ℤ) := by rw [Int.abs_eq_natAbs]; exact_mod_cast h1
      have hb : |p.2| ≤ (M : ℤ) := by rw [Int.abs_eq_natAbs]; exact_mod_cast h2
      exact ⟨⟨Finset.mem_Icc.mpr (abs_le.mp ha), Finset.mem_Icc.mpr (abs_le.mp hb)⟩, hp⟩
    · rintro ⟨-, hp⟩; exact hp
  rw [hset, Set.ncard_coe_finset]
  have hbound : ∀ b ∈ Nat.divisors M,
      (s.filter (fun p => Int.gcd p.1 p.2 = b)).card ≤ 4 * D * (Nat.divisors M).card ^ 3 := by
    intro b hb
    rw [Nat.mem_divisors] at hb
    obtain ⟨hbdvd, -⟩ := hb
    have hbpos : 0 < b := Nat.pos_of_dvd_of_pos hbdvd (by omega)
    by_cases hb2 : b ^ 2 ∣ M
    · set T : Set (ℤ × ℤ) :=
        {q : ℤ × ℤ | q.1 ^ 2 + (D : ℤ) * q.2 ^ 2 = (((M / b ^ 2 : ℕ) : ℤ)) ∧
          Int.gcd q.1 q.2 = 1} with hTdef
      have hle1 : 1 ≤ M / b ^ 2 := by
        rw [Nat.le_div_iff_mul_le (by positivity : 0 < b ^ 2), one_mul]
        exact Nat.le_of_dvd (by omega) hb2
      have hTbound : T.ncard ≤ 4 * D * (Nat.divisors M).card ^ 3 := by
        have h1 : T.ncard
            ≤ 4 * ({α : ZMod (M / b ^ 2) |
                α ^ 2 = -((D : ℕ) : ZMod (M / b ^ 2))}).ncard := by
          rw [hTdef]
          exact Commons.NumberTheory.Diophantine.ncard_primitive_sq_add_mul_sq_le
            D (M / b ^ 2) hD hle1
        have h2 : ({α : ZMod (M / b ^ 2) |
              α ^ 2 = -((D : ℕ) : ZMod (M / b ^ 2))}).ncard
            ≤ D * (Nat.divisors (M / b ^ 2)).card ^ 3 :=
          ncard_sq_eq_neg_le D (M / b ^ 2) hD hle1
        have h3 : (Nat.divisors (M / b ^ 2)).card ≤ (Nat.divisors M).card := by
          apply Finset.card_le_card
          intro d hd
          rw [Nat.mem_divisors] at hd ⊢
          exact ⟨hd.1.trans (Nat.div_dvd_of_dvd hb2), hM0⟩
        have h4 : D * (Nat.divisors (M / b ^ 2)).card ^ 3
            ≤ D * (Nat.divisors M).card ^ 3 :=
          Nat.mul_le_mul_left _ (Nat.pow_le_pow_left h3 3)
        calc T.ncard
            ≤ 4 * ({α : ZMod (M / b ^ 2) |
                α ^ 2 = -((D : ℕ) : ZMod (M / b ^ 2))}).ncard := h1
          _ ≤ 4 * (D * (Nat.divisors M).card ^ 3) := by
              apply Nat.mul_le_mul_left
              exact le_trans h2 h4
          _ = 4 * D * (Nat.divisors M).card ^ 3 := by ring
      have hTfin : T.Finite := by
        apply Set.Finite.subset (Finset.finite_toSet
          (Finset.Icc (-((M : ℤ))) (M : ℤ) ×ˢ Finset.Icc (-((M : ℤ))) (M : ℤ)))
        intro q hq
        rw [hTdef] at hq
        obtain ⟨hq1, -⟩ := hq
        obtain ⟨h1, h2⟩ := natAbs_le_of_sq_add_mul_sq_eq hD hq1
        have hA : |q.1| ≤ (M : ℤ) := by
          rw [Int.abs_eq_natAbs]; exact_mod_cast (le_trans h1 (Nat.div_le_self M (b ^ 2)))
        have hB : |q.2| ≤ (M : ℤ) := by
          rw [Int.abs_eq_natAbs]; exact_mod_cast (le_trans h2 (Nat.div_le_self M (b ^ 2)))
        simp only [Finset.mem_coe, Finset.mem_product, Finset.mem_Icc]
        exact ⟨abs_le.mp hA, abs_le.mp hB⟩
      have hinj : (s.filter (fun p => Int.gcd p.1 p.2 = b)).card ≤ T.ncard := by
        set f : ℤ × ℤ → ℤ × ℤ := fun p => (p.1 / (b : ℤ), p.2 / (b : ℤ)) with hf
        have hmaps : ∀ p ∈ s.filter (fun p => Int.gcd p.1 p.2 = b), f p ∈ T := by
          intro p hp
          rw [Finset.mem_filter] at hp
          obtain ⟨hps, hgcd⟩ := hp
          have hp_eq := hs_eq p hps
          have hd1 : (b : ℤ) ∣ p.1 := by rw [← hgcd]; exact Int.gcd_dvd_left p.1 p.2
          have hd2 : (b : ℤ) ∣ p.2 := by rw [← hgcd]; exact Int.gcd_dvd_right p.1 p.2
          have hu : p.1 / (b : ℤ) * (b : ℤ) = p.1 := Int.ediv_mul_cancel hd1
          have hv : p.2 / (b : ℤ) * (b : ℤ) = p.2 := Int.ediv_mul_cancel hd2
          have hb2ne : ((b : ℤ)) ^ 2 ≠ 0 := by positivity
          have hnorm : (p.1 / (b : ℤ)) ^ 2 + (D : ℤ) * (p.2 / (b : ℤ)) ^ 2
              = (((M / b ^ 2 : ℕ)) : ℤ) := by
            have h0 : (p.1 / (b : ℤ) * (b : ℤ)) ^ 2
                + (D : ℤ) * (p.2 / (b : ℤ) * (b : ℤ)) ^ 2 = (M : ℤ) := by
              rw [hu, hv]; exact hp_eq
            have hkey : ((p.1 / (b : ℤ)) ^ 2 + (D : ℤ) * (p.2 / (b : ℤ)) ^ 2) * (b : ℤ) ^ 2
                = (M : ℤ) := by
              calc ((p.1 / (b : ℤ)) ^ 2 + (D : ℤ) * (p.2 / (b : ℤ)) ^ 2) * (b : ℤ) ^ 2
                  = (p.1 / (b : ℤ) * (b : ℤ)) ^ 2
                    + (D : ℤ) * (p.2 / (b : ℤ) * (b : ℤ)) ^ 2 := by ring
                _ = (M : ℤ) := h0
            have h3 : (M : ℤ) = (((M / b ^ 2 : ℕ)) : ℤ) * (b : ℤ) ^ 2 := by
              have h := Nat.div_mul_cancel hb2
              have h' : (((M / b ^ 2 : ℕ)) : ℤ) * (((b ^ 2 : ℕ)) : ℤ) = (M : ℤ) := by
                rw [← Nat.cast_mul, h]
              rw [← h', Nat.cast_pow]
            rw [h3] at hkey
            exact mul_right_cancel₀ hb2ne hkey
          have hgc : Int.gcd (p.1 / (b : ℤ)) (p.2 / (b : ℤ)) = 1 := by
            have h := Int.gcd_mul_right (p.1 / (b : ℤ)) (b : ℤ) (p.2 / (b : ℤ))
            rw [hu, hv, hgcd, Int.natAbs_natCast] at h
            have hh : Int.gcd (p.1 / (b : ℤ)) (p.2 / (b : ℤ)) * b = 1 * b := by
              rw [one_mul]; exact h.symm
            exact Nat.mul_right_cancel hbpos hh
          rw [hTdef]
          exact ⟨hnorm, hgc⟩
        have hinjf : Set.InjOn f (↑(s.filter (fun p => Int.gcd p.1 p.2 = b)) : Set (ℤ × ℤ)) := by
          intro p hp q hq hpq
          rw [Finset.mem_coe, Finset.mem_filter] at hp hq
          obtain ⟨hps, hgcd⟩ := hp
          obtain ⟨hqs, hgcdq⟩ := hq
          have hd1 : (b : ℤ) ∣ p.1 := by rw [← hgcd]; exact Int.gcd_dvd_left p.1 p.2
          have hd1' : (b : ℤ) ∣ q.1 := by rw [← hgcdq]; exact Int.gcd_dvd_left q.1 q.2
          have hd2 : (b : ℤ) ∣ p.2 := by rw [← hgcd]; exact Int.gcd_dvd_right p.1 p.2
          have hd2' : (b : ℤ) ∣ q.2 := by rw [← hgcdq]; exact Int.gcd_dvd_right q.1 q.2
          have h1 : p.1 / (b : ℤ) = q.1 / (b : ℤ) := by
            have := congrArg Prod.fst hpq; simpa [hf] using this
          have h2 : p.2 / (b : ℤ) = q.2 / (b : ℤ) := by
            have := congrArg Prod.snd hpq; simpa [hf] using this
          have hp1 : p.1 = q.1 := by rw [← Int.ediv_mul_cancel hd1, h1, Int.ediv_mul_cancel hd1']
          have hp2 : p.2 = q.2 := by rw [← Int.ediv_mul_cancel hd2, h2, Int.ediv_mul_cancel hd2']
          exact Prod.ext hp1 hp2
        calc (s.filter (fun p => Int.gcd p.1 p.2 = b)).card
            = (↑(s.filter (fun p => Int.gcd p.1 p.2 = b)) : Set (ℤ × ℤ)).ncard :=
              (Set.ncard_coe_finset _).symm
          _ ≤ T.ncard := Set.ncard_le_ncard_of_injOn f hmaps hinjf hTfin
      exact le_trans hinj hTbound
    · have hemp : (s.filter (fun p => Int.gcd p.1 p.2 = b)) = ∅ := by
        rw [Finset.eq_empty_iff_forall_notMem]
        intro p hp
        rw [Finset.mem_filter] at hp
        obtain ⟨hps, hgcd⟩ := hp
        apply hb2
        have hd1 : (b : ℤ) ∣ p.1 := by rw [← hgcd]; exact Int.gcd_dvd_left p.1 p.2
        have hd2 : (b : ℤ) ∣ p.2 := by rw [← hgcd]; exact Int.gcd_dvd_right p.1 p.2
        have : (((b ^ 2 : ℕ)) : ℤ) ∣ (M : ℤ) := by
          rw [← hs_eq p hps]; push_cast
          exact dvd_add (pow_dvd_pow_of_dvd hd1 2)
            (dvd_mul_of_dvd_right (pow_dvd_pow_of_dvd hd2 2) (D : ℤ))
        exact Int.ofNat_dvd.mp this
      rw [hemp]; simp
  have hmap : ∀ p ∈ s, Int.gcd p.1 p.2 ∈ Nat.divisors M := by
    intro p hp
    rw [Nat.mem_divisors]
    refine ⟨?_, hM0⟩
    have h1 : ((Int.gcd p.1 p.2 : ℤ)) ∣ p.1 := Int.gcd_dvd_left p.1 p.2
    have h2 : ((Int.gcd p.1 p.2 : ℤ)) ∣ p.2 := Int.gcd_dvd_right p.1 p.2
    have h3 : ((Int.gcd p.1 p.2 : ℤ)) ∣ p.1 ^ 2 := by
      rw [pow_two]; exact dvd_mul_of_dvd_left h1 p.1
    have h4 : ((Int.gcd p.1 p.2 : ℤ)) ∣ (D : ℤ) * p.2 ^ 2 := by
      rw [pow_two]; exact dvd_mul_of_dvd_right (dvd_mul_of_dvd_right h2 p.2) (D : ℤ)
    have : ((Int.gcd p.1 p.2 : ℤ)) ∣ (M : ℤ) := by rw [← hs_eq p hp]; exact dvd_add h3 h4
    exact Int.ofNat_dvd.mp this
  have hmain := Finset.card_le_mul_card_image_of_maps_to (s := s) (t := Nat.divisors M)
    (f := fun p : ℤ × ℤ => Int.gcd p.1 p.2) hmap (4 * D * (Nat.divisors M).card ^ 3) hbound
  calc s.card ≤ (4 * D * (Nat.divisors M).card ^ 3) * (Nat.divisors M).card := hmain
    _ = 4 * D * (Nat.divisors M).card ^ 4 := by ring

/-! ## The main theorem -/

theorem ncard_binary_quadratic_repr_le (a b : ℕ) (ha : 1 ≤ a) (hb : 1 ≤ b) (eps : ℝ) (heps : 0 < eps) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 1 ≤ n →
      (Nat.card {p : ℤ × ℤ // (a : ℤ) * p.1 ^ 2 + (b : ℤ) * p.2 ^ 2 = (n : ℤ)} : ℝ)
        ≤ C * (n : ℝ) ^ eps := by
  obtain ⟨C', hC'pos, hC'⟩ :=
    Commons.NumberTheory.DivisorBound.card_divisors_le_rpow (eps / 4) (by linarith)
  have ha0 : 0 < a := lt_of_lt_of_le Nat.zero_lt_one ha
  have hb0 : 0 < b := lt_of_lt_of_le Nat.zero_lt_one hb
  have hab0 : 0 < a * b := Nat.mul_pos ha0 hb0
  have hda_pos : 0 < (Nat.divisors a).card :=
    Finset.card_pos.mpr ⟨1, Nat.one_mem_divisors.mpr ha0.ne'⟩
  have hda_pos' : (0 : ℝ) < ((Nat.divisors a).card : ℝ) := by exact_mod_cast hda_pos
  have hDpos : (0 : ℝ) < ((a * b : ℕ) : ℝ) := by exact_mod_cast hab0
  refine ⟨4 * ((a * b : ℕ) : ℝ) * ((Nat.divisors a).card : ℝ) ^ 4 * C' ^ 4, ?_, ?_⟩
  · have h2 : (0 : ℝ) < ((Nat.divisors a).card : ℝ) ^ 4 := by positivity
    have h3 : (0 : ℝ) < 4 * ((a * b : ℕ) : ℝ) * C' ^ 4 := by positivity
    nlinarith [h2, h3]
  intro n hn
  have hD : 1 ≤ a * b := hab0
  have hM : 1 ≤ a * n := Nat.mul_pos ha0 (lt_of_lt_of_le Nat.zero_lt_one hn)
  have hcard : Nat.card {p : ℤ × ℤ // (a : ℤ) * p.1 ^ 2 + (b : ℤ) * p.2 ^ 2 = (n : ℤ)}
      = ({p : ℤ × ℤ | (a : ℤ) * p.1 ^ 2 + (b : ℤ) * p.2 ^ 2 = (n : ℤ)} : Set (ℤ × ℤ)).ncard := rfl
  have hinj : ({p : ℤ × ℤ | (a : ℤ) * p.1 ^ 2 + (b : ℤ) * p.2 ^ 2 = (n : ℤ)} : Set (ℤ × ℤ)).ncard
      ≤ ({q : ℤ × ℤ | q.1 ^ 2 + ((a * b : ℕ) : ℤ) * q.2 ^ 2 = ((a * n : ℕ) : ℤ)}).ncard := by
    refine Set.ncard_le_ncard_of_injOn (fun p : ℤ × ℤ => ((a : ℤ) * p.1, p.2)) ?_ ?_ ?_
    · intro p hp
      simp only [Set.mem_ofPred_eq] at hp ⊢
      have : ((a : ℤ) * p.1) ^ 2 + ((a * b : ℕ) : ℤ) * p.2 ^ 2
          = (a : ℤ) * ((a : ℤ) * p.1 ^ 2 + (b : ℤ) * p.2 ^ 2) := by push_cast; ring
      rw [this, hp]; push_cast; ring
    · intro p _ q _ hpq
      have hpq' : ((a : ℤ) * p.1, p.2) = ((a : ℤ) * q.1, q.2) := hpq
      have h1 : (a : ℤ) * p.1 = (a : ℤ) * q.1 := (Prod.ext_iff.mp hpq').1
      have h2 : p.2 = q.2 := (Prod.ext_iff.mp hpq').2
      have ha0' : (a : ℤ) ≠ 0 := by exact_mod_cast ha0.ne'
      exact Prod.ext (mul_left_cancel₀ ha0' h1) h2
    · apply Set.Finite.subset (Finset.finite_toSet
        (Finset.Icc (-((a * n : ℕ) : ℤ)) ((a * n : ℕ) : ℤ) ×ˢ
          Finset.Icc (-((a * n : ℕ) : ℤ)) ((a * n : ℕ) : ℤ)))
      intro q hq
      simp only [Set.mem_ofPred_eq] at hq
      have hq1 : q.1 ^ 2 ≤ ((a * n : ℕ) : ℤ) := by
        have : (0 : ℤ) ≤ ((a * b : ℕ) : ℤ) * q.2 ^ 2 := by positivity
        linarith
      have hq2' : q.2 ^ 2 ≤ ((a * n : ℕ) : ℤ) := by
        have hle : q.2 ^ 2 ≤ ((a * b : ℕ) : ℤ) * q.2 ^ 2 := by
          calc q.2 ^ 2 = 1 * q.2 ^ 2 := by ring
            _ ≤ ((a * b : ℕ) : ℤ) * q.2 ^ 2 := by
                apply mul_le_mul_of_nonneg_right _ (sq_nonneg q.2)
                exact_mod_cast hD
        have : ((a * b : ℕ) : ℤ) * q.2 ^ 2 ≤ ((a * n : ℕ) : ℤ) := by
          have : (0 : ℤ) ≤ q.1 ^ 2 := sq_nonneg q.1
          linarith
        linarith
      have hA : |q.1| ≤ ((a * n : ℕ) : ℤ) := by
        rw [Int.abs_eq_natAbs]
        have : q.1.natAbs ^ 2 ≤ a * n := by
          have : (q.1.natAbs : ℤ) ^ 2 ≤ ((a * n : ℕ) : ℤ) := by rw [Int.natAbs_sq]; exact hq1
          exact_mod_cast this
        exact_mod_cast (le_trans (Nat.le_self_pow (by norm_num) q.1.natAbs) this)
      have hB : |q.2| ≤ ((a * n : ℕ) : ℤ) := by
        rw [Int.abs_eq_natAbs]
        have : q.2.natAbs ^ 2 ≤ a * n := by
          have : (q.2.natAbs : ℤ) ^ 2 ≤ ((a * n : ℕ) : ℤ) := by rw [Int.natAbs_sq]; exact hq2'
          exact_mod_cast this
        exact_mod_cast (le_trans (Nat.le_self_pow (by norm_num) q.2.natAbs) this)
      simp only [Finset.mem_coe, Finset.mem_product, Finset.mem_Icc]
      exact ⟨abs_le.mp hA, abs_le.mp hB⟩
  have hrepr : ({q : ℤ × ℤ | q.1 ^ 2 + ((a * b : ℕ) : ℤ) * q.2 ^ 2 = ((a * n : ℕ) : ℤ)}).ncard
      ≤ 4 * (a * b) * (Nat.divisors (a * n)).card ^ 4 :=
    ncard_sq_add_mul_sq_le (a * b) (a * n) hD hM
  have hsub : (Nat.divisors (a * n)).card ≤ (Nat.divisors a).card * (Nat.divisors n).card :=
    Commons.NumberTheory.FriedlanderIwaniec.card_divisors_mul_le a n
  have htau : ((Nat.divisors n).card : ℝ) ≤ C' * (n : ℝ) ^ (eps / 4) := hC' n
  have hxsq : ((n : ℝ) ^ (eps / 4)) ^ 4 = (n : ℝ) ^ eps := by
    rw [← Real.rpow_natCast ((n : ℝ) ^ (eps / 4)) 4, ← Real.rpow_mul (by positivity)]
    congr 1; ring
  have hd2 : ((Nat.divisors n).card : ℝ) ^ 4 ≤ C' ^ 4 * (n : ℝ) ^ eps := by
    calc ((Nat.divisors n).card : ℝ) ^ 4 ≤ (C' * (n : ℝ) ^ (eps / 4)) ^ 4 :=
          pow_le_pow_left₀ (by positivity) htau 4
      _ = C' ^ 4 * ((n : ℝ) ^ (eps / 4)) ^ 4 := by ring
      _ = C' ^ 4 * (n : ℝ) ^ eps := by rw [hxsq]
  have hsubR : ((Nat.divisors (a * n)).card : ℝ)
      ≤ ((Nat.divisors a).card : ℝ) * ((Nat.divisors n).card : ℝ) := by exact_mod_cast hsub
  have hfac : (0 : ℝ) < 4 * ((a * b : ℕ) : ℝ) := by positivity
  have hfac2 : (0 : ℝ) ≤ 4 * ((a * b : ℕ) : ℝ) * ((Nat.divisors a).card : ℝ) ^ 4 := by positivity
  rw [hcard]
  calc ({p : ℤ × ℤ | (a : ℤ) * p.1 ^ 2 + (b : ℤ) * p.2 ^ 2 = (n : ℤ)} : Set (ℤ × ℤ)).ncard
      ≤ (({q : ℤ × ℤ | q.1 ^ 2 + ((a * b : ℕ) : ℤ) * q.2 ^ 2
          = ((a * n : ℕ) : ℤ)}).ncard : ℝ) := by exact_mod_cast hinj
    _ ≤ ((4 * (a * b) * (Nat.divisors (a * n)).card ^ 4 : ℕ) : ℝ) := by exact_mod_cast hrepr
    _ = 4 * ((a * b : ℕ) : ℝ) * ((Nat.divisors (a * n)).card : ℝ) ^ 4 := by push_cast; ring
    _ ≤ 4 * ((a * b : ℕ) : ℝ) * (((Nat.divisors a).card : ℝ)
        * ((Nat.divisors n).card : ℝ)) ^ 4 := by
        apply mul_le_mul_of_nonneg_left _ hfac.le
        exact pow_le_pow_left₀ (by positivity) hsubR 4
    _ = 4 * ((a * b : ℕ) : ℝ) * ((Nat.divisors a).card : ℝ) ^ 4
        * ((Nat.divisors n).card : ℝ) ^ 4 := by ring
    _ ≤ 4 * ((a * b : ℕ) : ℝ) * ((Nat.divisors a).card : ℝ) ^ 4 * (C' ^ 4 * (n : ℝ) ^ eps) := by
        apply mul_le_mul_of_nonneg_left hd2 hfac2
    _ = 4 * ((a * b : ℕ) : ℝ) * ((Nat.divisors a).card : ℝ) ^ 4 * C' ^ 4 * (n : ℝ) ^ eps := by ring

end Commons.NumberTheory.Int
