/-
  Companion paper ("Asymptotic sieve for primes"), §7 (`S₂`).

  This file develops the *pointwise* combinatorial reduction of §7: with `ρ_m = ∑_{ν|m}λ_ν`
  and `a` supported on squarefree numbers, the inner sums of `S₂` are rearranged into the
  bilinear shape to which the hypothesis (B′) applies.

  Main statements:
  * `abs_S2_le_log_Ksum`  — (7.1) first step: `|S₂| ≤ (log x)∑_k |Ksum k|`;
  * `Ksum_abs_le_merge`   — the expansion of `ρ_{bk}` with the divisibility constraint
                            `ν₂ | k` retained (so that the `ν`-sums can be merged by `ℓ = ν₁k`).
-/
import Mathlib
import Submission.ASP.S7
import Mathlib.NumberTheory.Divisors

namespace Submission.ASP

open Finset

noncomputable section

/-! ### The (B′)-shape sum and the inner `k`-sum of §7 -/

/-- `Xsum a N ℓ t u = ∑_{t < b ≤ u, bℓ ≤ N} μ(b)·a(bℓ)` — the "(B′)-shape" inner sum,
with `m = ℓ` (the outer, `τ`-weighted variable) and `n = b` (the inner variable). -/
def Xsum (a : ℕ → ℝ) (N : ℕ) (ℓ : ℕ) (t u : ℝ) : ℝ :=
  ∑ b ∈ (Finset.Icc 1 N).filter
      (fun b => t < ((b : ℕ) : ℝ) ∧ ((b : ℕ) : ℝ) ≤ u ∧ b * ℓ ≤ N),
    (ArithmeticFunction.moebius b : ℝ) * a (b * ℓ)

/-- The `b`-range of the inner sum of §7: `y < b ≤ sy` and `bk ≤ N`. -/
def Krange (N k : ℕ) (y sy : ℝ) : Finset ℕ :=
  (Finset.Icc 1 N).filter
    (fun b => y < ((b : ℕ) : ℝ) ∧ ((b : ℕ) : ℝ) ≤ sy ∧ b * k ≤ N)

/-- The inner `k`-sum of (7.1): `∑_{b ∈ Krange} μ(b)ρ_{bk}a_{bk}`. -/
def Ksum (a lam : ℕ → ℝ) (N : ℕ) (y sy : ℝ) (k : ℕ) : ℝ :=
  ∑ b ∈ Krange N k y sy,
    (ArithmeticFunction.moebius b : ℝ) * (a (b * k) * rhoOf lam (b * k))

/-- **(7.1), first step**, in the notation of `Ksum`: `|S₂| ≤ (log x)∑_k |Ksum k|`. -/
theorem abs_S2_le_log_Ksum (a lam : ℕ → ℝ) (N : ℕ) (y z sy : ℝ) :
    |S2 a lam N y z sy| ≤ Real.log (N : ℝ) * ∑ k ∈ Finset.Icc 1 N, |Ksum a lam N y sy k| :=
  abs_S2_le a lam N y z sy

/-! ### The divisor splitting of `ρ` -/

/-- For coprime `b, k` the divisors of `bk` are exactly the products `ν₁ν₂` with `ν₁ ∣ b`,
`ν₂ ∣ k`. -/
lemma divisors_prod_sum {b k : ℕ} (hb : 0 < b) (hk : 0 < k) (h : b.Coprime k) (lam : ℕ → ℝ) :
    (∑ ν ∈ (b * k).divisors, lam ν) = ∑ p ∈ b.divisors.product k.divisors, lam (p.1 * p.2) := by
  refine Finset.sum_bij' (fun ν _ => (Nat.gcd ν b, ν / Nat.gcd ν b))
    (fun p _ => p.1 * p.2) ?_ ?_ ?_ ?_ ?_
  · rintro ν hν
    obtain ⟨hνd, _⟩ := Nat.mem_divisors.mp hν
    have hν0' : 0 < ν := Nat.pos_of_dvd_of_pos hνd (Nat.mul_pos hb hk)
    have hdν : Nat.gcd ν b ∣ ν := Nat.gcd_dvd_left ν b
    have hdb : Nat.gcd ν b ∣ b := Nat.gcd_dvd_right ν b
    have hd0 : 0 < Nat.gcd ν b := Nat.pos_of_dvd_of_pos hdb hb
    refine Finset.mem_product.mpr ⟨Nat.mem_divisors.mpr ⟨hdb, hb.ne'⟩, ?_⟩
    refine Nat.mem_divisors.mpr ⟨?_, hk.ne'⟩
    have hcop : (ν / Nat.gcd ν b).Coprime (b / Nat.gcd ν b) :=
      Nat.coprime_div_gcd_div_gcd hd0
    have hdvd : ν / Nat.gcd ν b ∣ (b / Nat.gcd ν b) * k := by
      have h1 : Nat.gcd ν b * (ν / Nat.gcd ν b) ∣ Nat.gcd ν b * ((b / Nat.gcd ν b) * k) := by
        have h2 : Nat.gcd ν b * (ν / Nat.gcd ν b) = ν := Nat.mul_div_cancel' hdν
        have h3 : Nat.gcd ν b * ((b / Nat.gcd ν b) * k) = b * k := by
          rw [← mul_assoc, Nat.mul_div_cancel' hdb]
        rw [h2, h3]
        exact hνd
      exact Nat.dvd_of_mul_dvd_mul_left hd0 h1
    exact hcop.dvd_of_dvd_mul_left hdvd
  · rintro p hp
    obtain ⟨hp1, hp2⟩ := Finset.mem_product.mp hp
    obtain ⟨hd1, _⟩ := Nat.mem_divisors.mp hp1
    obtain ⟨hd2, _⟩ := Nat.mem_divisors.mp hp2
    exact Nat.mem_divisors.mpr ⟨Nat.mul_dvd_mul hd1 hd2, by positivity⟩
  · intro ν hν
    exact Nat.mul_div_cancel' (Nat.gcd_dvd_left ν b)
  · rintro p hp
    obtain ⟨hp1, hp2⟩ := Finset.mem_product.mp hp
    obtain ⟨hd1, _⟩ := Nat.mem_divisors.mp hp1
    obtain ⟨hd2, _⟩ := Nat.mem_divisors.mp hp2
    have hp1pos : 0 < p.1 := Nat.pos_of_dvd_of_pos hd1 hb
    have hbd : b = p.1 * (b / p.1) := (Nat.mul_div_cancel' hd1).symm
    have hcopd : (p.2).Coprime (b / p.1) :=
      ((h.coprime_dvd_right hd2).coprime_dvd_left (Nat.div_dvd_of_dvd hd1)).symm
    have hgcd : Nat.gcd (p.1 * p.2) b = p.1 := by
      rw [hbd, Nat.gcd_mul_left, hcopd.gcd_eq_one, mul_one]
    refine Prod.ext hgcd ?_
    rw [hgcd, Nat.mul_div_right p.2 hp1pos]
  · intro ν hν
    rw [Nat.mul_div_cancel' (Nat.gcd_dvd_left ν b)]

/-- `ρ_{bk} = ∑_{ν₁|b}∑_{ν₂|k}λ_{ν₁ν₂}` for coprime `b, k`. -/
lemma rhoOf_mul_of_coprime {b k : ℕ} (hb : 0 < b) (hk : 0 < k) (h : b.Coprime k)
    (lam : ℕ → ℝ) :
    rhoOf lam (b * k) = ∑ ν₁ ∈ b.divisors, ∑ ν₂ ∈ k.divisors, lam (ν₁ * ν₂) := by
  unfold rhoOf
  rw [divisors_prod_sum hb hk h lam, Finset.product_eq_sprod, Finset.sum_product]

/-! ### The reindexing `b ↦ ν₁b'` -/

/-- Reindex `b ↦ ν₁·b'` in the filtered `b`-sum of §7: the conditions `y < b ≤ sy` become
`y/ν₁ < b' ≤ sy/ν₁` and `bk ≤ N` becomes `b'·(ν₁k) ≤ N`. -/
lemma sum_filter_mul_reindex (F : ℕ → ℝ) {N ν₁ k : ℕ} (hν₁ : 1 ≤ ν₁) (hk : 1 ≤ k)
    {y sy : ℝ} (_hy : 0 < y) :
    (∑ b ∈ (Finset.Icc 1 N).filter
        (fun b => (y < ((b : ℕ) : ℝ) ∧ ((b : ℕ) : ℝ) ≤ sy ∧ b * k ≤ N) ∧ ν₁ ∣ b), F b)
      = ∑ b' ∈ (Finset.Icc 1 N).filter
          (fun b' => y / ν₁ < ((b' : ℕ) : ℝ) ∧ ((b' : ℕ) : ℝ) ≤ sy / ν₁
            ∧ b' * (ν₁ * k) ≤ N),
        F (ν₁ * b') := by
  have hν₁0 : (0 : ℝ) < ν₁ := by exact_mod_cast hν₁
  have hν₁pos : 0 < ν₁ := by omega
  refine Finset.sum_bij' (fun b _ => b / ν₁) (fun b' _ => ν₁ * b') ?_ ?_ ?_ ?_ ?_
  · rintro b hb
    rw [Finset.mem_filter] at hb
    obtain ⟨hbmem, ⟨hyb, hbsy, hbk⟩, hdvd⟩ := hb
    obtain ⟨hb1, hbN⟩ := Finset.mem_Icc.mp hbmem
    have hle : ν₁ ≤ b := Nat.le_of_dvd (by omega) hdvd
    have hcast : (((b / ν₁ : ℕ)) : ℝ) = (b : ℝ) / ν₁ := Nat.cast_div hdvd (by positivity)
    rw [Finset.mem_filter, Finset.mem_Icc]
    refine ⟨⟨(Nat.one_le_div_iff hν₁pos).mpr hle, le_trans (Nat.div_le_self b ν₁) hbN⟩,
      ?_, ?_, ?_⟩
    · rw [hcast]; exact div_lt_div_of_pos_right (by exact_mod_cast hyb) hν₁0
    · rw [hcast]; exact div_le_div_of_nonneg_right (by exact_mod_cast hbsy) hν₁0.le
    · have h1 : b / ν₁ * (ν₁ * k) = b * k := by
        rw [← Nat.mul_assoc, Nat.div_mul_cancel hdvd]
      rw [h1]; exact hbk
  · rintro b' hb'
    rw [Finset.mem_filter] at hb'
    obtain ⟨hb'mem, hyb', hbsy', hbk'⟩ := hb'
    obtain ⟨hb'1, hb'N⟩ := Finset.mem_Icc.mp hb'mem
    have hyb'' : y < (ν₁ : ℝ) * b' := by
      rw [div_lt_iff₀ hν₁0] at hyb'
      linarith [hyb']
    have hbsy'' : (ν₁ : ℝ) * b' ≤ sy := by
      rw [le_div_iff₀ hν₁0] at hbsy'
      linarith [hbsy']
    have hleN : ν₁ * b' ≤ N := by
      have h1 : ν₁ * b' ≤ (ν₁ * b') * k := by
        calc ν₁ * b' = (ν₁ * b') * 1 := (mul_one _).symm
          _ ≤ (ν₁ * b') * k := Nat.mul_le_mul_left _ hk
      have h2 : (ν₁ * b') * k = b' * (ν₁ * k) := by ring
      calc ν₁ * b' ≤ (ν₁ * b') * k := h1
        _ = b' * (ν₁ * k) := h2
        _ ≤ N := hbk'
    refine Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨?_, hleN⟩, ⟨?_, ?_, ?_⟩,
      dvd_mul_right ν₁ b'⟩
    · exact Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
    · exact_mod_cast hyb''
    · exact_mod_cast hbsy''
    · have h2 : (ν₁ * b') * k = b' * (ν₁ * k) := by ring
      rw [h2]; exact hbk'
  · intro b hb
    exact Nat.mul_div_cancel' (Finset.mem_filter.mp hb).2.2
  · intro b' hb'
    exact Nat.mul_div_right b' hν₁pos
  · intro b hb
    rw [Nat.mul_div_cancel' (Finset.mem_filter.mp hb).2.2]

/-! ### `μ(ν₁b')·a((ν₁b')k) = μν₁·μb'·a(b'(ν₁k))` -/

/-- When `a` vanishes off squarefree numbers, the Möbius factor splits:
`μ(ν₁b')a((ν₁b')k) = μ(ν₁)μ(b')a(b'(ν₁k))`.  (If `ν₁b'` is not squarefree both sides vanish,
because `a` is supported on squarefree numbers.) -/
lemma moebius_mul_a_eq {a : ℕ → ℝ} (ha : ∀ n, ¬ Squarefree n → a n = 0) (ν₁ b' k : ℕ) :
    (ArithmeticFunction.moebius (ν₁ * b') : ℝ) * a ((ν₁ * b') * k)
      = (ArithmeticFunction.moebius ν₁ : ℝ) * (ArithmeticFunction.moebius b' : ℝ)
          * a (b' * (ν₁ * k)) := by
  have harg : b' * (ν₁ * k) = (ν₁ * b') * k := by ring
  rw [harg]
  by_cases h : Squarefree (ν₁ * b')
  · have hcop : ν₁.Coprime b' := (Nat.squarefree_mul_iff.mp h).1
    have hmu : ArithmeticFunction.moebius (ν₁ * b')
        = ArithmeticFunction.moebius ν₁ * ArithmeticFunction.moebius b' :=
      ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime hcop.gcd_eq_one
    rw [hmu]
    push_cast
    ring
  · have h2 : ¬ Squarefree ((ν₁ * b') * k) := by
      intro hs
      have h3 : Squarefree (ν₁ * b') :=
        Squarefree.squarefree_of_dvd (Nat.dvd_mul_right (ν₁ * b') k) hs
      exact h h3
    rw [ha _ h2]
    ring

/-! ### §7, the expansion of `ρ_{bk}` -/

/-- **§7, the expansion**: with `ρ_m = ∑_{ν|m}λ_ν` and `a` supported on squarefree numbers,
`|∑_b μ(b)ρ_{bk}a_{bk}| ≤ ∑_{ν₁}∑_{ν₂|k}|λ_{ν₁ν₂}|·|Xsum a N (ν₁k) (y/ν₁) (sy/ν₁)|`.
The divisibility constraint `ν₂ | k` is retained so that the `(ν₁,ν₂,k)`-sum can afterwards be
merged by `ℓ = ν₁k`. -/
lemma Ksum_abs_le_merge (a lam : ℕ → ℝ) (N k : ℕ) (y sy : ℝ) (hy : 0 < y) (hk : 1 ≤ k)
    (_hkN : k ≤ N) (ha : ∀ n, ¬ Squarefree n → a n = 0) :
    |Ksum a lam N y sy k| ≤
      ∑ ν₁ ∈ Finset.Icc 1 N, ∑ ν₂ ∈ k.divisors,
        |lam (ν₁ * ν₂)| * |Xsum a N (ν₁ * k) (y / ν₁) (sy / ν₁)| := by
  have hk0 : 0 < k := by omega
  set Q : ℕ → Prop := fun b => y < ((b : ℕ) : ℝ) ∧ ((b : ℕ) : ℝ) ≤ sy ∧ b * k ≤ N with hQ
  -- ### Step 1: expand `ρ` pointwise
  have step1 : Ksum a lam N y sy k
      = ∑ b ∈ (Finset.Icc 1 N).filter Q, ∑ ν₁ ∈ b.divisors, ∑ ν₂ ∈ k.divisors,
          lam (ν₁ * ν₂) * ((ArithmeticFunction.moebius b : ℝ) * a (b * k)) := by
    simp only [Ksum, Krange, hQ]
    refine Finset.sum_congr rfl (fun b hb => ?_)
    obtain ⟨hb1, -⟩ := Finset.mem_Icc.mp (Finset.mem_filter.mp hb).1
    by_cases hsf : Squarefree (b * k)
    · rw [rhoOf_mul_of_coprime (by omega) hk0 (Nat.squarefree_mul_iff.mp hsf).1 lam]
      rw [Finset.mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl (fun ν₁ _ => ?_)
      rw [Finset.mul_sum, Finset.mul_sum]
      exact Finset.sum_congr rfl (fun ν₂ _ => by ring)
    · rw [ha _ hsf]
      simp
  -- ### Step 2: swap the `ν₁`-sum out
  have step2 : (∑ b ∈ (Finset.Icc 1 N).filter Q, ∑ ν₁ ∈ b.divisors, ∑ ν₂ ∈ k.divisors,
        lam (ν₁ * ν₂) * ((ArithmeticFunction.moebius b : ℝ) * a (b * k)))
      = ∑ ν₁ ∈ Finset.Icc 1 N,
          ∑ b ∈ (Finset.Icc 1 N).filter (fun b => Q b ∧ ν₁ ∣ b),
          ∑ ν₂ ∈ k.divisors,
            lam (ν₁ * ν₂) * ((ArithmeticFunction.moebius b : ℝ) * a (b * k)) :=
    sum_filter_divisors_swap Q
      (fun b ν₁ => ∑ ν₂ ∈ k.divisors,
        lam (ν₁ * ν₂) * ((ArithmeticFunction.moebius b : ℝ) * a (b * k)))
  -- ### Step 3: reindex `b ↦ ν₁b'`
  have step3 : (∑ ν₁ ∈ Finset.Icc 1 N,
        ∑ b ∈ (Finset.Icc 1 N).filter (fun b => Q b ∧ ν₁ ∣ b),
          ∑ ν₂ ∈ k.divisors,
            lam (ν₁ * ν₂) * ((ArithmeticFunction.moebius b : ℝ) * a (b * k)))
      = ∑ ν₁ ∈ Finset.Icc 1 N,
          ∑ b' ∈ (Finset.Icc 1 N).filter
            (fun b' => y / ν₁ < ((b' : ℕ) : ℝ) ∧ ((b' : ℕ) : ℝ) ≤ sy / ν₁
              ∧ b' * (ν₁ * k) ≤ N),
          ∑ ν₂ ∈ k.divisors,
            lam (ν₁ * ν₂) * ((ArithmeticFunction.moebius (ν₁ * b') : ℝ) * a ((ν₁ * b') * k)) := by
    refine Finset.sum_congr rfl (fun ν₁ hν₁ => ?_)
    exact sum_filter_mul_reindex
      (fun b => ∑ ν₂ ∈ k.divisors,
        lam (ν₁ * ν₂) * ((ArithmeticFunction.moebius b : ℝ) * a (b * k)))
      (Finset.mem_Icc.mp hν₁).1 hk hy
  -- ### Step 4: bring the `ν₂`-sum out and identify `Xsum`
  have step4 : (∑ ν₁ ∈ Finset.Icc 1 N,
        ∑ b' ∈ (Finset.Icc 1 N).filter
            (fun b' => y / ν₁ < ((b' : ℕ) : ℝ) ∧ ((b' : ℕ) : ℝ) ≤ sy / ν₁
              ∧ b' * (ν₁ * k) ≤ N),
          ∑ ν₂ ∈ k.divisors,
            lam (ν₁ * ν₂) * ((ArithmeticFunction.moebius (ν₁ * b') : ℝ) * a ((ν₁ * b') * k)))
      = ∑ ν₁ ∈ Finset.Icc 1 N, ∑ ν₂ ∈ k.divisors,
          lam (ν₁ * ν₂) * ((ArithmeticFunction.moebius ν₁ : ℝ)
            * Xsum a N (ν₁ * k) (y / ν₁) (sy / ν₁)) := by
    refine Finset.sum_congr rfl (fun ν₁ _ => ?_)
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun ν₂ _ => ?_)
    simp only [Xsum]
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun b' _ => ?_)
    rw [moebius_mul_a_eq ha ν₁ b' k]
    ring
  -- ### Step 5: the triangle inequality
  rw [step1, step2, step3, step4]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  refine (Finset.sum_le_sum (fun ν₁ _ => Finset.abs_sum_le_sum_abs _ _)).trans ?_
  refine Finset.sum_le_sum (fun ν₁ _ => Finset.sum_le_sum (fun ν₂ _ => ?_))
  have hmu : |(ArithmeticFunction.moebius ν₁ : ℝ)| ≤ 1 := by
    have := ArithmeticFunction.abs_moebius_le_one (n := ν₁)
    exact_mod_cast this
  rw [abs_mul, abs_mul]
  have h1 : |(ArithmeticFunction.moebius ν₁ : ℝ)|
        * |Xsum a N (ν₁ * k) (y / ν₁) (sy / ν₁)| ≤ 1 * |Xsum a N (ν₁ * k) (y / ν₁) (sy / ν₁)| :=
    mul_le_mul_of_nonneg_right hmu (abs_nonneg _)
  calc |lam (ν₁ * ν₂)| * (|(ArithmeticFunction.moebius ν₁ : ℝ)|
        * |Xsum a N (ν₁ * k) (y / ν₁) (sy / ν₁)|)
      ≤ |lam (ν₁ * ν₂)| * (1 * |Xsum a N (ν₁ * k) (y / ν₁) (sy / ν₁)|) :=
        mul_le_mul_of_nonneg_left h1 (abs_nonneg _)
    _ = |lam (ν₁ * ν₂)| * |Xsum a N (ν₁ * k) (y / ν₁) (sy / ν₁)| := by ring

end

end Submission.ASP
