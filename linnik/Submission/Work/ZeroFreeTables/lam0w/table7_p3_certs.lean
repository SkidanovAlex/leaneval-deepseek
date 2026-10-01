/-
# ZeroFreeTables — lam0w/table7_p3_certs

The `P₃`-certificates for the seventeen rows of Heath-Brown's **Table 7** (p. 47,
"`λ₂` for real `χ₁` and `ρ₁`"), in the form of HB Lemma 8.3 (§8.2, the second
method).

Read as in `HBProps.lean`, an entry `p = (λ₁, λ₂)` of `tableR hbTable7` means
*"`λ(ρ₁) ≤ p.1` implies the second zero satisfies `λ(ρ₂) ≥ p.2`"*.  The mechanism
is the one already used for Table 4 in `Table4Cert.lean`: for each row the
statement below exhibits rational parameters `(a, K, v)` with `v ≥ p.2` such that

* `cond88 0 a K` — the sufficient condition (8.8) (at `λ₁ = 0`, hence, since the
  left hand side of (8.8) is increasing in `λ₁` and its right hand side
  decreasing, for every `λ₁ ≥ 0`), which makes the left hand side of (8.7)
  non-decreasing in `λ₁`;
* `cond86 p.1 v a` — the side condition (8.6) at `(p.1, v)`;
* `p83 p.1 v a K < 0` — the left hand side of (8.7) is *strictly negative* at
  `(p.1, v)`.

Since (8.7)'s left hand side is non-decreasing in `λ₀` (`p83_mono_lam₀`), these
three facts force `λ(ρ₂) ≥ v ≥ p.2`: if `λ(ρ₂) < v` then (8.6) still holds at
`(λ(ρ₁), λ(ρ₂))` (its left hand side is *decreasing* in `λ₀`), and (8.7)'s left
hand side is `< 0` there, contradicting HB Lemma 8.3.

All data below are exact rationals found by exact (rational) arithmetic; every
row is closed by `norm_num` on the unfolded definitions `cond88`, `cond86`,
`p83`, `P3R`.  Margins of `p83` are between `6·10⁻³` and `1.5`; the witnesses
`a ∈ [3.4, 4]`, `K ∈ [1.21, 1.88]` are close to HB's own choices.

| row | `λ₁` (p.1) | `λ₂` (p.2) | `a` | `K` | `v` |
|---|---|---|---|---|---|
| 01 | 0.10 | 2.76 | 3.4 | 1.26 | 2.76 |
| 02 | 0.12 | 2.56 | 3.4 | 1.26 | 2.56 |
| 03 | 0.14 | 2.39 | 3.6 | 1.23 | 2.39 |
| 04 | 0.16 | 2.25 | 3.6 | 1.23 | 2.25 |
| 05 | 0.18 | 2.12 | 3.6 | 1.23 | 2.12 |
| 06 | 0.20 | 2.01 | 3.7 | 1.22 | 2.01 |
| 07 | 0.25 | 1.77 | 3.8 | 1.21 | 1.77 |
| 08 | 0.30 | 1.58 | 3.8 | 1.22 | 1.58 |
| 09 | 0.35 | 1.42 | 3.9 | 1.24 | 1.42 |
| 10 | 0.40 | 1.29 | 3.9 | 1.25 | 1.29 |
| 11 | 0.45 | 1.18 | 3.9 | 1.26 | 1.18 |
| 12 | 0.50 | 1.08 | 4 | 1.27 | 1.08 |
| 13 | 0.55 | 1.00 | 4 | 1.27 | 1.00 |
| 14 | 0.60 | 0.92 | 3.9 | 1.27 | 0.92 |
| 15 | 0.65 | 0.85 | 3.9 | 1.27 | 0.85 |
| 16 | 0.70 | 0.79 | 3.9 | 1.27 | 0.79 |
| 17 | 0.745 | 0.745 | 3.9 | 1.26 | 0.745 |
-/
import Mathlib
import Submission.Work.ZeroFreeTables.Table4Defs
import Submission.Work.ZeroFreeTables.HBProps

namespace Work.ZeroFreeTables.lam0w

open Work.ZeroFreeTables

theorem table7_p3_certs : ∀ p ∈ Work.ZeroFreeTables.tableR Work.ZeroFreeTables.hbTable7,
    ∃ a K v : ℝ, 0 < a ∧ 1 / 4 ≤ K ∧ p.2 ≤ v ∧
      Work.ZeroFreeTables.cond88 0 a K ∧
      Work.ZeroFreeTables.cond86 p.1 v a ∧
      Work.ZeroFreeTables.p83 p.1 v a K < 0 := by
  intro p hp
  simp only [Work.ZeroFreeTables.tableR, Work.ZeroFreeTables.hbTable7, List.mem_map, List.mem_cons,
    List.not_mem_nil, or_false] at hp
  rcases hp with ⟨q, hq, rfl⟩
  rcases hq with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;> subst h
  · refine ⟨17/5, 63/50, 69/25, by norm_num, by norm_num, by norm_num, ?_, ?_, ?_⟩
    · norm_num [cond88]
    · norm_num [cond86]
    · norm_num [p83, P3R]
  · refine ⟨17/5, 63/50, 64/25, by norm_num, by norm_num, by norm_num, ?_, ?_, ?_⟩
    · norm_num [cond88]
    · norm_num [cond86]
    · norm_num [p83, P3R]
  · refine ⟨18/5, 123/100, 239/100, by norm_num, by norm_num, by norm_num, ?_, ?_, ?_⟩
    · norm_num [cond88]
    · norm_num [cond86]
    · norm_num [p83, P3R]
  · refine ⟨18/5, 123/100, 9/4, by norm_num, by norm_num, by norm_num, ?_, ?_, ?_⟩
    · norm_num [cond88]
    · norm_num [cond86]
    · norm_num [p83, P3R]
  · refine ⟨18/5, 123/100, 53/25, by norm_num, by norm_num, by norm_num, ?_, ?_, ?_⟩
    · norm_num [cond88]
    · norm_num [cond86]
    · norm_num [p83, P3R]
  · refine ⟨37/10, 61/50, 201/100, by norm_num, by norm_num, by norm_num, ?_, ?_, ?_⟩
    · norm_num [cond88]
    · norm_num [cond86]
    · norm_num [p83, P3R]
  · refine ⟨19/5, 121/100, 177/100, by norm_num, by norm_num, by norm_num, ?_, ?_, ?_⟩
    · norm_num [cond88]
    · norm_num [cond86]
    · norm_num [p83, P3R]
  · refine ⟨19/5, 61/50, 158/100, by norm_num, by norm_num, by norm_num, ?_, ?_, ?_⟩
    · norm_num [cond88]
    · norm_num [cond86]
    · norm_num [p83, P3R]
  · refine ⟨39/10, 31/25, 142/100, by norm_num, by norm_num, by norm_num, ?_, ?_, ?_⟩
    · norm_num [cond88]
    · norm_num [cond86]
    · norm_num [p83, P3R]
  · refine ⟨39/10, 5/4, 129/100, by norm_num, by norm_num, by norm_num, ?_, ?_, ?_⟩
    · norm_num [cond88]
    · norm_num [cond86]
    · norm_num [p83, P3R]
  · refine ⟨39/10, 63/50, 118/100, by norm_num, by norm_num, by norm_num, ?_, ?_, ?_⟩
    · norm_num [cond88]
    · norm_num [cond86]
    · norm_num [p83, P3R]
  · refine ⟨4, 127/100, 108/100, by norm_num, by norm_num, by norm_num, ?_, ?_, ?_⟩
    · norm_num [cond88]
    · norm_num [cond86]
    · norm_num [p83, P3R]
  · refine ⟨4, 127/100, 1, by norm_num, by norm_num, by norm_num, ?_, ?_, ?_⟩
    · norm_num [cond88]
    · norm_num [cond86]
    · norm_num [p83, P3R]
  · refine ⟨39/10, 127/100, 92/100, by norm_num, by norm_num, by norm_num, ?_, ?_, ?_⟩
    · norm_num [cond88]
    · norm_num [cond86]
    · norm_num [p83, P3R]
  · refine ⟨39/10, 127/100, 85/100, by norm_num, by norm_num, by norm_num, ?_, ?_, ?_⟩
    · norm_num [cond88]
    · norm_num [cond86]
    · norm_num [p83, P3R]
  · refine ⟨39/10, 127/100, 79/100, by norm_num, by norm_num, by norm_num, ?_, ?_, ?_⟩
    · norm_num [cond88]
    · norm_num [cond86]
    · norm_num [p83, P3R]
  · refine ⟨39/10, 63/50, 149/200, by norm_num, by norm_num, by norm_num, ?_, ?_, ?_⟩
    · norm_num [cond88]
    · norm_num [cond86]
    · norm_num [p83, P3R]

end Work.ZeroFreeTables.lam0w
