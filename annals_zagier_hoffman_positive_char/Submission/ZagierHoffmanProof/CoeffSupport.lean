import Submission.ZagierHoffmanProof.CoeffTwoTerms

/-!
# The `w+1`-monomial coefficient collapse (`coeffNu_mul_of_support_le`)

The general form of `coeffNu_mul_two_terms`: if `B` is `qℤ`-supported and vanishes above `w*q`, and `A`
is `qℤ`-supported, then for `m ≥ w` the `θ^(q·m)`-coefficient of `B * A` is the `w+1`-term combination

  `∑_{i ≤ w} coeffNu 0 (q·i) B · coeffNu 0 (q·(m-i)) A`.

This is what the `W^w` reads of the two-term endgame need (`W = X - C(θ^q)` has `θ`-support
`{0, q, …, wq}`), and `coeffNu_mul_two_terms` is the `w = 1` instance.

⚠ `hm : w ≤ m` is essential: without it the terms with `i > m` would contribute
`coeffNu 0 (q*i) B * coeffNu 0 (q*(m-i)) A` with `q*(m-i) = 0` in `ℕ`, phantom summands that are not in
the true coefficient.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
open Polynomial

namespace ZagierHoffmanPositiveChar

variable (F : Type*) [Field F] [Finite F] [DecidableEq (RatFunc F)]

lemma coeffNu_mul_of_support_le {A B : Ambient F} (hA : A ∈ ambA F 0) (hB : B ∈ ambA F 0)
    (hAsupp : ∀ m, ¬ Nat.card F ∣ m → coeffNu F 0 m A = 0)
    (hBsupp : ∀ m, ¬ Nat.card F ∣ m → coeffNu F 0 m B = 0)
    {w : ℕ} (hBle : ∀ m, w * Nat.card F < m → coeffNu F 0 m B = 0)
    {m : ℕ} (hm : w ≤ m) :
    coeffNu F 0 (Nat.card F * m) (B * A)
      = ∑ i ∈ Finset.range (w + 1),
          coeffNu F 0 (Nat.card F * i) B * coeffNu F 0 (Nat.card F * (m - i)) A := by
  have hq0 : 0 < Nat.card F := Nat.pos_of_ne_zero (FrobPow.ne_zero (Ambient F) (q := Nat.card F))
  rw [coeffNu_mul F hB hA (Nat.card F * m)]
  rw [show (∑ b ∈ Finset.HasAntidiagonal.antidiagonal (Nat.card F * m),
        coeffNu F 0 b.1 B * coeffNu F 0 b.2 A)
      = ∑ k ∈ Finset.range (Nat.card F * m + 1),
        coeffNu F 0 k B * coeffNu F 0 (Nat.card F * m - k) A
      from sum_hasAntidiagonal_eq_sum_range (Nat.card F * m)
        (fun x y => coeffNu F 0 x B * coeffNu F 0 y A)]
  refine (Finset.sum_subset (s₁ := (Finset.range (w + 1)).image (fun i => Nat.card F * i))
    ?_ ?_).symm.trans ?_
  · intro k hk
    rw [Finset.mem_image] at hk
    obtain ⟨i, hi, rfl⟩ := hk
    rw [Finset.mem_range] at hi ⊢
    nlinarith
  · intro k hk hks
    rw [Finset.mem_range] at hk
    by_cases hdvd : Nat.card F ∣ k
    · obtain ⟨i, rfl⟩ := hdvd
      have hnot : ¬ (i < w + 1) := fun hlt =>
        hks (Finset.mem_image.mpr ⟨i, Finset.mem_range.mpr hlt, rfl⟩)
      rw [hBle (Nat.card F * i) (by nlinarith), zero_mul]
    · rw [hAsupp (Nat.card F * m - k) ?_, mul_zero]
      intro hdvd'
      have h2 : Nat.card F ∣ Nat.card F * m - (Nat.card F * m - k) :=
        Nat.dvd_sub (dvd_mul_right (Nat.card F) m) hdvd'
      have h3 : Nat.card F * m - (Nat.card F * m - k) = k := Nat.sub_sub_self (by omega)
      rw [h3] at h2
      exact hdvd h2
  · rw [Finset.sum_image]
    · refine Finset.sum_congr rfl fun i hi => ?_
      rw [Finset.mem_range] at hi
      rw [Nat.mul_sub_left_distrib]
    · intro x _ y _ hxy
      exact Nat.eq_of_mul_eq_mul_left hq0 hxy


end ZagierHoffmanPositiveChar
