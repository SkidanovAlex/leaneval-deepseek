import Mathlib
import Submission.Work.Peluse.TransferUp.arithIcc_sum
import Submission.Work.Peluse.TransferUp.sum_Icc_natCast
import Submission.Work.Peluse.TransferUp.sum_prod_fiberwise
import Submission.Work.Peluse.TransferUp.card_prod_filter_sub

/-!
# The triangular pair sum over the arithmetic progression `c·[1,H]`

For `c ≠ 0` the set `Work.Peluse.arithIcc c H = {c, 2c, …, Hc}` is an arithmetic progression
(the map `n ↦ c * n` is injective on `{1, …, H}`), and summing a function `Φ (b - a)` over all
*ordered pairs* `(a, b)` of the progression collects, for each difference `m = n' - n`, exactly
`H - |m|` pairs:

`∑_{a ∈ c[H]} ∑_{b ∈ c[H]} Φ (b - a) = ∑_{-(H-1) ≤ m ≤ H-1} (H - |m|) Φ (c m)`.

The right-hand side is the "triangular" autocorrelation of the window `[1, H]`.  This is the
combinatorial input of the correlation/transfer-up computations of the van der Corput step
(`Work.Peluse.TransferUp.windowSum_sq_eq_corr` and friends).

The proof is a short assembly on top of four combinatorial lemmas of this directory:

* `Work.Peluse.TransferUp.arithIcc_sum` rewrites the sums over the progression `c·[1,H]` as sums
  over `[1,H]` (via `Finset.sum_image`, injectivity of `n ↦ c n` for `c ≠ 0`);
* `Work.Peluse.TransferUp.sum_Icc_natCast` passes between the `ℤ`- and the `ℕ`-interval `[1,H]`;
* `Work.Peluse.TransferUp.sum_prod_fiberwise` regroups a sum over `A × A` by the value of
  `p.2 - p.1`;
* `Work.Peluse.TransferUp.card_prod_filter_sub` counts the fibres: `H - |m|` pairs of `[1,H]²`
  have difference `m`.

What remains here is the linear combination `c n' - c n = c (n' - n)` inside `Φ` and the
bookkeeping of the ranges and of the coefficient `(H - |m| : ℕ) : ℂ`.
-/

namespace Work.Peluse.TransferUp

open scoped BigOperators

set_option autoImplicit false

/-- **The pair sum of the arithmetic progression `c·[1,H]` is a triangle-weighted single sum.**

Summing `Φ (b - a)` over all pairs `(a, b)` of the arithmetic progression
`Work.Peluse.arithIcc c H = {c, 2c, …, Hc}` (`c ≠ 0`, so that `n ↦ c n` is injective) collects,
for each difference `m = n' - n`, exactly `H - |m|` pairs:

`∑_{a ∈ c[H]} ∑_{b ∈ c[H]} Φ (b - a) = ∑_{|m| ≤ H-1} (H - |m|) Φ (c m)`.

This is the "triangular" autocorrelation of the window `[1,H]`, the combinatorial input of the
correlation computations of the transfer-up step. -/
theorem arithIcc_pairSum {c : ℤ} (hc : c ≠ 0) (H : ℕ) (Φ : ℤ → ℂ) :
    (∑ a ∈ Work.Peluse.arithIcc c H, ∑ b ∈ Work.Peluse.arithIcc c H, Φ (b - a))
      = ∑ m ∈ Finset.Icc (-(H : ℤ) + 1) ((H : ℤ) - 1),
          (((H - m.natAbs : ℕ)) : ℂ) * Φ (c * m) := by
  -- The difference of two points of `[1,H]²` lies in `[1-H, H-1]`.
  have hAprod : ∀ p ∈ (Finset.Icc (1 : ℤ) (H : ℤ)).product (Finset.Icc (1 : ℤ) (H : ℤ)),
      p.2 - p.1 ∈ Finset.Icc (-(H : ℤ) + 1) ((H : ℤ) - 1) := by
    intro p hp
    rw [Finset.product_eq_sprod, Finset.mem_product] at hp
    simp only [Finset.mem_Icc] at hp ⊢
    omega
  calc ∑ a ∈ Work.Peluse.arithIcc c H, ∑ b ∈ Work.Peluse.arithIcc c H, Φ (b - a)
      = ∑ n ∈ Finset.Icc 1 H, ∑ n' ∈ Finset.Icc 1 H,
          Φ (c * (n' : ℤ) - c * (n : ℤ)) := by
        rw [arithIcc_sum hc H
          (g := fun a => ∑ b ∈ Work.Peluse.arithIcc c H, Φ (b - a))]
        refine Finset.sum_congr rfl (fun n _ => ?_)
        exact arithIcc_sum hc H (g := fun b => Φ (b - c * (n : ℤ)))
    _ = ∑ n ∈ Finset.Icc 1 H, ∑ n' ∈ Finset.Icc (1 : ℤ) (H : ℤ),
          Φ (c * n' - c * (n : ℤ)) := by
        refine Finset.sum_congr rfl (fun n _ => ?_)
        exact (sum_Icc_natCast (H := H)
          (g := fun n' : ℤ => Φ (c * n' - c * (n : ℤ)))).symm
    _ = ∑ n ∈ Finset.Icc (1 : ℤ) (H : ℤ), ∑ n' ∈ Finset.Icc (1 : ℤ) (H : ℤ),
          Φ (c * n' - c * n) := by
        exact (sum_Icc_natCast (H := H)
          (g := fun n : ℤ => ∑ n' ∈ Finset.Icc (1 : ℤ) (H : ℤ), Φ (c * n' - c * n))).symm
    _ = ∑ n ∈ Finset.Icc (1 : ℤ) (H : ℤ), ∑ n' ∈ Finset.Icc (1 : ℤ) (H : ℤ),
          Φ (c * (n' - n)) := by
        refine Finset.sum_congr rfl (fun n _ => Finset.sum_congr rfl (fun n' _ => ?_))
        simp only [mul_sub]
    _ = ∑ p ∈ (Finset.Icc (1 : ℤ) (H : ℤ)).product (Finset.Icc (1 : ℤ) (H : ℤ)),
          Φ (c * (p.2 - p.1)) := by
        rw [Finset.product_eq_sprod]
        exact (Finset.sum_product (Finset.Icc (1 : ℤ) (H : ℤ)) (Finset.Icc (1 : ℤ) (H : ℤ))
          (fun p : ℤ × ℤ => Φ (c * (p.2 - p.1)))).symm
    _ = ∑ m ∈ Finset.Icc (-(H : ℤ) + 1) ((H : ℤ) - 1),
          (((((Finset.Icc (1 : ℤ) (H : ℤ)).product (Finset.Icc (1 : ℤ) (H : ℤ))).filter
            (fun p : ℤ × ℤ => p.2 - p.1 = m)).card : ℂ)) * Φ (c * m) := by
        exact sum_prod_fiberwise hAprod (fun m => Φ (c * m))
    _ = ∑ m ∈ Finset.Icc (-(H : ℤ) + 1) ((H : ℤ) - 1),
          (((H - m.natAbs : ℕ)) : ℂ) * Φ (c * m) := by
        refine Finset.sum_congr rfl (fun m hm => ?_)
        rw [card_prod_filter_sub hm]

end Work.Peluse.TransferUp
