/-
# The second transposition identity `(transpose)` with a `FinSupp` hypothesis on `h` alone

`Submission/Work/Analysis/InverseTheory/Transpose.lean` proves the transposition identities

`⟨Ã_N(f,g), h⟩ = ⟨Ã_N^*(h,g), f⟩ = ⟨Ã_N^{**}(f,h), g⟩`

under `FinSupp` hypotheses on all three functions `f, g, h`.  The hypotheses on `f` and `g` are
unused: the sums against `f` (first form) and against `g` (second form) are finite because the
*other* factor in the pairing is finitely supported.  For the first form this is immediate
(`h` is finitely supported), and it is the content of
`Work.KMTAreas.A4.bilinPair_AhalfZ_eq_transpose_of_finSupp` in the neighbouring file.

For the second form the pairing is `⟨Ã_N^{**}(f,h), g⟩`, and `h` finite-supported makes
`Ã_N^{**}(f,h) = N⁻¹ ∑_{N/2 < n ≤ N} f(· + n − P(n)) h(· − P(n))` finitely supported (the
translation `P(n)` runs over a finite set of shifts).  The expansion of the pairing as a double sum
therefore still holds, with the finiteness of the inner `tsum` for each `n` coming from the finite
support of `h` (shifted by `P(n)`) rather than from that of `g`.  That is
`bilinPair_AhalfTranspose₂_expand_of_finSupp_h_A4` below; the transposition identity
`transposeTwoFinSupp` follows by the change of variables `x ↦ x − P(n)`.

## Main results

* `Work.KMTAreas.A4.bilinPair_AhalfTranspose₂_expand_of_finSupp_h_A4`;
* `Work.KMTAreas.A4.transposeTwoFinSupp`.
-/
import Mathlib
import Submission.Work.Analysis.InverseTheory.Transpose
import Submission.Work.KMTContract.Areas

set_option autoImplicit false
set_option maxHeartbeats 800000

open scoped BigOperators
open Polynomial

namespace Work.KMTAreas.A4

open Work.Analysis.InverseTheory

/-- **The second dual pairing as an explicit double sum, with only `FinSupp h` assumed.**
`⟨Ã_N^{**}(f,h), g⟩ = N⁻¹ ∑_{N/2 < n ≤ N} ∑'_x f(x + n − P(n)) h(x − P(n)) g x`.

This is `bilinPair_AhalfTranspose₂_expand` with the `FinSupp g` hypothesis replaced by
`FinSupp h`: each summand vanishes off the finite set of translates `t + P(n)` of the (finite)
support `t` of `h`, so the interchange of the `tsum` in `x` with the finite sum in `n` is still
legitimate. -/
theorem bilinPair_AhalfTranspose₂_expand_of_finSupp_h_A4 {f h g : ℤ → ℂ} (hh : FinSupp h)
    (N : ℕ) (P : Polynomial ℤ) :
    bilinPair (AhalfTranspose₂ N P f h) g
      = (N : ℝ)⁻¹ * ∑ n ∈ Finset.Ioc (N / 2) N,
          ∑' x : ℤ, f (x + (n : ℤ) - P.eval (n : ℤ)) * h (x - P.eval (n : ℤ)) * g x := by
  obtain ⟨t, ht⟩ := hh
  have hpt : ∀ x : ℤ, AhalfTranspose₂ N P f h x * g x
      = (N : ℝ)⁻¹ * ∑ n ∈ Finset.Ioc (N / 2) N,
          f (x + (n : ℤ) - P.eval (n : ℤ)) * h (x - P.eval (n : ℤ)) * g x := by
    intro x
    rw [AhalfTranspose₂, mul_assoc, Finset.sum_mul]
  rw [bilinPair]
  simp only [hpt]
  rw [tsum_mul_left]
  congr 1
  exact tsum_finset_sum_of_support (s := Finset.Ioc (N / 2) N)
    (t := (Finset.Ioc (N / 2) N).biUnion
      (fun n : ℕ => t.image (fun z : ℤ => z + P.eval (n : ℤ))))
    (φ := fun n x => f (x + (n : ℤ) - P.eval (n : ℤ)) * h (x - P.eval (n : ℤ)) * g x)
    (fun n hn x hx => by
      have hxn : x - P.eval (n : ℤ) ∉ t := fun hmem =>
        hx (Finset.mem_biUnion.mpr ⟨n, hn, Finset.mem_image.mpr
          ⟨x - P.eval (n : ℤ), hmem, by ring⟩⟩)
      simp [ht _ hxn])

/-- **Equation `(transpose)` of §6, second form, with a `FinSupp` hypothesis on `h` alone:**
`⟨Ã_N(f,g), h⟩ = ⟨Ã_N^{**}(f,h), g⟩`.

Both sides are finite sums because `h` is finitely supported: the left because the pairing is
against `h`, the right because `Ã_N^{**}(f,h)` is finitely supported whenever `h` is.  This is
`bilinPair_AhalfZ_eq_transpose₂` without its (unused) hypotheses on `f` and `g`. -/
theorem transposeTwoFinSupp {f g h : ℤ → ℂ} (hh : Work.Analysis.InverseTheory.FinSupp h) (N : ℕ) (P : Polynomial ℤ) : Work.Analysis.InverseTheory.bilinPair (Work.Analysis.InverseTheory.AhalfZ N P f g) h = Work.Analysis.InverseTheory.bilinPair (Work.Analysis.InverseTheory.AhalfTranspose₂ N P f h) g := by
  rw [bilinPair_AhalfZ_expand hh N P, bilinPair_AhalfTranspose₂_expand_of_finSupp_h_A4 hh N P]
  congr 1
  exact Finset.sum_congr rfl fun n _ => tsum_reindex_transpose₂ n P

end Work.KMTAreas.A4
