import Mathlib
import Submission.Work.GM.S3.Base
import Submission.Work.GM.S3.Defs
import Submission.Work.GM.S3.Iterm_eq_integral
import Submission.Work.GM.S2.hhat_neg_symm

/-!
# `Iterm` is invariant under transposition up to conjugation

`Submission.GM.Iterm N W m = N³ Σ_{t₁,t₂,t₃ ∈ W} ĥ_{t₁-t₂}(m₁N) ĥ_{t₂-t₃}(m₂N) ĥ_{t₃-t₁}(m₃N)`
(GM Lemma 4.5).  Swapping the two first coordinates of `m` while reversing the `t`-ordering
amounts to conjugating `Iterm` at `-m`:

`Iterm N W (m₂, m₁, m₃) = conj (Iterm N W (-m₁, -m₂, -m₃))`.

The two ingredients are the reflection symmetry `ĥ_t(-ξ) = conj (ĥ_{-t}(ξ))` of the Fourier
transform of `hfun t` (`Work.GM.S2.hhat_neg_symm`, whose proof uses
`conj (hfun s u) = hfun (-s) u` together with `integral_conj`), and the purely combinatorial
fact that in a triple sum over a common index set the outermost and innermost indices may be
exchanged (`sum3_swap_outer_inner`), which effects the reversal `(t₁,t₂,t₃) ↦ (t₃,t₂,t₁)` of the
summation variables.
-/

namespace Work.GM.S3

open Complex Finset
open scoped BigOperators
open Submission.GM (hhat Iterm)

/-- `conj (ĥ_a(-x)) = ĥ_{-a}(x)`: the reflection symmetry of `ĥ` read in the direction that lets a
conjugation pass through one factor of `Iterm` (as usual for a conjugate-linear statement, the
`-` on the frequency and the `-` on the spectral parameter swap sides). -/
lemma star_hhat_neg (a x : ℝ) : star (hhat a (-x)) = hhat (-a) x := by
  rw [Work.GM.S2.hhat_neg_symm a x]
  simp

/-- `(((-m : ℤ) : ℝ) * N) = -((m : ℝ) * N)`: the integer negation of a frequency, moved out of
the real scalar product with `N`. -/
lemma intCast_neg_mul_nat (m : ℤ) (N : ℕ) : (((-m : ℤ) : ℝ) * N) = -((m : ℝ) * N) := by
  push_cast
  ring

/-- In a triple sum over a common finite set the outermost and innermost summation indices may be
exchanged. -/
lemma sum3_swap_outer_inner (s : Finset ℝ) (F : ℝ → ℝ → ℝ → ℂ) :
    (∑ i ∈ s, ∑ j ∈ s, ∑ k ∈ s, F k j i) = ∑ i ∈ s, ∑ j ∈ s, ∑ k ∈ s, F i j k := by
  calc (∑ i ∈ s, ∑ j ∈ s, ∑ k ∈ s, F k j i)
      = ∑ j ∈ s, ∑ i ∈ s, ∑ k ∈ s, F k j i := Finset.sum_comm
    _ = ∑ j ∈ s, ∑ k ∈ s, ∑ i ∈ s, F k j i := by
          refine Finset.sum_congr rfl (fun j _ => ?_)
          exact Finset.sum_comm
    _ = ∑ k ∈ s, ∑ j ∈ s, ∑ i ∈ s, F k j i := Finset.sum_comm
    _ = ∑ i ∈ s, ∑ j ∈ s, ∑ k ∈ s, F i j k := rfl

theorem Iterm_transpose (N : ℕ) (W : Finset ℝ) (m₁ m₂ m₃ : ℤ) :
    Submission.GM.Iterm N W (m₂, m₁, m₃) =
      star (Submission.GM.Iterm N W (-m₁, -m₂, -m₃)) := by
  -- unfold the two sides, keeping the sums explicit
  have hL : Submission.GM.Iterm N W (m₂, m₁, m₃)
      = (N : ℂ) ^ 3 * (∑ t₁ ∈ W, ∑ t₂ ∈ W, ∑ t₃ ∈ W,
          hhat (t₁ - t₂) ((m₂ : ℝ) * N) * hhat (t₂ - t₃) ((m₁ : ℝ) * N) *
            hhat (t₃ - t₁) ((m₃ : ℝ) * N)) := rfl
  have hR : Submission.GM.Iterm N W (-m₁, -m₂, -m₃)
      = (N : ℂ) ^ 3 * (∑ t₁ ∈ W, ∑ t₂ ∈ W, ∑ t₃ ∈ W,
          hhat (t₁ - t₂) (((-m₁ : ℤ) : ℝ) * N) * hhat (t₂ - t₃) (((-m₂ : ℤ) : ℝ) * N) *
            hhat (t₃ - t₁) (((-m₃ : ℤ) : ℝ) * N)) := rfl
  -- conjugation of a single summand
  have hterm : ∀ t₁ t₂ t₃ : ℝ,
      star (hhat (t₁ - t₂) (((-m₁ : ℤ) : ℝ) * N) * hhat (t₂ - t₃) (((-m₂ : ℤ) : ℝ) * N) *
          hhat (t₃ - t₁) (((-m₃ : ℤ) : ℝ) * N))
        = hhat (t₂ - t₁) ((m₁ : ℝ) * N) * hhat (t₃ - t₂) ((m₂ : ℝ) * N) *
          hhat (t₁ - t₃) ((m₃ : ℝ) * N) := by
    intro t₁ t₂ t₃
    rw [star_mul, star_mul, intCast_neg_mul_nat m₁ N, intCast_neg_mul_nat m₂ N,
      intCast_neg_mul_nat m₃ N, star_hhat_neg, star_hhat_neg, star_hhat_neg]
    simp only [neg_sub]
    ring
  -- push the conjugation inside the triple sum
  have hstar : star (∑ t₁ ∈ W, ∑ t₂ ∈ W, ∑ t₃ ∈ W,
        hhat (t₁ - t₂) (((-m₁ : ℤ) : ℝ) * N) * hhat (t₂ - t₃) (((-m₂ : ℤ) : ℝ) * N) *
          hhat (t₃ - t₁) (((-m₃ : ℤ) : ℝ) * N))
      = ∑ t₁ ∈ W, ∑ t₂ ∈ W, ∑ t₃ ∈ W,
        hhat (t₂ - t₁) ((m₁ : ℝ) * N) * hhat (t₃ - t₂) ((m₂ : ℝ) * N) *
          hhat (t₁ - t₃) ((m₃ : ℝ) * N) := by
    simp only [star_sum]
    refine Finset.sum_congr rfl (fun t₁ _ => ?_)
    refine Finset.sum_congr rfl (fun t₂ _ => ?_)
    refine Finset.sum_congr rfl (fun t₃ _ => ?_)
    exact hterm t₁ t₂ t₃
  -- reorder the three factors inside each summand
  have hG : (∑ t₁ ∈ W, ∑ t₂ ∈ W, ∑ t₃ ∈ W,
        hhat (t₂ - t₁) ((m₁ : ℝ) * N) * hhat (t₃ - t₂) ((m₂ : ℝ) * N) *
          hhat (t₁ - t₃) ((m₃ : ℝ) * N))
      = ∑ t₁ ∈ W, ∑ t₂ ∈ W, ∑ t₃ ∈ W,
        hhat (t₃ - t₂) ((m₂ : ℝ) * N) * hhat (t₂ - t₁) ((m₁ : ℝ) * N) *
          hhat (t₁ - t₃) ((m₃ : ℝ) * N) := by
    refine Finset.sum_congr rfl (fun t₁ _ => ?_)
    refine Finset.sum_congr rfl (fun t₂ _ => ?_)
    refine Finset.sum_congr rfl (fun t₃ _ => ?_)
    ring
  -- exchange the outermost and innermost summation variables
  have hF : (∑ t₁ ∈ W, ∑ t₂ ∈ W, ∑ t₃ ∈ W,
        hhat (t₃ - t₂) ((m₂ : ℝ) * N) * hhat (t₂ - t₁) ((m₁ : ℝ) * N) *
          hhat (t₁ - t₃) ((m₃ : ℝ) * N))
      = ∑ t₁ ∈ W, ∑ t₂ ∈ W, ∑ t₃ ∈ W,
        hhat (t₁ - t₂) ((m₂ : ℝ) * N) * hhat (t₂ - t₃) ((m₁ : ℝ) * N) *
          hhat (t₃ - t₁) ((m₃ : ℝ) * N) :=
    sum3_swap_outer_inner W (fun a b c : ℝ =>
      hhat (a - b) ((m₂ : ℝ) * N) * hhat (b - c) ((m₁ : ℝ) * N) * hhat (c - a) ((m₃ : ℝ) * N))
  have hall : (∑ t₁ ∈ W, ∑ t₂ ∈ W, ∑ t₃ ∈ W,
        hhat (t₂ - t₁) ((m₁ : ℝ) * N) * hhat (t₃ - t₂) ((m₂ : ℝ) * N) *
          hhat (t₁ - t₃) ((m₃ : ℝ) * N))
      = ∑ t₁ ∈ W, ∑ t₂ ∈ W, ∑ t₃ ∈ W,
        hhat (t₁ - t₂) ((m₂ : ℝ) * N) * hhat (t₂ - t₃) ((m₁ : ℝ) * N) *
          hhat (t₃ - t₁) ((m₃ : ℝ) * N) := hG.trans hF
  have hN3 : star ((N : ℂ) ^ 3) = (N : ℂ) ^ 3 := by simp
  rw [hL, hR, star_mul, hstar, hall, hN3]
  ring

end Work.GM.S3
