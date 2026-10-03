import Mathlib
import Submission.Work.FIArea4.Vflip.Vfd.farPre
import Submission.Work.FIArea4.Vflip.Vfd.far_sum_eq_dyadic
import Submission.Work.FIArea4.Vflip.Vfd.InnerRangeI_eq_sum_farInner
import Submission.Work.FIArea4.Vflip.Vfd.FarSepDefs

/-!
# Reduction of the smoothly cut far form to the dyadic `(m,c,Q)`-pieces

This module proves `far_reduction`, the bookkeeping step that replaces the bounded quantity

`Σ_{p,q ∈ boxF R S} α_p conj(α_q) · nearCut a b (x_{pq}) · pairWeight D p q`

of the far part of the flipped-moduli bound by the sum over the Möbius variable `m < 2R+1`, the
common divisor `c < 2R+1` and the *dyadic* range `Q = 2^j` (`j < 4RS`), resp. the single piece
`Q = 1`, of the norms of the `(m,c,Q)`-pieces `farInner`:

`Σ_m Σ_c (Σ_{j<4RS} ‖farInner m c (2^j) (2^{j+1})‖ + ‖farInner m c 0 1‖)`.

The content is the pointwise flip identity `GG_mul_BB`, the four-fold reordering and dyadic split
`far_sum_eq_dyadic`, and the reduction by the common divisor `InnerRangeI_eq_sum_farInner`, followed
by the triangle inequality and a reordering of the finite sums.
-/

namespace Work.FIArea4.Vflip.Vfd

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

theorem far_reduction (D R S : ℕ) (a b : ℝ) (α : ℕ → ℕ → ℂ) (ha : 0 < a)
    (hcop : ∀ r s, α r s ≠ 0 → Nat.Coprime r (2 * s))
    (hcls : ∀ r s, α r s ≠ 0 → ∀ r' s', α r' s' ≠ 0 → r % 8 = r' % 8) :
    ‖∑ p ∈ Work.FIArea4.Vflip.boxF R S, ∑ q ∈ Work.FIArea4.Vflip.boxF R S,
        α p.1 p.2 * star (α q.1 q.2) *
          ((Work.FIArea4.Vflip.nearCut a b (Work.FIArea4.Vflip.xPair p q) : ℝ)
            * Work.FIArea4.Vflip.pairWeight D p q)‖
      ≤ ∑ m ∈ Finset.range (2*R+1), ∑ c ∈ Finset.range (2*R+1),
          (∑ j ∈ Finset.range (4*R*S),
              ‖Work.FIArea4.Vflip.Vfd.farInner D R S a b α m c (2^j) (2^(j+1))‖
            + ‖Work.FIArea4.Vflip.Vfd.farInner D R S a b α m c 0 1‖) := by
  -- Step 1: the pointwise flip identity turns the summand into `GG · BB`.
  have hstep1 : (∑ p ∈ Work.FIArea4.Vflip.boxF R S, ∑ q ∈ Work.FIArea4.Vflip.boxF R S,
        α p.1 p.2 * star (α q.1 q.2) *
          ((Work.FIArea4.Vflip.nearCut a b (Work.FIArea4.Vflip.xPair p q) : ℝ)
            * Work.FIArea4.Vflip.pairWeight D p q))
      = ∑ p ∈ Work.FIArea4.Vflip.boxF R S, ∑ q ∈ Work.FIArea4.Vflip.boxF R S,
          GG a b α p q * BB D R S p q := by
    refine Finset.sum_congr rfl (fun p hp => Finset.sum_congr rfl (fun q hq => ?_))
    simpa only [mul_assoc] using GG_mul_BB D R S a b α ha hcop hcls hp hq
  -- Step 2: the reindexing by the Möbius variable and the dyadic split.
  rw [hstep1, far_sum_eq_dyadic]
  -- Step 3: replace `μ(m) · InnerRangeI m Q₁ Q₂` by `Σ_c farInner m c Q₁ Q₂`.
  have hinner : ∀ m, (ArithmeticFunction.moebius m : ℂ) *
        (∑ j ∈ Finset.range (4*R*S), InnerRangeI D R S a b α m (2^j) (2^(j+1))
          + InnerRangeI D R S a b α m 0 1)
      = (∑ j ∈ Finset.range (4*R*S), ∑ c ∈ Finset.range (2*R+1),
            farInner D R S a b α m c (2^j) (2^(j+1)))
        + ∑ c ∈ Finset.range (2*R+1), farInner D R S a b α m c 0 1 := by
    intro m
    rw [mul_add, Finset.mul_sum]
    congr 1
    · exact Finset.sum_congr rfl (fun j _ =>
        InnerRangeI_eq_sum_farInner D R S a b α m (2^j) (2^(j+1)))
    · exact InnerRangeI_eq_sum_farInner D R S a b α m 0 1
  rw [Finset.sum_congr rfl (fun m _ => hinner m)]
  -- Step 4: the triangle inequality, term by term.
  have hterm : ∀ m, ‖(∑ j ∈ Finset.range (4*R*S), ∑ c ∈ Finset.range (2*R+1),
          farInner D R S a b α m c (2^j) (2^(j+1)))
        + ∑ c ∈ Finset.range (2*R+1), farInner D R S a b α m c 0 1‖
      ≤ ∑ c ∈ Finset.range (2*R+1),
          ((∑ j ∈ Finset.range (4*R*S),
              ‖farInner D R S a b α m c (2^j) (2^(j+1))‖)
            + ‖farInner D R S a b α m c 0 1‖) := by
    intro m
    have hAB : (∑ j ∈ Finset.range (4*R*S), ∑ c ∈ Finset.range (2*R+1),
          farInner D R S a b α m c (2^j) (2^(j+1)))
        + ∑ c ∈ Finset.range (2*R+1), farInner D R S a b α m c 0 1
        = ∑ c ∈ Finset.range (2*R+1),
            ((∑ j ∈ Finset.range (4*R*S),
                farInner D R S a b α m c (2^j) (2^(j+1)))
              + farInner D R S a b α m c 0 1) := by
      rw [Finset.sum_add_distrib, Finset.sum_comm]
    rw [hAB]
    calc ‖∑ c ∈ Finset.range (2*R+1),
            ((∑ j ∈ Finset.range (4*R*S),
                farInner D R S a b α m c (2^j) (2^(j+1)))
              + farInner D R S a b α m c 0 1)‖
        ≤ ∑ c ∈ Finset.range (2*R+1),
            ‖(∑ j ∈ Finset.range (4*R*S),
                farInner D R S a b α m c (2^j) (2^(j+1)))
              + farInner D R S a b α m c 0 1‖ := norm_sum_le _ _
      _ ≤ ∑ c ∈ Finset.range (2*R+1),
            (‖∑ j ∈ Finset.range (4*R*S),
                farInner D R S a b α m c (2^j) (2^(j+1))‖
              + ‖farInner D R S a b α m c 0 1‖) :=
          Finset.sum_le_sum (fun c _ => norm_add_le _ _)
      _ ≤ ∑ c ∈ Finset.range (2*R+1),
            ((∑ j ∈ Finset.range (4*R*S),
                ‖farInner D R S a b α m c (2^j) (2^(j+1))‖)
              + ‖farInner D R S a b α m c 0 1‖) :=
          Finset.sum_le_sum (fun c _ => add_le_add (norm_sum_le _ _) le_rfl)
  -- Step 5: sum the per-`m` bounds.
  calc ‖∑ m ∈ Finset.range (2*R+1),
        ((∑ j ∈ Finset.range (4*R*S), ∑ c ∈ Finset.range (2*R+1),
            farInner D R S a b α m c (2^j) (2^(j+1)))
          + ∑ c ∈ Finset.range (2*R+1), farInner D R S a b α m c 0 1)‖
      ≤ ∑ m ∈ Finset.range (2*R+1),
          ‖(∑ j ∈ Finset.range (4*R*S), ∑ c ∈ Finset.range (2*R+1),
              farInner D R S a b α m c (2^j) (2^(j+1)))
            + ∑ c ∈ Finset.range (2*R+1), farInner D R S a b α m c 0 1‖ :=
        norm_sum_le _ _
    _ ≤ ∑ m ∈ Finset.range (2*R+1), ∑ c ∈ Finset.range (2*R+1),
          ((∑ j ∈ Finset.range (4*R*S),
              ‖farInner D R S a b α m c (2^j) (2^(j+1))‖)
            + ‖farInner D R S a b α m c 0 1‖) :=
        Finset.sum_le_sum (fun m _ => hterm m)

end

end Work.FIArea4.Vflip.Vfd
