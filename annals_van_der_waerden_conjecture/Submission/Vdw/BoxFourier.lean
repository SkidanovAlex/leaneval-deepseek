import Mathlib
import Submission.Vdw.FourierExpand
import Submission.Commons.NumberTheory.ZMod.norm_sum_stdAddChar_range_le
import Submission.Commons.Analysis.Complex.two_mul_div_pi_le_norm_one_sub_exp
import Submission.Commons.NumberTheory.ZMod.sum_stdAddChar_range_eq
import Submission.Commons.NumberTheory.ZMod.norm_sum_box_stdAddChar_le

open Finset

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option linter.unusedVariables false

/-!
# The Fourier box atom (paper §4, equidistribution modulo `p` in boxes)

Bhargava's §4 proves that the set of monic degree-`n` polynomials over `𝔽_p`
with index `≥ k` is equidistributed in boxes `|a_i| ≤ H` as soon as `H < p`,
by bounding the Fourier transform of the index-characteristic function and
running a (twisted) Poisson-summation argument.  The analytic atom of that
argument — independent of the arithmetic input (the bound `M(Ψ)` on the
Fourier coefficients) — is that the sum of a character over a box
**factorizes** into one-dimensional interval sums, so that the partial-period
(Gauss-sum-over-an-interval) bound applies coordinatewise.  This module
provides that atom:

* `norm_stdAddChar_eq_one` — `‖ZMod.stdAddChar x‖ = 1`;
* (fleet commons `Commons.NumberTheory.ZMod.norm_sum_box_stdAddChar_le`) the
  factorization over the range box `{0,…,L-1}^m`;
* `norm_sum_bddVec_stdAddChar_le_of_bound` — the symmetric coefficient box
  `(BddInt H)^m = {|z_i| ≤ H}^m` of `Counting.lean`: reindexing along
  `bddIntEquivFin` (`z ↦ z + H`) and factoring out the translation phase
  `stdAddChar (-(Σ H·d_i))` (unit modulus), the character sum over the box is
  bounded by `∏_i K_i` whenever `K_i` bounds the one-dimensional range sums;
* `norm_sum_bddVec_stdAddChar_le` — the specialisation at the natural
  representatives `1 ≤ d_i ≤ p/2`, where the fleet commons
  `Commons.NumberTheory.ZMod.norm_sum_stdAddChar_range_le` gives
  `K_i = min (2H+1) (p/(2 d_i))` (from the geometric-series identity
  `sum_stdAddChar_range_eq` and the quantitative bound
  `two_mul_div_pi_le_norm_one_sub_exp`);
* `norm_sum_stdAddChar_range_eq_minrep` and
  `norm_sum_bddVec_stdAddChar_le_minrep` — the general-frequency form: for an
  arbitrary `a i ≠ 0`, the norm of the range sum only depends on the small
  representative `min (a i).val (p - (a i).val)` (negating a frequency
  conjugates the character sum), so the box bound holds with
  `K_i = min (2H+1) (p/(2·minrep (a i)))` — the exact bound a Fourier
  equidistribution argument needs for every nonzero frequency.

Axioms: propext / Classical.choice / Quot.sound only.
-/

namespace Submission.Vdw

noncomputable section

/-- **Fourier box atom** (symmetric coefficient box): the character sum over
`(BddInt H)^m` is bounded by the product of the one-dimensional bounds. -/
theorem norm_sum_bddVec_stdAddChar_le_of_bound (p : ℕ) [Fact p.Prime] (m H : ℕ)
    (a : Fin m → ZMod p) (K : Fin m → ℝ)
    (h : ∀ i, ‖∑ k ∈ Finset.range (2 * H + 1), ZMod.stdAddChar ((k : ZMod p) * a i)‖ ≤ K i) :
    ‖∑ z : BddVec m H, ZMod.stdAddChar (∑ i, ((z i : ℤ) : ZMod p) * a i)‖ ≤ ∏ i, K i := by
  classical
  haveI : NeZero p := ⟨(Fact.out : Nat.Prime p).ne_zero⟩
  set L : ℕ := 2 * H + 1 with hL
  have hreindex : ∑ z : BddVec m H,
        ZMod.stdAddChar (∑ i, ((z i : ℤ) : ZMod p) * a i)
      = ∑ v : Fin m → Fin L, ZMod.stdAddChar
          (∑ i, ((((v i : ℕ) : ℤ) - (H : ℤ) : ℤ) : ZMod p) * a i) := by
    rw [← Fintype.sum_equiv (Equiv.piCongrRight (fun _ : Fin m => (bddIntEquivFin H).symm))
        (fun v : Fin m → Fin L => ZMod.stdAddChar
          (∑ i, ((((v i : ℕ) : ℤ) - (H : ℤ) : ℤ) : ZMod p) * a i))
        (fun z : BddVec m H => ZMod.stdAddChar
          (∑ i, ((z i : ℤ) : ZMod p) * a i))]
    intro v
    exact congrArg _ (Finset.sum_congr rfl (fun i _ => rfl))
  have hsplit : ∀ (v : Fin m → Fin L),
      ZMod.stdAddChar (∑ i, ((((v i : ℕ) : ℤ) - (H : ℤ) : ℤ) : ZMod p) * a i)
        = ZMod.stdAddChar (-(∑ i, (H : ZMod p) * a i)) *
          ZMod.stdAddChar (∑ i, (((v i : ℕ) : ZMod p) * a i)) := by
    intro v
    have harg : (∑ i, ((((v i : ℕ) : ℤ) - (H : ℤ) : ℤ) : ZMod p) * a i)
        = (∑ i, (((v i : ℕ) : ZMod p) * a i))
          - (∑ i, (H : ZMod p) * a i) := by
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      push_cast
      ring
    rw [harg, AddChar.map_sub_eq_div, div_eq_mul_inv, AddChar.map_neg_eq_inv, mul_comm]
  rw [hreindex]
  have hfactor : ∑ v : Fin m → Fin L, ZMod.stdAddChar
        (∑ i, ((((v i : ℕ) : ℤ) - (H : ℤ) : ℤ) : ZMod p) * a i)
      = ZMod.stdAddChar (-(∑ i, (H : ZMod p) * a i)) *
        ∑ v : Fin m → Fin L, ZMod.stdAddChar
          (∑ i, (((v i : ℕ) : ZMod p) * a i)) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun v _ => ?_)
    rw [hsplit v]
  rw [hfactor, norm_mul, norm_stdAddChar_eq_one, one_mul]
  refine Commons.NumberTheory.ZMod.norm_sum_box_stdAddChar_le p m L a K ?_
  intro i
  simpa [L] using h i

/-- **Fourier box atom** at the natural representatives `1 ≤ d_i ≤ p/2`. -/
theorem norm_sum_bddVec_stdAddChar_le (p : ℕ) [Fact p.Prime] (m H : ℕ) (d : Fin m → ℕ)
    (hd1 : ∀ i, 1 ≤ d i) (hd2 : ∀ i, 2 * d i ≤ p) :
    ‖∑ z : BddVec m H, ZMod.stdAddChar (∑ i, ((z i : ℤ) : ZMod p) * (d i : ZMod p))‖
      ≤ ∏ i, min ((2 * H + 1 : ℕ) : ℝ) ((p : ℝ) / (2 * (d i : ℝ))) :=
  norm_sum_bddVec_stdAddChar_le_of_bound p m H (fun i => (d i : ZMod p))
    (fun i => min ((2 * H + 1 : ℕ) : ℝ) ((p : ℝ) / (2 * (d i : ℝ))))
    (fun i => Commons.NumberTheory.ZMod.norm_sum_stdAddChar_range_le p (d i) (hd1 i) (hd2 i)
      (2 * H + 1))

/-- The norm of the range character sum depends only on the *small*
representative of the frequency: `a` and `-a` give conjugate (equinormed)
sums, so with `d = min a.val (p - a.val)` the two sums have the same norm. -/
lemma norm_sum_stdAddChar_range_eq_minrep (p : ℕ) [Fact p.Prime] (a : ZMod p)
    (ha : a ≠ 0) (L : ℕ) :
    ‖∑ k ∈ Finset.range L, ZMod.stdAddChar ((k : ZMod p) * a)‖
      = ‖∑ k ∈ Finset.range L,
          ZMod.stdAddChar ((k : ZMod p) * ((min a.val (p - a.val) : ℕ) : ZMod p))‖ := by
  haveI : NeZero p := ⟨(Fact.out : Nat.Prime p).ne_zero⟩
  set d : ℕ := min a.val (p - a.val) with hd
  have hvp : a.val < p := ZMod.val_lt a
  have hv0 : a.val ≠ 0 := (ZMod.val_ne_zero a).mpr ha
  rcases le_total a.val (p - a.val) with hle | hle
  · have hdm : d = a.val := by simp [hd, min_eq_left hle]
    rw [hdm, ZMod.natCast_zmod_val]
  · have hdm : d = p - a.val := by simp [hd, min_eq_right hle]
    have haeq : a = -(((p - a.val : ℕ)) : ZMod p) := by
      have h1 : (((p - a.val : ℕ)) : ZMod p) = -a := by
        rw [Nat.cast_sub (le_of_lt hvp), ZMod.natCast_self p, ZMod.natCast_zmod_val a]
        ring
      rw [h1, neg_neg]
    have hconj : ∀ k : ℕ, ZMod.stdAddChar ((k : ZMod p) * a)
        = (starRingEnd ℂ) (ZMod.stdAddChar ((k : ZMod p) * ((d : ℕ) : ZMod p))) := by
      intro k
      have harg : (k : ZMod p) * a = -((k : ZMod p) * ((d : ℕ) : ZMod p)) := by
        rw [haeq, hdm]
        ring
      rw [harg, stdAddChar_neg_eq_conj]
    calc ‖∑ k ∈ Finset.range L, ZMod.stdAddChar ((k : ZMod p) * a)‖
        = ‖(starRingEnd ℂ)
            (∑ k ∈ Finset.range L, ZMod.stdAddChar ((k : ZMod p) * ((d : ℕ) : ZMod p)))‖ := by
          congr 1
          rw [map_sum]
          exact Finset.sum_congr rfl (fun k _ => hconj k)
      _ = ‖∑ k ∈ Finset.range L, ZMod.stdAddChar ((k : ZMod p) * ((d : ℕ) : ZMod p))‖ :=
          Complex.norm_conj _

/-- **Fourier box atom, general frequency**: for arbitrary nonzero frequencies
`a i`, the character sum over the symmetric coefficient box is bounded by the
product of the one-dimensional bounds at the small representatives. -/
theorem norm_sum_bddVec_stdAddChar_le_minrep (p : ℕ) [Fact p.Prime] (m H : ℕ)
    (a : Fin m → ZMod p) (ha : ∀ i, a i ≠ 0) :
    ‖∑ z : BddVec m H, ZMod.stdAddChar (∑ i, ((z i : ℤ) : ZMod p) * a i)‖
      ≤ ∏ i, min ((2 * H + 1 : ℕ) : ℝ)
          ((p : ℝ) / (2 * ((min (a i).val (p - (a i).val) : ℕ) : ℝ))) := by
  haveI : NeZero p := ⟨(Fact.out : Nat.Prime p).ne_zero⟩
  refine norm_sum_bddVec_stdAddChar_le_of_bound p m H a
    (fun i => min ((2 * H + 1 : ℕ) : ℝ)
      ((p : ℝ) / (2 * ((min (a i).val (p - (a i).val) : ℕ) : ℝ)))) (fun i => ?_)
  have hd1 : 1 ≤ min (a i).val (p - (a i).val) := by
    have hv0 : (a i).val ≠ 0 := (ZMod.val_ne_zero (a i)).mpr (ha i)
    have hvp : (a i).val < p := ZMod.val_lt (a i)
    omega
  have hd2 : 2 * min (a i).val (p - (a i).val) ≤ p := by omega
  calc ‖∑ k ∈ Finset.range (2 * H + 1), ZMod.stdAddChar ((k : ZMod p) * a i)‖
      = ‖∑ k ∈ Finset.range (2 * H + 1),
          ZMod.stdAddChar ((k : ZMod p) * ((min (a i).val (p - (a i).val) : ℕ) : ZMod p))‖ :=
        norm_sum_stdAddChar_range_eq_minrep p (a i) (ha i) (2 * H + 1)
    _ ≤ min ((2 * H + 1 : ℕ) : ℝ)
          ((p : ℝ) / (2 * ((min (a i).val (p - (a i).val) : ℕ) : ℝ))) :=
        Commons.NumberTheory.ZMod.norm_sum_stdAddChar_range_le p _ hd1 hd2 (2 * H + 1)

/-- **The one-dimensional weight of a frequency**: the interval bound
`min (2H+1) (p/(2·minrep a))` for `a ≠ 0` (where `minrep a = min a.val (p - a.val)`)
and the trivial bound `2H+1` for `a = 0`. -/
def freqWeight (p H : ℕ) (a : ZMod p) : ℝ :=
  if a = 0 then ((2 * H + 1 : ℕ) : ℝ)
  else min ((2 * H + 1 : ℕ) : ℝ)
    ((p : ℝ) / (2 * ((min a.val (p - a.val) : ℕ) : ℝ)))

/-- **Fourier box atom, arbitrary frequencies**: the character sum over the
symmetric coefficient box `(BddInt H)^m` is bounded by the product of the
one-dimensional weights. -/
theorem norm_sum_bddVec_stdAddChar_le_weight (p : ℕ) [Fact p.Prime] (m H : ℕ)
    (a : Fin m → ZMod p) :
    ‖∑ z : BddVec m H, ZMod.stdAddChar (∑ i, ((z i : ℤ) : ZMod p) * a i)‖
      ≤ ∏ i, freqWeight p H (a i) := by
  haveI : NeZero p := ⟨(Fact.out : Nat.Prime p).ne_zero⟩
  refine norm_sum_bddVec_stdAddChar_le_of_bound p m H a (fun i => freqWeight p H (a i))
    (fun i => ?_)
  by_cases hai : a i = 0
  · rw [hai]
    have h1 : ∀ k ∈ Finset.range (2 * H + 1),
        ZMod.stdAddChar ((k : ZMod p) * (0 : ZMod p)) = 1 := by
      intro k _
      simp
    rw [Finset.sum_congr rfl h1, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one,
      freqWeight, if_pos rfl]
    exact le_of_eq (Complex.norm_natCast (2 * H + 1))
  · rw [freqWeight, if_neg hai]
    have hd1 : 1 ≤ min (a i).val (p - (a i).val) := by
      have hv0 : (a i).val ≠ 0 := (ZMod.val_ne_zero (a i)).mpr hai
      have hvp : (a i).val < p := ZMod.val_lt (a i)
      omega
    have hd2 : 2 * min (a i).val (p - (a i).val) ≤ p := by omega
    refine le_trans (le_of_eq (norm_sum_stdAddChar_range_eq_minrep p (a i) hai (2 * H + 1))) ?_
    exact Commons.NumberTheory.ZMod.norm_sum_stdAddChar_range_le p _ hd1 hd2 (2 * H + 1)

/-- **Fourier equidistribution in the coefficient box**: for a set `T` of
residue vectors whose Fourier coefficients are bounded by `B`, the number of
coefficient vectors in `(BddInt H)^m` whose reduction mod `p` lies in `T` is at
most `|T|·(2H+1)^m/p^m` plus the Fourier error term
`B/p^m · Σ_{a ≠ 0} ∏_i min (2H+1) (p/(2·minrep (a i)))` (paper §4). -/
theorem ncard_box_residue_index_le (p : ℕ) [Fact p.Prime] (m H : ℕ)
    (T : Finset (Fin m → ZMod p)) (B : ℝ) (hB0 : 0 ≤ B)
    (hB : ∀ a : Fin m → ZMod p, a ≠ 0 →
      ‖∑ x ∈ T, ZMod.stdAddChar (∑ i, a i * x i)‖ ≤ B) :
    (Nat.card {z : BddVec m H // (fun i => ((z i : ℤ) : ZMod p)) ∈ T} : ℝ)
      ≤ (T.card : ℝ) * ((2 * H + 1 : ℕ) : ℝ) ^ m / (p : ℝ) ^ m
        + B / (p : ℝ) ^ m * ∑ a ∈ (Finset.univ : Finset (Fin m → ZMod p)).erase 0,
            ∏ i, freqWeight p H (a i) := by
  haveI : NeZero p := ⟨(Fact.out : Nat.Prime p).ne_zero⟩
  refine ncard_box_residue_le_of_fourier p m H T B hB0
    (fun a => ∏ i, freqWeight p H (a i)) hB (fun a _ => ?_)
  have h1 : (∑ y : BddVec m H, ZMod.stdAddChar (-(∑ i, a i * ((y i : ℤ) : ZMod p))))
      = (starRingEnd ℂ)
          (∑ y : BddVec m H, ZMod.stdAddChar (∑ i, a i * ((y i : ℤ) : ZMod p))) := by
    rw [map_sum]
    exact Finset.sum_congr rfl (fun y _ => stdAddChar_neg_eq_conj _)
  rw [h1, Complex.norm_conj]
  have h2 : (∑ y : BddVec m H, ZMod.stdAddChar (∑ i, a i * ((y i : ℤ) : ZMod p)))
      = ∑ y : BddVec m H, ZMod.stdAddChar (∑ i, ((y i : ℤ) : ZMod p) * a i) :=
    Finset.sum_congr rfl (fun y _ => by
      congr 1
      exact Finset.sum_congr rfl (fun i _ => mul_comm _ _))
  rw [h2]
  exact norm_sum_bddVec_stdAddChar_le_weight p m H a

end

end Submission.Vdw
