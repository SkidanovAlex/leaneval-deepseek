import Mathlib
import Submission.Work.FIArea3.JointCount.countDefs
import Submission.Work.FIArea3.JointCount.card_filter_le_le_pieces
import Submission.Work.FIArea3.JointCount.card_jointPieceLat_le
import Submission.Work.FIArea3.JointCount.GaussPieceMax_arith
import Submission.Work.FIArea3.JointCount.maxPieceDefs
import Submission.Work.FIArea3.JointCount.maxPieceFinset_card_le

namespace Work.FIArea3.JointCount

open Finset Work.FIPlan

noncomputable section

attribute [local instance] Classical.propDecidable

/-!
# `Work.FIArea3.JointCount.card_filter_le_le_arith`

The arithmetic assembly of the joint count: the number of points of the polar box with
`d ∣ |z₂|²` and `e ∣ Δ(z₁,z₂)` is bounded by

  `π·u²·(τ(d)/d) + 80·u·(τ(d)/√d) + τ(d)`,   `u = θ·√N`,  `τ(d) = d.divisors.card`.

The pieces are already counted in

* `card_filter_le_le_pieces` — the box splits over the *maximal* Gaussian-divisor pieces
  `maxPieceFinset d`: `#box ≤ Σ_{w ∈ maxPieceFinset d} #(box ∩ wℤ[i] ∩ {e ∣ Δ})`;
* `card_jointPieceLat_le` — each piece contributes
  `≤ π u² / c_w + 80 u / √|w|² + 1`, `c_w = index (jointPieceLat z₁ w e)`;
* `GaussPieceMax_arith` — for a maximal piece generator, `d ≤ |w|²` (and `w ≠ 0`), so that
  `c_w ≥ |w|² ≥ d`: the main term is `≤ π u²/d` and the middle term `≤ 80 u/√d`;
* `maxPieceFinset_card_le` — there are at most `τ(d)` maximal pieces.

Summing the three bounds over the `τ(d)` pieces gives the claimed arithmetic bound.
-/

/-- A maximal piece generator `w` of the modulus `d` has `|w|² ≥ d`, so the joint piece
lattice `jointPieceLat z₁ w e` — whose index is `|w|² · (e / gcd …) ≥ |w|²` — has index `≥ d`. -/
lemma le_index_jointPieceLat_of_mem_maxPieceFinset (z₁ : GaussianInt) (d e : ℕ) (hd : 1 ≤ d)
    (he : 1 ≤ e) {w : GaussianInt} (hw : w ∈ maxPieceFinset d) :
    (d : ℝ) ≤ ((jointPieceLat z₁ w e).index : ℝ) := by
  have hmax : GaussPieceMax d w := (Finset.mem_filter.mp hw).2.1
  have hdw : d ≤ Work.FIPlan.gnorm w := (GaussPieceMax_arith d hd).1 w hmax
  have hw0 : w ≠ 0 := GaussPieceMax_ne_zero d hd hmax
  have hsplit := index_jointPieceLat z₁ w e he hw0
  have hgpos : 0 < Nat.gcd e (Nat.gcd (star z₁ * w).im.natAbs (star z₁ * w).re.natAbs) :=
    Nat.gcd_pos_of_pos_left _ (by omega)
  have hgle : Nat.gcd e (Nat.gcd (star z₁ * w).im.natAbs (star z₁ * w).re.natAbs) ≤ e :=
    Nat.gcd_le_left _ (by omega)
  have hdiv : 1 ≤ e / Nat.gcd e (Nat.gcd (star z₁ * w).im.natAbs (star z₁ * w).re.natAbs) := by
    have := Nat.div_pos hgle hgpos
    omega
  have hindex : (d : ℕ) ≤ (jointPieceLat z₁ w e).index := by
    rw [hsplit]
    exact le_trans hdw (Nat.le_mul_of_pos_right _ hdiv)
  exact_mod_cast hindex

/-- Each maximal piece contributes at most `π u²/d + 80 u/√d + 1` points of the polar box. -/
lemma card_jointPieceBox_le_of_mem_maxPieceFinset (Pa : Work.FITop.Params) (φ : ℝ)
    (z₁ : GaussianInt) (d e : ℕ) (hd : 1 ≤ d) (he : 1 ≤ e) {w : GaussianInt}
    (hw : w ∈ maxPieceFinset d) :
    ((jointPieceBoxFinset Pa φ z₁ w e).card : ℝ)
      ≤ Real.pi * (Pa.θ * Real.sqrt Pa.N) ^ 2 / (d : ℝ)
        + 80 * (Pa.θ * Real.sqrt Pa.N) / Real.sqrt (d : ℝ) + 1 := by
  have hmax : GaussPieceMax d w := (Finset.mem_filter.mp hw).2.1
  have hdw : d ≤ Work.FIPlan.gnorm w := (GaussPieceMax_arith d hd).1 w hmax
  have hw0 : w ≠ 0 := GaussPieceMax_ne_zero d hd hmax
  have hd0 : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  have hu0 : 0 ≤ Pa.θ * Real.sqrt Pa.N := mul_nonneg Pa.hθ0.le (Real.sqrt_nonneg _)
  have hidx := le_index_jointPieceLat_of_mem_maxPieceFinset z₁ d e hd he hw
  have hbase := card_jointPieceLat_le Pa φ z₁ w e hw0 he
  -- index term
  have h1 : Real.pi * (Pa.θ * Real.sqrt Pa.N) ^ 2
        / ((jointPieceLat z₁ w e).index : ℝ)
      ≤ Real.pi * (Pa.θ * Real.sqrt Pa.N) ^ 2 / (d : ℝ) :=
    div_le_div_of_nonneg_left (by positivity) hd0 hidx
  -- square-root term
  have hgw : (d : ℝ) ≤ (Work.FIPlan.gnorm w : ℝ) := by exact_mod_cast hdw
  have h2 : 80 * (Pa.θ * Real.sqrt Pa.N) / Real.sqrt ((Work.FIPlan.gnorm w : ℝ))
      ≤ 80 * (Pa.θ * Real.sqrt Pa.N) / Real.sqrt (d : ℝ) :=
    div_le_div_of_nonneg_left (by linarith) (Real.sqrt_pos.mpr hd0) (Real.sqrt_le_sqrt hgw)
  linarith

theorem card_filter_le_le_arith (Pa : Work.FITop.Params) (φ : ℝ) (z₁ : GaussianInt) (d e : ℕ)
    (hd : 1 ≤ d) (he : 1 ≤ e) :
    ((Work.FIArea3.JointCount.pairBoxFinset Pa φ z₁ d e).card : ℝ)
      ≤ Real.pi * (Pa.θ * Real.sqrt Pa.N) ^ 2 * ((d.divisors.card : ℝ) / (d : ℝ))
        + 80 * (Pa.θ * Real.sqrt Pa.N) * ((d.divisors.card : ℝ) / Real.sqrt (d : ℝ))
        + (d.divisors.card : ℝ) := by
  classical
  set u : ℝ := Pa.θ * Real.sqrt Pa.N with hu
  set C : ℝ := Real.pi * u ^ 2 / (d : ℝ) + 80 * u / Real.sqrt (d : ℝ) + 1 with hCdef
  have hd0 : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  have hu0 : 0 ≤ u := by
    rw [hu]; exact mul_nonneg Pa.hθ0.le (Real.sqrt_nonneg _)
  have hC0 : 0 ≤ C := by
    rw [hCdef]
    have h1 : 0 ≤ Real.pi * u ^ 2 / (d : ℝ) := div_nonneg (by positivity) hd0.le
    have h2 : 0 ≤ 80 * u / Real.sqrt (d : ℝ) :=
      div_nonneg (by linarith) (Real.sqrt_pos.mpr hd0).le
    linarith
  -- Step 1: the box is covered by the maximal pieces.
  have h1 : ((Work.FIArea3.JointCount.pairBoxFinset Pa φ z₁ d e).card : ℝ)
      ≤ ∑ w ∈ Work.FIArea3.JointCount.maxPieceFinset d,
          ((Work.FIArea3.JointCount.jointPieceBoxFinset Pa φ z₁ w e).card : ℝ) :=
    card_filter_le_le_pieces Pa φ z₁ d e hd
  -- Step 2: each piece contributes at most `C`.
  have h2 : (∑ w ∈ Work.FIArea3.JointCount.maxPieceFinset d,
        ((Work.FIArea3.JointCount.jointPieceBoxFinset Pa φ z₁ w e).card : ℝ))
      ≤ ((Work.FIArea3.JointCount.maxPieceFinset d).card : ℝ) * C := by
    calc (∑ w ∈ Work.FIArea3.JointCount.maxPieceFinset d,
          ((Work.FIArea3.JointCount.jointPieceBoxFinset Pa φ z₁ w e).card : ℝ))
        ≤ ∑ _w ∈ Work.FIArea3.JointCount.maxPieceFinset d, C := by
          refine Finset.sum_le_sum (fun w hw => ?_)
          have := card_jointPieceBox_le_of_mem_maxPieceFinset Pa φ z₁ d e hd he hw
          rw [hCdef]
          rw [← hu] at this
          exact this
      _ = ((Work.FIArea3.JointCount.maxPieceFinset d).card : ℝ) * C := by
          rw [Finset.sum_const, nsmul_eq_mul]
  -- Step 3: there are at most `τ(d)` maximal pieces.
  have h3 : ((Work.FIArea3.JointCount.maxPieceFinset d).card : ℝ) * C
      ≤ ((d.divisors.card : ℝ)) * C :=
    mul_le_mul_of_nonneg_right
      (by exact_mod_cast (maxPieceFinset_card_le d hd).1) hC0
  have h4 : ((d.divisors.card : ℝ)) * C
      = Real.pi * u ^ 2 * ((d.divisors.card : ℝ) / (d : ℝ))
        + 80 * u * ((d.divisors.card : ℝ) / Real.sqrt (d : ℝ)) + (d.divisors.card : ℝ) := by
    rw [hCdef]; ring
  have hfin : ((Work.FIArea3.JointCount.pairBoxFinset Pa φ z₁ d e).card : ℝ)
      ≤ Real.pi * u ^ 2 * ((d.divisors.card : ℝ) / (d : ℝ))
        + 80 * u * ((d.divisors.card : ℝ) / Real.sqrt (d : ℝ)) + (d.divisors.card : ℝ) := by
    linarith [h1, h2, h3, h4.le, h4.ge]
  rwa [hu] at hfin

end

end Work.FIArea3.JointCount
